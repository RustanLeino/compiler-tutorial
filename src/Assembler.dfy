// The Assembler translates a CFG program into assembly code for the RawMachine.
//
// This translation could be done straight from the AST, in a way similar to how the CFG
// program is constructed by the Compiler. However, translating to RawMachine is more
// complicated than translating to Machine, because, in addition to the basic-block
// construction that already goes into the translation to CFG, it involves computing
// offsets of parameters and local variables on the stack and computing addresses of
// procedure entries, basic-block entries, etc. in the generated code. So, instead, the
// Assembler takes a CFG program as a starting point. This lets it reuse the work that
// went into the CFG construction. However, the Assembler needs one piece of information
// that wasn't needed for the CFG construction or for execution on Machine, namely, an
// indication of when the code starts pushing actual parameters onto the evaluation stack.
// For this reason, the CFG construction in Compiler has been modified to include that
// information. In the CFG, the information is carried in a special PreCall instruction,
// which the Machine ignores.
//
// The Assembler assumes that the given program has a particular shape. If the Assembler
// detects otherwise, it returns a failure. (With more work, one would want to prove that
// Assembler never fails on the programs that Compiler generates.)

module Assembler {
  export
    provides Util, CFG
    provides Assemble
    reveals AssemblyCode

  import opened Util
  import AST
  import CFG
  import opened RawMachine

  method Assemble(program: CFG.Program) returns (r: Result<AssemblyCode>) {
    var builder := new Builder();

    // The harness looks like this:
    //     ADJ -1
    //     PUSH halt
    //     JMP Main
    //   halt:
    //     HALT
    builder.AppendComment("harness");
    builder.AppendOpcode(Adjust);
    builder.Append(-1);
    builder.AppendOpcode(Push);
    var halt := new object;
    builder.AppendPlaceholder(halt);
    builder.AppendOpcode(Jump);
    builder.AppendPlaceholder(program.routines[0].procedure);
    builder.DefinePlaceholder(halt);
    builder.AppendOpcode(Halt);

    for i := 0 to |program.routines| {
      var outcome := AssembleRoutine(program.routines[i], builder);
      var _ :- outcome.ToResult();
    }

    var asm :- builder.Finish();
    return Success(asm);
  }

  datatype AssemblyCode = AssemblyCode(code: seq<int>, noteworthyLocations: map<nat, seq<string>>)

  class Builder {
    var noteworthyLocations: map<nat, seq<string>>
    var code: seq<int>
    var placeholderUses: seq<(nat, object)>
    var placeholderDefinitions: map<object, nat>

    constructor () {
      noteworthyLocations := map[];
      code := [];
      placeholderUses := [];
      placeholderDefinitions := map[];
    }

    method Finish() returns (r: Result<AssemblyCode>)
      modifies this
    {
      for i := 0 to |placeholderUses|
        invariant placeholderUses == old(placeholderUses)
      {
        var (n, placeholder) := placeholderUses[i];
        if placeholder !in placeholderDefinitions.Keys {
          return Failure("undefined placeholder");
        }
        var x := placeholderDefinitions[placeholder];
        if 0 <= n < |code| {
          code := code[n := x];
        } else {
          return Failure("illegal placeholder use location");
        }
      }
      return Success(AssemblyCode(code, noteworthyLocations));
    }

    method AppendComment(comment: string)
      modifies this
    {
      var n := |code|;
      var comments := (if n in noteworthyLocations.Keys then noteworthyLocations[n] else []) + [comment];
      noteworthyLocations := noteworthyLocations[n := comments];
    }

    method AppendOpcode(op: Opcode)
      modifies this
    {
      Append(Encode(op));
    }

    method Append(w: int)
      modifies this
    {
      code := code + [w];
    }

    method AppendPlaceholder(placeholder: object)
      modifies this
    {
      var n := |code|;
      placeholderUses := placeholderUses + [(n, placeholder)];
      Append(0);
    }

    method DefinePlaceholder(placeholder: object)
      modifies this
    {
      var n := |code|;
      placeholderDefinitions := placeholderDefinitions[placeholder := n];
    }
  }

  method AssembleRoutine(routine: CFG.Routine, builder: Builder) returns (r: Outcome)
    modifies builder
  {
    builder.AppendComment(";;; " + routine.procedure.name + " ;;;");
    builder.DefinePlaceholder(routine.procedure);

    // On entry to the routine, the evaluation stack will look like
    //     ... reservedForResultValue returnAddress p0 p1 ... p_last
    // where the p0, p1, ..., p_last are the actual parameters of the call
    // Next, we'll adjust the stack pointer by another N slots, where N is
    // number of local-variable entries we need for this procedure.

    var offsets, numberOfLocalVariableSlots :- ComputeOffsets(routine.procedure);
    if numberOfLocalVariableSlots != 0 {
      builder.AppendOpcode(Adjust);
      var nn: int := numberOfLocalVariableSlots;
      builder.Append(-nn);
    }

    for i := 0 to |routine.basicBlocks| {
      var bb := routine.basicBlocks[i];
      builder.DefinePlaceholder(bb);
      builder.AppendComment("basic block " + Hex(bb.id));

      var state := new AssembleState(offsets);
      :- AssembleInstructions(bb.instructions, state, builder);

      match bb.ending
      case Goto(target) =>
        builder.AppendOpcode(Jump);
        builder.AppendPlaceholder(target);
      case Return =>
        // The evaluation stack now looks like
        //     ... reservedForResultValue returnAddress p0 p1 ... p_last local0 local1 ... local_last returnValue
        // First, we move the returnValue into reservedForResultValue
        builder.AppendOpcode(Store);
        builder.Append(2 + |offsets|);
        // The evaluation stack now looks like
        //     ... returnValue returnAddress p0 p1 ... p_last local0 local1 ... local_last
        // Next, we adjust the stack to remove the area for the local variables.
        if |offsets| != 0 {
          builder.AppendOpcode(Adjust);
          builder.Append(|offsets|);
        }
        //     ... returnValue returnAddress
        // Finally, we return to the caller
        builder.AppendOpcode(JumpIndirect);
    }

    return Pass;
  }

  type OffsetMap = map<AST.Variable, nat>

  // Compute a map from every parameter and local variable of "procedure" to an offset on the stack. The offsets
  // determine a placement of these variables on the stack as follows:
  //     ... p0 p1 ... p_last local0 local1 ... local_last <top-of-stack>
  // For example, local_last will map to 1 and p0 will map to an offset that's equal to the number of locals plus
  // the number of parameters.
  method ComputeOffsets(procedure: AST.Procedure) returns (r: Outcome, offsets: OffsetMap, numberOfLocalVariableSlots: nat)
  {
    // To compute the offsets we want, we need to know how many local variables are used at any one time.
    // That requires a traversal of the procedure body AST. Rather than doing two such traversals, we start
    // by constructing an offset map that goes in the opposite direction. When that's done, we construct
    // the desired offset map.

    offsets := map i | 0 <= i < |procedure.parameters| :: procedure.parameters[i] := i;
    var highwaterMark;
    offsets, highwaterMark := ComputeOffsetsStmtList(procedure.body, offsets, |procedure.parameters|);

    // Reverse the map computed so far
    if !forall v <- offsets.Keys :: offsets[v] <= |offsets| {
      return Fail("some variable declaration is used more than once in the AST"), offsets, 0;
    }
    offsets := map v <- offsets.Keys :: |offsets| - offsets[v];
    numberOfLocalVariableSlots := highwaterMark - |procedure.parameters|;
    r := Pass;
  }

  method ComputeOffsetsStmtList(statements: seq<AST.Statement>, offsetsIn: OffsetMap, currentOffset: nat)
    returns (offsets: OffsetMap, highwaterMark: nat)
    ensures currentOffset <= highwaterMark
  {
    offsets, highwaterMark := offsetsIn, currentOffset;
    var current := currentOffset;

    for i := 0 to |statements|
      invariant currentOffset <= current

    {
      match statements[i]
      case VarDeclStmt(variable, _) =>
        offsets := offsets[variable := current];
        current := current + 1;
      case AssignStmt(_, _) =>
      case CallStmt(_, _, _) =>
      case IfStmt(_, thn, els) =>
        var thenHigh, elseHigh;
        offsets, thenHigh := ComputeOffsetsStmtList(thn, offsets, current);
        offsets, elseHigh := ComputeOffsetsStmtList(els, offsets, current);
        highwaterMark := Max(highwaterMark, Max(thenHigh, elseHigh));
      case BlockStmt(statements) =>
        var high;
        offsets, high := ComputeOffsetsStmtList(statements, offsets, current);
        highwaterMark := Max(highwaterMark, high);
    }

    highwaterMark := Max(highwaterMark, current);
  }

  class AssembleState {
    const offsets: OffsetMap
    var evaluationStackHeight: nat

    constructor(offsets: OffsetMap) {
      this.offsets := offsets;
      evaluationStackHeight := 0;
    }

    method IncEvaluationStackHeight(n: nat := 1)
      modifies this
    {
      evaluationStackHeight := evaluationStackHeight + n;
    }

    method DecEvaluationStackHeight(n: nat := 1) returns (r: Outcome)
      modifies this
    {
      if evaluationStackHeight < n {
        return Fail("empty evaluation stack");
      }
      evaluationStackHeight := evaluationStackHeight - n;
      return Pass;
    }

    method AppendVariableOffset(builder: Builder, variable: AST.Variable) returns (r: Outcome)
      modifies builder
    {
      if variable !in offsets.Keys {
        return Fail("offset information missing for variable: " + variable.name);
      }
      builder.Append(offsets[variable] + evaluationStackHeight);
      return Pass;
    }
  }

  method AssembleInstructions(instructions: seq<CFG.Instruction>, state: AssembleState, builder: Builder) returns (r: Outcome)
    modifies builder, state
  {
    for i := 0 to |instructions| {
      :- AssembleInstruction(instructions[i], state, builder);
    }
    return Pass;
  }

  method AssembleInstruction(instruction: CFG.Instruction, state: AssembleState, builder: Builder) returns (r: Outcome)
    modifies builder, state
  {
    r := Pass; // unless shown otherwise below

    match instruction
    case Load(variable) =>
      builder.AppendOpcode(Load);
      :- state.AppendVariableOffset(builder, variable);
      state.IncEvaluationStackHeight();

    case Store(variable) =>
      if variable.writable {
        :- state.DecEvaluationStackHeight();
        builder.AppendOpcode(Store);
        :- state.AppendVariableOffset(builder, variable);
      } else {
        // The Compiler generates STORE instructions into non-writable variables (that is, parameters)
        // only when storing stack values into variables slots. These are not mimicked by the Assembler,
        // since the parameter values just stay in place on the stack.
      }

    case LoadLiteral(value) =>
      builder.AppendOpcode(Push);
      builder.Append(value);
      state.IncEvaluationStackHeight();

    case Subtract =>
      builder.AppendOpcode(Subtract);
      :- state.DecEvaluationStackHeight();

    case Compare =>
      builder.AppendOpcode(Compare);
      :- state.DecEvaluationStackHeight();
    
    case BranchIfZero(target) =>
      builder.AppendOpcode(ConditionalJump);
      builder.AppendPlaceholder(target);
      :- state.DecEvaluationStackHeight();

    case PreCall(callee) =>
      // Prepare for a call by reserving space on the evaluation stack for the result value and the return address.
      builder.AppendOpcode(Adjust);
      builder.Append(-2);
      state.IncEvaluationStackHeight(2);

    case Call(callee) =>
      // At the time of a Call instruction, we expect the Compiler to set up the evaluation stack to look like
      //     ... reservedForResultValue reservedForReturnAddress p0 p1 ... p_last
      // We fill in the return address and then jump to the entry of the callee.
      //
      // The assembly code will look like:
      //     PUSH returnAddress
      //     STOR numberOfParameters
      //     JMP callee
      //   returnAddress:
      var numberOfParameters := |callee.parameters|;
      var returnAddress := new object;
      builder.AppendOpcode(Push);
      builder.AppendPlaceholder(returnAddress);
      builder.AppendOpcode(Store);
      builder.Append(1 + numberOfParameters);
      builder.AppendOpcode(Jump);
      builder.AppendPlaceholder(callee);
      builder.DefinePlaceholder(returnAddress);
      :- state.DecEvaluationStackHeight(1 + numberOfParameters);
  }

}
