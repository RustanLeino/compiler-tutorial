// This Machine module simulates the execution of a CFG program. The machine has the
// following pieces:
//
//   * The CFG program that contains the code.
//   * A call stack. Each entry of the call stack is an _activation record_
//     "(locals, pc)", where
//       - "locals" is a map from (parameters and local) variables to values
//       - "pc" is the program counter, which is a BasicBlock and an index into
//         the instruction list of that BasicBlock
//   * A (global) evaluation stack, which is used to store intermediate values
//     during expression evaluation and to pass procedure parameters and result
//     values.
//
// Other than making changes to the call stack itself, the Machine makes changes
// only in the activation record at the top of the call stack. Therefore, the
// top of the call stack (fields "locals" and "pc" in class MachineState) is
// implemented separately from the rest of the call stack (field "returnStack"
// in class MachineState).
//
// The instructions themselves operate on the evaluation stack, get values into
// or out of local variables, and push/pop the call stack. This Machine does not
// have any registers, but if it did, the instructions would include some
// analogous "three-address codes".

module Machine {
  export
    provides Util, CFG
    provides Run

  import opened Util
  import AST
  import opened CFG

  method Run(program: Program, maxSteps: nat) returns (r: Result<int>)
  {
    var state := new MachineState(program);
    for i := 0 to maxSteps {
      var maybeResult :- state.Step();
      if maybeResult.Some? {
        return Success(maybeResult.value);
      }
    }
    return Failure("program required too many steps to run");
  }

  type LocalMap = map<AST.Variable, int>

  datatype ProgramCounter = ProgramCounter(bb: BasicBlock, nextInstruction: nat)

  class MachineState {
    const program: Program
    var locals: LocalMap
    var pc: ProgramCounter
    var returnStack: List<(LocalMap, ProgramCounter)>
    var evaluationStack: List<int>

    constructor (program: Program) {
      this.program := program;
      this.locals := map[];
      this.pc := ProgramCounter(program.routines[0].basicBlocks[0], 0);
      this.returnStack := Nil;
      this.evaluationStack := Nil;
    }

    method Pop() returns (r: Result<int>)
      modifies `evaluationStack
    {
      if evaluationStack == Nil {
        return Failure("pop of empty stack");
      }
      var n := evaluationStack.head;
      evaluationStack := evaluationStack.tail;
      return Success(n);
    }

    method Push(value: int)
      modifies `evaluationStack
    {
      evaluationStack := Cons(value, evaluationStack);
    }

    method Step() returns (r: Result<Option<int>>)
      modifies this
    {
      if pc.nextInstruction < |pc.bb.instructions| {
        var instruction := pc.bb.instructions[pc.nextInstruction];
        pc := pc.(nextInstruction := pc.nextInstruction + 1);
        var next :- DoInstruction(instruction);
        if next.Some? {
          locals, pc := next.value.0, next.value.1;
        }
        return Success(None);

      } else {
        match pc.bb.ending
        case Goto(target) =>
          pc := pc.(bb := target, nextInstruction := 0);
          return Success(None);

        case Return =>
          if returnStack == Nil {
            var result :- Pop();
            return Success(Some(result));
          }
          locals, pc, returnStack := returnStack.head.0, returnStack.head.1, returnStack.tail;
          return Success(None);
      }
    }

    method DoInstruction(instruction: Instruction) returns (r: Result<Option<(LocalMap, ProgramCounter)>>)
      modifies this
    {
      match instruction {
        case Load(variable) =>
          if variable !in locals {
            return Failure("use of undefined variable: " + variable.name);
          }
          Push(locals[variable]);

        case Store(variable) =>
          var value :- Pop();
          locals := locals[variable := value];

        case LoadLiteral(value) =>
          Push(value);

        case Subtract =>
          var e1 :- Pop();
          var e0 :- Pop();
          Push(e0 - e1);

        case Compare =>
          var e1 :- Pop();
          var e0 :- Pop();
          Push(if e0 <= e1 then 1 else 0);
        
        case BranchIfZero(target) =>
          var a :- Pop();
          if a == 0 {
            return Success(Some((locals, ProgramCounter(target, 0))));
          }

        case PreCall(_) =>
          // this is a no-op; see comment in Assembler.Assemble

        case Call(callee) =>
          if routine :| routine in program.routines && routine.procedure == callee {
            returnStack := Cons((locals, pc), returnStack);
            var pc' := ProgramCounter(routine.basicBlocks[0], 0);
            return Success(Some((map[], pc')));
          } else {
            return Failure("call to undefined routine: " + callee.name);
          }
      }

      return Success(None);
    }
  }

}