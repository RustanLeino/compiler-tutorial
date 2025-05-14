// CFG declares the data structure for a Control-Flow Graph. The vertices of a CFG are
// _basic blocks_, each of which contains a list of instructions. In this way, a CFG is
// usually a piece of straightline code with no internal jumps. The CFG here is a slight
// variation thereof, where the almost-straightline code can include conditional jumps.
// That is, the list of instructions in a BasicBlock can include condition-jump instructions.
//
// A BasicBlock ends with either a goto to another BasicBlock or an indication that
// the execution of the enclosing procedure has completed.
//
// The instruction set is for a simple machine with a call stack and an evaluation stack,
// see module Machine.

module CFG {
  export
    provides Util, AST
    reveals Program, Routine, BasicBlock, Instruction, EndInstruction
    provides BasicBlock.Emit, BasicBlock.id, BasicBlock.instructions, BasicBlock.ending

  import opened Util
  import AST

  datatype Program = Program(routines: NonemptySeq<Routine>)

  datatype Routine = Routine(procedure: AST.Procedure, basicBlocks: NonemptySeq<BasicBlock>)

  class BasicBlock {
    const id: nat
    var instructions: seq<Instruction>
    var ending: EndInstruction

    constructor (id: nat) {
      this.id := id;
      instructions := [];
      ending := Return;
    }

    method Emit(instruction: Instruction)
      modifies this
    {
      instructions := instructions + [instruction];
    }
  }

  datatype Instruction =
    | Load(variable: AST.Variable)
    | Store(variable: AST.Variable)
    | LoadLiteral(value: int)
    | Subtract
    | Compare
    | BranchIfZero(target: BasicBlock)
    | PreCall(callee: AST.Procedure) // this is a no-op for Machine; see comment in Assembler.Assemble
    | Call(callee: AST.Procedure)

  datatype EndInstruction =
    | Goto(target: BasicBlock)
    | Return

}