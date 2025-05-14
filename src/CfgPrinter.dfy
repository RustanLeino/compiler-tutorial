// This module prints a given CFG program.

module CfgPrinter {
  export
    provides Util, CFG
    provides Print

  import opened Util
  import AST
  import opened CFG

  method Print(cfg: Program) {
    for i := 0 to |cfg.routines| {
      PrintRoutine(cfg.routines[i]);
    }
  }

  method PrintRoutine(routine: Routine) {
    for i := 0 to |routine.basicBlocks| {
      PrintBasicBlock(routine.basicBlocks[i], routine.procedure);
    }
  }

  method PrintBasicBlock(bb: BasicBlock, context: AST.Procedure) {
    PrintBlockName(context, bb.id);
    print ":\n";
    for i := 0 to |bb.instructions| {
      print "  ";
      PrintInstruction(bb.instructions[i], context);
      print "\n";
    }
    match bb.ending
    case Goto(target) =>
      print "  GOTO ";
      PrintBlockName(context, target.id);
      print "\n";
    case Return =>
      print "  RETURN\n";
  }

  method PrintBlockName(context: AST.Procedure, id: nat) {
    print context.name, "_", id;
  }

  method PrintInstruction(instruction: Instruction, context: AST.Procedure) {
    match instruction
    case Load(variable) =>
      print "LOAD ", variable.name;
    case Store(variable) =>
      print "STORE ", variable.name;
    case LoadLiteral(value) =>
      print "LOADLIT ", value;
    case Subtract =>
      print "SUBTRACT";
    case Compare =>
      print "COMPARE";
    case BranchIfZero(target) =>
      print "IFZ ";
      PrintBlockName(context, target.id);
    case PreCall(callee) =>
      print "// PRE-CALL ";
      PrintBlockName(callee, 0);
    case Call(callee) =>
      print "CALL ";
      PrintBlockName(callee, 0);
  }
}