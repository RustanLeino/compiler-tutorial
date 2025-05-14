// This module translates an AST program into a CFG program. This involves creating
// basic blocks and the instructions inside basic blocks. The result can be executed
// on the Machine.

module Compiler {
  export
    provides Util, AST, CFG
    provides Compile

  import opened Util
  import opened AST
  import opened CFG

  method Compile(program: AST.Program) returns (cfg: CFG.Program)
    requires |program.procedures| != 0
  {
    var routines := [];
    for i := 0 to |program.procedures|
      invariant |routines| == i
    {
      var routine := CompileProcedure(program.procedures[i]);
      routines := routines + [routine];
    }
    return CFG.Program(routines);
  }

  class State {
    var startBlock: BasicBlock
    var basicBlocks: NonemptySeq<BasicBlock>

    constructor ()
      ensures fresh(startBlock)
    {
      startBlock := new BasicBlock(0);
      basicBlocks := [startBlock];
    }

    method GetNewBlock() returns (bb: BasicBlock)
      modifies this
      ensures fresh(bb)
    {
      bb := new BasicBlock(|basicBlocks|);
      basicBlocks := basicBlocks + [bb];
    }
  }

  method CompileProcedure(procedure: Procedure) returns (routine: Routine) {
    var state := new State();
    var start := state.startBlock;

    // move parameters from stack to locals
    for i := |procedure.parameters| downto 0 {
      var parameter := procedure.parameters[i];
      start.Emit(Store(parameter));
    }

    var bb := CompileStmtList(procedure.body, start, state);
    CompileExpr(procedure.result, bb);
    bb.ending := Return;

    return Routine(procedure, state.basicBlocks);
  }

  method CompileStmtList(statements: seq<Statement>, bb: BasicBlock, state: State) returns (current: BasicBlock)
    modifies bb, state
    ensures current == bb || fresh(current)
  {
    current := bb;
    for i := 0 to |statements|
      invariant current == bb || fresh(current)
    {
      current := CompileStatement(statements[i], current, state);
    }
  }

  method CompileStatement(statement: Statement, bb: BasicBlock, state: State) returns (current: BasicBlock)
    modifies bb, state
    ensures current == bb || fresh(current)
  {
    match statement
    case VarDeclStmt(variable, initialExpr) =>
      CompileExpr(initialExpr, bb);
      bb.Emit(Store(variable));
      return bb;

    case AssignStmt(lhs, rhs) =>
      CompileExpr(rhs, bb);
      bb.Emit(Store(lhs));
      return bb;

    case CallStmt(lhs, callee, arguments) =>
      bb.Emit(PreCall(callee));
      CompileExprList(arguments, bb);
      bb.Emit(Call(callee));
      bb.Emit(Store(lhs));
      return bb;

    case IfStmt(guard, thn, els) =>
      CompileExpr(guard, bb);
      var elseBlock := state.GetNewBlock();
      var joinBlock := state.GetNewBlock();

      bb.Emit(BranchIfZero(elseBlock));
      current := CompileStmtList(thn, bb, state);
      current.ending := Goto(joinBlock);

      current := CompileStmtList(els, elseBlock, state);
      current.ending := Goto(joinBlock);

      return joinBlock;

    case BlockStmt(statements) =>
      current := CompileStmtList(statements, bb, state);
  }

  method CompileExprList(expressions: seq<Expression>, bb: BasicBlock)
    modifies bb
  {
    for i := 0 to |expressions| {
      CompileExpr(expressions[i], bb);
    }
  }

  method CompileExpr(expr: Expression, bb: BasicBlock)
    modifies bb
  {
    match expr
    case LiteralExpr(x) =>
      bb.Emit(LoadLiteral(x));
    case IdentifierExpr(variable) =>
      bb.Emit(Load(variable));
    case MinusExpr(e0, e1) =>
      CompileExpr(e0, bb);
      CompileExpr(e1, bb);
      bb.Emit(Subtract);
    case AtMostExpr(e0, e1) =>
      CompileExpr(e0, bb);
      CompileExpr(e1, bb);
      bb.Emit(Compare);
  }

}