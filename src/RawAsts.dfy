// RawAst is an abstract syntax tree (AST) that reflects the structure of the parsed program.
// The AST is "raw" in that it does not carry information about, for example, what identifiers
// stand for or what types expressions have.

module RawAsts {
  export
    reveals RawAst, RawProcedure, RawVarDecl, RawType, RawStmt, RawExpr

  datatype RawAst = RawAst(procedures: seq<RawProcedure>)
  datatype RawProcedure = RawProcedure(
    name: string,
    parameters: seq<RawVarDecl>,
    resultType: RawType,
    statements: seq<RawStmt>,
    returnExpr: RawExpr)
  datatype RawVarDecl = RawVarDecl(name: string, typ: RawType)
  datatype RawType = Bool | Int
  datatype RawStmt =
    | RawLocalVarDecl(name: string, initialExpr: RawExpr)
    | RawAssign(lhs: string, rhs: RawExpr)
    | RawCall(lhs: string, callee: string, arguments: seq<RawExpr>)
    | RawIf(guard: RawExpr, thn: seq<RawStmt>, els: seq<RawStmt>)
    | RawBlockStmt(statements: seq<RawStmt>)
  datatype RawExpr =
    | RawLiteralExpr(n: nat)
    | RawIdentifierExpr(name: string)
    | RawMinus(0: RawExpr, 1: RawExpr)
    | RawAtMost(0: RawExpr, 1: RawExpr)

}