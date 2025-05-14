// This module contains the main AST for the program. This AST is similar to the RawAST,
// but contains references to procedure/variable declarations instead of just the names
// of these procedures/variables.

module AST {
  class Variable {
    const name: string
    const typ: Type
    const writable: bool

    constructor (name: string, typ: Type, writable: bool) {
      this.name := name;
      this.typ := typ;
      this.writable := writable;
    }
  }

  type DistinctSeq<X> = s: seq<X> | forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]

  class Procedure {
    const name: string
    const parameters: DistinctSeq<Variable>
    const resultType: Type
    var body: seq<Statement>
    var result: Expression

    constructor (name: string, parameters: DistinctSeq<Variable>, resultType: Type) {
      this.name := name;
      this.parameters := parameters;
      this.resultType := resultType;
    }
  }

  datatype Type = Bool | Int
  {
    function ToString(): string {
      match this
      case Bool => "bool"
      case Int => "int"
    }
  }

  datatype Program = Program(procedures: seq<Procedure>)
 
  datatype Statement =
    | VarDeclStmt(variable: Variable, initialExpr: Expression)
    | AssignStmt(lhs: Variable, rhs: Expression)
    | CallStmt(lhs: Variable, callee: Procedure, arguments: seq<Expression>)
    | IfStmt(guard: Expression, thn: seq<Statement>, els: seq<Statement>)
    | BlockStmt(statements: seq<Statement>)

  datatype Expression =
    | LiteralExpr(value: int)
    | IdentifierExpr(variable: Variable)
    | MinusExpr(0: Expression, 1: Expression)
    | AtMostExpr(0: Expression, 1: Expression)
  {
    function Type(): Type {
      match this
      case LiteralExpr(_) => Int
      case IdentifierExpr(variable) => variable.typ
      case MinusExpr(_, _) => Int
      case AtMostExpr(_, _) => Bool
    }
  }

}