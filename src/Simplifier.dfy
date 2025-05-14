// The Simplifier demonstrates a simple static analysis and optimization that can be
// done to the AST. In particular:
//   * If an occurrence of a variable in an expression can be determined to always have
//     a fixed value, then that occurrence of the variable is replaced by the value.
//     This is known as _constant propagation_.
//   * If the operands of an expression are literals, then the expression is
//     replaced by the result of applying the operator to those literal arguments.
//     This is part of constant propagation, and is also a simple case of
//     _partial evaluation_.
//   * If the analysis can determine the value of the guard of an "if" statement,
//     then the "if" statement is replaced by its then branch or by its else branch.
//   * The analysis is intra-procedural. That is, no analysis information is shared
//     between procedures.
//
// The analysis changes the AST into a simpler one. The result may be an AST
// that is not legal as input. In particular, a LiteralExpr may, after the analysis,
// contain a negative integer, whereas the parsed input language does not allow
// that.
//
// After this analysis, the program may contain variables that are never used
// (or contain cliques of variables that are used only for assigning to variables
// within the clique). A further _dead variable_ analysis could remove such
// variable declarations.
//
// A slightly more advanced version of constant propagation is to keep track
// of ranges of values that variables can have.
//
// The static analysis performed by constant propagation and range analysis are
// examples of _abstract interpretation_. Since there are no loops in this simple
// input language, the abstract interpretation can be done using a single pass.
// In languages with loops (or to perform interprocedural analysis), the abstract
// interpretation iterates until it reaches a fixpoint.

module Simplifier {
  export
    provides AST
    provides Simplify

  import opened AST

  type ValueMap = map<Variable, int>

  method Simplify(program: Program)
    modifies program.procedures
  {
    for i := 0 to |program.procedures| {
      SimplifyProcedure(program.procedures[i]);
    }
  }

  method SimplifyProcedure(procedure: Procedure)
    modifies procedure
  {
    var simplifiedBody, knownValues := SimplifyStmtList(procedure.body, map[]);
    procedure.body := simplifiedBody;
    procedure.result := SimplifyExpr(procedure.result, knownValues);
  }

  method SimplifyStmtList(statements: seq<Statement>, knownValues: ValueMap) returns (ss: seq<Statement>, kv: ValueMap) {
    ss, kv := [], knownValues;
    for i := 0 to |statements| {
      var s;
      s, kv := SimplifyStatement(statements[i], kv);
      ss := ss + [s];
    }
  }

  method SimplifyStatement(statement: Statement, knownValues: ValueMap) returns (s: Statement, kv: ValueMap) {
    match statement
    case VarDeclStmt(variable, initialExpr) =>
      var expr := SimplifyExpr(initialExpr, knownValues);
      s := VarDeclStmt(variable, expr);
      kv := UpdateValueMap(variable, expr, knownValues);

    case AssignStmt(lhs, rhs) =>
      var expr := SimplifyExpr(rhs, knownValues);
      s := AssignStmt(lhs, expr);
      kv := UpdateValueMap(lhs, expr, knownValues);

    case CallStmt(lhs, callee, arguments) =>
      var simplifiedArguments := SimplifyExprList(arguments, knownValues);
      s := CallStmt(lhs, callee, simplifiedArguments);
      kv := knownValues - {lhs};

    case IfStmt(guard, thn, els) =>
      var condition := SimplifyExpr(guard, knownValues);
      var thenBranch, thenValues := SimplifyStmtList(thn, knownValues);
      var elseBranch, elseValues := SimplifyStmtList(els, knownValues);
      var comparingLiterals := condition.AtMostExpr? && condition.0.LiteralExpr? && condition.1.LiteralExpr?;
      if comparingLiterals && condition.0.value <= condition.1.value {
        return BlockStmt(thenBranch), thenValues;
      } else if comparingLiterals && condition.1.value < condition.0.value {
        return BlockStmt(elseBranch), elseValues;
      }
      s := IfStmt(condition, thenBranch, elseBranch);
      kv := MergeValueMaps(thenValues, elseValues);

    case BlockStmt(statements) =>
      var simplifiedStatements;
      simplifiedStatements, kv := SimplifyStmtList(statements, knownValues);
      s := BlockStmt(simplifiedStatements);
  }

  function UpdateValueMap(variable: Variable, rhs: Expression, knownValues: ValueMap): ValueMap {
    match rhs
    case LiteralExpr(x) =>
      knownValues[variable := x]
    case _ =>
      knownValues - {variable}
  }

  method MergeValueMaps(a: ValueMap, b: ValueMap) returns (kv: ValueMap) {
    var commonKeys := a.Keys * b.Keys;
    return map k | k in commonKeys && a[k] == b[k] :: a[k];
  }

  method SimplifyExprList(expressions: seq<Expression>, knownValues: ValueMap) returns (ee: seq<Expression>) {
    ee := [];
    for i := 0 to |expressions| {
      var e := SimplifyExpr(expressions[i], knownValues);
      ee := ee + [e];
    }
  }

  method SimplifyExpr(expr: Expression, knownValues: ValueMap) returns (e: Expression) {
    match expr
    case LiteralExpr(_) =>
      return expr;

    case IdentifierExpr(variable) =>
      if variable in knownValues {
        return LiteralExpr(knownValues[variable]);
      } else {
        return expr;
      }

    case MinusExpr(e0, e1) =>
      var expr0 := SimplifyExpr(e0, knownValues);
      var expr1 := SimplifyExpr(e1, knownValues);
      match (expr0, expr1) {
        case (LiteralExpr(x), LiteralExpr(y)) =>
          return LiteralExpr(x - y);
        case _ =>
          return MinusExpr(expr0, expr1);
      }

    case AtMostExpr(e0, e1) =>
      var expr0 := SimplifyExpr(e0, knownValues);
      var expr1 := SimplifyExpr(e1, knownValues);
      return AtMostExpr(expr0, expr1);
  }
}
