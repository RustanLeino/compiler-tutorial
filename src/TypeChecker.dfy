// TypeChecker computes types for expressions and checks that statements and expressions
// use variables, procedures, and expressions in a way that respects the types. It also
// checks that only mutable variables (which in the simple input language corresponds
// to local variables) are assigned.

module TypeChecker {
  export
    provides Util, AST
    provides TypeCheck

  import opened Util
  import opened AST

  method TypeCheck(program: Program) returns (r: Outcome) {
    for i := 0 to |program.procedures| {
      :- TypeCheckProcedure(program.procedures[i]);
    }
    return Pass;
  }

  method TypeCheckProcedure(procedure: Procedure) returns (r: Outcome) {
    :- TypeCheckStmtList(procedure.body);
    :- ExpectTypesEqual(procedure.resultType, procedure.result.Type(), "procedure result");
    return Pass;
  }

  method TypeCheckStmtList(statements: seq<Statement>) returns (r: Outcome) {
    for i := 0 to |statements| {
      :- TypeCheckStatement(statements[i]);
    }
    return Pass;
  }

  method TypeCheckStatement(statement: Statement) returns (r: Outcome) {
    match statement {
      case VarDeclStmt(variable, initialExpr) =>
        :- TypeCheckExpr(initialExpr);
        // no need to check the variable's type, since it was inferred from "initialExpr" during resolution

      case AssignStmt(lhs, rhs) =>
        :- TypeCheckExpr(rhs);
        :- ExpectTypesEqual(lhs.typ, rhs.Type(), "assignment");
        :- ExpectWritable(lhs);

      case CallStmt(lhs, callee, arguments) =>
        if |callee.parameters| != |arguments| {
          return Fail("wrong number of arguments pass to procedure: " + callee.name);
        }
        for i := 0 to |arguments| {
          var formal, actual := callee.parameters[i], arguments[i];
          :- TypeCheckExpr(actual);
          :- ExpectTypesEqual(formal.typ, actual.Type(), "parameter " + formal.name + " to procedure " + callee.name);
        }
        :- ExpectTypesEqual(lhs.typ, callee.resultType, "result of procedure " + callee.name);
        :- ExpectWritable(lhs);

      case IfStmt(guard, thn, els) =>
        :- TypeCheckExpr(guard);
        :- ExpectTypesEqual(Bool, guard.Type(), "if guard");
        :- TypeCheckStmtList(thn);
        :- TypeCheckStmtList(els);

      case BlockStmt(statements) =>
        :- TypeCheckStmtList(statements);
    }

    return Pass;
  }

  method TypeCheckExpr(expression: Expression) returns (r: Outcome) {
    match expression {
      case LiteralExpr(_) =>
      case IdentifierExpr(_) =>
      case MinusExpr(e0, e1) =>
        :- TypeCheckExpr(e0);
        :- TypeCheckExpr(e1);
        :- ExpectTypesEqual(Int, e0.Type(), "left argument to -");
        :- ExpectTypesEqual(Int, e1.Type(), "right argument to -");
      case AtMostExpr(e0, e1) =>
        :- TypeCheckExpr(e0);
        :- TypeCheckExpr(e1);
        :- ExpectTypesEqual(Int, e0.Type(), "left argument to <=");
        :- ExpectTypesEqual(Int, e1.Type(), "right argument to <=");
    }

    return Pass;
  }

  method ExpectTypesEqual(expectedType: Type, typ: Type, context: string) returns (r: Outcome) {
    if typ == expectedType {
      return Pass;
    } else {
      return Fail("incorrect type: got " + typ.ToString() + ", expected " + expectedType.ToString() + " as " + context);
    }
  }

  method ExpectWritable(variable: Variable) returns (r: Outcome) {
    if variable.writable {
      return Pass;
    } else {
      return Fail("illegal assignment to non-writable variable: " + variable.name);
    }
  }

}