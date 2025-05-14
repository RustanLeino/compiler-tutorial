// This module pretty prints the AST.
//
// It prints types of local variables.
// It prints parentheses in expressions only when these are necessary.
//
// What is printed may be a program that would not be accepted by the parser.
// In particular, the inferred types of local variables are not allowed in
// the grammar of the simple language. As another example, the Printer is
// happy to print negative LiteralExpr's (which may exist after the Simplifier
// has run), but the parser does not accept such literals (or unary-minus
// expression). One could modify this Printer to always print the program
// as one that can be parsed (by omitting types of local variables and by
// printing, say, -7 as 0-7).

module Printer {
  export
    provides AST, Print

  import AST

  const IndentLevel := 2

  method Indent(n: nat) {
    print seq(n, _ => ' ');
  }

  method Print(ast: AST.Program) {
    for i := 0 to |ast.procedures| {
      var p := ast.procedures[i];
      print "procedure ", p.name, "(";
      PrintVariables(p.parameters);
      print "): ";
      PrintType(p.resultType);
      print " {\n";
      PrintStmtList(p.body, IndentLevel);
      Indent(IndentLevel);
      print "return ";
      PrintExpr(p.result);
      print "\n}\n";
    }
  }

  method PrintVariables(variables: seq<AST.Variable>) {
    var sep := "";
    for i := 0 to |variables| {
      print sep;
      PrintVariable(variables[i]);
      sep := ", ";
    }
  }

  method PrintVariable(variable: AST.Variable) {
    print variable.name, ": ";
    PrintType(variable.typ);
  }

  method PrintType(typ: AST.Type) {
    match typ
    case Bool => print "bool";
    case Int => print "int";
  }

  method PrintStmtList(statements: seq<AST.Statement>, indent: nat) {
    for i := 0 to |statements| {
      PrintStmt(statements[i], indent);
    }
  }

  method PrintStmt(statement: AST.Statement, indent: nat)
    decreases statement, 1
  {
    Indent(indent);
    match statement {
      case VarDeclStmt(variable, initialExpr) =>
        print "var ";
        PrintVariable(variable);
        print " := ";
        PrintExpr(initialExpr);
      case AssignStmt(lhs, rhs) =>
        print lhs.name, " := ";
        PrintExpr(rhs);
      case CallStmt(lhs, callee, arguments) =>
        print lhs.name, " := ", callee.name, "(";
        PrintExprList(arguments);
        print ")";
      case IfStmt(guard, thn, els) =>
        print "if ";
        PrintExpr(guard);
        print " ";
        PrintBlockStmt(thn, indent, statement);
        if |els| != 0 {
          print " else ";
          PrintBlockStmt(els, indent, statement);
        }
      case BlockStmt(statements) =>
        PrintBlockStmt(statements, indent, statement);
    }
    print "\n";
  }

  method PrintBlockStmt(statements: seq<AST.Statement>, indent: nat, ghost parent: AST.Statement)
    requires forall i :: 0 <= i < |statements| ==> statements[i] < parent
    decreases parent, 0
  {
    print "{\n";
    for i := 0 to |statements| {
      PrintStmt(statements[i], indent + IndentLevel);
    }
    Indent(indent);
    print "}";
  }

  method PrintExprList(expressions: seq<AST.Expression>) {
    var sep := "";
    for i := 0 to |expressions| {
      print sep;
      PrintExpr(expressions[i]);
      sep := ", ";
    }
  }

  method PrintExpr(expr: AST.Expression, enclosingBindingStrength: nat := 0) {
    match expr
    case LiteralExpr(n) =>
      print n;
    case IdentifierExpr(variable) =>
      print variable.name;
    case MinusExpr(e0, e1) =>
      if 2 <= enclosingBindingStrength {
        print "(";
      }
      PrintExpr(e0, 1);
      print " - ";
      PrintExpr(e1, 2);
      if 2 <= enclosingBindingStrength {
        print ")";
      }
    case AtMostExpr(e0, e1) =>
      if 1 <= enclosingBindingStrength {
        print "(";
      }
      PrintExpr(e0, 1);
      print " <= ";
      PrintExpr(e1, 1);
      if 1 <= enclosingBindingStrength {
        print ")";
      }
  }
}