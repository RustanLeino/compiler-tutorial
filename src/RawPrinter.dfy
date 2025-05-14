// RawPrinter pretty prints a RawAst. Its purpose is to display the result of the parser.
// Therefore, it fully parenthesizes expressions.

module RawPrinter {
  export
    provides RawAsts
    provides Print

  import opened RawAsts

  const IndentLevel := 2

  method Indent(n: nat) {
    print seq(n, _ => ' ');
  }

  method Print(ast: RawAst) {
    for i := 0 to |ast.procedures| {
      var p := ast.procedures[i];
      print "procedure ", p.name, "(";
      PrintVarDecls(p.parameters);
      print "): ";
      PrintType(p.resultType);
      print " {\n";
      PrintStmtList(p.statements, IndentLevel);
      Indent(IndentLevel);
      print "return ";
      PrintExpr(p.returnExpr);
      print "\n}\n";
    }
  }

  method PrintVarDecls(variables: seq<RawVarDecl>) {
    var sep := "";
    for i := 0 to |variables| {
      var v := variables[i];
      print sep, v.name, ": ";
      PrintType(v.typ);
      sep := ", ";
    }
  }

  method PrintType(typ: RawType) {
    match typ
    case Bool => print "bool";
    case Int => print "int";
  }

  method PrintStmtList(statements: seq<RawStmt>, indent: nat) {
    for i := 0 to |statements| {
      PrintStmt(statements[i], indent);
    }
  }

  method PrintStmt(statement: RawStmt, indent: nat)
    decreases statement, 1
  {
    Indent(indent);
    match statement {
      case RawLocalVarDecl(name, initialExpr) =>
        print "var ", name, " := ";
        PrintExpr(initialExpr);
      case RawAssign(lhs, rhs) =>
        print lhs, " := ";
        PrintExpr(rhs);
      case RawCall(lhs, callee, arguments) =>
        print lhs, " := ", callee, "(";
        PrintExprList(arguments);
        print ")";
      case RawIf(guard, thn, els) =>
        print "if ";
        PrintExpr(guard);
        print " ";
        PrintBlockStmt(thn, indent, statement);
        if |els| != 0 {
          print " else ";
          PrintBlockStmt(els, indent, statement);
        }
      case RawBlockStmt(statements) =>
        PrintBlockStmt(statements, indent, statement);
    }
    print "\n";
  }

  method PrintBlockStmt(statements: seq<RawStmt>, indent: nat, ghost parent: RawStmt)
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

  method PrintExprList(expressions: seq<RawExpr>) {
    var sep := "";
    for i := 0 to |expressions| {
      print sep;
      PrintExpr(expressions[i]);
      sep := ", ";
    }
  }

  method PrintExpr(expr: RawExpr) {
    match expr
    case RawLiteralExpr(n) =>
      print n;
    case RawIdentifierExpr(name) =>
      print name;
    case RawMinus(e0, e1) =>
      print "(";
      PrintExpr(e0);
      print " - ";
      PrintExpr(e1);
      print ")";
    case RawAtMost(e0, e1) =>
      print "(";
      PrintExpr(e0);
      print " <= ";
      PrintExpr(e1);
      print ")";
  }
}