// The Parser turns a sequence of tokens into a "raw" abstract syntax tree (AST).
//
// The grammar of the concrete syntax is:
//
//   Program ::= Procedure^*
//   Procedure ::= "procedure" Identifier "(" VarDecl^,* ")" ":" Type
//                 "{"
//                   Stmt^*
//                   "return" Expr
//                 "}"
//   VarDecl ::= Identifier ":" Type
//
//   Stmt ::=
//     | "var" Identifier ":=" Expr
//     | Identifer ":=" Expr
//     | Identifier ":=" Identifier "(" Expr^,* ")"
//     | "if" Expr BlockStmt [ "else" BlockStmt ]
//     | BlockStmt
//   BlockStmt := "{" Stmt^* "}"
//
//   Expr ::= ArithExpr [ "<=" ArithExpr ]
//   ArithExpr ::= [ ArithExpr "-" ] AtomicExpr
//   AtomicExpr ::= Literal | Identifier | "(" Expr ")"
//
// Legend:
//   X^*   means 0 or more occurrences of X
//   X^,*  means 0 or more comma-separated occurrences of X
//   X^,+  means 1 or more comma-separated occurrences of X
//   [ X ] means 0 or 1 occurrence of X
//
// Notes:
//   * To determine if the input contains another statement or not, the parser uses
//     the predicate IsStartOfStmt. It is often called the "start set" of a grammar
//     production.
//   * "if" statements in the abstract syntax tree always have an "else" branch, whereas
//     the concrete syntax may omit it.
//   * The breakdown of expressions into several productions (Expr, ArithExpr, AtomicExpr),
//     the grammar encodes the relative precedence levels of operators.
//   * There is a difference in how "<=" and "-" expressions are parsed. The comparison
//     is not associative, so parsing it is simple. The "-" operator is associative, so
//     parsing it involves recursion. Because it is left-associative, the corresponding
//     grammar production looks like it starts with a recursive call. Implementing it
//     that way would lead to infinite recursion, so the grammar production is instead
//     implemented by a loop that gathers operands up into the left argument.
//   * Parentheses in expressions are discarded by the parser. That is, parentheses (as
//     as well other punctuation) are not represented in the AST.

module Parser {
  export
    provides Util, Tokens, TR, RawAsts
    provides Parse

  import opened Util
  import opened Tokens
  import opened RawAsts
  import TR = TokenReader

  method Parse(input: TR.TokenReader) returns (r: Result<RawAst>)
    modifies input
  {
    // Program ::= Procedure^*
    var procedures := [];
    var i := 0;
    while input.Peek() != Token.EOF
      decreases input.Remaining()
    {
      var procedure :- ParseProcedure(input);
      procedures := procedures + [procedure];
    }

    return Success(RawAst(procedures));
  }

  // Procedure ::= "procedure" Identifier "(" VarDecl^,+ ")" ":" Type "{" Stmt^* "return" Expr "}"
  method ParseProcedure(input: TR.TokenReader) returns (r: Result<RawProcedure>)
    modifies input
    ensures r.Success? ==> input.Progress()
  {
    var _ :- input.Expect(Token.Procedure);
    var name :- input.ExpectIdent();
    var _ :- input.Expect(Token.Open);
    var parameters;
    if input.Peek() == Token.Close {
      parameters := [];
    } else {
      parameters :- ParseVarDeclList(input);
    }
    var _ :- input.Expect(Token.Close);
    var resultType :- ParseColonType(input);
    var _ :- input.Expect(Token.OpenCurly);
    var statements :- ParseStmtList(input);
    var _ :- input.Expect(Token.Return);
    var returnExpr :- ParseExpr(input);
    var _ :- input.Expect(Token.CloseCurly);

    return Success(RawProcedure(name, parameters, resultType, statements, returnExpr));
  }

  // VarDeclList ::= VarDecl^,+
  method ParseVarDeclList(input: TR.TokenReader) returns (r: Result<seq<RawVarDecl>>)
    modifies input
    ensures r.Success? ==> input.Progress()
  {
    var decl :- ParseVarDecl(input);
    var decls := [decl];
    while input.Peek() == Token.Comma
      decreases input.Remaining()
    {
      var _ :- assert input.Expect(Token.Comma);
      decl :- ParseVarDecl(input);
      decls := decls + [decl];
    }
    return Success(decls);
  }

  // VarDecl ::= Identifier ":" Type
  method ParseVarDecl(input: TR.TokenReader) returns (r: Result<RawVarDecl>)
    modifies input
    ensures r.Success? ==> input.Progress()
  {
    var name :- input.ExpectIdent();
    var typ :- ParseColonType(input);
    return Success(RawVarDecl(name, typ));
  }

  // ColonType ::= ":" Type
  method ParseColonType(input: TR.TokenReader) returns (r: Result<RawType>)
    modifies input
    ensures r.Success? ==> input.Progress()
  {
    var _ :- input.Expect(Token.Colon);
    var typ := input.Next();
    match typ
    case Bool =>
      return Success(RawType.Bool);
    case Int =>
      return Success(RawType.Int);
    case _ =>
      return Failure("expected type, got " + typ.ToString());
  }

  predicate IsStartOfStmt(token: Token) {
    || token == Token.Var
    || token.Identifier?
    || token == Token.If
    || token == Token.OpenCurly
  }

  // StmtList ::= Stmt^*
  method ParseStmtList(input: TR.TokenReader) returns (r: Result<seq<RawStmt>>)
    modifies input
    ensures r.Success? ==> input.ProgressNonStrict()
    decreases input.Remaining(), 2
  {
    var statements := [];
    while IsStartOfStmt(input.Peek())
      decreases input.Remaining()
    {
      var stmt :- ParseStmt(input);
      statements := statements + [stmt];
    }
    return Success(statements);
  }

  // Stmt ::=
  //   | "var" Identifier ":=" Expr
  //   | Identifer ":=" Expr
  //   | Identifier ":=" Identifier "(" ExprList ")"
  //   | "if" Expr BlockStmt [ "else" BlockStmt ]
  //   | BlockStmt
  method ParseStmt(input: TR.TokenReader) returns (r: Result<RawStmt>)
    requires IsStartOfStmt(input.Peek())
    modifies input
    ensures r.Success? ==> input.Progress()
    decreases input.Remaining(), 1
  {
    match input.Peek()
    case Var =>
      var _ :- assert input.Expect(Token.Var);
      var name :- input.ExpectIdent();
      var _ :- input.Expect(Token.Gets);
      var init :- ParseExpr(input);
      return Success(RawLocalVarDecl(name, init));

    case Identifier(_) =>
      var lhs :- assert input.ExpectIdent();
      var _ :- input.Expect(Token.Gets);
      if input.Peek(0).Identifier? && input.Peek(1) == Token.Open {
        // RHS is a procedure call
        var callee :- assert input.ExpectIdent();
        var _ :- input.Expect(Token.Open);
        var arguments;
        if input.Peek() == Token.Close {
          arguments := [];
        } else {
          arguments :- ParseExprList(input);
        }
        var _ :- input.Expect(Token.Close);
        return Success(RawCall(lhs, callee, arguments));
      } else {
        // RHS is, we expect, an expression
        var rhs :- ParseExpr(input);
        return Success(RawAssign(lhs, rhs));
      }

    case If =>
      var _ :- assert input.Expect(Token.If);
      var guard :- ParseExpr(input);
      var thn :- ParseBlockStmt(input);
      var els := [];
      if input.Peek() == Token.Else {
        var _ :- assert input.Expect(Token.Else);
        els :- ParseBlockStmt(input);
      }
      return Success(RawIf(guard, thn, els));

    case OpenCurly =>
      var statements :- ParseBlockStmt(input);
      return Success(RawBlockStmt(statements));
  }

  // BlockStmt ::= "{" Stmt^* "}"
  method ParseBlockStmt(input: TR.TokenReader) returns (r: Result<seq<RawStmt>>)
    modifies input
    ensures r.Success? ==> input.Progress()
    decreases input.Remaining(), 0
  {
    var _ :- input.Expect(Token.OpenCurly);
    var statements :- ParseStmtList(input);
    var _ :- input.Expect(Token.CloseCurly);
    return Success(statements);
  }

  // ExprList ::= Expr^,+
  method ParseExprList(input: TR.TokenReader) returns (r: Result<seq<RawExpr>>)
    modifies input
    ensures r.Success? ==> input.Progress()
  {
    var expr :- ParseExpr(input);
    var expressions := [expr];
    while input.Peek() == Token.Comma
      decreases input.Remaining()
    {
      var _ :- assert input.Expect(Token.Comma);
      var expr :- ParseExpr(input);
      expressions := expressions + [expr];
    }
    return Success(expressions);
  }

  // Expr ::= ArithExpr [ "<=" ArithExpr ]
  method ParseExpr(input: TR.TokenReader) returns (r: Result<RawExpr>)
    modifies input
    ensures r.Success? ==> input.Progress()
    decreases input.Remaining(), 2
  {
    var e0 :- ParseArithExpr(input);

    if input.Peek() == Token.AtMost {
      var _ :- assert input.Expect(Token.AtMost);
      var e1 :- ParseArithExpr(input);
      e0 := RawAtMost(e0, e1);
    }

    return Success(e0);
  }

  // ArithExpr ::= [ ArithExpr "-" ] AtomicExpr
  method ParseArithExpr(input: TR.TokenReader) returns (r: Result<RawExpr>)
    modifies input
    ensures r.Success? ==> input.Progress()
    decreases input.Remaining(), 1
  {
    var e0 :- ParseAtomicExpr(input);

    while input.Peek() == Token.Minus
      decreases input.Remaining()
    {
      var _ :- assert input.Expect(Token.Minus);
      var e1 :- ParseAtomicExpr(input);
      e0 := RawMinus(e0, e1);
    }

    return Success(e0);
  }

  // AtomicExpr ::= Literal | Identifier | "(" Expr ")"
  method ParseAtomicExpr(input: TR.TokenReader) returns (r: Result<RawExpr>)
    modifies input
    ensures r.Success? ==> input.Progress()
    decreases input.Remaining(), 0
  {
    var next := input.Next();
    match next
    case Literal(n) =>
      return Success(RawLiteralExpr(n));
    case Identifier(name) =>
      return Success(RawIdentifierExpr(name));
    case Open =>
      var e :- ParseExpr(input);
      var _ :- input.Expect(Token.Close);
      return Success(e);
    case _ =>
      return Failure("expected AtomicExpr, got " + next.ToString());
  }
}