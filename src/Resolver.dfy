// The responsibility of the Resolver is to perform name resolution. This means figuring out
// what identifiers appearing in the program refer to. In this way, the Resolver turns a
// RawAST into a ("resolved") AST.
//
// Local variables are in scope until the end of the enclosing BlockStmt. An inner scope
// (that is, a BlockStmt inside another) is allowed to declare a variable with the same name
// as in an enclosing scope; in this case, the variable in the inner scope shadows the
// one in the outer scope, from the point of declaration until the end of the inner block.
//
// The resolver creates a unique identity for every procedure declaration, parameter declaration,
// and variable declaration. This is a great use of class instances (that is, _objects_) in the
// implementation, because the AST can then includes _references_ (that is, pointers) to those
// class instances. Some of those class instances also include mutable fields, which will be
// filled in or changed during later stages of the compiler pipeline.
//
// When creating variables, the resolver marks parameters as being immutable and local
// variables as being mutable.
//
// For more complicated input languages, it may be necessary to combine name resolution and
// type checking, or even type inference. But in this simple language, the types that are needed
// by Resolver are immidiately evident from the syntax.

module Resolver {
  export
    provides Util, RawAsts, AST
    provides Resolve

  import opened Util
  import opened AST
  import opened RawAsts

  method Resolve(ast: RawAst) returns (r: Result<Program>)
    ensures r.Success? ==> fresh(r.value.procedures)
    ensures r.Success? ==> |r.value.procedures| != 0
  {
    // Create an object for each procedure, and create a symbol table for these (that is, a
    // map from procedure names to these procedure-declaration objects).
    var procedures, procedureMap :- RegisterProcedures(ast.procedures);

    for i := 0 to |ast.procedures| {
      var _ :- ResolveProcedure(procedures[i], ast.procedures[i].statements, ast.procedures[i].returnExpr, procedureMap);
    }

    // Check for Main and move it first. This (is possible for the simple input language and) will
    // simplify the later stages of the compiler.
    if "Main" !in procedureMap.Keys {
      return Failure("program is missing Main procedure");
    }
    var main := procedureMap["Main"];
    if |main.parameters| != 0 {
      return Failure("Main procedure is expected to have 0 parameters");
    }
    var indexMain :| 0 <= indexMain < |procedures| && procedures[indexMain] == main;
    procedures := [main] + procedures[..indexMain] + procedures[indexMain + 1..];

    return Success(Program(procedures));
  }

  datatype Scope = Scope(procedures: map<string, Procedure>, locals: map<string, Variable>, currentScope: set<string>)
  {
    function FindProcedure(name: string): Result<Procedure> {
      if name in procedures.Keys then
        Success(procedures[name])
      else
        Failure("undeclared procedure: " + name)
    }

    function Find(name: string): Result<Variable> {
      if name in locals.Keys then
        Success(locals[name])
      else
        Failure("undeclared identifier: " + name)
    }

    function Add(variable: Variable): Result<Scope> {
      var name := variable.name;
      if name in currentScope then
        Failure("duplicate variable name: " + name)
      else
        var scope := this.(locals := locals[name := variable], currentScope := currentScope + {name});
        Success(scope)
    }

    function NestedScope(): Scope {
      Scope(procedures, locals, {})
    }
  }

  method RegisterProcedures(rawProcedures: seq<RawProcedure>) returns (r: Result<seq<Procedure>>, m: map<string, Procedure>)
    ensures r.Success? ==> fresh(r.value) && |r.value| == |rawProcedures|
    ensures r.Success? ==> forall name <- m.Keys :: m[name] in r.value
  {
    var procedures := [];
    m := map[];
    for i := 0 to |rawProcedures|
      invariant fresh(procedures)
      invariant |procedures| == i
      invariant forall name <- m.Keys :: m[name] in procedures
    {
      var raw := rawProcedures[i];
      if raw.name in m.Keys {
        return Failure("duplicate procedure name: " + raw.name), m;
      }
      var parameters: DistinctSeq<Variable> :- ResolveParameters(raw.parameters);
      var resultType :- ResolveType(raw.resultType);
      var p := new Procedure(raw.name, parameters, resultType);
      procedures := procedures + [p];
      m := m[raw.name := p];
    }
    return Success(procedures), m;
  }

  method ResolveParameters(rawParameters: seq<RawVarDecl>) returns (r: Result<DistinctSeq<Variable>>) {
    var parameters: DistinctSeq := [];
    var scope := Scope(map[], map[], {});
    for i := 0 to |rawParameters| {
      var raw := rawParameters[i];
      var typ :- ResolveType(raw.typ);
      var parameter := new Variable(raw.name, typ, false);
      parameters := parameters + [parameter];
      scope :- scope.Add(parameter);
    }
    return Success(parameters);
  }

  method ResolveType(rawType: RawType) returns (r: Result<Type>) {
    match rawType
    case Bool => return Success(AST.Bool);
    case Int => return Success(AST.Int);
  }

  method ResolveProcedure(p: Procedure, rawStatements: seq<RawStmt>, returnExpr: RawExpr,
                          procedureMap: map<string, Procedure>) returns (r: Result<()>)
    modifies p
  {
    var parameterMap := VariablesToMap(p.parameters);
    var scope := Scope(procedureMap, parameterMap, {});
    var statements;
    statements, scope :- ResolveStmtList(rawStatements, scope);

    var result :- ResolveExpr(returnExpr, scope);

    p.body := statements;
    p.result := result;
    return Success(());
  }

  method VariablesToMap(parameters: seq<Variable>) returns (m: map<string, Variable>) {
    m := map[];
    for i := 0 to |parameters| {
      var p := parameters[i];
      m := m[p.name := p];
    }
  }

  method ResolveStmtList(rawStatements: seq<RawStmt>, scopeIn: Scope) returns (r: Result<seq<Statement>>, scope: Scope) {
    var statements := [];
    scope := scopeIn;
    for i := 0 to |rawStatements| {
      var statement;
      statement, scope :- ResolveStatement(rawStatements[i], scope);
      statements := statements + [statement];
    }
    return Success(statements), scope;
  }

  method ResolveStatement(rawStatement: RawStmt, scopeIn: Scope) returns (r: Result<Statement>, scope: Scope) {
    var statement;
    scope := scopeIn;

    match rawStatement {
    case RawLocalVarDecl(name, initialExpr) =>
      var expr :- ResolveExpr(initialExpr, scope);
      var variable := new Variable(name, expr.Type(), true);
      scope :- scope.Add(variable);
      statement := VarDeclStmt(variable, expr);

    case RawAssign(lhs, rhs) =>
      var variable :- scope.Find(lhs);
      var expr :- ResolveExpr(rhs, scope);
      statement := AssignStmt(variable, expr);

    case RawCall(lhs, callee, arguments) =>
      var variable :- scope.Find(lhs);
      var proc :- scope.FindProcedure(callee);
      var exprs :- ResolveExprs(arguments, scope);
      statement := CallStmt(variable, proc, exprs);

    case RawIf(guard, thn, els) =>
      var condition :- ResolveExpr(guard, scope);
      var thenBranch, _ :- ResolveStmtList(thn, scope.NestedScope());
      var elseBranch, _ :- ResolveStmtList(els, scope.NestedScope());
      statement := IfStmt(condition, thenBranch, elseBranch);

    case RawBlockStmt(rawStatements) =>
      var statements, _ :- ResolveStmtList(rawStatements, scope.NestedScope());
      statement := BlockStmt(statements);
    }

    return Success(statement), scope;
  }

  method ResolveExprs(rawExpressions: seq<RawExpr>, scope: Scope) returns (r: Result<seq<Expression>>) {
    var expressions := [];
    for i := 0 to |rawExpressions| {
      var expr :- ResolveExpr(rawExpressions[i], scope);
      expressions := expressions + [expr];
    }
    return Success(expressions);
  }

  method ResolveExpr(rawExpression: RawExpr, scope: Scope) returns (r: Result<Expression>) {
    match rawExpression
    case RawLiteralExpr(n) =>
      return Success(LiteralExpr(n));
    case RawIdentifierExpr(name) =>
      var variable :- scope.Find(name);
      return Success(IdentifierExpr(variable));
    case RawMinus(e0, e1) =>
      var expr0 :- ResolveExpr(e0, scope);
      var expr1 :- ResolveExpr(e1, scope);
      return Success(MinusExpr(expr0, expr1));
    case RawAtMost(e0, e1) =>
      var expr0 :- ResolveExpr(e0, scope);
      var expr1 :- ResolveExpr(e1, scope);
      return Success(AtMostExpr(expr0, expr1));
  }

}