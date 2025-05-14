import opened Util

// Rustan Leino, September 2023.
//
// Main in the entry point to the compiler. The Run method below calls out to
// the pipeline of stages of the compiler.

method Main(arguments: seq<string>) {
  if |arguments| == 0 {
    ReportError("usage: Compiler <filename>");
    return;
  }

  var outcome := Run(arguments[|arguments| - 1]);
  match outcome
  case Success(_) =>
  case Failure(error) => ReportError(error);
}

method ReportError(error: string) {
  print "Error: ", error, "\n";
}

method Run(filename: string) returns (r: Result<()>) {
  var text :- Util.ReadInput(filename);
  var tokens :- Lexer.Lex(text);
  print "===== Tokens:\n", tokens, "\n";

  var input := new TokenReader.TokenReader(tokens);
  var rawAst :- Parser.Parse(input);
  print "===== Raw program:\n";
  RawPrinter.Print(rawAst);

  var program :- Resolver.Resolve(rawAst);
  print "===== Resolved program:\n";
  Printer.Print(program);

  var outcome := TypeChecker.TypeCheck(program);
  var _ :- outcome.ToResult();

  Simplifier.Simplify(program);
  print "===== Simplified program:\n";
  Printer.Print(program);

  var cfg := Compiler.Compile(program);
  print "===== Target program:\n";
  CfgPrinter.Print(cfg);

  print "Running on Machine...\n";
  var n :- Machine.Run(cfg, 1000);
  print n, "\n";

  print "===== Assembly program:\n";
  var asm :- Assembler.Assemble(cfg);
  AsmPrinter.Print(asm);

  print "Running on RawMachine...\n";
  var stack :- RawMachine.Run(asm.code, 1000);
  print stack, "\n";
  
  return Success(());
}