# compiler-tutorial

This repo contains a simple compiler pipeline, from parsing to running target code. Its purpose
is to be a tutorial of the various stages of a common compiler pipeline. It shows how a text file
(that is, a stream of characters) is turned into assembly instructions that can be executed
on a machine.

The tutorial compiler uses a toy language that illustrates imperative programs with control
flow (`if` statements, but no loops) and procedure calls.

To be self-contained, the tutorial also defines the machine that executes the assembly
instructions. In fact, it defines two machines, one more abstract and the other more
representative of traditional CPU hardware.

The compiler pipeline is implemented in the programming language [Dafny](https://github.com/dafny-lang/dafny),
which provides both immutable datatypes (which are useful for working with AST data structures in
compilers) and mutable objects (which are useful when giving an identity to declarations
of procedures, types, and variables).

## Viewing and building the compiler

The best way to view the sources is with the Dafny extension for VS Code. In VS Code, open the
folder containing this repository. (If you haven't already installed the Dafny extension, VS Code
should prompt you to install it when you open one of the `.dfy` files.)

There is also a `Makefile` with targets for building, verifying, and running the code.

## Overview of compiler pipeline

```
stream of characters (e.g., input.txt)
    |
    v
/--------------------------------\
| Lexer (Lexer.dfy)              |
\--------------------------------/
    |
    v
stream of tokens (defined in Tokens.dfy)
    |
    v
/--------------------------------\
| Parser (Parser.dfy)            |
\--------------------------------/
    |
    v
raw abstract syntax tree (AST) (defined in RawAst.dfy)
    |
    v
/--------------------------------\
| Resolver (Resolver.dfy)        |
\--------------------------------/
    |
    v
resolved AST (defined in AST.dfy)
    |
    v
/--------------------------------\
| Type checker (TypeChecker.dfy) |
\--------------------------------/
    |
    v
resolved AST (no change from the previous pipeline stage)
    |
    v
/--------------------------------\
| Simplifier (Simplifier.dfy)    |
\--------------------------------/
    |
    v
resolved AST (simplified from the previous pipeline stage)
    |
    v
/--------------------------------\
| Compiler (Compiler.dfy)        |
\--------------------------------/
    |
    v
control-flow graph (CFG) (defined in Cfg.dfy and runnable on a Machine, see Machine.dfy)
    |
    v
/--------------------------------\
| Assembler (Assembler.dfy)      |
\--------------------------------/
    |
    v
sequence of machine instructions (assembly code) (defined in RawAsts.dfy and runnable on
a RawMachine, see RawMachine.dfy)
```

## The stages

The stages in the compiler pipeline are described as follows. In the tutorial compiler, these stages are all called from `Main.dfy`.

### Lexer (`Lexer.dfy`)

The role of the _lexer_ is to convert a sequence of characters to a sequence of tokens.
The `Lexer` discards comments (starting with `//` and going to the end of the current line)
in the input.

### Parser (`Parser.dfy`)

The _parser_ turns a sequence of tokens into a "raw" abstract syntax tree (AST), see `RawAst.dfy`.

The grammar of the concrete syntax is:

```
Program ::= Procedure^*
Procedure ::= "procedure" Identifier "(" VarDecl^,* ")" ":" Type
              "{"
                Stmt^*
                "return" Expr
              "}"
VarDecl ::= Identifier ":" Type

Stmt ::=
  | "var" Identifier ":=" Expr
  | Identifer ":=" Expr
  | Identifier ":=" Identifier "(" Expr^,* ")"
  | "if" Expr BlockStmt [ "else" BlockStmt ]
  | BlockStmt
BlockStmt := "{" Stmt^* "}"

Expr ::= ArithExpr [ "<=" ArithExpr ]
ArithExpr ::= [ ArithExpr "-" ] AtomicExpr
AtomicExpr ::= Literal | Identifier | "(" Expr ")"
```

Legend:

* `X^*`   means 0 or more occurrences of `X`
* `X^,*`  means 0 or more comma-separated occurrences of `X`
* `X^,+`  means 1 or more comma-separated occurrences of `X`
* `[ X ]` means 0 or 1 occurrence of `X`

Notes:

* To determine if the input contains another statement or not, the parser uses
  the predicate `IsStartOfStmt`. It is often called the _start set_ of a grammar
  production.
* `if` statements in the abstract syntax tree always have an `else` branch, whereas
  the concrete syntax may omit it.
* By factoring expressions into several productions (`Expr`, `ArithExpr`, `AtomicExpr`),
  the grammar encodes the relative precedence levels of operators.
* There is a difference in how `<=` and `-` expressions are parsed. The comparison `<=`
  is not associative, so parsing it is simple. The `-` operator is associative, so
  parsing it involves recursion. Because it is left-associative, the corresponding
  grammar production looks like it starts with a recursive call. Implementing it
  that way would lead to infinite recursion, so the grammar production is instead
  implemented by a loop that gathers operands up into the left argument.
* Parentheses in expressions are discarded by the parser. That is, parentheses (as
  as well other punctuation) are not represented in the AST.

### Resolver (`Resolver.dfy`)

The responsibility of the _resolver_ is to perform name resolution. This means figuring out
what identifiers appearing in the program refer to. In this way, the `Resolver` turns a
`RawAST` into a (resolved) `AST`.

Local variables are in scope until the end of the enclosing `BlockStmt`. An inner scope
(that is, a `BlockStmt` inside another) is allowed to declare a variable with the same name
as in an enclosing scope; in this case, the variable in the inner scope shadows the
one in the outer scope, from the point of declaration until the end of the inner block.

The resolver creates a unique identity for every procedure declaration, parameter declaration,
and variable declaration. This is a great use of class instances (that is, _objects_) in the
implementation, because the AST can then include _references_ (that is, pointers) to those
class instances. Some of those class instances also include mutable fields, which will be
filled in or changed during later stages of the compiler pipeline.

When creating variables, the resolver marks parameters as being immutable and local
variables as being mutable.

For more complicated input languages, it may be necessary to combine name resolution and
type checking, or even type inference. But in this simple language, the types that are needed
by Resolver are immediately evident from the syntax.

### Type checker (`TypeChecker.dfy`)

The _type checker_ computes types for expressions and checks that statements and expressions
use variables, procedures, and expressions in a way that respects the types. It also
checks that only mutable variables (which in the simple input language corresponds
to local variables) are assigned.

### Simplifier (`Simplifier.dfy`)

The _simplifier_ demonstrates a simple static analysis and optimization that can be
done to the AST. In particular:

* If an occurrence of a variable in an expression can be determined to always have
  a fixed value, then that occurrence of the variable is replaced by the value.
  This is known as _constant propagation_.
* If the operands of an expression are literals, then the expression is
  replaced by the result of applying the operator to those literal arguments.
  This is part of constant propagation, and is also a simple case of
  _partial evaluation_.
* If the analysis can determine the value of the guard of an `if` statement,
  then the `if` statement is replaced by its then branch or by its else branch.
* The analysis is intra-procedural. That is, no analysis information is shared
  between procedures.

The analysis changes the AST into a simpler one. The result may be an AST
that is not legal as input. In particular, a `LiteralExpr` may, after the analysis,
contain a negative integer, whereas the parsed input language does not allow
that.

After this analysis, the program may contain variables that are never used
(or contain cliques of variables that are used only for assigning to variables
within the clique). A further _dead variable_ analysis could remove such
variable declarations.

A slightly more advanced version of constant propagation is to keep track
of ranges of values that variables can have.

The static analysis performed by constant propagation and range analysis are
examples of _abstract interpretation_. Since there are no loops in this simple
input language, the abstract interpretation can be done using a single pass.
In languages with loops (or to perform interprocedural analysis), the abstract
interpretation iterates until it reaches a fixpoint.

### Compiler (`Compiler.dfy`)

This stage translates an AST into a _control-flow graph_ (CFG). This involves creating
basic blocks and the instructions inside basic blocks. The result can be executed
on a `Machine`, which is a somewhat abstract definition of a hardware machine.

### Assembler (`Assembler.dfy`)

The _assembler_ translates a CFG program into assembly code for the `RawMachine`, which is
representative of a traditional CPU and its machine language.

This translation could be done straight from the AST, in a way similar to how the CFG
program is constructed by the `Compiler`. However, translating to `RawMachine` is more
complicated than translating to `Machine`, because, in addition to the basic-block
construction that already goes into the translation to CFG, it involves computing
offsets of parameters and local variables on the stack and computing addresses of
procedure entries, basic-block entries, etc. in the generated code. So, instead, the
`Assembler` takes a CFG program as a starting point. This lets it reuse the work that
went into the CFG construction. However, the `Assembler` needs one piece of information
that wasn't needed for the CFG construction or for execution on `Machine`, namely, an
indication of when the code starts pushing actual parameters onto the evaluation stack.
For this reason, the CFG construction in `Compiler` has been modified to include that
information. In the CFG, the information is carried in a special `PreCall` instruction,
which the `Machine` ignores.

The `Assembler` assumes that the given program has a particular shape. If the `Assembler`
detects otherwise, it returns a failure. (With more work, one would want to prove that
`Assembler` never fails on the programs that `Compiler` generates.)

## Data structures

* `Token.dfy` defines the tokens that the lexer produces. The file `TokenReader.dfy` contains
  useful methods for handling tokens.

    A `Token` is an abstraction of the characters in the input. Essentially, each token
    represents a number of consecutive characters.

* `RawAsts.dfy` defined the raw AST. The file `RawPrinter.dfy` pretty prints a raw AST.

    `RawAst` is an abstract syntax tree (AST) that reflects the structure of the parsed program.
    The AST is "raw" in that it does not carry information about, for example, what identifiers
    stand for or what types expressions have.

* `Ast.dfy` defines the main (resolved) AST. Its pretty printer is found in `Printer.dfy`.

    This module contains the main AST for the program. This AST is similar to the RawAST,
    but contains references to procedure/variable declarations instead of just the names
    of these procedures/variables.

* `Cfg.dfy` defines control-flow graphs (CFGs). These can be printed using the code in `CfgPrinter.dfy`

    This module declares the data structure for a control-flow graph. The vertices of a CFG are
    _basic blocks_, each of which contains a list of instructions. In this way, a CFG is
    usually a piece of straightline code with no internal jumps. The CFG here is a slight
    variation thereof, where the almost-straightline code can include conditional jumps.
    That is, the list of instructions in a `BasicBlock` can include condition-jump instructions.

    A `BasicBlock` ends with either a goto to another `BasicBlock` or an indication that
    the execution of the enclosing procedure has completed.

    The instruction set is for a simple machine with a call stack and an evaluation stack,
    see module `Machine` (in `Machine.dfy`).

* `RawMachine.dfy` defines the instruction set for a simple but representative machine. An assembly
  program is really just a sequence of integers, but they are decoded and printed as an assembly
  program by `AsmPrinter.dfy`.

    The `RawMachine` is a primitive machine for program execution. Unlike the slightly more
    abstract `Machine`, `RawMachine` does not have a call stack. Instead, all operations are performed
    on a single evaluation stack. Moreover, while the `Machine` directly makes use of `Variable`,
    `BasicBlock`, and `Procedure` declarations, the `RawMachine` instead just uses integer indices
    into the global code area or indices into the global evaluation stack. These indices are
    computed by the `Assembler`.

## Machines

There are two machines.

### The more abstract machine (`Machine.dfy`)

This `Machine` module simulates the execution of a CFG program. The machine has the
following pieces:

* The CFG program that contains the code.
* A call stack. Each entry of the call stack is an _activation record_
  `(locals, pc)`, where

    - `locals` is a map from (parameters and local) variables to values
    - `pc` is the program counter, which is a `BasicBlock` and an index into
      the instruction list of that `BasicBlock`

* A (global) evaluation stack, which is used to store intermediate values
  during expression evaluation and to pass procedure parameters and result
  values.

Other than making changes to the call stack itself, the `Machine` makes changes
only in the activation record at the top of the call stack. Therefore, the
top of the call stack (fields `locals` and `pc` in class `MachineState`) is
implemented separately from the rest of the call stack (field `returnStack`
in class `MachineState`).

The instructions themselves operate on the evaluation stack, get values into
or out of local variables, and push/pop the call stack. This `Machine` does not
have any registers, but if it did, the instructions would include some
analogous _three-address codes_.

### The more realistic machine (`RawMachine.dfy`)

The `RawMachine` is a primitive machine for program execution. Unlike the slightly more
abstract `Machine`, `RawMachine` does not have a call stack. Instead, all operations are performed
on a single evaluation stack. Moreover, while the `Machine` directly makes use of `Variable`,
`BasicBlock`, and `Procedure` declarations, the `RawMachine` instead just uses integer indices
into the global code area or indices into the global evaluation stack. These indices are
computed by the `Assembler`.

Its instruction set is

| instruction | description |
|-------------|---------------------------------------------------------------|
| `HALT`      | halts execution of the machine |
| `PUSH x`    | pushes `x` onto the stack |
| `ADJ x`     | adjusts the stack pointer by `x` (e.g., `ADJ 1` has the effect of popping the top of the stack) |
| `LOAD x`    | reads the value at offset `x` from the stack pointer and pushes it onto the stack (e.g., `LOAD 1` duplicates the top element) |
| `STOR x`    | pops the top element of the stack (say, `s`) and then stores `s` at offset `x` from the new stack pointer |
| `JMP x`     | sets the program counter to `x` |
| `IJMP`      | pops the top element of the stack (say, `s`) and sets the program counter to `s` |
| `JMPZ x`    | pops the top element of the stack (say, `s`) and, if `s==0`, sets the program counter to `x` |
| `SUB`       | replaces the top two elements of the stack (say, `s` and `t`) with `s - t` |
| `CMP`       | replaces the top two elements of the stack (say, `s` and `t`) with `1` if `s <= t` and with `0` otherwise |
