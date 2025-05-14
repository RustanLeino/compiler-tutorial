module Tokens {
  export
    reveals Token
    provides Token.ToString

  import opened Util

  // A Token is an abstraction of the characters in the input. Essentially, each token
  // represents a number of consecutive characters.

  datatype Token =
    | Literal(n: nat)
    | Identifier(name: string)
    | Procedure | If | Else | Return | Var
    | Int | Bool
    | AtMost | Minus
    | Open | Close | OpenCurly | CloseCurly
    | Colon | Comma
    | Gets
    | EOF
  {
    function ToString(): string {
      match this
      case Literal(n) => Util.IntToString(n)
      case Identifier(name) => name
      case Procedure => "procedure"
      case If => "if"
      case Else => "else"
      case Return => "return"
      case Var => "var"
      case Int => "int"
      case Bool => "bool"
      case AtMost => "<="
      case Minus => "-"
      case Open => "("
      case Close => ")"
      case OpenCurly => "{"
      case CloseCurly => "}"
      case Colon => ":"
      case Comma => ","
      case Gets => ":="
      case EOF => "<EOF>"
    }
  }


}