// The role of the Lexer is to convert a sequence of characters to a sequence of tokens.
// The Lexer discards comments (starting with "//" and going to the end of the current line)
// in the input.

module Lexer {
  export
    provides Util, Tokens
    provides Lex

  import opened Util
  import opened Tokens

  method Lex(s: string) returns (r: Result<seq<Token>>) {
    var tokens := [];
    var i := SkipWhitespace(s, 0);
    while i < |s|
      invariant i <= |s|
    {
      var token;
      token, i :- ReadToken(s, i);
      i := SkipWhitespace(s, i);
      tokens := tokens + [token];
    }
    return Success(tokens);
  }

  method SkipWhitespace(s: string, i: nat) returns (j: nat)
    requires i <= |s|
    ensures i <= j <= |s|
  {
    j := i;
    while j < |s|
      invariant i <= j <= |s|
    {
      if s[j] in {' ', '\t', '\n'} {
        j := j + 1;
      } else if s[j] == '/' && j + 1 < |s| && s[j + 1] == '/' {
        j := SkipUntilEndOfLine(s, j + 2);
      } else {
        break;
      }
    }
  }

  method SkipUntilEndOfLine(s: string, i: nat) returns (j: nat)
    requires i <= |s|
    ensures i <= j <= |s|
  {
    j := i;
    while j < |s| && s[j] != '\n'
      invariant i <= j <= |s|
    {
      j := j + 1;
    }
  }

  predicate IsDigit(ch: char) {
    '0' <= ch <= '9'
  }

  predicate IsLetterLike(ch: char) {
    || 'a' <= ch <= 'z'
    || 'A' <= ch <= 'Z'
    || ch == '_'
  }

  method ReadToken(s: string, i: nat) returns (r: Result<Token>, j: nat)
    requires i < |s|
    ensures r.Success? ==> i < j <= |s|
  {
    var token;
    if IsDigit(s[i]) {
      var n;
      n, j := ReadLiteral(s, i);
      token := Literal(n);

    } else if IsLetterLike(s[i]) {
      var word;
      word, j := ReadWord(s, i);
      match word
      case "procedure" => token := Procedure;
      case "if" => token := If;
      case "else" => token := Else;
      case "return" => token := Return;
      case "var" => token := Var;
      case "int" => token := Int;
      case "bool" => token := Bool;
      case _ => token := Identifier(word);

    } else if i + 1 < |s| && s[i] == '<' && s[i + 1] == '=' {
      token, j := AtMost, i + 2;

    } else if i + 1 < |s| && s[i] == ':' && s[i + 1] == '=' {
      token, j := Gets, i + 2;

    } else {
      match s[i] {
        case '-' => token := Minus;
        case '(' => token := Open;
        case ')' => token := Close;
        case '{' => token := OpenCurly;
        case '}' => token := CloseCurly;
        case ':' => token := Colon;
        case ',' => token := Comma;
        case _ =>
          return Failure("unexpected input: '" + [s[i]] + "'"), 0;
      }
      j := i + 1;
    }

    return Success(token), j;
  }

  method ReadLiteral(s: string, i: nat) returns (n: nat, j: nat)
    requires i < |s| && IsDigit(s[i])
    ensures i < j <= |s|
  {
    n := 0;
    j := i;
    while j < |s|
      invariant j == i || i < j <= |s|
    {
      if IsDigit(s[j]) {
        n := 10 * n + (s[j] - '0') as int;
        j := j + 1;
      } else {
        return;
      }
    }
  }

  method ReadWord(s: string, i: nat) returns (word: string, j: nat)
    requires i < |s| && IsLetterLike(s[i])
    ensures i < j <= |s|
  {
    j := i;
    while j < |s|
      invariant j == i || i < j <= |s|
    {
      if IsLetterLike(s[j]) || IsDigit(s[j]) {
        j := j + 1;
      } else {
        break;
      }
    }
    return s[i..j], j;
  }

}