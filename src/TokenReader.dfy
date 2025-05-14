// TokenReader contains helpful methods for consuming, and looking ahead into, a sequence
// of tokens.

module TokenReader {
  export
    provides Util, Tokens
    reveals TokenReader, TokenReader.Progress, TokenReader.ProgressNonStrict, Token
    provides TokenReader.Remaining, TokenReader.Next, TokenReader.Peek
    provides TokenReader.Expect, TokenReader.ExpectIdent
  
  import opened Util
  import Tokens

  type Token = Tokens.Token

  class TokenReader {
    const tokens: seq<Token>
    var i: nat

    constructor (tokens: seq<Token>) {
      this.tokens := tokens;
      i := 0;
    }

    ghost function Remaining(): nat
      reads this
    {
      if i <= |tokens| then |tokens| - i else 0
    }

    twostate predicate Progress()
      reads this
    {
      Remaining() < old(Remaining())
    }

    twostate predicate ProgressNonStrict()
      reads this
    {
      Remaining() <= old(Remaining())
    }

    method Next() returns (token: Token)
      modifies this
      ensures token == old(Peek())
      ensures token != Token.EOF ==> Progress()
    {
      token := Peek();
      i := i + 1;
    }

    function Peek(n: nat := 0): Token
      reads this
    {
      if i + n < |tokens| then tokens[i + n] else Token.EOF
    }

    method Expect(token: Token) returns (r: Result<Token>)
      modifies this
      ensures r.Success? ==> r.value == token
      ensures r.Success? && token != Token.EOF ==> Progress()
      ensures old(Peek() == token) ==> r.Success?
    {
      var next := Next();
      if next == token {
        return Success(next);
      } else {
        return Failure("expected " + token.ToString() + " got " + next.ToString());
      }
    }

    method ExpectIdent() returns (r: Result<string>)
      modifies this
      ensures r.Success? ==> Progress()
      ensures old(Peek().Identifier?) ==> r.Success?
    {
      var next := Next();
      if next.Identifier? {
        return Success(next.name);
      } else {
        return Failure("expected identifier, got " + next.ToString());
      }
    }
  }
}
