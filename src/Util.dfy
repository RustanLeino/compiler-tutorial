// This module contains several types, functions, and methods that are commonly used
// in the compiler program.

module Util {
  export
    reveals Option, Option.IsFailure, Option.PropagateFailure, Option.Extract
    reveals Result, Result.IsFailure, Result.PropagateFailure, Result.Extract
    reveals Outcome, Outcome.IsFailure, Outcome.PropagateFailure, Outcome.ToResult
    reveals NonemptySeq
    reveals List
    provides Hex, HexDigit, FlushLeft, FlushRight
    reveals Max
    provides ReadInput, IntToString

  datatype Option<+T> = None | Some(value: T) {
    predicate IsFailure() {
      None?
    }

    function PropagateFailure<U>(): Option<U>
      requires None?
    {
      None
    }

    function Extract(): T
      requires Some?
    {
      value
    }
  }

  datatype Result<+T> = | Success(value: T) | Failure(error: string) {
    predicate IsFailure() {
      Failure?
    }

    function PropagateFailure<U>(): Result<U>
      requires Failure?
    {
      Failure(this.error)
    }

    function Extract(): T
      requires Success?
    {
      value
    }
  }

  datatype Outcome = Pass | Fail(error: string)
  {
    predicate IsFailure() {
      Fail?
    }

    function PropagateFailure(): Outcome {
      this
    }

    // Note: no Extract method, so Outcome can be used with :- without a LHS

    function ToResult(): Result<()> {
      match this
      case Pass => Success(())
      case Fail(error) => Failure(error)
    }
  }

  type NonemptySeq<X> = s: seq<X> | |s| != 0 witness *

  datatype List<X> = Nil | Cons(head: X, tail: List<X>)

  function Max(x: int, y: int): int {
    if x < y then y else x
  }

  function IntToString(w: int): string
    decreases w < 0, w
  {
    if w < 0 then
      "-" + IntToString(-w)
    else if w == 0 then
      "0"
    else
      var d := ['0' + (w % 10) as char];
      var r := w / 10;
      if r == 0 then d else IntToString(r) + d        
  }

  function Hex(w: int): string
    decreases w < 0, w
  {
    if w < 0 then
      "-" + Hex(-w)
    else if w == 0 then
      "0"
    else
      var d := [HexDigit(w % 16)];
      var r := w / 16;
      if r == 0 then d else Hex(r) + d        
  }

  function HexDigit(d: nat): char
    requires d < 16
  {
    if d < 10 then
      '0' + d as char
    else
      'A' + (d - 10) as char
  }

  function FlushRight(s: string, width: nat): string {
    if width <= |s| then
      s
    else
      seq(width - |s|, _ => ' ') + s
  }

  function FlushLeft(s: string, width: nat): string {
    if width <= |s| then
      s
    else
      s + seq(width - |s|, _ => ' ')
  }

  method {:extern "Util.DotNetUtil", "ReadFile"} ReadFile(filename: string) returns (s: Result<string>)

  method ReadInput(filename: string) returns (r: Result<string>) {
    var s :- ReadFile(filename);
    return Success(s);
  }
}
