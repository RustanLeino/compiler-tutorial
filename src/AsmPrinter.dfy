// This module prints an assembly program.

module AsmPrinter {
  export
    provides Assembler
    provides Print

  import opened Util
  import opened RawMachine
  import Assembler

  method Print(assemblyCode: Assembler.AssemblyCode) {
    var i := 0;
    while i < |assemblyCode.code| {
      if i in assemblyCode.noteworthyLocations {
        var comments := assemblyCode.noteworthyLocations[i];
        for j := 0 to |comments| {
          print "; ", comments[j], "\n";
        }
      }

      var w := assemblyCode.code[i];
      var op := Decode(w);
      var len := 1;
      var comment := "";
      if op.Some? {
        var argumentCount := if op.value.HasArgument() then 1 else 0;
        if i + 1 + argumentCount <= |assemblyCode.code| {
          len := 1 + argumentCount;
          comment := op.value.ToString();
        }
      }
      PrintLine(i, assemblyCode.code[i..i + len], comment);
      i := i + len;
    }
  }

  method PrintLine(i: nat, words: seq<int>, comment: string) {
    print FlushRight(Hex(i), 6), ":  ";

    var s := "";
    for i := 0 to |words| {
      s := s + Hex(words[i]) + " ";
    }
    print FlushLeft(s, 20);

    if comment != "" {
      print "      ; ", comment;
    }

    print "\n";
  }

}