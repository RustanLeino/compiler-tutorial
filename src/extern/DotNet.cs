namespace Util {
  abstract class DotNetUtil {
    public static Util._IResult<Dafny.ISequence<Dafny.Rune>> ReadFile(Dafny.ISequence<Dafny.Rune> filename) {
      try {
        var fn = filename.ToVerbatimString(false);
        var s = System.IO.File.ReadAllText(fn);
        var contents = Dafny.Sequence<Dafny.Rune>.UnicodeFromString(s);
        return Util.Result<Dafny.ISequence<Dafny.Rune>>.create_Success(contents);
      } catch (System.Exception e) {
        var msg = e.Message;
        return Util.Result<Dafny.ISequence<Dafny.Rune>>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(msg));
      }
    }
  }
}