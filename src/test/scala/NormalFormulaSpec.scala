import NormalFormula.nf
import Term.stringToVar
import org.scalatest.matchers.should.Matchers
import org.scalatest.flatspec.AnyFlatSpec

class NormalFormulaSpec extends AnyFlatSpec with Matchers {
  val ctx: Context = Context(
    new Signature(
      Seq(
        Generator("f", Seq("T"), "T"),
        Generator("g", Seq("T", "T"), "T")
      ),
      Set("T")),
    Seq("u" -> "T", "v" -> "T", "w" -> "T", "x" -> "T", "y" -> "T"))

  "Renaming" should "work correctly" in {
    nf(Seq.empty, "u" =~ "v" & "x" =~ "u" & "v" =~ "f".ap("u") & "u".fin(),
      nf(Seq.empty, "u" =~ "v" & "x" =~ "u" & "v" =~ "f".ap("u") & "u".fin()))
      .rename(Map("u" -> "w")) should equal(
      nf(Seq.empty, "w" =~ "v" & "x" =~ "w" & "v" =~ "f".ap("w") & "w".fin(),
        nf(Seq.empty, "w" =~ "v" & "x" =~ "w" & "v" =~ "f".ap("w") & "w".fin())))
    nf(Seq("u" -> "T"), "u".fin()).rename(Map("u" -> "v")) should equal(
      nf(Seq("u" -> "T"), "u".fin()))
    nf(Seq("u" -> "T"), "u".fin(), nf(Seq.empty, "u".fin())).rename(Map("u" -> "v")) should equal(
      nf(Seq("u" -> "T"), "u".fin(), nf(Seq.empty, "u".fin())))
  }

  "Making variables fresh" should "work correctly" in {
    nf(Seq("u" -> "T"), "u" =~ "v" & "x" =~ "u" & "v" =~ "f".ap("u") & "u".fin())
      .makeVarsFresh(ctx) should equal(
      nf(Seq("u'" -> "T"), "u'" =~ "v" & "x" =~ "u'" & "v" =~ "f".ap("u'") & "u'".fin()))
    nf(Seq("u" -> "T", "u" -> "T"), "u" =~ "v" & "x" =~ "u" & "v" =~ "f".ap("u") & "u".fin())
      .makeVarsFresh(ctx) should equal(
      nf(Seq("u'" -> "T", "u''" -> "T"), "u''" =~ "v" & "x" =~ "u''" & "v" =~ "f".ap("u''") & "u''".fin()))
    NormalFormula.nf(Seq("x" -> "T"), "x" =~ "y", NormalFormula.nf(Seq("x" -> "T"), "x".fin()))
      .recursivelyMakeVarsFresh(ctx.without("x")) should equal(
      NormalFormula.nf(Seq("x" -> "T"), "x" =~ "y", NormalFormula.nf(Seq("x'" -> "T"), "x'".fin())))
  }
}
