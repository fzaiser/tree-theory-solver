import Binding.pair2Bind
import Term.stringToVar
import org.scalatest.matchers.should.Matchers
import org.scalatest.flatspec.AnyFlatSpec

class FormulaSpec extends AnyFlatSpec with Matchers {
  val ctx: Context = Context(
    new Signature(
      Seq(
        Generator("const", Seq.empty, "T"),
        Generator("f", Seq("T"), "T"),
        Generator("g", Seq("T", "T"), "T")
      ),
      Set("T")),
    Seq("a" -> "T", "b" -> "T", "v" -> "T"))

  "Normalization" should "transform simple equations and finiteness constraints correctly" in {
    Equation("a", "b").negatedNormalize(ctx) should equal(NormalFormula.nf(Seq.empty, "a" =~ "b"))
    Equation("a", "b").normalize(ctx) should equal(NormalFormula.nf(Seq.empty, BasicFormula.empty,
      NormalFormula.nf(Seq.empty, "a" =~ "b")))
    Finite("v").negatedNormalize(ctx) should equal(NormalFormula.nf(Seq.empty, "v".fin()))
    Finite("v").normalize(ctx) should equal(NormalFormula.nf(Seq.empty, BasicFormula.empty,
      NormalFormula.nf(Seq.empty, "v".fin())))
    Equation("f".app("a"), "b").negatedNormalize(ctx) should equal(
      NormalFormula.nf(Seq.empty, "b" =~ "f".ap("a")))
  }

  it should "transform complex equations and finiteness constraints correctly" in {
    Equation("f".app("a"), "g".app("a", "f".app("b"))).negatedNormalize(ctx) should equal(
      NormalFormula.nf(Seq("_0" -> "T", "_1" -> "T"),
        "_0" =~ "f".ap("a") & "_0" =~ "g".ap("a", "_1") & "_1" =~ "f".ap("b")))
    Finite("f".app("a", "f".app("a", "a"))).negatedNormalize(ctx) should equal(
      NormalFormula.nf(Seq("_0" -> "T", "_1" -> "T"),
        "_0".fin() & "_0" =~ "f".ap("a", "_1") & "_1" =~ "f".ap("a", "a")))
  }

  it should "transform Boolean combinations correctly" in {
    Not(Equation("a", "b")).normalize(ctx) should equal(NormalFormula.nf(Seq.empty, "a" =~ "b"))
    Disjunction(Seq(Equation("a", "b"), Equation("b", "c"))).normalize(ctx) should equal(
      NormalFormula.nf(Seq.empty, BasicFormula.empty,
        NormalFormula.nf(Seq.empty, "a" =~ "b"),
        NormalFormula.nf(Seq.empty, "b" =~ "c")))
    Conjunction(Seq(Not(Equation("a", "b")), Not(Equation("b", "c")))).negatedNormalize(ctx) should equal(
      NormalFormula.nf(Seq.empty, BasicFormula.empty,
        NormalFormula.nf(Seq.empty, "a" =~ "b"),
        NormalFormula.nf(Seq.empty, "b" =~ "c")))
  }

  it should "transform quantifiers correctly" in {
    Forall(Seq("a" -> "T"), Not(Finite("a"))).normalize(ctx) should equal(
      NormalFormula.nf(Seq("a" -> "T"), "a".fin()))
    Exists(Seq("a" -> "T"), Finite("a")).negatedNormalize(ctx) should equal(
      NormalFormula.nf(Seq("a" -> "T"), "a".fin()))
  }

  it should "handle variable shadowing correctly" in {
    Disjunction(Seq(Equation("f".app("a"), "f".app("b")), Equation("f".app("c"), "g".app())))
      .normalize(ctx) should equal(
      NormalFormula.nf(Seq.empty, BasicFormula.empty,
        NormalFormula.nf(Seq("_0" -> "T"), "_0" =~ "f".ap("a") & "_0" =~ "f".ap("b")),
        NormalFormula.nf(Seq("_0" -> "T"), "_0" =~ "f".ap("c") & "_0" =~ "g".ap())))
  }

  it should "handle nested constructors correctly" in {
    val actual = Equation("g".app("a", "c"), "g".app("f".app("g".app("b", "const".app())), "const".app()))
      .negatedNormalize(ctx)
    actual should equal(
      NormalFormula.nf(Seq("_0" -> "T", "_1" -> "T", "_2" -> "T", "_3" -> "T", "_4" -> "T"),
        "_0" =~ "g".ap("a", "c")
          & "_0" =~ "g".ap("_1", "_4")
          & "_1" =~ "f".ap("_2")
          & "_2" =~ "g".ap("b", "_3")
          & "_3" =~ "const".ap()
          & "_4" =~ "const".ap())
    )
  }
}
