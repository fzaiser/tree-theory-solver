import NormalFormula.nf
import Term.stringToVar
import org.scalatest.matchers.should.Matchers
import org.scalatest.flatspec.AnyFlatSpec

class RuleSpec extends AnyFlatSpec with Matchers {
  val ctx: Context = Context(
    new Signature(
      Seq(
        Generator("f", Seq("T"), "T"),
        Generator("g", Seq("T", "T"), "T"),
        Generator("true", Seq.empty, "bool"),
        Generator("false", Seq.empty, "bool"),
        Generator("infcons1", Seq("inflist"), "inflist"),
        Generator("infcons2", Seq("inflist"), "inflist")
      ),
      Set("T")),
    Seq(
      "a" -> "T",
      "b" -> "T",
      "u" -> "T",
      "u1" -> "T",
      "u2" -> "T",
      "u3" -> "T",
      "v" -> "T",
      "v1" -> "T",
      "v2" -> "T",
      "w" -> "T",
      "w1" -> "T",
      "w2" -> "T",
      "x" -> "T",
      "y" -> "T",
      "z" -> "T"))

  "Rule 1" should "remove tautologies" in {
    Rule.rule1("a" =~ "a" & "a" =~ "b") should equal("a" =~ "b")
  }

  "Rule 2" should "reorder variable equations correctly" in {
    Rule.applyToNf(Rule.rule2, ctx, nf(Seq("v" -> "T"), "u" =~ "v")) should equal(
      nf(Seq("v" -> "T"), "v" =~ "u"))
    Rule.applyToNf(Rule.rule2, ctx, nf(Seq("u" -> "T"), "u" =~ "v")) should equal(
      nf(Seq("u" -> "T"), "u" =~ "v"))
  }

  it should "not touch anything else" in {
    Rule.applyToNf(Rule.rule2, ctx, nf(Seq("v" -> "T"), "u" =~ "f".ap("v"))) should equal(
      nf(Seq("v" -> "T"), "u" =~ "f".ap("v")))
  }

  "Rule 3" should "change the LHS of equations correctly" in {
    Rule.applyToNf(Rule.rule3, ctx, nf(Seq("u" -> "T"), "u" =~ "v" & "u" =~ "w")) should equal(
      nf(Seq("u" -> "T"), "u" =~ "v" & "v" =~ "w"))
    Rule.applyToNf(Rule.rule3, ctx, nf(Seq("u" -> "T"), "u" =~ "v" & "u" =~ "f".ap())) should equal(
      nf(Seq("u" -> "T"), "u" =~ "v" & "v" =~ "f".ap()))
    Rule.applyToNf(Rule.rule3, ctx,
      nf(Seq("v" -> "T", "u" -> "T"), "u" =~ "w" & "u" =~ "v" & "u" =~ "f".ap())) should equal(
      nf(Seq("v" -> "T", "u" -> "T"), "u" =~ "w" & "w" =~ "v" & "w" =~ "f".ap()))
    val n = nf(Seq("v" -> "T", "u" -> "T"), "u" =~ "v" & "v" =~ "w" & "u" =~ "f".ap())
    val n1 = Rule.applyToNf(Rule.rule3, ctx, n)
    n1 should equal(
      nf(Seq("v" -> "T", "u" -> "T"), "u" =~ "v" & "v" =~ "w" & "v" =~ "f".ap()))
    val n2 = Rule.applyToNf(Rule.rule3, ctx, n1)
    n2 should equal(
      nf(Seq("v" -> "T", "u" -> "T"), "u" =~ "v" & "v" =~ "w" & "w" =~ "f".ap()))
  }

  "Rule 4" should "detect conflicts" in {
    Rule.rule4("u" =~ "f".ap() & "u" =~ "g".ap()) should equal(
      None)
    Rule.rule4("u" =~ "f".ap() & "u" =~ "f".ap() & "u" =~ "g".ap()) should equal(
      None)
  }

  it should "not touch anything else" in {
    Rule.rule4("u" =~ "f".ap("v") & "u" =~ "f".ap("w")) should equal(
      Some("u" =~ "f".ap("v") & "u" =~ "f".ap("w")))
  }

  "Rule 5" should "unify arguments" in {
    Rule.rule5("u" =~ "f".ap() & "u" =~ "f".ap()) should equal(
      "u" =~ "f".ap())
    Rule.rule5("u" =~ "f".ap("v1", "v2") & "u" =~ "f".ap("w1", "w2")) should equal(
      "u" =~ "f".ap("v1", "v2") & "v1" =~ "w1" & "v2" =~ "w2")
  }

  it should "not touch anything else" in {
    Rule.rule5("u" =~ "v" & "u" =~ "f".ap() & "u" =~ "g".ap()) should equal(
      "u" =~ "v" & "u" =~ "f".ap() & "u" =~ "g".ap())
  }

  "Rule 7" should "remove duplicate finiteness constraints" in {
    "u".fin() & "u".fin() should equal("u".fin())
  }

  "Rule 8" should "change the argument of finiteness constraints correctly" in {
    Rule.applyToNf(Rule.rule8, ctx, nf(Seq("u" -> "T"), "u" =~ "v" & "u".fin())) should equal(
      nf(Seq("u" -> "T"), "u" =~ "v" & "v".fin()))
    Rule.applyToNf(Rule.rule8, ctx,
      nf(Seq("v" -> "T", "u" -> "T"), "u" =~ "w" & "u" =~ "v" & "u".fin())) should equal(
      nf(Seq("v" -> "T", "u" -> "T"), "u" =~ "w" & "u" =~ "v" & "w".fin()))
    val n = nf(Seq("v" -> "T", "u" -> "T"), "u" =~ "v" & "v" =~ "w" & "u".fin())
    val n1 = Rule.applyToNf(Rule.rule8, ctx, n)
    n1 should equal(nf(Seq("v" -> "T", "u" -> "T"), "u" =~ "v" & "v" =~ "w" & "v".fin()))
    val n2 = Rule.applyToNf(Rule.rule8, ctx, n1)
    n2 should equal(nf(Seq("v" -> "T", "u" -> "T"), "u" =~ "v" & "v" =~ "w" & "w".fin()))
  }

  "Reachability" should "be computed correctly" in {
    val basic = "z" =~ "f".ap("u", "v") & "v" =~ "g".ap("v", "u") & "w" =~ "f".ap("u", "v") &
      "u".fin() & "x".fin()
    basic.reachableFrom("z") should equal(Set(Var("u"), Var("v")))
    nf(Seq("u" -> "T", "v" -> "T", "w" -> "T"), basic).properlyReachableVariables(ctx) should equal(
      Set(Var("z"), Var("u"), Var("v")))
    nf(Seq("u" -> "T", "v" -> "T", "w" -> "T"), basic).reachablePartsOfBasic(ctx) should equal(
      (Seq(Var("u"), Var("v")), "z" =~ "f".ap("u", "v") & "v" =~ "g".ap("v", "u") &
        "u".fin() & "x".fin()))
  }

  "Rule 9" should "remove unsatisfiable finiteness constraints" in {
    Rule.rule9("x" =~ "f".ap("x") & "x".fin()) should equal(None)
    Rule.rule9("x" =~ "f".ap("y") & "x".fin()) should equal(Some("x" =~ "f".ap("y") & "x".fin()))
  }

  "Rule 10" should "distribute finiteness constraints over arguments" in {
    Rule.rule10("x" =~ "f".ap() & "x".fin()) should equal(
      "x" =~ "f".ap())
    Rule.rule10("x" =~ "f".ap("y", "z") & "x".fin()) should equal(
      "x" =~ "f".ap("y", "z") & "y".fin() & "z".fin())
  }

  "Rule 12" should "propagate constraints inward" in {
    Rule.rule12(ctx, nf(Seq.empty, "x" =~ "y", nf(Seq.empty, BasicFormula.empty))) should equal(
      nf(Seq.empty, "x" =~ "y", nf(Seq.empty, "x" =~ "y")))
    Rule.rule12(ctx.without("x"),
      nf(Seq("x" -> "T"), "x" =~ "y", nf(Seq("x" -> "T"), "x".fin()))) should equal(
      nf(Seq("x" -> "T"), "x" =~ "y", nf(Seq("x'" -> "T"), "x" =~ "y" & "x'".fin())))
  }

  "Rule 13" should "propagate constraints inward again" in {
    Rule.rule13(nf(Seq.empty, "x" =~ "y", nf(Seq.empty, "x" =~ "z" & "y" =~ "z"))) should equal(
      nf(Seq.empty, "x" =~ "y", nf(Seq.empty, "x" =~ "y" & "y" =~ "z")))
    Rule.rule13(nf(Seq("v1" -> "T"), "v1" =~ "f".ap("u1", "u2") & "u2" =~ "g".ap("u1"),
      nf(Seq("w2" -> "T"), "v1" =~ "f".ap("u1", "u2") & "u2" =~ "g".ap("w2") &
        "w2" =~ "u1" & "u1" =~ "g".ap("u3") & "u3".fin()))) should equal(
      nf(Seq("v1" -> "T"), "v1" =~ "f".ap("u1", "u2") & "u2" =~ "g".ap("u1"),
        nf(Seq("w2" -> "T"), "v1" =~ "f".ap("u1", "u2") & "u2" =~ "g".ap("u1") &
          "w2" =~ "u1" & "u1" =~ "g".ap("u3") & "u3".fin()))
    )
  }

  "Rule 14" should "detect nested conflicts" in {
    Rule.rule14(nf(Seq.empty, "z" =~ "x" & "x".fin(),
      nf(Seq.empty, "z" =~ "x" & "x".fin()))) should equal(
      None)
    Rule.rule14(nf(Seq.empty, "z" =~ "x" & "x".fin(),
      nf(Seq.empty, "x".fin()))) should equal(
      None)
    Rule.rule14(nf(Seq.empty, "z" =~ "x" & "x".fin(),
      nf(Seq.empty, "z" =~ "x" & "x".fin() & "z".fin()))) should equal(
      Some(nf(Seq.empty, "z" =~ "x" & "x".fin(),
        nf(Seq.empty, "z" =~ "x" & "x".fin() & "z".fin()))))
    val tooDeep = nf(Seq.empty, "x".fin(), nf(Seq.empty, "x".fin(), nf(Seq.empty, "y".fin())))
    Rule.rule14(tooDeep) should equal(Some(tooDeep))
  }

  "Rule 15" should "remove unreachable stuff" in {
    Rule.rule15(ctx, nf(Seq("v" -> "T"), "v" =~ "u")) should equal(
      nf(Seq.empty, BasicFormula.empty)
    )
    Rule.rule15(ctx, nf(Seq("w2" -> "T"), "v1" =~ "f".ap("u1", "u2") & "u2" =~ "g".ap("u1") &
      "w2" =~ "u1" & "u1" =~ "g".ap("u3") & "u3".fin())) should equal(
      nf(Seq.empty, "v1" =~ "f".ap("u1", "u2") & "u2" =~ "g".ap("u1") &
        "u1" =~ "g".ap("u3") & "u3".fin())
    )
    Rule.rule15(ctx, nf(Seq("v1" -> "T"), "v1" =~ "f".ap("u1", "u2") & "u2" =~ "g".ap("u1"),
      nf(Seq.empty, "v1" =~ "f".ap("u1", "u2") & "u2" =~ "g".ap("u1") &
        "u1" =~ "g".ap("u3") & "u3".fin()))) should equal(
      nf(Seq.empty, "u2" =~ "g".ap("u1"),
        nf(Seq.empty, "u2" =~ "g".ap("u1") & "u1" =~ "g".ap("u3") & "u3".fin()))
    )
    Rule.rule15(ctx, nf(Seq("v1" -> "T"), "v1" =~ "f".ap("u1", "u2") & "u2" =~ "g".ap("u1"),
      nf(Seq.empty, "v1" =~ "f".ap("u1", "u2") & "u2" =~ "g".ap("u1") &
        "u1" =~ "g".ap("u3") & "u3".fin()))) should equal(
      nf(Seq.empty, "u2" =~ "g".ap("u1"),
        nf(Seq.empty, "u2" =~ "g".ap("u1") & "u1" =~ "g".ap("u3") & "u3".fin()))
    )
    Rule.rule15(ctx, nf(Seq("v" -> "T"), "v".fin(), nf(Seq.empty, "v".fin() & "v" =~ "u"))) should equal(
      nf(Seq.empty, BasicFormula.empty)
    )
    // Example 4.2.14 (from Djelloul et al.):
    Rule.rule15(ctx, nf(Seq("x" -> "T"), BasicFormula.empty,
      nf(Seq("y" -> "T"), "z" =~ "f".ap("y") & "y" =~ "g".ap("x")),
      nf(Seq.empty, "x" =~ "w"),
      nf(Seq.empty, "x" =~ "g".ap("x")))) should equal(
      nf(Seq.empty, BasicFormula.empty)
    )
  }

  "Rule 16" should "reduce the nesting level" in {
    Rule.rule16(nf(Seq("x" -> "T"), "x".fin(),
      nf(Seq("y" -> "T"), "y".fin(),
        nf(Seq("z" -> "T"), "z".fin())))) should equal(
      (
        nf(Seq("x" -> "T"), "x".fin(), nf(Seq("y" -> "T"), "y".fin())),
        Seq(nf(Seq("x" -> "T", "y" -> "T", "z" -> "T"), "z".fin()))
      ))

    val n0 = nf(Seq.empty, "u" =~ "s".ap("v"))
    val n1 = nf(Seq("w1" -> "T"), "u" =~ "s".ap("w1") & "w1" =~ "s".ap("v"))
    val n20 = nf(Seq.empty, "v" =~ "u" & "u" =~ "0")
    val n21 = nf(Seq("w2" -> "T"), "v" =~ "u" & "u" =~ "s".ap("w2"))
    val n2 = nf(Seq.empty, "v" =~ "u", n20, n21)
    val n2reduced = nf(Seq.empty, "v" =~ "u")
    val n = nf(Seq.empty, BasicFormula.empty, n0, n1, n2)
    Rule.rule16(n) should equal(
      (nf(Seq.empty, BasicFormula.empty, n2reduced, n0, n1),
        Seq(n20.copy(nested = Seq(n0, n1)),
          n21.copy(nested = Seq(n0, n1)))
      ))
  }

  "Redundant Finiteness Rule" should "remove unnecessary finiteness constraints" in {
    Rule.redundantFinitenessRule(ctx.withBindings(Seq("bv" -> "bool")), "bv".fin()) should equal(
      Some(BasicFormula.empty))
    Rule.redundantFinitenessRule(ctx, "x".fin()) should equal(Some("x".fin()))
  }

  it should "detect finiteness conflicts" in {
    Rule.redundantFinitenessRule(ctx.withBindings(Seq("iv" -> "inflist")), "iv".fin()) should equal(None)
  }

}
