import NormalFormula.nf
import Term.stringToVar
import org.scalatest.matchers.should.Matchers
import org.scalatest.flatspec.AnyFlatSpec

class SolverSpec extends AnyFlatSpec with Matchers {
  val ctx: Context = Context(
    new Signature(
      Seq(
        Generator("f", Seq("T"), "T"),
        Generator("g", Seq("T", "T"), "T")
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

  "x=f(x)∧y=f(y)∧x!=y" should "be unsatisfiable" in {
    val f = nf(Seq.empty, "x" =~ "f".ap("x") & "y" =~ "f".ap("y"), nf(Seq.empty, "x" =~ "y"))
    Solver.solveNf(ctx, f) should equal(Seq.empty)
    val f2 = Equation("x", "f".app("x")) & Equation("y", "f".app("y")) & !Equation("x", "y")
    Solver.solve(ctx, f2) should equal(Seq(nf(Seq.empty, BasicFormula.empty)))
  }

  "x=f(x)∧y=f(f(y))∧x!=y" should "be unsatisfiable" in {
    val f = nf(
      Seq("z" -> "T"),
      "x" =~ "f".ap("x") & "y" =~ "f".ap("z") & "z" =~ "f".ap("y"),
      nf(Seq.empty, "x" =~ "y"))
    Solver.solveNf(ctx, f) should equal(Seq.empty)
    val f2 = Equation("x", "f".app("x")) & Equation("y", "f".app("f".app("y"))) & !Equation("x", "y")
    Solver.solve(ctx, f2) should equal(Seq(nf(Seq.empty, BasicFormula.empty)))
  }

  "Example 4.6.1" should "reduce as expected" in {
    val n0 = nf(Seq("w1" -> "T"), "v1" =~ "g".ap("w1"))
    val n1 = nf(Seq("w2" -> "T"), "u2" =~ "g".ap("w2") & "w2" =~ "g".ap("u3") & "w2".fin())
    val n = nf(Seq("v1" -> "T"), "v1" =~ "f".ap("u1", "u2") & "u2" =~ "g".ap("u1"), n0, n1)

    val expected =
      Seq(nf(Seq.empty, "u2" =~ "g".ap("u1"),
        nf(Seq.empty, "u1" =~ "g".ap("u3") & "u3".fin())))

    Solver.solveNf(ctx, n) should equal(expected)
    Solver.solve(ctx, n.toFormula) should equal(expected)
  }

  "Example 1 from the CHR tests" should "reduce as expected" in {
    val p1 = nf(Seq("v4" -> "T"), "w1" =~ "s".ap("v3") & "v4" =~ "s".ap("w1"))
    val p = nf(
      Seq("v1" -> "T", "v2" -> "T", "v3" -> "T"),
      "u" =~ "s".ap("v1") & "v2" =~ "f".ap("u", "v3") & "v3" =~ "f".ap("v2", "v3"),
      p1)

    val expected = Seq(nf(Seq("v1" -> "T"), "u" =~ "s".ap("v1"),
      nf(Seq("v2" -> "T", "v3" -> "T"), "v2" =~ "f".ap("u", "v3") & "w1" =~ "s".ap("v3")
        & "v3" =~ "f".ap("v2", "v3"))))

    Solver.solveNf(ctx, p) should equal(expected)
    Solver.solve(ctx, p.toFormula) should equal(expected)
  }

  "Example 2 from the CHR tests" should "be always satisfied" in {
    val p1 = nf(Seq("w1" -> "T"), "w1" =~ "s".ap("v3"))
    val p = nf(
      Seq("v1" -> "T", "v2" -> "T", "v3" -> "T"),
      "u" =~ "s".ap("v1") & "v2" =~ "f".ap("u", "v3") & "v3" =~ "f".ap("v2", "v3"),
      p1)
    Solver.solveNf(ctx, p) should equal(Seq.empty)
    Solver.solve(ctx, p.toFormula) should equal(Seq.empty)
  }

  "Example 3 from the CHR tests" should "reduce as expected" in {
    val p1 = nf(Seq.empty, "w1" =~ "s".ap("v3"))
    val p = nf(Seq("v1" -> "T", "v3" -> "T"), "u" =~ "s".ap("v1") & "v3" =~ "f".ap("v3"), p1)

    val expected = Seq(nf(
      Seq("v1" -> "T"),
      "u" =~ "s".ap("v1"), nf(
        Seq("v3" -> "T"),
        "w1" =~ "s".ap("v3") & "v3" =~ "f".ap("v3"))))

    Solver.solveNf(ctx, p) should equal(expected)
    Solver.solve(ctx, p.toFormula) should equal(expected)
  }

  "Example 4 from the CHR tests" should "reduce as expected" in {
    val p1 = nf(Seq.empty, "w1" =~ "s".ap("v3"))
    val p = nf(Seq("v2" -> "T", "v3" -> "T"), "v2" =~ "f".ap("v3") & "v3" =~ "f".ap("v2"), p1)

    val expected = Seq(nf(Seq.empty, BasicFormula.empty,
      nf(
        Seq("v2" -> "T", "v3" -> "T"),
        "v2" =~ "f".ap("v3") & "w1" =~ "s".ap("v3") & "v3" =~ "f".ap("v2"))))

    Solver.solveNf(ctx, p) should equal(expected)
    Solver.solve(ctx, p.toFormula) should equal(expected)
  }

  "Example 5 from the CHR tests" should "reduce as expected" in {
    val p1 = nf(Seq.empty, "w1" =~ "s".ap("v3"))
    val p = nf(Seq("v2" -> "T", "v3" -> "T"), "v3" =~ "f".ap("v2"), p1)
    Solver.solveNf(ctx, p) should equal(Seq(nf(Seq.empty, BasicFormula.empty)))
    Solver.solve(ctx, p.toFormula) should equal(Seq(nf(Seq.empty, BasicFormula.empty)))
  }

  "Sorts with only finite inhabitants" should "be recognized correctly" in {
    val sig = new Signature(
      Seq(Generator("true", Seq.empty, "Bool"), Generator("false", Seq.empty, "Bool")),
      Set.empty
    )
    val ctx = Context(sig, Seq.empty)
    Solver.solveNf(ctx, nf(Seq("x" -> "Bool"), BasicFormula.empty, nf(Seq.empty, "x".fin()))) should equal(Seq.empty)
  }

  "Sorts with only infinite inhabitants" should "be recognized correctly" in {
    val sig = new Signature(
      Seq(Generator("true", Seq.empty, "Bool"),
        Generator("false", Seq.empty, "Bool"),
        Generator("c1", Seq("Bool", "InfList"), "InfList"),
        Generator("c2", Seq("InfList"), "InfList")),
      Set.empty
    )
    val ctx = Context(sig, Seq.empty)
    Solver.solveNf(ctx, nf(Seq("x" -> "InfList"), "x".fin())) should equal(Seq.empty)
  }

  "Non-Cons" should "be Nil" in {
    val sig = new Signature(
      Seq(Generator("Nil", Seq.empty, "List"),
        Generator("Cons", Seq("List"), "List")),
      Set.empty
    )
    val ctx = Context(sig, Seq("x" -> "List"))
    Solver.solveNf(ctx, nf(Seq.empty, BasicFormula.empty, nf(Seq("y" -> "List"), "x" =~ "Cons".ap("y")))) should equal(
      Seq(nf(Seq.empty, "x" =~ "Nil".ap()))
    )
  }

  "Non-Cons" should "not be finite" in {
    val sig = new Signature(
      Seq(Generator("Nil", Seq.empty, "List"),
        Generator("Cons", Seq("List"), "List")),
      Set.empty
    )
    val ctx = Context(sig, Seq("x" -> "List"))
    Solver.solveNf(ctx, nf(Seq("x" -> "List"), BasicFormula.empty,
      nf(Seq("y" -> "List"), "x" =~ "Cons".ap("y")),
      nf(Seq.empty, "x".fin())
    )) should equal(
      Seq.empty
    )
  }

  val defaultSig = new Signature(
    Seq(
      Generator("false", Seq.empty, "bool"),
      Generator("true", Seq.empty, "bool"),
      Generator("zero", Seq.empty, "nat"),
      Generator("succ", Seq("nat"), "nat"),
      Generator("nil", Seq.empty, "list"),
      Generator("cons", Seq("nat", "list"), "list"),
      Generator("tree1", Seq("inftree"), "inftree"),
      Generator("tree2", Seq("inftree", "inftree"), "inftree"),
      Generator("c1", Seq("bool"), "d"),
      Generator("c2", Seq("nat", "inftree"), "d"),
    ),
    Set.empty)

  "Excluding all constructors" should "be impossible" in {
    val ctx = Context(defaultSig, Seq.empty)
    Solver.solveNf(ctx, nf(Seq("x" -> "list"), BasicFormula.empty,
      nf(Seq.empty, "x" =~ "nil".ap()),
      nf(Seq("y" -> "nat", "z" -> "list"), "x" =~ "cons".ap("y", "z"))
    )) should equal(Seq.empty)
  }

  "Nested recursive constructor equations" should "not be instantiated" in {
    val ctx = Context(defaultSig, Seq("x" -> "list"))
    val original = nf(Seq.empty, BasicFormula.empty,
      nf(Seq("y" -> "nat"), "x" =~ "cons".ap("y", "x"))
    )
    Solver.solveNf(ctx, original) should equal(Seq(original))
  }

  it should "be instantiated if there's another non-recursive constructor" in {
    val ctx = Context(defaultSig, Seq("x" -> "list"))
    val original = nf(Seq.empty, BasicFormula.empty,
      nf(Seq.empty, "x" =~ "nil".ap()),
      nf(Seq("y" -> "nat"), "x" =~ "cons".ap("y", "x"))
    )
    val expected = nf(Seq("x_cons_0" -> "nat", "x_cons_1" -> "list"),
      "x" =~ "cons".ap("x_cons_0", "x_cons_1"),
      nf(Seq.empty, "x_cons_1" =~ "x")
    )
    Solver.solveNf(ctx, original) should equal(Seq(expected))
  }

  "Counting inhabitants" should "be handled correctly" in {
    val sig = new Signature(
      Seq(Generator("a", Seq.empty, "D"),
        Generator("b", Seq(), "D"),
        Generator("None", Seq(), "Option"),
        Generator("Some", Seq("D"), "Option")),
      Set.empty
    )
    val ctx = Context(sig, Seq.empty)
    Solver.solveNf(ctx, nf(Seq("x" -> "D", "y" -> "D", "z" -> "D"), BasicFormula.empty,
      nf(Seq.empty, "x" =~ "y"),
      nf(Seq.empty, "x" =~ "z"),
      nf(Seq.empty, "y" =~ "z")
    )) should equal(Seq.empty)
    Solver.solveNf(ctx, nf(Seq("x" -> "Option", "y" -> "Option", "z" -> "Option"), BasicFormula.empty,
      nf(Seq.empty, "x" =~ "y"),
      nf(Seq.empty, "x" =~ "z"),
      nf(Seq.empty, "y" =~ "z")
    )).toSet should equal(Set(nf(Seq.empty, BasicFormula.empty)))
  }

  "Sorts with finitely many inhabitants" should "be handled correctly" in {
    val ctx = Context(defaultSig, Seq.empty)
    val original = nf(Seq("x" -> "bool"),
      BasicFormula.empty,
      nf(Seq.empty, "x" =~ "y"),
      nf(Seq.empty, "x" =~ "z")
    )
    Solver.solveNf(ctx, original) should equal(Seq.empty)
  }

  "Sorts with finitely many finite inhabitants" should "be handled correctly" in {
    val ctx = Context(defaultSig, Seq("y" -> "d", "z" -> "d"))
    val original = nf(Seq("x" -> "d"),
      "x".fin(),
      nf(Seq.empty, "x" =~ "y"),
      nf(Seq.empty, "x" =~ "z")
    )
    val expected = Set(
      nf(Seq("y_c1_0" -> "bool", "z_c1_0" -> "bool"),
        "z" =~ "c1".ap("z_c1_0") & "y" =~ "c1".ap("y_c1_0")
          & "z_c1_0" =~ "true".ap() & "y_c1_0" =~ "true".ap()),
      nf(Seq("y_c1_0" -> "bool", "z_c1_0" -> "bool"),
        "z" =~ "c1".ap("z_c1_0") & "y" =~ "c1".ap("y_c1_0")
          & "z_c1_0" =~ "false".ap() & "y_c1_0" =~ "false".ap()),
      nf(Seq("y_c1_0" -> "bool", "z_c2_0" -> "nat", "z_c2_1" -> "inftree"),
        "z" =~ "c2".ap("z_c2_0", "z_c2_1") & "y" =~ "c1".ap("y_c1_0") & "y_c1_0" =~ "true".ap()),
      nf(Seq("y_c1_0" -> "bool", "z_c2_0" -> "nat", "z_c2_1" -> "inftree"),
        "z" =~ "c2".ap("z_c2_0", "z_c2_1") & "y" =~ "c1".ap("y_c1_0") & "y_c1_0" =~ "false".ap()),
      nf(Seq("y_c2_0" -> "nat", "y_c2_1" -> "inftree", "z_c1_0" -> "bool"),
        "z" =~ "c1".ap("z_c1_0") & "y" =~ "c2".ap("y_c2_0", "y_c2_1") & "z_c1_0" =~ "true".ap()),
      nf(Seq("y_c2_0" -> "nat", "y_c2_1" -> "inftree", "z_c1_0" -> "bool"),
        "z" =~ "c1".ap("z_c1_0") & "y" =~ "c2".ap("y_c2_0", "y_c2_1") & "z_c1_0" =~ "false".ap()),
      nf(Seq("y_c2_0" -> "nat", "y_c2_1" -> "inftree", "z_c2_0" -> "nat", "z_c2_1" -> "inftree"),
        "z" =~ "c2".ap("z_c2_0", "z_c2_1") & "y" =~ "c2".ap("y_c2_0", "y_c2_1")),
    )
    Solver.solveNf(ctx, original).toSet should equal(expected)
  }

  "Sorts with finitely many infinite inhabitants" should "be handled correctly" in {
    val ctx = Context(defaultSig, Seq("y" -> "nat"))
    val original = nf(Seq("x" -> "nat"),
      BasicFormula.empty,
      nf(Seq.empty, "x".fin()),
      nf(Seq.empty, "x" =~ "y")
    )
    val intermediate = nf(Seq("x" -> "nat", "u_nat" -> "nat"),
      "x" =~ "u_nat" & "u_nat" =~ "succ".ap("u_nat"),
      nf(Seq.empty, "x" =~ "y")
    )
    val expected = Set(
      nf(Seq.empty, "y" =~ "zero".ap()),
      nf(Seq("y_succ_0" -> "nat"), "y" =~ "succ".ap("y_succ_0"),
        nf(Seq("x" -> "nat", "u_nat" -> "nat"),
          "x" =~ "succ".ap("u_nat") & "u_nat" =~ "x" & "y_succ_0" =~ "u_nat"))
    )
    Solver.solveNf(ctx, original) should equal(Solver.solveNf(ctx, intermediate))
    Solver.solveNf(ctx, original).toSet should equal(expected)
  }

  it should "be handled correctly even if that requires renaming" in {
    val ctx = Context(defaultSig, Seq("y" -> "nat"))
    val original = nf(Seq("u_nat" -> "nat"),
      BasicFormula.empty,
      nf(Seq.empty, "u_nat".fin()),
      nf(Seq.empty, "u_nat" =~ "y")
    )
    val intermediate = nf(Seq("u_nat" -> "nat", "u_nat_0" -> "nat"),
      "u_nat" =~ "u_nat_0" & "u_nat_0" =~ "succ".ap("u_nat_0"),
      nf(Seq.empty, "u_nat" =~ "y")
    )
    val expected = Set(
      nf(Seq.empty, "y" =~ "zero".ap()),
      nf(Seq("y_succ_0" -> "nat"), "y" =~ "succ".ap("y_succ_0"),
        nf(Seq("u_nat" -> "nat", "u_nat_0" -> "nat"),
          "u_nat" =~ "succ".ap("u_nat_0") & "u_nat_0" =~ "u_nat" & "y_succ_0" =~ "u_nat_0"))
    )
    Solver.solveNf(ctx, original) should equal(Solver.solveNf(ctx, intermediate))
    Solver.solveNf(ctx, original).toSet should equal(expected)
  }

  it should "be handled correctly for complex infinite inhabitants" in {
    val sig = new Signature(
      Seq(
        Generator("false", Seq.empty, "bool"),
        Generator("true", Seq.empty, "bool"),
        Generator("zero", Seq.empty, "nat"),
        Generator("succ", Seq("nat"), "nat"),
        Generator("c1", Seq("nat"), "d"),
        Generator("c2", Seq("bool"), "d"),
      ),
      Set.empty)
    val ctx = Context(sig, Seq("y" -> "d"))
    val original = nf(Seq("x" -> "d"),
      BasicFormula.empty,
      nf(Seq.empty, "x".fin()),
      nf(Seq.empty, "x" =~ "y")
    )
    val intermediate = nf(Seq("x" -> "d", "u_d" -> "d", "u_nat" -> "nat"),
      "x" =~ "u_d" & "u_d" =~ "c1".ap("u_nat") & "u_nat" =~ "succ".ap("u_nat"),
      nf(Seq.empty, "x" =~ "y")
    )
    val expected = Set(
      nf(Seq("y_c1_0" -> "nat"), "y" =~ "c1".ap("y_c1_0"),
        nf(Seq("u_nat" -> "nat"),
          "u_nat" =~ "succ".ap("u_nat") & "y_c1_0" =~ "u_nat")),
      nf(Seq("y_c2_0" -> "bool"), "y" =~ "c2".ap("y_c2_0"))
    )
    Solver.solveNf(ctx, original) should equal(Solver.solveNf(ctx, intermediate))
    Solver.solveNf(ctx, original).toSet should equal(expected)
  }

  "Problematic rule 15 applications" should "be handled correctly" in {
    val sig = new Signature(
      Seq(
        Generator("false", Seq.empty, "bool"),
        Generator("true", Seq.empty, "bool"),
        Generator("nil", Seq.empty, "list"),
        Generator("cons", Seq("bool", "list"), "list")),
      Set.empty)
    val ctx = Context(sig, Seq("x" -> "list", "y" -> "list"))
    val original = nf(Seq("v" -> "bool"), BasicFormula.empty,
      nf(Seq.empty, "x" =~ "cons".ap("v", "x")),
      nf(Seq.empty, "y" =~ "cons".ap("v", "y"))
    )
    val expected = Seq(
      nf(Seq.empty, BasicFormula.empty,
        nf(Seq("v" -> "bool"), "x" =~ "cons".ap("v", "x") & "v" =~ "false".ap()),
        nf(Seq("v" -> "bool"), "y" =~ "cons".ap("v", "y") & "v" =~ "false".ap())
      ),
      nf(Seq.empty, BasicFormula.empty,
        nf(Seq("v" -> "bool"), "x" =~ "cons".ap("v", "x") & "v" =~ "true".ap()),
        nf(Seq("v" -> "bool"), "y" =~ "cons".ap("v", "y") & "v" =~ "true".ap())
      )
    )
    Solver.solveNf(ctx, original) should equal(expected)
  }
}
