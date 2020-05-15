import Binding.pair2Bind
import Term.stringToVar
import org.scalatest.matchers.should.Matchers
import org.scalatest.flatspec.AnyFlatSpec

class DatatypeReductionSpec extends AnyFlatSpec with Matchers {
  "Selector elimination" should "create the correct functional consistency constraint" in {
    val decls = Seq(
      DatatypeDecl("nat", Seq(ConDecl("succ", Seq(("pred", "nat"))), ConDecl("zero", Seq.empty))),
      DatatypeDecl("list", Seq(ConDecl("cons", Seq(("car", "tree"), ("cdr", "list"))), ConDecl("null", Seq.empty))),
      DatatypeDecl("tree", Seq(ConDecl("node", Seq(("children", "list"))), ConDecl("leaf", Seq(("data", "nat")))))
    )
    val vars: Seq[Binding] = Seq("a" -> "list", "b" -> "list", "c" -> "list")
    val assertion = Equation("car".app("a"), "car".app("cdr".app("b")))
    val instance = DatatypeInstance(decls, vars, assertion)
    val (ctx, actual) = DatatypeReduction.eliminateSelectors(instance, StandardSemantics)
    val expected = Conjunction(Seq(
      !Exists(Seq("_0" -> "tree", "_1" -> "list"), Equation("b", "cons".app("_0", "_1")))
        | Exists(Seq("_0" -> "tree"), Equation("b", "cons".app("_0", "_cdr"))),
      !Equation("a", "_cdr") | Equation("_car", "_car_0"),
      !Exists(Seq("_0" -> "tree", "_1" -> "list"), Equation("a", "cons".app("_0", "_1")))
        | Exists(Seq("_1" -> "list"), Equation("a", "cons".app("_car", "_1"))),
      !Exists(Seq("_0" -> "tree", "_1" -> "list"), Equation("_cdr", "cons".app("_0", "_1")))
        | Exists(Seq("_1" -> "list"), Equation("_cdr", "cons".app("_car_0", "_1"))),
      Equation("_car", "_car_0")
    ))
    ctx.sig.sorts.keys should equal(Set("nat", "list", "tree"))
    ctx.sig.generators.keys should be(Set("succ", "zero", "cons", "null", "node", "leaf"))
    ctx.bindings.toSet should be(Set(
      "a" -> "list",
      "b" -> "list",
      "c" -> "list",
      "_car" -> "tree",
      "_car_0" -> "tree",
      "_cdr" -> "list"): Set[Binding])
    actual should be(expected)
  }

  "Selector elimination" should "work correctly for default-value selectors" in {
    val decls = Seq(
      DatatypeDecl("nat", Seq(ConDecl("succ", Seq(("pred", "nat"))), ConDecl("zero", Seq.empty))),
      DatatypeDecl("list", Seq(ConDecl("cons", Seq(("car", "tree"), ("cdr", "list"))), ConDecl("null", Seq.empty))),
      DatatypeDecl("tree", Seq(ConDecl("node", Seq(("children", "list"))), ConDecl("leaf", Seq(("data", "nat")))))
    )
    val vars: Seq[Binding] = Seq("a" -> "list", "b" -> "list", "c" -> "list")
    val assertion = Equation("car".app("a"), "car".app("cdr".app("b")))
    val instance = DatatypeInstance(decls, vars, assertion)
    val (ctx, actual) = DatatypeReduction.eliminateSelectors(instance, DefaultValueSemantics)
    val expected = Exists(Seq("_cdr" -> "list", "_car" -> "tree", "_car_0" -> "tree"), Conjunction(Seq(
      Equation("_car", "_car_0"),
      Exists(Seq("_0" -> "tree", "_1" -> "list"),
        Equation("a", "cons".app("_0", "_1")) & Equation("_car", "_0"))
        | (!Exists(Seq("_0" -> "tree", "_1" -> "list"),
        Equation("a", "cons".app("_0", "_1"))) & Equation("_car", "default_tree")),
      Exists(Seq("_0" -> "tree", "_1" -> "list"),
        Equation("_cdr", "cons".app("_0", "_1")) & Equation("_car_0", "_0"))
        | (!Exists(Seq("_0" -> "tree", "_1" -> "list"),
        Equation("_cdr", "cons".app("_0", "_1"))) & Equation("_car_0", "default_tree")),
      Exists(Seq("_0" -> "tree", "_1" -> "list"),
        Equation("b", "cons".app("_0", "_1")) & Equation("_cdr", "_1"))
        | (!Exists(Seq("_0" -> "tree", "_1" -> "list"),
        Equation("b", "cons".app("_0", "_1"))) & Equation("_cdr", "default_list"))
    )))
    ctx.sig.sorts.keys should equal(Set("nat", "list", "tree"))
    ctx.sig.generators.keys should be(Set("succ", "zero", "cons", "null", "node", "leaf"))
    ctx.bindings.toSet should be(Set("a" -> "list", "b" -> "list", "c" -> "list",
      "default_list" -> "list", "default_tree" -> "tree"): Set[Binding])
    actual should be(expected)
  }

  "Finiteness constraints" should "be added for datatypes" in {
    val decls = Seq(
      DatatypeDecl("nat", Seq(ConDecl("succ", Seq(("pred", "nat"))), ConDecl("zero", Seq.empty))),
      DatatypeDecl("list", Seq(ConDecl("cons", Seq(("car", "tree"), ("cdr", "list"))), ConDecl("null", Seq.empty))),
      DatatypeDecl("tree", Seq(ConDecl("node", Seq(("children", "list"))), ConDecl("leaf", Seq(("data", "nat")))))
    )
    val vars: Seq[Binding] = Seq("a" -> "list", "b" -> "list")
    val assertion = Not(Equation("a", "b"))
    val instance = DatatypeInstance(decls, vars, assertion)
    val result = DatatypeReduction.reduce(instance, StandardSemantics, negate = false)
    result._2.basic should equal("a".fin() & "b".fin())
  }

  "Finiteness constraints" should "not be added for codatatypes" in {
    val decls = Seq(
      DatatypeDecl("codat", Seq(ConDecl("c", Seq.empty), ConDecl("d", Seq.empty)), isCodata = true)
    )
    val vars: Seq[Binding] = Seq("a" -> "codat", "b" -> "codat")
    val assertion = Not(Equation("a", "b"))
    val instance = DatatypeInstance(decls, vars, assertion)
    val result = DatatypeReduction.reduce(instance, StandardSemantics, negate = false)
    result._2.basic should equal(BasicFormula.empty)
  }
}
