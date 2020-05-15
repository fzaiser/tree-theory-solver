import Term.stringToVar
import org.scalatest.matchers.should.Matchers
import org.scalatest.flatspec.AnyFlatSpec

class SignatureSpec extends AnyFlatSpec with Matchers {
  "Option[Bool]" should "be recognized correctly" in {
    val sig = new Signature(Seq(
      Generator("true", Seq.empty, "bool"),
      Generator("false", Seq.empty, "bool"),
      Generator("none", Seq.empty, "option"),
      Generator("some", Seq("bool"), "option")), Set.empty)
    val bool = sig.sorts("bool")
    bool.hasUniqueInfinite should equal(false)
    bool.allInfinite should equal(false)
    bool.allFinite should equal(true)
    bool.hasFinInfinite should equal(true)
    bool.hasFinFinite should equal(true)
    val option = sig.sorts("option")
    option.hasUniqueInfinite should equal(false)
    option.allInfinite should equal(false)
    option.allFinite should equal(true)
    option.hasFinInfinite should equal(true)
    option.hasFinFinite should equal(true)
  }

  "List[Bool]" should "be recognized correctly" in {
    val sig = new Signature(Seq(
      Generator("true", Seq.empty, "bool"),
      Generator("false", Seq.empty, "bool"),
      Generator("nil", Seq.empty, "list"),
      Generator("cons", Seq("bool", "list"), "list")), Set.empty)
    val bool = sig.sorts("bool")
    bool.hasUniqueInfinite should equal(false)
    bool.allInfinite should equal(false)
    bool.allFinite should equal(true)
    bool.hasFinInfinite should equal(true)
    bool.hasFinFinite should equal(true)
    val list = sig.sorts("list")
    list.hasUniqueInfinite should equal(false)
    list.allInfinite should equal(false)
    list.allFinite should equal(false)
    list.hasFinFinite should equal(false)
    list.hasFinInfinite should equal(false)
  }

  "InfList[Bool]" should "be recognized correctly" in {
    val sig = new Signature(Seq(
      Generator("true", Seq.empty, "bool"),
      Generator("false", Seq.empty, "bool"),
      Generator("cons1", Seq("bool", "inflist"), "inflist"),
      Generator("cons2", Seq("bool", "inflist"), "inflist")), Set.empty)
    val bool = sig.sorts("bool")
    bool.hasUniqueInfinite should equal(false)
    bool.allInfinite should equal(false)
    bool.allFinite should equal(true)
    bool.hasFinInfinite should equal(true)
    bool.hasFinFinite should equal(true)
    val inflist = sig.sorts("inflist")
    inflist.hasUniqueInfinite should equal(false)
    inflist.allInfinite should equal(true)
    inflist.allFinite should equal(false)
    inflist.hasFinInfinite should equal(false)
    inflist.hasFinFinite should equal(true)
  }

  "Unique infinite nat" should "be recognized correctly" in {
    val sig = new Signature(Seq(
      Generator("true", Seq.empty, "bool"),
      Generator("false", Seq.empty, "bool"),
      Generator("zero", Seq.empty, "nat"),
      Generator("succ", Seq("nat"), "nat"),
      Generator("wrap", Seq("nat"), "wrapped"),
      Generator("wrap2", Seq("bool"), "wrapped")), Set.empty)
    val nat = sig.sorts("nat")
    nat.hasUniqueInfinite should equal(true)
    nat.allInfinite should equal(false)
    nat.allFinite should equal(false)
    nat.hasFinInfinite should equal(true)
    nat.hasFinFinite should equal(false)
    val wrapped = sig.sorts("wrapped")
    wrapped.hasUniqueInfinite should equal(true)
    wrapped.allInfinite should equal(false)
    wrapped.allFinite should equal(false)
    wrapped.hasFinInfinite should equal(true)
    wrapped.hasFinFinite should equal(false)
  }

  "Another example" should "work correctly" in {
    val sig = new Signature(Seq(
      Generator("true", Seq.empty, "bool"),
      Generator("false", Seq.empty, "bool"),
      Generator("zero", Seq.empty, "nat"),
      Generator("succ", Seq("nat"), "nat"),
      Generator("nil", Seq.empty, "list"),
      Generator("cons", Seq("nat", "list"), "list"),
      Generator("tree1", Seq("inftree"), "inftree"),
      Generator("tree2", Seq("inftree", "inftree"), "inftree"),
      Generator("c1", Seq("bool"), "d"),
      Generator("c2", Seq("nat", "inftree"), "d"),
      Generator("f1", Seq("bool"), "e"),
      Generator("f2", Seq("nat"), "e"),
      Generator("g1", Seq("nat", "e"), "ee"),
      Generator("g2", Seq("nat"), "ee")),
      Set.empty)
    val bool = sig.sorts("bool")
    bool.hasUniqueInfinite should equal(false)
    bool.allInfinite should equal(false)
    bool.allFinite should equal(true)
    bool.hasFinInfinite should equal(true)
    bool.hasFinFinite should equal(true)
    bool.finiteInhabitants should equal(Set("true".app(), "false".app()))
    bool.infiniteInhabitants should equal(Set.empty)
    val nat = sig.sorts("nat")
    nat.hasUniqueInfinite should equal(true)
    nat.allInfinite should equal(false)
    nat.allFinite should equal(false)
    nat.hasFinInfinite should equal(true)
    nat.hasFinFinite should equal(false)
    val expectedUniqueInf = ("u_nat", "succ".ap("u_nat"))
    nat.uniqueInfiniteInhabitant should equal(Some(expectedUniqueInf))
    nat.infiniteInhabitants should equal(Set(Var("u_nat")))
    val list = sig.sorts("list")
    list.hasUniqueInfinite should equal(false)
    list.allInfinite should equal(false)
    list.allFinite should equal(false)
    list.hasFinInfinite should equal(false)
    list.hasFinFinite should equal(false)
    val inftree = sig.sorts("inftree")
    inftree.hasUniqueInfinite should equal(false)
    inftree.allInfinite should equal(true)
    inftree.allFinite should equal(false)
    inftree.hasFinInfinite should equal(false)
    inftree.hasFinFinite should equal(true)
    inftree.finiteInhabitants should equal(Set.empty)
    val d = sig.sorts("d")
    d.hasUniqueInfinite should equal(false)
    d.allInfinite should equal(false)
    d.allFinite should equal(false)
    d.hasFinInfinite should equal(false)
    d.hasFinFinite should equal(true)
    d.finiteInhabitants should equal(Set("c1".app("true".app()), "c1".app("false".app())))
    val e = sig.sorts("e")
    e.hasUniqueInfinite should equal(true)
    e.allInfinite should equal(false)
    e.allFinite should equal(false)
    e.hasFinInfinite should equal(true)
    e.hasFinFinite should equal(false)
    e.infiniteInhabitants should equal(Set(Var("u_e")))
    e.uniqueInfiniteInhabitant should equal(Some(("u_e", "f2".ap("u_nat"))))
    val ee = sig.sorts("ee")
    ee.hasUniqueInfinite should equal(false)
    ee.allInfinite should equal(false)
    ee.allFinite should equal(false)
    ee.hasFinInfinite should equal(false)
    ee.hasFinFinite should equal(false)
  }

  "Infinite individuals" should "be generated correctly" in {
    val sig = new Signature(Seq(
      Generator("true", Seq.empty, "bool"),
      Generator("false", Seq.empty, "bool"),
      Generator("zero", Seq.empty, "nat"),
      Generator("succ", Seq("nat"), "nat"),
      Generator("a", Seq("bool"), "d"),
      Generator("b", Seq("bool", "nat"), "d")),
      Set.empty)
    val d = sig.sorts("d")
    d.hasUniqueInfinite should equal(false)
    d.allInfinite should equal(false)
    d.allFinite should equal(false)
    d.hasFinInfinite should equal(true)
    d.infiniteInhabitants should equal(Set("b".app("true".app(), "u_nat"), "b".app("false".app(), "u_nat")))
    d.hasFinFinite should equal(false)
  }

  "Open sorts" should "be classified correctly" in {
    val sig = new Signature(Seq(
      Generator("true", Seq.empty, "bool"),
      Generator("false", Seq.empty, "bool"),
      Generator("zero", Seq.empty, "nat"),
      Generator("succ", Seq("nat"), "nat"),
      Generator("wrap", Seq("nat"), "wrapped"),
      Generator("wrap2", Seq("bool"), "wrapped")), Set("bool", "nat", "wrapped"))
    for (sortName <- Seq("bool", "nat", "wrapped")) {
      val sort = sig.sorts(sortName)
      sort.hasUniqueInfinite should equal(false)
      sort.allInfinite should equal(false)
      sort.allFinite should equal(false)
      sort.hasFinFinite should equal(false)
      sort.hasFinInfinite should equal(false)
    }
  }
}
