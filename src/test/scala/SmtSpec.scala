import Binding.pair2Bind
import Term.stringToVar
import org.scalatest.matchers.should.Matchers
import org.scalatest.flatspec.AnyFlatSpec

class SmtSpec extends AnyFlatSpec with Matchers {
  "SMT files" should "be parsed correctly" in {
    val actual = Smt.parse(
      """
        |(set-info :smt-lib-version 2.6)
        |(set-logic QF_DT)
        |(set-info :source |
        |Generated by: Andrew Reynolds
        |Generated on: 2017-04-28
        |Generator: Random, converted to v2.6 by CVC4
        |Application: Regressions for datatypes decision procedure.
        |Target solver: CVC3
        |Publications: "An Abstract Decision Procedure for Satisfiability in the Theory of Inductive Data Types"
        |by Clark Barrett, Igor Shikanian, and Cesare Tinelli,
        |Journal on Satisfiability, Boolean Modeling and Computation 2007.
        ||)
        |(set-info :license "https://creativecommons.org/licenses/by/4.0/")
        |(set-info :category "random")
        |(set-info :status sat)
        |
        |
        |(declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))
        |((cons (car tree) (cdr list)) (null))
        |((node (children list)) (leaf (data nat)))
        |))
        |(declare-fun x1 () nat)
        |(declare-fun x2 () nat)
        |(declare-fun x3 () nat)
        |(declare-fun x4 () nat)
        |(declare-fun x5 () nat)
        |(declare-fun x6 () nat)
        |(declare-fun x7 () nat)
        |(declare-fun x8 () nat)
        |(declare-fun x9 () nat)
        |(declare-fun x10 () nat)
        |(declare-fun x11 () list)
        |(declare-fun x12 () list)
        |(declare-fun x13 () list)
        |(declare-fun x14 () list)
        |(declare-fun x15 () list)
        |(declare-fun x16 () list)
        |(declare-fun x17 () list)
        |(declare-fun x18 () list)
        |(declare-fun x19 () list)
        |(declare-fun x20 () list)
        |(declare-fun x21 () tree)
        |(declare-fun x22 () tree)
        |(declare-fun x23 () tree)
        |(declare-fun x24 () tree)
        |(declare-fun x25 () tree)
        |(declare-fun x26 () tree)
        |(declare-fun x27 () tree)
        |(declare-fun x28 () tree)
        |(declare-fun x29 () tree)
        |(declare-fun x30 () tree)
        |
        |(assert (and (and (not (= x21 x26)) ((_ is cons) x11)) (not ((_ is succ) x2))))
        |(check-sat)
        |(exit)
        |
        |""".stripMargin)
    val decls = Seq(
      DatatypeDecl("nat", Seq(ConDecl("succ", Seq(("pred", "nat"))), ConDecl("zero", Seq.empty))),
      DatatypeDecl("list", Seq(ConDecl("cons", Seq(("car", "tree"), ("cdr", "list"))), ConDecl("null", Seq.empty))),
      DatatypeDecl("tree", Seq(ConDecl("node", Seq(("children", "list"))), ConDecl("leaf", Seq(("data", "nat")))))
    )
    val vars = (1 to 30).map(n => Binding(s"x$n", if (n <= 10) "nat" else if (n <= 20) "list" else "tree"))
    val assertion = Conjunction(Seq(
      !Equation("x21", "x26"),
      Exists(Seq("car" -> "tree", "cdr" -> "list"), Equation("x11", "cons".app("car", "cdr"))),
      !Exists(Seq("pred" -> "nat"), Equation("x2", "succ".app("pred")))
    ))
    val expected = Smt(DatatypeInstance(decls, vars, assertion), isSat = true)
    actual should equal(expected)
  }
}
