import scala.language.implicitConversions

sealed trait Term {
  /** A convenience function to be able to write `s ~ t` for the formula "s = t". */
  def ~(that: Term): Equation = Equation(this, that)

  /** Returns all the variables occurring in the term. */
  def vars: Set[String]

  /** Checks whether the term is well-sorted and returns its sort; otherwise throws. */
  def sort(ctx: Context): String
}

object Term {
  /** A convenience function to implicitly convert a string to a variable. */
  implicit def stringToVar(s: String): Var = Var(s)

  final case class App(label: String, terms: Seq[Term]) extends Term {

    override def vars: Set[String] = Set.from(terms.flatMap(t => t.vars))

    override def toString = s"$label(${terms.mkString(",")})"

    override def sort(ctx: Context): String = {
      if (!ctx.sig.generators.contains(label)) {
        throw new InvalidInputException(s"The function `$label` used in the term `$this` does not exist.")
      }
      val generator = ctx.sig.generator(label)
      terms.zip(generator.paramSorts).foreach { case (term, expected) =>
        val found = term.sort(ctx)
        if (found != expected) {
          throw new InvalidInputException(
            s"In `$this`, the argument `$term` has sort `$found` but should have sort `$expected`.")
        }
      }
      generator.resultSort
    }
  }
}

/** A term without nested applications. */
sealed trait FlatTerm {
  /** Rename the variables occurring as keys in the map. */
  def rename(r: Map[String, String]): FlatTerm

  def toTerm: Term
}

final case class Var(name: String) extends FlatTerm with Term {
  override def toString: String = name

  /** A convenience function to be able to write "f".ap() instead of App("f", Seq.empty) */
  def ap(vars: Var*): FlatTerm = App(name, vars)

  /** A convenience function to be able to write "f".app() instead of Term.App("f", Seq.empty) */
  def app(terms: Term*): Term = Term.App(name, terms)

  /** A convenience function to be able to write the basic formula `v =~ t`. */
  def =~(t: FlatTerm): BasicFormula = BasicFormula(Set((this, t)), Set.empty)

  /** A convenience function to be able to write `v.fin()` for the basic formula "fin(v)". */
  def fin(): BasicFormula = BasicFormula(Set.empty, Set(this))

  override def vars: Set[String] = Set(name)

  override def rename(r: Map[String, String]): Var = Var(r.getOrElse(name, name))

  override def toTerm: Term = this

  override def sort(ctx: Context): String = {
    if (ctx.contains(name)) {
      ctx.sortOf(name)
    } else {
      throw new InvalidInputException(s"Variable `$name` not found.")
    }
  }
}

/** An application of the function symbol `label` to the arguments `args`. */
final case class App(label: String, args: Seq[Var]) extends FlatTerm {
  override def toString: String = s"$label(${args.mkString(",")})"

  override def rename(r: Map[String, String]): App = App(label, args.map(v => v.rename(r)))

  override def toTerm: Term = Term.App(label, args.map(_.toTerm))
}
