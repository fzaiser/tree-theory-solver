import scala.collection.mutable

/** A logical formula. */
sealed trait Formula {
  /** Negate the given formula. */
  def unary_! : Not = Not(this)

  /** Conjunction of two formulae. */
  def &(that: Formula): Conjunction = Conjunction((this match {
    case Conjunction(cs) => cs
    case _ => Seq(this)
  }) ++ (that match {
    case Conjunction(cs) => cs
    case _ => Seq(that)
  }))

  /** Disjunction of two formulae. */
  def |(that: Formula): Disjunction = Disjunction((this match {
    case Disjunction(cs) => cs
    case _ => Seq(this)
  }) ++ (that match {
    case Disjunction(cs) => cs
    case _ => Seq(that)
  }))

  /** Returns the free variables of the formula. */
  def freeVars: Set[String]

  /** Transforms this formula into a normal one. */
  def normalize(ctx: Context): NormalFormula = {
    val negated = negatedNormalize(ctx)
    NormalFormula(Seq.empty, BasicFormula.empty, Seq(negated))
  }

  /** Transforms the negation of this formula into a normal one. */
  def negatedNormalize(ctx: Context): NormalFormula = {
    val normal = normalize(ctx)
    NormalFormula(Seq.empty, BasicFormula.empty, Seq(normal))
  }

  /** Checks whether the formula is well-sorted and throws if it isn't.
   * Additionally, if `quantifiersAllowed` is false, throws if it encounters a quantifier. */
  def check(ctx: Context, quantifiersAllowed: Boolean = true): Unit
}

/** An equation of two terms. */
final case class Equation(s: Term, t: Term) extends Formula {
  override def toString: String = s"$s = $t"

  override def freeVars: Set[String] = s.vars ++ t.vars

  override def negatedNormalize(ctx: Context): NormalFormula = {
    val newCtx = ctx.copy()
    val (bound, eqs) = normalizeHelp(newCtx)
    NormalFormula(bound, BasicFormula(eqs.toSet, Set.empty), Seq.empty)
  }

  /** Introduces bindings and equations `v = t` (where t is flat) equivalent to this equation. */
  def normalizeHelp(ctx: Context): (Seq[Binding], Seq[(Var, FlatTerm)]) = {
    s match {
      case Var(v) => t match {
        case Var(w) => (Seq.empty, Seq((Var(v), Var(w))))
        case Term.App(label, terms) =>
          var bindings = mutable.Buffer.empty[Binding]
          var args = mutable.Buffer.empty[Var]
          var allEqs = mutable.Buffer.empty[(Var, FlatTerm)]
          for (t <- terms) {
            t match {
              case Var(x) => args += Var(x)
              case t: Term.App =>
                val y = ctx.addFreshVar(ctx.sig.generator(t.label).resultSort)
                args += y.name
                bindings += y
                val (bound, eqs) = Equation(Var(y.name), t).normalizeHelp(ctx)
                bindings ++= bound
                allEqs ++= eqs
            }
          }
          (bindings.toSeq, (Var(v), App(label, args.toSeq)) +: allEqs.toSeq)
      }
      case Term.App(f, ss) =>
        t match {
          case Var(v) => Equation(Var(v), Term.App(f, ss)).normalizeHelp(ctx)
          case Term.App(g, ts) =>
            val x = ctx.addFreshVar(ctx.sig.generator(f).resultSort)
            val (bound1, eqs1) = Equation(Var(x.name), Term.App(f, ss)).normalizeHelp(ctx)
            val (bound2, eqs2) = Equation(Var(x.name), Term.App(g, ts)).normalizeHelp(ctx)
            (x +: (bound1 ++ bound2), eqs1 ++ eqs2)
        }
    }
  }

  override def check(ctx: Context, quantifiersAllowed: Boolean): Unit = {
    val lhsSort = s.sort(ctx)
    val rhsSort = t.sort(ctx)
    if (lhsSort != rhsSort) {
      throw new InvalidInputException(s"The sides of the equation `$this` have different sorts (`$lhsSort` and `rhsSort`).")
    }
  }
}

/** Finiteness constraint. */
final case class Finite(t: Term) extends Formula {
  override def toString: String = s"fin($t)"

  override def freeVars: Set[String] = t.vars

  override def negatedNormalize(ctx: Context): NormalFormula = {
    t match {
      case Var(v) => NormalFormula(Seq.empty, BasicFormula(Set.empty, Set(Var(v))), Seq.empty)
      case t: Term.App =>
        val curCtx = ctx.copy()
        val v = curCtx.addFreshVar(ctx.sig.generator(t.label).resultSort)
        val (bound, eqs) = Equation(v.name, t).normalizeHelp(curCtx)
        NormalFormula(v +: bound, BasicFormula(eqs.toSet, Set(Var(v.name))), Seq.empty)
    }
  }

  override def check(ctx: Context, quantifiersAllowed: Boolean): Unit = {
    t.sort(ctx)
  }
}

/** Negation of a formula. */
final case class Not(f: Formula) extends Formula {
  override def freeVars: Set[String] = f.freeVars

  override def toString: String = s"!($f)"

  override def normalize(ctx: Context): NormalFormula = f.negatedNormalize(ctx)

  override def negatedNormalize(ctx: Context): NormalFormula = f.normalize(ctx)

  override def check(ctx: Context, quantifiersAllowed: Boolean): Unit = {
    f.check(ctx, quantifiersAllowed)
  }
}

/** Conjunction of formulae. */
final case class Conjunction(cs: Seq[Formula]) extends Formula {
  override def freeVars: Set[String] = Set.from(cs.flatMap(f => f.freeVars))

  override def negatedNormalize(ctx: Context): NormalFormula = {
    val nested = cs.map(f => f.normalize(ctx))
    NormalFormula(Seq.empty, BasicFormula.empty, nested)
  }

  override def &(that: Formula): Conjunction = Conjunction(this.cs ++ (that match {
    case Conjunction(ds) => ds
    case _ => Seq(that)
  }))

  override def toString: String = if (cs.isEmpty) "true" else "(" + cs.mkString(" & ") + ")"

  override def check(ctx: Context, quantifiersAllowed: Boolean): Unit = {
    cs.foreach(_.check(ctx, quantifiersAllowed))
  }
}

/** Disjunction of formulae. */
final case class Disjunction(ds: Seq[Formula]) extends Formula {
  override def freeVars: Set[String] = Set.from(ds.flatMap(f => f.freeVars))

  override def normalize(ctx: Context): NormalFormula = {
    val nested = ds.map(f => f.negatedNormalize(ctx))
    NormalFormula(Seq.empty, BasicFormula.empty, nested)
  }

  override def |(that: Formula): Disjunction = Disjunction(this.ds ++ (that match {
    case Disjunction(cs) => cs
    case _ => Seq(that)
  }))

  override def toString: String = if (ds.isEmpty) "false" else "(" + ds.mkString(" | ") + ")"

  override def check(ctx: Context, quantifiersAllowed: Boolean): Unit = {
    ds.foreach(_.check(ctx, quantifiersAllowed))
  }
}

/** Existentially quantified formula. */
final case class Exists(bound: Seq[Binding], f: Formula) extends Formula {
  override def freeVars: Set[String] = f.freeVars -- bound.map(_.name)

  override def negatedNormalize(ctx: Context): NormalFormula = {
    val curCtx = ctx.withBindings(bound)
    val normal = f.negatedNormalize(curCtx)
    NormalFormula(bound ++ normal.existential, normal.basic, normal.nested)
  }

  override def toString: String = s"(exists ${bound.mkString(", ")}. $f)"

  override def check(ctx: Context, quantifiersAllowed: Boolean): Unit = {
    if (!quantifiersAllowed) {
      throw new InvalidInputException(
        "No quantifiers are allowed in standard semantics (since there is no reduction to the theory of trees).")
    }
    f.check(ctx.withBindings(bound))
  }
}

/** Universally quantified formula. */
final case class Forall(bound: Seq[Binding], f: Formula) extends Formula {
  override def freeVars: Set[String] = f.freeVars -- bound.map(_.name)

  override def normalize(ctx: Context): NormalFormula = {
    val curCtx = ctx.withBindings(bound)
    val normal = f.normalize(curCtx)
    NormalFormula(bound ++ normal.existential, normal.basic, normal.nested)
  }

  override def toString: String = s"(forall ${bound.mkString(", ")}. $f)"

  override def check(ctx: Context, quantifiersAllowed: Boolean): Unit = {
    if (!quantifiersAllowed) {
      throw new InvalidInputException(
        "No quantifiers are allowed in standard semantics (since there is no reduction to the theory of trees).")
    }
    f.check(ctx.withBindings(bound))
  }
}

object Formula {
  def True: Conjunction = Conjunction(Seq.empty)

  def False: Disjunction = Disjunction(Seq.empty)

  def fin(t: Term): Formula = Finite(t)
}
