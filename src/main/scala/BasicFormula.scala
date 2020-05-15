import scala.collection.mutable

/** A basic formula, consisting of equations (v = t) and finiteness constraints (fin(v)) */
case class BasicFormula(eqs: Set[(Var, FlatTerm)], fins: Set[Var]) {
  def toFormula: Formula = {
    Conjunction(eqs.map { case (v, t) => Equation(v, t.toTerm) }.toSeq ++ fins.map(Finite).toSeq)
  }

  /** Conjunction of two basic formulae. */
  def &(that: BasicFormula): BasicFormula = BasicFormula(this.eqs ++ that.eqs, this.fins ++ that.fins)

  /** Returns all the variable names occurring in the basic formula. */
  def vars: Set[String] = {
    var result = mutable.Set.empty[String]
    for ((v, t) <- eqs) {
      result += v.name
      t match {
        case Var(w) => result += w
        case App(_, vs) => result ++= vs.map(_.name)
      }
    }
    result ++= fins.map(_.name)
    result.toSet
  }

  /** Renames variables occurring as keys in the given map. */
  def rename(map: Map[String, String]): BasicFormula = {
    BasicFormula(eqs.map { case (v, t) => (v.rename(map), t.rename(map)) }, fins.map(v => v.rename(map)))
  }

  /** Computes the variables reachable from the given one. */
  def reachableFrom(v: Var): Set[Var] = {
    val reachable = mutable.Set.empty[Var]
    reachableFrom(v, mutable.Set.empty[Var], reachable)
    reachable.toSet
  }

  private def reachableFrom(v: Var, visited: mutable.Set[Var], reachable: mutable.Set[Var]): Unit = {
    if (visited contains v) return
    visited += v
    for ((w, t) <- eqs) {
      if (v == w) {
        t match {
          case u: Var =>
            reachable += u
            reachableFrom(u, visited, reachable)
          case App(_, args) =>
            reachable ++= args
            args.foreach(u => reachableFrom(u, visited, reachable))
        }
      }
    }
  }

  override def toString: String = {
    val eqsStr = eqs.map { case (v, t) => s"$v = $t" }.toSeq
    val finStr = fins.map(v => s"fin($v)").toSeq
    val strs = eqsStr ++ finStr
    if (strs.isEmpty) "true" else strs.mkString(" & ")
  }
}

object BasicFormula {
  /** The basic formula "true". */
  def empty: BasicFormula = BasicFormula(Set.empty[(Var, FlatTerm)], Set.empty[Var])
}
