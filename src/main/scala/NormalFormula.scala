import scala.collection.mutable

/** Represents a normal formula. */
case class NormalFormula(existential: Seq[Binding], basic: BasicFormula, nested: Seq[NormalFormula]) {
  override def toString: String = {
    val existentialStr = if (existential.isEmpty) "" else s"exists ${existential.mkString(", ")}. "
    val basicStr = basic.toString
    val nestedStr = nested.map(" & " + _.toString).mkString("")
    s"![$existentialStr$basicStr$nestedStr]"
  }

  /** The nesting level of this normal formula. */
  def depth: Int = {
    nested.map(_.depth).maxOption.map(_ + 1).getOrElse(0)
  }

  /** The free variables occurring in the formula. */
  def computeFree(): Set[String] = {
    (basic.vars ++ nested.flatMap(_.computeFree())) -- existential.map(_.name)
  }

  /** Computes the reachable variables of the normal formula. */
  def reachableVariables(ctx: Context): Set[Var] = {
    val free = ctx.bindings.map(_.name).toSet -- existential.map(_.name)
    val f = free.map(Var)
    f ++ f.flatMap(basic.reachableFrom)
  }

  /** Computes the properly reachable variables of the normal formula. */
  def properlyReachableVariables(ctx: Context): Set[Var] = {
    val free = ctx.bindings.map(_.name).toSet -- existential.map(_.name)
    val f = free.map(Var)
    (basic.eqs.map(_._1) intersect f) ++ f.flatMap(basic.reachableFrom)
  }

  def toFormula: Formula = {
    !Exists(existential, basic.toFormula & Conjunction(nested.map(_.toFormula)))
  }

  /** Rename existential variables to avoid collisions with variables in the context. */
  def makeVarsFresh(ctx: Context): NormalFormula = {
    val renamed = mutable.Buffer.empty[String]
    val map = mutable.Map.empty[String, String]
    for (Binding(v, _) <- existential) {
      var w = v
      while (ctx.contains(w) || renamed.contains(w)) {
        w += "'"
      }
      renamed += w
      if (v != w) {
        map.update(v, w)
      }
    }
    val newMap = map.toMap
    NormalFormula(
      renamed.toSeq.zip(existential).map { case (r, b) => Binding(r, b.sort) },
      basic.rename(newMap),
      nested.map(_.rename(newMap)))
  }

  /** Rename all nested existential variables in this formula to avoid name collisions. */
  def recursivelyMakeVarsFresh(ctx: Context): NormalFormula = {
    val f = makeVarsFresh(ctx)
    f.copy(nested = f.nested.map(_.recursivelyMakeVarsFresh(ctx.withBindings(f.existential))))
  }

  /** Rename variables occurring as keys in the map. */
  def rename(map: Map[String, String]): NormalFormula = {
    val newMap = map.removedAll(existential.map(_.name))
    NormalFormula(existential, basic.rename(newMap), nested.map(_.rename(newMap)))
  }

  /** Computes the reachable variables and formulae of the basic formula. */
  def reachablePartsOfBasic(ctx: Context): (Seq[Var], BasicFormula) = {
    val properlyReachableVars = properlyReachableVariables(ctx)
    val reachableVars = reachableVariables(ctx)
    val eqs = basic.eqs.filter { case (v, _) => reachableVars.contains(v) }
    val fins = basic.fins.intersect(reachableVars)
    (existential.map(b => Var(b.name)).filter(properlyReachableVars.contains), BasicFormula(eqs, fins))
  }
}

object NormalFormula {
  /** Convenience function to make normal formulae easier to write. */
  def nf(existential: Seq[(String, String)], basic: BasicFormula, nested: NormalFormula*): NormalFormula = {
    NormalFormula(existential.map(Binding.pair2Bind), basic, nested)
  }
}
