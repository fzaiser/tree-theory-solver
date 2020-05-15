import scala.collection.mutable

/** Contains all the rewrite rules used in the solver.
 * The numbering follows the article "Djelloul, Dao and Frühwirth: Theory of finite or infinite trees revisited".
 */
object Rule {
    /** Applies a transformation to a basic formula inside a given normal formula. */
  def applyToNf(f: (Context, BasicFormula) => BasicFormula, ctx: Context, nf: NormalFormula): NormalFormula =
    nf.copy(basic = f(ctx.withBindings(nf.existential), nf.basic))

  /** Removes tautologies. */
  def rule1(bf: BasicFormula): BasicFormula = {
    bf.copy(eqs = bf.eqs.filterNot { case (v, t) => t == v })
  }

  /** Adjusts the LHS and RHS of variable-variable equations. */
  def rule2(ctx: Context, bf: BasicFormula): BasicFormula = {
    bf.copy(eqs = bf.eqs.map(adjustOrder(ctx, _)))
  }

  def adjustOrder(ctx: Context, eq: (Var, FlatTerm)): (Var, FlatTerm) = {
    val (Var(v), t) = eq
    t match {
      case Var(w) => if (ctx.indexOf(w) > ctx.indexOf(v)) {
        return (Var(w), Var(v))
      }
      case _ =>
    }
    eq
  }

  /** Makes further adjustments to the variable ordering. */
  def rule3(ctx: Context, bf: BasicFormula): BasicFormula = {
    val innerToOuter = mutable.Map.empty[String, String]
    for ((Var(v), t) <- bf.eqs) {
      t match {
        case Var(w) => if (ctx.indexOf(v) > ctx.indexOf(w)) {
          val doUpdate = innerToOuter.get(v) match {
            case Some(u) => ctx.indexOf(u) > ctx.indexOf(w)
            case None => true
          }
          if (doUpdate) innerToOuter.update(v, w)
        }
        case _ =>
      }
    }
    val newEqs = bf.eqs.map { case (Var(v), t) => innerToOuter.get(v) match {
      case None => (Var(v), t)
      case Some(w) => if (t == Var(w)) (Var(v), t) else (Var(w), t)
    }
    }
    bf.copy(eqs = newEqs)
  }

  /** Checks for conflicting equations. */
  def rule4(bf: BasicFormula): Option[BasicFormula] = {
    if (isConflicting(bf)) None else Some(bf)
  }

  def isConflicting(bf: BasicFormula): Boolean = {
    val varToLabel = mutable.Map.empty[String, String]
    for ((Var(v), t) <- bf.eqs) {
      t match {
        case App(l, _) => varToLabel.get(v) match {
          case Some(l2) => if (l != l2) return true
          case None => varToLabel.update(v, l)
        }
        case _ =>
      }
    }
    false
  }

  /** Performs "unification" on generator applications.
   * Note: This could be combined with rule 4
   */
  def rule5(bf: BasicFormula): BasicFormula = {
    val varToLabel = mutable.Map.empty[String, App]
    bf.copy(eqs = bf.eqs.flatMap { case (Var(v), t) => t match {
      case App(g, ws) => varToLabel.get(v) match {
        case Some(App(f, vs)) if f == g =>
          assert(vs.size == ws.size)
          vs.zip(ws)
        case _ =>
          varToLabel.update(v, App(g, ws))
          Seq((Var(v), t))
      }
      case _ => Seq((Var(v), t))
    }
    })
  }

  /** Adjusts the variables in finiteness constraints according to the variable ordering. */
  def rule8(ctx: Context, bf: BasicFormula): BasicFormula = {
    val innerToOuter = mutable.Map.empty[String, String] // maps a variable to an equal outer variable
    for ((Var(v), t) <- bf.eqs) {
      t match {
        case Var(w) => if (ctx.indexOf(v) > ctx.indexOf(w)) {
          val doUpdate = innerToOuter.get(v) match {
            case Some(u) => ctx.indexOf(u) > ctx.indexOf(w)
            case None => true
          }
          if (doUpdate) innerToOuter.update(v, w)
        }
        case _ =>
      }
    }
    val newFins = bf.fins.map { case Var(v) => innerToOuter.get(v) match {
      case None => Var(v)
      case Some(w) => Var(w)
    }
    }
    bf.copy(fins = newFins)
  }

  /** Checks for impossible finiteness constraints because of recursive equations. */
  def rule9(bf: BasicFormula): Option[BasicFormula] = {
    for (v <- bf.fins) {
      if (bf.reachableFrom(v) contains v) {
        return None
      }
    }
    Some(bf)
  }

  /** Pushes finiteness constraints into arguments of applications. */
  def rule10(bf: BasicFormula): BasicFormula = {
    val newFins = bf.fins.flatMap(u => {
      val eqs = bf.eqs.filter { case (v, _) => v == u }
      if (eqs.isEmpty) {
        Set(u)
      } else {
        eqs.flatMap { case (_, t) => t match {
          case App(_, ws) => ws.toSet
          case _ => Seq(u)
        }
        }
      }
    })
    bf.copy(fins = newFins)
  }

  /** Checks for redundant finiteness constraints, i.e. if all/no inhabitants of the sort are finite. */
  def redundantFinitenessRule(ctx: Context, bf: BasicFormula): Option[BasicFormula] = {
    Some(bf.copy(fins = bf.fins.filterNot(v => {
      val sort = ctx.sig.sort(ctx.sortOf(v.name))
      if (sort.allInfinite)
        return None
      else
        sort.allFinite
    })))
  }

  /** Copies the basic formula inwards into the nested normal formulae. */
  def rule12(ctx: Context, nf: NormalFormula): NormalFormula = {
    val nnf = nf.makeVarsFresh(ctx).copy(nested = nf.nested.map(_.makeVarsFresh(ctx.withBindings(nf.existential))))
    nnf.copy(nested = nnf.nested.map(n => n.copy(basic = n.basic & nnf.basic)))
  }

  /** Restores some equations in nested normal formulae to the ones in the basic formula. */
  def rule13(nf: NormalFormula): NormalFormula = {
    nf.copy(nested = nf.nested.map(propagateInwards(nf.basic, _)))
  }

  def propagateInwards(outer: BasicFormula, inner: NormalFormula): NormalFormula = {
    val varToRhs = outer.eqs.toMap
    val newEqs = inner.basic.eqs.map { case (v, t) => varToRhs.get(v) match {
      case Some(s) => (v, s)
      case None => (v, t)
    }
    }
    inner.copy(basic = inner.basic.copy(eqs = newEqs))
  }

  /** Checks for contradicting nested formulae. */
  def rule14(nf: NormalFormula): Option[NormalFormula] = {
    for (n <- nf.nested) {
      if (n.nested.isEmpty && n.basic.eqs.subsetOf(nf.basic.eqs) && n.basic.fins.subsetOf(nf.basic.fins)) {
        return None
      }
    }
    Some(nf)
  }

  /** Removes unreachable parts of this normal formulae. */
  def rule15(ctx: Context, nf: NormalFormula): NormalFormula = {
    if (nf.depth > 1) {
      return nf
    }
    val rrvars = nf.reachableVariables(ctx)
    val (x1, basic1) = nf.reachablePartsOfBasic(ctx)
    val x1bdg = nf.existential.filter(b => x1.exists(_.name == b.name))
    val unreachableFins = nf.basic.fins -- basic1.fins
    val unreachableEqs = nf.basic.eqs.filterNot { case (v, _) => rrvars contains v }
    val unreachableLhsVars = nf.existential.filter(
      v => !(x1 contains Var(v.name)) && unreachableEqs.exists { case (w, _) => v.name == w.name })
    val x2: Seq[Binding] = nf.existential.diff(x1bdg ++ unreachableLhsVars)
    val newNested = nf.nested.flatMap(n => {
      val b_star = n.basic.copy(fins = n.basic.fins.diff(unreachableFins))
      val (y2, b2) = NormalFormula(unreachableLhsVars ++ n.existential, b_star, Seq.empty)
        .reachablePartsOfBasic(ctx.withBindings(nf.existential))
      if (x2.map(_.name).toSet.intersect(b2.vars).isEmpty) {
        Seq(n.copy(
          existential = (unreachableLhsVars ++ n.existential).filter(b => y2.exists(_.name == b.name)),
          basic = b2))
      } else {
        Seq.empty
      }
    })
    nf.copy(
      existential = nf.existential.filter(b => x1.exists(_.name == b.name)),
      basic = basic1,
      nested = newNested
    )
  }

  /** Reduces the depth of this normal formulae if > 2. */
  def rule16(nf: NormalFormula): (NormalFormula, Seq[NormalFormula]) = {
    nf.nested.find(n => n.nested.nonEmpty && n.nested.forall(_.nested.isEmpty)) match {
      case None => (nf, Seq.empty)
      case Some(reduct) =>
        val x = nf.existential
        val y = reduct.existential
        val rest = nf.nested.diff(Seq(reduct))
        val triplyNested = reduct.nested
        val reduced = reduct.copy(nested = Seq.empty)
        val first = nf.copy(nested = reduced +: rest)
        (first, triplyNested.map(c => {
          c.copy(existential = x ++ y ++ c.existential, nested = c.nested ++ rest)
        }))
    }
  }

}
