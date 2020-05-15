import scala.collection.mutable

object Solver {
  /** Solve (simplify) a formula, given a context.
   * Returns a sequence of normal formulae whose conjunction is equivalent to the given one.
   */
  def solve(ctx: Context, f: Formula): Seq[NormalFormula] = {
    new Solver().solve(ctx, f)
  }

  /** Solve a normal formula, given a context.
   * Returns a sequence of normal formulae whose conjunction is equivalent to the given one.
   */
  def solveNf(ctx: Context, nf: NormalFormula): Seq[NormalFormula] = {
    new Solver().solveNf(ctx, nf)
  }
}

/** A pretty direct implementation of the pseudocode from the paper. */
class Solver {
  /** Whether the computation should be stopped (timeout). */
  @volatile var shouldStop: Boolean = false

  /** Solve (simplify) a formula, given a context.
   * Returns a sequence of normal formulae whose conjunction is equivalent to the given one.
   */
  def solve(ctx: Context, f: Formula): Seq[NormalFormula] = {
    solveNf(ctx, f.normalize(ctx))
  }

  /** Solves the given normal formula.
   * If `simplify` is true, conjuncts introduced by Rule 12 (which are superfluous at the end) will be removed again.
   */
  def solveNf(ctx: Context, nf: NormalFormula, simplify: Boolean = true): Seq[NormalFormula] = {
    val newCtx = ctx.keepOnly(nf.computeFree().toSeq: _*)
    val n = solveBasic(newCtx, nf) match {
      case None => return Seq.empty
      case Some(n) => n
    }
    val result = solveNested(newCtx, n)
    if (simplify) {
      result.map(removePropagatedConstraints(_))
    } else {
      result
    }
  }

  /** Removes parts of basic formulae that also occur in the parent basic formula (normally introduced by Rule 12). */
  def removePropagatedConstraints(nf: NormalFormula, toRemove: BasicFormula = BasicFormula.empty): NormalFormula = {
    val newBasic = nf.basic.copy(eqs = nf.basic.eqs -- toRemove.eqs, fins = nf.basic.fins -- toRemove.fins)
    nf.copy(basic = newBasic, nested = nf.nested.map(removePropagatedConstraints(_, nf.basic)))
  }

  /** Solves the basic formula inside the given normal formula. */
  def solveBasic(ctx: Context, nf: NormalFormula): Option[NormalFormula] = {
    solveBasic(ctx.withBindings(nf.existential), nf.basic).map(newBasic => nf.copy(basic = newBasic))
  }

  /** Solves the given basic formula. */
  def solveBasic(ctx: Context, bf: BasicFormula): Option[BasicFormula] = {
    var b = bf
    var prev = b
    // Stage 1: solve equations in the basic formula
    do {
      prev = b
      b = Rule.rule1(b)
      b = Rule.rule2(ctx, b)
      b = Rule.rule3(ctx, b)
      b = Rule.rule4(b) match {
        case None => return None
        case Some(b) => b
      }
      b = Rule.rule5(b)
    } while (b != prev)
    // Stage 2: solve fin(...)-constraints in the basic formula
    do {
      prev = b
      b = Rule.rule8(ctx, b)
      b = Rule.rule9(b) match {
        case None => return None
        case Some(b) => b
      }
      b = Rule.rule10(b)
      b = Rule.redundantFinitenessRule(ctx, b) match {
        case None => return None
        case Some(b) => b
      }
    } while (b != prev)
    // now at stage 3: solveNested is next
    Some(b)
  }

  /** Solves the nested normal formulae inside the given normal formula (assuming its basic formula is solved). */
  def solveNested(ctx: Context, nf: NormalFormula): Seq[NormalFormula] = {
    var n = nf
    n = Rule.rule12(ctx, n)
    n = n.copy(nested = n.nested.flatMap(solveBasic(ctx.withBindings(n.existential), _)))
    n = Rule.rule13(n)
    n = n.copy(nested = n.nested.flatMap(solveNested(ctx.withBindings(n.existential), _)))
    val result = solveFinal(ctx, n)
    result
  }

  /** Performs the final steps to solve the given normal formula. */
  def solveFinal(ctx: Context, nf: NormalFormula): Seq[NormalFormula] = {
    if (shouldStop) {
      throw ComputationStoppedException
    }
    // Check for contradictions:
    val n = Rule.rule14(nf) match {
      case None => return Seq.empty
      case Some(n) => n
    }
    // Depth reduction:
    assert(n.depth <= 2)
    if (n.depth >= 2) {
      val (first, rest) = Rule.rule16(n)
      val firstSolved = solveFinal(ctx, first)
      val restSolved = rest.flatMap(solveNested(ctx, _))
      firstSolved ++ restSolved
    } else {
      // Check for instantiable variables:
      findInstantiation(ctx, n) match {
        case None =>
          // Remove unreachable parts:
          val reachable = Rule.rule15(ctx, n)
          Seq(reachable)
        case Some(instantiations) =>
          // Instantiation step:
          instantiations.flatMap { case (bindings, instantiation) =>
            val instantiated = n.copy(existential = n.existential ++ bindings, basic = n.basic & instantiation)
            val result = solveNf(ctx, instantiated, simplify = false)
            result
          }
      }
    }
  }

  /** Looks for an instantiable variable in the normal formula and returns all possible instantiations if successful. */
  def findInstantiation(ctx: Context, nf: NormalFormula): Option[Seq[(Seq[Binding], BasicFormula)]] = {
    val newCtx = ctx.withBindings(nf.existential)
    for (b <- newCtx.bindings) {
      val reduced = removePropagatedConstraints(nf)
      val isAnalyzedInBasic = reduced.basic.eqs.exists { case (Var(v), t) => t match {
        case Var(_) => false
        case App(_, _) => v == b.name
      }
      }
      lazy val isAnalyzedInNested = reduced.nested.exists(n =>
        n.basic.eqs.exists { case (Var(v), t) => t match {
          case Var(_) => false
          case App(_, _) => v == b.name && !n.basic.reachableFrom(v).contains(v)
        }
        })
      val sort = ctx.sig.sort(b.sort)
      if (!isAnalyzedInBasic && !sort.isOpen && isAnalyzedInNested) {
        val instantiations = generatorInstantiations(newCtx, b)
        return Some(instantiations)
      }
      lazy val occursInNested = reduced.nested.exists(n =>
        n.basic.eqs.exists { case (Var(v), t) => v == b.name || (t match {
          case Var(w) => w == b.name
          case App(_, args) => args.contains(Var(b.name))
        })
        }
      )
      if (!isAnalyzedInBasic && sort.hasFinFinite && sort.hasFinInfinite && occursInNested) {
        val instantiations = finiteInstantiations(newCtx, b) ++ infiniteInstantiations(newCtx, b)
        return Some(instantiations.toSeq)
      }
      lazy val hasFiniteConstraint = reduced.basic.fins.contains(Var(b.name))
      if (!isAnalyzedInBasic && sort.hasFinFinite && hasFiniteConstraint && occursInNested) {
        val instantiations = finiteInstantiations(newCtx, b)
        return Some(instantiations.toSeq)
      }
      lazy val hasInfiniteConstraint = reduced.nested.exists(n =>
        n.basic.eqs.isEmpty && n.basic.fins.contains(Var(b.name)))
      if (!isAnalyzedInBasic && sort.hasFinInfinite && hasInfiniteConstraint && occursInNested) {
        val instantiations = infiniteInstantiations(newCtx, b)
        return Some((Seq.empty, Var(b.name).fin()) +: instantiations.toSeq)
      }
    }
    None
  }

  /** Returns all the instantiations of the given variable with the finitely many generators. */
  private def generatorInstantiations(ctx: Context, b: Binding): Seq[(Seq[Binding], BasicFormula)] = {
    val instantiations = ctx.sig.sort(b.sort).generators.map(con => {
      val curCtx = ctx.copy()
      val argBindings = con.paramSorts.zipWithIndex.map {
        case (s, i) => curCtx.addFreshVar(s, s"${b.name}_${con.name}_$i")
      }
      val additionalEq = (Var(b.name), App(con.name, argBindings.map(b => Var(b.name))))
      (argBindings, BasicFormula(Set(additionalEq), Set.empty))
    })
    instantiations
  }

  /** Returns all the instantiations of the given variable with finitely many finite values. */
  private def finiteInstantiations(ctx: Context, b: Binding): Set[(Seq[Binding], BasicFormula)] = {
    val instantiations = ctx.sig.sort(b.sort).finiteInhabitants.map(term => {
      val curCtx = ctx.copy()
      val (bindings, eqs) = Equation(Var(b.name), term).normalizeHelp(curCtx)
      (bindings, BasicFormula(eqs.toSet, Set.empty))
    })
    instantiations
  }

  /** Returns all the instantiations of the given variable with infinitely many infinite values. */
  private def infiniteInstantiations(ctx: Context, b: Binding): Set[(Seq[Binding], BasicFormula)] = {
    val instantiations = ctx.sig.sort(b.sort).infiniteInhabitants.map(term => {
      val curCtx = ctx.copy()
      val dummyVarName = "" // necessary for proper renaming
      val (termBindings, termEqs) = Equation(dummyVarName, term).normalizeHelp(curCtx)
      val vars = term.vars
      val uniqueSortsOccurring = ctx.sig.sorts.values.filter(s => vars.contains(s.uniqueVarName))
      val uniqueAssignments = mutable.Set.from(uniqueSortsOccurring.map(s => {
        val (v, t) = s.uniqueInfiniteInhabitant.get
        (Binding(v, s.name), t)
      }))
      var sizeBefore = uniqueAssignments.size
      var sizeAfter = uniqueAssignments.size
      do {
        sizeBefore = uniqueAssignments.size
        for ((_, App(c, _)) <- uniqueAssignments) {
          ctx.sig.generator(c).paramSorts.foreach {
            s =>
              val (v, t) = ctx.sig.sort(s).uniqueInfiniteInhabitant.get
              uniqueAssignments.addOne((Binding(v, s), t))
          }
        }
        sizeAfter = uniqueAssignments.size
      } while (sizeAfter > sizeBefore)
      val uniqueRenaming = uniqueAssignments.map {
        case (b, _) => (b.name, curCtx.addFreshVar(b.sort, b.name).name)
      }.toMap
      val renaming = uniqueRenaming + (dummyVarName -> b.name)
      val uniqueBindings = uniqueAssignments.map { case (b, _) => b }.toSeq.sortBy(_.name)
      val uniqueEqs = uniqueAssignments.map { case (b, t) => (Var(b.name), t) }.toSet
      val bindings = termBindings ++ uniqueBindings.map(b => b.copy(name = renaming.getOrElse(b.name, b.name)))
      val eqs = (termEqs.toSet ++ uniqueEqs).map {
        case (Var(v), t) => (Var(renaming.getOrElse(v, v)), t.rename(renaming))
      }
      (bindings, BasicFormula(eqs, Set.empty))
    })
    instantiations
  }
}

/** Signals that the computation was aborted (usually by timeout). */
object ComputationStoppedException extends Exception
