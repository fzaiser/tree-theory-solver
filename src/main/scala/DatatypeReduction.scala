import scala.collection.mutable

/** A selector extracting argument number `index` from `constructor`. */
case class Selector(name: String, constructor: String, index: Int)

/** A (co-)datatype declaration. */
case class DatatypeDecl(sort: String, cons: Seq[ConDecl], isCodata: Boolean = false)

/** A constructor declaration, with parameters storing (selector name, sort of the parameter). */
case class ConDecl(name: String, params: Seq[(String, String)])

sealed trait SelectorSemantics

object StandardSemantics extends SelectorSemantics

object DefaultValueSemantics extends SelectorSemantics

/**
 * A formula in the theory of (co)datatypes.
 *
 * @param decls (co)datatype declarations
 * @param vars free variables and their sorts
 * @param assertion formula to be solved
 */
case class DatatypeInstance(decls: Seq[DatatypeDecl], vars: Seq[Binding], assertion: Formula) {
  /** Checks whether the given datatype instance is well-sorted and valid. */
  def checkSorted(semantics: SelectorSemantics): Unit = {
    // Check for mixing of dataypes and codatatypes:
    val finiteSorts = decls.filter(decl => !decl.isCodata).map(_.sort).toSet
    for (decl <- decls) {
      for (con <- decl.cons) {
        for ((_,paramSort) <- con.params) {
          val sortFinite = finiteSorts.contains(decl.sort)
          val paramSortFinite = finiteSorts.contains(paramSort)
          if (sortFinite && !paramSortFinite) {
            throw new InvalidInputException(
              s"Datatype `${decl.sort}` uses the codatatype `$paramSort` in the constructor `${con.name}`" +
                s" but mixing datatypes and codatatypes is not allowed.")
          }
          if (!sortFinite && paramSortFinite) {
            throw new InvalidInputException(
              s"Codatatype `${decl.sort}` uses the datatype `$paramSort` in the constructor `${con.name}`" +
                s" but mixing datatypes and codatatypes is not allowed.")
          }
        }
      }
    }
    // Check that the formula is well-sorted, taking selectors into account:
    val (sig, sels) = DatatypeReduction.analyzeDatatypeDecls(decls)
    // Add selectors as generators to be able to use the normal sort checking mechanism.
    val newGenerators = sig.generators.values ++ sels.map { case (_, sel) =>
      val constructor = sig.generators(sel.constructor)
      Generator(sel.name, Seq(constructor.resultSort), constructor.paramSorts(sel.index))
    }
    val newSig = new Signature(newGenerators.toSeq, Set.empty)
    assertion.check(Context(newSig, vars), semantics == DefaultValueSemantics)
  }
}

/** Reduction of a datatype formula to an equisatisfiable tree formula. */
object DatatypeReduction {

  /** Transforms a datatype instance to an equisatisfiable tree instance.
   *
   * The result is negated if negate is set to true.
   * */
  def reduce(instance: DatatypeInstance, semantics: SelectorSemantics, negate: Boolean): (Context, NormalFormula) = {
    val (ctx, f) = eliminateSelectors(instance, semantics)
    val nf = if (negate) f.negatedNormalize(ctx) else f.normalize(ctx)
    val finiteSorts = instance.decls.filter(decl => !decl.isCodata).map(_.sort).toSet
    val result = addFiniteConstraints(ctx, nf, finiteSorts)
    (ctx, result)
  }

  /** Eliminates the selectors of a datatype instance according to the specified semantics. */
  def eliminateSelectors(instance: DatatypeInstance, semantics: SelectorSemantics): (Context, Formula) = {
    val (sig, selectors) = analyzeDatatypeDecls(instance.decls)
    val ctx = Context(sig, instance.vars)
    val elimination = new DatatypeReduction(ctx, selectors)
    val transformed = semantics match {
      case StandardSemantics => elimination.eliminateStandardSelectors(instance.assertion)
      case DefaultValueSemantics => elimination.eliminateDefaultValueSelectors(instance.assertion)
    }
    (elimination.ctx, transformed)
  }

  /** Extracts the selectors from a datatype declaration. */
  def analyzeDatatypeDecls(decls: Seq[DatatypeDecl]): (Signature, Map[String, Selector]) = {
    val constructors = decls.flatMap(decl =>
      decl.cons.map(con => Generator(con.name, con.params.map(_._2), decl.sort)))
    val selectors = decls.flatMap(decl =>
      decl.cons.flatMap(con =>
        con.params.map(_._1).zipWithIndex.map { case (s, i) => (s, Selector(s, con.name, i)) }
      )).toMap
    (new Signature(constructors, Set.empty), selectors)
  }

  /** Adds finiteness constraints for datatypes to a normal formula. */
  def addFiniteConstraints(ctx: Context, nf: NormalFormula, datatypes: Set[String], includeFreeVars: Boolean = true):
  NormalFormula = {
    val vars = if (includeFreeVars) {
      nf.computeFree().map(v => ctx.binding(v)) ++ nf.existential
    } else {
      nf.existential
    }
    val finiteVars = vars.filter(b => datatypes.contains(b.sort))
    val newBasic = nf.basic.copy(fins = nf.basic.fins ++ finiteVars.map(b => Var(b.name)))
    nf.copy(
      basic = newBasic,
      nested = nf.nested.map(n =>
        addFiniteConstraints(ctx.withBindings(nf.existential), n, datatypes, includeFreeVars = false)))
  }
}

class DatatypeReduction(var ctx: Context, val selectors: Map[String, Selector]) {
  val selectorTerms: mutable.Map[String, mutable.Set[(Var, Term)]] =
    new mutable.HashMap()

  /** Eliminates selectors according to the standard semantics. */
  def eliminateStandardSelectors(f: Formula): Formula = {
    val f2 = collectSelectorTerms(f)
    val selectorVarConsistency = generateSelectorVarConstraints
    selectorVarConsistency & f2
  }

  /** For each "v = sel_C(t)", generate "¬(∃z. t = C(z...)) ∨ (∃z. t = C(..., v, ...))". */
  def generateSelectorVarConstraints: Formula = {
    Conjunction(selectorTerms.toSeq.flatMap { case (sel, substitutions) =>
      val subs = substitutions.toSeq
      val selector = selectors(sel)
      val functionalConsistency = subs.zipWithIndex.flatMap {
        case ((v1, t1), i) => subs.slice(i + 1, subs.size).map { case (v2, t2) => !Equation(t1, t2) | Equation(v1, v2) }
      }
      val con = ctx.sig.generator(selectors(sel).constructor)
      val dummies = con.paramSorts.map(s => ctx.addFreshVar(s))
      val selectorProperty = subs.map { case (v, t) => !Exists(
        dummies,
        Equation(t, Term.App(con.name, dummies.map(b => Var(b.name))))
      ) | Exists(
        dummies.zipWithIndex.filterNot { case (_, i) => i == selector.index }.map { case (d, _) => d },
        Equation(t, Term.App(con.name,
          dummies.zipWithIndex.map { case (d, i) => if (selector.index == i) v else Var(d.name) }))
      )
      }
      ctx = ctx.without(dummies.map(_.name): _*)
      functionalConsistency ++ selectorProperty
    })
  }

  /** Collects all selector terms into this.selectorTerms. */
  def collectSelectorTerms(f: Formula): Formula = f match {
    case Equation(s, t) => Equation(collectSelectorTerms(s), collectSelectorTerms(t))
    case Not(f) => Not(collectSelectorTerms(f))
    case Finite(t) => Finite(collectSelectorTerms(t))
    case Conjunction(cs) => Conjunction(cs.map(collectSelectorTerms))
    case Disjunction(cs) => Disjunction(cs.map(collectSelectorTerms))
    case Exists(bound, f) => Exists(bound, collectSelectorTerms(f))
    case Forall(bound, f) => Forall(bound, collectSelectorTerms(f))
  }

  def collectSelectorTerms(t: Term): Term = {
    t match {
      case Var(v) => Var(v)
      case Term.App(label, terms) =>
        val newTerms = terms.map(collectSelectorTerms)
        if (selectors.contains(label)) {
          assert(newTerms.size == 1)
          val scrutinee = newTerms.head
          val sel = selectors(label)
          val sort = ctx.sig.generator(sel.constructor).paramSorts(sel.index)
          val v = ctx.addFreshVar(sort, s"_${sel.name}")
          if (!selectorTerms.contains(sel.name)) {
            selectorTerms(sel.name) = mutable.Set.empty
          }
          selectorTerms(sel.name) += ((Var(v.name), scrutinee))
          Var(v.name)
        } else {
          Term.App(label, newTerms)
        }
    }
  }

  val selectedSorts = mutable.Set.empty[String]

  /** Eliminates selectors according to the semantics with default values. */
  def eliminateDefaultValueSelectors(f: Formula): Formula = {
    val f2 = eliminateDefaultValueSelectors(ctx.copy(), f)
    val defaultBindings = selectedSorts.map(s => Binding(defaultVarName(s), s))
    ctx = ctx.withBindings(defaultBindings.toSeq.sortBy(_.name))
    f2
  }

  private def defaultVarName(sort: String): String = s"default_$sort"

  def eliminateDefaultValueSelectors(ctx: Context, f: Formula): Formula = {
    f match {
      case Equation(s, t) =>
        val oldCtx = this.ctx
        this.ctx = ctx
        this.selectorTerms.clear()
        val s2 = collectSelectorTerms(s)
        val t2 = collectSelectorTerms(t)
        val (selectorVarBindings, selectorConstraints) = generateDefaultValueSelectorConstraints
        val result = Conjunction(Equation(s2, t2) +: selectorConstraints)
        this.ctx = oldCtx
        if (selectorVarBindings.isEmpty) {
          result
        } else {
          Exists(selectorVarBindings, result)
        }
      case Finite(t) =>
        val oldCtx = this.ctx
        this.ctx = ctx
        this.selectorTerms.clear()
        val t2 = collectSelectorTerms(t)
        val (selectorVarBindings, selectorConstraints) = generateDefaultValueSelectorConstraints
        val result = Conjunction(Finite(t2) +: selectorConstraints)
        this.ctx = oldCtx
        if (selectorVarBindings.isEmpty) {
          result
        } else {
          Exists(selectorVarBindings, result)
        }
      case Not(f) => Not(eliminateDefaultValueSelectors(ctx, f))
      case Conjunction(cs) => Conjunction(cs.map(c => eliminateDefaultValueSelectors(ctx, c)))
      case Disjunction(ds) => Disjunction(ds.map(d => eliminateDefaultValueSelectors(ctx, d)))
      case Exists(bound, f) => Exists(bound, eliminateDefaultValueSelectors(ctx.withBindings(bound), f))
      case Forall(bound, f) => Forall(bound, eliminateDefaultValueSelectors(ctx.withBindings(bound), f))
    }
  }

  /** For each "v = sel_C(t)", generate "(∃z. t = C(...,v,...)) ∨ (¬(∃z. t = C(z)) ∧ v = default-value)". */
  private def generateDefaultValueSelectorConstraints: (Seq[Binding], Seq[Formula]) = {
    val selectorVarBindings = selectorTerms.toSeq.flatMap { case (sel, subs) =>
      val selector = selectors(sel)
      val con = ctx.sig.generator(selector.constructor)
      subs.map { case (v, _) => Binding(v.name, con.paramSorts(selector.index)) }
    }
    val selectorConstraints = selectorTerms.toSeq.sortBy(_._1).flatMap { case (sel, subs) =>
      subs.toSeq.sortBy(_._1.name).map { case (v, t) => eliminateDefaultValueSelectorInstance(v, sel, t)
      }
    }
    (selectorVarBindings, selectorConstraints)
  }

  def eliminateDefaultValueSelectorInstance(helperVar: Var, sel: String, argument: Term): Formula = {
    val selector = selectors(sel)
    val con = ctx.sig.generator(selector.constructor)
    val dummies = con.paramSorts.map(s => ctx.addFreshVar(s))
    val selectorResultSort = con.paramSorts(selector.index)
    selectedSorts.add(selectorResultSort)
    val result = Exists(dummies,
      Equation(argument, Term.App(con.name, dummies.map(b => Var(b.name))))
        & Equation(helperVar, Var(dummies(selector.index).name))
    ) | (!Exists(dummies, Equation(argument, Term.App(con.name, dummies.map(b => Var(b.name)))))
      & Equation(helperVar, Var(defaultVarName(selectorResultSort)))
      )
    ctx = ctx.without(dummies.map(_.name): _*)
    result
  }
}
