import scala.collection.mutable

class Sort(val name: String) {
  /** Whether the sort is assumed to have infinitely many: generators, finite inhabitants and infinite inhabitants. */
  var isOpen: Boolean = false
  var allFinite: Boolean = false
  var allInfinite: Boolean = true
  /** Whether the sort has a unique infinite inhabitant. */
  var hasUniqueInfinite: Boolean = false
  /** Describes the unique infinite individual of this sort, if it `hasUniqueInfinite`.
   *
   * u_sort = f(u_sort2) would be stored as Some("u_sort", App("f", Seq(Var("u_sort2")))).
   * */
  var uniqueInfiniteInhabitant: Option[(String, App)] = None
  /** Whether the sort has finitely many finite inhabitants. */
  var hasFinFinite: Boolean = false
  /** The set of finite individuals of this sort or empty if `!hasFinFinite`. */
  var finiteInhabitants: Set[Term] = Set.empty
  /** Whether the sort has finitely many infinite inhabitants. */
  var hasFinInfinite: Boolean = false
  /** The set of infinite individuals or empty if `!hasFinInfinite`.
   * They may contain the variable names of the unique infinite individuals. */
  var infiniteInhabitants: Set[Term] = Set.empty
  var generators: Seq[Generator] = Seq.empty

  /** The variable name for the unique infinite individual of this sort (if it exists). */
  def uniqueVarName: String = "u_" + name
}

/** A generator of `resultSort`, given by its `name`, the sorts of its `parameterSorts`.  */
case class Generator(name: String, paramSorts: Seq[String], resultSort: String)

/** Stores a signature, meaning all sorts and their generators/constructors. */
class Signature(gens: Seq[Generator], openSorts: Set[String]) {
  val sorts: Map[String, Sort] = Signature.computeSorts(gens, openSorts)
  val generators: Map[String, Generator] = gens.map(c => (c.name, c)).toMap

  /** Looks up a sort in the signature or throws an error if it doesn't exist. */
  def sort(name: String): Sort = {
    if (!sorts.contains(name)) {
      throw new InvalidInputException(s"Sort `$name` not found.")
    }
    sorts(name)
  }

  /** Looks up a generator in the signature or throws an error if it doesn't exist. */
  def generator(name: String): Generator = {
    if (!generators.contains(name)) {
      throw new InvalidInputException(s"Generator `$name` not found.")
    }
    generators(name)
  }
}

object Signature {
  /** Given a list of constructors and a set of sorts that are to be considered open, construct a signature.
   *
   * Open sorts are assumed to have infinitely many generators, finite inhabitants, and infinite inhabitants.
   *
   * This computes the relevant properties of the sorts, like finiteness.
   * */
  def computeSorts(gens: Seq[Generator], openSorts: Set[String]): Map[String, Sort] = {
    val sorts = mutable.Map.empty[String, Sort]
    // Collect all generators:
    for (gen <- gens) {
      val s = gen.resultSort
      if (!sorts.contains(s)) {
        sorts(s) = new Sort(s)
        sorts(s).hasUniqueInfinite = true
      }
      sorts(s).generators = sorts(s).generators :+ gen
    }
    // Process open sorts (sorts assumed to have infinitely many generators, finite, and infinite inhabitants):
    for (s <- openSorts) {
      if (!sorts.contains(s)) {
        sorts(s) = new Sort(s)
      }
      sorts(s).isOpen = true
      sorts(s).hasUniqueInfinite = false
      sorts(s).allFinite = false
      sorts(s).allInfinite = false
    }
    // Check for invalid sorts:
    for ((_, sort) <- sorts) {
      if (!sort.isOpen && sort.generators.size < 2) {
        throw new InvalidInputException(s"Sort `${sort.name}` has fewer than 2 generators, which is disallowed.")
      }
      for (gen <- sort.generators) {
        gen.paramSorts.foreach(paramSort => if (!sorts.contains(paramSort)) {
          throw new InvalidInputException(
            s"Sort `$paramSort` (parameter of generator `${gen.name}` in `${sort.name}`) not found.")
        })
      }
    }
    // Fixed point iteration for `allFinite` and `allInfinite`:
    var changeMade = false
    do {
      changeMade = false
      for ((_, sort) <- sorts) {
        if (!sort.isOpen) {
          if (!sort.allFinite && sort.generators.forall(c => c.paramSorts.forall(s => sorts(s).allFinite))) {
            sort.allFinite = true
            changeMade = true
          }
          if (sort.allInfinite && sort.generators.exists(c => c.paramSorts.forall(s => !sorts(s).allInfinite))) {
            sort.allInfinite = false
            changeMade = true
          }
        }
      }
    } while (changeMade)
    // Fixed point iteration for `hasFinite`, `finiteInhabitants`, `hasUniqueInfinite` and `uniqueInfiniteInhabitant`:
    do {
      changeMade = false
      for ((_, sort) <- sorts) {
        if (!sort.isOpen) {
          if (!sort.hasFinFinite &&
            sort.generators.forall(c =>
              c.paramSorts.exists(s => sorts(s).allInfinite) || c.paramSorts.forall(s => sorts(s).hasFinFinite))) {
            sort.hasFinFinite = true
            sort.finiteInhabitants = sort.generators
              .flatMap(g => allCombinations(g.paramSorts.map(s => sorts(s).finiteInhabitants))
                .map(args => Term.App(g.name, args)))
              .toSet
            changeMade = true
          }
          val uniqueInfiniteGenerator = sort.generators.find(c =>
            c.paramSorts.size == 1 && sorts(c.paramSorts.head).hasUniqueInfinite &&
              sort.generators.forall(d => c == d || d.paramSorts.forall(s => sorts(s).allFinite)))
          uniqueInfiniteGenerator match {
            case Some(u) =>
              val argSort = sorts(u.paramSorts.head)
              sort.uniqueInfiniteInhabitant = Some((sort.uniqueVarName, App(u.name, Seq(argSort.uniqueVarName))))
            case None => if (sort.hasUniqueInfinite) {
              sort.hasUniqueInfinite = false
              changeMade = true
            }
          }
        }
      }
    } while (changeMade)

    // Compute `hasFinInfinite` and `infiniteInhabitants`.
    // Initialization:
    for ((_, sort) <- sorts) {
      if (sort.allFinite) {
        sort.hasFinInfinite = true
        sort.infiniteInhabitants = Set.empty
      }
      if (sort.hasUniqueInfinite) {
        sort.hasFinInfinite = true
        sort.infiniteInhabitants = Set(Var(sort.uniqueVarName))
      }
    }
    // Fixed point iteration:
    do {
      changeMade = false
      for ((_, sort) <- sorts) {
        if (!sort.isOpen) {
          if (!sort.hasFinInfinite && sort.generators
            .forall(g => g.paramSorts.zipWithIndex.forall { case (si, i) =>
              sorts(si).allFinite || (sorts(si).hasFinInfinite &&
                g.paramSorts.zipWithIndex.forall { case (sj, j) =>
                  j == i || (sorts(sj).hasFinFinite && sorts(sj).hasFinInfinite)
                })
            })) {
            sort.hasFinInfinite = true
            changeMade = true
            sort.infiniteInhabitants = sort.generators.flatMap(g =>
              g.paramSorts.zipWithIndex.flatMap { case (si, i) =>
                if (!sorts(si).hasFinInfinite)
                  Set.empty
                else {
                  val argSets = g.paramSorts.zipWithIndex.map { case (sj, j) =>
                    if (i == j)
                      sorts(si).infiniteInhabitants
                    else
                      sorts(sj).finiteInhabitants ++ sorts(sj).infiniteInhabitants
                  }
                  allCombinations(argSets).map(args => Term.App(g.name, args))
                }
              }
            ).toSet
          }
        }
      }
    } while (changeMade)
    sorts.toMap
  }

  /** allCombinations([s_1,...,s_n]) = { [e_1,...,e_n] | e_i ∈ s_i }. */
  def allCombinations[T](in: Seq[Set[T]]): Set[Seq[T]] = {
    in match {
      case h +: t => h.flatMap(x => allCombinations(t).map(y => x +: y))
      case _ => Set(Seq.empty)
    }
  }
}
