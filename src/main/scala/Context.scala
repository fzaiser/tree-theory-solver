import scala.language.implicitConversions

/** A binding consists of a variable name and its sort. */
case class Binding(name: String, sort: String) {
  override def toString: String = s"$name: $sort"
}

object Binding {
  /** A convenience function allowing bindings to be written as "name -> sort". */
  implicit def pair2Bind(p: (String, String)): Binding = Binding(p._1, p._2)
}

/** Stores a (tree) signature and variable bindings. */
case class Context(sig: Signature, var bindings: Seq[Binding]) {

  /** Finds the index of a variable. Returns the last binding if there's more than one. */
  def indexOf(name: String): Int = bindings.lastIndexWhere(_.name == name)

  /** Finds the variable name corresponding to an index. */
  def nameOf(index: Int): String = bindings(bindings.size - index - 1).name

  /** Returns the binding of a variable. */
  def binding(name: String): Binding = {
    val idx = indexOf(name)
    if(idx < 0) {
      throw new InvalidInputException(s"Variable '$name' not found in the context.")
    }
    bindings(idx)
  }

  /** Returns the sort of a variable. */
  def sortOf(name: String): String = binding(name).sort

  /** Creates a copy of the context with the additional bindings. */
  def withBindings(vs: Seq[Binding]): Context = Context(sig, bindings ++ vs)

  /** Creates a copy of the context without the given variables. */
  def without(vs: String*): Context = {
    val excluded = vs.toSet
    Context(sig, bindings.filterNot(b => excluded.contains(b.name)))
  }

  /** Creates a copy of the context containing only the given variables. */
  def keepOnly(vs: String*): Context = {
    val included = vs.toSet
    Context(sig, bindings.filter(b => included.contains(b.name)))
  }

  /** Checks whether the given variable name is bound in this context. */
  def contains(name: String): Boolean = bindings.exists(_.name == name)

  /** Adds a fresh variable name starting with the given prefix. */
  def addFreshVar(sort: String, prefix: String = ""): Binding = {
    val v = freshName(prefix)
    bindings = bindings :+ (v -> sort)
    Binding(v, sort)
  }

  private def freshName(prefix: String = ""): String = {
    var i = 0
    if (prefix.nonEmpty && !bindings.exists(_.name == prefix)) {
      return prefix
    }
    while (true) {
      if (!bindings.exists(_.name == s"${prefix}_$i")) {
        return s"${prefix}_$i"
      }
      i += 1
    }
    throw new RuntimeException("unreachable")
  }

}
