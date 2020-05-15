import scala.collection.mutable
import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers

case class TreeInstance(sorts: Seq[SortDecl], free: Seq[Binding], formula: Formula)

case class SortDecl(sort: String, generators: Seq[GeneratorDecl], isOpen: Boolean)

case class GeneratorDecl(name: String, paramSorts: Seq[String])

object Parser {
  /** Parses a tree instance to be solved. */
  def parseTreeInstance(input: String): TreeInstance = {
    val parser = new FileParser()
    val result = parser.parseAll(parser.treeInstance, input)
    if (result.isEmpty) {
      throw new InvalidInputException(result.toString)
    }
    result.get
  }

  /** Parses a datatype instance to be solved. */
  def parseDatatypeInstance(input: String): DatatypeInstance = {
    val parser = new FileParser()
    val result = parser.parseAll(parser.datatypeInstance, input)
    if (result.isEmpty) {
      throw new InvalidInputException(result.toString)
    }
    result.get
  }
}

class FileParser extends RegexParsers {
  override protected val whiteSpace: Regex = """(\s+|#[^\n]*)+""".r
  val functionSymbols: mutable.Set[String] = mutable.Set.empty

  def datatypeInstance: Parser[DatatypeInstance] =
    datatypeDecl.* ~ ("free" ~> rep1sep(binding, ",")).? ~ ("solve" ~> formula) ^^ {
      case decls ~ free ~ f => DatatypeInstance(decls, free.getOrElse(Seq.empty), f)
    }

  def datatypeDecl: Parser[DatatypeDecl] =
    ("data" | "codata") ~ (symbol <~ "=") ~ repsep(conDecl, "," | "|") ^^ {
      case data ~ sort ~ cons => DatatypeDecl(sort, cons, data == "codata")
    }

  def conDecl: Parser[ConDecl] =
    symbol ~ ("(" ~> repsep(conArg, ",") <~ ")").? ^^ { case con ~ args =>
      functionSymbols += con
      ConDecl(con, args.getOrElse(Seq.empty))
    }

  def conArg: Parser[(String, String)] = symbol ~ (":" ~> symbol).? ^^ { case s1 ~ s2 => s2 match {
    case None => ("", s1)
    case Some(sort) =>
      functionSymbols += s1
      (s1, sort)
  }
  }

  def treeInstance: Parser[TreeInstance] =
    sortDecl.* ~ ("free" ~> rep1sep(binding, ",")).? ~ ("solve" ~> formula) ^^ {
      case decls ~ free ~ f => TreeInstance(decls, free.getOrElse(Seq.empty), f)
    }

  def sortDecl: Parser[SortDecl] =
    ("open".? <~ "sort") ~ (symbol <~ "=") ~ rep1sep(genDecl, "," | "|") ^^ {
      case open ~ sort ~ gens => SortDecl(sort, gens, open.nonEmpty)
    }

  def genDecl: Parser[GeneratorDecl] =
    symbol ~ ("(" ~> repsep(symbol, ",") <~ ")").? ^^ {
      case gen ~ args =>
        functionSymbols += gen
        GeneratorDecl(gen, args.getOrElse(Seq.empty))
    }

  def symbol: Parser[String] = """[-a-zA-Z0-9$]+""".r

  def term: Parser[Term] =
    symbol ~ ("(" ~> repsep(term, ",") <~ ")").? ^^ { case s ~ ts =>
      ts match {
        case Some(ts) => Term.App(s, ts)
        case None => if (functionSymbols.contains(s)) {
          Term.App(s, Seq.empty)
        } else {
          Var(s)
        }
      }
    }

  def atomicFormula: Parser[Formula] =
    "true" ^^^ Conjunction(Seq.empty) |
      "false" ^^^ Disjunction(Seq.empty) |
      "fin" ~> "(" ~> term <~ ")" ^^ { t => Finite(t) } |
      term ~ ("=" ~> term) ^^ { case s ~ t => Equation(s, t) } |
      "(" ~> formula <~ ")"

  def negatedFormula: Parser[Formula] = ("!" | "¬") ~> atomicFormula ^^ Not | atomicFormula

  def conjunction: Parser[Formula] =
    rep1sep(negatedFormula, "&" | "∧") ^^ { cs => if (cs.size == 1) cs.head else Conjunction(cs) }

  def disjunction: Parser[Formula] =
    rep1sep(conjunction, "|" | "∨") ^^ { ds => if (ds.size == 1) ds.head else Disjunction(ds) }

  def quantifier: Parser[Formula] =
    ("exists" | "∃") ~> repsep(binding, ",") ~ ("." ~> disjunction) ^^ { case b ~ f => Exists(b, f) } |
      ("forall" | "∀") ~> repsep(binding, ",") ~ ("." ~> conjunction) ^^ { case b ~ f => Forall(b, f) } |
      disjunction

  def binding: Parser[Binding] = symbol ~ (":" ~> symbol) ^^ { case v ~ s => Binding(v, s) }

  def formula: Parser[Formula] = quantifier
}
