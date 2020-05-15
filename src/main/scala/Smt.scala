import scala.util.parsing.combinator._

/** Represents an s-expression. */
sealed trait SExp

/** A symbol s-expression. */
case class Symbol(sym: String) extends SExp {
  override def toString: String = sym
}

/** An s-expression list. */
case class SExps(elems: Seq[SExp]) extends SExp {
  override def toString: String = elems.map(_.toString).mkString("(", " ", ")")
}

/** Represents a QF_DT instance from the SMT-LIB. */
case class Smt(inst: DatatypeInstance, isSat: Boolean)

object Smt {
  /** Limited parser for the SMT-LIB format. It can only parse what's necessary for QF_DT tests. */
  def parse(input: String): Smt = {
    var isSat = false
    var assertion: Formula = Formula.True
    var vars = Seq.empty[Binding]
    var decls = Seq.empty[DatatypeDecl]
    val commands = SmtParser.parse(SmtParser.commands, input).get
    for (SExps(cmd) <- commands) {
      val cmdName = cmd.head match {
        case Symbol(c) => c
        case _ => throw new InvalidInputException(s"Invalid command `$cmd` in SMT input.")
      }
      cmdName match {
        case "set-info" =>
          if (cmd(1) == Symbol(":status")) {
            cmd(2) match {
              case Symbol("sat") => isSat = true
              case Symbol("unsat") => isSat = false
              case s => throw new InvalidInputException(
                s"Invalid status `$s` in the SMT input (should be `sat` or `unsat`).")
            }
          }
        case "set-logic" => // ignore
        case "declare-fun" =>
          val Symbol(name) = cmd(1)
          assert(cmd(2) == SExps(Seq.empty))
          val Symbol(sort) = cmd(3)
          vars = vars :+ Binding(name, sort)
        case "declare-datatypes" =>
          decls = decls ++ parseDatatypeDecls(cmd.slice(1, cmd.size))
        case "assert" => assertion = sexpToFormula(cmd(1), vars, decls)
        case "check-sat" => // ignore
        case "exit" => // ignore
        case _ => throw new InvalidInputException(s"Unknown command `$cmd` in SMT input.")
      }
    }
    Smt(DatatypeInstance(decls, vars, assertion), isSat)
  }

  /** Parse an SMT datatype declaration */
  def parseDatatypeDecls(sexps: Seq[SExp]): Seq[DatatypeDecl] = {
    val (sorts, cons) = sexps match {
      case Seq(SExps(sorts), SExps(decls)) => (sorts, decls)
    }
    assert(sorts.size == cons.size)
    sorts.zip(cons).map { case (SExps(Seq(Symbol(sort), Symbol("0"))), SExps(cons)) =>
      val constructors = cons.map { case SExps(Symbol(conName) +: conArgs) =>
        ConDecl(conName, conArgs.map { case SExps(Seq(Symbol(argName), Symbol(argSort))) =>
          (argName, argSort)
        })
      }
      DatatypeDecl(sort, constructors)
    }
  }

  /** Convert an SMT s-expression to a formula. */
  def sexpToFormula(exp: SExp, vars: Seq[Binding], decls: Seq[DatatypeDecl]): Formula = {
    exp match {
      case SExps(Symbol(op) +: args) => op match {
        case "or" => args.map(sexpToFormula(_, vars, decls)).fold(Formula.False)(_ | _)
        case "and" => args.map(sexpToFormula(_, vars, decls)).fold(Formula.True)(_ & _)
        case "not" => assert(args.size == 1); Not(sexpToFormula(args.head, vars, decls))
        case "=" => assert(args.size == 2); Equation(sexpToTerm(args.head, vars), sexpToTerm(args(1), vars))
        case _ => throw new InvalidInputException(s"Unknown `$op` in `$exp` in SMT input.")
      }
      case SExps(Seq(SExps(Seq(Symbol("_"), Symbol("is"), Symbol(con))), term)) =>
        val conDecl = decls.flatMap(decl => decl.cons.find(_.name == con)).head
        Exists(conDecl.params.map { case (p, s) => Binding(p, s) },
          Equation(sexpToTerm(term, vars), Term.App(con, conDecl.params.map { case (p, _) => Var(p) })))
      case _ => throw new InvalidInputException(s"Unknown formula expression `$exp` in SMT input.")
    }
  }

  /** Convert an SMT s-expression to a term. */
  def sexpToTerm(exp: SExp, vars: Seq[Binding]): Term = {
    exp match {
      case Symbol(name) => if (vars.exists(p => p.name == name)) {
        Var(name)
      } else {
        Term.App(name, Seq.empty)
      }
      case SExps(Symbol(first) +: args) =>
        if (first == "ite") {
          val Seq(_, _, _) = args
          throw new InvalidInputException("The operation `ite` is not supported for SMT inputs.")
        } else {
          Term.App(first, args.map(sexpToTerm(_, vars)))
        }
      case _ => throw new InvalidInputException(s"Unknown term expression `$exp` in SMT input.")
    }
  }

  /** Convert a formula back to an SMT s-expression. */
  def formulaToSExp(f: Formula): SExp = f match {
    case Equation(s, t) => SExps(Seq(Symbol("="), termToSExp(s), termToSExp(t)))
    case Finite(_) => Symbol("true")
    case Not(f) => SExps(Seq(Symbol("not"), formulaToSExp(f)))
    case Conjunction(cs) => cs.foldRight(Symbol("true"): SExp) { case (a, b) =>
      SExps(Seq(Symbol("and"), formulaToSExp(a), b))
    }
    case Disjunction(ds) => ds.foldRight(Symbol("false"): SExp) { case (a, b) =>
      SExps(Seq(Symbol("or"), formulaToSExp(a), b))
    }
    case Exists(bound, f) => if (bound.isEmpty)
      formulaToSExp(f)
    else
      SExps(Seq(
        Symbol("exists"),
        SExps(bound.map(b => SExps(Seq(Symbol(b.name), Symbol(b.sort))))),
        formulaToSExp(f)))
    case Forall(bound, f) => if (bound.isEmpty)
      formulaToSExp(f)
    else
      SExps(Seq(
        Symbol("forall"),
        SExps(bound.map(b => SExps(Seq(Symbol(b.name), Symbol(b.sort))))),
        formulaToSExp(f)))
  }

  /** Convert a term back to an SMT s-expression. */
  def termToSExp(t: Term): SExp = t match {
    case Var(v) => Symbol(v)
    case Term.App(label, terms) => if (terms.isEmpty)
      Symbol(label)
    else
      SExps(Symbol(label) +: terms.map(termToSExp))
  }
}

object SmtParser extends RegexParsers {
  def symbol: Parser[SExp] = """[-a-zA-Z0-9_=>:.]+|\|[^|]*\||"[^"]*"""".r ^^ Symbol

  def sexps: Parser[SExp] = "(" ~> sexp.* <~ ")" ^^ SExps

  def sexp: Parser[SExp] = symbol | sexps

  def commands: Parser[Seq[SExp]] = sexp.*
}
