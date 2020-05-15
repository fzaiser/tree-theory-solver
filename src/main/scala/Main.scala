import java.io.{FileOutputStream, IOException, PrintStream}
import java.nio.file.{Files, Paths}

object Main {
  def main(args: Array[String]): Unit = {
    var benchmarkPath = ""
    var treeInstancePath = ""
    var datatypeInstancePath = ""
    var smtInstancePath = ""
    var timeout = 50
    var output = System.out
    var semantics: SelectorSemantics = StandardSemantics
    val argsIter = args.toSeq.iterator
    if (args.isEmpty || args.contains("help") || args.contains("--help")) {
      println(
        """Usage: <command> <file> <options>
          |
          |Commands:
          | * benchmark <path to the QF_DT directory> [--output <output file path>] [--timeout <milliseconds>]
          | * smt <path to SMT file>
          | * datatypes <path to datatypes file>
          | * trees <path to trees file>
          |
          |Options:
          | --selector-semantics (standard|default-values)
          | """.stripMargin)
    }
    while (argsIter.hasNext) {
      val next = argsIter.next()
      next match {
        case "datatypes" => datatypeInstancePath = argsIter.nextOption().getOrElse {
          System.err.println("missing argument after datatypes")
          return
        }
        case "trees" => treeInstancePath = argsIter.nextOption().getOrElse {
          System.err.println("missing argument after trees")
          return
        }
        case "smt" => smtInstancePath = argsIter.nextOption().getOrElse {
          System.err.println("missing argument after smt")
          return
        }
        case "benchmark" => benchmarkPath = argsIter.nextOption().getOrElse {
          System.err.println("missing argument after benchmark")
          return
        }
        case "--timeout" => argsIter.nextOption() match {
          case Some(t) => timeout = t.toInt
          case None =>
            System.err.println("missing argument after --timeout")
            return
        }
        case "--selector-semantics" => argsIter.nextOption() match {
          case Some("standard") =>
          case Some("default-values") => semantics = DefaultValueSemantics
          case _ =>
            System.err.println("missing or invalid argument after --selector-semantics")
            return
        }
        case "--output" => argsIter.nextOption() match {
          case None =>
            System.err.println("missing argument after --output")
            return
          case Some(file) => output = new PrintStream(new FileOutputStream(file, false))
        }
        case _ =>
          System.err.println("invalid argument: " + next)
          return
      }
    }
    try {
      if (treeInstancePath.nonEmpty) {
        processTreeFile(treeInstancePath)
      } else if (datatypeInstancePath.nonEmpty) {
        processDatatypeFile(datatypeInstancePath, semantics)
      } else if (smtInstancePath.nonEmpty) {
        processSmtFile(smtInstancePath, semantics)
      } else if (benchmarkPath.nonEmpty) {
        SmtLibTest.runBenchmark(benchmarkPath, timeout, output, semantics)
      }
    } catch {
      case e: InvalidInputException =>
        System.err.println(s"\nINVALID INPUT: ${e.getMessage}\n")
        System.exit(1)
      case e: IOException =>
        System.err.println(s"Error reading file: ${e.getMessage}\n")
        e.printStackTrace()
        System.exit(1)
    }
  }

  /** Solves and prints the solution of a given tree instance. */
  def processTreeFile(path: String): Unit = {
    val content = readFile(path)
    val treeInstance = try {
      Parser.parseTreeInstance(content)
    } catch {
      case ex: Exception =>
        System.err.println(s"Error parsing $path: ${ex.getMessage}")
        return
    }
    val generators = treeInstance.sorts.flatMap { s =>
      s.generators.map(g => Generator(g.name, g.paramSorts, s.sort))
    }
    val openSorts = treeInstance.sorts.filter(_.isOpen).map(_.sort)
    val signature = new Signature(generators, openSorts.toSet)
    val ctx = Context(signature, treeInstance.free)
    println("PARSED FORMULA: " + treeInstance.formula)
    treeInstance.formula.check(ctx)
    val nf = treeInstance.formula.negatedNormalize(ctx)
    processNegatedTreeFormula(ctx, nf)
  }

  /** Solves and prints the solution of a given datatype instance. */
  def processDatatypeFile(path: String, semantics: SelectorSemantics): Unit = {
    val content = readFile(path)
    val instance: DatatypeInstance = try {
      Parser.parseDatatypeInstance(content)
    } catch {
      case ex: Exception =>
        System.err.println(s"Error parsing $path: ${ex.getMessage}")
        return
    }
    println("PARSED FORMULA: " + instance.assertion)
    instance.checkSorted(semantics)
    val (ctx, nf) = DatatypeReduction.reduce(instance, semantics, negate = true)
    processNegatedTreeFormula(ctx, nf)
  }

  /** Solves and prints the solution of a given SMT instance. */
  def processSmtFile(path: String, semantics: SelectorSemantics): Unit = {
    val content = readFile(path)
    val instance: Smt = try {
      Smt.parse(content)
    } catch {
      case ex: Exception =>
        System.err.println(s"Error parsing $path: ${ex.getMessage}")
        return
    }
    println("PARSED FORMULA: " + instance.inst.assertion)
    instance.inst.checkSorted(semantics)
    val (ctx, nf) = DatatypeReduction.reduce(instance.inst, semantics, negate = true)
    processNegatedTreeFormula(ctx, nf)
  }

  /** Solves and prints the (negated) solution of the given formula. */
  def processNegatedTreeFormula(ctx: Context, nf: NormalFormula): Unit = {
    println("\nNORMAL FORMULA TO SOLVE (NEGATED):\n   " + nf)
    val solved = Solver.solveNf(ctx, nf)
    val result = if (solved.isEmpty) {
      "false"
    } else if (solved.exists(n => n.nested.isEmpty && n.basic.eqs.isEmpty && n.basic.fins.isEmpty)) {
      "true"
    } else {
      "   " + solved.map { n =>
        val existential = if (n.existential.isEmpty) "" else s"exists ${n.existential.mkString(", ")}. "
        var basic = if (n.basic.eqs.isEmpty && n.basic.fins.isEmpty) "" else n.basic.toString
        if (basic.isEmpty && n.nested.isEmpty) {
          basic = "true"
        }
        val nested = n.nested.mkString(" & ")
        if (basic.nonEmpty && n.nested.nonEmpty) {
          basic += " & "
        }
        "(" + existential + basic + nested + ")"
      }.mkString("\n | ")
    }
    println(s"\nSOLVED FORM:\n$result")
  }

  /** Only needed for compatibility with old Java versions. */
  def readFile(path: String): String = {
    new String(Files.readAllBytes(Paths.get(path)))
  }
}

class InvalidInputException(message: String) extends Exception(message)
