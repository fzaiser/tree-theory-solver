import java.io.PrintStream
import java.nio.file.{Files, Path, Paths}

import scala.collection.mutable
import scala.jdk.StreamConverters._

object SmtLibTest {
  /** Runs the reductions and solver on the QF_DT benchmark suite from the SMT-LIB. */
  def runBenchmark(benchmarkPath: String, timeout: Int, output: PrintStream, semantics: SelectorSemantics): Unit = {
    val dir = Paths.get(benchmarkPath)
    val paths = Files.walk(dir).toScala(Seq)
      .filter(p => p.toString.endsWith(".smt2") && p.toString.contains("tests"))
      .sorted
    var counter = 0
    var skippedUnknown = 0
    var parseFailed = 0
    var timedOut = mutable.Buffer.empty[Path]
    var solvedCorrectly = 0
    var solvedWrongly = mutable.Buffer.empty[Path]
    output.println("path; time in ms")
    for (path <- paths) {
      if (counter % 100 == 0) System.err.println(s"$counter done.")
      counter += 1
      val source = io.Source.fromFile(path.toFile)
      try {
        val contents = source.mkString
        if (contents.contains(":status sat") || contents.contains(":status unsat")) {
          val instance = Smt.parse(contents)
          val result = solveInstance(instance.inst, timeout, semantics)
          if (result.isEmpty) {
            timedOut += path
            output.println(s"$path; $timeout")
          } else {
            val (resultSat, time) = result.get
            output.println(s"$path; $time")
            if (resultSat == instance.isSat) {
              solvedCorrectly += 1
            } else {
              solvedWrongly += path
            }
          }
        } else {
          skippedUnknown += 1
        }
      } catch {
        case ex: Exception =>
          parseFailed += 1
          System.err.println(s"$path: Exception while processing $path")
          ex.printStackTrace()
          System.exit(1)
      }
      finally {
        source.close()
      }
    }
    output.flush()
    println(s"Total files                   : $counter")
    println(s"Skipped because status missing: $skippedUnknown")
    println(s"Parse errors                  : $parseFailed")
    println(s"Solved correctly              : $solvedCorrectly")
    println(s"Solving timed out             : ${timedOut.size}")
    println(s"Solved incorrectly            : ${solvedWrongly.size}")
    println("SOLVED WRONGLY:")
    solvedWrongly.sorted.foreach(println)
    println("TIMED OUT:")
    timedOut.sorted.foreach(println)
  }

  /** Try to solve the given SMT datatype instance.
   * Returns whether it is satisfiable and the computation time, or None if it times out. */
  def solveInstance(instance: DatatypeInstance, timeoutMillis: Int, semantics: SelectorSemantics):
  Option[(Boolean, Double)] = {
    val (ctx, nf) = DatatypeReduction.reduce(instance, semantics, negate = true)
    var result: Option[Seq[NormalFormula]] = None
    var time = 0.0
    val solver = new Solver()
    val thread = new Thread {
      override def run(): Unit = {
        val startTime = System.nanoTime()
        try {
          result = Some(solver.solveNf(ctx, nf))
        } catch {
          case ComputationStoppedException =>
          case ex: Exception => ex.printStackTrace()
        }
        time = (System.nanoTime() - startTime) / 1_000_000.0
      }
    }
    thread.start()
    thread.join(timeoutMillis)
    if (result.isEmpty) {
      solver.shouldStop = true
      thread.join()
      None
    } else {
      val resultSat = result.get.nonEmpty
      Some((resultSat, time))
    }
  }
}
