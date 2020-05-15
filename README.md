Overview
===

This repository contains the implementation (in Scala) of the algorithms in the article

> [Fabian Zaiser, C.-H. Luke Ong: *The Extended Theory of Trees and Algebraic (Co)Datatypes.* (2020)](https://arxiv.org/abs/2005.06659)

The program takes an input file describing a formula
in the extended theory of trees and solves (simplifies) it.
The simplified formula makes it easy to read off all possible models.
The program can also solve formulae about (co)datatypes by a reduction to formulae about trees.

Code overview
---

The main code is in `src/main/scala/` and tests in `src/test/scala/`.
Example input files can be found in `examples/`.

Good starting points for exploring the code are the following:
* `DatatypeReduction.scala`: reduces formulae about (co)datatypes to formulae about trees (Section 3 of the article).
* `Signature.scala`: stores information about the sorts and contains the algorithm for analyzing sorts (Section 4 of the article).
* `Solver.scala`: contains the main solver (Section 5 of the article).
  It makes use of the rewriting rules implemented in `Rule.scala`.

How to build
===

* Install [*Scala*](https://www.scala-lang.org/) and
  [*sbt* (the Scala build tool)](https://www.scala-sbt.org/)
  if you haven't yet.
  Regarding versions, Scala 2.13.2 and sbt 1.3.10 were verified to work.
* Run
  ```
  $ sbt assembly
  ```
  For more information on `sbt assembly`, see [here](https://github.com/sbt/sbt-assembly).
  (You can also use `sbt build` and `sbt run` later
  but this does not create a single `jar` file.)
* This will create the file `target/scala-2.13/tree-theory-solver-assembly-0.1.jar`.
  (The path may differ depending on the Scala version.)

How to run
===

Run the `jar` file using
```
$ java -jar target/scala-2.13/constraint-solver-assembly-0.1.jar
```
It will print a help text explaining how to use it.
The input file formats are described below.

**Note:** For different Scala versions, you will have to adapt the path `target/scala-2.13/tree-theory-solver-assembly-0.1.jar`.

How to run the `QF_DT` benchmark suite from the SMT-LIB
---

* Download the [`QF_DT` benchmark suite](http://smtlib.cs.uiowa.edu/benchmarks.shtml).
* Run the following command
  ```
  $ java -jar target/scala-2.13/tree-theory-solver-assembly-0.1.jar benchmark <path to downloaded QF_DT directory> --output <output file.csv> --timeout <timeout in milliseconds>
  ```
* The above command uses the standard selector semantics by default,
  which can be explicitly specified by adding `--selector-semantics standard`.
  The semantics with default values can be specified by adding `--selector-semantics default-values`.
* The output will be a CSV file that lists for each SMT file the time it took to solve it (or until it timed out).

Input file formats
===

There are two text formats: for trees and for (co)datatypes.
Examples can be found in `examples/`.

Tree inputs
---

A tree input looks like this:
```
sort sort1 = generator1(sort1, sort2, ...), generator2(...) ...
open sort sort2 = ...
...

free free_variable1: sort_of_variable1, ...

solve {formula}
```
where

* `sort` declares sorts
* `open sort` declares sorts that are assumed to have
  infinitely many generators, finite inhabitants and infinite inhabitants,
* `free` declares the free variables that can be used in the formula,
* `{formula}` is a logical formula where
  * `fin(t)` denotes a finiteness constraint for the term `t`,
  * `s = t` denotes an equation of two terms `s` and `t`,
  * `!` denotes negation,
  * `&` conjunction,
  * `|` disjunction,
  * `exists var1: sort1, var2:sort2. {formula}` existential quantification
  * `and forall var1: sort1, var2: sort2. {formula}` universal quantification.

(Co)datatype inputs
---
A (co)datatype input looks like this:
```
data datatype1 = constructor1(selector1: datatype1, selector2: datatype2, ...) | constructor2(...) ...
data datatype2 = ...
...
codata codatatype1 = constructor1(selector1: codatatype1, selector2: codatatype2, ...) | constructor2(...) ...
codata codatatype2 = ...
...

free free_variable1: sort_of_variable1, ...

solve {formula}
```
where `{formula}` is written as for trees.

Output format
---
The output will consist of the input formula, put into normal form, and its solved form.
