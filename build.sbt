name := "tree-theory-solver"

version := "0.1"

scalaVersion := "2.13.2"

libraryDependencies += "org.scalatest" % "scalatest_2.13" % "3.1.1" % "test"
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2"

scalacOptions ++= Seq(
  "-deprecation"
)
