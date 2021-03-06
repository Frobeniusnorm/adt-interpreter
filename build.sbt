val scala3Version = "3.1.0"

lazy val root = project
  .in(file("."))
  .settings(
    name := "adt-interpreter",
    version := "1.3.3",

    scalaVersion := scala3Version,

    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test"
  )
