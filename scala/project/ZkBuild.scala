import sbt._
import sbt.Keys._

object ZkBuild extends Build {
  val useScalaVersion = "2.11.1"
  lazy val zk = Project(
    id = "zk",
    base = file("."),
    settings = Project.defaultSettings ++ Seq(
      name := "zk",
      organization := "zk",
      version := "0.1",
      scalaVersion := useScalaVersion,
      autoScalaLibrary := false,
      exportJars := true,
      // add other settings here
      scalacOptions ++= Seq("-feature", "-language:higherKinds", "-language:implicitConversions", "-deprecation", "-unchecked", "-Yinline-warnings"),
      //scalacOptions += "-optimise",
      //scalacOptions += "-verbose",

      // add other settings here
      libraryDependencies += "org.scala-lang" %  "scala-library"     % useScalaVersion,
      libraryDependencies += "org.scalaz"     %% "scalaz-core"       % "7.1.0-M7"
    )
  )
}
