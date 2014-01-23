import de.johoop.findbugs4sbt.FindBugs._


name := "NetworkSecurityModellingTool"

version := "0.1.1"

scalaVersion := "2.10.0"


//https://github.com/sbt/sbt-onejar
seq(com.github.retronym.SbtOneJar.oneJarSettings: _*)

libraryDependencies += "commons-lang" % "commons-lang" % "2.6"

// http://mvnrepository.com/artifact/org.scala-lang/jline/2.9.2
//http://vikashazrati.wordpress.com/2011/09/01/quicktip-ignoring-some-jars-from-getting-assembled-in-sbt-0-10x/
libraryDependencies += "org.scala-lang" % "jline" % "2.10.0" intransitive()  

//https://github.com/lift/framework/tree/master/core/json
// exclude fixes bug (larsch)
libraryDependencies += "net.liftweb" %% "lift-json" % "2.5-M4" exclude("org.specs2","specs2_2.10")

scalacOptions += "-deprecation"

scalacOptions += "-unchecked"

scalacOptions += "-feature"

//https://bitbucket.org/jmhofer/findbugs4sbt/wiki/Home
//import de.johoop.findbugs4sbt.FindBugs._

findbugsSettings

findbugsReportType := Some(de.johoop.findbugs4sbt.ReportType.FancyHistHtml)

findbugsReportName := Some("findbugs.html")

//http://www.scalatest.org/user_guide/using_scalatest_with_sbt
libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" % "test"

