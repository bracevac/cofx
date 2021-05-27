val AkkaVersion = "2.6.13"

lazy val javaFXModules = Seq("base", "controls", "fxml", "graphics", "media", "swing", "web")

// Determine OS version of JavaFX binaries
lazy val osName = System.getProperty("os.name") match {
  case n if n.startsWith("Linux")   => "linux"
  case n if n.startsWith("Mac")     => "mac"
  case n if n.startsWith("Windows") => "win"
  case _ => throw new Exception("Unknown platform!")
}

lazy val root = project
  .in(file("."))
  .settings(
    name := "cofx",
    version := "0.1.0",
    scalaVersion := "3.0.0",
    libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3",
    libraryDependencies += ("org.scalafx" %% "scalafx" % "15.0.1-R21").cross(CrossVersion.for3Use2_13),
    libraryDependencies ++= javaFXModules.map { m =>
      "org.openjfx" % s"javafx-$m" % "15.0.1" classifier osName
    },
    libraryDependencies += ("com.typesafe.akka" %% "akka-actor-typed" % AkkaVersion).cross(CrossVersion.for3Use2_13),
    libraryDependencies += ("com.typesafe.akka" %% "akka-actor-testkit-typed" % AkkaVersion % Test).cross(CrossVersion.for3Use2_13),
  )
