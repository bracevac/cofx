val AkkaVersion = "2.6.13"

lazy val root = project
  .in(file("."))
  .settings(
    name := "cofx",
    version := "0.1.0",
    scalaVersion := "3.0.0-M3",
    useScala3doc := true,
    libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3",
    libraryDependencies += ("com.typesafe.akka" %% "akka-actor-typed" % AkkaVersion).withDottyCompat(scalaVersion.value),
    libraryDependencies += ("com.typesafe.akka" %% "akka-actor-testkit-typed" % AkkaVersion % Test).withDottyCompat(scalaVersion.value),
  )
