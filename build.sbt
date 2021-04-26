lazy val root = project
  .in(file("."))
  .settings(
    name := "cofx",
    version := "0.1.0",
    scalaVersion := "3.0.0-RC2",
    useScala3doc := true 
  )
