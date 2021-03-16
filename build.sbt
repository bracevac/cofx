lazy val root = project
  .in(file("."))
  .settings(
    name := "cofx",
    version := "0.1.0",
    scalaVersion := "3.0.0-M3",
    useScala3doc := true 
  )
