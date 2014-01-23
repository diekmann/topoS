// https://github.com/sbt/sbt-onejar
// This resolver declaration is added by default SBT 0.12.x
//resolvers += Resolver.url(
//  "sbt-plugin-releases", 
//  new URL("http://scalasbt.artifactoryonline.com/scalasbt/sbt-plugin-releases/")
//)(Resolver.ivyStylePatterns)

addSbtPlugin("com.github.retronym" % "sbt-onejar" % "0.8")


//https://github.com/typesafehub/sbteclipse
addSbtPlugin("com.typesafe.sbteclipse" % "sbteclipse-plugin" % "2.4.0")

//https://bitbucket.org/jmhofer/findbugs4sbt/wiki/Home
addSbtPlugin("de.johoop" % "findbugs4sbt" % "1.2.2")

