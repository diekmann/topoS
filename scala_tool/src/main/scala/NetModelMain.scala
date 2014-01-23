

object NetModelMain{

  def startInteractive() : Unit = {
    println("hello, World!")
    
    println("setting up warning printer")
    util.WarningPrinter.print_function = {err =>
      val txt = Console.RED + Console.BOLD + "WARNING:" + Console.RESET + " "+ err
      println(txt)
    }

    println("Available requirements as models:")
    println(tum.in.net.psn.log_topo.NetworkModels.JSONParser.modelParserMapping.keys)
    println()
    
    val in = try {
      new tum.in.net.Interactive()
    } catch {
      case e: Throwable =>
        println(e)
        e.printStackTrace()
        println("Failed to init Interactive. maybe call reset to reset your terminal")
        scala.tools.jline.TerminalFactory.get().restore()
        //scala.tools.jline.TerminalFactory.get().reset() this fucks up your terminal
        null
    }
    
    if (in != null)	try{
      in.readConsole
    } catch {
      case e : Throwable => {
        println("terminated with some excpetion, ...")
        println(e)
        e.printStackTrace()
        println("resetting terminal")
        in.resetTerminal()
      }
    } finally {
      println("goodbye")
    }
  }

  def extraConvenienceFunctions(): Unit = {
    import tum.in.net.psn.log_topo.JSONLoader
    import tum.in.net.psn.log_topo.NetworkModels.DomainHierarchyTENetworkModel
    //print domain hierarchy for all loaded models
    val models = JSONLoader.load_models
    import tum.in.net.psn.log_topo.NetworkModels.DomainHierarchyNetworkModel

    models.foreach(m => if (m.isInstanceOf[DomainHierarchyNetworkModel])
      println((m.asInstanceOf[DomainHierarchyNetworkModel]).globalConfigToGraphvizCompatibleString))


      models.foreach(m => if (m.isInstanceOf[DomainHierarchyTENetworkModel])
        println((m.asInstanceOf[DomainHierarchyTENetworkModel]).globalConfigToGraphvizCompatibleString))
  }

  def breachRating(): Unit = {
    tum.in.net.experimental.NIDSConfig.breachRating()
  }


  def precalculateBreachRating(): Unit = {
    tum.in.net.experimental.NIDSConfig.precalculateBreachRating()
  }

  def main(args: Array[String]) {
    val startupCMD: Map[String, () => Unit] = Map(
        "breach-rating" -> breachRating,
        "precal-breach-rating" -> precalculateBreachRating,
        "convenience" -> extraConvenienceFunctions
        )

    args.toList match {
      case List(cmd) => if(startupCMD.keySet.contains(cmd)) startupCMD(cmd)() else{
        println("Unknown parameter `"+cmd+"'")
        println("Available commands: "+startupCMD.keys.toList)
        println("Omit command line argument to start interactive")
      }
      case Nil => startInteractive()
      case e => println("Unknown parameter list: "+e)
    }
  }
}
