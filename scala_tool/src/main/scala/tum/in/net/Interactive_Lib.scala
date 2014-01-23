package tum.in.net

import tum.in.net.psn.log_topo.NetworkModels.{NetGraph, NetworkModelAbstract}
import tum.in.net.netModelVisualizer.{ShellOut, GraphVizify}
import tum.in.net.psn.log_topo.{TopologyGenerator}
import tum.in.net.StringNode._
import tum.in.net.export.{OpenVPNconfigExtractor}
import tum.in.net.netModelVisualizer.{GraphUpdateObserver, GraphUpdateSubject}
import be.jvb.iptypes.IpAddress

protected object InteractiveHelper{
  def blue(s: String): String = Console.BLUE+s+Console.RESET
  def red(s: String): String = Console.RED+s+Console.RESET
}

abstract class InteractiveWithMutableState {
  
  protected class mutableStorage(private[this] var graph: NetGraph, 
      private[this] val models: List[NetworkModelAbstract],
      private[this] val visual_extra: Map[String, List[Node]]) extends GraphUpdateSubject
  {
    import InteractiveHelper._
    private var myVisualShell: ShellOut = null
    private var myVisualGraphviz: GraphVizify = null
    private var myTopology: TopologyGenerator = null
    private var myCompletionsNode: java.util.Collection[String] = null
  
    //getter
    def visualShell: ShellOut = myVisualShell
    def visualGraphviz: GraphVizify = myVisualGraphviz
    def completionsNode: java.util.Collection[String] = myCompletionsNode
    def nodes: List[Node] = graph.nodes
    def getGraph: NetGraph = graph
    def _getModels: List[NetworkModelAbstract] = models
    def _getVisualExtra: Map[String, List[Node]] = visual_extra
    
    //observer pattern inherited
    
    
    update()
    
    
    private def update() = {
      println("updating console's mutable state")
      myVisualShell = new ShellOut(graph, models)
      myVisualGraphviz = new GraphVizify(graph, models, visual_extra)
      myTopology = new TopologyGenerator(graph, models)
      
      import collection.JavaConversions._
      myCompletionsNode = graph.nodes.toSeq
      
      //notify observers about changes in graph
      notifyGraphUpdateObservers(graph)
    }
    
    def add_edge(e1: Node, e2: Node): Unit = {
      if (graph.edges.contains((e1, e2))) println(red("Warning")+": edge already exists")
      graph = graph.add_edge(e1, e2)
      update
    }
    
    def del_edge(e1: Node, e2: Node): Unit = {
      if (!graph.edges.contains((e1, e2))) println(red("Warning")+": edge does not exist")
      graph = graph.delete_edge(e1, e2)
      update
    }
    
    def add_node(n: Node): Unit = {
      if (graph.nodes.contains(n)) println(red("Warning")+": node already exists")
      graph = graph.add_node(n)
      update
    }
    
    def del_node(n: Node): Unit = {
      graph = graph.delete_node(n)
      update
    }
    
    /**
     * get THE maximum topology
     * Do not update state
     */
    def get_maximum_topology: NetGraph = {
      myTopology.tryCreateTopology
      println("Topology generation stats:\n"+myTopology.stats)
      assert(myTopology.isMaximum)
      myTopology.getCreatedGraph
    }
    
    /**
     * get some generated topology
     * Do not update state
     */
    def get_create_topology: NetGraph = {
      myTopology.tryCreateTopology
      println("Topology generation stats:\n"+myTopology.stats)
      myTopology.getCreatedGraph
    }
    
    /**
     * updates the graph with some maximum topology
     */
    def create_topology_update(): Unit = {
      myTopology.tryCreateTopology
      println("Topology generation stats:\n"+myTopology.stats)
      println(blue("INFO")+": reloading graph with created one. You are now working on a new graph.")
      graph = myTopology.getCreatedGraph
      update
    }
    
    def newMutableStoragepreserveGraph(models: List[NetworkModelAbstract]): mutableStorage = 
      new mutableStorage(graph, models, visual_extra)
    
    
    def writeOpenVPNconfig(serverIP: IpAddress): Unit = {
      val exporter = new OpenVPNconfigExtractor(graph, models, serverIP)
      exporter.writeConfiguration()
      
      // destroy exporter. One exporter per temp directory it writes its results in
    }
  } /* end mutableStorage */
  
  
  private var models: List[NetworkModelAbstract] = psn.log_topo.JSONLoader.load_models
  protected var data = {
    import psn.log_topo.JSONLoader
    val graph: NetGraph = JSONLoader.load_graph
    
    val visual_extra = JSONLoader.load_visual_extra()
    
    new mutableStorage(graph, models, visual_extra)
  }
  
  protected def reload_models() = {
    import psn.log_topo.JSONLoader
    models = JSONLoader.load_models
    data = data.newMutableStoragepreserveGraph(models)
    
    println(printLoadedModelsInfo)
  }
  
  protected def printLoadedModelsInfo(): String = {
    val l = for (m <- models) yield m.toString()
    l mkString "\n"
  }
} /* end InteractiveWithMutableState */


abstract class InteractiveWithConsole extends InteractiveWithMutableState {
  import scala.tools.jline
  import collection.JavaConversions._
  
  protected val console = new jline.console.ConsoleReader()
  console.setPrompt(">>> ")
  println(Console.BLUE+"Hint"+Console.RESET+": use tab completion")
  
  protected def readLineCommand(): Option[String] = {
    val CommandCompletions: java.util.Collection[String] = availableCommands.keys.toSeq
    val CommandCompleter = new jline.console.completer.StringsCompleter(CommandCompletions)
    
    console.addCompleter(CommandCompleter)
    val result = console.readLine() match {
      case null => None
      case x => Some(x.trim())
    }
    console.removeCompleter(CommandCompleter)
    result
  }
  
  protected def realLineYesNo(): Boolean = {
    val oldPromt = console.getPrompt()
    console.setHistoryEnabled(false)
    console.setPrompt("[yes/no] ")
    val result = console.readLine() match {
      case null => println("Are you trying to quit? " + "\n" +
          "I'm afraid that's something I cannot allow to happen." + "\n" +
          "[y/n]?"); realLineYesNo()
      case x => {
        val answer = x.trim().toLowerCase()
        if (answer == "y" || answer == "yes") true
        else if (answer == "n" || answer == "no") false
        else {println("yes or no? [y/n]"); realLineYesNo()}
      }
    }
    console.setHistoryEnabled(true)
    console.setPrompt(oldPromt)
    result
  }
  protected def readLineNode(warnNotExisting: Boolean = false, warnExisting: Boolean = false): 
      Option[String] = {
    val NodeCompleter = new jline.console.completer.StringsCompleter(data.completionsNode)
    console.setHistoryEnabled(false)
    console.addCompleter(NodeCompleter)
    
    val result = console.readLine() match {
      case null => None
      case x => {
        val node = x.trim()
        val continue = if (warnNotExisting && !data.nodes.contains(node)) {
          println("Node `"+node+"' does not exist")
          println("continue? [y/n]")
          realLineYesNo()
        } else if (warnExisting && data.nodes.contains(node)) {
          println("Node `"+node+"' does already exist")
          println("continue? [y/n]")
          realLineYesNo()
        } else true
        if (continue) Some(node)
        else None
      }
    }
    console.removeCompleter(NodeCompleter)
    console.setHistoryEnabled(true)
    result
  }
  
  protected def readLineString(): String = {
    val oldPromt = console.getPrompt()
    console.setHistoryEnabled(false)
    console.setPrompt("[String] ")
    val result = Option(console.readLine()) getOrElse {
      println("Are you trying to quit? " + "\n" +
             "I'm afraid that's something I cannot allow to happen.")
      readLineString()
    }
    console.setHistoryEnabled(true)
    console.setPrompt(oldPromt)
    result
  }
  
  protected abstract trait ShellCommand{
    def cmd(): Unit
    val help: String
    val continue: Boolean
  }

  
  protected val availableCommands: Map[String, ShellCommand]
  
  /**
   * reset the terminal.
   * Call this after some exception was thrown to restore terminal.
   * If you run the program from sbt, sbt's readline is a bit broken.
   */
  def resetTerminal() = {
    println(Console.RESET)
    jline.TerminalFactory.get().restore()
  }
  
  /**
   * return a help message
   */
  def help: String = "available commands are\n"+
      availableCommands.foldLeft("")((acc, e) => acc+"  "+e._1+": "+e._2.help+"\n")
  
  /**
   * start interactive shell
   */
  def readConsole(): Unit = {
    val ln = readLineCommand()
    ln match {
      case None => println("EOF"); resetTerminal()
      case Some(line) => availableCommands.get(line) match {
        case Some(command) => {
          command.cmd()
          if (command.continue) readConsole()
        }
        case None => println("unknown command `"+line+"'"+"\n"+help); readConsole()
      }
    }
  }
}


abstract class InteractiveWithTimeoutCode extends InteractiveWithConsole{
  
  /**
   * run function f for some time, return f's result
   * Ask nicely if you want to interrupt f if it takes longer than timeout milliseconds
   * 
   * Note: f should do no locking and should be side effect free
   */
  def runTimeout[T](timeout: Long)(f: => T)(implicit m: scala.reflect.ClassTag[T]): Option[T] = {
    val task = new Thread{
      def getResult() = this.synchronized{result}
      private var result: Option[T] = None
      override def run() = {
        try {
          val myResult = f
          this.synchronized{result = Some(myResult)}
        } catch {
          case e: InterruptedException => println("interrupted")
        }
      }
    }
    
    task.start()
    
    def waitForResult(): Option[T] = {
      task.join(timeout)
      if(task.getResult() == None){
        println("No result yet, wait some more?")
        if (realLineYesNo())
          waitForResult()
        else{
          task.interrupt()
          task.getResult()
        }
      }else
        task.getResult()
    }
    
    val result = waitForResult()
    result
  }
}
