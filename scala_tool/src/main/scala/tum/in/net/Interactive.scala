package tum.in.net

import tum.in.net.psn.log_topo.NetworkModels.{NetGraph, NetworkModelAbstract}
import tum.in.net.netModelVisualizer.{ShellOut, GraphVizify}
import tum.in.net.StringNode._
import be.jvb.iptypes.IpAddress


/*
 * File contains an interactive shell
 */




/**
 * run the readConsole method to start an interactive shell
 */
class Interactive extends InteractiveWithTimeoutCode{
  
  protected def generateDiffMatrix(both: String = "  *  ",
      newOnly: String = "  _  ",
      oldOnly: String = " X-X ",
      neither: String = "     "): Array[Array[String]] = 
  {
      import tum.in.net.psn.log_topo.FlowMatrix
      // old graph
      val g_old = data.getGraph
      
      //new graph
      println("generating some maximum topology")
      val g_new = data.get_create_topology
      
      // diffing g_old and g_new
      val diffMatrix  = FlowMatrix.diffMatrix(g_old, g_new, both, newOnly, oldOnly, neither)
      
      //println(diffMatrix.deep.mkString("\n"))
      
      println("Your diff matrix:")
      println(both+" == flow in both")
      println(newOnly+" == flow only in generated")
      println(oldOnly+" == flow only in old matrix. potential error!")
      
      diffMatrix
  }
  
  
  /**
   * Ask user for two edges and execute a command
   * Used in add and delete edge command
   */
  protected def readExistingEdgesExec(cmd: (Node, Node) => Unit): Unit = {
    println("enter first edge:")
    readLineNode(warnNotExisting=true) match {
      case None => println("canceled")
      case Some(e1) => {
        println("enter second edge:")
        readLineNode(warnNotExisting=true) match {
            case None => println("canceled")
            case Some(e2) => cmd(e1, e2)
          }
        }
    }
  }
  
  
  /**
   * If graph is large: Ask user whether to aggregate biflows
   */
  def askAggegateBiflows(): Boolean = {
    val num_biflows = data.getGraph.edges.filter(e => data.getGraph.edges.contains(e._2, e._1)).length
    //println(data.getGraph.edges.filter(e => data.getGraph.edges.contains(e._2, e._1)))
    val aggregate = if(num_biflows >= 15){
      println("Aggregate bidirectional flows, remove reflexive flows? You have "+
          num_biflows+" of them. [y/n]")
      realLineYesNo()
    } else false
    aggregate
  }
  
 
  protected case object CMDquit extends ShellCommand {
    def cmd()= {println("bye"); resetTerminal()}
    val help = "quit"
    val continue = false
  }
  protected case object CMDeval extends ShellCommand {
    def cmd()= data.visualShell.output
    val help = "evaluate all models"
    val continue = true
  }
  protected case object CMDevaldetail extends ShellCommand {
    def cmd()= {
      data.visualShell.outputDetail()
      val s = runTimeout(3000){data.visualShell.otherAllowedFlows()}
      println(s.getOrElse(""))
    }
    val help = "evaluate all models, prind detailed information"
    val continue = true
  }
  protected case object CMDoutputFlowMatrix extends ShellCommand {
    def cmd()= data.visualShell.outputFlowsMatrix()
    val help = "print the matrix of all flows"
    val continue = true
  }
  protected case object CMDoutputFlowMatrixLatex extends ShellCommand {
    def cmd()= data.visualShell.outputFlowsMatrixLatex()
    val help = "'' (LaTeX style)"
    val continue = true
  }
  protected case object CMDoutputDifferentialFlowMatrix extends ShellCommand {
    def cmd()= {
      val diffMatrix = generateDiffMatrix(both = "  "+Console.BOLD+Console.GREEN+"*"+Console.RESET+"  ",
      newOnly = "  "+Console.BOLD+Console.BLUE+"m"+Console.RESET+"  ",
      oldOnly = " "+Console.BOLD+Console.RED+"X-X"+Console.RESET+" ",
      neither = "     ")
      data.visualShell.outputFlowsMatrix(diffMatrix)
    }
    val help = "print the differential matrix of your current configuration and some generated topology."
    val continue = true
  }
  protected case object CMDoutputDifferentialFlowMatrixLatex extends ShellCommand {
    def cmd()= {
      val diffMatrix = generateDiffMatrix(both = "  \\textcolor{ForestGreen}{*}  ",
      newOnly = "  \\textcolor{Blue}{m}  ",
      oldOnly = " \\textcolor{BrickRed}{XX} ",
      neither = "     ")
      data.visualShell.outputFlowsMatrixLatex(diffMatrix)
    }
    val help = "'' (LaTeX Style)"
    val continue = true
  }
  protected case object CMDoutputDifferentialGraphviz extends ShellCommand {
    def cmd()= {
      import tum.in.net.netModelVisualizer.GraphVizify_MaxTopoDiff

      val oldGraph = data.getGraph
      println("generating some maximum topology (must be unambiguous)")
      val newGraph = data.get_maximum_topology
      assert(oldGraph.nodes == newGraph.nodes)
      assert(oldGraph.edges.toSet.subsetOf(newGraph.edges.toSet), "The unambiguous maximum topology")
      val newEdges = newGraph.edges.diff(oldGraph.edges)
      
      val visual = new GraphVizify_MaxTopoDiff(newGraph, data._getModels, data._getVisualExtra, newEdges)
      val aggregate = askAggegateBiflows()
      visual.displayGraph(aggregate)
    }
    val help = "visualize the difference of your current configuration and the maximum topology."
    val continue = true
  }
  protected case object CMDoutputGraphJSON extends ShellCommand {
    def cmd()= {
      val reflRemove = if(data.getGraph.edges.exists(e => e._1 == e._2)){
          println("Remove reflexive flows? [y/n]")
          realLineYesNo()
        } else false
      
      val g = if(reflRemove){
        NetGraph(data.getGraph.nodes, data.getGraph.edges.filterNot(e => e._1 == e._2))
      } else data.getGraph
      
      import psn.log_topo.JSONLoader
      println(JSONLoader.graph_to_json_str(g))
    }
    val help = "print the network graph as JSON"
    val continue = true
  }
  protected case object CMDvisualize extends ShellCommand {
    def cmd()= {
      val aggregate = askAggegateBiflows()
      data.visualGraphviz.displayGraph(aggreagte_biflow=aggregate)
    }
    val help = "visualize (invoke dot, start evince)"
    val continue = true
  }
  protected case object CMDvisualizeNeato extends ShellCommand {
    def cmd()= data.visualGraphviz.displayGraphNeato
    val help = "visualize (invoke neato, start evince)"
    val continue = true
  }
  protected case object CMDtopology extends ShellCommand {
    def cmd()= data.create_topology_update()
    val help = "try create maximum topology which fulfills all requirements"
    val continue = true
  }
  protected case object CMDaddedge extends ShellCommand {
    def cmd() = {
      readExistingEdgesExec((e1, e2) => data.add_edge(e1, e2))
    }
    val help = "add edge to graph"
    val continue = true
  }
  protected case object CMDdeledge extends ShellCommand {
    def cmd() = readExistingEdgesExec((e1, e2) => data.del_edge(e1, e2))
    val help = "delete edge from graph"
    val continue = true
  }
  protected case object CMDdeltenode extends ShellCommand {
    def cmd() = {
    println("enter node to delete:")
    readLineNode(warnNotExisting=true) match {
      case None => println("canceled")
      case Some(n) => data.del_node(n)
    }
    }
    val help = "delete node from graph"
    val continue = true
  }
  protected case object CMDaddnode extends ShellCommand {
    def cmd() = {
      println("enter node to add:")
      readLineNode(warnExisting=true) match {
        case None => println("canceled")
        case Some(n) => data.add_node(n)
      }
    }
    val help = "add node to graph"
    val continue = true
  }
  protected case object CMDreloadmodels extends ShellCommand {
    def cmd()= reload_models()
    val help = "reload all models, preserve graph"
    val continue = true
  }
  protected case object CMDexportOpenVPNconfig extends ShellCommand {
    def cmd(): Unit = {
      import InteractiveHelper._
      println("Please supply VPN server IP address")
      val inStr = readLineString()
      val srvIp = try {
        IpAddress(inStr)
      } catch {
        case e: Throwable => println("Error parsing IPv4 "+e)
        		return ()
      }
      try{
        data.writeOpenVPNconfig(srvIp)
      } catch {
        case e: java.lang.IllegalArgumentException => println(e)
          println(red("You cannot export an insecure configuration."))
          println("I'll dump you a strack trace, then you know where to disable this check ;)")
          e.printStackTrace()
      }
    }
    val help = "write a OpenVPN configuration from the current graph"
    val continue = true
  }
  protected case object CMDguiGraphWindow extends ShellCommand {
    def cmd(): Unit = {
      import tum.in.net.netModelVisualizer.InteractiveGraphView
      
      val w = new InteractiveGraphView(data.getGraph)
      data.registerGraphUpdateObserver(w)
    }
      
    val help = "GUI Graph Window"
    val continue = true
  }
  
  
  /**
   * command name as typed by user in interactive shell to actual function mapping
   */
  override val availableCommands: Map[String, ShellCommand] = scala.collection.immutable.TreeMap (
    "quit" -> CMDquit, 
    "reload-models" -> CMDreloadmodels,
    "eval" -> CMDeval,
    "eval-detail" -> CMDevaldetail,
    "print-flow-matrix" -> CMDoutputFlowMatrix,
    "print-flow-matrix--latex" -> CMDoutputFlowMatrixLatex,
    "print-flow-matrix--latex--diff" -> CMDoutputDifferentialFlowMatrixLatex,
    "print-flow-matrix--diff" -> CMDoutputDifferentialFlowMatrix,
    "print-graph--JSON" -> CMDoutputGraphJSON,
    "visualize" -> CMDvisualize,
    "visualize-neato" -> CMDvisualizeNeato,
    "visualize-diff-max" -> CMDoutputDifferentialGraphviz,
    "generate-topology" -> CMDtopology,
    "add-edge" -> CMDaddedge,
    "delete-edge" -> CMDdeledge,
    "add-node" -> CMDaddnode,
    "delete-node" -> CMDdeltenode,
    "export--openvpn" -> CMDexportOpenVPNconfig,
    "gui-graph" -> CMDguiGraphWindow
    )
  
  
}
