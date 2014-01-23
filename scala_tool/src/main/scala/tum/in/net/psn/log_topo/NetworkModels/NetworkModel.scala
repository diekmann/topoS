package tum.in.net.psn.log_topo.NetworkModels

import GENERATED.NetworkModel_Lists_Impl_Interface.networkModel_packed_ext
import GENERATED.NetworkModel_Lists_Impl_Interface.{
  nm_default, nm_eval, nm_node_props, nm_offending_flows, nm_name, 
  nm_verify_globals, nm_target_focus}
import GENERATED.NetworkModel_Interface.networkModel_Params_ext
import GENERATED.NetworkModel_Interface.{
  networkModel_Params_ext, NetworkModel_Params_ext, model_global_properties}
import tum.in.net.psn.log_topo.HOLequal_String._

/**
 * call isabelle's generated code
 */
protected abstract class NetworkModelVerifedCode[NodeP, GlobalP](
    model_packed: networkModel_packed_ext[Node, NodeP, GlobalP, Unit],
    params: networkModel_Params_ext[Node,NodeP,GlobalP,Unit]
    )
    extends NetworkModelAbstract
{

  protected final val nP: (Node => NodeP) = nm_node_props(model_packed).apply(params)
  protected final val gP: GlobalP = model_global_properties(params)
  
  
  override final def model_type: String = {
    nm_name[Node, NodeP, GlobalP, Unit](model_packed).mkString
  }
  
  override def eval(graph: NetGraph): Boolean = {
    (nm_eval[Node, NodeP, GlobalP, Unit](model_packed)).apply(graph.graph_ext).apply(params)
  }
  
  
  override def offending_flows(graph: NetGraph, errorStream: java.io.PrintStream = Console.err): List[List[(Node, Node)]] = {
    if (!verify_globals(graph)){
      throw new RuntimeException("Call on offending_flows where verify globals is false");
  	}
      try {
        (nm_offending_flows[Node, NodeP, GlobalP, Unit](model_packed)).apply(graph.graph_ext).apply(nP)
  	  } catch {
  	    case e:java.lang.StackOverflowError => {
  	      errorStream.println("Stack overflow in offending_flows!!")
  	      errorStream.println(" "+model_type+": "+description)
  	      errorStream.println(" (known problem)")
  	      errorStream.println(" try increasing stack size: java -Xss4M")
  	      errorStream.println(" "+e.toString)
  	      // throw new to clear stack trace
  	      throw new java.lang.StackOverflowError
  	      }
  	  }
  }

  final override def verify_globals(graph: NetGraph): Boolean = {
    (nm_verify_globals[Node, NodeP, GlobalP, Unit](model_packed)).apply(graph.graph_ext).apply(nP).apply(gP)
  }
  
  
  final override def isIFS(): Boolean = {
    val result = nm_target_focus[Node, NodeP, GlobalP, Unit](model_packed)
    assert(result == !isACM())
    result
  }
  
  final override def isACM(): Boolean = {
    ! nm_target_focus[Node, NodeP, GlobalP, Unit](model_packed)
  }
} /* end NetworkModelVerifedCode */


/**
 * cache expensive computations
 */
protected trait NetworkModelResultCacher[NodeP, GlobalP] extends NetworkModelVerifedCode[NodeP, GlobalP]
{
  private var cache_eval: (NetGraph, Boolean) = (null, false)
  override def eval(graph: NetGraph): Boolean = {
      //printDebugOutput(graph)
    if (cache_eval._1 == graph){
      //println("cache_eval hit")
      cache_eval._2 
    } else {
      val res = super.eval(graph)
      cache_eval = (graph, res)
      res
    }
  }

  private var cache_offending_flows: (NetGraph, List[List[(Node, Node)]]) = (null, null)
  override def offending_flows(graph: NetGraph, errorStream: java.io.PrintStream = Console.err): List[List[(Node, Node)]] = {
    if (cache_offending_flows._1 == graph){
      //println("cache_offending_flows hit")
      cache_offending_flows._2 
      } else {
        val res = super.offending_flows(graph, errorStream)
    	  cache_offending_flows = (graph, res)
    	  res
    	}
    }
}

/**
 * functions to pretty print everything
 */
protected trait NetworkModelPrettyPrinter[NodeP, GlobalP]
{
    this: NetworkModel[NodeP, GlobalP] =>
    
    final def nodeConfigToString(node: Node): String = {
      if (configured_nodes.contains(node))
        prettyprint_nodeConfigToString(node)
      else
        "⊥"
  }

  // override this to pretty print the output.
  protected def prettyprint_nodeConfigToString(node: Node): String = {
    import GENERATED.Nat
    import GENERATED.Code_Numeral.integer_of_nat
    val value: NodeP = nP(node)
    val str = if (value.isInstanceOf[Nat.nat])
                  integer_of_nat(value.asInstanceOf[Nat.nat]).toString
              else
                  value.toString
    // fix introduced by Isabelle2013
    // case objects are now case classes
    // instead of printing "Unassigned()", let's print "Unassigned"
    if (str.endsWith("()"))
      str.dropRight("()".length)
    else
      str
  }


  def nPtoString: String = {
    def iter(c: List[Node]): String = if (c.isEmpty) "" else c.head.toString() + "->" + nodeConfigToString(c.head) + ", " + iter(c.tail)
    iter(configured_nodes)
  }
  
  def globalConfigToString: String = gP.toString
    
  override def toString: String = "NetworkModel "+model_type+" in config\n  nP: "+nPtoString+"\n  gP: "+globalConfigToString

}


/**
 * add warnings
 */
protected trait NetworkModelWarnings[NodeP, GlobalP] extends NetworkModelVerifedCode[NodeP, GlobalP]{
  this: NetworkModel[NodeP, GlobalP] =>
  
  protected def printDebugOutput(graph: NetGraph) = {
    def conf_node_iter(ns: List[Node]): Unit = {
      if (!ns.isEmpty){
        if (!graph.nodes.contains(ns.head)){
          util.WarningPrinter.emit_warning("Warning ("+model_type+"): Configured but not in graph: "+ns.head)
          }
          conf_node_iter(ns.tail)
        }
      }
      conf_node_iter(configured_nodes)
  }
  
  override def eval(graph: NetGraph): Boolean = {
    printDebugOutput(graph)
    super.eval(graph)
  }
}

/**
 * Final NetworkModel, mixin all previous traits
 */
protected class NetworkModel[NodeP, GlobalP](
    model_packed: networkModel_packed_ext[Node, NodeP, GlobalP, Unit],
    params: networkModel_Params_ext[Node,NodeP,GlobalP,Unit],
    protected val configured_nodes: List[Node],
    val description: String,
    val model_breach_severity: Int
    ) extends NetworkModelVerifedCode[NodeP, GlobalP](model_packed, params)
        with NetworkModelPrettyPrinter[NodeP, GlobalP]
        with NetworkModelResultCacher[NodeP, GlobalP] 
        with NetworkModelWarnings[NodeP, GlobalP]
{
  final def isConfiguredNode(n: Node) = configured_nodes.contains(n)
  
  final def model_breach_severity_rating(graph: NetGraph, errorStream: java.io.PrintStream = Console.err): Int = {
    if (eval(graph)) return 0
    
    val illegal_flows_all: List[List[(Node,Node)]] = offending_flows(graph, errorStream)
    assert(illegal_flows_all.length > 0)
    
    // length of longest illegal flow set
    val num_illegal = illegal_flows_all.map(_.length).foldLeft(0)(_ max _)
    assert(num_illegal > 0)
    
    // select first illegal flow with max size
    val illegal_flows: List[(Node,Node)] = illegal_flows_all.filter(f => f.length == num_illegal).head
    
    // simple metric
    val unrated = num_illegal * model_breach_severity
    
    if(illegal_flows_all.length > 1)
      println("Warining: offending flows ambiguous! Choosing longest flow. Rating may be skewed.")
      
    unrated
  }

}