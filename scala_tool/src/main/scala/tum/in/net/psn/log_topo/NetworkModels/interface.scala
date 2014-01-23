package tum.in.net.psn.log_topo.NetworkModels

import GENERATED.FiniteListGraph
import GENERATED.FiniteListGraph.{list_graph_ext, List_graph_ext}

import tum.in.net.psn.log_topo.HOLequal_String._


/**
 * The Network graph we are working on
 * 
 * can be obtained from a JSON String in
 * JSONParser.GraphParser(JSONString).G
 */
class NetGraph(final val graph_ext: FiniteListGraph.list_graph_ext[Node, Unit]){
  if (!FiniteListGraph.valid_list_graph(graph_ext)) throw new RuntimeException("Invalid graph")
  
  final val nodes: List[Node] = FiniteListGraph.nodesL(graph_ext)
  final val edges: List[(Node, Node)] = FiniteListGraph.edgesL(graph_ext)
  
  
  override def toString: String = "valid graph:\n  nodes: "+nodes+"\n  edges: "+edges
  
  /**
   * object is immutable. returns new object
   */
  final def add_edge(e1: Node, e2: Node): NetGraph = new NetGraph(
        FiniteListGraph.add_edge[Node](e1, e2, this.graph_ext))
  
  final def add_node(n: Node): NetGraph = new NetGraph(
        FiniteListGraph.add_node[Node](n, this.graph_ext))
  
  final def delete_edge(e1: Node, e2: Node): NetGraph = new NetGraph(
        FiniteListGraph.delete_edge[Node](e1, e2, this.graph_ext))
  
  final def delete_node(n: Node): NetGraph = new NetGraph(
        FiniteListGraph.delete_node[Node](n, this.graph_ext))
  
}

/**
 * Companion object, Allows easy creation of net NetGraph
 * NetGraph(nodes, edges)
 */
object NetGraph{
  def apply(nodes: List[Node], edges: List[(Node, Node)]): NetGraph = {
    val g: list_graph_ext[Node, Unit] = List_graph_ext[Node, Unit](nodes, edges, ())
    new NetGraph(g)
  }
}

/**
 * The essential functions of a network model. 
 * Verified code for them
 */
abstract class NetworkModelAbstractPure {
  /** name **/
  def model_type: String
  
  /** true iff model valid **/
  def eval(graph: NetGraph): Boolean
  
  /** flows which invalidate model **/
  def offending_flows(graph: NetGraph, errorStream: java.io.PrintStream = Console.err): List[List[(String, String)]]
  
  /** syntactic check of model parameters **/
  def verify_globals(graph: NetGraph): Boolean
  
  /** return true iff this is an information flow security model */
  def isIFS(): Boolean
  
  /** return true iff this is an access control model */
  def isACM(): Boolean
}

/**
 * Network Security Model
 * With convenience functions
 */
abstract class NetworkModelAbstract extends NetworkModelAbstractPure{
    /** Textual description of the security requirement encoded in this model **/
  def description: String
  
  /** pretty print configuration for node as configured in model **/
  def nodeConfigToString(node: Node): String
  
  /** returns true if node is explicitly configured */
  def isConfiguredNode(node: Node): Boolean
  
  /** return how severe a violation of this model, given a graph, is **/
  def model_breach_severity_rating(graph: NetGraph, errorStream: java.io.PrintStream = Console.err): Int
}

/**
 * convenience functions on List[NetworkModelAbstract]
 */
object NetworkModelList {
  // import tum.in.net.NetworkSecurityModelling.NetworkModels.NetworkModelList._
  // to get these convenient functions on List[NetworkModelAbstract]
  
  implicit def NetworkModelListToRichNetworkModelList(l: List[NetworkModelAbstract]) = 
    new RichNetworkModelList(l)
  
  class RichNetworkModelList(models: List[NetworkModelAbstract]) {
    def breach_severity_rating(graph: NetGraph): Int = 
      models.foldLeft(0)((acc, m) => acc + m.model_breach_severity_rating(graph))
    
    /** true iff all models valid */
    def allValid(graph: NetGraph): Boolean = models.foldLeft(true)((acc, m) => acc && m.eval(graph))
    
    /** true iff node n is explicitly configured in all models */
    def isConfiguredALL(n: Node): Boolean = models.forall(_.isConfiguredNode(n))
    
    /** true iff node n is explicitly configured in at least one models */
    def isConfiguredEX(n: Node): Boolean = models.exists(_.isConfiguredNode(n))
    
    /** return the union of all offending flows **/
    def unionOffendingEndges(graph: NetGraph): List[(Node, Node)] = {
      def iterModels(ms: List[NetworkModelAbstract]): List[(Node,Node)] = {
        if (ms.isEmpty) 
          List()
        else {
          {
            if (ms.head.eval(graph)) List() else {
              if (ms.head.verify_globals(graph)){
                ms.head.offending_flows(graph).flatten
              }
             else{
                util.WarningPrinter.emit_warning("asking for offending flows for "+
                    "`"+ms.head.description+"' but verify_globals failed")
               List()
             }
            }
          } union iterModels(ms.tail)
        }
      }
      iterModels(models).distinct
    }
      
      /** return a list of models this flow violates */
      def violatesModels(e: (Node, Node), graph: NetGraph): List[NetworkModelAbstract] = {
        assert(graph.edges.contains(e))
        // flatten is important to check if ANY offending flow contains e
        //println(models.map(m => m.offending_flows(graph).flatten.contains(e)))
        models.filter(m => m.offending_flows(graph).flatten.contains(e))
      }
      
      def shortToString: String =
        models.map(m => "["+m.model_type+":"+m.description+"]").mkString(", ")
      
  }
}



