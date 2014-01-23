package tum.in.net.psn.log_topo.NetworkModels.JSONParser

import net.liftweb.json
import net.liftweb.json.JsonParser.ParseException
import net.liftweb.json.MappingException
import tum.in.net.psn.log_topo.NetworkModels._
import GENERATED.{FiniteListGraph, Nat}
import GENERATED.FiniteListGraph.{list_graph_ext, List_graph_ext}
import GENERATED.NetworkModel_Interface.{
  networkModel_Params_ext, NetworkModel_Params_ext, model_global_properties}
import GENERATED.datatype_DomainHierarchy
import GENERATED.Lista.distinct
import tum.in.net.psn.log_topo.HOLequal_String._

/*** start parsing graph ***/
protected case class GraphEdgesJSONTemplate(e1: Node, e2: Node) {
	override def toString: String = "("+e1+", "+e2+")"
	def toTuple: (Node, Node) = (e1, e2)
}
protected case class NetGraphJSONTemplate(nodes: List[Node], edges: List[GraphEdgesJSONTemplate]){
	def toGraph_ext: list_graph_ext[Node, Unit] = List_graph_ext[Node, Unit](nodes, edges.map(e => e.toTuple), ())
}

class GraphParser(netgraph_string: String) {
	private final val parsed_graph = parse_JSON_graph(netgraph_string)
	private final val graph_ext = parsed_graph.toGraph_ext
	valid_graph(graph_ext)
	final val G: NetGraph = new NetGraph(graph_ext)

	def parse_JSON_graph(netgraph_string: String): NetGraphJSONTemplate = {
		implicit val formats = json.DefaultFormats
		val graph = try{
			val json_parsed = json.parse(netgraph_string)
			//println(json_parsed)
			try{
				val extracted = json_parsed.extract[NetGraphJSONTemplate]
				
				//println("Extracted graph:")
				//println("  nodes: "+extracted.nodes)
				//println("  edges: "+extracted.edges)

				def listNotNULL_iter(l: List[Any]):Boolean = {
					if (l.isEmpty) true
					else if (l.head == null) false
					else listNotNULL_iter(l.tail)
				}

				def edgeNotNULL_iter(l: List[GraphEdgesJSONTemplate]):Boolean = {
					if (l.isEmpty) true
					else if (l.head.e1 == null || l.head.e2 == null) false
					else edgeNotNULL_iter(l.tail)
				}

				if(!listNotNULL_iter(extracted.nodes)){
					println("Some node is null")
					throw new RuntimeException("Some node null in graph")
				}
				if(!listNotNULL_iter(extracted.edges)){
					println("Some edge is null")
					throw new RuntimeException("Some edge null in graph")
				}
				if(!edgeNotNULL_iter(extracted.edges)){
					println("Some edge label is null")
					throw new RuntimeException("Some edge label null")
				}
				extracted
			} catch {
			case e: MappingException => {
			  	println("Failed to parse graph")
					println(e)
					throw new RuntimeException(e)
				}
			}
		} catch {
		case e:ParseException => {println("Parsing Graph: Failed to parse. Illegal JSON?")
				println(e)
				throw new RuntimeException(e)
			}
		}
		graph
	}
	
	def valid_graph(G: list_graph_ext[Node, Unit]):Unit = {
		if(!GENERATED.FiniteListGraph.valid_list_graph(G)){
		  println("The supplied graph is semantically invalid. Debug:")
		  val dn = distinct(FiniteListGraph.nodesL(G))
		  val de = distinct(FiniteListGraph.edgesL(G))
		  println("  distinct nodes: "+dn)
		  println("  distinct edges: "+de)
		  if(!de) {
		    val notsdisitnct = for (e <- FiniteListGraph.edgesL(G) if FiniteListGraph.edgesL(G).diff(List(e)).contains(e))
		      yield e
		    println("duplicate edges: "+notsdisitnct.toSet)
		  }
		  if(dn && de){
		    println("  Some nodes must be listed in edges which do not occur in nodes!")
		    val notsenders = for ((e1, e2) <- FiniteListGraph.edgesL(G) if !FiniteListGraph.nodesL(G).contains(e1))
		      yield e1
		    val notreceivers = for ((e1, e2) <- FiniteListGraph.edgesL(G) if !FiniteListGraph.nodesL(G).contains(e2))
		      yield e2
		    println("illegal senders: "+notsenders+"\nillegal receivers: "+notreceivers)
		  }
		  throw new RuntimeException("invalid graph")
		}//else println("graph valid")
	}
	
	override def toString: String = "converted graph: "+graph_ext
}
/*** end parsing graph ***/


/*** start parsing visual_extra***/
protected case class NetGraphVisualExtraGroupedNodesJSONTemplate(group: String, members: List[Node]){
  def toTuple: (String, List[Node]) = (group, members)
}	
protected case class NetGraphVisualExtraJSONTemplate(grouped_nodes: List[NetGraphVisualExtraGroupedNodesJSONTemplate]){
	def toMap: Map[String, List[Node]] = grouped_nodes.map(n => n.toTuple).toMap
}
class VisualExtraParser(visual_extra_string: String) {
  final val visual_extra = parse_JSON_visual_extra().toMap
  
	protected def parse_JSON_visual_extra(): NetGraphVisualExtraJSONTemplate = {
		implicit val formats = json.DefaultFormats
		
		val result = try{
				val json_parsed = json.parse(visual_extra_string)
				val extracted = json_parsed.extract[NetGraphVisualExtraJSONTemplate]
				extracted
				} catch {
					case e: MappingException => {
					  	println("Failed to parse graph visual extra")
							println(e)
							throw new RuntimeException(e)
					}
					case e:ParseException => {
					  println("Parsing Graph: Failed to parse visual extra. Illegal JSON?")
						println(e)
						throw new RuntimeException(e)
					}
			}
		result
	}
}
/*** end parsing visual_extra ***/
