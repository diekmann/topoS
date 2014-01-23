package tum.in.net.netModelVisualizer

import tum.in.net.psn.log_topo.NetworkModels.{NetGraph, NetworkModelAbstract}
import scala.sys.process.stringSeqToProcess
import tum.in.net.StringNode._


/**
 * A changed GraphVizify class which is used to display the 
 * maximum topology diff
 * 
 * diff: edges in the maximum topology but not in some graph
 * graph: the maximum topology
 */
class GraphVizify_MaxTopoDiff(graph: NetGraph, models: List[NetworkModelAbstract], 
      __visual_extra_in: Map[String, List[Node]],
      diff: List[(Node, Node)]) 
      extends GraphVizify(graph, models, __visual_extra_in) {

  
  import tum.in.net.psn.log_topo.NetworkModels.NetworkModelList._

  assert(diff.toSet.subsetOf(graph.edges.toSet))
  assert(models.allValid(graph), "maximum topology is valid")
  
  override protected def addEdge_generateLabel(e1: Node, e2: Node): List[String] = {
    val label = super.addEdge_generateLabel(e1, e2)
    
    def additional(e1: Node, e2: Node) = List("style=dotted", "color=\"#FF8822\"")
    
    if (diff.contains((e1,e2))) 
      label ++ additional(e1,e2)
    else{
      label
    }
  }
  
}
