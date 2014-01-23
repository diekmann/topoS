package tum.in.net.psn.log_topo

import org.scalatest.FlatSpec

import NetworkModels.{NetGraph, NetworkModelAbstract}
import NetworkModels.NetworkModelList._
import tum.in.net.StringNode._

class FlowMatrixAndTopologySuite extends FlatSpec {
  
  val n1 = "n1"
  val n2 = "n2"
  val n3 = "n3"
  val graph = NetGraph(List(n1, n2, n3), List((n1, n2), (n2, n3), (n3, n3)))
	
	"FlowMatrix" should "be valid" in {
	  val matrix = FlowMatrix.create(graph)
	  // to -->
	  // from \/
	  //   1 2 3
	  // 1 . X .
	  // 2 . . X
	  // 3 . . X 
	  
	  assert(matrix.size == 3)
	  assert(matrix.forall(j => j.size == 3))
	  
	  // the matrix entries that must be valid
	  val validPos = List((0,1), (1,2), (2,2))
	  
	  for(i <- 0 until matrix.size; j <- 0 until matrix(i).size){
	    if (validPos.contains(i, j)){
	      assert(matrix(i)(j) == true)
	    } else {
	      assert(matrix(i)(j) == false)
	    }
	  }
	  
	}
	
	
	"FullyConnected" must "be fully connected" in {
	  val fullEdges: List[(Node, Node)] = TopologyGeneration.fullyConnected(graph)
	  assert(fullEdges.distinct == fullEdges)
	  assert(fullEdges.contains(n1,n1))
	  assert(fullEdges.size == math.pow(graph.edges.size, 2))
	}
	
	"GenerateTopology" must "return fully connected on no security requirements" in {
	  
	  val generator = new TopologyGenerator(graph, List())
	  assert(generator.isMaximum)
	  val maxGraph: NetGraph = generator.getCreatedGraph
	  assert(generator.isMaximum)
	  assert(maxGraph.edges == TopologyGeneration.fullyConnected(graph))
	  
	}

	  
}