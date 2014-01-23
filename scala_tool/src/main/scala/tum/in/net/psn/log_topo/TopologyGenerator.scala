package tum.in.net.psn.log_topo


import NetworkModels.{NetGraph, NetworkModelAbstract}
import NetworkModels.NetworkModelList._
import scala.collection.immutable
import scala.collection.mutable
import HOLequal_String._
import scala.compat.Platform


object TopologyGeneration{

  /**
   * return edges of fully connected graph
   */
  def fullyConnected(graph: NetGraph): List[(Node, Node)] = {
    def connectToAll_tailrec(n: Node, ns: List[Node], acc: List[(Node, Node)]): List[(Node, Node)] = 
      ns match {
        case Nil => acc
        case x::xs => connectToAll_tailrec(n, xs, (n, x)::acc)
      }
    def connectToAll(n: Node, ns: List[Node]): List[(Node, Node)] = connectToAll_tailrec(n, ns, List())
    
    def iterFullyConnected(n: List[Node]): List[(Node, Node)] = {
      val size_nodes = graph.nodes.size
      val size_result = size_nodes * size_nodes
      n match {
        case Nil => List()
        case n::ns => 
            //note: constructing a List[List] and flatten afterwards is slower
            connectToAll(n, graph.nodes) ::: iterFullyConnected(ns)
      }
    }
    val result = iterFullyConnected(graph.nodes)
    assert(result.length == graph.nodes.length * graph.nodes.length)
    result
  }
  
  /** 
   * Return a list of other flows which alone are accepted by all models.
   * Graph must be valid or otherwise list would be empty
   * brute force!
   */
  def getOtherAllowedFlows(graph: NetGraph, models: List[NetworkModelAbstract], 
      dropReflexive: Boolean =false): List[(Node, Node)] = {
    require(models.allValid(graph))
    
    val allEdges = fullyConnected(graph)
    
    // possible edges to test
    val candidateEdges = allEdges.diff(graph.edges)
    
    val allowedEdges = candidateEdges.filter{e =>
        val testGraph = graph.add_edge(e._1, e._2)
        models.allValid(testGraph)
      }
    
    assert(allowedEdges.forall(e => !graph.edges.contains(e)))
    
    if (!dropReflexive)
      allowedEdges
    else
      allowedEdges.filterNot(e => e._1 == e._2)
    }
  
  }
  
  
  class TopologyGenerator(graph: NetGraph, models: List[NetworkModelAbstract], init: Boolean=true) {
    
  protected var stackOverflowCount = 0
  //suppress stack overflow warnings
  protected val nullErrStream = new java.io.PrintStream(new java.io.OutputStream() {
       override def write(b: Int): Unit = {}
    })
  
  
  protected var varEdges = if (init) TopologyGeneration.fullyConnected(graph) else graph.edges
  
  if (init) {
    assert(graph.nodes.size * graph.nodes.size == varEdges.size)
    assert(varEdges.distinct == varEdges)
  } else {
    assert(graph.edges == varEdges)
  }
  
  protected def varGraph = NetGraph(graph.nodes, varEdges)
  
  protected def allValid: Boolean = models.allValid(varGraph)
  
  /**
   * the models which have a linear time offending flows function
   */
  protected val safeAndFastModels = List("BLPbasic", "Subnets", "DomainHierarchy", "SubnetsInGW")
  
  /**
   * Heuristic:
   * split graph if it has not connected components
   */
  protected def partition: (NetGraph, NetGraph) = {
    def BFS(G: NetGraph, v: Node): List[(Node,Node)] = {
      var reachable = scala.collection.mutable.ListBuffer[(Node,Node)]()
      val Q = new mutable.Queue[Node]
      Q.enqueue(v)
      val marks = mutable.Set[Node]()
      marks.add(v)
      while (!Q.isEmpty){
        val t = Q.dequeue
        //  if t is what we are looking for:
        //reachable.append(t)
        
        val adjacent: List[(Node, Node)] = G.edges.filter(x => x._1 == t || x._2 == t)
        reachable ++= adjacent
        for (e <- adjacent) {
          // G.opposite returns adjacent vertex 
          val o: Node = e match {
            case (e1,e2) if e2==t => e1
            case (e1,e2) if e1==t => e2
          }
          if (!marks.contains(o)){
            marks.add(o)
            Q.enqueue(o)
          }
        }
      }
      reachable.toList
    }
    //TODO not distinct
    val connectedComponent = BFS(varGraph, varEdges.head._1).distinct
    assert(connectedComponent == connectedComponent.distinct)
    
    val connectedComponentNodes = (connectedComponent.map(_._1) ::: connectedComponent.map(_._2)).distinct
    
    val g1 = NetGraph(connectedComponentNodes, connectedComponent)
    val g2 = NetGraph(varGraph.nodes.diff(connectedComponentNodes), varEdges.diff(connectedComponent))
    
    assert( (g1.nodes ::: g2.nodes).toSet == graph.nodes.toSet )
    assert( (g1.edges ::: g2.edges).toSet == varGraph.edges.toSet )
    
    //(g1, g2)
    (NetGraph(graph.nodes, g1.edges), NetGraph(graph.nodes, g2.edges))
  }
    
  
  protected var partitionCount = 0
  protected def partitonIntoSubgraphs: Boolean = {
    val (g1, g2) = partition
    
    if(g1.edges.isEmpty) return false
    if(g2.edges.isEmpty) return false
    
    
    partitionCount += 1
    
    val t1 = new TopologyGenerator(g1, models, init=false)
    val t2 = new TopologyGenerator(g2, models, init=false)
    
    t1.tryCreateTopology
    
    t2.tryCreateTopology
    
    val oldVarEdgesSize = varEdges.size
    varEdges = t1.varEdges ::: t2.varEdges
    val newVarEdgesSize = varEdges.size
    assert(oldVarEdgesSize >= newVarEdgesSize)
    
    ambiguousChoices += t1.ambiguousChoices
    ambiguousChoices += t2.ambiguousChoices
    partitionCount += t1.partitionCount
    partitionCount += t2.partitionCount
    stackOverflowCount += t1.stackOverflowCount
    stackOverflowCount += t2.stackOverflowCount
    
    oldVarEdgesSize > newVarEdgesSize
  }
  
  protected def removeSafeDefiniteOffendingEdges(m: NetworkModelAbstract): Boolean = {
    if (safeAndFastModels.contains(m.model_type) && !m.eval(varGraph)) m.offending_flows(varGraph) match {
      case List(f) => varEdges = varEdges.diff(f); true
      case Nil => println("it looks like there is a model which cannot be validated"); false
      case _ => false
    } else false
  }
  
  protected def removeUnSafeDefiniteOffendingEdges(m: NetworkModelAbstract): Boolean = {
    if (!m.eval(varGraph)) m.offending_flows(varGraph, nullErrStream) match {
      case List(f) => varEdges = varEdges.diff(f); true
      case Nil => println("it looks like there is a model which cannot be validated"); false
      case _ => false
    } else false
  }
  
  
  protected var ambiguousChoices = 0
  protected def removeUnSafeOffendingEdges(m: NetworkModelAbstract): Boolean = {
    if (!m.eval(varGraph)) m.offending_flows(varGraph, nullErrStream) match {
      case f::fs => {
        varEdges = varEdges.diff(f)
        println("multiple choices, picking "+f+"to remove")
        ambiguousChoices += 1
        true
      }
      case Nil => println("it looks like there is a model which cannot be validated"); false
    } else false
  }
  
  /** but topology will not be maximal then! **/
  protected def removeReflexive: Boolean = {
    val oldVarEdgesSize = varEdges.size
    
    varEdges = varEdges.filterNot(x => x._1 == x._2)
    
    val newVarEdgesSize = varEdges.size
    assert(oldVarEdgesSize >= newVarEdgesSize)
    oldVarEdgesSize > newVarEdgesSize
  }
  
  
  def tryCreateTopology: Unit = {
    var changes = false
    
    for (m <- models){
      changes |= removeSafeDefiniteOffendingEdges(m)
    }
    
    if(allValid) return
    if (changes) tryCreateTopology
    
    for (m <- models){
      try {
        changes |= removeUnSafeDefiniteOffendingEdges(m)
      } catch {
          case e:StackOverflowError => stackOverflowCount +=1
      }
    }
    
    if(allValid) return
    if (changes) tryCreateTopology
    
    println("removing reflexive flows")
    changes = removeReflexive
    println("flows: "+varEdges.size); 
    
    if(allValid) return
    if (changes) tryCreateTopology
    
    println("trying ambiguous models")
    
    for (m <- models){
      try {
        changes |= removeUnSafeOffendingEdges(m)
      } catch {
          case e:StackOverflowError => stackOverflowCount +=1
      }
    }
    
    if(allValid) return
    if (changes) tryCreateTopology
    
    println("trying partitonIntoSubgraphs")
    println("flows: "+varEdges.size); 
    changes = partitonIntoSubgraphs
    println("flows: "+varEdges.size); 
    
    
    if(allValid) return
    if (changes) tryCreateTopology
    
    println ("!! ERROR !! Topology generation failed")
  }
  
  def stats: String = {
    "  made "+ambiguousChoices+" ambiguous choices"+"\n"+
    "  partitionioned "+partitionCount+" times"+"\n"+
    "  stackoverflows: "+stackOverflowCount+"\n"+
    "  maximum: "+isMaximum
  }
  
  def isMaximum: Boolean = {
    ambiguousChoices == 0 && partitionCount == 0
  }
  
  def getCreatedGraph() = varGraph
  
}
