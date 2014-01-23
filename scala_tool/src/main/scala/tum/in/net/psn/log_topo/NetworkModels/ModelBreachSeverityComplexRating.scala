package tum.in.net.psn.log_topo.NetworkModels

import tum.in.net.psn.log_topo.HOLequal_String._
import NetworkModelList._


/**
 * EXPERIMENTAL
 */

object ModelBreachSeverityRating {
  
  abstract sealed trait BackflowRating
  case object BackflowOk extends BackflowRating
  case class BackflowNotOk(cause: Set[NetworkModelAbstract]) extends BackflowRating{
    override def toString(): String = "BackflowNotOk("+cause.toList.shortToString+")"
  }
	
  
  sealed case class InvalidFlowRating(violates: Set[NetworkModelAbstract], backflowRating: BackflowRating){
    override def toString(): String = "InvalidFlowRating(violates: "+violates.toList.shortToString+", "+
    		"backflowRating: "+backflowRating+")"
  }
  
  
  /**
   * get the breach severity rating, which is a parameter of NetworkModel
   */
  protected def get_model_breach_severity(m: NetworkModelAbstract): Int = m match {
    case mm: NetworkModel[_, _] => mm.model_breach_severity
    case _ => throw new RuntimeException("Unkown type "+m)
  }
  
  
  def simple_rating(models: List[NetworkModelAbstract], graph: NetGraph): Int =
  {
	  if (models.allValid(graph)) 0 else models.breach_severity_rating(graph)
  }
  
  /**
   * looks kind of wtf, but seems good for the eads cabin scenario
   */
  
  /**
   * f: illegal flow to rate
   * m: model to rate flow in 
   * graphValid: graph valid according to m, of course without f
   * models: all models
   * graph: actual graph
   */
  protected def complex_rate_one_flow_BackflowRating(f: (Node, Node),
      m: NetworkModelAbstract,
      graphValid: NetGraph,
      models: List[NetworkModelAbstract], 
      graph: NetGraph): BackflowRating = 
  {
    require(m.eval(graphValid))
    require(!graphValid.edges.contains(f))
    require(!m.eval(graph))
    require(graph.edges.contains(f))
    require(m.offending_flows(graph).flatten.contains(f))
    
    /**
     * returns BackflowOk if in all other models :
     * 	either model with backflow is valid or model is invalid but not because of backflow
     * This means, no other model has problems (apart from direction) with this flow
     */
    def validOppositeDirectionALL(f: (Node, Node)): BackflowRating = {
	    assert(!m.eval(graphValid.add_edge(f._1, f._2)), "model must be invalid with this flow")
	    
	    val f_back = (f._2, f._1) // backflow
	    val g_valid_back = graphValid.add_edge(f._2, f._1) // valid graph +  backflow
	    val g_back = graph.delete_edge(f._1, f._2).add_edge(f._2, f._1) // graph with reversed flow
	    
	    assert(g_back.edges.contains(f_back))
	    
	    /* list of models which have a problem with f_back */
	    val cause = models.filter{m =>
	      if(m.eval(g_back)){
	        //println("model valid with backflow: ["+m.model_type+":"+m.description+"]")
	        false
	      }else if (m.offending_flows(g_back).flatten.contains(f_back)) {
	        //println("backflow NOT ok with: ["+m.model_type+":"+m.description+"]")
	        true
	      }else {
	        //println("model invalid but not due to backflow: ["+m.model_type+":"+m.description+"]")
	        false
	      }
	    }
	    
	    if (cause.isEmpty)
	      BackflowOk
	    else
	      BackflowNotOk(cause.toSet)  
	  }
	  
    validOppositeDirectionALL(f)
  }
  
  protected def complex_rate_one_model_BackflowRating(m: NetworkModelAbstract,
      models: List[NetworkModelAbstract], 
      graph: NetGraph, 
      errorStream: java.io.PrintStream = Console.err): Map[(Node, Node), BackflowRating] = 
  {
    require(models contains m)
    
    if (m.eval(graph)) return Map()
    
    val illegal_flows_all: List[List[(Node,Node)]] = m.offending_flows(graph, errorStream)
	  assert(illegal_flows_all.length > 0)
	  assert(illegal_flows_all.length == 1, "offending flows must be uniquely defined. Model: "+m.model_type+" -- "+m.description)
	  
	  // length of longest illegal flow set
	  val num_illegal = illegal_flows_all.map(_.length).foldLeft(0)(_ max _)
	  assert(num_illegal > 0)
	  
	  // select first illegal flow with max size
	  val illegal_flows: List[(Node,Node)] = illegal_flows_all.filter(f => f.length == num_illegal).head
	  
	  val graphValid = NetGraph(graph.nodes, graph.edges.diff(illegal_flows))
	  assert(m.eval(graphValid), "graph without offending edges must be valid")
	  assert((graphValid.edges.toSet union illegal_flows.toSet) == graph.edges.toSet)
	  
	  
    val simpleMetric = m.model_breach_severity_rating(graph, errorStream)
    
	  var resultMap = Map[(Node, Node), BackflowRating]()
	  for (f: (Node, Node) <- illegal_flows){
	    assert(resultMap.get(f) == None)
	    resultMap = resultMap.updated(f, complex_rate_one_flow_BackflowRating(f, m, graphValid, models, graph))
	  }
	  
    resultMap
  }
  
  def printModelBreachRating(models: List[NetworkModelAbstract]): Unit = {
	  models.foreach(m => println("Model "+m.description+"  breach rating: "+get_model_breach_severity(m)))
  }
  
  def complex_rating(graph: NetGraph, models: List[NetworkModelAbstract],
      errorStream: java.io.PrintStream = Console.err): ModelBreachSeverityRatingResult =
  {
	  val resultModelMaps: List[Map[(Node, Node), BackflowRating]] = 
	    for (m <- models) yield complex_rate_one_model_BackflowRating(m, models, graph, errorStream)
    
	  /** calculate union of a list of maps to yield a single map **/
	  def unionResultMap(r: List[Map[(Node, Node), BackflowRating]]): Map[(Node, Node), BackflowRating] = 
	    r match {
  	    case Nil => Map()
  	    case rm::rms => 
  	      val resultMap = unionResultMap(rms)
  	      def updateResultMap(
  	          entries: List[((Node, Node), BackflowRating)],
  	          acc: Map[(Node, Node), BackflowRating]): 
  	          	Map[(Node, Node), BackflowRating] =
  	        entries match {
  	        case Nil => acc
  	        case e::es => 
  	          assert(acc.get(e._1) == None || acc(e._1) == e._2)
  	          updateResultMap(es, acc.updated(e._1, e._2))
  	      }
  	      updateResultMap(rm.toList, resultMap)
	  }
	  
	  val resultMapBackflow: Map[(Node, Node), BackflowRating] = unionResultMap(resultModelMaps)
	  
	  
	  assert(resultMapBackflow.keySet == models.unionOffendingEndges(graph).toSet, "set of offending edges is complete. "+
	        "maybe a not unique model? "+
	        "\nmissing: "+ models.unionOffendingEndges(graph).toSet.diff(resultMapBackflow.keySet)+
	        "\nfalse: "+resultMapBackflow.keySet.diff(models.unionOffendingEndges(graph).toSet))
	  
	  
	  val resultMap: Map[(Node, Node), InvalidFlowRating] = Map() ++ { 
	    for (e <- resultMapBackflow.keysIterator) yield 
	    	(e, InvalidFlowRating(models.violatesModels(e, graph).toSet, resultMapBackflow(e)))
	    }
	  
	  assert(resultMap.values.forall(v => ! v.violates.isEmpty), "invalid flow must violate model")
	  
	  assert(models.unionOffendingEndges(graph).isEmpty || resultMap.size > 0)
	  
	  //assert debug
//	  resultMap.foreach(v => v._2.backflowRating match {
//	    case BackflowOk => if(v._2.violates.size != 1)
//	      System.err.println("BackflowOk v._2.violates.size != 1 "+v)
//	    case BackflowNotOk(cause) => if(!(cause.size >= 1 && v._2.violates.size >= 1))
//	      System.err.println("BackflowNotOk("+cause+") "+"!(cause.size >= 1 && v._2.violates.size >= 1) " +v)
//	  })
	  assert(resultMap.values.forall(v => v.backflowRating match {
	    case BackflowOk => v.violates.size >= 1
	    case BackflowNotOk(cause) => cause.size >= 1 && v.violates.size >= 1
	  }), "BackflowOk must only violate one flow")
	  
	  //println(resultMapBackflow.keys.toList.map(e => (e, models.violatesModels(e, graph))))
	  
	  
	  new ModelBreachSeverityRatingResult(resultMap)
	  
	}
  
  
  protected class ModelBreachSeverityRatingResult(val resultMap: Map[(Node, Node), InvalidFlowRating]){
    def _getResultMapString: String = resultMap.mkString("\n")
    def printResultMap(): Unit = println(_getResultMapString)
    
    def getRating: Int = {
      var breach_rating = 0
		  for (e <- resultMap.keys){
		    // toList!! resultMap(e).violates returns a SET
		    // without toList: map(m => get_model_breach_severity(m)) is a SET of Ints!!
		    // sum({1,1,1}) = 1
		    // sum([1,1,1]) = 1
		    breach_rating += resultMap(e).violates.toList.map(m => get_model_breach_severity(m)).sum
		  }
		  breach_rating
		  }
  }
}
