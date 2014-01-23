package tum.in.net.psn.log_topo


import NetworkModels.{NetGraph, NetworkModelAbstract}
import NetworkModels.JSONParser
import org.scalatest.FlatSpec

class BenchmarkSuite extends FlatSpec{
  
	
	def generateRandomCfg(model: String, nodes: Array[String], size: Int): String = {
	  require(nodes.length >= size)
	  
	  def json_cfg(model_params:String) = """{"model_type": """"+model+"""",
			 "model_description": "Random Test config", 
	     "model_breach_severity": 10,
			 "model_params":"""+model_params+"""
			}"""
		
		/**
		 * create random _unused_ integer
		 */
	  class cfgInt() {
	    val rand = new scala.util.Random()
    	var used: Set[Int] = Set() // used randoms
    	def freshInt(): Int = {
    	  val rtmp = rand.nextInt(nodes.length)
    	  if (used contains rtmp)
    	    freshInt()
    	  else {
    	    used = used + rtmp
    	    rtmp
    	  }
    	}
	  }
	  
	  def cfg_BLPbasic: String = {
	    val cfgint = new cfgInt()
	    val nP = for(_ <- 0 until size) yield {
	    	val n = nodes(cfgint.freshInt())
	    	"""{"node":""""+n+"""", "privacy":"""+scala.util.Random.nextInt(100)+"""}"""
	    }
	    """{
	    "node_properties": ["""+"\n\t"+nP.mkString(",\n\t")+"""], 
			    "global_properties":null
			    }"""
	  }
	  
	  def cfg_BLPtrusted: String = {
	    val cfgint = new cfgInt()
	    val nP = for(_ <- 0 until size) yield {
	    	val n = nodes(cfgint.freshInt())
	    	val trust = if(scala.util.Random.nextBoolean())
	    	  	""", "trusted": true"""
	    		else
	    		  ""
	    	"""{"node":""""+n+"""", "privacy":"""+scala.util.Random.nextInt(100)+trust+"""}"""
	    }
	    """{
	    "node_properties": ["""+"\n\t"+nP.mkString(",\n\t")+"""], 
			    "global_properties":null
			    }"""
	  }
	  
	  def cfg_Subnets: String = {
	    val cfgint = new cfgInt()
	    val nP = for(_ <- 0 until size) yield {
	    	val n = nodes(cfgint.freshInt())
	    	val m_type = if(scala.util.Random.nextBoolean())
	    	  	"Subnet"
	    		else
	    		  "BorderRouter"
	    	"""{"node":""""+n+"""", "member_type": """"+m_type+
	    			"""", "member": """+scala.util.Random.nextInt(100)+"""}"""
	    }
	    """{
	    "node_properties": ["""+"\n\t"+nP.mkString(",\n\t")+"""], 
			    "global_properties":null
			    }"""
	  }
	  
	  def cfg_SecurityGatewayExtended: String = {
	    val cfgint = new cfgInt()
	    val nP = for(_ <- 0 until size) yield {
	    	val n = nodes(cfgint.freshInt())
	    	val members = Array("SecurityGatewayIN", "DomainMember", "AccessibleMember", "SecurityGateway")
	    	val m_type = members(scala.util.Random.nextInt(members.length))
	    	
	    	"""{"node":""""+n+"""", "member_type": """"+m_type+""""}"""
	    }
	    """{
	    "node_properties": ["""+"\n\t"+nP.mkString(",\n\t")+"""], 
			    "global_properties":null
			    }"""
	  }
	  
	  val ret:String = model match {
	    case "BLPbasic" => cfg_BLPbasic
	    case "BLPtrusted" => cfg_BLPtrusted
	    case "Subnets" => cfg_Subnets
	    case "SecurityGatewayExtended" => cfg_SecurityGatewayExtended
	  }
	  
	  json_cfg(ret)
	}
	
	//val testedModels: scala.collection.mutable.Set[String] = scala.collection.mutable.Set()
	
	//println(generateRandomCfg("SecurityGatewayExtended", Array("1","2","3","4"), 2))
	
	val cfg_models = List("BLPbasic", "BLPtrusted", "Subnets", "SecurityGatewayExtended")
	
	
	def generateRandomGraph(nodes: Array[String], num_edges: Int): String = {
	  /**
		 * create random _unused_ integer pair
		 */
	  class cfgInt() {
	    val rand = new scala.util.Random()
    	var used: Set[(Int, Int)] = Set() // used randoms
    	def freshInt(): (Int, Int) = {
    	  val rtmp1 = rand.nextInt(nodes.length)
    	  val rtmp2 = rand.nextInt(nodes.length)
    	  val rtmp = (rtmp1, rtmp2)
    	  if (used contains rtmp)
    	    freshInt()
    	  else {
    	    used = used + rtmp
    	    rtmp
    	  }
    	}
	  }
	  
	  val cfgint = new cfgInt()
	  val edges = for(_ <- 0 until num_edges) yield {
	    val (e1, e2) = cfgint.freshInt()
	    """{"e1": """"+nodes(e1)+"""", "e2": """"+nodes(e2)+""""},"""
	  }
	  """{
"nodes": [
	  """+nodes.map("\""+_+"\"").mkString(",\n")+"""], 
"edges": [
	  """+edges.mkString(",\n")+""" ]
}
"""
	}
	
	"Benchmark" must "load all randomly generated configs" in {
	  for(m <- cfg_models){
		  val json = generateRandomCfg(m, Array("1","2","3","4"), 2)
		  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
		  assert(nm.model_type === m)
	  }
	}
	
	it must "load generated graph" in {
	  val json = generateRandomGraph(Array("1","2","3","4"), 7)
	  try{
		val Gparsed = new NetworkModels.JSONParser.GraphParser(json)
	    val graph: NetGraph = Gparsed.G
	  }catch{
	    case e: java.lang.StackOverflowError =>
	      println("java.lang.StackOverflowError when genertaing graph")
	      throw e;
	  }
	  //println(graph)
	}
	
	var bench_graph: NetGraph = null
	var bench_models: List[NetworkModelAbstract] = null
	
	it must "initialize benchmark" in {
	  
	  //// CHANGE ME
	  val num_nodes = 100
	  
	  val num_edges = (num_nodes*(num_nodes-1))/4
	  val num_models = 100 //num_nodes/10
	  
	  val start = System.currentTimeMillis
	  
	  val nodes: Array[String] = (1 until (num_nodes+1)).map("n"+_).toArray
	  
	  {
	    println("initialize graph: generating graph")
		  assert(nodes.length === num_nodes)
		  val graph_json = generateRandomGraph(nodes, num_edges)
		  
		  println("done")
		  println("parsing graph")
		  try{
		    val Gparsed = new NetworkModels.JSONParser.GraphParser(graph_json)
			val graph: NetGraph = Gparsed.G
			bench_graph = graph
		  }catch{
		    case e: java.lang.StackOverflowError =>
		      println("java.lang.StackOverflowError when genertaing graph")
		      throw e;
		  }
		  println("done")
	  }
		
		assert(!(bench_graph eq null))
		assert(bench_graph.nodes.length === num_nodes)
		assert(bench_graph.edges.length === num_edges)
	  
	  
	  println("generating models")
	  val l: Seq[NetworkModelAbstract] = for(_ <- 0 until num_models) yield {
	    print(".")
	    val model: String = cfg_models(scala.util.Random.nextInt(cfg_models.length))
	    val json = generateRandomCfg(model, nodes, 2)
	  	val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  	nm
	  }
		
		println()
		println("done")
		
		bench_models = l.toList
		assert(!(bench_models eq null))
		assert(bench_models.length === num_models)
		assert(bench_models.forall(m => nodes.exists(n => m.isConfiguredNode(n))))
		
		val end = System.currentTimeMillis-start
		
		println("Benchmark setup statistics")
		println(" graph")
		println("  num nodes: "+num_nodes)
		println("  num edges: "+num_edges)
		println(" models")
		println("  num models: "+num_models)
		println("  model types: "+bench_models.map(m => m.model_type).groupBy(identity).mapValues(_.size))
		println("time to init: "+end+" ms")
	}
	
	it must "eval all" in {
		import NetworkModels.NetworkModelList._
		
	  val start = System.currentTimeMillis
	  
		val v = bench_models.map(m => m.eval(bench_graph))
	  
		val end = System.currentTimeMillis-start
		
		println("stats")
		println(" evaluating all models: "+end+" ms ("+(end*1.0)/1000+" s)")
		println(" all valid: "+bench_models.allValid(bench_graph))
		
		
		println(" num valid: "+v.filter(m => m).size)
		println(" num invalid: "+v.filter(m => ! m).size)
	}
	
	it must "offending flows all" in {
		import NetworkModels.NetworkModelList._
		
	  val start = System.currentTimeMillis
	  
	  val offedning = bench_models.map(m => m.offending_flows(bench_graph))
	  
		val end = System.currentTimeMillis-start
		
		println("stats")
		println(" calculating offending flows for all models: "+end+" ms ("+(end*1.0)/1000+" s)")
		println(" num offending flows: "+offedning.flatten.toList.flatten.toList.length)
		//println(offedning.flatten.toList.flatten.toList)
	}
	
	it must "generate topology" in {
		import NetworkModels.NetworkModelList._
		
		val start_init = System.currentTimeMillis
		
		    val topo = new TopologyGenerator(bench_graph, bench_models)
			val end_init = System.currentTimeMillis
			val result = topo.tryCreateTopology
		
		val end = System.currentTimeMillis
		
		val get_start = System.currentTimeMillis
			assert(topo.isMaximum)
			val result_graph = topo.getCreatedGraph
		val get_end = System.currentTimeMillis
		
		val total = get_end - start_init
		val init = end - start_init
		val get = get_end - get_start
		
		println("stats")
		println(" generate topology total: "+total+" ms ("+(total*1.0)/1000+" s)")
		println(" generate topology init: "+init+" ms ("+(init*1.0)/1000+" s)")
		println(" generate topology getresult: "+get+" ms ("+(get*1.0)/1000+" s)")
		println("   flows: "+result_graph.edges.size)
		//println(offedning.flatten.toList.flatten.toList)
	  
	  
	}
	

}


