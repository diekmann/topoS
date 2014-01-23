package tum.in.net.experimental

import tum.in.net.psn.log_topo.JSONLoader
import tum.in.net.psn.log_topo.NetworkModels.ModelBreachSeverityRating
import tum.in.net.psn.log_topo.NetworkModels.NetGraph

/**
 * Generate a configuration for a network intrusion detection system
 */
object NIDSConfig {

  def breachRating(): Unit = {
    import tum.in.net.psn.log_topo.NetworkModels.NetworkModelAbstract
    import tum.in.net.psn.log_topo.NetworkModels.NetworkModelList._
    val models: List[NetworkModelAbstract] = new JSONLoader(verbose=false).load_models
    val G = JSONLoader.load_graph

    val rating = if (models.allValid(G)) 0 else models.breach_severity_rating(G)
    println("Simple Security Breach Rating: "+rating)

    println()

    ModelBreachSeverityRating.printModelBreachRating(models)


    val complexrating = ModelBreachSeverityRating.complex_rating(G, models)

    println("Output: ")
    println("(from,to) -> InvalidFlowRating(violates: listOfSecurityRequirements, backflowRating: X)")
    println("backflowRating is set to BackflowOk if this flow (from, to) is an allowed answer to an request from (to, from)")

    complexrating.printResultMap()
    println("complex Security Breach Rating: "+complexrating.getRating)
  }


  def precalculateBreachRating(): Unit = {
    import tum.in.net.psn.log_topo.NetworkModels.NetworkModelAbstract
    import tum.in.net.psn.log_topo.NetworkModels.NetworkModelList._

    val models: List[NetworkModelAbstract] = new JSONLoader(verbose=false).load_models
    val G = JSONLoader.load_graph

    println("experimental:")
    if(models.allValid(G)){ 
      println("WARNING: the following rating only work on unambiguous local models!!!!")
      println("It pre-calculates the breach rating for all flows not in the graph")
  
      import tum.in.net.psn.log_topo.TopologyGeneration.{fullyConnected}
      val allEdges = fullyConnected(G)
      val testEdges = allEdges.diff(G.edges) //the edges not in G

      var rating_map: Map[(String, String), Int] = Map()

      //for all edges NOT IN G, generate rating
      val str = for(e <- testEdges) yield {
        val Gtest = G.add_edge(e._1, e._2)
        val complexrating = ModelBreachSeverityRating.complex_rating(Gtest, models) //use println side effects
        //detailed output
        //complexrating.printResultMap()
        //println(complexrating.getRating)

        assert(complexrating.resultMap.size <= 1, "at most one flow is invalid") //breaks with ambiguous models
        if(complexrating.resultMap.size == 1){
          assert(complexrating.resultMap.keys.head == e, "invalid edge is the one we test. "+
                "expected: "+e+" got: "+complexrating.resultMap.keys.head) // breaks at non-local models
          assert(complexrating.getRating == models.breach_severity_rating(Gtest), "complex and simple rating is equal in this case "+
              "(for flow: "+e+")"+". "+
                "expected: "+models.breach_severity_rating(Gtest)+" got: "+complexrating.getRating+
                "\nDebug: "+complexrating._getResultMapString)
          rating_map += (complexrating.resultMap.keys.head -> complexrating.getRating)
          "\""+complexrating.resultMap.keys.head+"\": "+complexrating.getRating
        }else{
          rating_map += (e -> 0)
          "\""+e+"\": 0"
        }
      }

      //for all edges IN G, generate rating
      assert(models.allValid(G), "all security requirements must be fulfilled to " +
          "rate all edges in the graph with zero")
      val strG = for(e <- G.edges) yield { rating_map += (e -> 0); "\""+e+"\": 0" }

      println("{\n"+(strG ++ str).mkString(",\n")+"\n}")


      if(true){
        println("trying to visualize ...")

        val visual_extra = new JSONLoader(verbose=false).load_visual_extra()
        import tum.in.net.netModelVisualizer.GraphVizify_IDS
        val max_rating = rating_map.values.max
        val visualize_map = rating_map

        import tum.in.net.psn.log_topo.TopologyGeneration.{fullyConnected}

        // pass a fully connectd graph to visualization to display all edges
        val Gdraw = NetGraph(G.nodes, fullyConnected(G))

            // only print most offedning
            //val drawEdges = fullyConnected(G).filter(e => G.edges.contains(e) || visualize_map(e) > max_rating/2)
            //val Gdraw = NetGraph(G.nodes, drawEdges)

        val visual = new GraphVizify_IDS(Gdraw, models, visual_extra, visualize_map)
        visual.displayGraphCirco(true)

        println("Accumulated evilness statistics:")
        val badness_list : List[(String, Int)]= for(n <- G.nodes) yield {
          val badness = rating_map.filter(eev => eev._1._1 == n).values.sum
              //println("  "+n+": "+badness)
              (n -> badness)
        }

        val sorted_badness = badness_list.sortWith((a,b) => a._2 <= b._2).reverse

        println(sorted_badness.map(nb => "  "+nb._1+": "+nb._2).mkString("\n"))

        println("pyplot compatible input:")
        println("("+sorted_badness.map("'"+_._1+"'").mkString(", ")+")")
        println("("+sorted_badness.map(_._2).mkString(", ")+")")
      }
    }else{
      println("only for valid graph")
    }
  }
}