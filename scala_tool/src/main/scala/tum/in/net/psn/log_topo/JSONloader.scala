package tum.in.net.psn.log_topo


import NetworkModels.NetworkModelAbstract
import tum.in.net.StringNode._
import java.io.File

/**
 * Load models and graph from file
 */
class JSONLoader(verbose: Boolean = true) {
  
  protected def load_models_directory: List[java.io.File] = {
    import java.io.File
    val files = new File("./models")
    if (!files.isDirectory()){
      println("directory "+files+" not found. " +
          "Place all models as .json files in this directory in your current working directory")
      throw new java.io.FileNotFoundException(files.toString())
    }
    
    class MyFileFilter extends java.io.FilenameFilter
    {
      def accept(f: File, s: String): Boolean = {
        s.toLowerCase().endsWith( ".json")
      }
    }
    
    val retUnsorted = files.listFiles(new MyFileFilter).toList
    val ret = retUnsorted.sorted
    if (verbose) println("available models: "+ret)
    ret
  }

  protected def load_file_to_string(f: java.io.File): String = {
    val modelReader = scala.io.Source.fromFile(f)
    val model_string = try{ 
      modelReader.mkString
    } finally {
      modelReader.close()
    }
    model_string
  }

  def load_models : List[NetworkModelAbstract] = {
    val models: List[NetworkModelAbstract] = 
      load_models_directory.map{l : java.io.File =>
        val m: NetworkModelAbstract = 
        try{
          NetworkModels.JSONParser.new_model_from_JSONstring(load_file_to_string(l), verbose) 
        } catch {
          case e: RuntimeException =>
            println("RuntimeException when trying to load "+l)
            throw e
        }
        m
      }
    models
  }
  
  def load_graph: NetworkModels.NetGraph = {
    val graphReader = try {
      scala.io.Source.fromFile("graph.json")
    } catch {
    case e: java.io.FileNotFoundException => 
        println("expected a file graph.json in your current working directory")
        throw e
    }
    val netgraph_string =  try{ 
      graphReader.mkString
    } finally {
      graphReader.close()
    }
    val Gparsed = new NetworkModels.JSONParser.GraphParser(netgraph_string)
    Gparsed.G
  }
  
  def load_visual_extra(): Map[String, List[Node]] = {
    val visualReader = try {
      scala.io.Source.fromFile("visual_extra.json")
    } catch {
    case e: java.io.FileNotFoundException => 
      println("expected a file visual_extra.json in your current working directory")
      throw e
    }
    val json_string =  try{ 
      visualReader.mkString
    } finally {
      visualReader.close()
    }
    val visual_parsed = new NetworkModels.JSONParser.VisualExtraParser(json_string)
    visual_parsed.visual_extra
  }
  
}

/**
 * Companion object. Convenient methods to load models and graph from files in your
 * current working directory.
 * @author corny
 *
 */
object JSONLoader {
  /**
   * parse all *.json files in ./models directory
   */
  def load_models : List[NetworkModelAbstract] = new JSONLoader().load_models
  
  /**
   * load ./graph.json
   */
  def load_graph: NetworkModels.NetGraph = new JSONLoader().load_graph
  
  /**
   * load ./visual_extra.json
   */
  def load_visual_extra(): Map[String, List[Node]] = new JSONLoader().load_visual_extra()
  
  
  def graph_to_json_str(g: NetworkModels.NetGraph):String = {
    import net.liftweb.json
    import net.liftweb.json.JsonDSL._
    
    val nodes = json.pretty(json.render(g.nodes))
    val edges = json.pretty(json.render(g.edges.map(n => ("e1", n._1) ~ ("e2", n._2))))
    val edges_compressed = edges.replace("{\n  ", "\n  {").replace("\n},", "},").
      replace("\",\n  ", "\", ").replace("\n}]", "}\n]")
    
"""{
"nodes": """+nodes+"\n\n"+""""edges": """+edges_compressed+"\n}"
		
  }
  
}
