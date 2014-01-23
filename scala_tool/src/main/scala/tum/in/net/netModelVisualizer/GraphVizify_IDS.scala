package tum.in.net.netModelVisualizer

import tum.in.net.psn.log_topo.NetworkModels.{NetGraph, NetworkModelAbstract}
import scala.sys.process.stringSeqToProcess
import tum.in.net.StringNode._


/**
 * A changed GraphVizify class which is used to display the 
 * security breach rating
 */
class GraphVizify_IDS(graph: NetGraph, models: List[NetworkModelAbstract], 
      __visual_extra_in: Map[String, List[Node]],
      __breach_rating_map_in: Map[(Node, Node), Int]) 
      extends GraphVizify(graph, models, __visual_extra_in) {
  protected val breach_rating_map = {
    //TODO verify input
    __breach_rating_map_in
  }

  
  val max_rating = breach_rating_map.values.max


  override protected def addEdge_generateLabel(e1: Node, e2: Node): List[String] = {
    val label = super.addEdge_generateLabel(e1, e2)
    
    def weight(e1: Node, e2: Node) = if(breach_rating_map((e1, e2)) != 0) {
      val relRating = (breach_rating_map((e1,e2)).toFloat / max_rating)
      val penwidth = (relRating*8).toInt+1
      val saturation = ((relRating*200).toInt + 55).toHexString
      assert(penwidth >= 0)
      //List("penwidth="+penwidth, "constraint=false", "style=solid")
      //List("arrowsize="+penwidth, "arrowtail=inv", "constraint=false", "dir=back")
      //List("penwidth="+penwidth, "constraint=true", "style=solid", "color=\"#FF0000"+saturation+"\"")
      List("penwidth="+0.5, "constraint=true", 
        "style=dotted", "color=\"#FF0000"+saturation+"\"",
        "arrowtail=crow", "dir=back", "arrowsize="+penwidth)
    } else {
      List()
    }
    
    if (breach_rating_map.contains((e1,e2))) 
      label ++ weight(e1,e2)
    else{
      println("WARNING: edge "+e1+"->"+e2+" has no associated weight")
      List("style=invisible", "dir=none")
    }
  }
  
  
  override protected val graphvizHeader = """/* circo circo_ids.dot -Tpdf -o circo_ids.pdf */
digraph G {
 rankdir=BT
 graph [overlap=false, margin="0.00,0.00", pad="0.00,0.00", mindist="0.6", splines=true];

 
 
 node [shape=box]
 node [fontname=Verdana,fontsize=34,margin="0.5,0.5"]
 node [style=filled]
 node [fillcolor="#EEEEEE"]
 node [color="#EEEEEE"]
 edge [color="#31CEF0"]
 
 """
  
  override protected def addLegend: String =  ""
    
  override protected def addNode(name: Node): String = {
    //val (hdr, footer) = addNode_generateLabel(name)
    
    val hdr = name+"""[label=<<TABLE BORDER="0" CELLSPACING="0" CELLPADDING="0"><TR><TD CELLPADDING="2">"""+
      """<FONT face="Verdana">"""+name.mkString(" ")+"""</FONT></TD></TR>"""
    val footer = ("""</TABLE>>]"""+"\n\n")
    
    hdr+footer
  }
  
  
}
