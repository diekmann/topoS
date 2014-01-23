package tum.in.net.netModelVisualizer

import tum.in.net.psn.log_topo.NetworkModels.{NetGraph, NetworkModelAbstract}
import scala.sys.process.stringSeqToProcess
import tum.in.net.StringNode._




class GraphVizify(graph: NetGraph, models: List[NetworkModelAbstract], 
     protected val __visual_extra_in: Map[String, List[Node]]) 
  extends GraphVizBase(graph)
  with GraphViz_RenderView
  with GraphViz_visualExtra
{
  
  visualExtra_initialize(__visual_extra_in)
  
  protected val graphvizHeader = """/* dot name.dot -Tpdf -o name.pdf */
digraph G {
 rankdir=BT
 graph [overlap=false, margin="0.00,0.00", pad="0.00,0.00", ranksep="1.2", splines=true];

 
 
 node [shape=box]
 node [fontname=Verdana,fontsize=12]
 node [style=filled]
 node [fillcolor="#EEEEEE"]
 node [color="#EEEEEE"]
 edge [color="#31CEF0"]
 
 """
  protected val graphvizFooter = """}"""
    
  
    
    
  protected def printLabel(label: Int): String = {
    if (models.length <= 3) ""
    else label.toString+") "
  }
  
  override protected def addNode(name: Node): String = {
    def iterModels(models: List[NetworkModelAbstract], label: Int): List[String] = {
      if (models.isEmpty) List() else (printLabel(label)+models.head.nodeConfigToString(name)) :: iterModels(models.tail, label+1)
    }
    
    def printNodeConfig(models: List[NetworkModelAbstract]): String = {
      val cfg = iterModels(models, 1)
      //remove all default configurations
      val cfgsmall = cfg.filterNot(e => e.trim().matches("""\d{1,3}\s?\)\s*⊥"""))
      cfgsmall.map(e => "<TR><TD>"+e+"</TD></TR>").mkString("")
    }
    val (hdr, footer) = addNode_generateLabel(name)
    
    hdr+printNodeConfig(models)+footer
  }
  
  
  
  
  protected def calulateOffendingEdges: List[(Node,Node)] = {
    import tum.in.net.psn.log_topo.NetworkModels.NetworkModelList._
    models.unionOffendingEndges(graph)
  }
  val offendingEdges: List[(Node,Node)] = try {calulateOffendingEdges} catch {
    case e:StackOverflowError => {
      global_warnings += "calculating offending edges failed due to stack overflow"+"\n"
      graph.edges
    }
  }
  
    
  /**
   * print offending edges red and dotted
   */
  override protected def addEdge_generateLabel(e1: Node, e2: Node): List[String] = {
    if (offendingEdges.contains((e1,e2))) 
      List("""style=dotted""", """color="#FF0000"""")
    else
      List()
  }
  
  protected def addLegend: String = {
    def iterModels(ms: List[NetworkModelAbstract], label: Int): String = {
      if (ms.isEmpty) "" else "<TR><TD>"+printLabel(label)+"""<FONT COLOR="#"""+
      { if (ms.head.eval(graph)) "00BB00" else "BB0000"}+"""">"""+
      ms.head.model_type+"</FONT>: "+ms.head.description+"</TD></TR>" + iterModels(ms.tail, label+1)
    }
    """{ rank = sink;
    GraphvizNodeLegend [shape=none, margin=0, label=<<TABLE BORDER="0" CELLSPACING="0" CELLPADDING="2" CELLBORDER="2"><TR><TD ALIGN="LEFT"> key:</TD></TR><TR><TD>"""+
      """<FONT face="Verdana Bold">"""+"nodeName"+"""</FONT></TD></TR>"""+iterModels(models, 1)+"""</TABLE>>]}"""+"\n"
  }
  
  protected def addWarning: String = {
    def iterModels(ms: List[NetworkModelAbstract]): String = {
      if (ms.isEmpty) "" else 
      { if (!ms.head.verify_globals(graph)) "<TR><TD>"+ ms.head.model_type+"</TD></TR>" else ""} + iterModels(ms.tail)
    }
    val warn = iterModels(models)
    if (warn == "" && global_warnings == "") "" else
    """{ rank = sink;
    GraphvizNodeWarning [shape=none, margin=0, label=<<TABLE BORDER="0" CELLSPACING="0"><TR><TD>"""+
      """<FONT face="Verdana Bold" color="#BB0000">"""+"WARNING: verify_globals failed for"+"""</FONT></TD></TR>"""+warn+
      """<TR><TD><FONT face="Verdana Bold" color="#BB0000">"""+"other warnings:"+"""</FONT></TD></TR>"""+
      global_warnings.split('\n').map(w => "<TR><TD>"+w+"</TD></TR>").mkString("\n")+
      //"<TR><TD>"+global_warnings+"</TD></TR>"+
      """</TABLE>>]}"""+"\n"
  }
  
  
  def displayGraph(aggreagte_biflow: Boolean): Unit = {
    val graphviz = toGraphviz(aggreagte_biflow)
    displayGraphFromDescr(graphviz, RenderBackends.Dot)
  }
  
  def displayGraphNeato: Unit = {
    val graphviz = toGraphviz(aggreagte_biflow=false)
    displayGraphFromDescr(graphviz, RenderBackends.Neato)
  }
  def displayGraphCirco(aggreagte_biflow: Boolean): Unit = {
    val graphviz = toGraphviz(aggreagte_biflow)
    displayGraphFromDescr(graphviz, RenderBackends.Circo)
  }
  
  protected def toGraphviz(aggreagte_biflow: Boolean): String = {
    
    val directed_edges = if (!aggreagte_biflow) {
        graph.edges
      } else {
        /* all nodes where no backflow exists */
        val no_backflows = graph.edges.filter(e => !graph.edges.contains((e._2, e._1)))
        
        /* display offending flows separately */
        val offending = graph.edges.filter(e => 
          offendingEdges.contains(e) || offendingEdges.contains((e._2, e._1)))
        
        (no_backflows ++ offending).distinct
      }
    
    val bidirectional_edges = if (!aggreagte_biflow) {
        List()
      } else {
        /* all nodes where backflow exists */
        val backflows = graph.edges.diff(directed_edges)
        assert((backflows.toSet union directed_edges.toSet) == graph.edges.toSet)
        
        // only works because edges distinct
        // removes reflexive flows
        def remdups(n: List[(Node,Node)]): List[(Node, Node)] = n match {
          case Nil => n
          case l::ls => if (ls.contains((l._2, l._1))) l::remdups(ls) else remdups(ls)
        }
        
        remdups(backflows)
      }
      
    assert({
      val all = graph.edges.toSet
      val bi_edges = bidirectional_edges ++ bidirectional_edges.map(e => (e._2, e._1))
      val edges = directed_edges.toSet union bi_edges.toSet
      val diff = all.diff(edges)
      diff.forall(e => e._1 == e._2) && (edges.diff(all).isEmpty)
      }, "aggegated edges are complete (modulo reflexive flows)")
    
    graphvizHeader+"\n"+
      listNodes(graph.nodes)+"\n"+
      listEdges(directed_edges)+"\n"+
      """/* bidirectional flows */
      edge [dir="none", color="#484848"]"""+"\n"+
      listEdges(bidirectional_edges)+"\n"+
      addLegend+"\n\n"+
      addWarning+"\n\n"+
      graphvizFooter
  }
  
  
}
