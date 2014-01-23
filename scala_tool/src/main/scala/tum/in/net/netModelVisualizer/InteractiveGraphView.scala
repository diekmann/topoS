package tum.in.net.netModelVisualizer


import tum.in.net.psn.log_topo.NetworkModels.NetGraph
import java.awt.Dimension
import edu.uci.ics.jung.algorithms.layout.CircleLayout
import edu.uci.ics.jung.graph.DirectedSparseGraph
import edu.uci.ics.jung.visualization.VisualizationViewer
import edu.uci.ics.jung

/**
 * Uses JUNG
 * maybe i will discontinue this and switch to gephi
 */

class InteractiveGraphView(initialGraph: NetGraph) extends GraphUpdateObserverJFrame{
  require(initialGraph != NetGraph(List(), List()), "not sure if it works in this case")
  
  private[this] var old_graph_cache: NetGraph = NetGraph(List(), List())
  
  protected var jung_graph = new DirectedSparseGraph[String, String]()
  updateJUNGgraph(initialGraph, old_graph_cache)
  old_graph_cache = initialGraph
  
  
  
  
  // not sure if JUNG is maintained
  private var vv: VisualizationViewer[String, String] = new VisualizationViewer[String, String](
      new CircleLayout[String, String](jung_graph), new Dimension(400, 400))
  
  /**
   * set fancy things like node color
   */
  private def initVisualizationViewer(): Unit = {
      vv.setPreferredSize(new Dimension(500,500))
	  vv.setBackground(java.awt.Color.white);
	  vv.getRenderer().getVertexLabelRenderer().setPosition(
				  jung.visualization.renderers.Renderer.VertexLabel.Position.CNTR)
				  // display vertex names
	  vv.getRenderContext().setVertexLabelTransformer(
				  new jung.visualization.decorators.ToStringLabeller())
	
	  // The following code adds capability for mouse picking of vertices/edges. Vertices can even be moved!
	  val graphMouse = new jung.visualization.control.DefaultModalGraphMouse[String,String]();
	  graphMouse.setMode(jung.visualization.control.ModalGraphMouse.Mode.PICKING);
	  vv.setGraphMouse(graphMouse);
		  
	  vv.getRenderContext().setVertexFillPaintTransformer(
		     new org.apache.commons.collections15.Transformer[String,java.awt.Paint]() {
	            def transform(label: String): java.awt.Paint = java.awt.Color.CYAN
	        })
	        
	  vv.getRenderContext().setVertexShapeTransformer(
		     new org.apache.commons.collections15.Transformer[String,java.awt.Shape]() {
	            def transform(label: String): java.awt.Shape = {
	              //val longest_name = G.nodes.map(_.toString.length).max
	              val longest_name = label.length
	              val width = longest_name * 10.0 // 12.0 is approx size of letter
	              val circle = new java.awt.geom.Ellipse2D.Double(-(width/2), -12.5, width, 25);
	              //circle.setFrame(circle.getX()+100, circle.getY(), 200, 200)
	              circle
	            }
	        })
  }
  initVisualizationViewer()
  
  

  /**
   * add button to change graph layouter
   */
  def initializeSwitchLayoutButton(): Unit = {
      /**
	   * change the graph layouter
	   * with fancy animation
	   */
	  def changeJUNGLayout(layout: jung.algorithms.layout.AbstractLayout[String, String], 
	      relax: Boolean = false): Unit = 
	  {
		
	      //zooming
		  //val scaler: jung.visualization.control.ScalingControl = 
		  //		  new jung.visualization.control.CrossoverScalingControl()
		  //scaler.scale(vv, 1.1f, vv.getCenter());
		  
		  layout.setSize(vv.getSize())
		  
		  //println(vv.getModel().getRelaxer() + "could:relax:"+layout.isInstanceOf[edu.uci.ics.jung.algorithms.util.IterativeContext])
		  assert(vv.getModel().getRelaxer() eq null)
		  if(relax && layout.isInstanceOf[edu.uci.ics.jung.algorithms.util.IterativeContext]){
			  val relaxer: jung.algorithms.layout.util.Relaxer
			  	= new jung.algorithms.layout.util.VisRunner(
			  	    layout.asInstanceOf[edu.uci.ics.jung.algorithms.util.IterativeContext])
			  relaxer.stop()
			  relaxer.prerelax()
		      //val process = layout.asInstanceOf[edu.uci.ics.jung.algorithms.util.IterativeContext]
			  //(0 to 1000).toStream.takeWhile(_ => !process.done()){ process.step(); 0}
		  }
		  
		  {
			  import collection.JavaConversions._
			  val vs : Iterable[String] = layout.getGraph().getVertices()
			  for (v <- vs){
				  //println(v+" "+layout.getX(v)+" "+layout.getY(v))
				  val minX = v.length()*5.0
				  val maxX = vv.getSize().getWidth() - minX
				  val X = layout.getX(v)
				  val newX = if (X < minX) minX else if (X > maxX) maxX else X
				  val minY = 12.5
				  val maxY = vv.getSize().getHeight() - minY
				  val Y = layout.getY(v)
				  val newY = if (Y < minY) minY else if (Y > maxY) maxY else Y
				  layout.setLocation(v, newX, newY)
			  }
		  }
		  
		  val staticLayout: jung.algorithms.layout.Layout[String, String] =
			new jung.algorithms.layout.StaticLayout[String, String](jung_graph, layout)
			
		  val lt: jung.visualization.layout.LayoutTransition[String,String] =
			new jung.visualization.layout.LayoutTransition[String,String](vv, vv.getGraphLayout(),
				staticLayout)
		  val animator = new jung.visualization.util.Animator(lt);
		  animator.start();
		  
		  
		  vv.repaint();
	  }
  
    val switchLayout = new javax.swing.JButton("Switch to CircleLayout");
    switchLayout.addActionListener(new java.awt.event.ActionListener() {
      import jung.graph.AbstractTypedGraph
      import jung.algorithms.layout.AbstractLayout
      
      /* Name -> (layouter, useRelaxer) */
	  val layoutTxtLayout = scala.collection.immutable.ListMap[String, 
	    (AbstractTypedGraph[String, String] => AbstractLayout[String, String], Boolean)](
	      "SpringLayout" -> (new jung.algorithms.layout.SpringLayout[String,String](_), false),
	      "FRLayout" -> (new jung.algorithms.layout.FRLayout[String,String](_), true),
	      "CircleLayout" -> (new jung.algorithms.layout.CircleLayout[String,String](_), false),
	      //"DAGLayout" -> (new jung.algorithms.layout.DAGLayout[String,String](_), true),
	      //DAGlayout crashes for cyclic graphs
	      "KKLayout" -> (new jung.algorithms.layout.KKLayout[String,String](_), true)
	      )
    	      
        def actionPerformed(ae: java.awt.event.ActionEvent): Unit = {
            val layoutKey = switchLayout.getText().drop("Switch to ".length()) 
            
            assert(layoutTxtLayout.contains(layoutKey), 
                "switchLayout button text contains valid layout `"+layoutKey+"`")
            
            val (layouter, relax) = layoutTxtLayout(layoutKey)
            changeJUNGLayout(layouter(jung_graph), relax)
            
            val keys = layoutTxtLayout.keys.toList
            val nextSwitchTo = keys(
                (keys.indexOf(layoutKey) + 1) % keys.toList.length
                )
            switchLayout.setText("Switch to "+nextSwitchTo)
        }
    })
    
    frame.getContentPane().add(switchLayout, java.awt.BorderLayout.SOUTH);
    
    switchLayout.doClick()
  }
  initializeSwitchLayoutButton()
        
  // setting up JFrame
  //val panel = new javax.swing.JPanel(new java.awt.FlowLayout(java.awt.FlowLayout.LEFT))
  //frame.getContentPane().add(panel)
  //panel.add(vv)
  frame.getContentPane().add(vv)
  frame.pack()
  frame.setVisible(true)
  
  /** label of a JUNG edge */
  protected def jungEdgeLabel(e: (String, String) ): String = e._1+"->"+e._2
  
  
  /**
   * add and remove edges/nodes from jung_graph
   * 
   * do nothing else here with side effect!
   */
  protected def updateJUNGgraph(newG: NetGraph, oldG: NetGraph): Unit = {
	val new_vertixes = newG.nodes diff oldG.nodes
	val disappeared_vertixes = oldG.nodes diff newG.nodes
	val new_edges = newG.edges diff oldG.edges
	val disappeared_edges = oldG.edges diff newG.edges
	
	new_vertixes.foreach(jung_graph.addVertex(_))
	disappeared_vertixes.foreach(jung_graph.removeVertex(_))
	new_edges.foreach(e => jung_graph.addEdge(jungEdgeLabel(e), e._1, e._2))
	disappeared_edges.foreach(e => jung_graph.removeEdge(jungEdgeLabel(e)))
  }
  
	  
  def notify(G: NetGraph): Unit = {  
	if(old_graph_cache == G){
	  println("InteractiveGraphView: no new graph")
		return
	}
	updateJUNGgraph(G, old_graph_cache)
	
	old_graph_cache = G
	

	vv.repaint()
  }
}
