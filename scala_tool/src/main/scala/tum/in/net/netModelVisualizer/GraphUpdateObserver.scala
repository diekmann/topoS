package tum.in.net.netModelVisualizer

import tum.in.net.psn.log_topo.NetworkModels.NetGraph

/**
 * Observer pattern
 * 
 * this observer is called when something in the subject changes
 */
trait GraphUpdateObserver {
  /**
   * called whenever the graph changes
   */
  def notify(G: NetGraph): Unit
  
  /**
   * call s.cleanup(this) when the GraphUpdateObserver is destroyed
   */
  def registerCleanupSubject(s: GraphUpdateSubject): Unit
}

/**
 * GraphUpdateObserver extended with a JFrame
 * Features the JFrame cleanup stuff
 */
trait GraphUpdateObserverJFrame extends GraphUpdateObserver {
  
  import javax.swing.JFrame
  val frame : JFrame = new JFrame()
  frame.setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
  
  def registerCleanupSubject(s: GraphUpdateSubject): Unit = {
    frame.addWindowListener(new java.awt.event.WindowAdapter() {
      override def windowClosing(e: java.awt.event.WindowEvent): Unit = {
        val closing_frame: JFrame = e.getSource().asInstanceOf[JFrame]
        assert(closing_frame eq frame)
        s.unregisterGraphUpdateObserver(GraphUpdateObserverJFrame.this)
      }
    })
  }
  
  // call the following to finish setting up the JRAME according to your needs
  //  frame.getContentPane().add(my_component);
  //  frame.pack();
  //  frame.setVisible(true);
}

/**
 * The subject which notifies the observer
 */
trait GraphUpdateSubject {
  
  /** set of registered observers */
  private[this] var registeredObservers: Set[GraphUpdateObserver] = Set()
  
  /**
   * Add new observer to the list of notified observers
   */
  def registerGraphUpdateObserver(o: GraphUpdateObserver) = {
  if(registeredObservers.contains(o))
    throw new IllegalArgumentException("Observer "+o+" already in set")
  
  registeredObservers += o
  
  o.registerCleanupSubject(this)
  }
  
  /**
   * This is called when the observer decides to destroy itself.
   * E.g., the [x] on the window represented by the observeris pressed
   */
  def unregisterGraphUpdateObserver(o: GraphUpdateObserver): Unit = {
    if(! registeredObservers.contains(o))
      throw new RuntimeException("Observer "+o+" not in registeredObservers")

    registeredObservers -= o
  }
  
  def notifyGraphUpdateObservers(G: NetGraph): Unit = registeredObservers.foreach(_.notify(G))
}
