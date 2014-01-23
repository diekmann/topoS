package tum.in.net.netModelVisualizer

import tum.in.net.psn.log_topo.NetworkModels.{NetGraph, NetworkModelAbstract}
import tum.in.net.psn.log_topo.NetworkModels.NetworkModelList._
import tum.in.net.StringNode._
import tum.in.net.psn.log_topo.FlowMatrix


/**
 * Nice Output for a Shell which understands colors
 */
class ShellOut(graph: NetGraph, models: List[NetworkModelAbstract]) {
  protected def green(s: String): String = Console.GREEN + s + Console.RESET
  protected def red(s: String): String = Console.RED + s + Console.RESET
  protected def redBold(s: String): String = Console.RED + Console.BOLD + s + Console.RESET
  protected def modelStatus(m: NetworkModelAbstract): String = "[" + 
     {if (m.eval(graph)) green("valid") else red("invalid")} + "] "

  protected def printOverview: String = {
    def iterModels(ms: List[NetworkModelAbstract]): String = {
      if (ms.isEmpty) "" else modelStatus(ms.head) + 
      ms.head.model_type + ": "+ms.head.description + "\n" + iterModels(ms.tail)
    }
    "Overview:\n"+iterModels(models)+"\n"
  }

  
  protected def printWarning: String = {
    def iterModels(ms: List[NetworkModelAbstract]): String = {
      if (ms.isEmpty) "" else 
      { if (!ms.head.verify_globals(graph)) ""+ ms.head.model_type+"" else ""} + iterModels(ms.tail)
    }
    val warn = iterModels(models)
    if (warn == "") "" else
    redBold("WARNING:") + " verify_globals failed for "+warn+"\n"
  }
  
  protected def printOffendingFlows(m: NetworkModelAbstract): String = {
    if (!m.verify_globals(graph))
      redBold("WARNING:") + " verify_globals failed, cannot print offending flows"+"\n"
    else if (m.eval(graph)) "" else {
      val offflows = try {
         m.offending_flows(graph) match {
           case Nil => "[]"
           case List(offflows) => "[\n"+offflows.foldLeft("")((acc, f) => acc+"  "+f+"\n")+"]"
           case offflows => "ambiguous: "+offflows.foldLeft("[\n")((acc, fs) => acc+"    ["+fs.mkString(", ")+"]\n")+"]"
         }
      } catch {
        case e:StackOverflowError => "StackOverflow"
      }
      "  Offending flows: " +offflows + "\n"
    }
  }
  
  protected def printSecurityBreachlevel(m: NetworkModelAbstract): String = {
    if (m.eval(graph)) "" else {
      val level = m.model_breach_severity_rating(graph)
      "  Severence of security breach: " +level+ "\n"
    }
  }
  
  protected def printDetail: String = {
    def iterModels(ms: List[NetworkModelAbstract]): String = {
      if (ms.isEmpty) "" else {
          modelStatus(ms.head) + ms.head.model_type+": "+ms.head.description + "\n" + 
          printOffendingFlows(ms.head) +
          printSecurityBreachlevel(ms.head) +
          iterModels(ms.tail)
      }
    }
    "Detailed Overview:\n"+iterModels(models)+ "\n" +
    "Overall severence of security breach: "+models.breach_severity_rating(graph)+"\n"
  }
  
  def output: Unit = {
    println(printWarning)
    println(printOverview)
  }
  
  def outputDetail(): Unit = {
    println(printDetail)
  }
  
  def otherAllowedFlows(): String = {
    if (models.allValid(graph)){
      import tum.in.net.psn.log_topo.TopologyGeneration
      val otherAllowedFlows = TopologyGeneration.getOtherAllowedFlows(graph, models, dropReflexive=true)
      "Flows which would also be valid candidates:\n"+otherAllowedFlows.map("  "+_).mkString("\n")
    } else "" //no other flows can be calculated as model invalid
  }
  

  
  /**
   * output as ASCII art the flow matrix
   * per default, the current graph is printed
   */
  def outputFlowsMatrix(
      matrix: Array[Array[String]] = 
        FlowMatrix.simpleStringRepr(FlowMatrix.create(graph), "  *  ", "     ")
      ) = 
  {
    val max_line_length = 5
    val separator = " | "
    
    def max_line_str(s: String, offset:Int): String = {
      require(offset >= 0)
      if (s.length >= offset){
        val len = offset+max_line_length min s.length
        s.substring(offset, len) + (" "*(offset+max_line_length-len))
      } else " "*max_line_length
    }
    
    def max_line_str_end(s: String, offset:Int): String = {
      require(offset >= max_line_length)
      if (s.length >= offset){
        val len = offset max (s.length-max_line_length)
        s.substring(len, s.length) + (" "*(max_line_length-(s.length-len)))
      } else " "*max_line_length
    }
    
    
    val header1 = "   to" + separator + 
        graph.nodes.map(max_line_str(_, 0)).mkString(separator) + separator
    val header2 = ("-"*max_line_length) + separator + 
        graph.nodes.map(max_line_str(_, max_line_length)).mkString(separator) + separator
    val header3 = "from " + separator + 
        graph.nodes.map(max_line_str_end(_, max_line_length*2)).mkString(separator) + separator
    
    def printlnWithLineEnder(s: String): Unit = {
      val len = s.length
      val empty_field = (" "*max_line_length) + separator
      if (len >= header1.length) println(s)
      else if (len % empty_field.length == 0)
        println(s + (empty_field)*((header1.length-len-(separator.length))/empty_field.length+1))
      else println(s + " "*(header1.length-len-(separator.length)) + separator)
    }
    
    println(header1)
    println(header2)
    println(header3)
    println("-" * header1.length)
    for (i_line <- 0 until matrix.length){
      printlnWithLineEnder(max_line_str(graph.nodes(i_line), 0) + separator)
      val flowex = matrix(i_line).mkString(separator)
      printlnWithLineEnder(max_line_str(graph.nodes(i_line), max_line_length) + separator +flowex)
      printlnWithLineEnder(max_line_str_end(graph.nodes(i_line), max_line_length*2) + separator)
      println("-" * header1.length)
    }
  }
  
  def outputFlowsMatrixLatex(
      matrix: Array[Array[String]] = 
        FlowMatrix.simpleStringRepr(FlowMatrix.create(graph), "  *  ", "     ")
      ) = 
  {
    def latexSloppyHyphneation(s: String, width_cm: Double): String = {
      require(width_cm > 0)
      // fixed size parbox, add ability to separate word after every letter
      // without adding an hyphen.
      // requires babel ngerman!!
      // my document: usepackage[english,ngerman]{babel}
      """\parbox[b]{"""+width_cm+"""cm}{\smallskip\sloppy\selectlanguage{ngerman}{"""+s.mkString("""""""")+"""}}"""
    }
    
    def latexRotate(s: String): String = {
      """\rotatebox{90}{"""+s+"""}"""
    }
    
    def latexFilterName(s: String): String = {
      s.filter(c => c.isUpper || c.isDigit)
    }
    
    val header1 = """
				\begin{center}
    		\begin{tiny}
				\begin{tabular}{ c || """+ ("c | ")*(graph.nodes.length-1) + """c }"""+"\n"+
				"""\backslashbox{From\kern-1em}{\kern-2em To} """ + 
				" & "+graph.nodes.map(latexRotate(_)).mkString(" & ") + """\\"""
    val header2 = """\hline"""+"\n"+"""\hline"""
      
    println(header1)
    println(header2)
    
    for (i_line <- 0 until matrix.length){
      val flowex = matrix(i_line).mkString(" & ")
      println(latexSloppyHyphneation(latexFilterName(graph.nodes(i_line)), 1.2) + " & " +
          flowex + """\\""")
      println("""\hline""")
    }
    
    val footer1 = """
				\end{tabular}
    		\end{tiny}
				\end{center}"""
    println(footer1)
  }
  
}
