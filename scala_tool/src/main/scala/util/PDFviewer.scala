package util


/**
 * Utility to view PDFs
 */
object PDFviewer {
  
  /** Possible PDF viewers in PATH or cwd **/
  protected val viewers = List("xdg-open", "evince", "open", "pdfviewer.bat")
  
  /**
   * start external PDF viewer
   */
  def viewPDF(fileName: String) = {
	  import scala.sys.process._
	  
		def startPDFviewer(viewer: String): Unit = {
		  val command = Seq(viewer, fileName+".pdf")
			val evinceReturn = command.!
			if(evinceReturn != 0) {
			  println("Error running pdf viewer!")
			  println("Command was `"+command+"'")
				println("cmd returned :"+evinceReturn)
				throw new RuntimeException
			}
    }
    
	  def iterViewers(vievers: List[String]): Unit = vievers match {
	    case Nil => println("No PDF viewer left to try.")
	    case v::vs => try{
			      startPDFviewer(v)
			    }catch {
			      case e: java.io.IOException => println(e);println("trying next viewer")
			      		iterViewers(vs)
			    }
    }
	  
	  iterViewers(viewers)
  }
  
  

}