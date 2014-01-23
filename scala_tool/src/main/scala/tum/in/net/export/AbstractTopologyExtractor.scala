package tum.in.net.export


import tum.in.net.StringNode._
import be.jvb.iptypes.IpAddress
import tum.in.net.psn.log_topo.NetworkModels.{NetGraph, NetworkModelAbstract}

/**
 * generate a configuration from the topology
 * implementations: for openVPN
 * @author corny
 *
 */
abstract class AbstractTopologyExtractor{
  
  val graph: NetGraph
  val models: List[NetworkModelAbstract]
  
  private val temporaryDirectory = new java.io.File(System.getProperty("java.io.tmpdir"))
  private val MaximumTries = 10
  private val random = new java.util.Random()

  private def createTemporaryDirectory(): java.io.File = {
    def create(tries: Int): java.io.File = {
      if(tries > MaximumTries)
        throw new RuntimeException("Could not create temporary directory after "+MaximumTries+" tries.")
      else {
        val randomName = "nsm_" + java.lang.Integer.toHexString(random.nextInt)
        val dir = new java.io.File(temporaryDirectory, randomName)

        if(dir.exists){
          if(dir.isDirectory)
            throw new RuntimeException(dir + " exists and is a directory.")
          else
            throw new RuntimeException(dir + " exists and is not a directory.")
        } else {
          if (!dir.mkdirs()) throw new RuntimeException(dir + " mkdirs failed")
          dir
        }
        //create(tries + 1)
      }
    }
    create(0)
  }
  
  /**
   * create the subdirectories in `dir' in a temp diectory
   * create a file named `name' in this directory
   * write `content' to that file
   * set the flag `create' if all directories in `dir' must be created
   */
  protected def writeToFile(dir: List[String], name: String, content: String, create: Boolean=true): Unit = {
    def generateSubDirs(dirs: List[String], currDir: java.io.File): java.io.File = dirs match {
      case Nil => currDir
      case d::ds =>
        val out = new java.io.File(currDir, d)
        if (!out.mkdir() && create) throw new RuntimeException("Could " +
          "not create directory "+out+" in "+currDir)
      
        if (out.exists() && out.isDirectory() && !create){
          //println("directory "+out+"exists")
        }
        
        generateSubDirs(ds, out)
    }
    
    val out = generateSubDirs(dir, outDir)
    val outFile = new java.io.File(out, name)
    
    if (outFile.exists())
      throw new RuntimeException("File "+outFile+" already exists")
    
    if (!outFile.createNewFile())
      throw new RuntimeException("File "+outFile+" could not be created")
   
    val p = new java.io.PrintWriter(outFile)
    try { p.write(content) } finally { p.close() }
    
    if (outFile.getName().endsWith(".sh"))
      outFile.setExecutable(true)
  }
  
  protected val outDir: java.io.File = createTemporaryDirectory()
  
  trait ServerClient{
    val addr: IpAddress
    val name: String
    val config: String
    
    def writeConfig(): Unit
  }
  protected abstract class Client extends ServerClient with Ordered[Client] {
    def compare(that: Client) =  this.addr.value.compareTo(that.addr.value)
  }
  
  protected abstract class Server extends ServerClient
  
  protected val cnames: Map[Node, Client]
  
  protected val server: Server
  
  def writeConfiguration(): Unit = {
    import tum.in.net.psn.log_topo.NetworkModels.NetworkModelList._
    require(models.allValid(graph), "all models must be valid to export configuration")
    
    println("Writing config to "+outDir)
    server.writeConfig()
    for (c <- cnames.values) {c.writeConfig()}
    println("Done")
  }

}
