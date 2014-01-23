package tum.in.net.export

trait otherdevicesXML extends AbstractTopologyExtractor{
   /**
   * write an xml file for each client to which IP it can connect.
   * Used for the BACnet simulator
   * <bacdevices>
   *  <device>192.168.56.102</device>
   *  <device>192.168.56.103</device>
   * </bacdevices>
   */
  protected def writeOtherdevicesXML(): Unit = {
    import scala.xml._
    for(node <- cnames.keys){
      // other nodes `node' can connect to
      val otherNodes = graph.edges.filter(_._1 == node).map(_._2)
      
      val devIPs = for (other <- otherNodes) 
        yield {
        val c: Client = cnames(other)
        <device cname={other}>{c.addr}</device>
      }
      
      val devIPsXML = NodeSeq.Empty ++ devIPs
      val xmlResult = <bacdevices>{devIPsXML}</bacdevices>
      val dir = new java.io.File(outDir, node)
      val file = new java.io.File(dir, "otherdevices.xml").toString()
      XML.save(file, xmlResult, "utf-8", true, null)
    }
  }
  
  override def writeConfiguration(): Unit = {
    super.writeConfiguration()
    
    println("Writing otherdevices.xml")
    writeOtherdevicesXML()
    println("Done")
  }

}


trait AbstactNameIpMapping extends AbstractTopologyExtractor{
  
  protected def getNameIpMapping(): String = {
    
    val str = for(node <- cnames.keys) yield{
      "\""+cnames(node).addr+"\": \""+node+"\""
    }
    
    val mapping = "{"+str.mkString(",\n")+"}"
    mapping
  }
  
  override def writeConfiguration(): Unit = {
    super.writeConfiguration()
    
    //TODO write
    println("abstractName to IP mapping: "+getNameIpMapping())
    println("Done")
  }

}


trait hostnameExporter extends AbstractTopologyExtractor{
  protected def writeHostename(): Unit = {
    import scala.xml._
    for(node <- cnames.keys){
      writeToFile(dir=List(node), name="hostname", content=node+"\n", create=false)
    }
  }
  
  override def writeConfiguration(): Unit = {
    super.writeConfiguration()
    
    println("Writing hostname file")
    writeHostename()
    println("Done")
  }
}

trait iptablesFirewall extends AbstractTopologyExtractor{
  
  protected def writeIptablesSetup(): Unit = {
  val setupCerts_hdr = """#!/bin/bash
#
# Linux Version

# we are a router
echo 1 > /proc/sys/net/ipv4/ip_forward

# flush all rules
iptables -F

#default policy for FORWARD chain:
iptables -P FORWARD DROP

# accept all established connections
# todo: we could write a stricter rule but we trust in conntrack here
# real filtering occurs in connection establishment
iptables -A FORWARD -m conntrack --ctstate RELATED,ESTABLISHED -j ACCEPT

      
# flow matrix
"""

    val cfg_clients_list = for ((c1, c2) <- graph.edges) yield {
        "# "+cnames(c1).name+" -> "+cnames(c2).name+"\n"+
        "iptables -A FORWARD -s "+cnames(c1).addr+" -d "+
        cnames(c2).addr + " -m conntrack --ctstate NEW -j ACCEPT"
    }
    val setupCerts_middle: String = cfg_clients_list.mkString("\n\n")

    val setupCerts_footer = """

# log all invalid flows
iptables -A FORWARD -j LOG --log-prefix "invalid flow: "
    """
    val script = setupCerts_hdr + setupCerts_middle + setupCerts_footer
      
    writeToFile(dir=List(), name="iptables.sh", content=script)

  }
  
    
  
    override def writeConfiguration(): Unit = {
    super.writeConfiguration()
    
    println("Setup the firewall with the script iptables.sh")
    writeIptablesSetup()
    println("script generated")
  }
}