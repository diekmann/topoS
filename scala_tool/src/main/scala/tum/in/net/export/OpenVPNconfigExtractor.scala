package tum.in.net.export


import tum.in.net.psn.log_topo.NetworkModels.{NetGraph, NetworkModelAbstract}
import be.jvb.iptypes.IpAddress
import tum.in.net.StringNode._

class OpenVPNconfigExtractor(val graph: NetGraph, val models: List[NetworkModelAbstract], serverIP: IpAddress) extends AbstractTopologyExtractor
  with otherdevicesXML
  with iptablesFirewall
  with hostnameExporter
  with AbstactNameIpMapping
{

  protected class MyClient(val addr: IpAddress, val name: String, srvIPAddr: IpAddress) 
    extends Client
  {
    val config: String = """
# use openvpn default config
client
dev tun
proto udp

#TODO change
remote """+srvIPAddr.toString+""" 1194
#TODO
      
resolv-retry infinite
nobind
persist-key
persist-tun

#TODO
ca ca.crt
cert """+name+""".crt
key """+name+""".key
      
ns-cert-type server
comp-lzo
verb 3
      """
    
    override def writeConfig(): Unit = {
      writeToFile(dir=List(name), name="client.conf", content=config)
    }
  }
  
  protected class MyServer(val addr: IpAddress) extends Server {
    val name = "OpenVPNServer"
    val cfg_header: String = """
port 1194
proto udp
dev tun # IPv4 and IPv6

ca ca.crt
cert """+name+""".crt
key """+name+""".key  # This file should be kept secret
dh dh1024.pem

#verify that this is 10.8.0.0
server """+(addr-1).toString+""" 255.255.255.0

ifconfig-pool-persist ipp.txt #should be always empty

ccd-exclusive #only explicitly configured clients allowed
client-config-dir ccd

keepalive 10 120
comp-lzo
persist-key
persist-tun
status openvpn-status.log
verb 3

# iter over clients

""".stripMargin
    
    val cfg_clients_list = for (c <- clients) yield {
      import be.jvb.iptypes.{IpNetwork, IpNetworkMask}
      
      // complicated way as this will throw exceptions on logical addressing errors
      val netmask = new IpNetworkMask("255.255.255.252")
      val netaddr = new IpNetwork(new IpAddress((c.addr-1).toString), netmask).address
      
      val network1 = new IpNetwork(new IpAddress("192.168.0.0"), new IpNetworkMask("255.255.255.0"))
      val verifynetwork = new IpNetwork((c.addr-1).toString+"/30")
      
      assert(verifynetwork.address == netaddr)
      
      "route "+netaddr+" "+netmask+"\n"+
      "push \"route "+netaddr+" "+netmask+"\""+"\n"
    }
    val config: String = cfg_header + cfg_clients_list.mkString("\n")
    
    override def writeConfig(): Unit = {
      writeToFile(dir=List(name), name="server.conf", content=config)
      
      for (c <- clients) {
        val clientccd = "ifconfig-push "+c.addr.toString+" "+(c.addr + 1).toString+"\n"
        writeToFile(dir=List(name, "ccd"), name=c.name, content=clientccd, create=false)
      }
    }
  }
  
  protected final val srvIp = new IpAddress("10.8.0.1")
  
  protected final val clientFirstIp = new IpAddress("10.9.0.1")
  
  // each clients gets a /30 subnet
  // openvpn default when assigning a fix IP to a client
  protected final val ipSteps = 4 // clientFirstIp + i*ipSteps will be the ith client IP
  
  protected def setupClients(serverIP: IpAddress): Map[Node, Client] = {
    def setupOne(n: Node, i: Int): (Node, Client) = {
      val ip = clientFirstIp + (i+1)*ipSteps
      
      //println("Info: setting the server IP to "+serverIP)
      
      val c = new MyClient(ip, n.toString(), serverIP)
      
      (n, c)
    }
    
    val clients = for(i <- 0 until graph.nodes.length) yield setupOne(graph.nodes(i), i)
    clients.toMap
  }
  
  protected def setupServer: Server = {
    new MyServer(srvIp)
  }

  override protected val cnames: Map[Node, Client] = setupClients(serverIP)
  protected val clients = cnames.values.toList.sorted
  override protected val server: Server = setupServer
  
  protected def writeEasyRSAscript(): Unit = {
    val setupCerts_hdr = """
#!/bin/bash
#
# run this in the easy-rsa directory of openVPN
# debian: /usr/share/doc/openvpn/examples/easy-rsa/2.0/
# it is recommended to make a copy of that directory.
# the subdirectory keys will contain the whole PKI
#
# Linux Version

. ./vars
./clean-all
./build-ca

./build-key-server """+server.name+"\n\n"

    // generate client certificates
    // tuple (interactive cmd, automatic cmd)
    val cfg_clients_list = for (c <- clients) yield {
      ("\t./build-key "+c.name, "\t./pkitool "+c.name)
    }
    
    
    val setupCerts_middle: String = """
case "$1" in
  automatic )
      """+cfg_clients_list.map(_._2).mkString("\n")+"""
      ;;
  *)
      echo "=========================================================="
      echo "starting client certification creation in interactive mode"
      echo "issue \`automatic' option to create them all at once."
      echo "without user interaction"
      echo "=========================================================="
      """+cfg_clients_list.map(_._1).mkString("\n")+"""
      ;;
esac
"""

    val setupCerts_footer = """
./build-dh
    """
    val script = setupCerts_hdr + setupCerts_middle + setupCerts_footer
      
    writeToFile(dir=List(), name="setup_pki.sh", content=script)
    
    println("Setup the PKI with the script setup_pki.sh")
  }
  
  
  def copyOpenVPNcerts(): Unit = {
    val hdr = """#!/bin/bash

if [ $# -ne 1 ]; then
	echo "Usage: execute $0 in the generated nsm directory"
	echo "param1: path to easy-rsa keys directory"
	exit
fi

if [ ! -d $1 ]; then
	echo "$1 is not a directory"
	exit
else
	KEYDIR=$1
fi

for file in "$KEYDIR/"""+server.name+""".crt" "$KEYDIR/"""+server.name+""".key" "$KEYDIR/ca.crt"; do
	if [ ! -f $file ]; then
		echo "$file does not exist"
		exit
	fi
done

for file in "$KEYDIR/"""+server.name+""".crt" "$KEYDIR/"""+server.name+""".key" "$KEYDIR/ca.crt" "$KEYDIR/dh*.pem"; do
	cp -i $file """+server.name+"""
done
	
"""

	val clientsFor = for (client <- clients) yield {
	val c = client.name
"""
for file in "$KEYDIR/ca.crt" "$KEYDIR/"""+c+".crt\" \"$KEYDIR/"+c+""".key"; do
	cp -i $file """+c+"""
done
"""}
    
   writeToFile(dir=List(), name="copycerts.sh", content=hdr+clientsFor.mkString("\n"))
   println("user copycerts.sh to distribute generated certificates/keys to client directories")
    
  }

  
  override def writeConfiguration(): Unit = {
    super.writeConfiguration()
    
    writeEasyRSAscript()
    copyOpenVPNcerts()
  }

}
