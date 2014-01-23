package tum.in.net.psn.log_topo.NetworkModels

import GENERATED.NetworkModel_Library._
import GENERATED.NetworkModel_Interface.networkModel_Params_ext
import GENERATED.datatype_DomainHierarchy
import GENERATED.NetworkModel_Interface.{networkModel_Params_ext, NetworkModel_Params_ext, model_global_properties}
import GENERATED.Code_Numeral.integer_of_nat
import tum.in.net.psn.log_topo.HOLequal_String._



/********** begin concrete network models, overwriting NetworkModel for extended functionality ***********/

protected object DomainHierarchyPrettyPrinter{
	def printDomainName(s: datatype_DomainHierarchy.domainName): String = {
			s match {
			case datatype_DomainHierarchy.Leaf() => ""
			case datatype_DomainHierarchy.Dept(a, as) => a.mkString+"-"+printDomainName(as)
			case datatype_DomainHierarchy.Unassigned() => "Unassigned "
			case _ => throw new RuntimeException("domainName unknown pattern"+s)
			}
	}
	
  def printDomainTree(s: datatype_DomainHierarchy.domainTree): String = { 
	  def iter(s: List[datatype_DomainHierarchy.domainTree]): String = {
	    if (s.isEmpty) "" else printDomainTree(s.head)+", "+iter(s.tail)
	  }
    s match {
      case datatype_DomainHierarchy.Department(a, as) => a.mkString+" > "+"["+iter(as).dropRight(2)+"]"+""
      case _ => throw new RuntimeException("domainTree unknown pattern")
    }
  }
}

protected trait DomainHierarchyGlobalsGraphizPrinter{
  def pretty_globalConfigToGraphvizCompatibleString(gP: datatype_DomainHierarchy.domainTree): String = {
		  def iter(s: List[datatype_DomainHierarchy.domainTree]): String = {
		    if (s.isEmpty) "" else {
		      val edge = s.head match {case datatype_DomainHierarchy.Department(a, as) => 
		        intermediarities(as).map(x => a.mkString + " -> " + x).mkString("\n")
		      }
		      edge+"\n"+isdirectEdge(s.head)+"\n"+iter(s.tail)
		    }
		  }
		  
		  def intermediarities(s: List[datatype_DomainHierarchy.domainTree]): List[String] = {
		    s.foldLeft(List[String]())((acc, x) => x match {
		      case datatype_DomainHierarchy.Department(a, as) => if (!isLeaf(x)) (a.mkString)::acc else acc} )
		  }
		  
		  def isLeaf(s: datatype_DomainHierarchy.domainTree): Boolean = {
		    s match {
		      case datatype_DomainHierarchy.Department(a, as) => as.isEmpty
		    }
		  }
		  def printLeaf(s: datatype_DomainHierarchy.domainTree): String = {
		    s match {
		      case datatype_DomainHierarchy.Department(a, as) => assert(as.isEmpty); a.mkString
		    }
		  }
		  def isdirectEdge(s: datatype_DomainHierarchy.domainTree): String = {
		    s match {
		      case datatype_DomainHierarchy.Department(a, as) => 
		        if (as.isEmpty) "[]" else
		        	as.filter(isLeaf(_)).map(b => a.mkString+" -> "+printLeaf(b)+"\n").mkString("\n")+
		        	iter(as.filterNot(isLeaf(_)))
		    }
		  }
		  
		  iter(List(gP))
		}
}

	/*** begin DomainHierarchy ***/
	protected class DomainHierarchyNetworkModel(
    params: networkModel_Params_ext[Node,datatype_DomainHierarchy.domainName, datatype_DomainHierarchy.domainTree,Unit],
    configured_nodes: List[Node],
    description: String,
    model_breach_severity: Int
    ) extends NetworkModel[datatype_DomainHierarchy.domainName, datatype_DomainHierarchy.domainTree](
    		GENERATED.NM_DomainHierarchy.nM_LIB_DomainHierarchy[Node], params, configured_nodes, description, model_breach_severity
        )
    with DomainHierarchyGlobalsGraphizPrinter
	{
		override def prettyprint_nodeConfigToString(node: Node): String = {
		  DomainHierarchyPrettyPrinter.printDomainName(nP(node)).dropRight(1)
		}
		
		
		override def globalConfigToString: String = {
		  DomainHierarchyPrettyPrinter.printDomainTree(gP)
		}
		
		def globalConfigToGraphvizCompatibleString = pretty_globalConfigToGraphvizCompatibleString(gP)
		
	}
	/*** end DomainHierarchy ***/
	
  /*** begin DomainHierarchyTE ***/
	protected class DomainHierarchyTENetworkModel(
    params: networkModel_Params_ext[Node, GENERATED.NM_DomainHierarchyTE.node_config_ext[Unit], datatype_DomainHierarchy.domainTree,Unit],
    configured_nodes: List[Node],
    description: String,
    model_breach_severity: Int
    ) extends NetworkModel[GENERATED.NM_DomainHierarchyTE.node_config_ext[Unit], datatype_DomainHierarchy.domainTree](
    		GENERATED.NM_DomainHierarchyTE.nM_LIB_DomainHierarchyTE[Node], params, configured_nodes, description, model_breach_severity
        )
    with DomainHierarchyGlobalsGraphizPrinter
	{
		override def prettyprint_nodeConfigToString(node: Node): String = {
		  val level = GENERATED.NM_DomainHierarchyTE.level(nP(node))
		  val trust = integer_of_nat(GENERATED.NM_DomainHierarchyTE.trust(nP(node)))
		  val level_pp = DomainHierarchyPrettyPrinter.printDomainName(level).dropRight(1)
		  
		  val trust_pp = if(trust == 0) "" else
		    "  trust: "+trust
		  
		  level_pp+trust_pp
		}
		
		override def globalConfigToString: String = {
		  DomainHierarchyPrettyPrinter.printDomainTree(gP)
		}
		
		
		def globalConfigToGraphvizCompatibleString = pretty_globalConfigToGraphvizCompatibleString(gP)
		
	}
	/*** end DomainHierarchyTE ***/
	
	
	
	/*** begin BLPtrusted ***/
	protected class BLPtrustedNetworkModel(
    params: networkModel_Params_ext[Node,GENERATED.NM_BLPtrusted.node_config_ext[Unit],Unit,Unit],
    configured_nodes: List[Node],
    description: String,
    model_breach_severity: Int
    ) extends NetworkModel[GENERATED.NM_BLPtrusted.node_config_ext[Unit], Unit](
    		GENERATED.NM_BLPtrusted.nM_LIB_BLPtrusted[Node], params, configured_nodes, description, model_breach_severity
        )
	{
		override def prettyprint_nodeConfigToString(node: Node): String = {
		  import GENERATED.Code_Numeral.integer_of_nat
		  val conf = nP(node)
		  val level = integer_of_nat(GENERATED.NM_BLPtrusted.privacy_level(conf))
		  ""+level+{if (GENERATED.NM_BLPtrusted.trusted(conf)) " !trusted!" else ""}
		}
	}
	/*** end BLPtrusted ***/
	
	
	
	/*** begin CommunicationPartners ***/
	protected class CommunicationPartnersModel(
    params: networkModel_Params_ext[Node,GENERATED.NM_CommunicationPartners.node_config[Node],Unit,Unit],
    configured_nodes: List[Node],
    description: String,
    model_breach_severity: Int
    ) extends NetworkModel[GENERATED.NM_CommunicationPartners.node_config[Node], Unit](
    		GENERATED.NM_CommunicationPartners.nM_LIB_CommunicationPartners[Node], params, configured_nodes, description, model_breach_severity
        )
	{
		override def prettyprint_nodeConfigToString(node: Node): String = {
		  val conf = nP(node)
		  if (conf.toString.startsWith("Master")){
			 val aclstr = conf match {
			   case GENERATED.NM_CommunicationPartners.Master(acl) =>
			     	if (acl.isEmpty)
			     	  "-empty-"
			     	else
			     	  acl.mkString(", ")
			   case _ => sys.error("formatting error in CommunicationPartnersNetworkModel")
			   		"-formatting-error-"
			   }
			 "Master ACL:["+aclstr+"]"
		  }else
			super.prettyprint_nodeConfigToString(node)
		}
	}
	/*** end CommunicationPartners ***/
	
	/********** end concrete network models, overwriting NetworkModel for extended functionality ***********/
	
