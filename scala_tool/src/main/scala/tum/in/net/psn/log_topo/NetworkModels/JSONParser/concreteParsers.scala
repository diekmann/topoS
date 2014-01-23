package tum.in.net.psn.log_topo.NetworkModels.JSONParser

import net.liftweb.json
import net.liftweb.json.JsonParser.ParseException
import net.liftweb.json.MappingException
import tum.in.net.psn.log_topo.NetworkModels._
import GENERATED.NetworkModel_Lists_Impl_Interface.{
  nm_default, nm_eval, nm_node_props, nm_offending_flows, nm_name, 
  nm_verify_globals, nm_target_focus}
import GENERATED.NetworkModel_Lists_Impl_Interface.networkModel_packed_ext
import GENERATED.{FiniteListGraph, Nat}
import GENERATED.FiniteListGraph.{list_graph_ext, List_graph_ext}
import GENERATED.NetworkModel_Interface.{networkModel_Params_ext, NetworkModel_Params_ext, model_global_properties}
import GENERATED.datatype_DomainHierarchy
import GENERATED.Lista.distinct
import GENERATED.Code_Numeral.nat_of_integer
import tum.in.net.psn.log_topo.HOLequal_String._
import GENERATED.NM_DomainHierarchy
import GENERATED.NM_BLPbasic.nM_LIB_BLPbasic
import GENERATED.NM_BLPtrusted.nM_LIB_BLPtrusted
import GENERATED.NM_Dependability.nM_LIB_Dependability
import GENERATED.NM_DomainHierarchy.nM_LIB_DomainHierarchy
import GENERATED.NM_DomainHierarchyTE.nM_LIB_DomainHierarchyTE
import GENERATED.NM_SecGwExt.nM_LIB_SecurityGatewayExtended
import GENERATED.NM_SecurityGateway.nM_LIB_SecurityGateway
import GENERATED.NM_Sink.nM_LIB_Sink
import GENERATED.NM_Subnets.nM_LIB_Subnets
import GENERATED.NM_SubnetsInGW.nM_LIB_SubnetsInGW
import GENERATED.NM_NonInterference.nM_LIB_NonInterference
import GENERATED.NM_CommunicationPartners.nM_LIB_CommunicationPartners
import util.WarningPrinter


/*** start netmodel parsing ***/



/*** start abstract model parsing template ***/
/**
 * Template for JSON parsing of a single node configuration
 */
protected trait JSONConfigParseConfTemplate[NodeP]{
  val node: Node
  
  def try_pack = try {
    pack
  }	catch {
  	case e:MatchError => {
  	  println("MatchError trying to parse node `"+node+"'")
  	  println(e)
  	  throw e
  	  }
  }
  
  // a helper function to pack where a static match against keywords can be performed.
  // why? to print out debug infos if user enters sth wrong
  // can be used to implement pack
  final protected def pack_static_match: (Map[String, NodeP], String, String) => NodeP = 
    (values_mapping, value, fieldname_dbg) => {
    //implementation note: it is really a function and only executed when pack is called!
    // match exception is not caught if you uncurry it!
    values_mapping.get(value) match {
      case None =>
        val warn = "Not a valid value for "+fieldname_dbg+": `"+value+"'" + "\n"+
        		"valid values: "+values_mapping.keys.mkString(", ")
        util.WarningPrinter.emit_warning(warn)
        throw new MatchError(value)
      case Some(x) => x
    }
  }
    
  protected def pack: NodeP
  
  override def toString: String = ""+node+" -> ??? (unimplemented toString)"
}

/**
 * JSON parse template for a node_properties field
 */
protected trait JSONConfigParseTemplate[NodeParamsConf <: JSONConfigParseConfTemplate[NodeP], NodeP, GlobalP]	    
{
  val node_properties: List[NodeParamsConf]
  //val global_properties: GlobalP
  
  /**
   * convert parsed JSON to isabelle's NetworkModel_Params data structure
   */
  def toNetworkModel_Params_ext: networkModel_Params_ext[Node,NodeP,GlobalP,Unit]
  
  protected final val config_map: Map[Node, NodeP] = {
    val conf_nodes = node_properties.map(n => n.node)
    if(conf_nodes.distinct != conf_nodes){
      val err = "some nodes are defined several times: "+
        		conf_nodes.diff(conf_nodes.distinct).mkString(",")
      println(err)
      throw new MappingException(err)
    }
		
    Map() ++ (node_properties.map(o => (o.node, o.try_pack)))
  }
  
  protected def node_propertiesToOptionMap: (Node => Option[NodeP]) = (x => config_map.get(x))
  
  override def toString: String = "node_properties: "+config_map.toString
  
  final val configured: List[Node] = node_properties.map(o => o.node)
}

		
		
protected abstract class NetworkModelJSONParser[NodeParamsConf <: JSONConfigParseConfTemplate[NodeP], NodeP, GlobalP](
    model_packed: networkModel_packed_ext[Node, NodeP, GlobalP, Unit],
    params: String,
	expected_field_names: List[String])
{
	//name of the type of network security requirement model
	final val model_name: String = nm_name[Node, NodeP, GlobalP, Unit](model_packed).mkString
	
	//list of good keywords in the JSON file
	final protected val expected_reserved_field_names = List("node", "_comment")
	// see also expected_field_names: List[String]
	
	
	protected final val parsed_params: JSONConfigParseTemplate[NodeParamsConf, NodeP, GlobalP] = parse_JSON(params)
	
	/**
	 * returns the NetworkModel in the paresd configuration
	 */
	def model(model_description: String, model_breach_severity: Int) = new NetworkModel(
	    model_packed, 
	    parsed_params.toNetworkModel_Params_ext, 
	    parsed_params.configured, 
	    model_description,
	    model_breach_severity)
	
	//override
	protected def parse_JSON_from_template(json_parsed: json.JValue): JSONConfigParseTemplate[NodeParamsConf, NodeP, GlobalP]
	
	
	// maybe override
	protected def parse_JSON(p: String): JSONConfigParseTemplate[NodeParamsConf, NodeP, GlobalP]= {
		try{
			val json_parsed: json.JValue = json.parse(p)
			//println(json_parsed)
			try{
				val extracted = parse_JSON_from_template(json_parsed)
			
				//check that this matches the case classes
				// I.e. check that only expected fieldnames are supplied
				val json_nP = (json_parsed \\ "node_properties")
				val x = for (json.JField(fieldname, value) <- json_nP) yield (fieldname, value)
				//println("fields in the configuration: "+x.mkString(", "))
				
				for ((fieldname, _) <- x){
				  if(expected_reserved_field_names.contains(fieldname)){
				    //good fieldname
				  }else{
				    if(expected_field_names.contains(fieldname)){
				      //good fieldname for this model
				    }else{
				      val warn = "fieldname not recognized: '"+fieldname+"'" +"\n"+
				    		  "Available field names: "+expected_field_names.mkString(", ")+ "\n"+
				    		  "Reserved field names: "+expected_reserved_field_names.mkString(", ")
				      util.WarningPrinter.emit_warning(warn)
				    }
				  }
				}
				
				//println("Extracted: "+extracted)
				extracted
			} catch {
			case e: MappingException => {
			  	val cause = e.getCause() match {
			  	  case ec: java.lang.reflect.InvocationTargetException => ec.getCause()
			  	  case ec => ec
			  	}
			  	val err = ("Failed to parse config for model `"+model_name+"' "+e+", "+cause)
			  	println(err)
			  	//e.printStackTrace()
					throw new RuntimeException(err, e)
				}
			}
		} catch {
			case e:ParseException => {println("Failed to parse json for model `"+
				    model_name+"'")
					//println(e)
					throw new RuntimeException(e)
			}
		}
	}
	
	override def toString: String = "JSON TEMPLATE (NetworkModelJSONParser) "+parsed_params
}
/*** end model parsing template ***/



/*** start BLPbasic ***/
protected case class BLPbasicParamsConf(node: Node, privacy: BigInt) extends JSONConfigParseConfTemplate[Nat.nat]{
  require(privacy >= 0)
  def pack: Nat.nat = nat_of_integer(privacy)
}
protected case class BLPbasicParams(node_properties: List[BLPbasicParamsConf], global_properties: AnyRef) 
		extends JSONConfigParseTemplate[BLPbasicParamsConf, Nat.nat, Unit]{
  require(global_properties == null)
  
  // passing Unit instead of global_properties
  override def toNetworkModel_Params_ext: networkModel_Params_ext[Node,Nat.nat,Unit,Unit] =
    new NetworkModel_Params_ext[Node, Nat.nat, Unit, Unit](node_propertiesToOptionMap, (), ())
}


protected class BLPbasicParser(params:String) extends 
	NetworkModelJSONParser[BLPbasicParamsConf, Nat.nat, Unit](
	    nM_LIB_BLPbasic[Node], 
	    params, List("privacy"))
{
  override def parse_JSON_from_template(json_parsed: json.JValue): BLPbasicParams = json_parsed.extract[BLPbasicParams]
}
/*** end BLPbasic   ***/


/*** start BLPtrusted ***/
protected case class BLPtrustedParamsConf(node: Node, privacy: BigInt, trusted: Option[Boolean]) 
	extends JSONConfigParseConfTemplate[GENERATED.NM_BLPtrusted.node_config_ext[Unit]]{
  require(privacy >= 0)
  def pack = GENERATED.NM_BLPtrusted.Node_config_ext[Unit](nat_of_integer(privacy), trusted.getOrElse(false), ())
}
protected case class BLPtrustedParams(node_properties: List[BLPtrustedParamsConf], global_properties: AnyRef) 
		extends JSONConfigParseTemplate[BLPtrustedParamsConf, GENERATED.NM_BLPtrusted.node_config_ext[Unit], Unit]{
  require(global_properties == null)
  
  
  // passing Unit instead of global_properties
  override def toNetworkModel_Params_ext: networkModel_Params_ext[Node,GENERATED.NM_BLPtrusted.node_config_ext[Unit],Unit,Unit] =
    new NetworkModel_Params_ext[Node, GENERATED.NM_BLPtrusted.node_config_ext[Unit], Unit, Unit](node_propertiesToOptionMap, (), ())
}


protected class BLPtrustedParser(params:String) extends 
	NetworkModelJSONParser[BLPtrustedParamsConf, GENERATED.NM_BLPtrusted.node_config_ext[Unit], Unit](
	    nM_LIB_BLPtrusted[Node], 
	    params, List("privacy", "trusted"))
{
	override def model(description: String, model_breach_severity: Int) = new BLPtrustedNetworkModel(
	    parsed_params.toNetworkModel_Params_ext, 
	    parsed_params.configured, 
	    description,
	    model_breach_severity)
  
	override def parse_JSON_from_template(json_parsed: json.JValue): BLPtrustedParams = json_parsed.extract[BLPtrustedParams]
}
/*** end BLPtrusted   ***/


/*** start Dependability ***/
protected case class DependabilityParamsConf(node: Node, dependability_level: BigInt) extends JSONConfigParseConfTemplate[Nat.nat]{
  require(dependability_level >= 0)
  def pack: Nat.nat = nat_of_integer(dependability_level)
  
	override def toString: String = ""+node+" -> "+dependability_level+""
}
protected case class DependabilityParams(node_properties: List[DependabilityParamsConf], global_properties: AnyRef) 
		extends JSONConfigParseTemplate[DependabilityParamsConf, Nat.nat, Unit]{
  require(global_properties == null)
  
  // passing Unit instead of global_properties
  override def toNetworkModel_Params_ext: networkModel_Params_ext[Node,Nat.nat,Unit,Unit] =
    new NetworkModel_Params_ext[Node, Nat.nat, Unit, Unit](node_propertiesToOptionMap, (), ())
}


protected class DependabilityParser(params:String) extends 
	NetworkModelJSONParser[DependabilityParamsConf, Nat.nat, Unit](
	    nM_LIB_Dependability[Node], 
	    params, List("dependability_level"))
{ 
	override def parse_JSON_from_template(json_parsed: json.JValue): DependabilityParams = json_parsed.extract[DependabilityParams]
}
/*** end Dependability ***/


/*** start DomainHierarchy ***/
protected case class DomainHierarchyNodeParamsConf(node: Node, position: List[String]) 
extends JSONConfigParseConfTemplate[datatype_DomainHierarchy.domainName]{
  def pack: datatype_DomainHierarchy.domainName = {
    
    //LIFT JSON possible bug. when inserting null, I get the empty list
    val pos = if (position == List()){
      println(node+": position is empty, inserting default value\nThis is a possible configuration error!")
      new datatype_DomainHierarchy.Unassigned()
    } else {
    def iter(ls: List[String]): datatype_DomainHierarchy.domainName = if (ls.isEmpty) new datatype_DomainHierarchy.Leaf()
    		else datatype_DomainHierarchy.Dept(ls.head.toList, iter(ls.tail))
    iter(position)
    }
    pos
  }
	//override def toString: String = ""+node+" -> "+position+""
}

protected case class DomainHierarchyGlobalParams(division: String, sub_divisions: List[DomainHierarchyGlobalParams]){
  def pack: datatype_DomainHierarchy.domainTree = {
    def iter(ls: List[DomainHierarchyGlobalParams]): List[datatype_DomainHierarchy.domainTree] = 
    		if (ls.isEmpty) List()
    		else ls.head.pack :: iter(ls.tail)
    		
    datatype_DomainHierarchy.Department(division.toList, iter(sub_divisions))
  }
	//override def toString: String = "`"+division+"' > ["+sub_divisions+"]"
}

protected case class DomainHierarchyParams(node_properties: List[DomainHierarchyNodeParamsConf], global_properties: DomainHierarchyGlobalParams) 
		extends JSONConfigParseTemplate[DomainHierarchyNodeParamsConf, datatype_DomainHierarchy.domainName, datatype_DomainHierarchy.domainTree]{
  
  require(global_properties ne null, "global properties in DomainHierarchy config must be set!")
  override def toNetworkModel_Params_ext: 
  	networkModel_Params_ext[Node, datatype_DomainHierarchy.domainName,datatype_DomainHierarchy.domainTree,Unit] =
    	new NetworkModel_Params_ext(node_propertiesToOptionMap, global_properties.pack, ())
  
  
  override def toString: String = "DomainHierarchyParams\n  node_properties: "+config_map.toString+
  	"\n  global_properties: "+global_properties
}


protected class DomainHierarchyParser(params:String) extends 
	NetworkModelJSONParser[DomainHierarchyNodeParamsConf, datatype_DomainHierarchy.domainName, datatype_DomainHierarchy.domainTree](
	    nM_LIB_DomainHierarchy[Node],
	    params, List("position"))
{
	override def model(description: String, model_breach_severity: Int) = new DomainHierarchyNetworkModel(
	    parsed_params.toNetworkModel_Params_ext, 
	    parsed_params.configured, 
	    description,
	    model_breach_severity)
  
	override def parse_JSON_from_template(json_parsed: json.JValue): DomainHierarchyParams = json_parsed.extract[DomainHierarchyParams]
}

/*** end DomainHierarchy ***/

/*** start DomainHierarchyTE ***/
protected case class DomainHierarchyTENodeParamsConf(node: Node, position: List[String], trust: Option[BigInt]) 
extends JSONConfigParseConfTemplate[GENERATED.NM_DomainHierarchyTE.node_config_ext[Unit]]{
  def pack: GENERATED.NM_DomainHierarchyTE.node_config_ext[Unit] = {
    require(trust.getOrElse[BigInt](0) >= 0)
    
    //LIFT JSON possible bug. when inserting null, I get the empty list
    val pos = if (position == List()){
      println(node+": position is empty, inserting default value")
      println("This is a possible configuration error!")
      new datatype_DomainHierarchy.Unassigned()
    } else {
      def iter(ls: List[String]): datatype_DomainHierarchy.domainName = if (ls.isEmpty) new datatype_DomainHierarchy.Leaf()
    		else datatype_DomainHierarchy.Dept(ls.head.toList, iter(ls.tail))
    iter(position)
    }
    require(trust.getOrElse[BigInt](0) >= 0)
    GENERATED.NM_DomainHierarchyTE.Node_config_ext[Unit](pos, nat_of_integer(trust.getOrElse[BigInt](0)), ())
  }
}

// reuse normal DomainHierarchy
//protected case class DomainHierarchyGlobalParams(division: String, sub_divisions: List[DomainHierarchyGlobalParams]){


protected case class DomainHierarchyTEParams(node_properties: List[DomainHierarchyTENodeParamsConf], global_properties: DomainHierarchyGlobalParams) 
		extends JSONConfigParseTemplate[DomainHierarchyTENodeParamsConf, GENERATED.NM_DomainHierarchyTE.node_config_ext[Unit], 
		  datatype_DomainHierarchy.domainTree]
{
  require(global_properties ne null, "global properties in DomainHierarchy config must be set!")
  override def toNetworkModel_Params_ext: 
  	networkModel_Params_ext[Node, GENERATED.NM_DomainHierarchyTE.node_config_ext[Unit], datatype_DomainHierarchy.domainTree,Unit] =
    	new NetworkModel_Params_ext(node_propertiesToOptionMap, global_properties.pack, ())
}


protected class DomainHierarchyTEParser(params:String) extends 
	NetworkModelJSONParser[DomainHierarchyTENodeParamsConf, GENERATED.NM_DomainHierarchyTE.node_config_ext[Unit], datatype_DomainHierarchy.domainTree](
	    nM_LIB_DomainHierarchyTE[Node],
	    params, List("position", "trust"))
{
	override def model(description: String, model_breach_severity: Int) = new DomainHierarchyTENetworkModel(
	    parsed_params.toNetworkModel_Params_ext, 
	    parsed_params.configured, 
	    description,
	    model_breach_severity)
  
	override def parse_JSON_from_template(json_parsed: json.JValue) = json_parsed.extract[DomainHierarchyTEParams]
}

/*** end DomainHierarchyTE ***/

/*** start Subnets ***/
protected case class SubnetsParamsConf(node: Node, member_type: String, member: BigInt) 
	extends JSONConfigParseConfTemplate[GENERATED.NM_Subnets.subnets]{
  def printOnError(m: String): Nothing = { println(m); throw new RuntimeException(m) }
  
  def pack = member_type match {
    case "Unassigned" => if(member != null) printOnError("member must be null for Unassigned") else new GENERATED.NM_Subnets.Unassigned()
    case "BorderRouter" => 
        require(member >= 0)
        GENERATED.NM_Subnets.BorderRouter(nat_of_integer(member))
    case "Subnet" =>
        require(member >= 0)
        GENERATED.NM_Subnets.Subnet(nat_of_integer(member))
  }
}
protected case class SubnetsParams(node_properties: List[SubnetsParamsConf], global_properties: AnyRef) 
		extends JSONConfigParseTemplate[SubnetsParamsConf, GENERATED.NM_Subnets.subnets, Unit]{
  require(global_properties == null)
  
  // passing Unit instead of global_properties
  override def toNetworkModel_Params_ext =
    new NetworkModel_Params_ext[Node, GENERATED.NM_Subnets.subnets, Unit, Unit](node_propertiesToOptionMap, (), ())
}


protected class SubnetsParser(params:String) extends 
	NetworkModelJSONParser[SubnetsParamsConf, GENERATED.NM_Subnets.subnets, Unit](
	    nM_LIB_Subnets[Node], 
	    params, List("member_type", "member"))
{
	override def parse_JSON_from_template(json_parsed: json.JValue) = json_parsed.extract[SubnetsParams]
}
/*** end Subnets   ***/

/*** start SecurityGateway ***/
protected case class SecurityGatewayParamsConf(node: Node, member_type: String) 
	extends JSONConfigParseConfTemplate[GENERATED.NM_SecurityGateway.secgw_member]{
  def pack = pack_static_match(Map(
    "Unassigned" -> new GENERATED.NM_SecurityGateway.Unassigned(),
    "DomainMember" -> new GENERATED.NM_SecurityGateway.DomainMember(),
    "SecurityGateway" -> new GENERATED.NM_SecurityGateway.SecurityGateway()
    ), member_type, "member_type")
  
}
protected case class SecurityGatewayParams(node_properties: List[SecurityGatewayParamsConf], global_properties: AnyRef) 
		extends JSONConfigParseTemplate[SecurityGatewayParamsConf, GENERATED.NM_SecurityGateway.secgw_member, Unit]{
  require(global_properties == null)
  
  // passing Unit instead of global_properties
  override def toNetworkModel_Params_ext =
    new NetworkModel_Params_ext[Node, GENERATED.NM_SecurityGateway.secgw_member, Unit, Unit](node_propertiesToOptionMap, (), ())
}


protected class SecurityGatewayParser(params:String) extends 
	NetworkModelJSONParser[SecurityGatewayParamsConf, GENERATED.NM_SecurityGateway.secgw_member, Unit](
	    nM_LIB_SecurityGateway[Node], 
	    params, List("member_type"))
{
	override def parse_JSON_from_template(json_parsed: json.JValue) = json_parsed.extract[SecurityGatewayParams]
}
/*** end SecurityGateway   ***/

/*** start SecurityGatewayExtended ***/
// name is SecGwExt because other name is too long (does not compile)
protected case class SecurityGatewayExtendedParamsConf(node: Node, member_type: String) 
	extends JSONConfigParseConfTemplate[GENERATED.NM_SecGwExt.secgw_member]{
  def pack = pack_static_match(Map(
    "Unassigned" -> new GENERATED.NM_SecGwExt.Unassigned(),
    "DomainMember" -> new GENERATED.NM_SecGwExt.DomainMember(),
    "AccessibleMember" -> new GENERATED.NM_SecGwExt.AccessibleMember(),
    "SecurityGateway" -> new GENERATED.NM_SecGwExt.SecurityGateway(),
    "SecurityGatewayIN" -> new GENERATED.NM_SecGwExt.SecurityGatewayIN()
    ), member_type, "member_type")
 
}
protected case class SecurityGatewayExtendedParams(node_properties: List[SecurityGatewayExtendedParamsConf], global_properties: AnyRef) 
		extends JSONConfigParseTemplate[SecurityGatewayExtendedParamsConf, GENERATED.NM_SecGwExt.secgw_member, Unit]{
  require(global_properties == null)
  
  // passing Unit instead of global_properties
  override def toNetworkModel_Params_ext =
    new NetworkModel_Params_ext[Node, GENERATED.NM_SecGwExt.secgw_member, Unit, Unit](node_propertiesToOptionMap, (), ())
}


protected class SecurityGatewayExtendedParser(params:String) extends 
	NetworkModelJSONParser[SecurityGatewayExtendedParamsConf, GENERATED.NM_SecGwExt.secgw_member, Unit](
	    nM_LIB_SecurityGatewayExtended[Node], 
	    params, List("member_type"))
{
	override def parse_JSON_from_template(json_parsed: json.JValue) = json_parsed.extract[SecurityGatewayExtendedParams]
}
/*** end SecurityGatewayExtended   ***/


/*** start Sink ***/
protected case class SinkParamsConf(node: Node, member_type: String) 
	extends JSONConfigParseConfTemplate[GENERATED.NM_Sink.node_config]{
  def pack = member_type match {
    case "Unassigned" => new GENERATED.NM_Sink.Unassigned()
    case "Sink" => new GENERATED.NM_Sink.Sink()
    case "SinkPool" => new GENERATED.NM_Sink.SinkPool()
  }
}
protected case class SinkParams(node_properties: List[SinkParamsConf], global_properties: AnyRef) 
		extends JSONConfigParseTemplate[SinkParamsConf, GENERATED.NM_Sink.node_config, Unit]{
  require(global_properties == null)
  
  // passing Unit instead of global_properties
  override def toNetworkModel_Params_ext =
    new NetworkModel_Params_ext[Node, GENERATED.NM_Sink.node_config, Unit, Unit](node_propertiesToOptionMap, (), ())
}


protected class SinkParser(params:String) extends 
	NetworkModelJSONParser[SinkParamsConf, GENERATED.NM_Sink.node_config, Unit](
	    nM_LIB_Sink[Node], 
	    params, List("member_type"))
{
	override def parse_JSON_from_template(json_parsed: json.JValue) = json_parsed.extract[SinkParams]
}
/*** end Sink   ***/


/*** start NonInterference ***/
protected case class NonInterferenceParamsConf(node: Node, host_type: String) 
	extends JSONConfigParseConfTemplate[GENERATED.NM_NonInterference.node_config]{
  def pack = host_type match {
    case "Interfering" => new GENERATED.NM_NonInterference.Interfering()
    case "Unrelated" => new GENERATED.NM_NonInterference.Unrelated()
  }
}
protected case class NonInterferenceParams(node_properties: List[NonInterferenceParamsConf], global_properties: AnyRef) 
		extends JSONConfigParseTemplate[NonInterferenceParamsConf, GENERATED.NM_NonInterference.node_config, Unit]{
  require(global_properties == null)
  
  // passing Unit instead of global_properties
  override def toNetworkModel_Params_ext =
    new NetworkModel_Params_ext[Node, GENERATED.NM_NonInterference.node_config, Unit, Unit](node_propertiesToOptionMap, (), ())
}


protected class NonInterferenceParser(params:String) extends 
	NetworkModelJSONParser[NonInterferenceParamsConf, GENERATED.NM_NonInterference.node_config, Unit](
	    nM_LIB_NonInterference[Node], 
	    params, List("host_type"))
{
	override def parse_JSON_from_template(json_parsed: json.JValue) = json_parsed.extract[NonInterferenceParams]
}
/*** end NonInterference   ***/


/*** start SubnetsInGW ***/
protected case class SubnetsInGWParamsConf(node: Node, member_type: String) 
	extends JSONConfigParseConfTemplate[GENERATED.NM_SubnetsInGW.subnets]{
  def pack = member_type match {
    case "Unassigned" => new GENERATED.NM_SubnetsInGW.Unassigned()
    case "InboundGateway" => new GENERATED.NM_SubnetsInGW.InboundGateway()
    case "Member" => new GENERATED.NM_SubnetsInGW.Member()
  }
}
protected case class SubnetsInGWParams(node_properties: List[SubnetsInGWParamsConf], global_properties: AnyRef) 
		extends JSONConfigParseTemplate[SubnetsInGWParamsConf, GENERATED.NM_SubnetsInGW.subnets, Unit]{
  require(global_properties == null)
  
  // passing Unit instead of global_properties
  override def toNetworkModel_Params_ext =
    new NetworkModel_Params_ext[Node, GENERATED.NM_SubnetsInGW.subnets, Unit, Unit](node_propertiesToOptionMap, (), ())
}


protected class SubnetsInGWParser(params:String) extends 
	NetworkModelJSONParser[SubnetsInGWParamsConf, GENERATED.NM_SubnetsInGW.subnets, Unit](
	    nM_LIB_SubnetsInGW[Node], 
	    params, List("member_type"))
{
	override def parse_JSON_from_template(json_parsed: json.JValue) = json_parsed.extract[SubnetsInGWParams]
}
/*** end SubnetsInGW   ***/



/*** start CommunicationPartners ***/
protected case class CommunicationPartnersParamsConf(node: Node, member_type: String, acl: Option[List[String]]) 
	extends JSONConfigParseConfTemplate[GENERATED.NM_CommunicationPartners.node_config[Node]]{
  def pack = member_type match {
    case "DontCare" =>
      require(acl == None, "Only 'Master' nodes may have an 'acl'")
      new GENERATED.NM_CommunicationPartners.DontCare()
    case "Care" =>
      require(acl == None, "Only 'Master' nodes may have an 'acl'")
      new GENERATED.NM_CommunicationPartners.Care()
    case "Master" => 
      val my_acl: List[Node] = acl match {
		  case Some(l) => l 
		  case None => throw new RuntimeException("CommunicationPartners: a 'Master' node needs an 'acl'")
		}
      new GENERATED.NM_CommunicationPartners.Master(my_acl)
    case x => 
      util.WarningPrinter.emit_warning("For member_type, only the following is allowed: DontCare, Care, Master")
      throw new MatchError(x)
  }
}
protected case class CommunicationPartnersParams(node_properties: List[CommunicationPartnersParamsConf], global_properties: AnyRef) 
		extends JSONConfigParseTemplate[CommunicationPartnersParamsConf, GENERATED.NM_CommunicationPartners.node_config[Node], Unit]{
  require(global_properties == null)
  
  // passing Unit instead of global_properties
  override def toNetworkModel_Params_ext =
    new NetworkModel_Params_ext[Node, GENERATED.NM_CommunicationPartners.node_config[Node], Unit, Unit](node_propertiesToOptionMap, (), ())
}


protected class CommunicationPartnersParser(params:String) extends 
	NetworkModelJSONParser[CommunicationPartnersParamsConf, GENERATED.NM_CommunicationPartners.node_config[Node], Unit](
	    nM_LIB_CommunicationPartners[Node], 
	    params, List("member_type", "acl"))
{
	override def model(description: String, model_breach_severity: Int) = new CommunicationPartnersModel(
	    parsed_params.toNetworkModel_Params_ext, 
	    parsed_params.configured, 
	    description,
	    model_breach_severity)
	
	override def parse_JSON_from_template(json_parsed: json.JValue) = json_parsed.extract[CommunicationPartnersParams]
}
/*** end CommunicationPartners   ***/
