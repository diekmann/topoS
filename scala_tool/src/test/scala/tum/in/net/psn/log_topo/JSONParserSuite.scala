package tum.in.net.psn.log_topo

import org.scalatest.FlatSpec


import NetworkModels.{NetGraph, NetworkModelAbstract}


class JSONParserSuite extends FlatSpec {
  
	import NetworkModels.JSONParser
	
	val testedModels: scala.collection.mutable.Set[String] = scala.collection.mutable.Set()
	
	"A complete JSON security requirement must parse" must "BLPbasic" in {
	  val json = """{"model_type": "BLPbasic",
			 "model_description": "Privacy for employees", 
	     "model_breach_severity": 10,
			 "model_params":{
			    "node_properties": [
				  {"node":"Statistics", "privacy":3}
				  {"node":"SensorSink", "privacy":3},
				  {"node":"PresenceSensor", "privacy":2}, 
				  {"node":"Webcam", "privacy":3}
				  ], 
			    "global_properties":null
			    }
			}"""
	  val nodes = Map(("Statistics", 3), ("SensorSink", 3), ("PresenceSensor", 2), ("Webcam", 3))
	  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  assert(nm.description === "Privacy for employees")
	  assert(nm.isConfiguredNode("Statistics"))
	  assert(nodes.keys.forall(nm.isConfiguredNode(_)))
	  assert(nodes.keys.forall(n => nm.nodeConfigToString(n) == nodes(n).toString))
	  assert(nm.isIFS)
	  assert(!nm.isACM)
	  assert(nm.model_type === "BLPbasic")
	  
	  testedModels.add(nm.model_type)
	}
	
	it must "BLPtrusted" in {
	  val json = """{"model_type": "BLPtrusted",
			 "model_description": "Privacy for employees, exporting aggregated data", 
	     "model_breach_severity": 10,
			 "model_params":{
			    "node_properties": [
				  {"node":"Statistics", "privacy":3, "trusted": false}
				  {"node":"SensorSink", "privacy":2, "trusted": true},
				  {"node":"PresenceSensor", "privacy":2, "trusted": false}, 
				  {"node":"Webcam", "privacy":3, "trusted": false}
				  ], 
			    "global_properties":null
			    }
			}"""
	  val nodes = Map(("Statistics", "3"), ("SensorSink", "2 !trusted!"), ("PresenceSensor", "2"), ("Webcam", "3"))
	  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  assert(nm.description === "Privacy for employees, exporting aggregated data")
	  assert(nodes.keys.forall(nm.isConfiguredNode(_)))
	  assert(nm.nodeConfigToString("SensorSink") === nodes("SensorSink"))
	  assert(nodes.keys.forall(n => nm.nodeConfigToString(n) == nodes(n)))
	  assert(nm.isIFS)
	  assert(!nm.isACM)
	  assert(nm.model_type === "BLPtrusted")
	  
	  testedModels.add(nm.model_type)
	}
	
	it must "BLPtrusted with less config" in {
	  val json = """{"model_type": "BLPtrusted",
			 "model_description": "Privacy for employees, exporting aggregated data", 
	     "model_breach_severity": 10,
			 "model_params":{
			    "node_properties": [
				  {"node":"Statistics", "privacy":3}
				  {"node":"SensorSink", "privacy":2, "trusted": true},
				  {"node":"PresenceSensor", "privacy":2}, 
				  {"node":"Webcam", "privacy":3}
				  ], 
			    "global_properties":null
			    }
			}"""
	  val nodes = Map(("Statistics", "3"), ("SensorSink", "2 !trusted!"), ("PresenceSensor", "2"), ("Webcam", "3"))
	  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  assert(nm.description === "Privacy for employees, exporting aggregated data")
	  assert(nodes.keys.forall(nm.isConfiguredNode(_)))
	  assert(nm.nodeConfigToString("SensorSink") === nodes("SensorSink"))
	  assert(nodes.keys.forall(n => nm.nodeConfigToString(n) == nodes(n)))
	  assert(nm.isIFS)
	  assert(!nm.isACM)
	  assert(nm.model_type === "BLPtrusted")
	  
	  testedModels.add(nm.model_type)
	}
	
	
	it must "Subnets" in {
	  val json = """{"model_type": "Subnets",
			 "model_description": "we subnet the whole fab!", 
	     "model_breach_severity": 10,
			 "model_params":{
			    "node_properties": [
				  {"node":"Node1", "member_type": "Subnet", "member": 1},
	  			{"node":"Node2", "member_type": "Subnet", "member": 2},
	  			{"node":"Node3", "member_type": "BorderRouter", "member": 1},
	  			{"node":"Node4", "member_type": "BorderRouter", "member": 2}
				  ], 
			    "global_properties":null
			    }
			}"""
	  val nodes = Map(("Node1", "Subnet(1)"), ("Node2", "Subnet(2)"),
	      ("Node3", "BorderRouter(1)"), ("Node4", "BorderRouter(2)"))
	  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  assert(nm.model_type === "Subnets")
	  assert(nm.description === "we subnet the whole fab!")
	  assert(nodes.keys.forall(nm.isConfiguredNode(_)))
	  nodes.keys.foreach(n => assert(nm.nodeConfigToString(n) === nodes(n)))
	  assert(!nm.isIFS)
	  assert(nm.isACM)
	  
	  testedModels.add(nm.model_type)
	}
	
	it must "throw exception on double configuration" in {
		val json = """{"model_type": "Subnets",
		 "model_description": "we subnet the whole fab!", 
     "model_breach_severity": 10,
		 "model_params":{
		    "node_properties": [
			  {"node":"Node1", "member_type": "Subnet", "member": 1},
  			{"node":"Node1", "member_type": "Subnet", "member": 2},
			  {"node":"Node2", "member_type": "Subnet", "member": 2},
  			{"node":"Node2", "member_type": "Subnet", "member": 2}
			  ], 
		    "global_properties":null
		    }
		}"""
	  val thrown = intercept[RuntimeException] {
	  	val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  }
	  assert(thrown.getMessage.contains("some nodes are defined several times: Node1,Node2"))
	  assert(thrown.getMessage.contains("`Subnets'"))
	}
	
	
	it must "SecurityGatewayExtended" in {
	  val json = """{"model_type": "SecurityGatewayExtended",
			 "model_description": "SecurityGatewayExtended Requirements", 
	     "model_breach_severity": 98,
			 "model_params":{
			    "node_properties": [
				  {"node":"n1",  "member_type":"SecurityGatewayIN"},
	  			{"node":"n2", "member_type":"DomainMember"},
	  			{"node":"n3", "member_type":"AccessibleMember"},
	  			{"node":"n4", "member_type":"Unassigned"},
	  			{"node":"n5", "member_type":"SecurityGateway"}
				  ], 
			    "global_properties":null
			    }
			}"""
	  val nodes = Map(("n1", "SecurityGatewayIN"), 
	      ("n2", "DomainMember"), ("n3", "AccessibleMember"), 
	      ("n4", "Unassigned"), ("n5", "SecurityGateway"))
	  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  assert(nm.description === "SecurityGatewayExtended Requirements")
	  assert(nodes.keys.forall(nm.isConfiguredNode(_)))
	  assert(nm.nodeConfigToString("n99") === "⊥")
	  assert(nodes.keys.forall(n => nm.nodeConfigToString(n) == nodes(n)))
	  assert(nm.isACM)
	  assert(!nm.isIFS)
	  assert(nm.model_type === "SecurityGatewayExtended")
	  
	  testedModels.add(nm.model_type)
	}
	
		it must "SecurityGateway" in {
	  val json = """{"model_type": "SecurityGateway",
			 "model_description": "SecurityGateway Requirements", 
	     "model_breach_severity": 98,
			 "model_params":{
			    "node_properties": [
	  			{"node":"n2", "member_type":"DomainMember"},
	  			{"node":"n4", "member_type":"Unassigned"},
	  			{"node":"n5", "member_type":"SecurityGateway"}
				  ], 
			    "global_properties":null
			    }
			}"""
	  val nodes = Map(("n2", "DomainMember"), ("n4", "Unassigned"), ("n5", "SecurityGateway"))
	  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  assert(nm.description === "SecurityGateway Requirements")
	  assert(nodes.keys.forall(nm.isConfiguredNode(_)))
	  assert(nm.nodeConfigToString("n99") === "⊥")
	  assert(nodes.keys.forall(n => nm.nodeConfigToString(n) == nodes(n)))
	  assert(nm.isACM)
	  assert(!nm.isIFS)
	  assert(nm.model_type === "SecurityGateway")
	  
	  testedModels.add(nm.model_type)
	}
	
	it must "DomainHierarchyTE" in {
	  val json = """{"model_type": "DomainHierarchyTE",
			 "model_description": "DomainHierarchyTE Requirements", 
	     "model_breach_severity": 98,
			 "model_params":{
			    "node_properties": [
				  {"node":"n1",  "position":["TUM", "i99"]},
	  			{"node":"n2", "position":["TUM", "i8"]},
	  			{"node":"n3", "position":["TUM"], "trust": 1},
	  			{"node":"n4", "position":["TUM"], "trust": 5},
	  			{"node":"n5", "position":["TUM"], "trust": 0}
				  ], 
			    "global_properties":{"division": "TUM", "sub_divisions":[{"division": "i8", "sub_divisions":[]}]}
			    }
			}"""
	  val nodes = Map(("n1", "TUM-i99"), 
	      ("n2", "TUM-i8"), ("n3", "TUM  trust: 1"), ("n4", "TUM  trust: 5"), ("n5", "TUM"))
	  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  assert(nm.description === "DomainHierarchyTE Requirements")
	  assert(nodes.keys.forall(nm.isConfiguredNode(_)))
	  assert(nm.nodeConfigToString("n99") === "⊥")
	  nodes.keys.foreach(n => assert(nm.nodeConfigToString(n) === nodes(n)))
	  assert(nm.isACM)
	  assert(!nm.isIFS)
	  assert(nm.model_type === "DomainHierarchyTE")
	  
	  //check verify globals, n1 is illegal
	  assert(nm.verify_globals(NetGraph(List("n1"), List())) === false)
	  assert(nm.verify_globals(NetGraph(List("n2"), List())) === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4", "n5"), List())) === false)
	  assert(nm.eval(NetGraph(List("n2", "n3", "n4", "n5"), List())) === true)
	  
	  testedModels.add(nm.model_type)
	}
	
	it must "DomainHierarchy" in {
	  val json = """{"model_type": "DomainHierarchy",
			 "model_description": "DomainHierarchy Requirements", 
	     "model_breach_severity": 98,
			 "model_params":{
			    "node_properties": [
				  {"node":"n1",  "position":["LMU"]},
	  			{"node":"n2", "position":["TUM", "TUM", "i8"]},
	  			{"node":"n3", "position":["TUM", "TUM"]},
	  			{"node":"n4", "position":["TUM", "TUM", "TUM"]}
				  ], 
			    "global_properties":{"division": "TUM", "sub_divisions":[{"division": "TUM", "sub_divisions":[{"division": "i8", "sub_divisions":[]}]}]}
			    }
			}"""
	  val nodes = Map(("n1", "LMU"), 
	      ("n2", "TUM-TUM-i8"), ("n3", "TUM-TUM"), ("n4", "TUM-TUM-TUM"))
	  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  assert(nm.description === "DomainHierarchy Requirements")
	  assert(nodes.keys.forall(nm.isConfiguredNode(_)))
	  assert(nm.nodeConfigToString("n99") === "⊥")
	  nodes.keys.foreach(n => assert(nm.nodeConfigToString(n) === nodes(n)))
	  assert(nm.isACM)
	  assert(!nm.isIFS)
	  assert(nm.model_type === "DomainHierarchy")
	  
	  //check verify globals, n1 and n4 is illegal
	  assert(nm.verify_globals(NetGraph(List("n1"), List())) === false)
	  assert(nm.verify_globals(NetGraph(List("n4"), List())) === false)
	  assert(nm.verify_globals(NetGraph(List("n3"), List())) === true)
	  assert(nm.verify_globals(NetGraph(List("n2"), List())) === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n5"), List())) === false)
	  assert(nm.eval(NetGraph(List("n2", "n3", "n4", "n5"), List())) === false)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4", "n5"), List())) === false)
	  assert(nm.eval(NetGraph(List("n2", "n3", "n5"), List())) === true)
	  
	  testedModels.add(nm.model_type)
	}
	
	it must "SubnetsInGW" in {
	  val json = """{"model_type": "SubnetsInGW",
			 "model_description": "SubnetsInGW Requirements", 
	     "model_breach_severity": 98,
			 "model_params":{
			    "node_properties": [
				  {"node":"n1", "member_type":"Member"},
	  			{"node":"n2", "member_type":"InboundGateway"},
	  			{"node":"n3", "member_type":"Unassigned"}
				  ], 
			    "global_properties": null
			    }
			}"""
	  val nodes = Map(("n1", "Member"), 
	      ("n2", "InboundGateway"), ("n3", "Unassigned"))
	  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  assert(nm.description === "SubnetsInGW Requirements")
	  assert(nodes.keys.forall(nm.isConfiguredNode(_)))
	  assert(nm.nodeConfigToString("n99") === "⊥")
	  assert(nodes.keys.forall(n => nm.nodeConfigToString(n) == nodes(n)))
	  assert(nm.isACM)
	  assert(!nm.isIFS)
	  assert(nm.model_type === "SubnetsInGW")
	  
	  testedModels.add(nm.model_type)
	}
		
		
		
    it must "NonInterference" in {
	  val json = """{"model_type": "NonInterference",
		"model_description": "NonInterference Requirements", 
	    "model_breach_severity": 11,
			 "model_params":{
			    "node_properties": [
				  {"node":"n1",  "host_type":"Interfering"},
	  			{"node":"n2", "host_type":"Unrelated"},
	  			{"node":"n3", "host_type":"Unrelated"},
	  			{"node":"n4", "host_type":"Interfering"}
				  ], 
			    "global_properties":null
			    }
			}"""
	  val nodes = Map(("n1", "Interfering"), 
	      ("n2", "Unrelated"), ("n3", "Unrelated"), ("n4", "Interfering"))
	  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  assert(nm.description === "NonInterference Requirements")
	  assert(nodes.keys.forall(nm.isConfiguredNode(_)))
	  assert(nm.nodeConfigToString("n99") === "⊥")
	  assert(nodes.keys.forall(n => nm.nodeConfigToString(n) == nodes(n)))
	  assert(!nm.isACM)
	  assert(nm.isIFS)
	  assert(nm.model_type === "NonInterference")
	  
	  assert(nm.verify_globals(NetGraph(List("n2"), List())) === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4"), List(("n1", "n2"), ("n2", "n1")))) 
	      === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4"), 
	      List(("n2", "n3"), ("n3", "n2"), ("n3", "n4") ))) 
	      === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4"), 
	      List(("n2", "n1"), ("n2", "n3"), ("n3", "n2"), ("n3", "n4") ))) 
	      === false)
	  
	  testedModels.add(nm.model_type)
	}
	
	
    it must "Sink" in {
	  val json = """{"model_type": "Sink",
		"model_description": "Sink Requirements", 
	    "model_breach_severity": 11,
			 "model_params":{
			    "node_properties": [
				  {"node":"n1",  "member_type":"Sink"},
	  			{"node":"n2", "member_type":"Sink"},
	  			{"node":"n3", "member_type":"SinkPool"},
	  			{"node":"n4", "member_type":"SinkPool"}
				  ], 
			    "global_properties":null
			    }
			}"""
	  val nodes = Map(("n1", "Sink"), 
	      ("n2", "Sink"), ("n3", "SinkPool"), ("n4", "SinkPool"))
	  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  assert(nm.description === "Sink Requirements")
	  assert(nodes.keys.forall(nm.isConfiguredNode(_)))
	  assert(nm.nodeConfigToString("n99") === "⊥")
	  assert(nodes.keys.forall(n => nm.nodeConfigToString(n) == nodes(n)))
	  assert(!nm.isACM)
	  assert(nm.isIFS)
	  assert(nm.model_type === "Sink")
	  
	  assert(nm.verify_globals(NetGraph(List("n2"), List())) === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4"), List(("n3", "n4"), ("n4", "n3")))) 
	      === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4"), 
	      List(("n3", "n1")))) 
	      === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4", "n99", "n42"), 
	      List(("n99", "n1"), ("n99", "n3"), ("n99", "n42")))) 
	      === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4"), 
	      List(("n1", "n3") ))) 
	      === false)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4", "n99"), 
	      List(("n1", "n99") ))) 
	      === false)
	  
	  testedModels.add(nm.model_type)
	}
    
    
	
    it must "Dependability" in {
	  val json = """{"model_type": "Dependability",
		"model_description": "Dependability Requirements", 
	    "model_breach_severity": 11,
			 "model_params":{
			    "node_properties": [
				  {"node":"n1",  "dependability_level":2},
	  			{"node":"n2", "dependability_level":3},
	  			{"node":"n3", "dependability_level":1},
	  			{"node":"n4", "dependability_level":0}
				  ], 
			    "global_properties":null
			    }
			}"""
	  val nodes = Map(("n1", "2"), 
	      ("n2", "3"), ("n3", "1"), ("n4", "0"))
	  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  assert(nm.description === "Dependability Requirements")
	  assert(nodes.keys.forall(nm.isConfiguredNode(_)))
	  assert(nm.nodeConfigToString("n99") === "⊥")
	  nodes.keys.foreach(n => assert (nm.nodeConfigToString(n) === nodes(n))) //debug
	  assert(nodes.keys.forall(n => nm.nodeConfigToString(n) == nodes(n)))
	  assert(nm.isACM)
	  assert(!nm.isIFS)
	  assert(nm.model_type === "Dependability")
	  
	  assert(nm.verify_globals(NetGraph(List("n2"), List())) === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4"), 
	      List(("n2", "n1"), ("n2", "n3"), ("n3", "n4")))) 
	      === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4"), 
	      List(("n3", "n1")))) 
	      === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4", "n99", "n42"), 
	      List(("n1", "n2"), ("n2", "n3"), ("n3", "n4"))))
	      === false)
	  
	  testedModels.add(nm.model_type)
	}
	
    
     
	
    it must "CommunicationPartners" in {
	  val json = """{"model_type": "CommunicationPartners",
		"model_description": "CommunicationPartners Requirements", 
	    "model_breach_severity": 11,
			 "model_params":{
			    "node_properties": [
				  {"node":"n1",  "member_type":"DontCare"},
	  			{"node":"n2", "member_type":"Care"},
	  			{"node":"n3", "member_type":"Care"},
	  			{"node":"n4", "member_type":"Master", "acl":["n2", "n4"]}
				  ], 
			    "global_properties":null
			    }
			}"""
	  val nodes = Map(("n1", "DontCare"), 
	      ("n2", "Care"), ("n3", "Care"), ("n4", "Master ACL:[n2, n4]"))
	  val nm: NetworkModelAbstract = JSONParser.new_model_from_JSONstring(json)
	  assert(nm.description === "CommunicationPartners Requirements")
	  assert(nodes.keys.forall(nm.isConfiguredNode(_)))
	  assert(nm.nodeConfigToString("n99") === "⊥")
	  nodes.keys.foreach(n => assert (nm.nodeConfigToString(n) === nodes(n))) //debug
	  assert(nodes.keys.forall(n => nm.nodeConfigToString(n) == nodes(n)))
	  assert(nm.isACM)
	  assert(!nm.isIFS)
	  assert(nm.model_type === "CommunicationPartners")
	  
	  assert(nm.verify_globals(NetGraph(List("n2"), List())) === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4"), 
	      List(("n2", "n1"), ("n2", "n3"), ("n2", "n4")))) 
	      === true)
	  assert(nm.eval(NetGraph(List("n1", "n2", "n3", "n4"), 
	      List(("n2", "n1"), ("n2", "n3"), ("n3", "n4")))) 
	      === false)
	  
	  
	  testedModels.add(nm.model_type)
	}
	
	
	// META: check that we have tested all parsers for all models
	// note: fails at the moment
	"testedModels" should "test all models" in {
	  if(JSONParser.modelParserMapping.keys.toSet != testedModels)
	    println("[INFO] Test cases left to write: "+
	        JSONParser.modelParserMapping.keys.toSet.diff(testedModels).mkString(", "))
	  assert(JSONParser.modelParserMapping.keys.toSet === testedModels)
	}
	

}


