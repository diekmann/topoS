package tum.in.net.psn.log_topo.NetworkModels

import net.liftweb.json
import net.liftweb.json.JsonParser.ParseException
import net.liftweb.json.MappingException

import tum.in.net.psn.log_topo.HOLequal_String._


package JSONParser {
	/**
	 * The genral template of the JSON files for each security requirement
	 */
	protected case class ModelJSONParseTemplate(
	    model_type: String,
	    model_description: String, 
	    model_breach_severity: Int, 
	    model_params: json.JValue)
}

package object JSONParser {
		//eliminates this error:
		//  could not find implicit value for parameter formats: net.liftweb.json.Formats
		implicit val formats = json.DefaultFormats
		
		
		/**
		 *  maping from model names to their constructors
		 */
		val modelParserMapping = Map(
		    "BLPbasic" -> (new BLPbasicParser(_)),
			  "BLPtrusted" -> (new BLPtrustedParser(_)),
			  "Dependability" -> (new DependabilityParser(_)),
			  "DomainHierarchy" -> (new DomainHierarchyParser(_)),
			  "DomainHierarchyTE" -> (new DomainHierarchyTEParser(_)),
			  "Subnets" -> (new SubnetsParser(_)),
			  "SecurityGateway" -> (new SecurityGatewayParser(_)),
			  "SecurityGatewayExtended" -> (new SecurityGatewayExtendedParser(_)),
			  "Sink" -> (new SinkParser(_)),
			  "NonInterference" -> (new NonInterferenceParser(_)),
			  "SubnetsInGW" -> (new SubnetsInGWParser(_)),
			  "CommunicationPartners" -> (new CommunicationPartnersParser(_))
			  )
		
		
		/**
		 * Factory Method
		 * get a network model instance from JSON string
		 */
		def new_model_from_JSONstring(s: String, verbose:Boolean=true): NetworkModelAbstract = {
			def parse_json: ModelJSONParseTemplate = {
			  try{
					val json_parsed = json.parse(s)
					try{
						val extracted = json_parsed.extract[ModelJSONParseTemplate]
						extracted
					} catch {
					case e: MappingException => println("Failed to parse model. Debug:"+s.substring(0, s.length min 160))
							println(e)
							throw new RuntimeException(e)
					}
				} catch {
				case e:ParseException => println("Failed to parse json")
						println(e)
						throw new RuntimeException(e)
				}
			}
			val j = parse_json
			
			val params = json.compact(json.render(j.model_params))
			//println(params)
			
			val modelInstance = modelParserMapping.get(j.model_type) match {
				case Some(modelConstructor) => {
				  	if (verbose) println("Creating new "+j.model_type+" instance with description `"+j.model_description+"'")
						val modelParser = modelConstructor(params)
						
						modelParser.model(j.model_description, j.model_breach_severity)
						}
				case None => {
				  	throw new RuntimeException("unknown model type: `"+j.model_type+"'. Known models are "+modelParserMapping.keySet)
				  	}
				}
			if (verbose){
			  println("Done.")
			}
			modelInstance
		}
		
}