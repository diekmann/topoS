theory Entity
imports Main
begin

section{*Basic Definitions*}
  text{*entities we have in our network. 
      Hosts are devices the network is built for (e.g. servers, clients)
      Network Boxes are neccessary for perating the networkg (e.g, switches, routers)
      'v is the name (e.g. ''Hans'', 192.168.0.1)*}
  datatype 'v entity = Host 'v | NetworkBox 'v

  definition entity_name :: "'v entity \<Rightarrow> 'v" where
    "entity_name e \<equiv> case e of Host h \<Rightarrow> h | NetworkBox h \<Rightarrow> h"

  lemma "entity_name (Host X) = entity_name  (NetworkBox X)" by (simp add: entity_name_def)
  
  text{*A port, like a switche's port or a simple NIC*}
  datatype port = Port nat

  text{*Example: port matching*}
  value "(\<lambda> p. if p = Port 1 then True else False) (Port 1)"
  
  text{*We will move packets between interfaces.
    An interface is a certain port at an entity.*}
  record 'v interface = entity :: "'v entity"
                        port :: "port"
                        
  
  text{*Example: Port two in a three-port switch*}
  value "\<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 2 \<rparr>"

end
