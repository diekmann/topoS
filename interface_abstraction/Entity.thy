theory Entity
imports Main
begin

section{*Basic Definitions*}
  text{*entities we have in our network. 
      Hosts are devices the network is built for (e.g. servers, clients)
      Network Boxes are neccessary for perating the networkg (e.g, switches, routers)
      'v is the name (e.g. ''Hans'', 192.168.0.1)*}
  datatype 'v entity = Host 'v | NetworkBox 'v
  
  text{*A port, like a switche's port or a simple NIC*}
  datatype port = Port nat
  
  text{*We will move packets between interfaces.
    An interface is a certain port at an entity.*}
  record 'v interface = entity :: "'v entity"
                        port :: "port"
                        
  
  text{*Example: Port two in a three-port switch*}
  value "\<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 2 \<rparr>"


end
