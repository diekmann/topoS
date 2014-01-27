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


  text{*fwd is an entity's packet forward function: 
      A packet arriving at port with a header (src, dst) is outputted to a set of ports*}
  type_synonym 'v fwd_fun="port \<Rightarrow> ('v \<times> 'v) \<Rightarrow> port set"

  
  text{* A network consists of
          A set of interfaces (ports at entities where packets are moved between)
          A forwarding behaviour per entity
          Links betweend interfaces (edges in a graph or cables in real world)*}
  record 'v network = interfaces :: "'v interface set"
                      forwarding :: "'v entity \<Rightarrow> 'v fwd_fun"
                      links      :: "(('v interface) \<times> ('v interface)) set"


  value "\<lparr> interfaces = {\<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 1 \<rparr>,
                         \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 2 \<rparr>,
                         \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr>,
                         \<lparr> entity = Host ''Alice'', port = Port 1 \<rparr>,
                         \<lparr> entity = Host ''Bob'', port = Port 1 \<rparr>,
                         \<lparr> entity = Host ''Carl'', port = Port 1 \<rparr>},
           forwarding = (\<lambda> e. \<lambda> p (srd,dst). {}),
           links = {
            (\<lparr> entity = Host ''Alice'', port = Port 1 \<rparr>, \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 1 \<rparr>),
            (\<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 1 \<rparr>, \<lparr> entity = Host ''Alice'', port = Port 1 \<rparr>),

            (\<lparr> entity = Host ''Bob'', port = Port 1 \<rparr>, \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr>),
            (\<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr>, \<lparr> entity = Host ''Bob'', port = Port 1 \<rparr>),

            (\<lparr> entity = Host ''Carl'', port = Port 1 \<rparr>, \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr>),
            (\<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr>, \<lparr> entity = Host ''Carl'', port = Port 1 \<rparr>)
            }\<rparr>"


end
