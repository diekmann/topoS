theory VLANs
imports Network Network_View
begin

text{*devirtualizing VLANs*}

(*\<dots>*)

datatype vlan = VLANid nat

datatype memberOfCriterion = CPort | CSubnet 
datatype memberOf = TaggedMemberOf memberOfCriterion vlan |UntaggedMemberOf memberOfCriterion vlan

datatype portConfig = PortConfig port "memberOf set"

end
