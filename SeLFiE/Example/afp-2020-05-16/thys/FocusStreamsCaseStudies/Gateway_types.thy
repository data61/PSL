(*<*)
(*
   Title:  Gateway_types.thy  (Input/Output Definitions)
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*) 
(*>*)
 section \<open>Gateway: Types\<close> 

theory Gateway_types 
imports stream
begin

type_synonym
   Coordinates = "nat \<times> nat"
type_synonym 
   CollisionSpeed = "nat"

record ECall_Info = 
   coord :: Coordinates
   speed :: CollisionSpeed

datatype GatewayStatus = 
    init_state
  | call
  | connection_ok
  | sending_data
  | voice_com

datatype reqType = init | send

datatype stopType = stop_vc

datatype vcType = vc_com

datatype aType = sc_ack

end
