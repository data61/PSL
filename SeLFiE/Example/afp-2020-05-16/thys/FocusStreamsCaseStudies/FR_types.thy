(*<*)
(*
   Title:  FR_types.thy  (Input/Output Definitions)
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*) 
(*>*)
section \<open>FlexRay: Types\<close> 


theory FR_types 
imports stream
begin

record 'a Message = 
   message_id :: nat
   ftcdata    :: 'a

record 'a Frame = 
   slot :: nat
   dataF :: "('a Message) list"

record Config = 
   schedule    :: "nat list" 
   cycleLength :: nat

type_synonym 'a nFrame = "nat \<Rightarrow> ('a Frame) istream"

type_synonym nNat = "nat \<Rightarrow> nat istream"

type_synonym nConfig = "nat \<Rightarrow> Config"

consts sN :: "nat"

definition 
  sheafNumbers :: "nat list"
where
 "sheafNumbers \<equiv> [sN]"

end
