(*
   Title: Theory  inout.thy
   Author:    Maria Spichkova <maria.spichkova at rmit.edu.au>, 2014
*)
 
section \<open>Correctness of the relations between sets of Input/Output channels\<close>
 
theory  inout 
imports Secrecy_types
begin

consts 
  subcomponents ::  "specID \<Rightarrow> specID set"

\<comment> \<open>Mappings, defining sets of input, local, and output channels\<close>
\<comment> \<open>of a component\<close>
consts
  ins :: "specID \<Rightarrow> chanID set"
  loc :: "specID \<Rightarrow> chanID set"
  out :: "specID \<Rightarrow> chanID set"

\<comment> \<open>Predicate insuring the correct mapping from the component identifier\<close>
\<comment> \<open>to the set of input channels of a component\<close>
definition
  inStream :: "specID \<Rightarrow> chanID set \<Rightarrow> bool"
where
  "inStream x y  \<equiv> (ins x = y)"

\<comment> \<open>Predicate insuring the correct mapping from the component identifier\<close>
\<comment> \<open>to the set of local channels of a component\<close>
definition
  locStream :: "specID \<Rightarrow> chanID set \<Rightarrow> bool"
where
  "locStream x y \<equiv> (loc x = y)"

\<comment> \<open>Predicate insuring the correct mapping from the component identifier\<close>
\<comment> \<open>to the set of output channels of a component\<close>
definition
  outStream :: "specID \<Rightarrow> chanID set \<Rightarrow> bool"
where
  "outStream x y \<equiv> (out x = y)"

\<comment> \<open>Predicate insuring the correct relations between\<close>
\<comment> \<open>to the set of input, output and local channels of a component\<close>
definition
  correctInOutLoc :: "specID \<Rightarrow> bool"
where
  "correctInOutLoc x \<equiv> 
   (ins x) \<inter> (out x) = {} 
    \<and> (ins x) \<inter> (loc x) = {} 
    \<and> (loc x) \<inter> (out x) = {} " 

\<comment> \<open>Predicate insuring the correct relations between\<close>
\<comment> \<open>sets of input channels within a composed component\<close>
definition
  correctCompositionIn :: "specID \<Rightarrow> bool"
where
  "correctCompositionIn x \<equiv> 
  (ins x) = (\<Union> (ins ` (subcomponents x)) - (loc x))
  \<and> (ins x) \<inter> (\<Union> (out ` (subcomponents x))) = {}" 

\<comment> \<open>Predicate insuring the correct relations between\<close>
\<comment> \<open>sets of output channels within a composed component\<close>
definition
  correctCompositionOut :: "specID \<Rightarrow> bool"
where
  "correctCompositionOut x \<equiv> 
  (out x) = (\<Union> (out ` (subcomponents x))- (loc x))
  \<and> (out x) \<inter> (\<Union> (ins ` (subcomponents x))) = {} " 

\<comment> \<open>Predicate insuring the correct relations between\<close>
\<comment> \<open>sets of local channels within a composed component\<close>
definition
  correctCompositionLoc :: "specID \<Rightarrow> bool"
where
  "correctCompositionLoc x \<equiv> 
   (loc x) = \<Union> (ins ` (subcomponents x))
           \<inter> \<Union> (out ` (subcomponents x))" 

\<comment> \<open>If a component is an elementary one (has no subcomponents)\<close>
\<comment> \<open>its set of local channels should be empty\<close>
lemma subcomponents_loc:
assumes "correctCompositionLoc x"
       and "subcomponents x = {}"
shows "loc x = {}"
using assms by (simp add: correctCompositionLoc_def)

end
