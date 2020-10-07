theory InformationFlowProperties
imports BasicSecurityPredicates
begin

(* Security Predicates are sets of basic security predicates *)
type_synonym 'e SP = "('e BSP) set"

(* structurally, information flow properties consist of a set of views 
 and a security predicate. *)
type_synonym 'e IFP_type = "('e V_rec set) \<times> 'e SP"

(* side condition for information flow properties *)
definition IFP_valid :: "'e set \<Rightarrow> 'e IFP_type \<Rightarrow> bool"
where
"IFP_valid E ifp \<equiv>  
  \<forall>\<V> \<in> (fst ifp). isViewOn \<V> E  
                    \<and> (\<forall>BSP \<in> (snd ifp). BSP_valid BSP)"

(* An information flow property is an instance of IFP_type that 
 satisfies IFP_valid. *)
definition IFPIsSatisfied :: "'e IFP_type \<Rightarrow> ('e list) set  \<Rightarrow> bool"
where 
"IFPIsSatisfied ifp Tr \<equiv> 
  \<forall> \<V>\<in>(fst ifp). \<forall> BSP\<in>(snd ifp). BSP \<V> Tr"

end
