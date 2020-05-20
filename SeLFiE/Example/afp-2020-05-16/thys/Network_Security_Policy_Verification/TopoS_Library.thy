theory TopoS_Library
imports
  "Lib/FiniteListGraph_Impl"
  "Security_Invariants/SINVAR_BLPbasic_impl"
  "Security_Invariants/SINVAR_Subnets_impl"
  "Security_Invariants/SINVAR_DomainHierarchyNG_impl"
  "Security_Invariants/SINVAR_BLPtrusted_impl"
  "Security_Invariants/SINVAR_SecGwExt_impl"
  "Security_Invariants/SINVAR_Sink_impl"
  "Security_Invariants/SINVAR_SubnetsInGW_impl"
  "Security_Invariants/SINVAR_CommunicationPartners_impl"
  "Security_Invariants/SINVAR_NoRefl_impl"
  "Security_Invariants/SINVAR_Tainting_impl"
  "Security_Invariants/SINVAR_TaintingTrusted_impl"
  (*invariants you probably don't want to use because of exponential runtime*)
  "Security_Invariants/SINVAR_Dependability_impl"
  "Security_Invariants/SINVAR_NonInterference_impl"
  "Security_Invariants/SINVAR_ACLnotCommunicateWith_impl"
  "Security_Invariants/SINVAR_ACLcommunicateWith_impl"
  "Security_Invariants/SINVAR_Dependability_norefl_impl"
  "Lib/Efficient_Distinct"
  "HOL-Library.Code_Target_Nat"
begin

(*<*)

section\<open>Summarizing the Security Invariant Library\<close>

(*none of those should be defined or a hide_const is missing at the end of a SINVAR_*.thy file*)
term sinvar
term receiver_violation
term eval

(*TODO check all before export*)

print_interps TopoS_modelLibrary

(*some checks: *)
thm SINVAR_LIB_BLPbasic_interpretation.impl_spec
thm SINVAR_LIB_Dependability_interpretation.impl_spec
thm SINVAR_LIB_DomainHierarchyNG_interpretation.impl_spec
thm SINVAR_LIB_Subnets_interpretation.impl_spec
thm SINVAR_LIB_BLPtrusted_interpretation.impl_spec
thm SINVAR_LIB_PolEnforcePointExtended_interpretation.impl_spec
thm SINVAR_LIB_Sink_interpretation.impl_spec
thm SINVAR_LIB_NonInterference_interpretation.impl_spec
thm SINVAR_LIB_SubnetsInGW_interpretation.impl_spec
thm SINVAR_LIB_CommunicationPartners_interpretation.impl_spec
thm SINVAR_LIB_Dependability_interpretation.impl_spec
thm SINVAR_LIB_ACLcommunicateWith_interpretation.impl_spec


(*>*)


end
