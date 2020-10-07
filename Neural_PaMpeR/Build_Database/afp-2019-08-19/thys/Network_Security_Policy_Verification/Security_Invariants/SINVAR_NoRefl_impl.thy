theory SINVAR_NoRefl_impl
imports SINVAR_NoRefl "../TopoS_Interface_impl"
begin

code_identifier code_module  SINVAR_NoRefl_impl => (Scala) SINVAR_NoRefl


subsubsection \<open>SecurityInvariant NoRefl List Implementation\<close>

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (s,r) \<in> set (edgesL G). s = r \<longrightarrow> nP s = Refl)"


definition NoRefl_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> ('v \<times> 'v) list list" where
  "NoRefl_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> e1 = e2 \<and> nP e1 = NoRefl] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_NoRefl.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_NoRefl.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "NoRefl_eval G P = (wf_list_graph G \<and>
  sinvar G (SecurityInvariant.node_props SINVAR_NoRefl.default_node_properties P))"


interpretation NoRefl_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_NoRefl.default_node_properties
  and sinvar_spec=SINVAR_NoRefl.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_NoRefl.receiver_violation
  and offending_flows_impl=NoRefl_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=NoRefl_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(simp add: TopoS_NoRefl list_graph_to_graph_def)
 apply(rule conjI)
  apply(simp add: list_graph_to_graph_def NoRefl_offending_set NoRefl_offending_set_def NoRefl_offending_list_def)
 apply(rule conjI)
  apply(simp only: NetModel_node_props_def)
  apply(metis NoRefl.node_props.simps NoRefl.node_props_eq_node_props_formaldef)
 apply(simp only: NoRefl_eval_def)
 apply(simp add: TopoS_eval_impl_proofrule[OF TopoS_NoRefl])
 apply(simp add: list_graph_to_graph_def)
done


subsubsection \<open>PolEnforcePoint packing\<close>
  definition SINVAR_LIB_NoRefl :: "('v::vertex, node_config) TopoS_packed" where
    "SINVAR_LIB_NoRefl \<equiv> 
    \<lparr> nm_name = ''NoRefl'', 
      nm_receiver_violation = SINVAR_NoRefl.receiver_violation,
      nm_default = SINVAR_NoRefl.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = NoRefl_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = NoRefl_eval
      \<rparr>"
  interpretation SINVAR_LIB_NoRefl_interpretation: TopoS_modelLibrary SINVAR_LIB_NoRefl
      SINVAR_NoRefl.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_NoRefl_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)

text \<open>Examples\<close>

  definition example_net :: "nat list_graph" where
  "example_net \<equiv> \<lparr> nodesL = [1::nat,2,3], 
    edgesL = [(1,2),(2,2),(2,1),(1,3)] \<rparr>"
  lemma "wf_list_graph example_net" by eval
  
  definition example_conf where
  "example_conf \<equiv> ((\<lambda>e. SINVAR_NoRefl.default_node_properties)(2:= Refl))" 
  
  lemma "sinvar example_net example_conf" by eval
  lemma "NoRefl_offending_list example_net (\<lambda>e. SINVAR_NoRefl.default_node_properties) = [[(2, 2)]]" by eval


hide_const (open) NetModel_node_props
hide_const (open) sinvar

end
