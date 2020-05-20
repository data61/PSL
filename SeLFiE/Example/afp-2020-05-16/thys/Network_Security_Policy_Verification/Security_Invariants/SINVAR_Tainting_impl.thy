theory SINVAR_Tainting_impl
imports SINVAR_Tainting "../TopoS_Interface_impl"
begin


subsubsection \<open>SecurityInvariant Tainting List Implementation\<close>

code_identifier code_module SINVAR_Tainting_impl => (Scala) SINVAR_Tainting

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> SINVAR_Tainting.taints) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> set (edgesL G). (nP e1) \<subseteq> (nP e2))"

definition Tainting_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> SINVAR_Tainting.taints) \<Rightarrow> ('v \<times> 'v) list list" where
  "Tainting_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> \<not>(nP e1) \<subseteq> (nP e2)] ])"



definition "NetModel_node_props P =
  (\<lambda> i. (case (node_properties P) i of
                  Some property \<Rightarrow> property
                | None \<Rightarrow> SINVAR_Tainting.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_Tainting.default_node_properties P = NetModel_node_props P"
by(simp add: NetModel_node_props_def SecurityInvariant.node_props.simps[OF TopoS_Tainting])


definition "Tainting_eval G P = (wf_list_graph G \<and> 
  sinvar G (SecurityInvariant.node_props SINVAR_Tainting.default_node_properties P))"


interpretation Tainting_impl:TopoS_List_Impl
  where default_node_properties=SINVAR_Tainting.default_node_properties
  and sinvar_spec=SINVAR_Tainting.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_Tainting.receiver_violation
  and offending_flows_impl=Tainting_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=Tainting_eval
  apply(unfold TopoS_List_Impl_def)
  apply(rule conjI)
   apply(simp add: TopoS_Tainting)
   apply(simp add: list_graph_to_graph_def SINVAR_Tainting.sinvar_def; fail)
  apply(rule conjI)
   apply(simp add: list_graph_to_graph_def)
   apply(simp add: list_graph_to_graph_def SINVAR_Tainting.sinvar_def Taints_offending_set
                    SINVAR_Tainting.Taints_offending_set_def Tainting_offending_list_def; fail)
  apply(rule conjI)
   apply(simp only: NetModel_node_props_def)
   (*interpretation is in local context*)
   apply (metis SecurityInvariant.node_props.simps SecurityInvariant.node_props_eq_node_props_formaldef TopoS_Tainting)
  apply(simp only: Tainting_eval_def)
  apply(simp add: TopoS_eval_impl_proofrule[OF TopoS_Tainting])
  apply(simp add: list_graph_to_graph_def SINVAR_Tainting.sinvar_def)
 done



subsubsection \<open>Tainting packing\<close>
  definition SINVAR_LIB_Tainting :: "('v::vertex, SINVAR_Tainting.taints) TopoS_packed" where
    "SINVAR_LIB_Tainting \<equiv> 
    \<lparr> nm_name = ''Tainting'', 
      nm_receiver_violation = SINVAR_Tainting.receiver_violation,
      nm_default = SINVAR_Tainting.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = Tainting_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = Tainting_eval
      \<rparr>"
  interpretation SINVAR_LIB_BLPbasic_interpretation: TopoS_modelLibrary SINVAR_LIB_Tainting
      SINVAR_Tainting.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_Tainting_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)

subsubsection\<open>Example\<close>
context
begin
  private definition tainting_example :: "string list_graph" where
  "tainting_example \<equiv> \<lparr> nodesL = [''produce 1'',
                                  ''produce 2'',
                                  ''produce 3'',
                                  ''read 1 2'',
                                  ''read 3'',
                                  ''consume 1 2 3'',
                                  ''consume 3''], 
              edgesL =[(''produce 1'', ''read 1 2''),
                       (''produce 2'', ''read 1 2''),
                       (''produce 3'', ''read 3''), 
                       (''read 3'', ''read 1 2''),
                       (''read 1 2'', ''consume 1 2 3''),
                       (''read 3'', ''consume 3'')] \<rparr>"
  lemma "wf_list_graph tainting_example" by eval


  private definition tainting_example_props :: "string \<Rightarrow> SINVAR_Tainting.taints" where
    "tainting_example_props \<equiv> (\<lambda> n. SINVAR_Tainting.default_node_properties)
                          (''produce 1'' := {''1''},
                           ''produce 2'' := {''2''},
                           ''produce 3'' := {''3''},
                           ''read 1 2'' := {''1'',''2'', ''3''},
                           ''read 3'' := {''3''},
                           ''consume 1 2 3'' := {''1'',''2'',''3''},
                           ''consume 3'' := {''3''})"
  private lemma "sinvar tainting_example tainting_example_props" by eval
end

export_code SINVAR_LIB_Tainting checking Scala

hide_const (open) NetModel_node_props Tainting_offending_list Tainting_eval

hide_const (open) sinvar

end
