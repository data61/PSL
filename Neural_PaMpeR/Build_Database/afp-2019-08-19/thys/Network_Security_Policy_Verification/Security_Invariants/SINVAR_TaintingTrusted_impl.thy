theory SINVAR_TaintingTrusted_impl
imports SINVAR_TaintingTrusted "../TopoS_Interface_impl"
begin


subsubsection \<open>SecurityInvariant Tainting with Trust List Implementation\<close>

code_identifier code_module SINVAR_Tainting_impl => (Scala) SINVAR_Tainting

(*could we use those to make code more efficient?*)
lemma "A - B \<subseteq> C \<longleftrightarrow> (\<forall>a\<in>A. a \<in> C \<or> a \<in> B)" by blast
lemma "\<not>(A - B \<subseteq> C) \<longleftrightarrow> (\<exists>a \<in> A. a \<notin> C \<and> a \<notin> B)" by blast

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> SINVAR_TaintingTrusted.taints) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (v1,v2) \<in> set (edgesL G). taints (nP v1) - untaints (nP v1) \<subseteq> taints (nP v2))"


(*Test that we have executable code, despite the abstractions*)
export_code sinvar checking SML
value[code] "sinvar \<lparr> nodesL = [], edgesL =[] \<rparr> (\<lambda>_. SINVAR_TaintingTrusted.default_node_properties)"
lemma "sinvar \<lparr> nodesL = [], edgesL =[] \<rparr> (\<lambda>_. SINVAR_TaintingTrusted.default_node_properties)" by eval


definition TaintingTrusted_offending_list 
  :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> SINVAR_TaintingTrusted.taints) \<Rightarrow> ('v \<times> 'v) list list" where
  "TaintingTrusted_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (v1,v2) \<Rightarrow> \<not>(taints (nP v1) - untaints (nP v1) \<subseteq> taints (nP v2))] ])"

(*TODO: is this code somewhat efficient?*)
export_code TaintingTrusted_offending_list checking SML


definition "NetModel_node_props P =
  (\<lambda> i. (case (node_properties P) i of
                  Some property \<Rightarrow> property
                | None \<Rightarrow> SINVAR_TaintingTrusted.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_TaintingTrusted.default_node_properties P = NetModel_node_props P"
by(simp add: NetModel_node_props_def SecurityInvariant.node_props.simps[OF TopoS_TaintingTrusted])


definition "TaintingTrusted_eval G P = (wf_list_graph G \<and> 
  sinvar G (SecurityInvariant.node_props SINVAR_TaintingTrusted.default_node_properties P))"


interpretation TaintingTrusted_impl:TopoS_List_Impl
  where default_node_properties=SINVAR_TaintingTrusted.default_node_properties
  and sinvar_spec=SINVAR_TaintingTrusted.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_TaintingTrusted.receiver_violation
  and offending_flows_impl=TaintingTrusted_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=TaintingTrusted_eval
  apply(unfold TopoS_List_Impl_def)
  apply(rule conjI)
   apply(simp add: TopoS_TaintingTrusted)
   apply(simp add: list_graph_to_graph_def SINVAR_TaintingTrusted.sinvar_def; fail)
  apply(rule conjI)
   apply(simp add: list_graph_to_graph_def)
   apply(simp add: list_graph_to_graph_def SINVAR_TaintingTrusted.sinvar_def Taints_offending_set
                    SINVAR_TaintingTrusted.Taints_offending_set_def TaintingTrusted_offending_list_def; fail)
  apply(rule conjI)
   apply(simp only: NetModel_node_props_def)
   (*interpretation is in local context*)
   apply (metis SecurityInvariant.node_props.simps SecurityInvariant.node_props_eq_node_props_formaldef TopoS_TaintingTrusted)
  apply(simp only: TaintingTrusted_eval_def)
  apply(simp add: TopoS_eval_impl_proofrule[OF TopoS_TaintingTrusted])
  apply(simp add: list_graph_to_graph_def SINVAR_TaintingTrusted.sinvar_def; fail)
 done



subsubsection \<open>TaintingTrusted packing\<close>
  definition SINVAR_LIB_TaintingTrusted :: "('v::vertex, SINVAR_TaintingTrusted.taints) TopoS_packed" where
    "SINVAR_LIB_TaintingTrusted \<equiv> 
    \<lparr> nm_name = ''TaintingTrusted'', 
      nm_receiver_violation = SINVAR_TaintingTrusted.receiver_violation,
      nm_default = SINVAR_TaintingTrusted.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = TaintingTrusted_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = TaintingTrusted_eval
      \<rparr>"
  interpretation SINVAR_LIB_BLPbasic_interpretation: TopoS_modelLibrary SINVAR_LIB_TaintingTrusted
      SINVAR_TaintingTrusted.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_TaintingTrusted_def)
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


  private definition tainting_example_props :: "string \<Rightarrow> SINVAR_TaintingTrusted.taints" where
    "tainting_example_props \<equiv> (\<lambda> n. SINVAR_TaintingTrusted.default_node_properties)
                          (''produce 1'' := TaintsUntaints {''1''} {},
                           ''produce 2'' := TaintsUntaints {''2''} {},
                           ''produce 3'' := TaintsUntaints {''3''} {},
                           ''read 1 2'' := TaintsUntaints {''3'',''foo''} {''1'',''2''},
                           ''read 3'' := TaintsUntaints {''3''} {},
                           ''consume 1 2 3'' := TaintsUntaints {''foo'',''3''} {},
                           ''consume 3'' := TaintsUntaints {''3''} {})"

  value "tainting_example_props (''consume 1 2 3'')"
  value[code] "TaintingTrusted_offending_list tainting_example tainting_example_props"
  private lemma "sinvar tainting_example tainting_example_props" by eval
end

(*TODO: fails. why?*)
export_code SINVAR_LIB_TaintingTrusted checking Scala
export_code SINVAR_LIB_TaintingTrusted checking SML

hide_const (open) NetModel_node_props TaintingTrusted_offending_list TaintingTrusted_eval

hide_const (open) sinvar

end
