theory SINVAR_Dependability_impl
imports SINVAR_Dependability "../TopoS_Interface_impl"
begin


code_identifier code_module SINVAR_Dependability_impl => (Scala) SINVAR_Dependability


subsubsection \<open>SecurityInvariant Dependability List Implementation\<close>


text \<open>Less-equal other nodes depend on the output of a node than its dependability level.\<close>
fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> set (edgesL G). (num_reachable G e1) \<le> (nP e1))"


value "sinvar 
    \<lparr> nodesL = [1::nat,2,3,4], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
    (\<lambda>e. 3)"
value "sinvar 
    \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
    (\<lambda>e. 2)"





text\<open>Generate a valid configuration to start from:\<close>
   fun dependability_fix_nP :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> ('v \<Rightarrow> dependability_level)" where
      "dependability_fix_nP G nP = (\<lambda>v. let nr = num_reachable G v in (if nr \<le> (nP v) then (nP v) else nr))"

   theorem dependability_fix_nP_impl_correct: "wf_list_graph G \<Longrightarrow> dependability_fix_nP G nP  = SINVAR_Dependability.dependability_fix_nP (list_graph_to_graph G) nP"
   by(simp add: num_reachable_correct fun_eq_iff)

   value "let G = \<lparr> nodesL = [1::nat,2,3,4], edgesL = [(1,1), (2,1), (3,1), (4,1), (1,2), (1,3)] \<rparr> in (let nP = dependability_fix_nP G (\<lambda>e. 0) in map (\<lambda>v. nP v) (nodesL G))"


   value "let G = \<lparr> nodesL = [1::nat,2,3,4], edgesL = [(1,1)] \<rparr> in (let nP = dependability_fix_nP G (\<lambda>e. 0) in map (\<lambda>v. nP v) (nodesL G))"



definition Dependability_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> ('v \<times> 'v) list list" where
  "Dependability_offending_list = Generic_offending_list sinvar"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_Dependability.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_Dependability.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "Dependability_eval G P = (wf_list_graph G \<and>
  sinvar G (SecurityInvariant.node_props SINVAR_Dependability.default_node_properties P))"



lemma sinvar_correct: "wf_list_graph G \<Longrightarrow> SINVAR_Dependability.sinvar (list_graph_to_graph G) nP = sinvar G nP"
   apply(simp)
   apply(rule all_edges_list_I)
   apply(simp add: fun_eq_iff)
   apply(clarify)
   apply(rename_tac x)
   apply(drule_tac v="x" in  num_reachable_correct)
  apply presburger
done



interpretation Dependability_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_Dependability.default_node_properties
  and sinvar_spec=SINVAR_Dependability.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_Dependability.receiver_violation
  and offending_flows_impl=Dependability_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=Dependability_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(rule conjI)
   apply(simp add: TopoS_Dependability; fail)
  apply(intro allI impI)
  apply(fact sinvar_correct)
 apply(rule conjI)
  apply(unfold Dependability_offending_list_def)
  apply(intro allI impI)
  apply(rule Generic_offending_list_correct)
   apply(assumption)
  apply(simp only: sinvar_correct)
 apply(rule conjI)
  apply(intro allI)
  apply(simp only: NetModel_node_props_def)
  apply(metis Dependability.node_props.simps Dependability.node_props_eq_node_props_formaldef)
 apply(simp only: Dependability_eval_def)
 apply(intro allI impI)
 apply(rule TopoS_eval_impl_proofrule[OF TopoS_Dependability])
 apply(simp only: sinvar_correct)
done

subsubsection \<open>Dependability packing\<close>
  definition SINVAR_LIB_Dependability :: "('v::vertex, SINVAR_Dependability.dependability_level) TopoS_packed" where
    "SINVAR_LIB_Dependability \<equiv> 
    \<lparr> nm_name = ''Dependability'', 
      nm_receiver_violation = SINVAR_Dependability.receiver_violation,
      nm_default = SINVAR_Dependability.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = Dependability_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = Dependability_eval
      \<rparr>"
  interpretation SINVAR_LIB_Dependability_interpretation: TopoS_modelLibrary SINVAR_LIB_Dependability
      SINVAR_Dependability.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_Dependability_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)

text \<open>Example:\<close>
  value "let G = \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
      in sinvar G  ((\<lambda> n. SINVAR_Dependability.default_node_properties)(1:=3, 2:=2, 3:=1, 4:=0, 8:=2, 9:=2, 10:=0))"
  
  value "let G = \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
      in sinvar G  ((\<lambda> n. SINVAR_Dependability.default_node_properties)(1:=10, 2:=10, 3:=10, 4:=10, 8:=10, 9:=10, 10:=10))"
  
  value "let G = \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
      in sinvar G  ((\<lambda> n. 2))"
  
  value "let G = \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
      in Dependability_eval G  \<lparr>node_properties=[1\<mapsto>3, 2\<mapsto>2, 3\<mapsto>1, 4\<mapsto>0, 8\<mapsto>2, 9\<mapsto>2, 10\<mapsto>0] \<rparr>"
  
  value "Dependability_offending_list \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr> (\<lambda> n. 2)"

hide_fact (open) sinvar_correct
hide_const (open) sinvar NetModel_node_props

end
