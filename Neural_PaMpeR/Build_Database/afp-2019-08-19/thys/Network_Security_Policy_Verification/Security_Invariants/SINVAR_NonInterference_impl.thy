theory SINVAR_NonInterference_impl
imports SINVAR_NonInterference "../TopoS_Interface_impl"
begin


code_identifier code_module SINVAR_NonInterference_impl => (Scala) SINVAR_NonInterference


subsubsection \<open>SecurityInvariant NonInterference List Implementation\<close>

definition undirected_reachable :: "'v list_graph \<Rightarrow> 'v => 'v list" where
  "undirected_reachable G v = removeAll v (succ_tran (undirected G) v)"

lemma undirected_reachable_set: "set (undirected_reachable G v) = {e2. (v,e2) \<in> (set (edgesL (undirected G)))\<^sup>+} - {v}"
  by(simp add: undirected_succ_tran_set undirected_nodes_set undirected_reachable_def)

fun sinvar_set :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "sinvar_set G nP = (\<forall> n \<in> set (nodesL G). (nP n) = Interfering \<longrightarrow> set (map nP (undirected_reachable G n)) \<subseteq> {Unrelated})"

(* equal: lemma sinvar_list_eq_set*)
fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> n \<in> set (nodesL G). (nP n) = Interfering \<longrightarrow> (let result = remdups (map nP (undirected_reachable G n)) in result = [] \<or> result = [Unrelated]))"

lemma "P = Q \<Longrightarrow> (\<forall> x. P x) = (\<forall> x. Q x)"
  by(erule arg_cong)


lemma sinvar_eq_help1: "nP ` set (undirected_reachable G n) = set (map nP (undirected_reachable G n))"
  by auto
lemma sinvar_eq_help2: "set l = {Unrelated} \<Longrightarrow> remdups l = [Unrelated]"
 apply(induction l)
  apply simp
 apply(simp)
  apply (metis empty_iff insertI1 set_empty2 subset_singletonD)
 done
lemma sinvar_eq_help3: "(let result = remdups (map nP (undirected_reachable G n)) in result = [] \<or> result = [Unrelated]) = (set (map nP (undirected_reachable G n)) \<subseteq> {Unrelated})"
  apply simp
  apply(rule iffI)
   apply(erule disjE)
    apply simp
   apply(simp only: set_map[symmetric]) 
   apply(subst set_remdups[symmetric])
   apply simp
  apply(case_tac " nP ` set (undirected_reachable G n) = {}")
   apply fast
  apply(case_tac " nP ` set (undirected_reachable G n) = {Unrelated}")
   defer
   apply(subgoal_tac "nP ` set (undirected_reachable G n) \<subseteq> {Unrelated} \<Longrightarrow>
    nP ` set (undirected_reachable G n) \<noteq> {} \<Longrightarrow>
    nP ` set (undirected_reachable G n) \<noteq> {Unrelated} \<Longrightarrow> False")
    apply fast
   apply (metis subset_singletonD)
  apply simp
  apply(rule disjI2)
  apply(simp only: sinvar_eq_help1)
  apply(simp add:sinvar_eq_help2)
  done

lemma sinvar_list_eq_set: "sinvar = sinvar_set"
  apply(insert sinvar_eq_help3)
  apply(simp add: fun_eq_iff)
  apply(rule allI)+
  apply fastforce
  done



value "sinvar 
    \<lparr> nodesL = [1::nat,2,3,4], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
    (\<lambda>e. SINVAR_NonInterference.default_node_properties)"
value "sinvar 
    \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4)] \<rparr>
    ((\<lambda>e. SINVAR_NonInterference.default_node_properties)(1:= Interfering, 2:= Unrelated, 3:= Unrelated, 4:= Unrelated))"
value "sinvar 
    \<lparr> nodesL = [1::nat,2,3,4,5, 8,9,10], edgesL = [(1,2), (2,3), (3,4), (5,4), (8,9),(9,8)] \<rparr>
    ((\<lambda>e. SINVAR_NonInterference.default_node_properties)(1:= Interfering, 2:= Unrelated, 3:= Unrelated, 4:= Unrelated))"
value "sinvar 
    \<lparr> nodesL = [1::nat], edgesL = [(1,1)] \<rparr>
    ((\<lambda>e. SINVAR_NonInterference.default_node_properties)(1:= Interfering))"

value "(undirected_reachable \<lparr> nodesL = [1::nat], edgesL = [(1,1)] \<rparr> 1) = []" 
  (* apply(simp add: removeAll_def remdups_def undirected_reachable_def succ_tran_def trancl_list_impl_def trancl_impl_def) *)





definition NonInterference_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> ('v \<times> 'v) list list" where
  "NonInterference_offending_list = Generic_offending_list sinvar"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_NonInterference.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_NonInterference.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "NonInterference_eval G P = (wf_list_graph G \<and>
  sinvar G (SecurityInvariant.node_props SINVAR_NonInterference.default_node_properties P))"



lemma sinvar_correct: "wf_list_graph G \<Longrightarrow> SINVAR_NonInterference.sinvar (list_graph_to_graph G) nP = sinvar G nP"
   apply(simp add: sinvar_list_eq_set)
   apply(rule all_nodes_list_I)
   by (simp add: SINVAR_NonInterference.undirected_reachable_def succ_tran_correct undirected_correct undirected_reachable_def)



interpretation NonInterference_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_NonInterference.default_node_properties
  and sinvar_spec=SINVAR_NonInterference.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_NonInterference.receiver_violation
  and offending_flows_impl=NonInterference_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=NonInterference_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(rule conjI)
   apply(simp add: TopoS_NonInterference; fail)
  apply(intro allI impI)
  apply(fact sinvar_correct)
 apply(rule conjI)
  apply(unfold NonInterference_offending_list_def)
  apply(intro allI impI)
  apply(rule Generic_offending_list_correct)
   apply(assumption)
  apply(simp only: sinvar_correct)
 apply(rule conjI)
  apply(intro allI)
  apply(simp only: NetModel_node_props_def)
  apply(metis NonInterference.node_props.simps NonInterference.node_props_eq_node_props_formaldef)
 apply(simp only: NonInterference_eval_def)
 apply(intro allI impI)
 apply(rule TopoS_eval_impl_proofrule[OF TopoS_NonInterference])
 apply(simp only: sinvar_correct)
done

subsubsection \<open>NonInterference packing\<close>
  definition SINVAR_LIB_NonInterference :: "('v::vertex, node_config) TopoS_packed" where
    "SINVAR_LIB_NonInterference \<equiv> 
    \<lparr> nm_name = ''NonInterference'', 
      nm_receiver_violation = SINVAR_NonInterference.receiver_violation,
      nm_default = SINVAR_NonInterference.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = NonInterference_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = NonInterference_eval
      \<rparr>"
  interpretation SINVAR_LIB_NonInterference_interpretation: TopoS_modelLibrary SINVAR_LIB_NonInterference
      SINVAR_NonInterference.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_NonInterference_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)




text \<open>Example:\<close>
context begin
  private definition "example_graph = \<lparr> nodesL = [1::nat,2,3,4,5, 8,9,10], edgesL = [(1,2), (2,3), (3,4), (5,4), (8,9), (9,8)] \<rparr>"
  private definition"example_conf = ((\<lambda>e. SINVAR_NonInterference.default_node_properties)
      (1:= Interfering, 2:= Unrelated, 3:= Unrelated, 4:= Unrelated, 8:= Unrelated, 9:= Unrelated))"
  
  private lemma "\<not> sinvar example_graph example_conf" by eval
  private lemma "NonInterference_offending_list example_graph example_conf =
                     [[(1, 2)], [(2, 3)], [(3, 4)], [(5, 4)]]" by eval
end


hide_const (open) NetModel_node_props
hide_const (open) sinvar

end
