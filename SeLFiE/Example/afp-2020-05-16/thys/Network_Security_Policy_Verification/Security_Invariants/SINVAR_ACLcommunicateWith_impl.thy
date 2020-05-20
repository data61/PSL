theory SINVAR_ACLcommunicateWith_impl
imports SINVAR_ACLcommunicateWith "../TopoS_Interface_impl"
begin

code_identifier code_module SINVAR_ACLcommunicateWith_impl => (Scala) SINVAR_ACLcommunicateWith


subsubsection \<open>List Implementation\<close>

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> 'v list) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> v \<in> set (nodesL G). \<forall>a \<in> (set (succ_tran G v)). a \<in> set (nP v))"


definition "NetModel_node_props (P::('v::vertex, 'v list) TopoS_Params) = 
  (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_ACLcommunicateWith.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_ACLcommunicateWith.default_node_properties P = NetModel_node_props P"
by(simp add: NetModel_node_props_def)

definition "ACLcommunicateWith_offending_list = Generic_offending_list sinvar"

definition "ACLcommunicateWith_eval G P = (wf_list_graph G \<and> 
  sinvar G (SecurityInvariant.node_props SINVAR_ACLcommunicateWith.default_node_properties P))"


lemma sinvar_correct: "wf_list_graph G \<Longrightarrow> SINVAR_ACLcommunicateWith.sinvar (list_graph_to_graph G) nP = sinvar G nP"
by (metis SINVAR_ACLcommunicateWith.sinvar.simps SINVAR_ACLcommunicateWith_impl.sinvar.simps graph.select_convs(1) list_graph_to_graph_def succ_tran_correct)


interpretation SINVAR_ACLcommunicateWith_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_ACLcommunicateWith.default_node_properties
  and sinvar_spec=SINVAR_ACLcommunicateWith.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_ACLcommunicateWith.receiver_violation
  and offending_flows_impl=ACLcommunicateWith_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=ACLcommunicateWith_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(rule conjI)
   apply(simp add: TopoS_ACLcommunicateWith; fail)
  apply(intro allI impI)
  apply(fact sinvar_correct)
 apply(rule conjI)
  apply(unfold ACLcommunicateWith_offending_list_def)
  apply(intro allI impI)
  apply(rule Generic_offending_list_correct)
   apply(assumption)
  apply(simp only: sinvar_correct; fail)
 apply(rule conjI)
  apply(intro allI)
  apply(simp only: NetModel_node_props_def)
  apply(metis ACLcommunicateWith.node_props.simps ACLcommunicateWith.node_props_eq_node_props_formaldef)
 apply(simp only: ACLcommunicateWith_eval_def)
 apply(intro allI impI)
 apply(rule TopoS_eval_impl_proofrule[OF TopoS_ACLcommunicateWith])
 apply(simp only: sinvar_correct; fail)
done


subsubsection \<open>packing\<close>
  definition SINVAR_LIB_ACLcommunicateWith:: "('v::vertex, 'v list) TopoS_packed" where
    "SINVAR_LIB_ACLcommunicateWith \<equiv> 
    \<lparr> nm_name = ''ACLcommunicateWith'', 
      nm_receiver_violation = SINVAR_ACLcommunicateWith.receiver_violation,
      nm_default = SINVAR_ACLcommunicateWith.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = ACLcommunicateWith_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = ACLcommunicateWith_eval
      \<rparr>"
  interpretation SINVAR_LIB_ACLcommunicateWith_interpretation: TopoS_modelLibrary SINVAR_LIB_ACLcommunicateWith
      SINVAR_ACLcommunicateWith.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_ACLcommunicateWith_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)



text \<open>Examples\<close>
context begin
  text\<open>
    1 can access 2 and 3
    2 can access 3
\<close>
  private lemma "sinvar
            \<lparr> nodesL = [1::nat, 2, 3],
              edgesL = [(1,2), (2,3)]\<rparr>
            (((\<lambda>v. SINVAR_ACLcommunicateWith.default_node_properties)
                    (1 := [2,3]))
                    (2 := [3]))" by eval

  text\<open>
    Everyone can access everyone, except for 1: 1 must not access 4.
    The offending flows may be any edge on the path from 1 to 4
\<close>
  lemma "ACLcommunicateWith_offending_list 
          \<lparr> nodesL = [1::nat, 2, 3, 4],
            edgesL = [(1,2), (2,3), (3, 4)]\<rparr>
          (((((\<lambda>v. SINVAR_ACLcommunicateWith.default_node_properties)
          (1 := [1,2,3]))
          (2 := [1,2,3,4]))
          (3 := [1,2,3,4]))
          (4 := [1,2,3,4])) =
       [[(1, 2)], [(2, 3)], [(3, 4)]]" by eval
  text\<open>
    If we add the additional edge from 1 to 3, then the offending flows are either
    \<^item> [(3.4)], because this disconnects 4 from the graph completely
    \<^item> any pair of edges which disconnects 1 from 3
\<close>
  lemma "ACLcommunicateWith_offending_list 
          \<lparr> nodesL = [1::nat, 2, 3, 4],
            edgesL = [(1,2), (1,3), (2,3), (3, 4)]\<rparr>
          (((((\<lambda>v. SINVAR_ACLcommunicateWith.default_node_properties)
          (1 := [1,2,3]))
          (2 := [1,2,3,4]))
          (3 := [1,2,3,4]))
          (4 := [1,2,3,4])) =
       [[(1, 2), (1, 3)], [(1, 3), (2, 3)], [(3, 4)]]" by eval
end


hide_const (open) NetModel_node_props
hide_const (open) sinvar

end
