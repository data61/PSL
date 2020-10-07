theory SINVAR_BLPtrusted
imports "../TopoS_Helper"
begin

subsection \<open>SecurityInvariant Basic Bell LaPadula with trusted entities\<close>

type_synonym security_level = nat

record node_config = 
    security_level::security_level
    trusted::bool

definition default_node_properties :: "node_config"
  where  "default_node_properties \<equiv> \<lparr> security_level = 0, trusted = False \<rparr>"

fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow>  bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> edges G. (if trusted (nP e2) then True else security_level (nP e1) \<le> security_level (nP e2) ))"


text\<open>A simplified version of the Bell LaPadula model was presented in @{file \<open>SINVAR_BLPbasic.thy\<close>}. 
In this theory, we extend this template with a notion of trust by adding a Boolean flag @{const trusted} to the host attributes. 
This is a refinement to represent real-world scenarios more accurately and analogously happened to the 
original Bell LaPadula model (see publication ``Looking Back at the Bell-La Padula Model''
A trusted host can receive information of any security level and may declassify it, 
i.e. distribute the information with its own security level. 
For example, a @{term "trusted (sc::node_config) = True"} host is allowed to receive any information 
and with the @{term "0::security_level"} level, it is allowed to reveal it to anyone. 
\<close>


definition receiver_violation :: "bool" where "receiver_violation \<equiv> True"


lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
  apply(simp only: SecurityInvariant_withOffendingFlows.sinvar_mono_def)
  apply(clarify)
  apply(simp split: prod.split prod.split_asm)
  by auto


interpretation SecurityInvariant_preliminaries
where sinvar = sinvar
  apply unfold_locales
    apply(frule_tac finite_distinct_list[OF wf_graph.finiteE])
    apply(erule_tac exE)
    apply(rename_tac list_edges)
    apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono])
        apply(auto split: prod.split prod.split_asm)[6]
   apply(simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def graph_ops split: prod.split prod.split_asm)[1]
   apply (metis prod.inject)
  apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
 done


lemma "a \<noteq> b \<Longrightarrow> ((\<exists> x. y x)) \<Longrightarrow> ((\<forall> x. \<not> y x) \<Longrightarrow> a = b )" by simp

lemma BLP_def_unique: "otherbot \<noteq> default_node_properties \<Longrightarrow>
    \<exists>G p i f. wf_graph G \<and> \<not> sinvar G p \<and> f \<in> (SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G p) \<and>
       sinvar (delete_edges G f) p \<and> 
         i \<in> snd ` f \<and> sinvar G (p(i := otherbot)) "
  apply(simp add:default_node_properties_def)
  apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
  apply (simp add:graph_ops)
  apply (simp split: prod.split_asm prod.split)
  apply(rule_tac x="\<lparr> nodes={vertex_1, vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: wf_graph_def)
  apply(rule_tac x="(\<lambda> x. default_node_properties)(vertex_1 := \<lparr>security_level = 1, trusted = False \<rparr>, vertex_2 := \<lparr>security_level = 0, trusted = False \<rparr>)" in exI, simp add:default_node_properties_def)
  apply(rule_tac x="vertex_2" in exI, simp)
  apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
  apply(case_tac otherbot)
  apply simp
  apply(erule disjE)
   apply force
  apply fast
  done


subsubsection \<open>ENF\<close>
  definition BLP_P where "BLP_P \<equiv> (\<lambda>n1 n2.(if trusted n2 then True else security_level n1 \<le> security_level n2 ))"
  lemma zero_default_candidate: "\<forall>nP e1 e2. \<not> BLP_P (nP e1) (nP e2) \<longrightarrow> \<not> BLP_P (nP e1) default_node_properties"
    apply(rule allI)+
    apply(case_tac "nP e1")
    apply(case_tac "nP e2")
    apply(rename_tac privacy2 trusted2 more2)
    apply (simp add: BLP_P_def default_node_properties_def)
    done
  lemma privacylevel_refl: "BLP_P e e"
    by(simp_all add: BLP_P_def)
  lemma BLP_ENF: "SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form sinvar BLP_P"
    unfolding SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_def
    unfolding BLP_P_def
    by simp
  lemma BLP_ENF_refl: "SecurityInvariant_withOffendingFlows.ENF_refl sinvar BLP_P"
    unfolding SecurityInvariant_withOffendingFlows.ENF_refl_def
    apply(rule conjI)
     apply(simp add: BLP_ENF)
    apply(simp add: privacylevel_refl)
  done


  definition BLP_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> ('v \<times> 'v) set set" where
  "BLP_offending_set G nP = (if sinvar G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> \<not> BLP_P (nP e1) (nP e2)} })"
  lemma BLP_offending_set: "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = BLP_offending_set"
    apply(simp only: fun_eq_iff SecurityInvariant_withOffendingFlows.ENF_offending_set[OF BLP_ENF] BLP_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto)
  done
   

interpretation BLPtrusted: SecurityInvariant_IFS 
  where default_node_properties = default_node_properties
  and sinvar = sinvar
  rewrites "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = BLP_offending_set"
    apply unfold_locales
      apply(rule ballI)
      apply (rule_tac f=f in SecurityInvariant_withOffendingFlows.ENF_snds_refl_instance[OF BLP_ENF_refl zero_default_candidate])
       apply(simp)
      apply(simp)
     apply(erule default_uniqueness_by_counterexample_IFS)
     apply(fact BLP_def_unique)
    apply(fact BLP_offending_set)
   done

 

  lemma TopoS_BLPtrusted: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales  
 
hide_type (open) node_config
hide_const (open) sinvar_mono

hide_const (open) BLP_P
hide_fact BLP_def_unique zero_default_candidate  privacylevel_refl BLP_ENF BLP_ENF_refl

hide_const (open) sinvar receiver_violation default_node_properties

end
