theory SINVAR_BLPbasic
imports "../TopoS_Helper"
begin

subsection \<open>SecurityInvariant Basic Bell LaPadula\<close>

type_synonym security_level = nat

definition default_node_properties :: "security_level"
  where  "default_node_properties \<equiv> 0"

fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> security_level) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> edges G. (nP e1) \<le> (nP e2))"

text\<open>What we call a @{typ security_level} is also referred to as security label
(or security clearance of subjects and classification of objects) in the literature. 
The lowest security level is @{term "0::nat"}, which can be understood as unclassified.
Consequently, 1 = confidential, 2 = secret, 3 = topSecret, .... 
The total order of the security levels corresponds to the total order of the natural numbers \<open>\<le>\<close>. 
It is important that there is smallest security level (i.e. @{const default_node_properties}), 
otherwise, a unique and secure default parameter could not exist. 
Hence, it is not possible to extend the security levels to @{typ int} to model unlimited ``un-confidentialness''. 
\<close>

definition receiver_violation :: "bool" where "receiver_violation \<equiv> True"


lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
  apply(simp only: SecurityInvariant_withOffendingFlows.sinvar_mono_def)
  apply(clarify)
  by auto


interpretation SecurityInvariant_preliminaries
where sinvar = sinvar
  apply unfold_locales
    apply(frule_tac finite_distinct_list[OF wf_graph.finiteE])
    apply(erule_tac exE)
    apply(rename_tac list_edges)
    apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono])
        apply(auto)[6]
   apply(auto simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def graph_ops)[1]
  apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
 done


lemma BLP_def_unique: "otherbot \<noteq> 0 \<Longrightarrow>
    \<exists>G p i f. wf_graph G \<and> \<not> sinvar G p \<and> f \<in> (SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G p) \<and>
       sinvar (delete_edges G f) p \<and>
        i \<in> snd ` f \<and> sinvar G (p(i := otherbot)) "
  apply(simp)
  apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
  apply (simp add:graph_ops)
  apply (simp split: prod.split_asm prod.split)
  apply(rule_tac x="\<lparr> nodes=set [vertex_1,vertex_2], edges = set [(vertex_1,vertex_2)] \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: wf_graph_def)
  apply(rule_tac x="(\<lambda> x. 0)(vertex_1 := 1, vertex_2 := 0)" in exI, simp)
  apply(rule_tac x="vertex_2" in exI, simp)
  apply(rule_tac x="set [(vertex_1,vertex_2)]" in exI, simp)
  done


(*Test instantiation without any fancy lemmata*)
(*
interpretation SecurityInvariant
where default_node_properties = default_node_properties
and sinvar = sinvar
and receiver_violation = receiver_violation
  unfolding default_node_properties_def
  unfolding receiver_violation_def
  apply unfold_locales
  
  apply(simp)
  apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
  apply (simp add:graph_ops)
  apply (simp split: prod.split_asm prod.split add:case_prod_beta)
   apply(auto intro!:bexI)[1]
   (*apply (smt image_iff offending_in_edges prod.collapse)*)
  apply(blast intro: BLP_def_unique)
done
*)
 

subsubsection \<open>ENF\<close>
  lemma zero_default_candidate: "\<And> nP e1 e2. \<not> ((\<le>)::security_level \<Rightarrow> security_level \<Rightarrow> bool) (nP e1) (nP e2) \<Longrightarrow> \<not> (\<le>) (nP e1) 0"
    by simp_all
  lemma zero_default_candidate_rule: "\<And> (nP::('v \<Rightarrow> security_level)) e1 e2. \<not> (nP e1) \<le> (nP e2) \<Longrightarrow> \<not> (nP e1) \<le> 0"
    by simp_all
  lemma privacylevel_refl: "((\<le>)::security_level \<Rightarrow> security_level \<Rightarrow> bool) e e"
    by(simp_all)
  lemma BLP_ENF: "SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form sinvar (\<le>)"
    unfolding SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_def
    by simp
  lemma BLP_ENF_refl: "SecurityInvariant_withOffendingFlows.ENF_refl sinvar (\<le>)"
    unfolding SecurityInvariant_withOffendingFlows.ENF_refl_def
    apply(rule conjI)
     apply(simp add: BLP_ENF)
    apply(simp add: privacylevel_refl)
  done

  definition BLP_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> security_level) \<Rightarrow> ('v \<times> 'v) set set" where
  "BLP_offending_set G nP = (if sinvar G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> (nP e1) > (nP e2)} })"
  lemma BLP_offending_set: "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = BLP_offending_set"
    apply(simp only: fun_eq_iff SecurityInvariant_withOffendingFlows.ENF_offending_set[OF BLP_ENF] BLP_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto)
  done
   

  interpretation BLPbasic: SecurityInvariant_IFS sinvar default_node_properties
  rewrites "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = BLP_offending_set"
    unfolding receiver_violation_def
    unfolding default_node_properties_def
    apply(unfold_locales)
      apply(rule ballI)
      apply(rule SecurityInvariant_withOffendingFlows.ENF_snds_refl_instance[OF BLP_ENF_refl])
         apply(simp_all add: BLP_ENF BLP_ENF_refl)[3]
     apply(erule default_uniqueness_by_counterexample_IFS)
     apply(fact BLP_def_unique)
    apply(fact BLP_offending_set)
   done


  lemma TopoS_BLPBasic: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales


text\<open>Alternate definition of the @{const sinvar}:
      For all reachable nodes, the security level is higher\<close>
lemma sinvar_BLPbasic_tancl:
  "wf_graph G \<Longrightarrow> sinvar G nP = (\<forall> v \<in> nodes G. \<forall>v' \<in> succ_tran G v. (nP v) \<le> (nP v'))"
  proof(unfold sinvar.simps, rule iffI, goal_cases)
  case 1
      have "(v, v') \<in> (edges G)\<^sup>+ \<Longrightarrow> nP v \<le> nP v'" for v v'
        proof(induction rule: trancl_induct)
        case base thus ?case using 1(2) by fastforce
        next
        case step thus ?case using 1(2) by fastforce
        qed
      thus ?case
      by(simp add: succ_tran_def)
    next
    case 2
      from 2(1)[simplified wf_graph_def] have f1: "fst ` edges G \<subseteq> nodes G" by simp
      from f1 2(2) have "\<forall>v \<in> (fst ` edges G). \<forall>v'\<in>succ_tran G v. nP v \<le> nP v'" by auto
      thus ?case unfolding succ_tran_def by fastforce
  qed

   
hide_fact (open) sinvar_mono
hide_fact BLP_def_unique zero_default_candidate zero_default_candidate_rule privacylevel_refl BLP_ENF BLP_ENF_refl

hide_const (open) sinvar receiver_violation default_node_properties

end
