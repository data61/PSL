theory SINVAR_BLPstrict
imports "../TopoS_Helper"
begin

subsection \<open>Stricter Bell LaPadula SecurityInvariant\<close>
text\<open>All unclassified data sources must be labeled, default assumption: all is secret.

Warning: This is considered here an access control strategy.
By default, everything is secret and one explicitly prohibits sending to non-secret hosts.\<close>

datatype security_level = Unclassified | Confidential | Secret

(*total order*)
instantiation security_level :: linorder
  begin
  fun less_eq_security_level :: "security_level \<Rightarrow> security_level \<Rightarrow> bool" where
    "(Unclassified \<le> Unclassified) = True" |
    "(Confidential \<le> Confidential) = True" |
    "(Secret \<le> Secret) = True" |
    "(Unclassified \<le> Confidential) = True" |
    "(Confidential \<le> Secret) = True"  |
    "(Unclassified \<le> Secret) = True"  |
    "(Secret \<le> Confidential) = False"  |
    "(Confidential \<le> Unclassified) = False"  |
    "(Secret \<le> Unclassified) = False"

  fun less_security_level :: "security_level \<Rightarrow> security_level \<Rightarrow> bool" where
    "(Unclassified < Unclassified) = False" |
    "(Confidential < Confidential) = False" |
    "(Secret < Secret) = False" |
    "(Unclassified < Confidential) = True" |
    "(Confidential < Secret) = True"  |
    "(Unclassified < Secret) = True"  |
    "(Secret < Confidential) = False"  |
    "(Confidential < Unclassified) = False"  |
    "(Secret < Unclassified) = False"
  instance
    apply(intro_classes)
    apply(case_tac [!] x)
    apply(simp_all)
    apply(case_tac  [!] y)
    apply(simp_all)
    apply(case_tac  [!] z)
    apply(simp_all)
    done
  end
  


definition default_node_properties :: "security_level"
  where  "default_node_properties \<equiv> Secret"



fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> security_level) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> edges G. (nP e1) \<le> (nP e2))"

definition receiver_violation :: "bool" where "receiver_violation \<equiv> False"


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



subsection \<open>ENF\<close>
  lemma secret_default_candidate: "\<And> (nP::('v \<Rightarrow> security_level)) e1 e2. \<not> (nP e1) \<le> (nP e2) \<Longrightarrow> \<not> Secret \<le> (nP e2)"
    apply(case_tac "nP e1")
    apply(simp_all)
    apply(case_tac [!] "nP e2")
    apply(simp_all)
    done
  lemma BLP_ENF: "SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form sinvar (\<le>)"
    unfolding SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_def
    by simp
  lemma BLP_ENF_refl: "SecurityInvariant_withOffendingFlows.ENF_refl sinvar (\<le>)"
    unfolding SecurityInvariant_withOffendingFlows.ENF_refl_def
    apply(rule conjI)
     apply(simp add: BLP_ENF)
    apply(simp)
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
   
  interpretation BLPstrict: SecurityInvariant_ACS sinvar default_node_properties
  (*TODO: why is there a where and no "rewrites" in the afp?*)
  rewrites "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = BLP_offending_set"
    unfolding default_node_properties_def
    apply(unfold_locales)
      apply(rule ballI)
      apply(rule SecurityInvariant_withOffendingFlows.ENF_fsts_refl_instance[OF BLP_ENF_refl])
         apply(simp_all add: BLP_ENF BLP_ENF_refl)[3]
      apply(simp add: secret_default_candidate; fail)
     apply(erule default_uniqueness_by_counterexample_ACS)
     apply(rule_tac x="\<lparr> nodes=set [vertex_1,vertex_2], edges = set [(vertex_1,vertex_2)] \<rparr>" in exI, simp)
     apply(simp add: BLP_offending_set graph_ops wf_graph_def)
     apply(rule_tac x="(\<lambda> x. Secret)(vertex_1 := Secret, vertex_2 := Confidential)" in exI, simp)
     apply(rule_tac x="vertex_1" in exI, simp)
     apply(rule_tac x="set [(vertex_1,vertex_2)]" in exI, simp)
     apply(simp add: BLP_offending_set_def)
     apply(rule conjI)
      apply fastforce
     apply (case_tac otherbot, simp_all)
    apply(fact BLP_offending_set)
   done


  lemma TopoS_BLPstrict: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales
   
hide_fact (open) sinvar_mono   

hide_const (open) sinvar receiver_violation default_node_properties

end
