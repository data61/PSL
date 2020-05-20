theory TopoS_Stateful_Policy_impl
imports TopoS_Composition_Theory_impl TopoS_Stateful_Policy_Algorithm
begin

section\<open>Stateful Policy -- List Implementaion\<close>

record 'v stateful_list_policy =
    hostsL :: "'v list"
    flows_fixL :: "('v \<times>'v) list"
    flows_stateL :: "('v \<times>'v) list"


definition stateful_list_policy_to_list_graph :: "'v stateful_list_policy \<Rightarrow> 'v list_graph" where
  "stateful_list_policy_to_list_graph \<T> = \<lparr> nodesL = hostsL \<T>, edgesL = (flows_fixL \<T>) @ [e \<leftarrow> flows_stateL \<T>. e \<notin> set (flows_fixL \<T>)] @ [e \<leftarrow> backlinks (flows_stateL \<T>). e \<notin> set (flows_fixL \<T>)] \<rparr>"

lemma stateful_list_policy_to_list_graph_complies:
  "list_graph_to_graph (stateful_list_policy_to_list_graph \<lparr> hostsL = V, flows_fixL = E\<^sub>f, flows_stateL = E\<^sub>\<sigma> \<rparr>) = 
    stateful_policy_to_network_graph \<lparr> hosts = set V, flows_fix = set E\<^sub>f, flows_state = set E\<^sub>\<sigma> \<rparr>"
    by(simp add: stateful_list_policy_to_list_graph_def stateful_policy_to_network_graph_def all_flows_def list_graph_to_graph_def backlinks_correct, blast)

lemma wf_list_graph_stateful_list_policy_to_list_graph: 
    "wf_list_graph G \<Longrightarrow> distinct E \<Longrightarrow> set E \<subseteq> set (edgesL G) \<Longrightarrow> wf_list_graph (stateful_list_policy_to_list_graph \<lparr>hostsL = nodesL G, flows_fixL = edgesL G, flows_stateL = E\<rparr>)"
  apply(simp add: wf_list_graph_def stateful_list_policy_to_list_graph_def)
  apply(rule conjI)
   apply(simp add: backlinks_distinct)
  apply(rule conjI)
   apply(simp add: backlinks_set)
   apply(blast)
  apply(rule conjI)
   apply(simp add: backlinks_set)
   apply(blast)
  apply(simp add: wf_list_graph_axioms_def)
   apply(rule conjI)
   apply(simp add: backlinks_set)
   apply(force)
  apply(simp add: backlinks_set)
  apply(clarsimp)
  apply(erule disjE)
   apply(auto)[1]
  apply(erule disjE)
   apply(auto)[1]
  by force
  


subsection\<open>Algorithms\<close>

   fun filter_IFS_no_violations_accu :: "'v list_graph \<Rightarrow> 'v SecurityInvariant list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list" where
      "filter_IFS_no_violations_accu G M accu [] = accu" |
      "filter_IFS_no_violations_accu G M accu (e#Es) = (if
        all_security_requirements_fulfilled (TopoS_Composition_Theory_impl.get_IFS M) (stateful_list_policy_to_list_graph \<lparr> hostsL = nodesL G, flows_fixL = edgesL G, flows_stateL = (e#accu) \<rparr>)
        then filter_IFS_no_violations_accu G M (e#accu) Es
        else filter_IFS_no_violations_accu G M accu Es)"
    definition filter_IFS_no_violations :: "'v list_graph \<Rightarrow> 'v SecurityInvariant list \<Rightarrow> ('v \<times> 'v) list" where
      "filter_IFS_no_violations G M = filter_IFS_no_violations_accu G M [] (edgesL G)"

   lemma filter_IFS_no_violations_accu_distinct: "\<lbrakk> distinct (Es@accu) \<rbrakk> \<Longrightarrow> distinct (filter_IFS_no_violations_accu G M accu Es)"
    apply(induction Es arbitrary: accu)
     by(simp_all)

   lemma filter_IFS_no_violations_accu_complies:
    "\<lbrakk>\<forall> (m_impl, m_spec) \<in> set M. SecurityInvariant_complies_formal_def m_impl m_spec;
      wf_list_graph G; set Es \<subseteq> set (edgesL G); set accu \<subseteq> set (edgesL G); distinct (Es@accu) \<rbrakk> \<Longrightarrow>
      filter_IFS_no_violations_accu G (get_impl M) accu Es = TopoS_Stateful_Policy_Algorithm.filter_IFS_no_violations_accu (list_graph_to_graph G) (get_spec M) accu Es"
      proof(induction Es arbitrary: accu)
      case Nil
        thus ?case by(simp add: get_impl_def get_spec_def)
      next
      case (Cons e Es)
        \<comment> \<open>@{thm Cons.IH[OF Cons.prems(1) Cons.prems(2)]}\<close>
        let ?caseDistinction = "all_security_requirements_fulfilled (TopoS_Composition_Theory_impl.get_IFS (get_impl M)) (stateful_list_policy_to_list_graph \<lparr> hostsL = nodesL G, flows_fixL = edgesL G, flows_stateL = (e#accu) \<rparr>)"

        from get_IFS_get_ACS_select_simps(2)[OF Cons.prems(1)] have get_impl_zip_simp: "(get_impl (zip (TopoS_Composition_Theory_impl.get_IFS (get_impl M)) (TopoS_Composition_Theory.get_IFS (get_spec M)))) = TopoS_Composition_Theory_impl.get_IFS (get_impl M)" by simp
          
        from get_IFS_get_ACS_select_simps(3)[OF Cons.prems(1)] have get_spec_zip_simp: "(get_spec (zip (TopoS_Composition_Theory_impl.get_IFS (get_impl M)) (TopoS_Composition_Theory.get_IFS (get_spec M)))) = TopoS_Composition_Theory.get_IFS (get_spec M)" by simp
     
        from Cons.prems(3) Cons.prems(4) have "set (e # accu) \<subseteq> set (edgesL G)" by simp
        from Cons.prems(4) have "set (accu) \<subseteq> set (edgesL G)" by simp
        from Cons.prems(5) have "distinct (e # accu)" by simp
        from Cons.prems(3) have "set Es \<subseteq> set (edgesL G)" by simp
        from Cons.prems(5) have "distinct (Es @ accu)" by simp
        from Cons.prems(5) have "distinct (Es @ (e # accu))" by simp

        from Cons.prems(2) have validLG: "wf_list_graph (stateful_list_policy_to_list_graph \<lparr>hostsL = nodesL G, flows_fixL = edgesL G, flows_stateL = e # accu\<rparr>)"
          apply(rule wf_list_graph_stateful_list_policy_to_list_graph)
           apply(fact \<open>distinct (e # accu)\<close>)
          apply(fact \<open>set (e # accu) \<subseteq> set (edgesL G)\<close>)
          done


        from get_IFS_get_ACS_select_simps(1)[OF Cons.prems(1)]
        have "\<forall> (m_impl, m_spec) \<in> set (zip (get_IFS (get_impl M)) (TopoS_Composition_Theory.get_IFS (get_spec M))). SecurityInvariant_complies_formal_def m_impl m_spec" .
        from all_security_requirements_fulfilled_complies[OF this] have all_security_requirements_fulfilled_eq_rule: 
        "\<And>G. wf_list_graph G \<Longrightarrow>
            TopoS_Composition_Theory_impl.all_security_requirements_fulfilled (TopoS_Composition_Theory_impl.get_IFS (get_impl M)) G =
            TopoS_Composition_Theory.all_security_requirements_fulfilled (TopoS_Composition_Theory.get_IFS (get_spec M)) (list_graph_to_graph G)"
            by(simp add: get_impl_zip_simp get_spec_zip_simp)

        have case_impl_spec: "?caseDistinction \<longleftrightarrow> TopoS_Composition_Theory.all_security_requirements_fulfilled (TopoS_Composition_Theory.get_IFS (get_spec M)) (stateful_policy_to_network_graph \<lparr> hosts = set (nodesL G), flows_fix = set (edgesL G), flows_state = set (e#accu) \<rparr>)"
          apply(subst all_security_requirements_fulfilled_eq_rule[OF validLG])
          by(simp add: stateful_list_policy_to_list_graph_complies)

        show ?case
          proof(case_tac ?caseDistinction)
          assume cTrue: ?caseDistinction
          
          from cTrue have g1: "TopoS_Stateful_Policy_impl.filter_IFS_no_violations_accu G (get_impl M) accu (e # Es) = TopoS_Stateful_Policy_impl.filter_IFS_no_violations_accu G (get_impl M) (e # accu) Es" by simp

          from cTrue[simplified case_impl_spec] have g2: "TopoS_Stateful_Policy_Algorithm.filter_IFS_no_violations_accu (list_graph_to_graph G) (get_spec M) accu (e # Es) =
            TopoS_Stateful_Policy_Algorithm.filter_IFS_no_violations_accu (list_graph_to_graph G) (get_spec M) (e#accu)Es"
            by(simp add: list_graph_to_graph_def)

          show ?case
            apply(simp only: g1 g2)
            using Cons.IH[OF Cons.prems(1) Cons.prems(2) \<open>set Es \<subseteq> set (edgesL G)\<close> \<open>set (e # accu) \<subseteq> set (edgesL G)\<close> \<open>distinct (Es @ (e # accu))\<close>] by simp
        next
          assume cFalse: "\<not> ?caseDistinction"

          from cFalse have g1: "TopoS_Stateful_Policy_impl.filter_IFS_no_violations_accu G (get_impl M) accu (e # Es) = TopoS_Stateful_Policy_impl.filter_IFS_no_violations_accu G (get_impl M) accu Es" by simp

          from cFalse[simplified case_impl_spec] have g2: "TopoS_Stateful_Policy_Algorithm.filter_IFS_no_violations_accu (list_graph_to_graph G) (get_spec M) accu (e # Es) =
            TopoS_Stateful_Policy_Algorithm.filter_IFS_no_violations_accu (list_graph_to_graph G) (get_spec M) accu Es"
            by(simp add: list_graph_to_graph_def)

          show ?case
            apply(simp only: g1 g2)
            using Cons.IH[OF Cons.prems(1) Cons.prems(2) \<open>set Es \<subseteq> set (edgesL G)\<close> \<open>set accu \<subseteq> set (edgesL G)\<close> \<open>distinct (Es @ accu)\<close>] by simp
          qed
       qed



   lemma filter_IFS_no_violations_complies:
    "\<lbrakk> \<forall> (m_impl, m_spec) \<in> set M. SecurityInvariant_complies_formal_def m_impl m_spec; wf_list_graph G \<rbrakk> \<Longrightarrow>
       filter_IFS_no_violations G (get_impl M) = TopoS_Stateful_Policy_Algorithm.filter_IFS_no_violations (list_graph_to_graph G) (get_spec M) (edgesL G)"
    apply(unfold filter_IFS_no_violations_def TopoS_Stateful_Policy_Algorithm.filter_IFS_no_violations_def) 
    apply(rule filter_IFS_no_violations_accu_complies)
        apply(simp_all)
    apply(simp add: wf_list_graph_def)
    done





    fun filter_compliant_stateful_ACS_accu :: "'v list_graph \<Rightarrow> 'v SecurityInvariant list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list" where
      "filter_compliant_stateful_ACS_accu G M accu [] = accu" |
      "filter_compliant_stateful_ACS_accu G M accu (e#Es) = (if
        e \<notin> set (backlinks (edgesL G)) \<and> (\<forall>F \<in> set (implc_get_offending_flows (get_ACS M) (stateful_list_policy_to_list_graph \<lparr> hostsL = nodesL G, flows_fixL = edgesL G, flows_stateL = (e#accu) \<rparr>)). set F \<subseteq> set (backlinks (e#accu)))
        then filter_compliant_stateful_ACS_accu G M (e#accu) Es
        else filter_compliant_stateful_ACS_accu G M accu Es)"
    definition filter_compliant_stateful_ACS :: "'v list_graph \<Rightarrow> 'v SecurityInvariant list \<Rightarrow> ('v \<times> 'v) list" where
      "filter_compliant_stateful_ACS G M = filter_compliant_stateful_ACS_accu G M [] (edgesL G)"


   lemma filter_compliant_stateful_ACS_accu_complies: 
    "\<lbrakk>\<forall> (m_impl, m_spec) \<in> set M. SecurityInvariant_complies_formal_def m_impl m_spec;
      wf_list_graph G; set Es \<subseteq> set (edgesL G); set accu \<subseteq> set (edgesL G); distinct (Es@accu) \<rbrakk> \<Longrightarrow>
      filter_compliant_stateful_ACS_accu G (get_impl M) accu Es = TopoS_Stateful_Policy_Algorithm.filter_compliant_stateful_ACS_accu (list_graph_to_graph G) (get_spec M) accu Es"
      proof(induction Es arbitrary: accu)
      case Nil
        thus ?case by(simp add: get_impl_def get_spec_def)
      next
      case (Cons e Es)
        \<comment> \<open>@{thm Cons.IH[OF Cons.prems(1) Cons.prems(2)]}\<close>
        let ?caseDistinction = "e \<notin> set (backlinks (edgesL G)) \<and> (\<forall>F \<in> set (implc_get_offending_flows (get_ACS (get_impl M)) (stateful_list_policy_to_list_graph \<lparr> hostsL = nodesL G, flows_fixL = edgesL G, flows_stateL = (e#accu) \<rparr>)). set F \<subseteq> set (backlinks (e#accu)))"
        
        have backlinks_simp: "(e \<notin> set (backlinks (edgesL G))) \<longleftrightarrow> (e \<notin> backflows (set (edgesL G)))"
          by(simp add: backlinks_correct)

        have "\<And> G X. (\<forall>F\<in>set (implc_get_offending_flows (TopoS_Composition_Theory_impl.get_ACS (get_impl M)) G). set F \<subseteq> X) =
              (\<forall>F\<in>set ` set (implc_get_offending_flows (TopoS_Composition_Theory_impl.get_ACS (get_impl M)) G). F \<subseteq> X)" by blast
        also have "\<And> G X. wf_list_graph G \<Longrightarrow> (\<forall>F\<in>set ` set (implc_get_offending_flows (TopoS_Composition_Theory_impl.get_ACS (get_impl M)) G). F \<subseteq> X) =
          (\<forall>F\<in>get_offending_flows (TopoS_Composition_Theory.get_ACS (get_spec M)) (list_graph_to_graph G). F \<subseteq> X)"
            using implc_get_offending_flows_complies[OF get_IFS_get_ACS_select_simps(4)[OF Cons.prems(1)], simplified get_IFS_get_ACS_select_simps[OF Cons.prems(1)]] by simp
        finally have implc_get_offending_flows_simp_rule: "\<And>G X. wf_list_graph G \<Longrightarrow> 
          (\<forall>F\<in>set (implc_get_offending_flows (TopoS_Composition_Theory_impl.get_ACS (get_impl M)) G). set F \<subseteq> X) = (\<forall>F\<in>get_offending_flows (TopoS_Composition_Theory.get_ACS (get_spec M)) (list_graph_to_graph G). F \<subseteq> X)" .


        from Cons.prems(3) Cons.prems(4) have "set (e # accu) \<subseteq> set (edgesL G)" by simp
        from Cons.prems(4) have "set (accu) \<subseteq> set (edgesL G)" by simp
        from Cons.prems(5) have "distinct (e # accu)" by simp
        from Cons.prems(3) have "set Es \<subseteq> set (edgesL G)" by simp
        from Cons.prems(5) have "distinct (Es @ accu)" by simp
        from Cons.prems(5) have "distinct (Es @ (e # accu))" by simp
        from Cons.prems(2) have validLG: "wf_list_graph (stateful_list_policy_to_list_graph \<lparr>hostsL = nodesL G, flows_fixL = edgesL G, flows_stateL = e # accu\<rparr>)"
          apply(rule wf_list_graph_stateful_list_policy_to_list_graph)
           apply(fact \<open>distinct (e # accu)\<close>)
          apply(fact \<open>set (e # accu) \<subseteq> set (edgesL G)\<close>)
          done

        have "set (backlinks (e # accu)) = backflows (insert e (set accu))"
          by(simp add: backlinks_set backflows_def)
        
        \<comment> \<open>@{thm implc_get_offending_flows_simp_rule[OF validLG]}\<close>
        have case_impl_spec: "?caseDistinction \<longleftrightarrow> (
          e \<notin> backflows (set (edgesL G)) \<and> (\<forall>F \<in> get_offending_flows (TopoS_Composition_Theory.get_ACS (get_spec M)) (stateful_policy_to_network_graph \<lparr> hosts = set (nodesL G), flows_fix = set (edgesL G), flows_state = set (e#accu) \<rparr>). F \<subseteq> (backflows (set (e#accu)))))" 
          apply(simp add: backlinks_simp)
          apply(simp add: implc_get_offending_flows_simp_rule[OF validLG])
          apply(simp add: stateful_list_policy_to_list_graph_complies)
          by(simp add: \<open>set (backlinks (e # accu)) = backflows (insert e (set accu))\<close>)
          

        show ?case
          proof(case_tac ?caseDistinction)
          assume cTrue: ?caseDistinction
          
          from cTrue have g1: "TopoS_Stateful_Policy_impl.filter_compliant_stateful_ACS_accu G (get_impl M) accu (e # Es) =  TopoS_Stateful_Policy_impl.filter_compliant_stateful_ACS_accu G (get_impl M) (e#accu) Es" by simp

          from cTrue[simplified case_impl_spec] have g2: "TopoS_Stateful_Policy_Algorithm.filter_compliant_stateful_ACS_accu (list_graph_to_graph G) (get_spec M) accu (e # Es) =
            TopoS_Stateful_Policy_Algorithm.filter_compliant_stateful_ACS_accu (list_graph_to_graph G) (get_spec M) (e#accu) Es"
            by(simp add: list_graph_to_graph_def)

          show ?case
            apply(simp only: g1 g2)
            using Cons.IH[OF Cons.prems(1) Cons.prems(2) \<open>set Es \<subseteq> set (edgesL G)\<close> \<open>set (e # accu) \<subseteq> set (edgesL G)\<close> \<open>distinct (Es @ (e # accu))\<close>] by simp
        next
          assume cFalse: "\<not> (?caseDistinction)"

          from cFalse have g1: "TopoS_Stateful_Policy_impl.filter_compliant_stateful_ACS_accu G (get_impl M) accu (e # Es)  = TopoS_Stateful_Policy_impl.filter_compliant_stateful_ACS_accu G (get_impl M) accu Es" by force

          from cFalse[simplified case_impl_spec] have g2: "TopoS_Stateful_Policy_Algorithm.filter_compliant_stateful_ACS_accu (list_graph_to_graph G) (get_spec M) accu (e # Es) =
            TopoS_Stateful_Policy_Algorithm.filter_compliant_stateful_ACS_accu (list_graph_to_graph G) (get_spec M) accu Es"
            apply(simp add: list_graph_to_graph_def) by fast

          show ?case
            apply(simp only: g1 g2)
            using Cons.IH[OF Cons.prems(1) Cons.prems(2) \<open>set Es \<subseteq> set (edgesL G)\<close> \<open>set accu \<subseteq> set (edgesL G)\<close> \<open>distinct (Es @ accu)\<close>] by simp
          qed
       qed


   lemma filter_compliant_stateful_ACS_cont_complies:
    "\<lbrakk> \<forall> (m_impl, m_spec) \<in> set M. SecurityInvariant_complies_formal_def m_impl m_spec; wf_list_graph G; set Es \<subseteq> set (edgesL G); distinct Es \<rbrakk> \<Longrightarrow>
       filter_compliant_stateful_ACS_accu G (get_impl M) [] Es = TopoS_Stateful_Policy_Algorithm.filter_compliant_stateful_ACS (list_graph_to_graph G) (get_spec M) Es"
    apply(unfold filter_compliant_stateful_ACS_def TopoS_Stateful_Policy_Algorithm.filter_compliant_stateful_ACS_def) 
    apply(rule filter_compliant_stateful_ACS_accu_complies)
        apply(simp_all)
    done

   lemma filter_compliant_stateful_ACS_complies:
    "\<lbrakk> \<forall> (m_impl, m_spec) \<in> set M. SecurityInvariant_complies_formal_def m_impl m_spec; wf_list_graph G \<rbrakk> \<Longrightarrow>
       filter_compliant_stateful_ACS G (get_impl M) = TopoS_Stateful_Policy_Algorithm.filter_compliant_stateful_ACS (list_graph_to_graph G) (get_spec M) (edgesL G)"
    apply(unfold filter_compliant_stateful_ACS_def TopoS_Stateful_Policy_Algorithm.filter_compliant_stateful_ACS_def) 
    apply(rule filter_compliant_stateful_ACS_accu_complies)
        apply(simp_all)
    apply(simp add: wf_list_graph_def)
    done


(*TODO: show wf_stateful_policy and distinctness and wf_list_graph, ...*)


   definition generate_valid_stateful_policy_IFSACS :: "'v list_graph \<Rightarrow> 'v SecurityInvariant list \<Rightarrow> 'v stateful_list_policy" where
    "generate_valid_stateful_policy_IFSACS G M = (let filterIFS = filter_IFS_no_violations G M in
        (let filterACS = filter_compliant_stateful_ACS_accu G M [] filterIFS in \<lparr> hostsL = nodesL G, flows_fixL = edgesL G, flows_stateL = filterACS \<rparr>))"



  fun inefficient_list_intersect :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "inefficient_list_intersect [] bs = []" |
    "inefficient_list_intersect (a#as) bs = (if a \<in> set bs then a#(inefficient_list_intersect as bs) else inefficient_list_intersect as bs)"
  lemma inefficient_list_intersect_correct: "set (inefficient_list_intersect a b) = (set a) \<inter> (set b)"
    apply(induction a)
     by(simp_all)

  definition generate_valid_stateful_policy_IFSACS_2 :: "'v list_graph \<Rightarrow> 'v SecurityInvariant list \<Rightarrow>  'v stateful_list_policy" where
    "generate_valid_stateful_policy_IFSACS_2 G M =
    \<lparr> hostsL = nodesL G, flows_fixL = edgesL G, flows_stateL = inefficient_list_intersect (filter_IFS_no_violations G M) (filter_compliant_stateful_ACS G M) \<rparr>"


   lemma generate_valid_stateful_policy_IFSACS_2_complies: "\<lbrakk>\<forall> (m_impl, m_spec) \<in> set M. SecurityInvariant_complies_formal_def m_impl m_spec;
          wf_list_graph G;
          valid_reqs (get_spec M);
          TopoS_Composition_Theory.all_security_requirements_fulfilled (get_spec M) (list_graph_to_graph G);
          \<T> = (generate_valid_stateful_policy_IFSACS_2 G (get_impl M))\<rbrakk> \<Longrightarrow> 
   stateful_policy_compliance \<lparr>hosts = set (hostsL \<T>), flows_fix = set (flows_fixL \<T>), flows_state = set (flows_stateL \<T>) \<rparr> (list_graph_to_graph G) (get_spec M)"
    apply(rule_tac edgesList="edgesL G" in generate_valid_stateful_policy_IFSACS_2_stateful_policy_compliance)
        apply(simp)
       apply (metis wf_list_graph_def wf_list_graph_iff_wf_graph)
      apply(simp)
     apply(simp add: list_graph_to_graph_def)
    apply(simp add: TopoS_Stateful_Policy_Algorithm.generate_valid_stateful_policy_IFSACS_2_def TopoS_Stateful_Policy_impl.generate_valid_stateful_policy_IFSACS_2_def)
    apply(simp add: list_graph_to_graph_def inefficient_list_intersect_correct)
    apply(thin_tac "\<T> = _")
    apply(frule(1) filter_compliant_stateful_ACS_complies)
    apply(frule(1) filter_IFS_no_violations_complies)
    apply(thin_tac "_")
    apply(thin_tac "_")
    apply(thin_tac "_")
    apply(thin_tac "_")
    apply(simp)
    by (metis list_graph_to_graph_def)
    



end
