theory TopoS_Stateful_Policy
imports TopoS_Composition_Theory
begin

section\<open>Stateful Policy\<close>


text\<open>Details described in \cite{diekmann2014esss}.\<close>


text\<open>Algorithm\<close>
term TopoS_Composition_Theory.generate_valid_topology
text\<open>generates a valid high-level topology. Now we discuss how to turn this into
       a stateful policy.\<close>

text\<open>
Example:
  SensorNode produces data and has no security level.
  SensorSink has high security level
  SensorNode -> SensorSink, but not the other way round.
  Implementation: UDP in one direction

  Alice is in internal protected subnet. Google can not arbitrarily access Alice.
  Alice sends requests to google.
  It is desirable that Alice gets the response back
  Implementation: TCP and stateful packet filter that allows, once Alice establishes a connection, to get a response back via this connection.

Result:
  IFS violations undesirable.
  ACS violations may be okay under certain conditions.
\<close>

term all_security_requirements_fulfilled

text\<open>@{term "G = (V, E\<^sub>f\<^sub>i\<^sub>x, E\<^sub>s\<^sub>t\<^sub>a\<^sub>t\<^sub>e)"}\<close>
record 'v stateful_policy =
    hosts :: "'v set" \<comment> \<open>nodes, vertices\<close>
    flows_fix :: "('v \<times>'v) set" \<comment> \<open>edges in high-level policy\<close>
    flows_state :: "('v \<times>'v) set" \<comment> \<open>edges that can have stateful flows, i.e. backflows\<close>

text\<open>All the possible ways packets can travel in a @{typ "'v stateful_policy"}.
        They can either choose the fixed links;
        Or use a stateful link, i.e. establish state.
        Once state is established, packets can flow back via the established link.\<close>
definition all_flows :: "'v stateful_policy \<Rightarrow> ('v \<times> 'v) set" where
  "all_flows \<T> \<equiv> flows_fix \<T> \<union> flows_state \<T> \<union> backflows (flows_state \<T>)"


definition stateful_policy_to_network_graph :: "'v stateful_policy \<Rightarrow> 'v graph" where
  "stateful_policy_to_network_graph \<T> = \<lparr> nodes = hosts \<T>, edges = all_flows \<T> \<rparr>"


text\<open>@{typ "'v stateful_policy"} syntactically well-formed\<close>
locale wf_stateful_policy = 
  fixes \<T> :: "'v stateful_policy"
  assumes E_wf: "fst ` (flows_fix \<T>) \<subseteq> (hosts \<T>)"
                   "snd ` (flows_fix \<T>) \<subseteq> (hosts \<T>)"
  and E_state_fix: "flows_state \<T> \<subseteq> flows_fix \<T>"
  and finite_Hosts: "finite (hosts \<T>)"
begin

  lemma E_wfD: assumes "(v,v') \<in> flows_fix \<T>"
    shows "v \<in> hosts \<T>" "v' \<in> hosts \<T>"
    apply -
     apply (rule subsetD[OF E_wf(1)])
     using assms apply force
    apply (rule subsetD[OF E_wf(2)])
    using assms apply force
    done
 
  lemma E_state_valid: "fst ` (flows_state \<T>) \<subseteq> (hosts \<T>)"
                       "snd ` (flows_state \<T>) \<subseteq> (hosts \<T>)"
   apply -
   using E_wf(1) E_state_fix apply(blast)
   using E_wf(2) E_state_fix apply(blast)
   done

  lemma E_state_validD: assumes "(v,v') \<in> flows_state \<T>"
    shows "v \<in> hosts \<T>" "v' \<in> hosts \<T>"
    apply -
     apply (rule subsetD[OF E_state_valid(1)])
     using assms apply force
    apply (rule subsetD[OF E_state_valid(2)])
    using assms apply force
    done

  lemma finite_fix: "finite (flows_fix \<T>)"
  proof -
    from finite_subset[OF E_wf(1) finite_Hosts] have 1: "finite (fst ` flows_fix \<T>)" .
    from finite_subset[OF E_wf(2) finite_Hosts] have 2: "finite (snd ` flows_fix \<T>)" .
    have s: "flows_fix \<T> \<subseteq> (fst ` flows_fix \<T> \<times> snd ` flows_fix \<T>)" by force
    from finite_cartesian_product[OF 1 2] have "finite (fst ` flows_fix \<T> \<times> snd ` flows_fix \<T>)" .
    from finite_subset[OF s this] show ?thesis .
  qed

  lemma finite_state: "finite (flows_state \<T>)"
    using finite_subset[OF E_state_fix finite_fix] by assumption


  lemma finite_backflows_state: "finite (backflows (flows_state \<T>))"
    using [[simproc add: finite_Collect]] by(simp add: backflows_def finite_state)

  lemma E_state_backflows_wf: "fst ` backflows (flows_state \<T>) \<subseteq> (hosts \<T>)"
                         "snd ` backflows (flows_state \<T>) \<subseteq> (hosts \<T>)"
    by(auto simp add: backflows_def E_state_valid E_state_validD)

end


text\<open>Minimizing stateful flows such that only newly added backflows remain\<close>
  definition filternew_flows_state :: "'v stateful_policy \<Rightarrow> ('v \<times> 'v) set" where
    "filternew_flows_state \<T> \<equiv> {(s, r) \<in> flows_state \<T>. (r, s) \<notin> flows_fix \<T>}"

  lemma filternew_subseteq_flows_state: "filternew_flows_state \<T> \<subseteq> flows_state \<T>"
    by(auto simp add: filternew_flows_state_def)

  \<comment> \<open>alternative definitions, all are equal\<close>
  lemma filternew_flows_state_alt: "filternew_flows_state \<T>  = flows_state \<T> - (backflows (flows_fix \<T>))"
    apply(simp add: backflows_def filternew_flows_state_def)
    apply(rule)
     apply blast+
    done
  lemma filternew_flows_state_alt2: "filternew_flows_state \<T>  = {e \<in> flows_state \<T>. e \<notin> backflows (flows_fix \<T>)}"
    apply(simp add: backflows_def filternew_flows_state_def)
    apply(rule)
     apply blast+
    done
  lemma backflows_filternew_flows_state: "backflows (filternew_flows_state \<T>) = (backflows (flows_state \<T>)) - (flows_fix \<T>)"
    by(simp add: filternew_flows_state_alt backflows_minus_backflows)

  lemma stateful_policy_to_network_graph_filternew: "\<lbrakk> wf_stateful_policy \<T> \<rbrakk> \<Longrightarrow> 
    stateful_policy_to_network_graph \<T> = 
    stateful_policy_to_network_graph \<lparr>hosts = hosts \<T>, flows_fix = flows_fix \<T>, flows_state = filternew_flows_state \<T> \<rparr>"
    apply(drule wf_stateful_policy.E_state_fix)
    apply(simp add: stateful_policy_to_network_graph_def all_flows_def)
    apply(rule Set.equalityI)
     apply(simp add: filternew_flows_state_def backflows_def)
     apply(rule, blast)+
    apply(simp add: filternew_flows_state_def backflows_def)
    apply fastforce
    done

  lemma backflows_filternew_disjunct_flows_fix: 
    "\<forall> b \<in> (backflows (filternew_flows_state \<T>)). b \<notin> flows_fix \<T>"
    by(simp add: filternew_flows_state_def backflows_def)





text\<open>Given a high-level policy, we can construct a pretty large syntactically valid low level policy. However, the stateful policy will
       almost certainly violate security requirements!\<close>
  lemma "wf_graph G \<Longrightarrow> wf_stateful_policy \<lparr> hosts = nodes G, flows_fix = nodes G \<times> nodes G, flows_state = nodes G \<times> nodes G \<rparr>"
    by(simp add: wf_stateful_policy_def wf_graph_def)


text\<open>@{const wf_stateful_policy} implies @{term wf_graph}\<close>
  lemma wf_stateful_policy_is_wf_graph: "wf_stateful_policy \<T> \<Longrightarrow> wf_graph \<lparr>nodes = hosts \<T>, edges = all_flows \<T>\<rparr>"
    apply(frule wf_stateful_policy.E_state_backflows_wf)
    apply(frule wf_stateful_policy.E_state_backflows_wf(2))
    apply(frule wf_stateful_policy.E_state_valid)
    apply(frule wf_stateful_policy.E_state_valid(2))
    apply(frule wf_stateful_policy.E_wf)
    apply(frule wf_stateful_policy.E_wf(2))
    apply(simp add: all_flows_def wf_graph_def wf_stateful_policy_def 
          wf_stateful_policy.finite_fix wf_stateful_policy.finite_state wf_stateful_policy.finite_backflows_state)
    apply(rule conjI)
     apply (metis image_Un sup.bounded_iff)+
    done


(*we use the second way of writing it in the paper*)
lemma "(\<forall>F \<in> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<T> ). F \<subseteq> backflows (filternew_flows_state \<T>)) \<longleftrightarrow>
    \<Union>(get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<T>)) \<subseteq> (backflows (flows_state \<T>)) - (flows_fix \<T>)"
    by(simp add: filternew_flows_state_alt backflows_minus_backflows, blast)


text\<open>When is a stateful policy @{term "\<T>"} compliant with a high-level policy @{term "G"} and the security requirements @{term "M"}?\<close>
locale stateful_policy_compliance =  
  fixes \<T> :: "('v::vertex) stateful_policy"
  fixes G :: "'v graph"
  fixes M :: "('v) SecurityInvariant_configured list"
  assumes
    \<comment> \<open>the graph must be syntactically valid\<close>
    wfG: "wf_graph G"
    and
    \<comment> \<open>security requirements must be valid\<close>
    validReqs: "valid_reqs M"
    and
    \<comment> \<open>the high-level policy must be valid\<close>
    high_level_policy_valid: "all_security_requirements_fulfilled M G"
    and
    \<comment> \<open>the stateful policy must be syntactically valid\<close>
    stateful_policy_wf:
    "wf_stateful_policy \<T>"
    and
    \<comment> \<open>the stateful policy must talk about the same nodes as the high-level policy\<close>
    hosts_nodes:
    "hosts \<T> = nodes G"
    and
    \<comment> \<open>only flows that are allowed in the high-level policy are allowed in the stateful policy\<close>
    flows_edges:
    "flows_fix \<T> \<subseteq> edges G"
    and
    \<comment> \<open>the low level policy must comply with the high-level policy\<close>
      \<comment> \<open>all information flow strategy requirements must be fulfilled, i.e. no leaks!\<close>
      compliant_stateful_IFS: 
        "all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<T>)"
      and
      \<comment> \<open>No Access Control side effects must occur\<close>
      compliant_stateful_ACS: 
        "\<forall>F \<in> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<T> ). F \<subseteq> backflows (filternew_flows_state \<T>)"
        
  begin
    lemma compliant_stateful_ACS_no_side_effects_filternew_helper: 
      "\<forall> E \<subseteq> backflows (filternew_flows_state \<T>). \<forall> F \<in> get_offending_flows (get_ACS M) \<lparr> nodes = hosts \<T>, edges = flows_fix \<T> \<union> E \<rparr>. F \<subseteq> E"
    proof(rule, rule)
      fix E
      assume a1: "E \<subseteq> backflows (filternew_flows_state \<T>)"
      from validReqs have valid_ReqsACS: "valid_reqs (get_ACS M)" by(simp add: get_ACS_def valid_reqs_def)

      from compliant_stateful_ACS stateful_policy_to_network_graph_filternew[OF stateful_policy_wf] have compliant_stateful_ACS_only_state_violations_filternew: 
      "\<forall>F \<in> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = hosts \<T>, flows_fix = flows_fix \<T>, flows_state = filternew_flows_state \<T> \<rparr>). F \<subseteq> backflows (filternew_flows_state \<T>)" by simp
    
      from wf_stateful_policy_is_wf_graph[OF stateful_policy_wf] have wfGfilternew: 
        "wf_graph \<lparr>nodes = hosts \<T>, edges = flows_fix \<T> \<union> filternew_flows_state \<T> \<union> backflows (filternew_flows_state \<T>)\<rparr>"
        apply(simp add: all_flows_def filternew_flows_state_alt backflows_minus_backflows)
        by(auto simp add: wf_graph_def)
    
      from wf_stateful_policy.E_state_fix[OF stateful_policy_wf] filternew_subseteq_flows_state have flows_fix_un_filternew_simp: "flows_fix \<T> \<union> filternew_flows_state \<T> = flows_fix \<T>" by blast
    
      from compliant_stateful_ACS_only_state_violations_filternew have 
        "\<And>m. m \<in> set (get_ACS M) \<Longrightarrow> 
        \<Union>(c_offending_flows m \<lparr>nodes = hosts \<T>, edges = flows_fix \<T> \<union> filternew_flows_state \<T> \<union> backflows (filternew_flows_state \<T>)\<rparr>) \<subseteq> backflows (filternew_flows_state \<T>)"
        by(simp add: stateful_policy_to_network_graph_def all_flows_def get_offending_flows_def, blast)
    
      \<comment> \<open>idea: use @{thm compliant_stateful_ACS} with the @{thm configured_SecurityInvariant.Un_set_offending_flows_bound_minus_subseteq} 
        lemma and substract @{term "backflows (filternew_flows_state \<T>) - E"}, on the right hand side @{term E} remains, as Graph's edges @{term "flows_fix \<T>  \<union> E"} remains\<close>

      from configured_SecurityInvariant.Un_set_offending_flows_bound_minus_subseteq[where X="backflows (filternew_flows_state \<T>)", OF _ wfGfilternew this]
        \<open>valid_reqs (get_ACS M)\<close>
        have
        "\<And> m E. m \<in> set (get_ACS M) \<Longrightarrow>
        \<forall>F\<in>c_offending_flows m \<lparr>nodes = hosts \<T>, edges = flows_fix \<T> \<union> filternew_flows_state \<T> \<union> backflows (filternew_flows_state \<T>) - E\<rparr>. F \<subseteq> backflows (filternew_flows_state \<T>) - E"
        by(auto simp add: all_flows_def valid_reqs_def)
      from this flows_fix_un_filternew_simp have rule:
        "\<And> m E. m \<in> set (get_ACS M) \<Longrightarrow>
        \<forall>F\<in>c_offending_flows m \<lparr>nodes = hosts \<T>, edges = flows_fix \<T> \<union> backflows (filternew_flows_state \<T>) - E\<rparr>. F \<subseteq> backflows (filternew_flows_state \<T>) - E"  
        by simp
    
      from  backflows_finite rev_finite_subset[OF wf_stateful_policy.finite_state[OF stateful_policy_wf] filternew_subseteq_flows_state] have
        "finite (backflows (filternew_flows_state \<T>))" by blast
      from a1 this have "finite E" by (metis rev_finite_subset)
    
      from a1 obtain E' where E'_prop1: "backflows (filternew_flows_state \<T>) - E' = E" and E'_prop2: "E' = backflows (filternew_flows_state \<T>) - E" by blast
      from E'_prop2 \<open>finite (backflows (filternew_flows_state \<T>))\<close> \<open>finite E\<close> have "finite E'" by blast
    
      from Set.double_diff[where B="backflows (filternew_flows_state \<T>)" and C="backflows (filternew_flows_state \<T>)" and A="E", OF a1, simplified] have Ebackflowssimp:
        "backflows (filternew_flows_state \<T>) - (backflows (filternew_flows_state \<T>) - E) = E" .
    
      have "flows_fix \<T> \<union> backflows (filternew_flows_state \<T>) - (backflows (filternew_flows_state \<T>) - E) = 
          (flows_fix \<T> - (backflows (filternew_flows_state \<T>))) \<union> E"
          apply(simp add: Set.Un_Diff)
          apply(simp add: Ebackflowssimp)
          by blast
      also have "(flows_fix \<T> - (backflows (filternew_flows_state \<T>))) \<union> E = flows_fix \<T>  \<union> E" using backflows_filternew_disjunct_flows_fix by blast
      finally have flows_E_simp: "flows_fix \<T> \<union> backflows (filternew_flows_state \<T>) - (backflows (filternew_flows_state \<T>) - E) = flows_fix \<T>  \<union> E" .
    
      from rule[simplified E'_prop1 E'_prop2] have
      "\<And>m. m \<in> set (get_ACS M) \<Longrightarrow>
      \<forall>F\<in>c_offending_flows m \<lparr>nodes = hosts \<T>, edges = flows_fix \<T> \<union> backflows (filternew_flows_state \<T>) - (backflows (filternew_flows_state \<T>) - E)\<rparr>.
       F \<subseteq> backflows (filternew_flows_state \<T>) - (backflows (filternew_flows_state \<T>) - E)"
       by(simp)
      from this Ebackflowssimp flows_E_simp have
      "\<And>m. m \<in> set (get_ACS M) \<Longrightarrow>
        \<forall>F\<in>c_offending_flows m \<lparr>nodes = hosts \<T>, edges = flows_fix \<T> \<union> E\<rparr>. F \<subseteq> E"
       by simp
      thus  "\<forall>F\<in>get_offending_flows (get_ACS M) \<lparr>nodes = hosts \<T>, edges = flows_fix \<T> \<union> E\<rparr>. F \<subseteq> E"
        by(simp add: get_offending_flows_def)
      qed
    
    
    theorem compliant_stateful_ACS_no_side_effects:
      "\<forall> E \<subseteq> backflows (flows_state \<T>). \<forall> F \<in> get_offending_flows(get_ACS M) \<lparr> nodes = hosts \<T>, edges = flows_fix \<T> \<union> E \<rparr>. F \<subseteq> E"
    proof -
      from compliant_stateful_ACS stateful_policy_to_network_graph_filternew[OF stateful_policy_wf] have a1: 
      "\<forall>F \<in> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = hosts \<T>, flows_fix = flows_fix \<T>, flows_state = filternew_flows_state \<T> \<rparr>). F \<subseteq> backflows (filternew_flows_state \<T>)" by simp
    
      have backflows_split: "backflows (filternew_flows_state \<T>) \<union> (backflows (flows_state \<T>) - backflows (filternew_flows_state \<T>)) = backflows (flows_state \<T>)"
        by (metis Diff_subset Un_Diff_cancel Un_absorb1 backflows_minus_backflows filternew_flows_state_alt)
    
      have 
        "\<forall>E\<subseteq>backflows (filternew_flows_state \<T>) \<union> (backflows (flows_state \<T>) - backflows (filternew_flows_state \<T>)). 
             \<forall>F\<in>get_offending_flows (get_ACS M) \<lparr>nodes = hosts \<T>, edges = flows_fix \<T> \<union> E\<rparr>. F \<subseteq> E"
        proof(rule allI, rule impI)
          fix E
          assume h1: "E \<subseteq> backflows (filternew_flows_state \<T>) \<union> (backflows (flows_state \<T>) - backflows (filternew_flows_state \<T>))"
    
          have "\<exists> E1 E2. E1 \<subseteq> backflows (filternew_flows_state \<T>) \<and> E2 \<subseteq> (backflows (flows_state \<T>) - backflows (filternew_flows_state \<T>)) \<and> E1 \<union> E2 = E \<and> E1 \<inter> E2 = {}"
            apply(rule_tac x="{e \<in> E. e \<in> backflows (filternew_flows_state \<T>)}" in exI)
            apply(rule_tac x="{e \<in> E. e \<in>(backflows (flows_state \<T>) - backflows (filternew_flows_state \<T>))}" in exI)
            apply(simp)
            apply(rule)
             apply blast
            apply(rule)
             apply blast
            apply(rule)
             using h1 apply blast
            using backflows_filternew_disjunct_flows_fix by blast
    
          from this obtain E1 E2 where E1_prop: "E1 \<subseteq> backflows (filternew_flows_state \<T>)" and E2_prop: "E2 \<subseteq> (backflows (flows_state \<T>) - backflows (filternew_flows_state \<T>))" and "E = E1 \<union> E2" and "E1 \<inter> E2 = {}" by blast
    
          \<comment> \<open>the stateful flows are @{text "\<subseteq>"} fix flows. If substracting the new stateful flows, onyly the existing fix flows remain\<close>
          from E2_prop filternew_flows_state_alt have "E2 \<subseteq> flows_fix \<T>" by (metis (hide_lams, no_types) Diff_subset_conv Un_Diff_cancel2 backflows_minus_backflows inf_sup_ord(3) order.trans)
          \<comment> \<open>hence, E2 disappears\<close>
          from Set.Un_absorb1[OF this] have E2_absorb: "flows_fix \<T> \<union> E2 = flows_fix \<T>" by blast
    
          from \<open>E = E1 \<union> E2\<close> have E2E1eq: "E2 \<union> E1 = E" by blast
    
          from \<open>E = E1 \<union> E2\<close> \<open>E1 \<inter> E2 = {}\<close> have "E1 \<subseteq> E" by simp
    
          from compliant_stateful_ACS_no_side_effects_filternew_helper E1_prop have "\<forall>F\<in>get_offending_flows (get_ACS M) \<lparr>nodes = hosts \<T>, edges = flows_fix \<T> \<union> E1 \<rparr>. F \<subseteq> E1" by simp
          hence "\<forall>F\<in>get_offending_flows (get_ACS M) \<lparr>nodes = hosts \<T>, edges = flows_fix \<T> \<union> E2 \<union> E1 \<rparr>. F \<subseteq> E1" using E2_absorb[symmetric] by simp
          hence "\<forall>F\<in>get_offending_flows (get_ACS M) \<lparr>nodes = hosts \<T>, edges = flows_fix \<T> \<union> E \<rparr>. F \<subseteq> E1" using E2E1eq by (metis Un_assoc)
    
          from this \<open>E1 \<subseteq> E\<close> show "\<forall>F\<in>get_offending_flows (get_ACS M) \<lparr>nodes = hosts \<T>, edges = flows_fix \<T> \<union> E\<rparr>. F \<subseteq> E" by blast
        qed
    
      from this backflows_split show ?thesis by presburger
    qed


    corollary compliant_stateful_ACS_no_side_effects': "\<forall> E \<subseteq> backflows (flows_state \<T>). \<forall> F \<in> get_offending_flows(get_ACS M) \<lparr> nodes = hosts \<T>, edges = flows_fix \<T> \<union> flows_state \<T> \<union> E \<rparr>. F \<subseteq> E"
      using compliant_stateful_ACS_no_side_effects wf_stateful_policy.E_state_fix[OF stateful_policy_wf] by (metis Un_absorb2)


    text\<open>The high level graph generated from the low level policy is a valid graph\<close>
    lemma valid_stateful_policy: "wf_graph \<lparr>nodes = hosts \<T>, edges = all_flows \<T>\<rparr>"
      by(rule wf_stateful_policy_is_wf_graph,fact stateful_policy_wf)

    text\<open>The security requirements are definitely fulfilled if we consider only the fixed flows and the
           normal direction of the stateful flows (i.e. no backflows).
           I.e. considering no states, everything must be fulfilled\<close>
    lemma compliant_stateful_ACS_static_valid: "all_security_requirements_fulfilled (get_ACS M) \<lparr> nodes = hosts \<T>, edges = flows_fix \<T>  \<rparr>"
    proof -
      from validReqs have valid_ReqsACS: "valid_reqs (get_ACS M)" by(simp add: get_ACS_def valid_reqs_def)
      from wfG hosts_nodes[symmetric] have wfG': "wf_graph \<lparr> nodes = hosts \<T>, edges = edges G  \<rparr>" by(case_tac G, simp)
      from high_level_policy_valid have "all_security_requirements_fulfilled (get_ACS M) G"
        by(simp add: get_ACS_def all_security_requirements_fulfilled_def)
      from this hosts_nodes[symmetric] have "all_security_requirements_fulfilled (get_ACS M) \<lparr> nodes = hosts \<T>, edges = edges G  \<rparr>"
        by(case_tac G, simp)
      from all_security_requirements_fulfilled_mono[OF valid_ReqsACS flows_edges wfG' this] show ?thesis .
    qed
    theorem compliant_stateful_ACS_static_valid':
      "all_security_requirements_fulfilled M \<lparr> nodes = hosts \<T>, edges = flows_fix \<T> \<union> flows_state \<T>  \<rparr>"
      proof -
        from validReqs have valid_ReqsIFS: "valid_reqs (get_IFS M)" by(simp add: get_IFS_def valid_reqs_def)
    
        \<comment> \<open>show that it holds for IFS, by monotonicity as it holds for more in IFS\<close>
        from all_security_requirements_fulfilled_mono[OF valid_ReqsIFS _ valid_stateful_policy compliant_stateful_IFS[unfolded stateful_policy_to_network_graph_def]] have
          goalIFS: "all_security_requirements_fulfilled (get_IFS M) \<lparr> nodes = hosts \<T>, edges = flows_fix \<T> \<union> flows_state \<T>  \<rparr>" by(simp add: all_flows_def)

        from wf_stateful_policy.E_state_fix[OF stateful_policy_wf] have "flows_fix \<T> \<union> flows_state \<T> =  flows_fix \<T>" by blast
        from this compliant_stateful_ACS_static_valid have goalACS:
          "all_security_requirements_fulfilled (get_ACS M) \<lparr> nodes = hosts \<T>, edges = flows_fix \<T> \<union> flows_state \<T>  \<rparr>" by simp
          
        \<comment> \<open>ACS and IFS together form M, we know it holds for ACS\<close>
        from goalACS goalIFS show ?thesis 
          apply(simp add: all_security_requirements_fulfilled_def get_IFS_def get_ACS_def)
          by fastforce
    qed

    text\<open>The flows with state are a subset of the flows allowed by the policy\<close>
    theorem flows_state_edges: "flows_state \<T> \<subseteq> edges G"
      using wf_stateful_policy.E_state_fix[OF stateful_policy_wf] flows_edges by simp


    text\<open>All offending flows are subsets of the reveres stateful flows\<close>
    lemma compliant_stateful_ACS_only_state_violations:
      "\<forall>F \<in> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<T>). F \<subseteq> backflows (flows_state \<T>)"
      proof -
        have "backflows (filternew_flows_state \<T>) \<subseteq> backflows (flows_state \<T>)" by (metis Diff_subset backflows_minus_backflows filternew_flows_state_alt)
        from compliant_stateful_ACS this have 
          "\<forall> F \<in> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<T>). F \<subseteq> backflows (flows_state \<T>)"
          by (metis subset_trans)
        thus ?thesis .
      qed
    theorem compliant_stateful_ACS_only_state_violations': "\<forall>F \<in> get_offending_flows M (stateful_policy_to_network_graph \<T>). F \<subseteq> backflows (flows_state \<T>)"
      proof -
        from validReqs have valid_ReqsIFS: "valid_reqs (get_IFS M)" by(simp add: get_IFS_def valid_reqs_def)
        have offending_split: "\<And>G. get_offending_flows M G = (get_offending_flows (get_IFS M) G \<union> get_offending_flows (get_ACS M) G)"
          apply(simp add: get_offending_flows_def get_IFS_def get_ACS_def) by blast 
       show ?thesis
        apply(subst offending_split)
        using compliant_stateful_ACS_only_state_violations 
              all_security_requirements_fulfilled_imp_get_offending_empty[OF valid_ReqsIFS compliant_stateful_IFS]
        by auto
      qed


    text \<open>All violations are backflows of valid flows\<close>
    corollary compliant_stateful_ACS_only_state_violations_union: "\<Union>(get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<T>)) \<subseteq> backflows (flows_state \<T>)"
    using compliant_stateful_ACS_only_state_violations by fastforce

    corollary compliant_stateful_ACS_only_state_violations_union': "\<Union>(get_offending_flows M (stateful_policy_to_network_graph \<T>)) \<subseteq> backflows (flows_state \<T>)"
    using compliant_stateful_ACS_only_state_violations' by fastforce

    text\<open>All individual flows cause no side effects, i.e. each backflow causes at most itself as violation, no other
           side-effect violations are induced.\<close>
    lemma  compliant_stateful_ACS_no_state_singleflow_side_effect:
      "\<forall> (v\<^sub>1, v\<^sub>2) \<in> backflows (flows_state \<T>). 
       \<Union>(get_offending_flows(get_ACS M) \<lparr> nodes = hosts \<T>, edges = flows_fix \<T> \<union> flows_state \<T> \<union> {(v\<^sub>1, v\<^sub>2)} \<rparr>) \<subseteq> {(v\<^sub>1, v\<^sub>2)}"
    using compliant_stateful_ACS_no_side_effects' by blast
  end


subsection\<open>Summarizing the important theorems\<close>

  text\<open>No information flow security requirements are violated (including all added stateful flows)\<close>
  thm stateful_policy_compliance.compliant_stateful_IFS
  
  
  text\<open>There are not access control side effects when allowing stateful backflows. 
          I.e. for all possible subsets of the to-allow backflows, the violations they cause are only these backflows themselves\<close>
  thm stateful_policy_compliance.compliant_stateful_ACS_no_side_effects'
  
    text\<open>Also, considering all backflows individually, they cause no side effect, i.e. the only violation added is the backflow itself\<close>
    thm stateful_policy_compliance.compliant_stateful_ACS_no_state_singleflow_side_effect
  
    text\<open>In particular, all introduced offending flows for access control strategies are at most the stateful backflows\<close>
    thm stateful_policy_compliance.compliant_stateful_ACS_only_state_violations_union
    text\<open>Which implies: all introduced offending flows are at most the stateful backflows\<close>
    thm stateful_policy_compliance.compliant_stateful_ACS_only_state_violations_union'
    
  
  text\<open>Disregarding the backflows of stateful flows, all security requirements are fulfilled.\<close>
  thm stateful_policy_compliance.compliant_stateful_ACS_static_valid'


 
end
