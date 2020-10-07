theory TopoS_Composition_Theory
imports TopoS_Interface TopoS_Helper
begin

section\<open>Composition Theory\<close>

text\<open>Several invariants may apply to one policy.\<close>

text\<open>The security invariants are all collected in a list. 
The list corresponds to the security requirements. 
The list should have the type @{typ "('v graph \<Rightarrow> bool) list"}, i.e.\ a list of predicates over the policy. 
We need in instantiated security invariant, i.e.\ get rid of @{typ "'a"} and @{typ "'b"}\<close>

 \<comment> \<open>An instance (configured) a security invariant I.e.\ a concrete security requirement, in different terminology.\<close>
 record ('v) SecurityInvariant_configured =
    c_sinvar::"('v) graph \<Rightarrow> bool"
    c_offending_flows::"('v) graph \<Rightarrow> ('v \<times> 'v) set set"
    c_isIFS::"bool"

  \<comment> \<open>parameters 1-3 are the @{text "SecurityInvariant"}:
      @{text sinvar} @{text "\<bottom>"} @{text "receiver_violation"}

      Fourth parameter is the host attribute mapping @{text nP}

      
      TODO: probably check @{text "wf_graph"} here and optionally some host-attribute sanity checker as in DomainHierachy.\<close>
  fun new_configured_SecurityInvariant ::
    "((('v::vertex) graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool) \<times> 'a \<times> bool \<times> ('v \<Rightarrow> 'a)) \<Rightarrow> ('v SecurityInvariant_configured) option" where 
      "new_configured_SecurityInvariant (sinvar, defbot, receiver_violation, nP) = 
        ( 
        if SecurityInvariant sinvar defbot receiver_violation then 
          Some \<lparr> 
            c_sinvar = (\<lambda>G. sinvar G nP),
            c_offending_flows = (\<lambda>G. SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G nP),
            c_isIFS = receiver_violation
          \<rparr>
        else None
        )"

   declare new_configured_SecurityInvariant.simps[simp del]

   lemma new_configured_TopoS_sinvar_correct:
   "SecurityInvariant sinvar defbot receiver_violation \<Longrightarrow> 
   c_sinvar (the (new_configured_SecurityInvariant (sinvar, defbot, receiver_violation, nP))) = (\<lambda>G. sinvar G nP)"
   by(simp add: Let_def new_configured_SecurityInvariant.simps)

   lemma new_configured_TopoS_offending_flows_correct:
   "SecurityInvariant sinvar defbot receiver_violation \<Longrightarrow> 
   c_offending_flows (the (new_configured_SecurityInvariant (sinvar, defbot, receiver_violation, nP))) = 
   (\<lambda>G. SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G nP)"
   by(simp add: Let_def new_configured_SecurityInvariant.simps)


text\<open>We now collect all the core properties of a security invariant, but without the @{typ "'a"} @{typ "'b"} 
      types, so it is instantiated with a concrete configuration.\<close>
locale configured_SecurityInvariant =
  fixes m :: "('v::vertex) SecurityInvariant_configured"
  assumes
    \<comment> \<open>As in SecurityInvariant definition\<close>
    valid_c_offending_flows:
    "c_offending_flows m G = {F. F \<subseteq> (edges G) \<and> \<not> c_sinvar m G \<and> c_sinvar m (delete_edges G F) \<and> 
      (\<forall> (e1, e2) \<in> F. \<not> c_sinvar m (add_edge e1 e2 (delete_edges G F)))}"
  and
    \<comment> \<open>A empty network can have no security violations\<close>
    defined_offending:
    "\<lbrakk> wf_graph \<lparr> nodes = N, edges = {} \<rparr> \<rbrakk> \<Longrightarrow> c_sinvar m \<lparr> nodes = N, edges = {}\<rparr>"
  and
    \<comment> \<open>prohibiting more does not decrease security\<close>
    mono_sinvar:
    "\<lbrakk> wf_graph \<lparr> nodes = N, edges = E \<rparr>; E' \<subseteq> E; c_sinvar m \<lparr> nodes = N, edges = E \<rparr> \<rbrakk> \<Longrightarrow> 
      c_sinvar m \<lparr> nodes = N, edges = E' \<rparr>"
  begin
    (*compatibility with other definitions*)
    lemma sinvar_monoI: 
    "SecurityInvariant_withOffendingFlows.sinvar_mono (\<lambda> (G::('v::vertex) graph) (nP::'v \<Rightarrow> 'a). c_sinvar m G)"
      apply(simp add: SecurityInvariant_withOffendingFlows.sinvar_mono_def, clarify)
      by(fact mono_sinvar)

    text\<open>if the network where nobody communicates with anyone fulfilles its security requirement,
          the offending flows are always defined.\<close>
    lemma defined_offending': 
      "\<lbrakk> wf_graph G; \<not> c_sinvar m G \<rbrakk> \<Longrightarrow> c_offending_flows m G \<noteq> {}"
      proof -
        assume a1: "wf_graph G"
        and    a2: "\<not> c_sinvar m G"
        have subst_set_offending_flows: 
        "\<And>nP. SecurityInvariant_withOffendingFlows.set_offending_flows (\<lambda>G nP. c_sinvar m G) G nP = c_offending_flows m G"
        by(simp add: valid_c_offending_flows fun_eq_iff 
            SecurityInvariant_withOffendingFlows.set_offending_flows_def
            SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
            SecurityInvariant_withOffendingFlows.is_offending_flows_def)

        from a1 have wfG_empty: "wf_graph \<lparr>nodes = nodes G, edges = {}\<rparr>" by(simp add:wf_graph_def)

        from a1 have "\<And>nP. \<not> c_sinvar m G \<Longrightarrow> SecurityInvariant_withOffendingFlows.set_offending_flows (\<lambda>G nP. c_sinvar m G) G nP \<noteq> {}"
          apply(frule_tac finite_distinct_list[OF wf_graph.finiteE])
          apply(erule_tac exE)
          apply(rename_tac list_edges)
          apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_monoI])
          by(auto simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def delete_edges_simp2 defined_offending[OF wfG_empty])
      
          thus ?thesis by(simp add: a2 subst_set_offending_flows)
    qed

    (* The offending flows definitions are equal, compatibility *)
    lemma subst_offending_flows: "\<And> nP. SecurityInvariant_withOffendingFlows.set_offending_flows (\<lambda>G nP. c_sinvar m G) G nP = c_offending_flows m G"
      apply (unfold SecurityInvariant_withOffendingFlows.set_offending_flows_def
            SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
            SecurityInvariant_withOffendingFlows.is_offending_flows_def)
      by(simp add: valid_c_offending_flows)

    text\<open>all the @{term SecurityInvariant_preliminaries} stuff must hold, for an arbitrary @{term nP}\<close>
    lemma SecurityInvariant_preliminariesD:
      "SecurityInvariant_preliminaries (\<lambda> (G::('v::vertex) graph) (nP::'v \<Rightarrow> 'a). c_sinvar m G)"
      proof(unfold_locales, goal_cases)
      case 1 thus ?case using defined_offending' by(simp add: subst_offending_flows)
      next case 2 thus ?case by(fact mono_sinvar)
      next case 3 thus ?case by(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_monoI])
      qed

    lemma negative_mono:
     "\<And> N E' E. wf_graph \<lparr> nodes = N, edges = E \<rparr> \<Longrightarrow> 
        E' \<subseteq> E \<Longrightarrow> \<not> c_sinvar m \<lparr> nodes = N, edges = E' \<rparr> \<Longrightarrow> \<not> c_sinvar m \<lparr> nodes = N, edges = E \<rparr>"
     by(blast dest: mono_sinvar)

    
    subsection\<open>Reusing Lemmata\<close>
      lemmas mono_extend_set_offending_flows =
      SecurityInvariant_preliminaries.mono_extend_set_offending_flows[OF SecurityInvariant_preliminariesD, simplified subst_offending_flows]
      text\<open>@{thm mono_extend_set_offending_flows [no_vars]}\<close>

      lemmas offending_flows_union_mono =
      SecurityInvariant_preliminaries.offending_flows_union_mono[OF SecurityInvariant_preliminariesD, simplified subst_offending_flows]
      text\<open>@{thm offending_flows_union_mono [no_vars]}\<close>

      lemmas sinvar_valid_remove_flattened_offending_flows =
      SecurityInvariant_preliminaries.sinvar_valid_remove_flattened_offending_flows[OF SecurityInvariant_preliminariesD, simplified subst_offending_flows]
      text\<open>@{thm sinvar_valid_remove_flattened_offending_flows [no_vars]}\<close>

      lemmas sinvar_valid_remove_SOME_offending_flows =
      SecurityInvariant_preliminaries.sinvar_valid_remove_SOME_offending_flows[OF SecurityInvariant_preliminariesD, simplified subst_offending_flows]
      text\<open>@{thm sinvar_valid_remove_SOME_offending_flows [no_vars]}\<close>


      lemmas sinvar_valid_remove_minimalize_offending_overapprox =
      SecurityInvariant_preliminaries.sinvar_valid_remove_minimalize_offending_overapprox[OF SecurityInvariant_preliminariesD, simplified subst_offending_flows]
      text\<open>@{thm sinvar_valid_remove_minimalize_offending_overapprox [no_vars]}\<close>
      

      lemmas empty_offending_contra =
      SecurityInvariant_withOffendingFlows.empty_offending_contra[where sinvar="(\<lambda>G nP. c_sinvar m G)", simplified subst_offending_flows]
      text\<open>@{thm empty_offending_contra [no_vars]}\<close>

      lemmas Un_set_offending_flows_bound_minus_subseteq = 
      SecurityInvariant_preliminaries.Un_set_offending_flows_bound_minus_subseteq[OF SecurityInvariant_preliminariesD, simplified subst_offending_flows]
      text\<open>@{thm Un_set_offending_flows_bound_minus_subseteq [no_vars]}\<close>

      lemmas Un_set_offending_flows_bound_minus_subseteq' = 
      SecurityInvariant_preliminaries.Un_set_offending_flows_bound_minus_subseteq'[OF SecurityInvariant_preliminariesD, simplified subst_offending_flows]
      text\<open>@{thm Un_set_offending_flows_bound_minus_subseteq' [no_vars]}\<close>
end

thm configured_SecurityInvariant_def
text\<open>@{thm configured_SecurityInvariant_def [no_vars]}\<close>

thm configured_SecurityInvariant.mono_sinvar
text\<open>@{thm configured_SecurityInvariant.mono_sinvar [no_vars]}\<close>



text\<open>
  Naming convention:
    m :: network security requirement
    M :: network security requirement list
\<close>

  text\<open>The function @{term new_configured_SecurityInvariant} takes some tuple and if it returns a result,
         the locale assumptions are automatically fulfilled.\<close>
  theorem new_configured_SecurityInvariant_sound: 
  "\<lbrakk> new_configured_SecurityInvariant (sinvar, defbot, receiver_violation, nP) = Some m \<rbrakk> \<Longrightarrow>
    configured_SecurityInvariant m"
    proof -
      assume a: "new_configured_SecurityInvariant (sinvar, defbot, receiver_violation, nP) = Some m"
      hence NetModel: "SecurityInvariant sinvar defbot receiver_violation"
        by(simp add: new_configured_SecurityInvariant.simps split: if_split_asm)
      hence NetModel_p: "SecurityInvariant_preliminaries sinvar" by(simp add: SecurityInvariant_def)

      from a have c_eval: "c_sinvar m = (\<lambda>G. sinvar G nP)"
         and c_offending: "c_offending_flows m = (\<lambda>G. SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G nP)"
         and "c_isIFS m = receiver_violation"
        by(auto simp add: new_configured_SecurityInvariant.simps NetModel split: if_split_asm)

      have monoI: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
        apply(simp add: SecurityInvariant_withOffendingFlows.sinvar_mono_def, clarify)
        by(fact SecurityInvariant_preliminaries.mono_sinvar[OF NetModel_p])
      from SecurityInvariant_withOffendingFlows.valid_empty_edges_iff_exists_offending_flows[OF monoI, symmetric]
            SecurityInvariant_preliminaries.defined_offending[OF NetModel_p]
      have eval_empty_graph: "\<And> N nP. wf_graph \<lparr>nodes = N, edges = {}\<rparr> \<Longrightarrow> sinvar \<lparr>nodes = N, edges = {}\<rparr> nP"
      by fastforce

       show ?thesis
        apply(unfold_locales)
          apply(simp add: c_eval c_offending SecurityInvariant_withOffendingFlows.set_offending_flows_def SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def SecurityInvariant_withOffendingFlows.is_offending_flows_def)
         apply(simp add: c_eval eval_empty_graph)
        apply(simp add: c_eval,drule(3) SecurityInvariant_preliminaries.mono_sinvar[OF NetModel_p])
        done
   qed

text\<open>All security invariants are valid according to the definition\<close>
definition valid_reqs :: "('v::vertex) SecurityInvariant_configured list \<Rightarrow> bool" where
  "valid_reqs M \<equiv> \<forall> m \<in> set M. configured_SecurityInvariant m"

 subsection \<open>Algorithms\<close>
    text\<open>A (generic) security invariant corresponds to a type of security requirements (type: @{typ "'v graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool"}).
          A configured security invariant is a security requirement in a scenario specific setting (type: @{typ "'v graph \<Rightarrow> bool"}).
          I.e., it is a security requirement as listed in the requirements document.
          All security requirements are fulfilled for a fixed policy @{term G} if all security requirements are fulfilled for @{term G}.\<close>


    text\<open>Get all possible offending flows from all security requirements\<close>
    definition get_offending_flows :: "'v SecurityInvariant_configured list \<Rightarrow> 'v graph \<Rightarrow> (('v \<times> 'v) set set)" where
      "get_offending_flows M G = (\<Union>m\<in>set M. c_offending_flows m G)"  

    (*Note: only checks sinvar, not eval!! No 'a 'b type variables here*)
    definition all_security_requirements_fulfilled :: "('v::vertex) SecurityInvariant_configured list \<Rightarrow> 'v graph \<Rightarrow> bool" where
      "all_security_requirements_fulfilled M G \<equiv> \<forall>m \<in> set M. (c_sinvar m) G"
    
    text\<open>Generate a valid topology from the security requirements\<close>
    (*constant G, remove after algorithm*)
    fun generate_valid_topology :: "'v SecurityInvariant_configured list \<Rightarrow> 'v graph \<Rightarrow> 'v graph" where
      "generate_valid_topology [] G = G" |
      "generate_valid_topology (m#Ms) G = delete_edges (generate_valid_topology Ms G) (\<Union> (c_offending_flows m G))"

     \<comment> \<open>return all Access Control Strategy models from a list of models\<close>
    definition get_ACS :: "('v::vertex) SecurityInvariant_configured list \<Rightarrow> 'v SecurityInvariant_configured list" where
      "get_ACS M \<equiv> [m \<leftarrow> M. \<not> c_isIFS m]"
     \<comment> \<open>return all Information Flows Strategy models from a list of models\<close>
    definition get_IFS :: "('v::vertex) SecurityInvariant_configured list \<Rightarrow> 'v SecurityInvariant_configured list" where
      "get_IFS M \<equiv> [m \<leftarrow> M. c_isIFS m]"
    lemma get_ACS_union_get_IFS: "set (get_ACS M) \<union> set (get_IFS M) = set M"
      by(auto simp add: get_ACS_def get_IFS_def)
  

   subsection\<open>Lemmata\<close>
    lemma valid_reqs1: "valid_reqs (m # M) \<Longrightarrow> configured_SecurityInvariant m"
      by(simp add: valid_reqs_def)
    lemma valid_reqs2: "valid_reqs (m # M) \<Longrightarrow> valid_reqs M"
      by(simp add: valid_reqs_def)
    lemma get_offending_flows_alt1: "get_offending_flows M G = \<Union> {c_offending_flows m G | m. m \<in> set M}"
      apply(simp add: get_offending_flows_def)
      by fastforce
    lemma get_offending_flows_un: "\<Union>(get_offending_flows M G) = (\<Union>m\<in>set M. \<Union>(c_offending_flows m G))"
      apply(simp add: get_offending_flows_def)
      by blast
  
  
    lemma all_security_requirements_fulfilled_mono:
      "\<lbrakk> valid_reqs M; E' \<subseteq> E; wf_graph \<lparr> nodes = V, edges = E \<rparr> \<rbrakk> \<Longrightarrow>  
        all_security_requirements_fulfilled M \<lparr> nodes = V, edges = E \<rparr> \<Longrightarrow>
        all_security_requirements_fulfilled M \<lparr> nodes = V, edges = E' \<rparr>"
        apply(induction M arbitrary: E' E)
         apply(simp_all add: all_security_requirements_fulfilled_def)
        apply(rename_tac m M E' E)
        apply(rule conjI)
         apply(erule(2) configured_SecurityInvariant.mono_sinvar[OF valid_reqs1])
         apply(simp_all)
        apply(drule valid_reqs2)
        apply blast
        done

    subsection\<open>generate valid topology\<close>
    (*
      lemma generate_valid_topology_def_delete_multiple: 
        "generate_valid_topology M G = delete_edges (generate_valid_topology M G) (\<Union> (get_offending_flows M G))"
        proof(induction M arbitrary: G)
          case Nil
            thus ?case by(simp add: get_offending_flows_def)
          next
          case (Cons m M)
            from Cons[simplified delete_edges_simp2 get_offending_flows_def] 
            have "edges (generate_valid_topology M G) = edges (generate_valid_topology M G) - \<Union>(\<Union>m\<in>set M. c_offending_flows m G)"
              by (metis graph.select_convs(2))
            thus ?case
              apply(simp add: get_offending_flows_def delete_edges_simp2)
              by blast
        qed*)
      lemma generate_valid_topology_nodes:
      "nodes (generate_valid_topology M G) = (nodes G)"
        apply(induction M arbitrary: G)
         by(simp_all add: graph_ops)

      lemma generate_valid_topology_def_alt:
        "generate_valid_topology M G = delete_edges G (\<Union> (get_offending_flows M G))"
        proof(induction M arbitrary: G)
          case Nil
            thus ?case by(simp add: get_offending_flows_def)
          next
          case (Cons m M)
            from Cons[simplified delete_edges_simp2 get_offending_flows_def] 
            have "edges (generate_valid_topology M G) = edges G - \<Union>(\<Union>m\<in>set M. c_offending_flows m G)"
              by (metis graph.select_convs(2))
            thus ?case
              apply(simp add: get_offending_flows_def delete_edges_simp2)
              apply(rule)
               apply(simp add: generate_valid_topology_nodes)
              by blast
        qed
    
      lemma wf_graph_generate_valid_topology: "wf_graph G \<Longrightarrow> wf_graph (generate_valid_topology M G)"
        proof(induction M arbitrary: G)
        qed(simp_all)
  
     lemma generate_valid_topology_mono_models:
      "edges (generate_valid_topology (m#M) \<lparr> nodes = V, edges = E \<rparr>) \<subseteq> edges (generate_valid_topology M \<lparr> nodes = V, edges = E \<rparr>)"
        proof(induction M arbitrary: E m)
        case Nil thus ?case by(simp add: delete_edges_simp2)
        case Cons thus ?case by(simp add: delete_edges_simp2)
      qed
     
      lemma generate_valid_topology_subseteq_edges:
      "edges (generate_valid_topology M G) \<subseteq> (edges G)"
        proof(induction M arbitrary: G)
        case Cons thus ?case by (simp add: delete_edges_simp2) blast
        qed(simp)

      text\<open>@{term generate_valid_topology} generates a valid topology (Policy)!\<close>
      theorem generate_valid_topology_sound:
      "\<lbrakk> valid_reqs M; wf_graph \<lparr>nodes = V, edges = E\<rparr> \<rbrakk> \<Longrightarrow> 
      all_security_requirements_fulfilled M (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)"
        proof(induction M arbitrary: V E)
          case Nil
          thus ?case by(simp add: all_security_requirements_fulfilled_def)
        next
          case (Cons m M)
          from valid_reqs1[OF Cons(2)] have validReq: "configured_SecurityInvariant m" .

          from Cons(3) have valid_rmUnOff: "wf_graph \<lparr>nodes = V, edges = E - \<Union>(c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>) \<rparr>"
            by(simp add: wf_graph_remove_edges)
          
          from configured_SecurityInvariant.sinvar_valid_remove_flattened_offending_flows[OF validReq Cons(3)]
          have valid_eval_rmUnOff: "c_sinvar m \<lparr>nodes = V, edges = E - \<Union>(c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>) \<rparr>" .
    
          from generate_valid_topology_subseteq_edges have edges_gentopo_subseteq: 
            "edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) - \<Union>(c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)
               \<subseteq>
            E - \<Union>(c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)"  by fastforce
    
          from configured_SecurityInvariant.mono_sinvar[OF validReq valid_rmUnOff edges_gentopo_subseteq valid_eval_rmUnOff]
          have "c_sinvar m \<lparr>nodes = V, edges = (edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)) - \<Union>(c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>) \<rparr>" .
          from this have goal1: 
            "c_sinvar m (delete_edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) (\<Union>(c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)))"
               by(simp add: delete_edges_simp2 generate_valid_topology_nodes)
    
          from valid_reqs2[OF Cons(2)] have "valid_reqs M" .
          from Cons.IH[OF \<open>valid_reqs M\<close> Cons(3)] have IH:
            "all_security_requirements_fulfilled M (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)" .

          have generate_valid_topology_EX_graph_record:
            "\<exists> hypE. (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) = \<lparr>nodes = V, edges = hypE\<rparr> "
              apply(induction M arbitrary: V E)
               by(simp_all add: delete_edges_simp2 generate_valid_topology_nodes)
              
          from generate_valid_topology_EX_graph_record obtain E_IH where  E_IH_prop:
            "(generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) = \<lparr>nodes = V, edges = E_IH\<rparr>" by blast
    
          from wf_graph_generate_valid_topology[OF Cons(3)] E_IH_prop
          have valid_G_E_IH: "wf_graph \<lparr>nodes = V, edges = E_IH\<rparr>" by metis
    
          \<comment> \<open>@{thm IH[simplified E_IH_prop]}\<close>
          \<comment> \<open>@{thm all_security_requirements_fulfilled_mono[OF `valid_reqs M` _  valid_G_E_IH IH[simplified E_IH_prop]]}\<close>
    
          from all_security_requirements_fulfilled_mono[OF \<open>valid_reqs M\<close> _  valid_G_E_IH IH[simplified E_IH_prop]] have mono_rule:
            "\<And> E'. E' \<subseteq> E_IH \<Longrightarrow> all_security_requirements_fulfilled M \<lparr>nodes = V, edges = E'\<rparr>" .
    
          have "all_security_requirements_fulfilled M 
            (delete_edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) (\<Union>(c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)))"
            apply(subst E_IH_prop)
            apply(simp add: delete_edges_simp2)
            apply(rule mono_rule)
            by fast
    
          from this have goal2:
            "(\<forall>ma\<in>set M.
            c_sinvar ma (delete_edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) (\<Union>(c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>))))"
            by(simp add: all_security_requirements_fulfilled_def)
    
          from goal1 goal2 
          show  "all_security_requirements_fulfilled (m # M) (generate_valid_topology (m # M) \<lparr>nodes = V, edges = E\<rparr>)" 
          by (simp add: all_security_requirements_fulfilled_def)
       qed


  lemma generate_valid_topology_as_set: 
  "generate_valid_topology M G = delete_edges G (\<Union>m \<in> set M. (\<Union> (c_offending_flows m G)))"
   apply(induction M arbitrary: G)
    apply(simp_all add: delete_edges_simp2 generate_valid_topology_nodes) by fastforce

  lemma c_offending_flows_subseteq_edges: "configured_SecurityInvariant m \<Longrightarrow> \<Union>(c_offending_flows m G) \<subseteq> edges G"
    apply(clarify)
    apply(simp only: configured_SecurityInvariant.valid_c_offending_flows)
    apply(thin_tac "configured_SecurityInvariant x" for x)
    by auto


  text\<open>Does it also generate a maximum topology? It does, if the security invariants are in ENF-form. That means, if 
        all security invariants can be expressed as a predicate over the edges, 
        @{term "\<exists>P. \<forall>G. c_sinvar m G = (\<forall>(v1,v2) \<in> edges G. P (v1,v2))"}\<close>
  definition max_topo :: "('v::vertex) SecurityInvariant_configured list \<Rightarrow> 'v graph \<Rightarrow> bool" where
    "max_topo M G \<equiv> all_security_requirements_fulfilled M G \<and> (
      \<forall> (v1, v2) \<in> (nodes G \<times> nodes G) - (edges G). \<not> all_security_requirements_fulfilled M (add_edge v1 v2 G))"

  lemma unique_offending_obtain: 
    assumes m: "configured_SecurityInvariant m" and unique: "c_offending_flows m G = {F}"
    obtains P where "F = {(v1, v2) \<in> edges G. \<not> P (v1, v2)}" and "c_sinvar m G = (\<forall>(v1,v2) \<in> edges G. P (v1, v2))" and 
                    "(\<forall>(v1,v2) \<in> edges G - F. P (v1, v2))"
    proof -
    assume EX: "(\<And>P. F = {(v1, v2). (v1, v2) \<in> edges G \<and> \<not> P (v1, v2)} \<Longrightarrow> c_sinvar m G = (\<forall>(v1, v2)\<in>edges G. P (v1, v2)) \<Longrightarrow> \<forall>(v1, v2)\<in>edges G - F. P (v1, v2) \<Longrightarrow> thesis)"

    from unique c_offending_flows_subseteq_edges[OF m] have "F \<subseteq> edges G" by force
    from this obtain P where "F = {e \<in> edges G. \<not> P e}" by (metis double_diff set_diff_eq subset_refl)
    hence 1: "F = {(v1, v2) \<in> edges G. \<not> P (v1, v2)}" by auto

    from configured_SecurityInvariant.valid_c_offending_flows[OF m] have "c_offending_flows m G =
          {F. F \<subseteq> edges G \<and> \<not> c_sinvar m G \<and> c_sinvar m (delete_edges G F) \<and> 
              (\<forall>(e1, e2)\<in>F. \<not> c_sinvar m (add_edge e1 e2 (delete_edges G F)))}" .

    from this unique have "\<not> c_sinvar m G" and 2: "c_sinvar m (delete_edges G F)" and 
                          3: "(\<forall>(e1, e2)\<in>F. \<not> c_sinvar m (add_edge e1 e2 (delete_edges G F)))" by auto

    from this \<open>F = {e \<in> edges G. \<not> P e}\<close> have x3: "\<forall> e \<in> edges G - F. P e" by (metis (lifting) mem_Collect_eq set_diff_eq)
    hence 4: "\<forall>(v1,v2) \<in> edges G - F. P (v1, v2)" by blast

    have "F \<noteq> {}" by (metis assms(1) assms(2) configured_SecurityInvariant.empty_offending_contra insertCI)
    from this \<open>F = {e \<in> edges G. \<not> P e}\<close> \<open>\<not> c_sinvar m G\<close> have 5: "c_sinvar m G = (\<forall>(v1,v2) \<in> edges G. P (v1, v2))"
      apply(simp add: graph_ops)
      by(blast)

    from EX[of P] unique 1 x3 5 show ?thesis by fast
  qed

  lemma enf_offending_flows:
    assumes vm: "configured_SecurityInvariant m" and enf: "\<forall>G. c_sinvar m G = (\<forall>e \<in> edges G. P e)"
    shows "\<forall>G. c_offending_flows m G = (if c_sinvar m G then {} else {{e \<in> edges G. \<not> P e}})"
    proof -
      { fix G
        from vm configured_SecurityInvariant.valid_c_offending_flows have offending_formaldef:
          "c_offending_flows m G =
            {F. F \<subseteq> edges G \<and> \<not> c_sinvar m G \<and> c_sinvar m (delete_edges G F) \<and>
                (\<forall>(e1, e2)\<in>F. \<not> c_sinvar m (add_edge e1 e2 (delete_edges G F)))}" by auto
        have "c_offending_flows m G = (if c_sinvar m G then {} else {{e \<in> edges G. \<not> P e}})"
          proof(cases "c_sinvar m G")
          case True thus ?thesis \<comment> \<open>@{term "{}"}\<close>
            by(simp add: offending_formaldef)
          next
          case False thus ?thesis by(auto simp add: offending_formaldef graph_ops enf)
        qed
      } thus ?thesis by simp
    qed
      
      
lemma enf_not_fulfilled_if_in_offending:
  assumes validRs: "valid_reqs M"
    and   wfG:     "wf_graph G"
    and   enf:     "\<forall>m \<in> set M. \<exists>P. \<forall>G. c_sinvar m G = (\<forall>e \<in> edges G. P e)"
    shows "\<forall>x \<in> (\<Union>m\<in>set M. \<Union>(c_offending_flows m (fully_connected G))).
                \<not> all_security_requirements_fulfilled M \<lparr> nodes = V, edges = insert x E\<rparr>"
   unfolding all_security_requirements_fulfilled_def
   proof(simp, clarify, rename_tac m F a b)
     let ?G="(fully_connected G)"
     fix m F v1 v2
     assume "m \<in> set M" and "F \<in> c_offending_flows m ?G" and "(v1, v2) \<in> F"
       
    from validRs have valid_mD:"\<And>m. m \<in> set M \<Longrightarrow> configured_SecurityInvariant m " 
      by(simp add: valid_reqs_def)
    
     from \<open>m \<in> set M\<close> valid_mD have "configured_SecurityInvariant m" by simp

     from enf \<open>m \<in> set M\<close> obtain P where enf_m: "\<forall>G. c_sinvar m G = (\<forall>e\<in>edges G. P e)" by blast
     
     from \<open>(v1, v2) \<in> F\<close> have "F \<noteq> {}" by auto

     from enf_offending_flows[OF \<open>configured_SecurityInvariant m\<close> \<open>\<forall>G. c_sinvar m G = (\<forall>e\<in>edges G. P e)\<close>] have
      offending: "\<And>G. c_offending_flows m G = (if c_sinvar m G then {} else {{e \<in> edges G. \<not> P e}})" by simp
     from \<open>F \<in> c_offending_flows m ?G\<close> \<open>F \<noteq> {}\<close> have "F = {e \<in> edges ?G. \<not> P e}"
       by(simp split: if_split_asm add: offending)
     from this \<open>(v1, v2) \<in> F\<close>  have "\<not> P (v1, v2)" by simp

     from this enf_m have "\<not> c_sinvar m \<lparr>nodes = V, edges = insert (v1, v2) E\<rparr>" by(simp)
     thus "\<exists>m\<in>set M. \<not> c_sinvar m \<lparr>nodes = V, edges = insert (v1, v2) E\<rparr>" using \<open>m \<in> set M\<close>
      apply(rule_tac x="m" in bexI)
       by simp_all
qed
        

 theorem generate_valid_topology_max_topo: "\<lbrakk> valid_reqs M; wf_graph G;
      \<forall>m \<in> set M. \<exists>P. \<forall>G. c_sinvar m G = (\<forall>e \<in> edges G. P e)\<rbrakk> \<Longrightarrow> 
      max_topo M (generate_valid_topology M (fully_connected G))"
  proof -
    let ?G="(fully_connected G)"
    assume validRs: "valid_reqs M"
    and    wfG:       "wf_graph G"
    and enf: "\<forall>m \<in> set M. \<exists>P. \<forall>G. c_sinvar m G = (\<forall>e \<in> edges G. P e)"

    obtain V E where VE_prop: "\<lparr> nodes = V, edges = E \<rparr> = generate_valid_topology M ?G" by (metis graph.cases)
    hence VE_prop_asset:
      "\<lparr> nodes = V, edges = E \<rparr> = \<lparr> nodes = V, edges = V \<times> V - (\<Union>m\<in>set M. \<Union>(c_offending_flows m ?G))\<rparr>"
      by(simp add: fully_connected_def generate_valid_topology_as_set delete_edges_simp2)

    from VE_prop_asset have E_prop: "E =  V \<times> V - (\<Union>m\<in>set M. \<Union>(c_offending_flows m ?G))" by fast
    from VE_prop have V_prop: "nodes G = V"
      by (simp add: fully_connected_def delete_edges_simp2 generate_valid_topology_def_alt)
    from VE_prop have V_full_prop: "nodes (generate_valid_topology M ?G) = V" by (metis graph.select_convs(1))
    from VE_prop have E_full_prop: "edges (generate_valid_topology M ?G) = E" by (metis graph.select_convs(2))

    from VE_prop wf_graph_generate_valid_topology[OF fully_connected_wf[OF wfG]]
    have wfG_VE: "wf_graph \<lparr> nodes = V, edges = E \<rparr>" by force

    from generate_valid_topology_sound[OF validRs wfG_VE] fully_connected_wf[OF wfG] have VE_all_valid: 
      "all_security_requirements_fulfilled M \<lparr> nodes = V, edges = V \<times> V - (\<Union>m\<in>set M. \<Union>(c_offending_flows m ?G))\<rparr>"
      by (metis VE_prop VE_prop_asset fully_connected_def generate_valid_topology_sound validRs)
    hence goal1: "all_security_requirements_fulfilled M (generate_valid_topology M (fully_connected G))" by (metis VE_prop VE_prop_asset)

    from validRs have valid_mD:"\<And>m. m \<in> set M \<Longrightarrow> configured_SecurityInvariant m " 
      by(simp add: valid_reqs_def)

    from c_offending_flows_subseteq_edges[where G="?G"] validRs have hlp1: "(\<Union>m\<in>set M. \<Union>(c_offending_flows m ?G)) \<subseteq> V \<times> V"
      apply(simp add: fully_connected_def V_prop)
      using valid_reqs_def by blast
    have "\<And>A B. A - (A - B) = B \<inter> A" by fast 
    from E_prop hlp1 have "V \<times> V - E = (\<Union>m\<in>set M. \<Union>(c_offending_flows m ?G))" by force


    from enf_not_fulfilled_if_in_offending[OF validRs wfG enf]
    have "\<forall>(v1, v2) \<in> (\<Union>m\<in>set M. \<Union>(c_offending_flows m ?G)).
       \<not> all_security_requirements_fulfilled M \<lparr> nodes = V, edges = E \<union> {(v1, v2)}\<rparr>" by simp
          
    from this \<open>V \<times> V - E = (\<Union>m\<in>set M. \<Union>(c_offending_flows m ?G))\<close> have "\<forall>(v1, v2) \<in> V \<times> V - E.
         \<not> all_security_requirements_fulfilled M \<lparr> nodes = V, edges = E \<union> {(v1, v2)}\<rparr>" by simp
    hence goal2: "(\<forall>(v1, v2)\<in>nodes (generate_valid_topology M ?G) \<times> nodes (generate_valid_topology M ?G) -
                edges (generate_valid_topology M ?G).
        \<not> all_security_requirements_fulfilled M (add_edge v1 v2 (generate_valid_topology M ?G)))"
    proof(unfold V_full_prop E_full_prop graph_ops)
      assume a: "\<forall>(v1, v2)\<in>V \<times> V - E. \<not> all_security_requirements_fulfilled M \<lparr>nodes = V, edges = E \<union> {(v1, v2)}\<rparr>"
      have "\<forall>(v1, v2)\<in>V \<times> V - E.  V \<union> {v1, v2} = V" by blast
      hence "\<forall>(v1, v2)\<in>V \<times> V - E. \<lparr>nodes = V \<union> {v1, v2}, edges = {(v1, v2)} \<union> E\<rparr> = \<lparr>nodes = V, edges = E \<union> {(v1, v2)}\<rparr>" by blast
      from this a show "\<forall>(v1, v2)\<in>V \<times> V - E. \<not> all_security_requirements_fulfilled M \<lparr>nodes = V \<union> {v1, v2}, edges = {(v1, v2)} \<union> E\<rparr>"
        \<comment> \<open>TODO: this should be trivial ...\<close>
        apply(simp)
        apply(rule ballI)
        apply(erule_tac x=x and A="V \<times> V - E" in ballE)
         prefer 2 apply(simp; fail)
        apply(erule_tac x=x and A="V \<times> V - E" in ballE)
         prefer 2 apply(simp; fail)
        apply(clarify)
        by presburger
    qed
     
    from goal1 goal2 show ?thesis
      unfolding max_topo_def by presburger
  qed

  lemma enf_all_valid_policy_subset_of_max:
    assumes validRs: "valid_reqs M"
    and     wfG:     "wf_graph G"
    and     enf:     "\<forall>m \<in> set M. \<exists>P. \<forall>G. c_sinvar m G = (\<forall>e \<in> edges G. P e)"
    and     nodesG': "nodes G = nodes G'"
    shows "\<lbrakk> wf_graph G';
        all_security_requirements_fulfilled M G'\<rbrakk> \<Longrightarrow> 
        edges G' \<subseteq> edges (generate_valid_topology M (fully_connected G))"
    using nodesG' apply(cases "generate_valid_topology M (fully_connected G)", rename_tac V E, simp)
    apply(cases "G'", rename_tac V' E', simp)
    apply(subgoal_tac "nodes G = V")
     prefer 2
     apply (metis fully_connected_def generate_valid_topology_nodes graph.select_convs(1))
    apply(simp)
  proof(rule ccontr)
    fix V E V' E'
    assume a5: "all_security_requirements_fulfilled M \<lparr>nodes = V, edges = E'\<rparr>" and
           a6: "generate_valid_topology M (fully_connected G) = \<lparr>nodes = V, edges = E\<rparr>" and
           a10: "wf_graph \<lparr>nodes = V, edges = E'\<rparr>" and
           contr: "\<not> E' \<subseteq> E"
    
    from wfG a6 have "wf_graph \<lparr>nodes = V, edges = E\<rparr>"
      by (metis fully_connected_wf wf_graph_generate_valid_topology)
    with a10 have EE'subsets: "fst ` E \<subseteq> V \<and> snd ` E \<subseteq> V \<and> fst ` E' \<subseteq> V \<and> snd ` E' \<subseteq> V"
      by(simp add: wf_graph_def)
    hence EE'subsets': "E \<subseteq> V \<times> V \<and> E' \<subseteq> V \<times> V" by auto
    
    from generate_valid_topology_max_topo[OF validRs wfG enf]
      have m1: "all_security_requirements_fulfilled M \<lparr>nodes = V, edges = E\<rparr>" and
           m2: "(\<forall>x\<in>V \<times> V - E. case x of (v1, v2) \<Rightarrow> \<not> all_security_requirements_fulfilled M (add_edge v1 v2 \<lparr>nodes = V, edges = E\<rparr>))"
      by(simp add: max_topo_def a6)+
        
    from m2 have m2': "\<forall>x\<in>V \<times> V - E. \<not> all_security_requirements_fulfilled M \<lparr>nodes = V, edges = insert x E\<rparr>"
      apply(simp add: add_edge_def)
      apply(rule ballI, rename_tac x)
      apply(erule_tac x=x in ballE, simp_all)
      apply(case_tac x, simp)
      by (simp add: insert_absorb)
    
     show False
       proof(cases "V = {}")
         case True
         with EE'subsets a10 have "E = {}" and "E' = {}"
           by(simp add: wf_graph_def)+
         with True contr show ?thesis by simp
       next
         case False
         with EE'subsets' contr obtain x where x: "x \<in> E' \<and> x \<notin> E \<and> x \<in> V \<times> V"
           by blast
         from m2' x have "\<not> all_security_requirements_fulfilled M \<lparr>nodes = V, edges = insert x E\<rparr>"
           by (simp)
         
         from a6 x have x_offedning: "x \<in> (\<Union>m\<in>set M. \<Union>(c_offending_flows m (fully_connected G)))"
           apply(simp add: generate_valid_topology_as_set delete_edges_simp2 fully_connected_def)
           by blast
  
         from enf_not_fulfilled_if_in_offending[OF validRs wfG enf] x_offedning have
           1: "\<not> all_security_requirements_fulfilled M \<lparr>nodes = V, edges = insert x myE\<rparr>" for myE by blast
         
         from x have insertxE': "insert x E' = E'" by blast
         with a5 have
           "all_security_requirements_fulfilled M \<lparr>nodes = V, edges = insert x E'\<rparr>" by simp
         with insertxE' all_security_requirements_fulfilled_mono[OF validRs _ a10 a5] have 
           2: "all_security_requirements_fulfilled M \<lparr>nodes = V, edges = insert x {}\<rparr>" by blast
         from 1 2 show ?thesis by blast
       qed
  qed
    


   subsection\<open>More Lemmata\<close>
     lemma (in configured_SecurityInvariant) c_sinvar_valid_imp_no_offending_flows: 
      "c_sinvar m G \<Longrightarrow> c_offending_flows m G = {}"
        by(simp add: valid_c_offending_flows)

     lemma all_security_requirements_fulfilled_imp_no_offending_flows:
        "valid_reqs M \<Longrightarrow> all_security_requirements_fulfilled M G \<Longrightarrow> (\<Union>m\<in>set M. \<Union>(c_offending_flows m G)) = {}"
        proof(induction M)
        case Cons thus ?case
          unfolding all_security_requirements_fulfilled_def
          apply(simp)
          by(blast dest: valid_reqs2 valid_reqs1 configured_SecurityInvariant.c_sinvar_valid_imp_no_offending_flows)
        qed(simp)

    corollary all_security_requirements_fulfilled_imp_get_offending_empty:
      "valid_reqs M \<Longrightarrow> all_security_requirements_fulfilled M G \<Longrightarrow> get_offending_flows M G = {}"
      apply(frule(1) all_security_requirements_fulfilled_imp_no_offending_flows)
      apply(simp add: get_offending_flows_def)
      apply(thin_tac "all_security_requirements_fulfilled M G")
      apply(simp add: valid_reqs_def)
      apply(clarify)
      using configured_SecurityInvariant.empty_offending_contra by fastforce
  
    corollary generate_valid_topology_does_nothing_if_valid:
      "\<lbrakk> valid_reqs M; all_security_requirements_fulfilled M G\<rbrakk> \<Longrightarrow> 
          generate_valid_topology M G = G"
      by(simp add: generate_valid_topology_as_set graph_ops all_security_requirements_fulfilled_imp_no_offending_flows)


    lemma mono_extend_get_offending_flows: "\<lbrakk> valid_reqs M;
         wf_graph \<lparr>nodes = V, edges = E\<rparr>;
         E' \<subseteq> E;
         F' \<in> get_offending_flows M \<lparr>nodes = V, edges = E'\<rparr> \<rbrakk> \<Longrightarrow>
       \<exists>F\<in>get_offending_flows M \<lparr>nodes = V, edges = E\<rparr>. F' \<subseteq> F"
     proof(induction M)
     case Nil thus ?case by(simp add: get_offending_flows_def)
     next
     case (Cons m M)
      from Cons.prems have "configured_SecurityInvariant m"
                       and "valid_reqs M" using valid_reqs2 valid_reqs1 by blast+
      from Cons.prems(4) have
        "F' \<in> c_offending_flows m \<lparr>nodes = V, edges = E'\<rparr> \<or>
         (F' \<in> get_offending_flows M \<lparr>nodes = V, edges = E'\<rparr>)"
       by(simp add: get_offending_flows_def)
      from this show ?case
       proof(elim disjE, goal_cases)
       case 1
         with \<open>configured_SecurityInvariant m\<close> Cons.prems(2,3,4) obtain F where
           "F\<in>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>" and "F' \<subseteq> F"
           by(blast dest: configured_SecurityInvariant.mono_extend_set_offending_flows)
         hence "F\<in>get_offending_flows (m # M) \<lparr>nodes = V, edges = E\<rparr>"
           by (simp add: get_offending_flows_def)
         with \<open>F' \<subseteq> F\<close> show ?case by blast
       next
       case 2 with Cons \<open>valid_reqs M\<close> show ?case by(simp add: get_offending_flows_def) blast
       qed
     qed

     lemma get_offending_flows_subseteq_edges: "valid_reqs M \<Longrightarrow> F \<in> get_offending_flows M \<lparr>nodes = V, edges = E\<rparr> \<Longrightarrow> F \<subseteq> E"
      apply(induction M)
       apply(simp add: get_offending_flows_def)
      apply(simp add: get_offending_flows_def)
      apply(frule valid_reqs2, drule valid_reqs1)
      apply(simp add: configured_SecurityInvariant.valid_c_offending_flows)
      by blast

    thm configured_SecurityInvariant.offending_flows_union_mono
    lemma get_offending_flows_union_mono: "\<lbrakk>valid_reqs M; 
      wf_graph \<lparr>nodes = V, edges = E\<rparr>; E' \<subseteq> E \<rbrakk> \<Longrightarrow>
      \<Union>(get_offending_flows M \<lparr>nodes = V, edges = E'\<rparr>) \<subseteq> \<Union>(get_offending_flows M \<lparr>nodes = V, edges = E\<rparr>)"
      apply(induction M)
       apply(simp add: get_offending_flows_def)
      apply(frule valid_reqs2, drule valid_reqs1)
      apply(drule(2) configured_SecurityInvariant.offending_flows_union_mono)
      apply(simp add: get_offending_flows_def)
      by auto

    thm configured_SecurityInvariant.Un_set_offending_flows_bound_minus_subseteq'
    lemma Un_set_offending_flows_bound_minus_subseteq':"\<lbrakk>valid_reqs M; 
      wf_graph \<lparr>nodes = V, edges = E\<rparr>; E' \<subseteq> E;
      \<Union>(get_offending_flows M \<lparr>nodes = V, edges = E\<rparr>) \<subseteq> X \<rbrakk> \<Longrightarrow> \<Union>(get_offending_flows M \<lparr>nodes = V, edges = E - E'\<rparr>) \<subseteq> X - E'"
      proof(induction M)
      case Nil thus ?case by (simp add: get_offending_flows_def)
      next
      case (Cons m M)
        from Cons.prems(1) valid_reqs2 have "valid_reqs M" by force
        from Cons.prems(1) valid_reqs1 have "configured_SecurityInvariant m" by force
        from Cons.prems(4) have "\<Union>(get_offending_flows M \<lparr>nodes = V, edges = E\<rparr>) \<subseteq> X" by(simp add: get_offending_flows_def)
        from Cons.IH[OF \<open>valid_reqs M\<close> Cons.prems(2) Cons.prems(3) \<open>\<Union>(get_offending_flows M \<lparr>nodes = V, edges = E\<rparr>) \<subseteq> X\<close>] have IH: "\<Union>(get_offending_flows M \<lparr>nodes = V, edges = E - E'\<rparr>) \<subseteq> X - E'" .
        from Cons.prems(4) have "\<Union>(c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>) \<subseteq> X" by(simp add: get_offending_flows_def)
        from configured_SecurityInvariant.Un_set_offending_flows_bound_minus_subseteq'[OF \<open>configured_SecurityInvariant m\<close> Cons.prems(2) \<open>\<Union>(c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>) \<subseteq> X\<close>] have "\<Union>(c_offending_flows m \<lparr>nodes = V, edges = E - E'\<rparr>) \<subseteq> X - E'" .
        from this IH show ?case by(simp add: get_offending_flows_def)
      qed

 


 (*ENF has uniquely defined offending flows*)
 lemma ENF_uniquely_defined_offedning: "valid_reqs M \<Longrightarrow> wf_graph G \<Longrightarrow> 
      \<forall>m \<in> set M. \<exists>P. \<forall>G. c_sinvar m G = (\<forall>e \<in> edges G. P e) \<Longrightarrow> 
      \<forall>m \<in> set M. \<forall>G. \<not> c_sinvar m G \<longrightarrow>  (\<exists>OFF. c_offending_flows m G = {OFF})"
 apply -
 apply(induction M)
  apply(simp; fail)
 apply(rename_tac m M)
 apply(frule valid_reqs1)
 apply(drule valid_reqs2)
 apply(simp)
 apply(elim conjE)
 apply(erule_tac x=m in ballE)
  apply(simp_all; fail)
 apply(erule exE, rename_tac P)
 apply(drule_tac P=P in enf_offending_flows)
  apply(simp; fail)
 apply(simp; fail)
 done

 lemma assumes "configured_SecurityInvariant m"
       and "\<forall>G. \<not> c_sinvar m G \<longrightarrow> (\<exists>OFF. c_offending_flows m G = {OFF})"
       shows "\<exists>OFF_P. \<forall>G. c_offending_flows m G = (if c_sinvar m G then {} else {OFF_P G})"
 proof -
   from assms have "\<exists>OFF_P. 
          c_offending_flows m G = (if c_sinvar m G then {} else {OFF_P G})" for G
     apply(erule_tac x=G in allE)
     apply(cases "c_sinvar m G")
      apply(drule configured_SecurityInvariant.c_sinvar_valid_imp_no_offending_flows, simp)
      apply(simp; fail)
     apply(simp)
     by meson
   with assms show ?thesis by metis
 qed
 (*TODO: generate_valid_topology_max_topo for sinvars with unique offending flows in general*)



   text\<open>Hilber's eps operator example\<close>
   lemma "(SOME x. x : {1::nat, 2, 3}) = x \<Longrightarrow> x = 1 \<or> x = 2 \<or> x = 3"
     proof -
      have "(SOME x. x \<in> {1::nat, 2, 3}) \<in> {1::nat, 2, 3}" unfolding some_in_eq by simp
      thus "(SOME x. x : {1::nat, 2, 3}) = x \<Longrightarrow> x = 1 \<or> x = 2 \<or> x = 3" by fast
     qed

  (*TODO: remove the offending flows from the graph for each iteration. requires proof arbitrary: G
          allows to put expensive invariants at back of list and hope that sinvar is true until the are evaluated*)
  text\<open>Only removing one offending flow should be enough\<close>
  fun generate_valid_topology_SOME :: "'v SecurityInvariant_configured list \<Rightarrow> 'v graph \<Rightarrow> 'v graph" where
    "generate_valid_topology_SOME [] G = G" |
    "generate_valid_topology_SOME (m#Ms) G = (if c_sinvar m G
      then generate_valid_topology_SOME Ms G
      else delete_edges (generate_valid_topology_SOME Ms G) (SOME F. F \<in> c_offending_flows m G)
      )"

  lemma generate_valid_topology_SOME_nodes: "nodes (generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>) = V"
    proof(induction M)
    qed(simp_all add: delete_edges_simp2)

  theorem generate_valid_topology_SOME_sound:
    "\<lbrakk> valid_reqs M; wf_graph \<lparr>nodes = V, edges = E\<rparr> \<rbrakk> \<Longrightarrow> 
    all_security_requirements_fulfilled M (generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>)"
      proof(induction M)
        case Nil
        thus ?case by(simp add: all_security_requirements_fulfilled_def)
      next
        case (Cons m M)
        from valid_reqs1[OF Cons(2)] have validReq: "configured_SecurityInvariant m" .
        
        from configured_SecurityInvariant.sinvar_valid_remove_SOME_offending_flows[OF validReq] have
         "c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> \<noteq> {} \<Longrightarrow>
           c_sinvar m \<lparr>nodes = V, edges = E - (SOME F. F \<in> c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)\<rparr>" .

        have generate_valid_topology_SOME_edges: "edges (generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>) \<subseteq> E"
          for M::"'a SecurityInvariant_configured list" and V E
          proof(induction M)
          qed(auto simp add: delete_edges_simp2)

        from configured_SecurityInvariant.mono_sinvar[OF validReq Cons.prems(2),
              of "edges (generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>)"]
            generate_valid_topology_SOME_edges
          have "c_sinvar m \<lparr>nodes = V, edges = E\<rparr> \<Longrightarrow>
            c_sinvar m \<lparr>nodes = V, edges = edges (generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>)\<rparr>"
          by simp
        moreover from configured_SecurityInvariant.defined_offending'[OF validReq Cons.prems(2)] have not_sinvar_off:
          "\<not> c_sinvar m \<lparr>nodes = V, edges = E\<rparr> \<Longrightarrow> c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> \<noteq> {}" by blast
        ultimately have goal_sinvar_m:
          "c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> = {} \<Longrightarrow> 
              c_sinvar m (generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>)"
           using generate_valid_topology_SOME_nodes 
           by (metis graph.select_convs(1) graph.select_convs(2) graph_eq_intro)

        from valid_reqs2[OF Cons(2)] have "valid_reqs M" .
        from Cons.IH[OF \<open>valid_reqs M\<close> Cons(3)] have IH:
          "all_security_requirements_fulfilled M (generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>)" .

        have goal_rm_SOME_m: "c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> \<noteq> {} \<Longrightarrow>
            c_sinvar m (delete_edges (generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>)
                                      (SOME F. F \<in> c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>))"
        proof - (*sledgehammered*)
          assume a1: "c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> \<noteq> {}"
          have f2: "(\<forall>r ra p. \<not> r \<subseteq> ra \<or> (p::'a \<times> 'a) \<notin> r \<or> p \<in> ra) = (\<forall>r ra p. \<not> r \<subseteq> ra \<or> (p::'a \<times> 'a) \<notin> r \<or> p \<in> ra)"
            by meson
          have f3: "wf_graph \<lparr>nodes = V, edges = E - (SOME r. r \<in> c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)\<rparr>"
            by (simp add: Cons.prems(2) wf_graph_remove_edges)
          have "edges (generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>) - (SOME r. r \<in> c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>) \<subseteq> E - (SOME r. r \<in> c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)"
            using f2 generate_valid_topology_SOME_edges[of M V E] by blast
          then have "c_sinvar m \<lparr>nodes = V, edges = edges (generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>) - (SOME r. r \<in> c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)\<rparr>"
            using f3 a1 \<open>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> \<noteq> {} \<Longrightarrow> c_sinvar m \<lparr>nodes = V, edges = E - (SOME F. F \<in> c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)\<rparr>\<close> configured_SecurityInvariant.negative_mono validReq by blast
          then show "c_sinvar m (delete_edges (generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>) (SOME r. r \<in> c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>))"
            by (simp add: generate_valid_topology_SOME_nodes graph_ops(5))
        qed

        have wf_graph_generate_valid_topology_SOME: "wf_graph G \<Longrightarrow> wf_graph (generate_valid_topology_SOME M G)"
          for G (*TODO: tune*)
          apply(cases G)
          apply(simp add: wf_graph_def generate_valid_topology_SOME_nodes)
          using generate_valid_topology_SOME_edges by (meson dual_order.trans image_mono rev_finite_subset) 

        { assume notempty: "c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> \<noteq> {}"
          hence "\<exists> hypE. (generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>) = \<lparr>nodes = V, edges = hypE\<rparr>"
            proof(induction M arbitrary: V E)
            qed(simp_all add: delete_edges_simp2 generate_valid_topology_SOME_nodes)
          from this obtain E_IH where E_IH_prop:
            "(generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>) = \<lparr>nodes = V, edges = E_IH\<rparr>" by blast
    
          from wf_graph_generate_valid_topology_SOME[OF Cons(3)] E_IH_prop
          have valid_G_E_IH: "wf_graph \<lparr>nodes = V, edges = E_IH\<rparr>" by simp
    
          from all_security_requirements_fulfilled_mono[OF \<open>valid_reqs M\<close> _ valid_G_E_IH ] IH E_IH_prop
          have mono_rule: "E' \<subseteq> E_IH \<Longrightarrow> all_security_requirements_fulfilled M \<lparr>nodes = V, edges = E'\<rparr>" for E' by simp
  
          have "all_security_requirements_fulfilled M
            (delete_edges (generate_valid_topology_SOME M \<lparr>nodes = V, edges = E\<rparr>)
                          (SOME F. F \<in> c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>))"
            unfolding E_IH_prop by(auto simp add: delete_edges_simp2 intro:mono_rule)
        } note goal_fulfilled_M=this

        have no_offending: "c_sinvar m \<lparr>nodes = V, edges = E\<rparr> \<Longrightarrow> c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> = {}"
          by (simp add: configured_SecurityInvariant.c_sinvar_valid_imp_no_offending_flows validReq)

        show "all_security_requirements_fulfilled (m # M) (generate_valid_topology_SOME (m # M) \<lparr>nodes = V, edges = E\<rparr>)"
        apply(simp add: all_security_requirements_fulfilled_def)
        apply(intro conjI impI)
           subgoal using goal_sinvar_m no_offending by blast
          subgoal using IH by(simp add: all_security_requirements_fulfilled_def; fail)
         subgoal using goal_rm_SOME_m not_sinvar_off by blast 
        subgoal using goal_fulfilled_M not_sinvar_off by(simp add: all_security_requirements_fulfilled_def)
        done
     qed

    
   lemma generate_valid_topology_SOME_def_alt:
      "generate_valid_topology_SOME M G = delete_edges G (\<Union>m \<in> set M. if c_sinvar m G then {} else (SOME F. F \<in> c_offending_flows m G))"
      proof(induction M arbitrary: G)
        case Nil
          thus ?case by(simp add: get_offending_flows_def)
        next
        case (Cons m M)
          from Cons[simplified delete_edges_simp2 get_offending_flows_def] 
          have IH :"edges (generate_valid_topology_SOME M G) =
                   edges G - (\<Union>m\<in>set M. if c_sinvar m G then {} else SOME F. F \<in> c_offending_flows m G)"
            by simp
          hence "\<not> c_sinvar m G \<Longrightarrow> 
                    edges (generate_valid_topology_SOME (m # M) G) =
                    (edges G) - (\<Union>m\<in>set (m#M). if c_sinvar m G then {} else SOME F. F \<in> c_offending_flows m G)"
            apply(simp add: get_offending_flows_def delete_edges_simp2)
            by blast
          with Cons.IH show ?case by(simp add: get_offending_flows_def delete_edges_simp2)
      qed

    lemma generate_valid_topology_SOME_superset:
      "\<lbrakk> valid_reqs M; wf_graph G \<rbrakk> \<Longrightarrow> 
      edges (generate_valid_topology M G) \<subseteq> edges (generate_valid_topology_SOME M G)"
    proof -
      have isabelle2016_1_helper:
        "x \<in> (\<Union>m\<in>set M. if c_sinvar m G then {} else SOME F. F \<in> c_offending_flows m G) \<longleftrightarrow>
          (\<exists>m\<in>set M. \<not> c_sinvar m G \<and> (c_sinvar m G \<or> x \<in> (SOME F. F \<in> c_offending_flows m G)))"
        for x by auto
      have 1: "m\<in>set M \<Longrightarrow> \<not> c_sinvar m G \<and> (c_sinvar m G \<or> x \<in> (SOME F. F \<in> c_offending_flows m G)) \<Longrightarrow>
            c_offending_flows m G \<noteq> {} \<Longrightarrow>
            x \<in> \<Union>(\<Union>m\<in>set M. c_offending_flows m G)"
      for x m
      apply(simp)
      apply(rule_tac x=m in bexI)
      apply(simp_all)
       using some_in_eq by blast
     
      show "valid_reqs M \<Longrightarrow> wf_graph G \<Longrightarrow> ?thesis"
      unfolding generate_valid_topology_SOME_def_alt generate_valid_topology_def_alt
      apply (rule delete_edges_edges_mono)
      apply (auto simp add: delete_edges_simp2 get_offending_flows_def valid_reqs_def)
      apply (metis (full_types) configured_SecurityInvariant.defined_offending' some_in_eq)
      done
    qed




  text\<open>Notation:
    @{const generate_valid_topology_SOME}: non-deterministic choice
    \<open>generate_valid_topology_some\<close>: executable which selects always the same
\<close>
  fun generate_valid_topology_some :: "'v SecurityInvariant_configured list \<Rightarrow> ('v\<times>'v) list \<Rightarrow> 'v graph \<Rightarrow> 'v graph" where
    "generate_valid_topology_some [] _ G = G" |
    "generate_valid_topology_some (m#Ms) Es G = (if c_sinvar m G
      then generate_valid_topology_some Ms Es G
      else delete_edges (generate_valid_topology_some Ms Es G) (set (minimalize_offending_overapprox (c_sinvar m) Es [] G))
      )"
  theorem generate_valid_topology_some_sound:
    "\<lbrakk> valid_reqs M; wf_graph \<lparr>nodes = V, edges = E\<rparr>; set Es = E; distinct Es \<rbrakk> \<Longrightarrow> 
    all_security_requirements_fulfilled M (generate_valid_topology_some M Es \<lparr>nodes = V, edges = E\<rparr>)"
      proof(induction M)
        case Nil
        thus ?case by(simp add: all_security_requirements_fulfilled_def)
      next
        case (Cons m M)
        from valid_reqs1[OF Cons(2)] have validReq: "configured_SecurityInvariant m" .
         
        from configured_SecurityInvariant.sinvar_valid_remove_minimalize_offending_overapprox[OF
          validReq Cons.prems(2) _  Cons.prems(3) Cons.prems(4)] have rm_off_valid:
         "\<not> c_sinvar m \<lparr>nodes = V, edges = E\<rparr>\<Longrightarrow>
           c_sinvar m \<lparr>nodes = V, edges = E - (set (minimalize_offending_overapprox (c_sinvar m) Es [] \<lparr>nodes = V, edges = E\<rparr>))\<rparr>"
        apply(subst(asm) minimalize_offending_overapprox_boundnP[symmetric]) (*TODO: type for nP unspecified!*)
        by blast

        have generate_valid_topology_some_nodes: "nodes (generate_valid_topology_some M Es \<lparr>nodes = V, edges = E\<rparr>) = V"
          for M::"'a SecurityInvariant_configured list" and V E
          proof(induction M)
          qed(simp_all add: delete_edges_simp2)


        have generate_valid_topology_some_edges: "edges (generate_valid_topology_some M Es \<lparr>nodes = V, edges = E\<rparr>) \<subseteq> E"
          for M::"'a SecurityInvariant_configured list" and V E
          proof(induction M)
          qed(auto simp add: delete_edges_simp2)
        
        from configured_SecurityInvariant.mono_sinvar[OF validReq Cons.prems(2),
              of "edges (generate_valid_topology_some M Es \<lparr>nodes = V, edges = E\<rparr>)"]
            generate_valid_topology_some_edges
          have "c_sinvar m \<lparr>nodes = V, edges = E\<rparr> \<Longrightarrow>
            c_sinvar m \<lparr>nodes = V, edges = edges (generate_valid_topology_some M Es \<lparr>nodes = V, edges = E\<rparr>)\<rparr>"
          by simp
        moreover from configured_SecurityInvariant.defined_offending'[OF validReq Cons.prems(2)] have not_sinvar_off:
          "\<not> c_sinvar m \<lparr>nodes = V, edges = E\<rparr> \<Longrightarrow> c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> \<noteq> {}" by blast
        ultimately have goal_sinvar_m:
          "c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> = {} \<Longrightarrow> 
              c_sinvar m (generate_valid_topology_some M Es \<lparr>nodes = V, edges = E\<rparr>)"
           using generate_valid_topology_some_nodes 
           by (metis graph.select_convs(1) graph.select_convs(2) graph_eq_intro)

  
        from valid_reqs2[OF Cons(2)] have "valid_reqs M" .
        from Cons.IH[OF \<open>valid_reqs M\<close> Cons(3)] Cons.prems have IH:
          "all_security_requirements_fulfilled M (generate_valid_topology_some M Es \<lparr>nodes = V, edges = E\<rparr>)" by simp

 


        have wf_graph_generate_valid_topology_some: "wf_graph G \<Longrightarrow> wf_graph (generate_valid_topology_some M Es G)"
          for G (*TODO: tune*)
          apply(cases G)
          apply(simp add: wf_graph_def generate_valid_topology_some_nodes)
          using generate_valid_topology_some_edges by (meson dual_order.trans image_mono rev_finite_subset) 

        
        { assume notempty: "c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> \<noteq> {}"
          hence "\<exists> hypE. (generate_valid_topology_some M Es \<lparr>nodes = V, edges = E\<rparr>) = \<lparr>nodes = V, edges = hypE\<rparr>"
            proof(induction M arbitrary: V E)
            qed(simp_all add: delete_edges_simp2 generate_valid_topology_some_nodes)
          from this obtain E_IH where E_IH_prop:
            "(generate_valid_topology_some M Es \<lparr>nodes = V, edges = E\<rparr>) = \<lparr>nodes = V, edges = E_IH\<rparr>" by blast
    
          from wf_graph_generate_valid_topology_some[OF Cons(3)] E_IH_prop
          have valid_G_E_IH: "wf_graph \<lparr>nodes = V, edges = E_IH\<rparr>" by simp
    
          from all_security_requirements_fulfilled_mono[OF \<open>valid_reqs M\<close> _ valid_G_E_IH ] IH E_IH_prop
          have mono_rule: "E' \<subseteq> E_IH \<Longrightarrow> all_security_requirements_fulfilled M \<lparr>nodes = V, edges = E'\<rparr>" for E' by simp
  
          have "all_security_requirements_fulfilled M
            (delete_edges (generate_valid_topology_some M Es \<lparr>nodes = V, edges = E\<rparr>)
                          (set (minimalize_offending_overapprox (c_sinvar m) Es [] \<lparr>nodes = V, edges = E\<rparr>)))"
            unfolding E_IH_prop by(auto simp add: delete_edges_simp2 intro:mono_rule)
        } note goal_fulfilled_M=this

        have no_offending: "c_sinvar m \<lparr>nodes = V, edges = E\<rparr> \<Longrightarrow> c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> = {}"
          by (simp add: configured_SecurityInvariant.c_sinvar_valid_imp_no_offending_flows validReq)

        show "all_security_requirements_fulfilled (m # M) (generate_valid_topology_some (m # M) Es \<lparr>nodes = V, edges = E\<rparr>)"
        apply(simp add: all_security_requirements_fulfilled_def)
        apply(intro conjI impI)
           subgoal using goal_sinvar_m no_offending by blast
          subgoal using IH by(simp add: all_security_requirements_fulfilled_def; fail)
         subgoal using rm_off_valid by (metis (no_types, lifting) Cons.prems(2) Diff_mono 
            configured_SecurityInvariant.mono_sinvar delete_edges_simp2 generate_valid_topology_some_edges
            generate_valid_topology_some_nodes order_refl validReq wf_graph_remove_edges) (*TODO!*)
        subgoal using goal_fulfilled_M not_sinvar_off by(simp add: all_security_requirements_fulfilled_def)
        done
     qed



end
