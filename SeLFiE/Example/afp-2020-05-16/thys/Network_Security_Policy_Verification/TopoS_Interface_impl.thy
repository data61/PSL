theory TopoS_Interface_impl
imports "Lib/FiniteGraph" "Lib/FiniteListGraph" TopoS_Interface TopoS_Helper
begin

section\<open>Executable Implementation with Lists\<close>
  text \<open>Correspondence List Implementation and set Specification\<close>
  
  subsection\<open>Abstraction from list implementation to set specification\<close>
  text\<open>Nomenclature: \<open>_spec\<close> is the specification, \<open>_impl\<close> the corresponding implementation.\<close>

  text\<open>\<open>_spec\<close> and \<open>_impl\<close> only need to comply for @{const wf_graph}s. 
   We will always require the stricter @{const wf_list_graph}, which implies @{const wf_graph}.
\<close>
  lemma "wf_list_graph G \<Longrightarrow> wf_graph (list_graph_to_graph G)"
    by %invisible (metis wf_list_graph_def wf_list_graph_iff_wf_graph)

  locale TopoS_List_Impl = 
    fixes default_node_properties :: "'a" ("\<bottom>") 
    and sinvar_spec::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool"
    and sinvar_impl::"('v::vertex) list_graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool"
    and receiver_violation :: "bool"
    and offending_flows_impl::"('v::vertex) list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<times> 'v) list list"
    and node_props_impl::"('v::vertex, 'a) TopoS_Params \<Rightarrow> ('v \<Rightarrow> 'a)"
    and eval_impl::"('v::vertex) list_graph \<Rightarrow> ('v, 'a) TopoS_Params \<Rightarrow> bool"
    assumes
      spec: "SecurityInvariant sinvar_spec default_node_properties receiver_violation" \<comment> \<open>specification is valid\<close>
    and
      sinvar_spec_impl: "wf_list_graph G \<Longrightarrow> 
        (sinvar_spec (list_graph_to_graph G) nP) = (sinvar_impl G nP)"
    and
      offending_flows_spec_impl: "wf_list_graph G \<Longrightarrow> 
      (SecurityInvariant_withOffendingFlows.set_offending_flows sinvar_spec (list_graph_to_graph G) nP) = 
      set`set (offending_flows_impl G nP)"
    and 
      node_props_spec_impl: 
     "SecurityInvariant.node_props_formaldef default_node_properties P = node_props_impl P"
    and
      eval_spec_impl:
     "(distinct (nodesL G) \<and> distinct (edgesL G) \<and> 
     SecurityInvariant.eval sinvar_spec default_node_properties (list_graph_to_graph G) P ) = 
     (eval_impl G P)"

  subsection \<open>Security Invariants Packed\<close>

  text \<open>We pack all necessary functions and properties of a security invariant in a struct-like data structure.\<close>
  record ('v::vertex, 'a) TopoS_packed =
    nm_name :: "string"
    nm_receiver_violation :: "bool"
    nm_default :: "'a"
    nm_sinvar::"('v::vertex) list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool"
    nm_offending_flows::"('v::vertex) list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<times> 'v) list list"
    nm_node_props::"('v::vertex, 'a) TopoS_Params \<Rightarrow> ('v \<Rightarrow> 'a)" 
    nm_eval::"('v::vertex) list_graph \<Rightarrow> ('v, 'a)TopoS_Params \<Rightarrow> bool"
    


   text\<open>The packed list implementation must comply with the formal definition.\<close>
   locale TopoS_modelLibrary =
    fixes m :: "('v::vertex, 'a) TopoS_packed" \<comment> \<open>concrete model implementation\<close>
    and sinvar_spec::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool" \<comment> \<open>specification\<close>
    assumes
       name_not_empty: "length (nm_name m) > 0"
     and
       impl_spec: "TopoS_List_Impl 
        (nm_default m)
        sinvar_spec
        (nm_sinvar m)
        (nm_receiver_violation m)
        (nm_offending_flows m)
        (nm_node_props m)
        (nm_eval m)"



  subsection\<open>Helpful Lemmata\<close>

  text\<open>show that @{term "sinvar"} complies\<close>
  lemma TopoS_eval_impl_proofrule: 
    assumes inst: "SecurityInvariant sinvar_spec default_node_properties receiver_violation"
    assumes ev: "\<And>nP. wf_list_graph G \<Longrightarrow> sinvar_spec (list_graph_to_graph G) nP = sinvar_impl G nP"
    shows "
      (distinct (nodesL G) \<and> distinct (edgesL G) \<and> 
       SecurityInvariant.eval sinvar_spec default_node_properties (list_graph_to_graph G) P) =
      (wf_list_graph G \<and> sinvar_impl G (SecurityInvariant.node_props default_node_properties P))"
  proof (cases "wf_list_graph G")
    case True
    hence "sinvar_spec (list_graph_to_graph G) (SecurityInvariant.node_props default_node_properties P) =
       sinvar_impl G (SecurityInvariant.node_props default_node_properties P)"
      using ev by blast

    with inst show ?thesis
      unfolding wf_list_graph_def 
      by (simp add: wf_list_graph_iff_wf_graph SecurityInvariant.eval_def)
  next
    case False
    hence "(distinct (nodesL G) \<and> distinct (edgesL G) \<and> wf_list_graph_axioms G) = False"
      unfolding wf_list_graph_def by blast
    with False show ?thesis
      unfolding SecurityInvariant.eval_def[OF inst]
      by (fastforce simp: wf_list_graph_iff_wf_graph)
  qed


subsection \<open>Helper lemmata\<close>

  text\<open>Provide @{term sinvar} function and get back a function that computes the list of offending flows
  
  Exponential time!
\<close>
  definition Generic_offending_list:: "('v list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool )\<Rightarrow> 'v list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<times> 'v) list list" where
    "Generic_offending_list sinvar G nP = [f \<leftarrow> (subseqs (edgesL G)). 
    (\<not> sinvar G nP \<and> sinvar (FiniteListGraph.delete_edges G f) nP) \<and> 
      (\<forall>(e1, e2)\<in>set f. \<not> sinvar (add_edge e1 e2 (FiniteListGraph.delete_edges G f)) nP)]"
  
  
  text\<open>proof rule: if @{term sinvar} complies, @{const Generic_offending_list} complies\<close>
  lemma Generic_offending_list_correct: 
    assumes valid: "wf_list_graph G"
    assumes spec_impl: "\<And>G nP. wf_list_graph G \<Longrightarrow> sinvar_spec (list_graph_to_graph G) nP = sinvar_impl G nP"
    shows "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar_spec (list_graph_to_graph G) nP = 
      set`set( Generic_offending_list sinvar_impl G nP )"
  proof -
    have "\<And> P G. set ` {x \<in> set (subseqs (edgesL G)). P G (set x)} = {x \<in> set ` set (subseqs (edgesL G)). P G (x)}"
      by fastforce
    hence subset_subseqs_filter: "\<And> G P. {f. f \<subseteq> edges (list_graph_to_graph G) \<and> P G f} 
    = set ` set [f\<leftarrow>subseqs (edgesL G) . P G (set f)]"
      unfolding list_graph_to_graph_def
      by (auto simp: subseqs_powset)

    from valid delete_edges_wf have "\<forall>f. wf_list_graph(FiniteListGraph.delete_edges G f)" by fast
    with spec_impl[symmetric] FiniteListGraph.delete_edges_correct[of "G"] have impl_spec_delete:
      "\<forall>f. sinvar_impl (FiniteListGraph.delete_edges G f) nP = 
          sinvar_spec (FiniteGraph.delete_edges (list_graph_to_graph G) (set f)) nP" by simp

    from spec_impl[OF valid, symmetric] have impl_spec_not:
      "(\<not> sinvar_impl G nP) = (\<not> sinvar_spec (list_graph_to_graph G) nP)" by auto

    from spec_impl[symmetric, OF FiniteListGraph.add_edge_wf[OF FiniteListGraph.delete_edges_wf[OF valid]]] have impl_spec_allE:
    "\<forall> e1 e2 E. sinvar_impl (FiniteListGraph.add_edge e1 e2 (FiniteListGraph.delete_edges G E)) nP =
    sinvar_spec (list_graph_to_graph (FiniteListGraph.add_edge e1 e2 (FiniteListGraph.delete_edges G E))) nP" by simp

    have list_graph: "\<And> e1 e2 G f. (list_graph_to_graph (FiniteListGraph.add_edge e1 e2 (FiniteListGraph.delete_edges G f))) = 
      (FiniteGraph.add_edge e1 e2 (FiniteGraph.delete_edges (list_graph_to_graph G) (set f)))"
    by(simp add: FiniteListGraph.add_edge_correct FiniteListGraph.delete_edges_correct)
    
    show ?thesis 
      unfolding SecurityInvariant_withOffendingFlows.set_offending_flows_def 
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def 
      SecurityInvariant_withOffendingFlows.is_offending_flows_def
      Generic_offending_list_def
        apply(subst impl_spec_delete)
        apply(subst impl_spec_not)
        apply(subst impl_spec_allE)
        apply(subst list_graph)
        apply(rule subset_subseqs_filter)
        done
  qed

  lemma all_edges_list_I: "P (list_graph_to_graph G) = Pl G \<Longrightarrow> 
    (\<forall>(e1, e2)\<in> (edges (list_graph_to_graph G)). P (list_graph_to_graph G) e1 e2) = (\<forall>(e1, e2)\<in>set (edgesL G). Pl G e1 e2)"
  unfolding list_graph_to_graph_def
  by simp

  lemma all_nodes_list_I: "P (list_graph_to_graph G) = Pl G \<Longrightarrow> 
    (\<forall>n \<in> (nodes (list_graph_to_graph G)). P (list_graph_to_graph G) n) = (\<forall> n \<in>set (nodesL G). Pl G n)"
  unfolding list_graph_to_graph_def
  by simp






  fun minimalize_offending_overapprox :: "('v list_graph \<Rightarrow> bool) \<Rightarrow> 
    ('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'v list_graph \<Rightarrow> ('v \<times> 'v) list" where
  "minimalize_offending_overapprox _ [] keep _ = keep" |
  "minimalize_offending_overapprox m (f#fs) keep G = (if m (delete_edges G (fs@keep)) then
      minimalize_offending_overapprox m fs keep G
    else
      minimalize_offending_overapprox m fs (f#keep) G
    )"

  thm minimalize_offending_overapprox_boundnP (*is usage of this one better?*)
  lemma minimalize_offending_overapprox_spec_impl:
    assumes valid: "wf_list_graph (G::'v::vertex list_graph)"
        and spec_impl: "\<And>G nP::('v \<Rightarrow> 'a). wf_list_graph G \<Longrightarrow> sinvar_spec (list_graph_to_graph G) nP = sinvar_impl G nP"
    shows "minimalize_offending_overapprox (\<lambda>G. sinvar_impl G nP) fs keeps G =
       TopoS_withOffendingFlows.minimalize_offending_overapprox (\<lambda>G. sinvar_spec G nP) fs keeps (list_graph_to_graph G)"
    apply(subst minimalize_offending_overapprox_boundnP)
    using valid spec_impl apply(induction fs arbitrary: keeps)
     apply(simp add: SecurityInvariant_withOffendingFlows.minimalize_offending_overapprox.simps; fail)
    apply(simp add: SecurityInvariant_withOffendingFlows.minimalize_offending_overapprox.simps)
    apply (metis FiniteListGraph.delete_edges_wf delete_edges_list_set list_graph_correct(5))
    done

  text\<open>With @{const minimalize_offending_overapprox}, we can get one offending flow\<close>
  lemma minimalize_offending_overapprox_gives_some_offending_flow:
    assumes wf: "wf_list_graph G"
        and NetModelLib: "TopoS_modelLibrary m sinvar_spec"
        and violation: "\<not> (nm_sinvar m) G nP"
    shows "set (minimalize_offending_overapprox (\<lambda>G. (nm_sinvar m) G nP) (edgesL G) [] G) \<in>
            SecurityInvariant_withOffendingFlows.set_offending_flows sinvar_spec (list_graph_to_graph G) nP"
    proof -
      from wf have wfG: "wf_graph (list_graph_to_graph G)"
        by (simp add: wf_list_graph_def wf_list_graph_iff_wf_graph)
      from wf have dist_edges: "distinct (edgesL G)" by (simp add: wf_list_graph_def)

      let ?spec_algo="TopoS_withOffendingFlows.minimalize_offending_overapprox
                          (\<lambda>G. sinvar_spec G nP) (edgesL G) [] (list_graph_to_graph G)"

      note spec=TopoS_List_Impl.spec[OF TopoS_modelLibrary.impl_spec[OF NetModelLib]]

      from spec have spec_prelim: "SecurityInvariant_preliminaries sinvar_spec"
        by(simp add: SecurityInvariant_def)
      from spec_prelim SecurityInvariant_preliminaries.sinvar_monoI have mono:
        "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar_spec" by blast
        
      from spec_prelim have empty_edges: "sinvar_spec \<lparr>nodes = set (nodesL G), edges = {}\<rparr> nP"
      using SecurityInvariant_preliminaries.defined_offending 
        SecurityInvariant_withOffendingFlows.sinvar_mono_imp_sinvar_mono 
        SecurityInvariant_withOffendingFlows.valid_empty_edges_iff_exists_offending_flows  
        mono empty_subsetI graph.simps(1) 
        list_graph_to_graph_def local.wf wf_list_graph_def wf_list_graph_iff_wf_graph
        by (metis)

      (*TODO: tune*)
      have spec_impl: "wf_list_graph G \<Longrightarrow> sinvar_spec (list_graph_to_graph G) nP = (nm_sinvar m) G nP" for G nP
        using NetModelLib TopoS_List_Impl.sinvar_spec_impl TopoS_modelLibrary.impl_spec by fastforce
      
      from minimalize_offending_overapprox_spec_impl[OF wf] spec_impl have alog_spec:
        "minimalize_offending_overapprox (\<lambda>G. (nm_sinvar m) G nP) fs keeps G =
         TopoS_withOffendingFlows.minimalize_offending_overapprox (\<lambda>G. sinvar_spec G nP) fs keeps (list_graph_to_graph G)"
         for fs keeps by blast

      (*TODO: tune*)
      from spec_impl violation have
        "SecurityInvariant_withOffendingFlows.is_offending_flows sinvar_spec (set (edgesL G)) (list_graph_to_graph G) nP"
        apply(simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def)
        apply(intro conjI)
         apply (simp add: local.wf; fail)
        apply(simp add: FiniteGraph.delete_edges_simp2 list_graph_to_graph_def)
        apply(simp add: empty_edges)
        done
      hence goal: "SecurityInvariant_withOffendingFlows.is_offending_flows_min_set sinvar_spec
        (set ?spec_algo) (list_graph_to_graph G) nP"
      apply(subst minimalize_offending_overapprox_boundnP) (*we do this subst pretty often. is this the right abstraction here?*)
      apply(rule SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_minimalize_offending_overapprox[OF
              mono wfG _ _ dist_edges])
       apply(simp add: list_graph_to_graph_def)+
      done

      from SecurityInvariant_withOffendingFlows.minimalize_offending_overapprox_subseteq_input[of
        "sinvar_spec" "(edgesL G)" "[]"] have subset_edges:
        "set ?spec_algo \<subseteq> edges (list_graph_to_graph G)" 
        apply(subst minimalize_offending_overapprox_boundnP)
        by(simp add: list_graph_to_graph_def)

      from goal show ?thesis
        by(simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def alog_spec subset_edges)
    qed






(*TODO: this should be a header of TopoS_Libary. The header should be printed BEFORE the imports are processed. *)
section\<open>Security Invariant Library\<close>
(*The SINVAR_* theory files all use the "subsection" command. Here is the top-section.*)

end
