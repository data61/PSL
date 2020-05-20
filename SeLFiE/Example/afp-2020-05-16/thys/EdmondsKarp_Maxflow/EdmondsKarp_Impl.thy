section \<open>Implementation of the Edmonds-Karp Algorithm\<close>
theory EdmondsKarp_Impl
imports 
  EdmondsKarp_Algo
  Augmenting_Path_BFS
  Refine_Imperative_HOL.IICF
begin

  text \<open>We now implement the Edmonds-Karp algorithm.
    Note that, during the implementation, we explicitly write down the 
    whole refined algorithm several times. As refinement is modular, most 
    of these copies could be avoided--- we inserted them deliberately for
    documentation purposes.
    \<close>

  subsection \<open>Refinement to Residual Graph\<close>
    text \<open>As a first step towards implementation, we refine the algorithm
      to work directly on residual graphs. For this, we first have to 
      establish a relation between flows in a network and residual graphs.
      \<close>
    
  subsubsection \<open>Refinement of Operations\<close>
  context Network 
  begin
    text \<open>We define the relation between residual graphs and flows\<close>
    definition "cfi_rel \<equiv> br flow_of_cf (RGraph c s t)"

    text \<open>It can also be characterized the other way round, i.e., 
      mapping flows to residual graphs:\<close>
    lemma cfi_rel_alt: "cfi_rel = {(cf,f). cf = residualGraph c f \<and> NFlow c s t f}"
      unfolding cfi_rel_def br_def
      by (auto 
          simp: NFlow.is_RGraph RGraph.is_NFlow 
          simp: RPreGraph.rg_fo_inv[OF RGraph.this_loc_rpg]
          simp: NPreflow.fo_rg_inv[OF NFlow.axioms(1)])

    
    text \<open>Initially, the residual graph for the zero flow equals the original network\<close>
    lemma residualGraph_zero_flow: "residualGraph c (\<lambda>_. 0) = c" 
      unfolding residualGraph_def by (auto intro!: ext)
    lemma flow_of_c: "flow_of_cf c = (\<lambda>_. 0)"
      by (auto simp add: flow_of_cf_def[abs_def])

    text \<open>The residual capacity is naturally defined on residual graphs\<close>
    definition "resCap_cf cf p \<equiv> Min {cf e | e. e\<in>set p}"
    lemma (in NFlow) resCap_cf_refine: "resCap_cf cf p = resCap p"
      unfolding resCap_cf_def resCap_def ..

    text \<open>Augmentation can be done by @{const Graph.augment_cf}.\<close> 

    
    lemma (in NFlow) augment_cf_refine_aux: (* For snippet *)
      assumes AUG: "isAugmentingPath p"
      shows "residualGraph c (augment (augmentingFlow p)) (u,v) = (
        if (u,v)\<in>set p then (residualGraph c f (u,v) - resCap p)
        else if (v,u)\<in>set p then (residualGraph c f (u,v) + resCap p)
        else residualGraph c f (u,v))"
      using augment_alt[OF AUG] by (auto simp: Graph.augment_cf_def)

    lemma augment_cf_refine:
      assumes R: "(cf,f)\<in>cfi_rel"
      assumes AUG: "NPreflow.isAugmentingPath c s t f p"
      shows "(Graph.augment_cf cf (set p) (resCap_cf cf p), 
          NFlow.augment_with_path c f p) \<in> cfi_rel"
    proof -    
      from R have [simp]: "cf = residualGraph c f" and "NFlow c s t f"
        by (auto simp: cfi_rel_alt br_def)
      then interpret f: NFlow c s t f by simp
      
      show ?thesis 
        unfolding f.augment_with_path_def
      proof (simp add: cfi_rel_alt; safe intro!: ext)
        fix u v
        show "Graph.augment_cf f.cf (set p) (resCap_cf f.cf p) (u,v) 
              = residualGraph c (f.augment (f.augmentingFlow p)) (u,v)"
          unfolding f.augment_cf_refine_aux[OF AUG]
          unfolding f.cf.augment_cf_def
          by (auto simp: f.resCap_cf_refine)
      qed (rule f.augment_pres_nflow[OF AUG])
    qed  

    text \<open>We rephrase the specification of shortest augmenting path to
      take a residual graph as parameter\<close>
    (* TODO: This actually rephrases the spec to make it look more similar to 
      what BFS does later. This rephrasing does not belong here, but where we 
      implement it with BFS. *)
    definition "find_shortest_augmenting_spec_cf cf \<equiv> 
      assert (RGraph c s t cf) \<then>
      SPEC (\<lambda>
        None \<Rightarrow> \<not>Graph.connected cf s t 
      | Some p \<Rightarrow> Graph.isShortestPath cf s p t)"

    lemma (in RGraph) find_shortest_augmenting_spec_cf_refine: 
       "find_shortest_augmenting_spec_cf cf 
      \<le> find_shortest_augmenting_spec (flow_of_cf cf)"
      unfolding f_def[symmetric]
      unfolding find_shortest_augmenting_spec_cf_def 
        and find_shortest_augmenting_spec_def
      by (auto 
        simp: pw_le_iff refine_pw_simps 
        simp: this_loc rg_is_cf
        simp: f.isAugmentingPath_def Graph.connected_def Graph.isSimplePath_def 
        dest: cf.shortestPath_is_path
        split: option.split)
      
    text \<open>This leads to the following refined algorithm\<close>  
    definition "edka2 \<equiv> do {
      let cf = c;

      (cf,_) \<leftarrow> while\<^sub>T 
        (\<lambda>(cf,brk). \<not>brk) 
        (\<lambda>(cf,_). do {
          assert (RGraph c s t cf);
          p \<leftarrow> find_shortest_augmenting_spec_cf cf;
          case p of 
            None \<Rightarrow> return (cf,True)
          | Some p \<Rightarrow> do {
              assert (p\<noteq>[]);
              assert (Graph.isShortestPath cf s p t);
              let cf = Graph.augment_cf cf (set p) (resCap_cf cf p);
              assert (RGraph c s t cf);
              return (cf, False)
            }  
        })
        (cf,False);
      assert (RGraph c s t cf);
      let f = flow_of_cf cf;  
      return f
    }"

    lemma edka2_refine: "edka2 \<le> \<Down>Id edka"
    proof -
      have [refine_dref_RELATES]: "RELATES cfi_rel" by (simp add: RELATES_def)

      show ?thesis
        unfolding edka2_def edka_def
        (*apply (rewrite in "let f' = NFlow.augmentingFlow c _ _ in _" Let_def)
        apply (rewrite in "let f = flow_of_cf _ in _" Let_def)*)
        apply (refine_rcg)
        apply refine_dref_type
        apply vc_solve

        \<comment> \<open>Solve some left-over verification conditions one by one\<close>
        apply (drule NFlow.is_RGraph; 
            auto simp: cfi_rel_def br_def residualGraph_zero_flow flow_of_c; 
            fail)
        apply (auto simp: cfi_rel_def br_def; fail)
        using RGraph.find_shortest_augmenting_spec_cf_refine
        apply (auto simp: cfi_rel_def br_def; fail)
        apply (auto simp: cfi_rel_def br_def simp: RPreGraph.rg_fo_inv[OF RGraph.this_loc_rpg]; fail)
        apply (drule (1) augment_cf_refine; simp add: cfi_rel_def br_def; fail)
        apply (simp add: augment_cf_refine; fail)
        apply (auto simp: cfi_rel_def br_def; fail)
        apply (auto simp: cfi_rel_def br_def; fail)
        done

    qed    

    subsection \<open>Implementation of Bottleneck Computation and Augmentation\<close>  
    text \<open>We will access the capacities in the residual graph
      only by a get-operation, which asserts that the edges are valid\<close>
    
    abbreviation (input) valid_edge :: "edge \<Rightarrow> bool" where
      "valid_edge \<equiv> \<lambda>(u,v). u\<in>V \<and> v\<in>V"

    definition cf_get 
      :: "'capacity graph \<Rightarrow> edge \<Rightarrow> 'capacity nres" 
      where "cf_get cf e \<equiv> ASSERT (valid_edge e) \<then> RETURN (cf e)"  
    definition cf_set 
      :: "'capacity graph \<Rightarrow> edge \<Rightarrow> 'capacity \<Rightarrow> 'capacity graph nres"
      where "cf_set cf e cap \<equiv> ASSERT (valid_edge e) \<then> RETURN (cf(e:=cap))"  

    definition resCap_cf_impl :: "'capacity graph \<Rightarrow> path \<Rightarrow> 'capacity nres" 
    where "resCap_cf_impl cf p \<equiv> 
      case p of
        [] \<Rightarrow> RETURN (0::'capacity)
      | (e#p) \<Rightarrow> do {
          cap \<leftarrow> cf_get cf e;
          ASSERT (distinct p);
          nfoldli 
            p (\<lambda>_. True)
            (\<lambda>e cap. do {
              cape \<leftarrow> cf_get cf e;
              RETURN (min cape cap)
            }) 
            cap
        }"

    lemma (in RGraph) resCap_cf_impl_refine:   
      assumes AUG: "cf.isSimplePath s p t"
      shows "resCap_cf_impl cf p \<le> SPEC (\<lambda>r. r = resCap_cf cf p)"
    proof -
      (* TODO: Can we exploit Min.set_eq_fold *)

      note [simp del] = Min_insert
      note [simp] = Min_insert[symmetric]
      from AUG[THEN cf.isSPath_distinct]
      have "distinct p" .
      moreover from AUG cf.isPath_edgeset have "set p \<subseteq> cf.E"
        by (auto simp: cf.isSimplePath_def)
      hence "set p \<subseteq> Collect valid_edge"  
        using cf.E_ss_VxV by simp
      moreover from AUG have "p\<noteq>[]" by (auto simp: s_not_t) 
        then obtain e p' where "p=e#p'" by (auto simp: neq_Nil_conv)
      ultimately show ?thesis  
        unfolding resCap_cf_impl_def resCap_cf_def cf_get_def
        apply (simp only: list.case)
        apply (refine_vcg nfoldli_rule[where 
            I = "\<lambda>l l' cap. 
              cap = Min (cf`insert e (set l)) 
            \<and> set (l@l') \<subseteq> Collect valid_edge"])
        apply (auto intro!: arg_cong[where f=Min])
        done
    qed    

    definition (in Graph) 
      "augment_edge e cap \<equiv> (c(
                  e := c e - cap, 
        prod.swap e := c (prod.swap e) + cap))"

    (* TODO: This would be much simpler to prove if we had a characterization 
      of simple-path only depending on p. *)    
    lemma (in Graph) augment_cf_inductive:
      fixes e cap
      defines "c' \<equiv> augment_edge e cap"
      assumes P: "isSimplePath s (e#p) t"
      shows "augment_cf (insert e (set p)) cap = Graph.augment_cf c' (set p) cap"
      and "\<exists>s'. Graph.isSimplePath c' s' p t"  
    proof -
      obtain u v where [simp]: "e=(u,v)" by (cases e)

      from isSPath_no_selfloop[OF P] have [simp]: "\<And>u. (u,u)\<notin>set p" "u\<noteq>v" by auto

      from isSPath_nt_parallel[OF P] have [simp]: "(v,u)\<notin>set p" by auto
      from isSPath_distinct[OF P] have [simp]: "(u,v)\<notin>set p" by auto

      show "augment_cf (insert e (set p)) cap = Graph.augment_cf c' (set p) cap"
        apply (rule ext)  
        unfolding Graph.augment_cf_def c'_def Graph.augment_edge_def
        by auto

      have "Graph.isSimplePath c' v p t"  
        unfolding Graph.isSimplePath_def
        apply rule
        apply (rule transfer_path)
        unfolding Graph.E_def
        apply (auto simp: c'_def Graph.augment_edge_def) []
        using P apply (auto simp: isSimplePath_def) []
        using P apply (auto simp: isSimplePath_def) []
        done
      thus "\<exists>s'. Graph.isSimplePath c' s' p t" .. 

    qed    
        
    definition "augment_edge_impl cf e cap \<equiv> do {
      v \<leftarrow> cf_get cf e; cf \<leftarrow> cf_set cf e (v-cap);
      let e = prod.swap e;
      v \<leftarrow> cf_get cf e; cf \<leftarrow> cf_set cf e (v+cap);
      RETURN cf
    }"

    lemma augment_edge_impl_refine: 
      assumes "valid_edge e" "\<forall>u. e\<noteq>(u,u)"
      shows "augment_edge_impl cf e cap 
          \<le> (spec r. r = Graph.augment_edge cf e cap)"
      using assms
      unfolding augment_edge_impl_def Graph.augment_edge_def 
      unfolding cf_get_def cf_set_def
      apply refine_vcg
      apply auto
      done
      
    definition augment_cf_impl 
      :: "'capacity graph \<Rightarrow> path \<Rightarrow> 'capacity \<Rightarrow> 'capacity graph nres" 
      where
      "augment_cf_impl cf p x \<equiv> do {
        (rec\<^sub>T D. \<lambda>
          ([],cf) \<Rightarrow> return cf
        | (e#p,cf) \<Rightarrow> do {
            cf \<leftarrow> augment_edge_impl cf e x;
            D (p,cf)
          }  
        ) (p,cf)
      }"

    text \<open>Deriving the corresponding recursion equations\<close>  
    lemma augment_cf_impl_simps[simp]: 
      "augment_cf_impl cf [] x = return cf"
      "augment_cf_impl cf (e#p) x = do { 
        cf \<leftarrow> augment_edge_impl cf e x; 
        augment_cf_impl cf p x}"
      apply (simp add: augment_cf_impl_def)
      apply (subst RECT_unfold, refine_mono)
      apply simp
      
      apply (simp add: augment_cf_impl_def)
      apply (subst RECT_unfold, refine_mono)
      apply simp
      done      

    lemma augment_cf_impl_aux:    
      assumes "\<forall>e\<in>set p. valid_edge e"
      assumes "\<exists>s. Graph.isSimplePath cf s p t"
      shows "augment_cf_impl cf p x \<le> RETURN (Graph.augment_cf cf (set p) x)"
      using assms
      apply (induction p arbitrary: cf)
      apply (simp add: Graph.augment_cf_empty)

      apply clarsimp
      apply (subst Graph.augment_cf_inductive, assumption)

      apply (refine_vcg augment_edge_impl_refine[THEN order_trans])
      apply simp
      apply simp
      apply (auto dest: Graph.isSPath_no_selfloop) []
      apply (rule order_trans, rprems)
        apply (drule Graph.augment_cf_inductive(2)[where cap=x]; simp)
        apply simp
      done  
      
    lemma (in RGraph) augment_cf_impl_refine:     
      assumes "Graph.isSimplePath cf s p t"
      shows "augment_cf_impl cf p x \<le> RETURN (Graph.augment_cf cf (set p) x)"
      apply (rule augment_cf_impl_aux)
      using assms cf.E_ss_VxV apply (auto simp: cf.isSimplePath_def dest!: cf.isPath_edgeset) []
      using assms by blast
      
    text \<open>Finally, we arrive at the algorithm where augmentation is 
      implemented algorithmically: \<close>  
    definition "edka3 \<equiv> do {
      let cf = c;

      (cf,_) \<leftarrow> while\<^sub>T 
        (\<lambda>(cf,brk). \<not>brk) 
        (\<lambda>(cf,_). do {
          assert (RGraph c s t cf);
          p \<leftarrow> find_shortest_augmenting_spec_cf cf;
          case p of 
            None \<Rightarrow> return (cf,True)
          | Some p \<Rightarrow> do {
              assert (p\<noteq>[]);
              assert (Graph.isShortestPath cf s p t);
              bn \<leftarrow> resCap_cf_impl cf p;
              cf \<leftarrow> augment_cf_impl cf p bn;
              assert (RGraph c s t cf);
              return (cf, False)
            }  
        })
        (cf,False);
      assert (RGraph c s t cf);
      let f = flow_of_cf cf;  
      return f
    }"

    lemma edka3_refine: "edka3 \<le> \<Down>Id edka2"
      unfolding edka3_def edka2_def
      apply (rewrite in "let cf = Graph.augment_cf _ _ _ in _" Let_def)
      apply refine_rcg
      apply refine_dref_type
      apply (vc_solve)
      apply (drule Graph.shortestPath_is_simple)
      apply (frule (1) RGraph.resCap_cf_impl_refine)
      apply (frule (1) RGraph.augment_cf_impl_refine)
      apply (auto simp: pw_le_iff refine_pw_simps)
      done
      
    
    subsection \<open>Refinement to use BFS\<close>

    text \<open>We refine the Edmonds-Karp algorithm to use breadth first search (BFS)\<close>
    definition "edka4 \<equiv> do {
      let cf = c;

      (cf,_) \<leftarrow> while\<^sub>T 
        (\<lambda>(cf,brk). \<not>brk) 
        (\<lambda>(cf,_). do {
          assert (RGraph c s t cf);
          p \<leftarrow> Graph.bfs cf s t;
          case p of 
            None \<Rightarrow> return (cf,True)
          | Some p \<Rightarrow> do {
              assert (p\<noteq>[]);
              assert (Graph.isShortestPath cf s p t);
              bn \<leftarrow> resCap_cf_impl cf p;
              cf \<leftarrow> augment_cf_impl cf p bn;
              assert (RGraph c s t cf);
              return (cf, False)
            }  
        })
        (cf,False);
      assert (RGraph c s t cf);
      let f = flow_of_cf cf;  
      return f
    }"

    text \<open>A shortest path can be obtained by BFS\<close>  
    lemma bfs_refines_shortest_augmenting_spec: 
      "Graph.bfs cf s t \<le> find_shortest_augmenting_spec_cf cf"
      unfolding find_shortest_augmenting_spec_cf_def
      apply (rule le_ASSERTI)
      apply (rule order_trans)
      apply (rule Graph.bfs_correct)
      apply (simp add: RPreGraph.resV_netV[OF RGraph.this_loc_rpg] s_node)
      apply (simp add: RPreGraph.resV_netV[OF RGraph.this_loc_rpg])
      apply (simp)
      done

    lemma edka4_refine: "edka4 \<le> \<Down>Id edka3"
      unfolding edka4_def edka3_def
      apply refine_rcg
      apply refine_dref_type
      apply (vc_solve simp: bfs_refines_shortest_augmenting_spec)
      done


    subsection \<open>Implementing the Successor Function for BFS\<close>  

    text \<open>We implement the successor function in two steps.
      The first step shows how to obtain the successor function by
      filtering the list of adjacent nodes. This step contains the idea   
      of the implementation. The second step is purely technical, and makes 
      explicit the recursion of the filter function as a recursion combinator
      in the monad. This is required for the Sepref tool.
      \<close>

    text \<open>Note: We use @{term filter_rev} here, as it is tail-recursive, 
      and we are not interested in the order of successors.\<close>
    definition "rg_succ am cf u \<equiv>  
      filter_rev (\<lambda>v. cf (u,v) > 0) (am u)"
  
    lemma (in RGraph) rg_succ_ref1: "\<lbrakk>is_adj_map am\<rbrakk> 
      \<Longrightarrow> (rg_succ am cf u, Graph.E cf``{u}) \<in> \<langle>Id\<rangle>list_set_rel"
      unfolding Graph.E_def
      apply (clarsimp simp: list_set_rel_def br_def rg_succ_def filter_rev_alt; 
        intro conjI)
      using cfE_ss_invE resE_nonNegative 
      apply (auto 
        simp: is_adj_map_def less_le Graph.E_def 
        simp del: cf.zero_cap_simp zero_cap_simp) []
      apply (auto simp: is_adj_map_def) []
      done

    definition ps_get_op :: "_ \<Rightarrow> node \<Rightarrow> node list nres" 
      where "ps_get_op am u \<equiv> assert (u\<in>V) \<then> return (am u)"

    definition monadic_filter_rev_aux 
      :: "'a list \<Rightarrow> ('a \<Rightarrow> bool nres) \<Rightarrow> 'a list \<Rightarrow> 'a list nres"
    where
      "monadic_filter_rev_aux a P l \<equiv> (rec\<^sub>T D. (\<lambda>(l,a). case l of
        [] \<Rightarrow> return a 
      | (v#l) \<Rightarrow> do {
          c \<leftarrow> P v;
          let a = (if c then v#a else a);
          D (l,a)
        }
      )) (l,a)"

    lemma monadic_filter_rev_aux_rule:
      assumes "\<And>x. x\<in>set l \<Longrightarrow> P x \<le> SPEC (\<lambda>r. r=Q x)"
      shows "monadic_filter_rev_aux a P l \<le> SPEC (\<lambda>r. r=filter_rev_aux a Q l)"
      using assms
      apply (induction l arbitrary: a)

      apply (unfold monadic_filter_rev_aux_def) []
      apply (subst RECT_unfold, refine_mono)
      apply (fold monadic_filter_rev_aux_def) []
      apply simp

      apply (unfold monadic_filter_rev_aux_def) []
      apply (subst RECT_unfold, refine_mono)
      apply (fold monadic_filter_rev_aux_def) []
      apply (auto simp: pw_le_iff refine_pw_simps)
      done

    definition "monadic_filter_rev = monadic_filter_rev_aux []"

    lemma monadic_filter_rev_rule:
      assumes "\<And>x. x\<in>set l \<Longrightarrow> P x \<le> (spec r. r=Q x)"
      shows "monadic_filter_rev P l \<le> (spec r. r=filter_rev Q l)"
      using monadic_filter_rev_aux_rule[where a="[]"] assms
      by (auto simp: monadic_filter_rev_def filter_rev_def)

    definition "rg_succ2 am cf u \<equiv> do {
      l \<leftarrow> ps_get_op am u;
      monadic_filter_rev (\<lambda>v. do {
        x \<leftarrow> cf_get cf (u,v);
        return (x>0)
      }) l
    }"

    lemma (in RGraph) rg_succ_ref2: 
      assumes PS: "is_adj_map am" and V: "u\<in>V"
      shows "rg_succ2 am cf u \<le> return (rg_succ am cf u)"
    proof -
      have "\<forall>v\<in>set (am u). valid_edge (u,v)"
        using PS V
        by (auto simp: is_adj_map_def Graph.V_def)
      
      thus ?thesis  
        unfolding rg_succ2_def rg_succ_def ps_get_op_def cf_get_def
        apply (refine_vcg monadic_filter_rev_rule[
            where Q="(\<lambda>v. 0 < cf (u, v))", THEN order_trans])
        by (vc_solve simp: V)
    qed    

    lemma (in RGraph) rg_succ_ref:
      assumes A: "is_adj_map am"
      assumes B: "u\<in>V"
      shows "rg_succ2 am cf u \<le> SPEC (\<lambda>l. (l,cf.E``{u}) \<in> \<langle>Id\<rangle>list_set_rel)"
      using rg_succ_ref1[OF A, of u] rg_succ_ref2[OF A B]
      by (auto simp: pw_le_iff refine_pw_simps)


    subsection \<open>Adding Tabulation of Input\<close>  
    text \<open>
      Next, we add functions that will be refined to tabulate the input of 
      the algorithm, i.e., the network's capacity matrix and adjacency map,
      into efficient representations. 
      The capacity matrix is tabulated to give the initial residual graph,
      and the adjacency map is tabulated for faster access.

      Note, on the abstract level, the tabulation functions are just identity,
      and merely serve as marker constants for implementation.
      \<close>
    definition init_cf :: "'capacity graph nres" 
      \<comment> \<open>Initialization of residual graph from network\<close>
      where "init_cf \<equiv> RETURN c"
    definition init_ps :: "(node \<Rightarrow> node list) \<Rightarrow> _" 
      \<comment> \<open>Initialization of adjacency map\<close>
      where "init_ps am \<equiv> ASSERT (is_adj_map am) \<then> RETURN am"

    definition compute_rflow :: "'capacity graph \<Rightarrow> 'capacity flow nres" 
      \<comment> \<open>Extraction of result flow from residual graph\<close>
      where
      "compute_rflow cf \<equiv> ASSERT (RGraph c s t cf) \<then> RETURN (flow_of_cf cf)"

    definition "bfs2_op am cf \<equiv> Graph.bfs2 cf (rg_succ2 am cf) s t"

    text \<open>We split the algorithm into a tabulation function, and the 
      running of the actual algorithm:\<close>
    definition "edka5_tabulate am \<equiv> do {
      cf \<leftarrow> init_cf;
      am \<leftarrow> init_ps am;
      return (cf,am)
    }"

    definition "edka5_run cf am \<equiv> do {
      (cf,_) \<leftarrow> while\<^sub>T 
        (\<lambda>(cf,brk). \<not>brk) 
        (\<lambda>(cf,_). do {
          assert (RGraph c s t cf);
          p \<leftarrow> bfs2_op am cf;
          case p of 
            None \<Rightarrow> return (cf,True)
          | Some p \<Rightarrow> do {
              assert (p\<noteq>[]);
              assert (Graph.isShortestPath cf s p t);
              bn \<leftarrow> resCap_cf_impl cf p;
              cf \<leftarrow> augment_cf_impl cf p bn;
              assert (RGraph c s t cf);
              return (cf, False)
            }  
        })
        (cf,False);
      f \<leftarrow> compute_rflow cf;  
      return f
    }"

    definition "edka5 am \<equiv> do {
      (cf,am) \<leftarrow> edka5_tabulate am;
      edka5_run cf am
    }"

    lemma edka5_refine: "\<lbrakk>is_adj_map am\<rbrakk> \<Longrightarrow> edka5 am \<le> \<Down>Id edka4"
      unfolding edka5_def edka5_tabulate_def edka5_run_def
        edka4_def init_cf_def compute_rflow_def
        init_ps_def Let_def nres_monad_laws bfs2_op_def
      apply refine_rcg
      apply refine_dref_type
      apply (vc_solve simp: )
      apply (rule refine_IdD)
      apply (rule Graph.bfs2_refine)
      apply (simp add: RPreGraph.resV_netV[OF RGraph.this_loc_rpg])
      apply (simp add: RGraph.rg_succ_ref)
      done

  end    

  subsection \<open>Imperative Implementation\<close>  
  text \<open>In this section we provide an efficient imperative implementation,
    using the Sepref tool. It is mostly technical, setting up the mappings
    from abstract to concrete data structures, and then refining the algorithm,
    function by function.  
    \<close>

  text \<open>
    This is also the point where we have to choose the implementation of 
    capacities. Up to here, they have been a polymorphic type with a
    typeclass constraint of being a linearly ordered integral domain.
    Here, we switch to @{typ [source] capacity_impl} (@{typ capacity_impl}).
    \<close>
  locale Network_Impl = Network c s t for c :: "capacity_impl graph" and s t

  text \<open>Moreover, we assume that the nodes are natural numbers less 
    than some number @{term N}, which will become an additional parameter 
    of our algorithm. \<close>
  locale Edka_Impl = Network_Impl +
    fixes N :: nat
    assumes V_ss: "V\<subseteq>{0..<N}"
  begin  
    lemma this_loc: "Edka_Impl c s t N" by unfold_locales

    lemma E_ss: "E \<subseteq> {0..<N}\<times>{0..<N}" using E_ss_VxV V_ss by auto

    lemma mtx_nonzero_iff[simp]: "mtx_nonzero c = E" unfolding E_def by (auto simp: mtx_nonzero_def)

    lemma mtx_nonzeroN: "mtx_nonzero c \<subseteq> {0..<N}\<times>{0..<N}" using E_ss by simp

    lemma [simp]: "v\<in>V \<Longrightarrow> v<N" using V_ss by auto


    text \<open>Declare some variables to Sepref. \<close>
    lemmas [id_rules] = 
      itypeI[Pure.of N "TYPE(nat)"]  
      itypeI[Pure.of s "TYPE(node)"]  
      itypeI[Pure.of t "TYPE(node)"]  
      itypeI[Pure.of c "TYPE(capacity_impl graph)"]  
    text \<open>Instruct Sepref to not refine these parameters. This is expressed
      by using identity as refinement relation.\<close>
    lemmas [sepref_import_param] = 
      IdI[of N]
      IdI[of s]
      IdI[of t]
      (*IdI[of c]*)

    lemma [sepref_fr_rules]: "(uncurry0 (return c),uncurry0 (return c))\<in>unit_assn\<^sup>k \<rightarrow>\<^sub>a pure (nat_rel\<times>\<^sub>rnat_rel \<rightarrow> int_rel)"
      apply sepref_to_hoare by sep_auto


    subsubsection \<open>Implementation of Adjacency Map by Array\<close>  
    definition "is_am am psi 
      \<equiv> \<exists>\<^sub>Al. psi \<mapsto>\<^sub>a l 
          * \<up>(length l = N \<and> (\<forall>i<N. l!i = am i) 
              \<and> (\<forall>i\<ge>N. am i = []))"
  
    lemma is_am_precise[safe_constraint_rules]: "precise (is_am)"
      apply rule
      unfolding is_am_def
      apply clarsimp
      apply (rename_tac l l')
      apply prec_extract_eqs
      apply (rule ext)
      apply (rename_tac i)
      apply (case_tac "i<length l'")
      apply fastforce+
      done

    sepref_decl_intf i_ps is "nat \<Rightarrow> nat list" 

    definition (in -) "ps_get_imp psi u \<equiv> Array.nth psi u"

    lemma [def_pat_rules]: "Network.ps_get_op$c \<equiv> UNPROTECT ps_get_op" by simp
    sepref_register "PR_CONST ps_get_op" :: "i_ps \<Rightarrow> node \<Rightarrow> node list nres"

    lemma ps_get_op_refine[sepref_fr_rules]: 
      "(uncurry ps_get_imp, uncurry (PR_CONST ps_get_op)) 
        \<in> is_am\<^sup>k *\<^sub>a (pure Id)\<^sup>k \<rightarrow>\<^sub>a list_assn (pure Id)"
      unfolding list_assn_pure_conv
      apply sepref_to_hoare
      using V_ss
      by (sep_auto 
            simp: is_am_def pure_def ps_get_imp_def 
            simp: ps_get_op_def refine_pw_simps)

    lemma is_pred_succ_no_node: "\<lbrakk>is_adj_map a; u\<notin>V\<rbrakk> \<Longrightarrow> a u = []"
      unfolding is_adj_map_def V_def
      by auto

    lemma [sepref_fr_rules]: "(Array.make N, PR_CONST init_ps) 
      \<in> (pure Id)\<^sup>k \<rightarrow>\<^sub>a is_am" 
      apply sepref_to_hoare
      using V_ss
      by (sep_auto simp: init_ps_def refine_pw_simps is_am_def pure_def
        intro: is_pred_succ_no_node)

    lemma [def_pat_rules]: "Network.init_ps$c \<equiv> UNPROTECT init_ps" by simp
    sepref_register "PR_CONST init_ps" :: "(node \<Rightarrow> node list) \<Rightarrow> i_ps nres"

    subsubsection \<open>Implementation of Capacity Matrix by Array\<close>  
    lemma [def_pat_rules]: "Network.cf_get$c \<equiv> UNPROTECT cf_get" by simp
    lemma [def_pat_rules]: "Network.cf_set$c \<equiv> UNPROTECT cf_set" by simp

    sepref_register 
      "PR_CONST cf_get" :: "capacity_impl i_mtx \<Rightarrow> edge \<Rightarrow> capacity_impl nres"
    sepref_register 
      "PR_CONST cf_set" :: "capacity_impl i_mtx \<Rightarrow> edge \<Rightarrow> capacity_impl 
        \<Rightarrow> capacity_impl i_mtx nres"

    text \<open>We have to link the matrix implementation, which encodes the bound, 
      to the abstract assertion of the bound\<close>

    sepref_definition cf_get_impl is "uncurry (PR_CONST cf_get)" :: "(asmtx_assn N id_assn)\<^sup>k *\<^sub>a (prod_assn id_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a id_assn"
      unfolding PR_CONST_def cf_get_def[abs_def]
      by sepref
    lemmas [sepref_fr_rules] = cf_get_impl.refine
    lemmas [sepref_opt_simps] = cf_get_impl_def

    sepref_definition cf_set_impl is "uncurry2 (PR_CONST cf_set)" :: "(asmtx_assn N id_assn)\<^sup>d *\<^sub>a (prod_assn id_assn id_assn)\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a asmtx_assn N id_assn"
      unfolding PR_CONST_def cf_set_def[abs_def]
      by sepref
    lemmas [sepref_fr_rules] = cf_set_impl.refine
    lemmas [sepref_opt_simps] = cf_set_impl_def


    sepref_thm init_cf_impl is "uncurry0 (PR_CONST init_cf)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a asmtx_assn N id_assn"
      unfolding PR_CONST_def init_cf_def 
      using E_ss
      apply (rewrite op_mtx_new_def[of c, symmetric])
      apply (rewrite amtx_fold_custom_new[of N N])
      by sepref

    concrete_definition (in -) init_cf_impl uses Edka_Impl.init_cf_impl.refine_raw is "(uncurry0 ?f,_)\<in>_" 
    prepare_code_thms (in -) init_cf_impl_def
    lemmas [sepref_fr_rules] = init_cf_impl.refine[OF this_loc]  

    (* TODO: Use sepref to synthesize the get-operations! *)
    lemma amtx_cnv: "amtx_assn N M id_assn = IICF_Array_Matrix.is_amtx N M" 
      by (simp add: amtx_assn_def)

    (*

    lemma init_cf_imp_refine[sepref_fr_rules]: 
      "(uncurry0 (mtx_new N c), uncurry0 (PR_CONST init_cf)) 
        \<in> (pure unit_rel)\<^sup>k \<rightarrow>\<^sub>a (asmtx_assn N id_assn)"
      unfolding asmtx_cnv
      apply sepref_to_hoare
      using E_ss
      by (sep_auto simp: init_cf_def)
    *)  

    lemma [def_pat_rules]: "Network.init_cf$c \<equiv> UNPROTECT init_cf" by simp
    sepref_register "PR_CONST init_cf" :: "capacity_impl i_mtx nres"

    subsubsection \<open>Representing Result Flow as Residual Graph\<close>
    definition (in Network_Impl) "is_rflow N f cfi 
      \<equiv> \<exists>\<^sub>Acf. asmtx_assn N id_assn cf cfi * \<up>(RGraph c s t cf \<and> f = flow_of_cf cf)"
    lemma is_rflow_precise[safe_constraint_rules]: "precise (is_rflow N)"
      apply rule
      unfolding is_rflow_def
      apply (clarsimp simp: amtx_assn_def)
      apply prec_extract_eqs
      apply simp
      done

    sepref_decl_intf i_rflow is "nat\<times>nat \<Rightarrow> int"

    lemma [sepref_fr_rules]: 
      "(\<lambda>cfi. return cfi, PR_CONST compute_rflow) \<in> (asmtx_assn N id_assn)\<^sup>d \<rightarrow>\<^sub>a is_rflow N"
      unfolding amtx_cnv
      apply sepref_to_hoare
      apply (sep_auto simp: amtx_cnv compute_rflow_def is_rflow_def refine_pw_simps hn_ctxt_def)
      done

    lemma [def_pat_rules]: 
      "Network.compute_rflow$c$s$t \<equiv> UNPROTECT compute_rflow" by simp
    sepref_register 
      "PR_CONST compute_rflow" :: "capacity_impl i_mtx \<Rightarrow> i_rflow nres"


    subsubsection \<open>Implementation of Functions\<close>  

    schematic_goal rg_succ2_impl:
      fixes am :: "node \<Rightarrow> node list" and cf :: "capacity_impl graph"
      notes [id_rules] = 
        itypeI[Pure.of u "TYPE(node)"]
        itypeI[Pure.of am "TYPE(i_ps)"]
        itypeI[Pure.of cf "TYPE(capacity_impl i_mtx)"]
      notes [sepref_import_param] = IdI[of N]
      notes [sepref_fr_rules] = HOL_list_empty_hnr
      shows "hn_refine (hn_ctxt is_am am psi * hn_ctxt (asmtx_assn N id_assn) cf cfi * hn_val nat_rel u ui) (?c::?'c Heap) ?\<Gamma> ?R (rg_succ2 am cf u)"
      unfolding rg_succ2_def APP_def monadic_filter_rev_def monadic_filter_rev_aux_def
      (* TODO: Make setting up combinators for sepref simpler, then we do not need to unfold! *)
      using [[id_debug, goals_limit = 1]]
      by sepref
    concrete_definition (in -) succ_imp uses Edka_Impl.rg_succ2_impl
    prepare_code_thms (in -) succ_imp_def

    lemma succ_imp_refine[sepref_fr_rules]: 
      "(uncurry2 (succ_imp N), uncurry2 (PR_CONST rg_succ2)) 
        \<in> is_am\<^sup>k *\<^sub>a (asmtx_assn N id_assn)\<^sup>k *\<^sub>a (pure Id)\<^sup>k \<rightarrow>\<^sub>a list_assn (pure Id)"
      apply rule
      using succ_imp.refine[OF this_loc]            
      by (auto simp: hn_ctxt_def mult_ac split: prod.split)

    lemma [def_pat_rules]: "Network.rg_succ2$c \<equiv> UNPROTECT rg_succ2" by simp
    sepref_register 
      "PR_CONST rg_succ2" :: "i_ps \<Rightarrow> capacity_impl i_mtx \<Rightarrow> node \<Rightarrow> node list nres"

    
    lemma [sepref_import_param]: "(min,min)\<in>Id\<rightarrow>Id\<rightarrow>Id" by simp


    abbreviation "is_path \<equiv> list_assn (prod_assn (pure Id) (pure Id))"

    schematic_goal resCap_imp_impl:
      fixes am :: "node \<Rightarrow> node list" and cf :: "capacity_impl graph" and p pi
      notes [id_rules] = 
        itypeI[Pure.of p "TYPE(edge list)"]
        itypeI[Pure.of cf "TYPE(capacity_impl i_mtx)"]
      notes [sepref_import_param] = IdI[of N]
      shows "hn_refine 
        (hn_ctxt (asmtx_assn N id_assn) cf cfi * hn_ctxt is_path p pi) 
        (?c::?'c Heap) ?\<Gamma> ?R 
        (resCap_cf_impl cf p)"
      unfolding resCap_cf_impl_def APP_def
      using [[id_debug, goals_limit = 1]]
      by sepref
    concrete_definition (in -) resCap_imp uses Edka_Impl.resCap_imp_impl
    prepare_code_thms (in -) resCap_imp_def

    lemma resCap_impl_refine[sepref_fr_rules]: 
      "(uncurry (resCap_imp N), uncurry (PR_CONST resCap_cf_impl)) 
        \<in> (asmtx_assn N id_assn)\<^sup>k *\<^sub>a (is_path)\<^sup>k \<rightarrow>\<^sub>a (pure Id)"
      apply sepref_to_hnr
      apply (rule hn_refine_preI)
      apply (clarsimp 
        simp: uncurry_def list_assn_pure_conv hn_ctxt_def 
        split: prod.split)
      apply (clarsimp simp: pure_def)
      apply (rule hn_refine_cons[OF _ resCap_imp.refine[OF this_loc] _])
      apply (simp add: list_assn_pure_conv hn_ctxt_def)
      apply (simp add: pure_def)
      apply (sep_auto simp add: hn_ctxt_def pure_def intro!: enttI)
      apply (simp add: pure_def)
      done

    lemma [def_pat_rules]: 
      "Network.resCap_cf_impl$c \<equiv> UNPROTECT resCap_cf_impl" 
      by simp
    sepref_register "PR_CONST resCap_cf_impl" 
      :: "capacity_impl i_mtx \<Rightarrow> path \<Rightarrow> capacity_impl nres"
    
    sepref_thm augment_imp is "uncurry2 (PR_CONST augment_cf_impl)" :: "((asmtx_assn N id_assn)\<^sup>d *\<^sub>a (is_path)\<^sup>k *\<^sub>a (pure Id)\<^sup>k \<rightarrow>\<^sub>a asmtx_assn N id_assn)"
      unfolding augment_cf_impl_def[abs_def] augment_edge_impl_def PR_CONST_def
      using [[id_debug, goals_limit = 1]]
      by sepref 
    concrete_definition (in -) augment_imp uses Edka_Impl.augment_imp.refine_raw is "(uncurry2 ?f,_)\<in>_"
    prepare_code_thms (in -) augment_imp_def
    lemma augment_impl_refine[sepref_fr_rules]: 
      "(uncurry2 (augment_imp N), uncurry2 (PR_CONST augment_cf_impl)) 
        \<in> (asmtx_assn N id_assn)\<^sup>d *\<^sub>a (is_path)\<^sup>k *\<^sub>a (pure Id)\<^sup>k \<rightarrow>\<^sub>a asmtx_assn N id_assn"
      using augment_imp.refine[OF this_loc] .

    lemma [def_pat_rules]: 
      "Network.augment_cf_impl$c \<equiv> UNPROTECT augment_cf_impl" 
      by simp
    sepref_register "PR_CONST augment_cf_impl" 
      :: "capacity_impl i_mtx \<Rightarrow> path \<Rightarrow> capacity_impl \<Rightarrow> capacity_impl i_mtx nres"

    sublocale bfs: Impl_Succ 
      "snd" 
      "TYPE(i_ps \<times> capacity_impl i_mtx)" 
      "PR_CONST (\<lambda>(am,cf). rg_succ2 am cf)" 
      "prod_assn is_am (asmtx_assn N id_assn)" 
      "\<lambda>(am,cf). succ_imp N am cf"
      unfolding APP_def
      apply unfold_locales
      apply (simp add: fold_partial_uncurry)
      apply (rule hfref_cons[OF succ_imp_refine[unfolded PR_CONST_def]])
      by auto
      
    definition (in -) "bfsi' N s t psi cfi 
      \<equiv> bfs_impl (\<lambda>(am, cf). succ_imp N am cf) (psi,cfi) s t"

    lemma [sepref_fr_rules]: 
      "(uncurry (bfsi' N s t),uncurry (PR_CONST bfs2_op)) 
        \<in> is_am\<^sup>k *\<^sub>a (asmtx_assn N id_assn)\<^sup>k \<rightarrow>\<^sub>a option_assn is_path"
      unfolding bfsi'_def[abs_def] bfs2_op_def[abs_def] 
      using bfs.bfs_impl_fr_rule unfolding bfs.op_bfs_def[abs_def]
      apply (clarsimp simp: hfref_def all_to_meta)
      apply (rule hn_refine_cons[rotated])
      apply rprems
      apply (sep_auto simp: pure_def intro!: enttI)
      apply (sep_auto simp: pure_def)
      apply (sep_auto simp: pure_def)
      done

    lemma [def_pat_rules]: "Network.bfs2_op$c$s$t \<equiv> UNPROTECT bfs2_op" by simp
    sepref_register "PR_CONST bfs2_op" 
      :: "i_ps \<Rightarrow> capacity_impl i_mtx \<Rightarrow> path option nres"  


    schematic_goal edka_imp_tabulate_impl:
      notes [sepref_opt_simps] = heap_WHILET_def
      fixes am :: "node \<Rightarrow> node list" and cf :: "capacity_impl graph"
      notes [id_rules] = 
        itypeI[Pure.of am "TYPE(node \<Rightarrow> node list)"]
      notes [sepref_import_param] = IdI[of am]
      shows "hn_refine (emp) (?c::?'c Heap) ?\<Gamma> ?R (edka5_tabulate am)"
      unfolding edka5_tabulate_def
      using [[id_debug, goals_limit = 1]]
      by sepref

    concrete_definition (in -) edka_imp_tabulate 
      uses Edka_Impl.edka_imp_tabulate_impl
    prepare_code_thms (in -) edka_imp_tabulate_def

    lemma edka_imp_tabulate_refine[sepref_fr_rules]: 
      "(edka_imp_tabulate c N, PR_CONST edka5_tabulate) 
      \<in> (pure Id)\<^sup>k \<rightarrow>\<^sub>a prod_assn (asmtx_assn N id_assn) is_am"
      apply (rule)
      apply (rule hn_refine_preI)
      apply (clarsimp 
        simp: uncurry_def list_assn_pure_conv hn_ctxt_def 
        split: prod.split)
      apply (rule hn_refine_cons[OF _ edka_imp_tabulate.refine[OF this_loc]])
      apply (sep_auto simp: hn_ctxt_def pure_def)+
      done

    lemma [def_pat_rules]: 
      "Network.edka5_tabulate$c \<equiv> UNPROTECT edka5_tabulate" 
      by simp
    sepref_register "PR_CONST edka5_tabulate"
      :: "(node \<Rightarrow> node list) \<Rightarrow> (capacity_impl i_mtx \<times> i_ps) nres"


    schematic_goal edka_imp_run_impl:
      notes [sepref_opt_simps] = heap_WHILET_def
      fixes am :: "node \<Rightarrow> node list" and cf :: "capacity_impl graph"
      notes [id_rules] = 
        itypeI[Pure.of cf "TYPE(capacity_impl i_mtx)"]
        itypeI[Pure.of am "TYPE(i_ps)"]
      shows "hn_refine 
        (hn_ctxt (asmtx_assn N id_assn) cf cfi * hn_ctxt is_am am psi) 
        (?c::?'c Heap) ?\<Gamma> ?R  
        (edka5_run cf am)"
      unfolding edka5_run_def
      using [[id_debug, goals_limit = 1]]
      by sepref

    concrete_definition (in -) edka_imp_run uses Edka_Impl.edka_imp_run_impl
    prepare_code_thms (in -) edka_imp_run_def

    thm edka_imp_run_def
    lemma edka_imp_run_refine[sepref_fr_rules]: 
      "(uncurry (edka_imp_run s t N), uncurry (PR_CONST edka5_run)) 
        \<in> (asmtx_assn N id_assn)\<^sup>d *\<^sub>a (is_am)\<^sup>k \<rightarrow>\<^sub>a is_rflow N"
      apply rule
      apply (clarsimp 
        simp: uncurry_def list_assn_pure_conv hn_ctxt_def 
        split: prod.split)
      apply (rule hn_refine_cons[OF _ edka_imp_run.refine[OF this_loc] _])
      apply (sep_auto simp: hn_ctxt_def)+
      done

    lemma [def_pat_rules]: 
      "Network.edka5_run$c$s$t \<equiv> UNPROTECT edka5_run" 
      by simp
    sepref_register "PR_CONST edka5_run" 
      :: "capacity_impl i_mtx \<Rightarrow> i_ps \<Rightarrow> i_rflow nres"


    schematic_goal edka_imp_impl:
      notes [sepref_opt_simps] = heap_WHILET_def
      fixes am :: "node \<Rightarrow> node list" and cf :: "capacity_impl graph"
      notes [id_rules] = 
        itypeI[Pure.of am "TYPE(node \<Rightarrow> node list)"]
      notes [sepref_import_param] = IdI[of am]
      shows "hn_refine (emp) (?c::?'c Heap) ?\<Gamma> ?R (edka5 am)"
      unfolding edka5_def
      using [[id_debug, goals_limit = 1]]
      by sepref

    concrete_definition (in -) edka_imp uses Edka_Impl.edka_imp_impl
    prepare_code_thms (in -) edka_imp_def
    lemmas edka_imp_refine = edka_imp.refine[OF this_loc]

    thm pat_rules TrueI def_pat_rules
    

  end

  export_code edka_imp checking SML_imp

  subsection \<open>Correctness Theorem for Implementation\<close>
  text \<open>We combine all refinement steps to derive a correctness 
    theorem for the implementation\<close>
  context Network_Impl begin
    theorem edka_imp_correct: 
      assumes VN: "Graph.V c \<subseteq> {0..<N}"
      assumes ABS_PS: "is_adj_map am"
      shows "
        <emp> 
          edka_imp c s t N am 
        <\<lambda>fi. \<exists>\<^sub>Af. is_rflow N f fi * \<up>(isMaxFlow f)>\<^sub>t"
    proof -
      interpret Edka_Impl by unfold_locales fact

      note edka5_refine[OF ABS_PS]
      also note edka4_refine                 
      also note edka3_refine    
      also note edka2_refine 
      also note edka_refine
      also note edka_partial_refine
      also note fofu_partial_correct
      finally have "edka5 am \<le> SPEC isMaxFlow" .
      from hn_refine_ref[OF this edka_imp_refine]
      show ?thesis 
        by (simp add: hn_refine_def)
    qed
  end    
end
