section "Kruskal Implementation"

theory Kruskal_Impl
imports Kruskal_Refine Refine_Imperative_HOL.IICF
begin

subsection \<open>Refinement III: concrete edges\<close>

text \<open>Given a concrete representation of edges and their endpoints as a pair, we refine
  Kruskal's algorithm to work on these concrete edges.\<close>

locale Kruskal_concrete = Kruskal_interface E V vertices  joins  forest connected  weight
  for E V vertices joins forest connected  and weight :: "'edge \<Rightarrow> int"  +
  fixes
    \<alpha> :: "'cedge \<Rightarrow> 'edge"
    and endpoints :: "'cedge \<Rightarrow> ('a*'a) nres"
  assumes  
    endpoints_refine: "\<alpha> xi = x \<Longrightarrow> endpoints xi \<le> \<Down> Id (a_endpoints x)"
begin

definition wsorted' where "wsorted' == sorted_wrt (\<lambda>x y. weight (\<alpha> x) \<le> weight (\<alpha> y))"

lemma wsorted_map\<alpha>[simp]: "wsorted' s \<Longrightarrow> wsorted (map \<alpha> s)"
  by(auto simp: wsorted'_def sorted_wrt_map) 

definition "obtain_sorted_carrier' == SPEC (\<lambda>L. wsorted' L \<and> \<alpha> ` set L = E)"

abbreviation concrete_edge_rel :: "('cedge  \<times> 'edge) set" where
  "concrete_edge_rel \<equiv> br \<alpha> (\<lambda>_. True)"

lemma obtain_sorted_carrier'_refine:
  "(obtain_sorted_carrier', obtain_sorted_carrier) \<in> \<langle>\<langle>concrete_edge_rel\<rangle>list_rel\<rangle>nres_rel"
  unfolding obtain_sorted_carrier'_def obtain_sorted_carrier_def 
  apply refine_vcg
  apply (auto intro!: RES_refine simp:     )
  subgoal for s apply(rule exI[where x="map \<alpha> s"])
    by(auto simp: map_in_list_rel_conv in_br_conv)  
  done

definition kruskal2
  where "kruskal2 \<equiv> do {
    l \<leftarrow> obtain_sorted_carrier';
    let initial_union_find = per_init V;
    (per, spanning_forest) \<leftarrow> nfoldli l (\<lambda>_. True)
        (\<lambda>ce (uf, T). do { 
            ASSERT (\<alpha> ce \<in> E);
            (a,b) \<leftarrow> endpoints ce;
            ASSERT (a\<in>V \<and> b\<in>V \<and> a \<in> Domain uf \<and> b \<in> Domain uf );
            if \<not> per_compare uf a b then
              do { 
                let uf = per_union uf a b;
                ASSERT (ce \<notin> set T);
                RETURN (uf, T@[ce])
              }
            else 
              RETURN (uf,T)
        }) (initial_union_find, []);
        RETURN spanning_forest
      }"

lemma lst_graph_rel_empty[simp]: "([], {}) \<in> \<langle>concrete_edge_rel\<rangle>list_set_rel"
  unfolding list_set_rel_def apply(rule relcompI[where b="[]"])
  by (auto simp add: in_br_conv)

lemma loop_initial_rel:
  "((per_init V, []), per_init V, {}) \<in> Id \<times>\<^sub>r \<langle>concrete_edge_rel\<rangle>list_set_rel"
  by simp

lemma concrete_edge_rel_list_set_rel:
  "(a, b) \<in> \<langle>concrete_edge_rel\<rangle>list_set_rel \<Longrightarrow> \<alpha> ` (set a) = b"  
  by (auto simp: in_br_conv list_set_rel_def dest: list_relD2)

theorem kruskal2_refine: "(kruskal2, kruskal1)\<in>\<langle>\<langle>concrete_edge_rel\<rangle>list_set_rel\<rangle>nres_rel"
  unfolding kruskal1_def kruskal2_def Let_def 
  apply (refine_rcg obtain_sorted_carrier'_refine[THEN nres_relD]
                    endpoints_refine loop_initial_rel)     
  by (auto intro!: list_set_rel_append
            dest: concrete_edge_rel_list_set_rel
            simp: in_br_conv)

end

subsection \<open>Refinement to Imperative/HOL with Sepref-Tool\<close>

text \<open>Given implementations for the operations of getting a list of concrete edges 
  and getting the endpoints of a concrete edge we synthesize Kruskal in Imperative/HOL.\<close>

locale Kruskal_Impl = Kruskal_concrete E V vertices joins forest connected weight \<alpha> endpoints                       
  for E V vertices joins forest connected and weight :: "'edge \<Rightarrow> int"
    and \<alpha> and endpoints :: "nat \<times> int \<times> nat \<Rightarrow> (nat \<times> nat) nres"
    +
  fixes getEdges  :: "(nat \<times> int \<times> nat) list nres"
    and getEdges_impl :: "(nat \<times> int \<times> nat) list Heap"         
    and superE :: "(nat \<times> int \<times> nat) set"         
    and endpoints_impl :: "(nat \<times> int \<times> nat) \<Rightarrow> (nat \<times> nat) Heap"                    
  assumes 
    getEdges_refine: "getEdges \<le> SPEC (\<lambda>L. \<alpha> ` set L = E 
                            \<and> (\<forall>(a,wv,b)\<in>set L.  weight (\<alpha> (a,wv,b)) = wv) \<and> set L \<subseteq> superE)"
    and
    getEdges_impl: "(uncurry0 getEdges_impl, uncurry0 getEdges)
                     \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
    and 
    max_node_is_Max_V: "E = \<alpha> ` set la \<Longrightarrow> max_node la = Max (insert 0 V)"
    and
    endpoints_impl: "( endpoints_impl,  endpoints) 
                      \<in> (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)\<^sup>k \<rightarrow>\<^sub>a (nat_assn \<times>\<^sub>a nat_assn)"
begin
  
  lemma this_loc: "Kruskal_Impl E V vertices  joins  forest connected  weight
            \<alpha> endpoints getEdges getEdges_impl superE    endpoints_impl" by unfold_locales
  
  
  subsubsection \<open>Refinement IV: given an edge set\<close>

  text \<open>We now assume to have an implementation of the operation to obtain a list of the edges of
    a graph. By sorting this list we refine @{term obtain_sorted_carrier'}.\<close>

  definition "obtain_sorted_carrier'' = do {
      l \<leftarrow> SPEC (\<lambda>L.  \<alpha> ` set L = E 
                              \<and> (\<forall>(a,wv,b)\<in>set L.  weight (\<alpha> (a,wv,b)) = wv) \<and> set L \<subseteq> superE);
      SPEC (\<lambda>L. sorted_wrt edges_less_eq L \<and> set L = set l)
  }"
  
  lemma wsorted'_sorted_wrt_edges_less_eq:
    assumes "\<forall>(a,wv,b)\<in>set s.  weight (\<alpha> (a,wv,b)) = wv"
        "sorted_wrt edges_less_eq s"
    shows "wsorted' s"
    using assms apply -
    unfolding wsorted'_def   unfolding edges_less_eq_def
    apply(rule sorted_wrt_mono_rel )    
    by (auto simp: case_prod_beta)
  
  lemma obtain_sorted_carrier''_refine:
    "(obtain_sorted_carrier'', obtain_sorted_carrier') \<in> \<langle>Id\<rangle>nres_rel"
    unfolding obtain_sorted_carrier''_def obtain_sorted_carrier'_def
    apply refine_vcg
     apply(auto simp: in_br_conv   wsorted'_sorted_wrt_edges_less_eq
        distinct_map map_in_list_rel_conv)  
    done

  definition "obtain_sorted_carrier''' =
        do {
      l \<leftarrow> getEdges; 
      RETURN (quicksort_by_rel edges_less_eq [] l, max_node l)
  }" 
    
  definition "add_size_rel   = br fst (\<lambda>(l,n). n= Max (insert 0 V))"    
  
  lemma obtain_sorted_carrier'''_refine:
    "(obtain_sorted_carrier''', obtain_sorted_carrier'') \<in> \<langle>add_size_rel\<rangle>nres_rel"
    unfolding obtain_sorted_carrier'''_def obtain_sorted_carrier''_def
    apply (refine_rcg getEdges_refine) 
    by (auto intro!: RETURN_SPEC_refine simp: quicksort_by_rel_distinct sort_edges_correct
        add_size_rel_def in_br_conv  max_node_is_Max_V
        dest!: distinct_mapI)

  lemmas osc_refine =  obtain_sorted_carrier'''_refine[FCOMP obtain_sorted_carrier''_refine,
                                                        to_foparam, simplified]

  definition kruskal3 :: "(nat \<times> int \<times> nat) list nres"
    where "kruskal3  \<equiv> do {
      (sl,mn) \<leftarrow> obtain_sorted_carrier''';
      let initial_union_find = per_init' (mn + 1);
      (per, spanning_forest) \<leftarrow> nfoldli sl (\<lambda>_. True)
          (\<lambda>ce (uf, T). do { 
              ASSERT (\<alpha> ce \<in> E);
              (a,b) \<leftarrow> endpoints ce;
              ASSERT (a \<in> Domain uf \<and> b \<in> Domain uf);
              if \<not> per_compare uf a b then
                do { 
                  let uf = per_union uf a b;
                  ASSERT (ce\<notin>set T);
                  RETURN (uf, T@[ce])
                }
              else 
                RETURN (uf,T)
          }) (initial_union_find, []);
          RETURN spanning_forest
        }"
 
  lemma endpoints_spec: "endpoints ce \<le> SPEC (\<lambda>_. True)"
    by(rule order.trans[OF endpoints_refine], auto)    

  lemma  kruskal3_subset:
    shows "kruskal3 \<le>\<^sub>n SPEC (\<lambda>T. distinct T \<and> set T \<subseteq> superE )" 
    unfolding kruskal3_def obtain_sorted_carrier'''_def
    apply (refine_vcg getEdges_refine[THEN leof_lift] endpoints_spec[THEN leof_lift]
        nfoldli_leof_rule[where I="\<lambda>_ _ (_, T). distinct T \<and>  set T \<subseteq> superE "])
             apply auto 
    subgoal   
      by (metis append_self_conv in_set_conv_decomp set_quicksort_by_rel subset_iff)  
    subgoal  
      by blast  
    done


  definition per_supset_rel :: "('a per \<times> 'a per) set" where
    "per_supset_rel
      \<equiv> {(p1,p2). p1 \<inter> Domain p2 \<times> Domain p2 = p2 \<and> p1 - (Domain p2 \<times> Domain p2) \<subseteq> Id}"

  lemma per_supset_rel_dom: "(p1, p2) \<in> per_supset_rel \<Longrightarrow> Domain p1 \<supseteq> Domain p2"
    by (auto simp: per_supset_rel_def)
  
  lemma per_supset_compare:
    "(p1, p2) \<in> per_supset_rel \<Longrightarrow> x1\<in>Domain p2 \<Longrightarrow> x2\<in>Domain p2
       \<Longrightarrow> per_compare p1 x1 x2 \<longleftrightarrow> per_compare p2 x1 x2"
    by (auto simp: per_supset_rel_def)
  
  lemma per_supset_union: "(p1, p2) \<in> per_supset_rel \<Longrightarrow> x1\<in>Domain p2 \<Longrightarrow> x2\<in>Domain p2 \<Longrightarrow>
    (per_union p1 x1 x2, per_union p2 x1 x2) \<in> per_supset_rel"
    apply (clarsimp simp: per_supset_rel_def per_union_def Domain_unfold )
    apply (intro subsetI conjI)
     apply blast
    apply force
    done

  lemma per_initN_refine: "(per_init' (Max (insert 0 V) + 1), per_init V) \<in> per_supset_rel"
    unfolding per_supset_rel_def per_init'_def per_init_def max_node_def
    by (auto simp: less_Suc_eq_le  ) 

  theorem kruskal3_refine: "(kruskal3, kruskal2)\<in>\<langle>Id\<rangle>nres_rel"
    unfolding kruskal2_def kruskal3_def Let_def
    apply (refine_rcg osc_refine[THEN nres_relD]   )
               supply RELATESI[where R="per_supset_rel::(nat per \<times> _) set", refine_dref_RELATES]
               apply refine_dref_type 
    subgoal by (simp add: add_size_rel_def in_br_conv)
    subgoal using per_initN_refine by (simp add: add_size_rel_def in_br_conv)
    by (auto simp add: add_size_rel_def in_br_conv per_supset_compare per_supset_union
        dest: per_supset_rel_dom
        simp del: per_compare_def ) 


  subsubsection \<open>Synthesis of Kruskal by SepRef\<close>


  lemma [sepref_import_param]: "(sort_edges,sort_edges)\<in>\<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow>\<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel"
    by simp
  lemma [sepref_import_param]: "(max_node, max_node) \<in> \<langle>Id\<times>\<^sub>rId\<times>\<^sub>rId\<rangle>list_rel \<rightarrow> nat_rel" by simp

  sepref_register "getEdges" :: "(nat \<times> int \<times> nat) list nres"
  sepref_register "endpoints" :: "(nat \<times> int \<times> nat) \<Rightarrow> (nat*nat) nres"
 
 
  declare getEdges_impl [sepref_fr_rules]
  declare endpoints_impl [sepref_fr_rules]
  
  schematic_goal kruskal_impl:
    "(uncurry0 ?c, uncurry0 kruskal3 ) \<in> (unit_assn)\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
    unfolding kruskal3_def obtain_sorted_carrier'''_def 
    unfolding sort_edges_def[symmetric]
    apply (rewrite at "nfoldli _ _ _ (_,rewrite_HOLE)" HOL_list.fold_custom_empty)
    by sepref 

  concrete_definition (in -) kruskal uses Kruskal_Impl.kruskal_impl
  prepare_code_thms (in -) kruskal_def
  lemmas kruskal_refine = kruskal.refine[OF this_loc]

  
  
  abbreviation "MSF == minBasis"   
  abbreviation "SpanningForest == basis"
  lemmas SpanningForest_def = basis_def
  lemmas MSF_def = minBasis_def 
  
  lemmas kruskal3_ref_spec_ = kruskal3_refine[FCOMP kruskal2_refine, FCOMP kruskal1_refine,
      FCOMP kruskal0_refine,
      FCOMP minWeightBasis_refine] 
  
  lemma kruskal3_ref_spec':
    "(uncurry0 kruskal3, uncurry0 (SPEC (\<lambda>r. MSF (\<alpha> ` set r)))) \<in> unit_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel" 
    unfolding fref_def 
    apply auto
    apply(rule nres_relI) 
    apply(rule order.trans[OF  kruskal3_ref_spec_[unfolded fref_def, simplified,  THEN nres_relD]])
    by (auto simp: conc_fun_def list_set_rel_def in_br_conv dest!: list_relD2) 
  
  lemma kruskal3_ref_spec:
   "(uncurry0 kruskal3,
      uncurry0 (SPEC (\<lambda>r. distinct r \<and> set r \<subseteq> superE \<and>  MSF (\<alpha> ` set r))))
      \<in> unit_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel"
    unfolding fref_def 
    apply auto
    apply(rule nres_relI) 
    apply simp
    using SPEC_rule_conj_leofI2[OF kruskal3_subset kruskal3_ref_spec'
              [unfolded fref_def, simplified,  THEN nres_relD, simplified]]
    by simp
  
  lemma [fcomp_norm_simps]: "list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn) = id_assn"
    by (auto simp: list_assn_pure_conv)
  
  lemmas kruskal_ref_spec = kruskal_refine[FCOMP kruskal3_ref_spec]
  

  text \<open>The final correctness lemma for Kruskal's algorithm. \<close>

  lemma kruskal_correct_forest:
    shows "<emp> kruskal getEdges_impl endpoints_impl ()
             <\<lambda>r. \<up>( distinct r \<and> set r \<subseteq> superE \<and> MSF (set (map \<alpha> r)))>\<^sub>t"
  proof -
    show ?thesis
      using kruskal_ref_spec[to_hnr]
      unfolding hn_refine_def  
      apply clarsimp
      apply (erule cons_post_rule)
      by (sep_auto simp: hn_ctxt_def pure_def list_set_rel_def in_br_conv dest: list_relD)     
  qed                            

end \<comment> \<open>locale @{text Kruskal_Impl}\<close>

end