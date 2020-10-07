section \<open>Edmonds-Karp Algorithm\<close>

theory EdmondsKarp_Termination_Abstract imports
  Flow_Networks.Ford_Fulkerson
begin

lemma mlex_fst_decrI:
  fixes a a' b b' N :: nat
  assumes "a<a'"
  assumes "b<N" "b'<N"
  shows "a*N + b < a'*N + b'"
proof -  
  have "a*N + b + 1 \<le> a*N + N" using \<open>b<N\<close> by linarith 
  also have "\<dots> \<le> a'*N" using \<open>a<a'\<close>
    by (metis Suc_leI ab_semigroup_add_class.add.commute 
      ab_semigroup_mult_class.mult.commute mult_Suc_right mult_le_mono2) 
  also have "\<dots> \<le> a'*N + b'" by auto
  finally show ?thesis by auto
qed      

lemma (in NFlow) augmenting_path_imp_shortest: 
  "isAugmentingPath p \<Longrightarrow> \<exists>p. Graph.isShortestPath cf s p t"
  using Graph.obtain_shortest_path unfolding isAugmentingPath_def
  by (fastforce simp: Graph.isSimplePath_def Graph.connected_def)

lemma (in NFlow) shortest_is_augmenting: 
  "Graph.isShortestPath cf s p t \<Longrightarrow> isAugmentingPath p"
  unfolding isAugmentingPath_def using Graph.shortestPath_is_simple
  by (fastforce)

subsection \<open>Complexity and Termination Analysis\<close>
text \<open>
  In this section, we show that the loop iterations of the Edmonds-Karp algorithm
  are bounded by $O(VE)$.

  The basic idea of the proof is, that a path that
  takes an edge reverse to an edge on some shortest path 
  cannot be a shortest path itself.

  As augmentation flips at least one edge, this yields a termination argument:
    After augmentation, either the minimum distance between source and target
    increases, or it remains the same, but the number of edges that lay on a
    shortest path decreases. As the minimum distance is bounded by $V$, 
    we get termination within $O(VE)$ loop iterations.
\<close>

context Graph begin

text \<open>
  The basic idea is expressed in the following lemma, which, however, 
  is not general enough to be applied for the correctness proof, where
  we flip more than one edge simultaneously.
  \<close>
lemma isShortestPath_flip_edge:
  assumes "isShortestPath s p t" "(u,v)\<in>set p"
  assumes "isPath s p' t" "(v,u)\<in>set p'"
  shows "length p' \<ge> length p + 2"
  using assms
proof -
  from \<open>isShortestPath s p t\<close> have 
    MIN: "min_dist s t = length p" and 
      P: "isPath s p t" and 
     DV: "distinct (pathVertices s p)"
    by (auto simp: isShortestPath_alt isSimplePath_def)
    
  from \<open>(u,v)\<in>set p\<close> obtain p1 p2 where [simp]: "p=p1@(u,v)#p2"
    by (auto simp: in_set_conv_decomp)
    
  from P DV have [simp]: "u\<noteq>v"
    by (cases p2) (auto simp add: isPath_append pathVertices_append)

  from P have DISTS: "dist s (length p1) u" "dist u 1 v" "dist v (length p2) t"
    by (auto simp: isPath_append dist_def intro: exI[where x="[(u,v)]"])

  from MIN have MIN': "min_dist s t = length p1 + 1 + length p2" by auto

  from min_dist_split[OF dist_trans[OF DISTS(1,2)] DISTS(3) MIN'] have
    MDSV: "min_dist s v = length p1 + 1" by simp
    
  from min_dist_split[OF DISTS(1) dist_trans[OF DISTS(2,3)]] MIN' have
    MDUT: "min_dist u t = 1 + length p2" by simp

  from \<open>(v,u)\<in>set p'\<close> obtain p1' p2' where [simp]: "p'=p1'@(v,u)#p2'"
    by (auto simp: in_set_conv_decomp)

  from \<open>isPath s p' t\<close> have 
    DISTS': "dist s (length p1') v" "dist u (length p2') t"
    by (auto simp: isPath_append dist_def)
  
  from DISTS'[THEN min_dist_minD, unfolded MDSV MDUT] show
    "length p + 2 \<le> length p'" by auto
qed    


text \<open>
  To be used for the analysis of augmentation, we have to generalize the 
  lemma to simultaneous flipping of edges:
  \<close> 
lemma isShortestPath_flip_edges:
  assumes "Graph.E c' \<supseteq> E - edges" "Graph.E c' \<subseteq> E \<union> (prod.swap`edges)"
  assumes SP: "isShortestPath s p t" and EDGES_SS: "edges \<subseteq> set p"
  assumes P': "Graph.isPath c' s p' t" "prod.swap`edges \<inter> set p' \<noteq> {}"
  shows "length p + 2 \<le> length p'"
proof -
  interpret g': Graph c' .

  (* TODO: The proof still contains some redundancy: A first flipped edge
    is searched in both, the induction, and the initialization *)
  {
    fix u v p1 p2'
    assume "(u,v)\<in>edges"
       and "isPath s p1 v" and "g'.isPath u p2' t"
    hence "min_dist s t < length p1 + length p2'"   
    proof (induction p2' arbitrary: u v p1 rule: length_induct)
      case (1 p2')
      note IH = "1.IH"[rule_format]
      note P1 = \<open>isPath s p1 v\<close>
      note P2' = \<open>g'.isPath u p2' t\<close>

      have "length p1 > min_dist s u"
      proof -
        from P1 have "length p1 \<ge> min_dist s v"
          using min_dist_minD by (auto simp: dist_def)
        moreover from \<open>(u,v)\<in>edges\<close> EDGES_SS 
        have "min_dist s v = Suc (min_dist s u)"
          using isShortestPath_level_edge[OF SP] by auto
        ultimately show ?thesis by auto
      qed  

      from isShortestPath_level_edge[OF SP] \<open>(u,v)\<in>edges\<close> EDGES_SS 
      have 
            "min_dist s t = min_dist s u + min_dist u t" 
        and "connected s u"
      by auto

      show ?case
      proof (cases "prod.swap`edges \<inter> set p2' = {}")
        \<comment> \<open>We proceed by a case distinction whether the suffix path contains swapped edges\<close>
        case True 
        with g'.transfer_path[OF _ P2', of c] \<open>g'.E \<subseteq> E \<union> prod.swap ` edges\<close>
        have "isPath u p2' t" by auto
        hence "length p2' \<ge> min_dist u t" using min_dist_minD
          by (auto simp: dist_def)
        moreover note \<open>length p1 > min_dist s u\<close>
        moreover note \<open>min_dist s t = min_dist s u + min_dist u t\<close>
        ultimately show ?thesis by auto
      next
        case False
        \<comment> \<open>Obtain first swapped edge on suffix path\<close>
        obtain p21' e' p22' where [simp]: "p2'=p21'@e'#p22'" and 
           E_IN_EDGES: "e'\<in>prod.swap`edges" and 
          P1_NO_EDGES: "prod.swap`edges \<inter> set p21' = {}"
          apply (rule split_list_first_propE[of p2' "\<lambda>e. e\<in>prod.swap`edges"])
          using \<open>prod.swap ` edges \<inter> set p2' \<noteq> {}\<close> by fastforce+
        obtain u' v' where [simp]: "e'=(v',u')" by (cases e')      
  
        \<comment> \<open>Split the suffix path accordingly\<close>
        from P2' have P21': "g'.isPath u p21' v'" and P22': "g'.isPath u' p22' t"
          by (auto simp: g'.isPath_append)
        \<comment> \<open>As we chose the first edge, the prefix of the suffix path is also a path in the original graph\<close>  
        from 
          g'.transfer_path[OF _ P21', of c] 
          \<open>g'.E \<subseteq> E \<union> prod.swap ` edges\<close> 
          P1_NO_EDGES
        have P21: "isPath u p21' v'" by auto
        from min_dist_is_dist[OF \<open>connected s u\<close>] 
        obtain psu where 
              PSU: "isPath s psu u" and 
          LEN_PSU: "length psu = min_dist s u" 
          by (auto simp: dist_def)
        from PSU P21 have P1n: "isPath s (psu@p21') v'" 
          by (auto simp: isPath_append)
        from IH[OF _ _ P1n P22'] E_IN_EDGES have 
          "min_dist s t < length psu + length p21' + length p22'" 
          by auto
        moreover note \<open>length p1 > min_dist s u\<close>
        ultimately show ?thesis by (auto simp: LEN_PSU)
      qed
    qed  
  } note aux=this

  (* TODO: This step is analogous to what we do in the False-case of the induction.
    Can we somehow remove the redundancy? *)
  \<comment> \<open>Obtain first swapped edge on path\<close>
  obtain p1' e p2' where [simp]: "p'=p1'@e#p2'" and 
    E_IN_EDGES: "e\<in>prod.swap`edges" and 
    P1_NO_EDGES: "prod.swap`edges \<inter> set p1' = {}"
    apply (rule split_list_first_propE[of p' "\<lambda>e. e\<in>prod.swap`edges"])
    using \<open>prod.swap ` edges \<inter> set p' \<noteq> {}\<close> by fastforce+
  obtain u v where [simp]: "e=(v,u)" by (cases e)      

  \<comment> \<open>Split the new path accordingly\<close>
  from \<open>g'.isPath s p' t\<close> have 
    P1': "g'.isPath s p1' v" and 
    P2': "g'.isPath u p2' t"
    by (auto simp: g'.isPath_append)
  \<comment> \<open>As we chose the first edge, the prefix of the path is also a path in the original graph\<close>  
  from 
    g'.transfer_path[OF _ P1', of c] 
    \<open>g'.E \<subseteq> E \<union> prod.swap ` edges\<close> 
    P1_NO_EDGES
  have P1: "isPath s p1' v" by auto
  
  from aux[OF _ P1 P2'] E_IN_EDGES 
  have "min_dist s t < length p1' + length p2'"
    by auto
  thus ?thesis using SP 
    by (auto simp: isShortestPath_min_dist_def)
qed    

end \<comment> \<open>Graph\<close>

text \<open>We outsource the more specific lemmas to their own locale, 
  to prevent name space pollution\<close>
locale ek_analysis_defs = Graph +
  fixes s t :: node

locale ek_analysis = ek_analysis_defs + Finite_Graph
begin

definition (in ek_analysis_defs) 
  "spEdges \<equiv> {e. \<exists>p. e\<in>set p \<and> isShortestPath s p t}"

lemma spEdges_ss_E: "spEdges \<subseteq> E"
  using isPath_edgeset unfolding spEdges_def isShortestPath_def by auto

lemma finite_spEdges[simp, intro]: "finite (spEdges)"  
  using finite_subset[OF spEdges_ss_E] 
  by blast

definition (in ek_analysis_defs) "uE \<equiv> E \<union> E\<inverse>"

lemma finite_uE[simp,intro]: "finite uE"
  by (auto simp: uE_def)

lemma E_ss_uE: "E\<subseteq>uE"  
  by (auto simp: uE_def)

lemma card_spEdges_le:
  shows "card spEdges \<le> card uE"
  apply (rule card_mono)
  apply (auto simp: order_trans[OF spEdges_ss_E E_ss_uE])
  done

lemma card_spEdges_less:
  shows "card spEdges < card uE + 1"
  using card_spEdges_le 
  by auto
  

definition (in ek_analysis_defs) "ekMeasure \<equiv> 
  if (connected s t) then
    (card V - min_dist s t) * (card uE + 1) + (card (spEdges))
  else 0"

lemma measure_decr:
  assumes SV: "s\<in>V"
  assumes SP: "isShortestPath s p t"
  assumes SP_EDGES: "edges\<subseteq>set p"
  assumes Ebounds: 
    "Graph.E c' \<supseteq> E - edges \<union> prod.swap`edges" 
    "Graph.E c' \<subseteq> E \<union> prod.swap`edges"
  shows "ek_analysis_defs.ekMeasure c' s t \<le> ekMeasure"
    and "edges - Graph.E c' \<noteq> {} 
         \<Longrightarrow> ek_analysis_defs.ekMeasure c' s t < ekMeasure"
proof -
  interpret g': ek_analysis_defs c' s t .

  interpret g': ek_analysis c' s t
    apply intro_locales
    apply (rule g'.Finite_Graph_EI)
    using finite_subset[OF Ebounds(2)] finite_subset[OF SP_EDGES]
    by auto
  
  from SP_EDGES SP have "edges \<subseteq> E" 
    by (auto simp: spEdges_def isShortestPath_def dest: isPath_edgeset)
  with Ebounds have Veq[simp]: "Graph.V c' = V"
    by (force simp: Graph.V_def)

  from Ebounds \<open>edges \<subseteq> E\<close> have uE_eq[simp]: "g'.uE = uE"  
    by (force simp: ek_analysis_defs.uE_def)

  from SP have LENP: "length p = min_dist s t" 
    by (auto simp: isShortestPath_min_dist_def) 

  from SP have CONN: "connected s t" 
    by (auto simp: isShortestPath_def connected_def)

  {
    assume NCONN2: "\<not>g'.connected s t"
    hence "s\<noteq>t" by auto
    with CONN NCONN2 have "g'.ekMeasure < ekMeasure"
      unfolding g'.ekMeasure_def ekMeasure_def
      using min_dist_less_V[OF SV]
      by auto
  } moreover {
    assume SHORTER: "g'.min_dist s t < min_dist s t"
    assume CONN2: "g'.connected s t"

    \<comment> \<open>Obtain a shorter path in $g'$\<close>
    from g'.min_dist_is_dist[OF CONN2] obtain p' where
      P': "g'.isPath s p' t" and LENP': "length p' = g'.min_dist s t"
      by (auto simp: g'.dist_def)

    { \<comment> \<open>Case: It does not use @{term "prod.swap`edges"}. 
        Then it is also a path in $g$, which is shorter than 
        the shortest path in $g$, yielding a contradiction.\<close>
      assume "prod.swap`edges \<inter> set p' = {}"
      with g'.transfer_path[OF _ P', of c] Ebounds have "dist s (length p') t"
        by (auto simp: dist_def)
      from LENP' SHORTER min_dist_minD[OF this] have False by auto 
    } moreover {
      \<comment> \<open>So assume the path uses the edge @{term "prod.swap e"}.\<close>
      assume "prod.swap`edges \<inter> set p' \<noteq> {}"
      \<comment> \<open>Due to auxiliary lemma, those path must be longer\<close>
      from isShortestPath_flip_edges[OF _ _ SP SP_EDGES P' this] Ebounds
      have "length p' > length p" by auto
      with SHORTER LENP LENP' have False by auto
    } ultimately have False by auto
  } moreover {
    assume LONGER: "g'.min_dist s t > min_dist s t"
    assume CONN2: "g'.connected s t"
    have "g'.ekMeasure < ekMeasure"
      unfolding g'.ekMeasure_def ekMeasure_def
      apply (simp only: Veq uE_eq CONN CONN2 if_True)
      apply (rule mlex_fst_decrI)
      using card_spEdges_less g'.card_spEdges_less 
        and g'.min_dist_less_V[OF _ CONN2] SV
        and LONGER
      apply auto

      done
  } moreover {
    assume EQ: "g'.min_dist s t = min_dist s t"
    assume CONN2: "g'.connected s t"

    {
      fix p'
      assume P': "g'.isShortestPath s p' t"
      have "prod.swap`edges \<inter> set p' = {}" 
      proof (rule ccontr) 
        assume EIP': "prod.swap`edges \<inter> set p' \<noteq> {}"
        from P' have 
             P': "g'.isPath s p' t" and 
          LENP': "length p' = g'.min_dist s t"
          by (auto simp: g'.isShortestPath_min_dist_def)
        from isShortestPath_flip_edges[OF _ _ SP SP_EDGES P' EIP'] Ebounds 
        have "length p + 2 \<le> length p'" by auto
        with LENP LENP' EQ show False by auto
      qed  
      with g'.transfer_path[of p' c s t] P' Ebounds have "isShortestPath s p' t"
        by (auto simp: Graph.isShortestPath_min_dist_def EQ)
    } hence SS: "g'.spEdges \<subseteq> spEdges" by (auto simp: g'.spEdges_def spEdges_def)
        
    {
      assume "edges - Graph.E c' \<noteq> {}"
      with g'.spEdges_ss_E SS SP SP_EDGES have "g'.spEdges \<subset> spEdges"
        unfolding g'.spEdges_def spEdges_def by fastforce
      hence "g'.ekMeasure < ekMeasure"  
        unfolding g'.ekMeasure_def ekMeasure_def 
        apply (simp only: Veq uE_eq EQ CONN CONN2 if_True)
        apply (rule add_strict_left_mono)
        apply (rule psubset_card_mono)
        apply simp
        by simp
    } note G1 = this

    have G2: "g'.ekMeasure \<le> ekMeasure"
      unfolding g'.ekMeasure_def ekMeasure_def
      apply (simp only: Veq uE_eq CONN CONN2 if_True)
      apply (rule add_mono[OF mult_right_mono])
      apply (simp add: EQ)
      apply simp
      apply (rule card_mono)
      apply simp
      by fact
    note G1 G2  
  } ultimately show 
    "g'.ekMeasure \<le> ekMeasure" 
    "edges - Graph.E c' \<noteq> {} \<Longrightarrow> g'.ekMeasure < ekMeasure"
    using less_linear[of "g'.min_dist s t" "min_dist s t"]   
    apply -
    apply (fastforce)+
    done

qed

end \<comment> \<open>Analysis locale\<close> 

text \<open>As a first step to the analysis setup, we characterize
  the effect of augmentation on the residual graph
  \<close>
context Graph
begin

definition "augment_cf edges cap \<equiv> \<lambda>e. 
  if e\<in>edges then c e - cap 
  else if prod.swap e\<in>edges then c e + cap
  else c e"

lemma augment_cf_empty[simp]: "augment_cf {} cap = c" 
  by (auto simp: augment_cf_def)

lemma augment_cf_ss_V: "\<lbrakk>edges \<subseteq> E\<rbrakk> \<Longrightarrow> Graph.V (augment_cf edges cap) \<subseteq> V"  
  unfolding Graph.E_def Graph.V_def
  by (auto simp add: augment_cf_def) []
  
lemma augment_saturate:
  fixes edges e
  defines "c' \<equiv> augment_cf edges (c e)"
  assumes EIE: "e\<in>edges"
  shows "e\<notin>Graph.E c'"
  using EIE unfolding c'_def augment_cf_def
  by (auto simp: Graph.E_def)
  

lemma augment_cf_split: 
  assumes "edges1 \<inter> edges2 = {}" "edges1\<inverse> \<inter> edges2 = {}"
  shows "Graph.augment_cf c (edges1 \<union> edges2) cap 
    = Graph.augment_cf (Graph.augment_cf c edges1 cap) edges2 cap"  
  using assms
  by (fastforce simp: Graph.augment_cf_def intro!: ext)
      
end \<comment> \<open>Graph\<close>

context NFlow begin

lemma augmenting_edge_no_swap: "isAugmentingPath p \<Longrightarrow> set p \<inter> (set p)\<inverse> = {}"
  using cf.isSPath_nt_parallel_pf
  by (auto simp: isAugmentingPath_def)

lemma aug_flows_finite[simp, intro!]: 
  "finite {cf e |e. e \<in> set p}"
  apply (rule finite_subset[where B="cf`set p"])
  by auto

lemma aug_flows_finite'[simp, intro!]: 
  "finite {cf (u,v) |u v. (u,v) \<in> set p}"
  apply (rule finite_subset[where B="cf`set p"])
  by auto

lemma augment_alt:
  assumes AUG: "isAugmentingPath p"
  defines "f' \<equiv> augment (augmentingFlow p)"
  defines "cf' \<equiv> residualGraph c f'"
  shows "cf' = Graph.augment_cf cf (set p) (resCap p)"
proof -
  {
    fix u v
    assume "(u,v)\<in>set p"
    hence "resCap p \<le> cf (u,v)"
      unfolding resCap_def by (auto intro: Min_le)
  } note bn_smallerI = this

  {
    fix u v
    assume "(u,v)\<in>set p"
    hence "(u,v)\<in>cf.E" using AUG cf.isPath_edgeset
      by (auto simp: isAugmentingPath_def cf.isSimplePath_def)
    hence "(u,v)\<in>E \<or> (v,u)\<in>E" using cfE_ss_invE by (auto)
  } note edge_or_swap = this 

  show ?thesis  
    apply (rule ext)
    unfolding cf.augment_cf_def
    using augmenting_edge_no_swap[OF AUG]
    apply (auto 
      simp: augment_def augmentingFlow_def cf'_def f'_def residualGraph_def
      split: prod.splits
      dest: edge_or_swap 
      )
    done
qed    


lemma augmenting_path_contains_resCap:
  assumes "isAugmentingPath p"
  obtains e where "e\<in>set p" "cf e = resCap p" 
proof -  
  from assms have "p\<noteq>[]" by (auto simp: isAugmentingPath_def s_not_t)
  hence "{cf e | e. e \<in> set p} \<noteq> {}" by (cases p) auto
  with Min_in[OF aug_flows_finite this, folded resCap_def]
    obtain e where "e\<in>set p" "cf e = resCap p" by auto
  thus ?thesis by (blast intro: that)
qed  
        
text \<open>Finally, we show the main theorem used for termination and complexity 
  analysis: Augmentation with a shortest path decreases the measure function.\<close>
theorem shortest_path_decr_ek_measure:
  fixes p
  assumes SP: "Graph.isShortestPath cf s p t"
  defines "f' \<equiv> augment (augmentingFlow p)"
  defines "cf' \<equiv> residualGraph c f'"
  shows "ek_analysis_defs.ekMeasure cf' s t < ek_analysis_defs.ekMeasure cf s t"
proof -
  interpret cf: ek_analysis cf by unfold_locales
  interpret cf': ek_analysis_defs cf' .

  from SP have AUG: "isAugmentingPath p" 
    unfolding isAugmentingPath_def cf.isShortestPath_alt by simp

  note BNGZ = resCap_gzero[OF AUG]  

  have cf'_alt: "cf' = cf.augment_cf (set p) (resCap p)"
    using augment_alt[OF AUG] unfolding cf'_def f'_def by simp

  obtain e where
    EIP: "e\<in>set p" and EBN: "cf e = resCap p"
    by (rule augmenting_path_contains_resCap[OF AUG]) auto

  have ENIE': "e\<notin>cf'.E" 
    using cf.augment_saturate[OF EIP] EBN by (simp add: cf'_alt)
  
  { fix e  
    have "cf e + resCap p \<noteq> 0" using resE_nonNegative[of e] BNGZ by auto 
  } note [simp] = this  
  
  { fix e
    assume "e\<in>set p"
    hence "e \<in> cf.E"
      using cf.shortestPath_is_path[OF SP] cf.isPath_edgeset by blast
    hence "cf e > 0 \<and> cf e \<noteq> 0" using resE_positive[of e] by auto
  } note [simp] = this

  show ?thesis 
    apply (rule cf.measure_decr(2))
    apply (simp_all add: s_node)
    apply (rule SP)
    apply (rule order_refl)

    apply (rule conjI)
      apply (unfold Graph.E_def) []
      apply (auto simp: cf'_alt cf.augment_cf_def) []

      using augmenting_edge_no_swap[OF AUG]
      apply (fastforce 
        simp: cf'_alt cf.augment_cf_def Graph.E_def 
        simp del: cf.zero_cap_simp) []
      
    apply (unfold Graph.E_def) []
    apply (auto simp: cf'_alt cf.augment_cf_def) []
    using EIP ENIE' apply auto []
    done
qed    

end \<comment> \<open>Network with flow\<close>

end
