section \<open>The Ford-Fulkerson Theorem\<close>
theory Ford_Fulkerson
imports Augmenting_Flow Augmenting_Path
begin
text \<open>In this theory, we prove the Ford-Fulkerson theorem, 
  and its well-known corollary, the min-cut max-flow theorem.
\<close>

text \<open>We fix a network with a flow and a cut\<close>
locale NFlowCut = NFlow c s t f + NCut c s t k 
  for c :: "'capacity::linordered_idom graph" and s t f k
begin

lemma finite_k[simp, intro!]: "finite k" 
  using cut_ss_V finite_V finite_subset[of k V] by blast
  
subsection \<open>Net Flow\<close>
text \<open>We define the \emph{net flow} to be the amount of flow effectively 
  passed over the cut from the source to the sink:\<close>
definition netFlow :: "'capacity"
  where "netFlow \<equiv> (\<Sum>e \<in> outgoing' k. f e) - (\<Sum>e \<in> incoming' k. f e)"

text \<open>We can show that the net flow equals the value of the flow.
  Note: Cormen et al.~\cite{CLRS09} present a whole page full of 
  summation calculations for this proof, and our formal proof also 
  looks quite complicated.
\<close>
lemma flow_value: "netFlow = val"
proof -
  let ?LCL = "{(u, v). u \<in> k \<and> v \<in> k \<and> (u, v) \<in> E}"
  let ?AOG = "{(u, v). u \<in> k \<and> (u, v) \<in> E}"
  let ?AIN = "{(v, u) | u v. u \<in> k \<and> (v, u) \<in> E}"
  let ?SOG = "\<lambda>u. (\<Sum>e \<in> outgoing u. f e)"
  let ?SIN = "\<lambda>u. (\<Sum>e \<in> incoming u. f e)"
  let ?SOG' = "(\<Sum>e \<in> outgoing' k. f e)"
  let ?SIN' = "(\<Sum>e \<in> incoming' k. f e)"

  text \<open>Some setup to make finiteness reasoning implicit\<close>
  note [[simproc finite_Collect]]

  have  
    "netFlow = ?SOG' + (\<Sum>e \<in> ?LCL. f e) - (?SIN' + (\<Sum>e \<in> ?LCL. f e))" 
    (is "_   =        ?SAOG              -          ?SAIN") 
    using netFlow_def by auto
  also have "?SAOG = (\<Sum>y \<in> k - {s}. ?SOG y) + ?SOG s"
  proof -
    have "?SAOG = (\<Sum>e\<in>(outgoing' k \<union> ?LCL). f e)"
      by (rule sum.union_disjoint[symmetric]) (auto simp: outgoing'_def)
    also have "outgoing' k \<union> ?LCL = (\<Union>y\<in>k-{s}. outgoing y) \<union> outgoing s"
      by (auto simp: outgoing_def outgoing'_def s_in_cut)
    also have "(\<Sum>e\<in>(\<Union>(outgoing ` (k - {s})) \<union> outgoing s). f e) 
      = (\<Sum>e\<in>(\<Union>(outgoing ` (k - {s}))). f e) + (\<Sum>e\<in>outgoing s. f e)"  
      by (rule sum.union_disjoint) 
         (auto simp: outgoing_def intro: finite_Image)
    also have "(\<Sum>e\<in>(\<Union>(outgoing ` (k - {s}))). f e) 
      = (\<Sum>y \<in> k - {s}. ?SOG y)"
      by (rule sum.UNION_disjoint)
         (auto simp: outgoing_def intro: finite_Image)
    finally show ?thesis .
  qed     
  also have "?SAIN = (\<Sum>y \<in> k - {s}. ?SIN y) + ?SIN s"
  proof -
    have "?SAIN = (\<Sum>e\<in>(incoming' k \<union> ?LCL). f e)"
      by (rule sum.union_disjoint[symmetric]) (auto simp: incoming'_def)
    also have "incoming' k \<union> ?LCL = (\<Union>y\<in>k-{s}. incoming y) \<union> incoming s"
      by (auto simp: incoming_def incoming'_def s_in_cut)
    also have "(\<Sum>e\<in>(\<Union>(incoming ` (k - {s})) \<union> incoming s). f e) 
      = (\<Sum>e\<in>(\<Union>(incoming ` (k - {s}))). f e) + (\<Sum>e\<in>incoming s. f e)"  
      by (rule sum.union_disjoint) 
         (auto simp: incoming_def intro: finite_Image)
    also have "(\<Sum>e\<in>(\<Union>(incoming ` (k - {s}))). f e) 
      = (\<Sum>y \<in> k - {s}. ?SIN y)"
      by (rule sum.UNION_disjoint)
         (auto simp: incoming_def intro: finite_Image)
    finally show ?thesis .
  qed  
  finally have "netFlow =  
      ((\<Sum>y \<in> k - {s}. ?SOG y) + ?SOG s) 
    - ((\<Sum>y \<in> k - {s}. ?SIN y) + ?SIN s)"
    (is "netFlow = ?R") .
  also have "?R = ?SOG s - ?SIN s"
  proof -
    have "(\<And>u. u \<in> k - {s} \<Longrightarrow> ?SOG u = ?SIN u)" 
      using conservation_const cut_ss_V t_ni_cut by force
    thus ?thesis by auto  
  qed
  finally show ?thesis unfolding val_def by simp
qed

text \<open>The value of any flow is bounded by the capacity of any cut.
  This is intuitively clear, as all flow from the source to the sink has to go
  over the cut.\<close>
corollary weak_duality: "val \<le> cap"
proof -
  have "(\<Sum>e \<in> outgoing' k. f e) \<le> (\<Sum>e \<in> outgoing' k. c e)" (is "?L \<le> ?R") 
    using capacity_const by (metis sum_mono)
  then have "(\<Sum>e \<in> outgoing' k. f e) \<le> cap" unfolding cap_def  by simp
  moreover have "val \<le> (\<Sum>e \<in> outgoing' k. f e)" using netFlow_def
    by (simp add: capacity_const flow_value sum_nonneg)
  ultimately show ?thesis by simp
qed

end \<comment> \<open>Cut\<close>

subsection \<open>Ford-Fulkerson Theorem\<close>
context NFlow begin

text \<open>We prove three auxiliary lemmas first, and the state the theorem as a corollary\<close>
lemma fofu_I_II: "isMaxFlow f \<Longrightarrow> \<not> (\<exists> p. isAugmentingPath p)"
unfolding isMaxFlow_alt
proof (rule ccontr)
  assume asm: "NFlow c s t f 
    \<and> (\<forall>f'. NFlow c s t f' \<longrightarrow> Flow.val c s f' \<le> Flow.val c s f)"
  assume asm_c: "\<not> \<not> (\<exists> p. isAugmentingPath p)"
  then obtain p where obt: "isAugmentingPath p" by blast
  have fct1: "Flow cf s t (augmentingFlow p)" using obt augFlow_resFlow by auto
  have fct2: "Flow.val cf s (augmentingFlow p) > 0" using obt augFlow_val
    resCap_gzero isAugmentingPath_def cf.isSimplePath_def by auto
  have "NFlow c s t (augment (augmentingFlow p))" 
    using fct1 augment_flow_presv Network_axioms 
    unfolding Flow_def NFlow_def NPreflow_def 
    by auto
  moreover have "Flow.val c s (augment (augmentingFlow p)) > val" 
    using fct1 fct2 augment_flow_value by auto
  ultimately show "False" using asm by auto
qed

lemma fofu_II_III: 
  "\<not> (\<exists> p. isAugmentingPath p) \<Longrightarrow> \<exists>k'. NCut c s t k' \<and> val = NCut.cap c k'" 
proof (intro exI conjI)
  let ?S = "cf.reachableNodes s"
  assume asm: "\<not> (\<exists> p. isAugmentingPath p)"
  hence "t\<notin>?S"
    unfolding isAugmentingPath_def cf.reachableNodes_def cf.connected_def
    by (auto dest: cf.isSPath_pathLE)
  then show CUT: "NCut c s t ?S"
  proof unfold_locales
    show "Graph.reachableNodes cf s \<subseteq> V"  
      using cf.reachable_ss_V s_node resV_netV by auto
    show "s \<in> Graph.reachableNodes cf s" 
      unfolding Graph.reachableNodes_def Graph.connected_def 
      by (metis Graph.isPath.simps(1) mem_Collect_eq)
  qed
  then interpret NCut c s t ?S .
  interpret NFlowCut c s t f ?S by intro_locales

  have "\<forall>(u,v)\<in>outgoing' ?S. f (u,v) = c (u,v)"
  proof (rule ballI, rule ccontr, clarify) \<comment> \<open>Proof by contradiction\<close>
    fix u v
    assume "(u,v)\<in>outgoing' ?S" 
    hence "(u,v)\<in>E" "u\<in>?S" "v\<notin>?S"
      by (auto simp: outgoing'_def)
    assume "f (u,v) \<noteq> c (u,v)"
    hence "f (u,v) < c (u,v)" 
      using capacity_const by (metis (no_types) eq_iff not_le)
    hence "cf (u, v) \<noteq> 0" 
      unfolding residualGraph_def using \<open>(u,v)\<in>E\<close> by auto
    hence "(u, v) \<in> cf.E" unfolding cf.E_def by simp
    hence "v\<in>?S" using \<open>u\<in>?S\<close> by (auto intro: cf.reachableNodes_append_edge)
    thus False using \<open>v\<notin>?S\<close> by auto
  qed  
  hence "(\<Sum>e \<in> outgoing' ?S. f e) = cap"
    unfolding cap_def by auto
  moreover 
  have "\<forall>(u,v)\<in>incoming' ?S. f (u,v) = 0"  
  proof (rule ballI, rule ccontr, clarify) \<comment> \<open>Proof by contradiction\<close>
    fix u v
    assume "(u,v)\<in>incoming' ?S"
    hence "(u,v)\<in>E" "u\<notin>?S" "v\<in>?S" by (auto simp: incoming'_def)
    hence "(v,u)\<notin>E" using no_parallel_edge by auto

    assume "f (u,v) \<noteq> 0"
    hence "cf (v, u) \<noteq> 0" 
      unfolding residualGraph_def using \<open>(u,v)\<in>E\<close> \<open>(v,u)\<notin>E\<close> by auto
    hence "(v, u) \<in> cf.E" unfolding cf.E_def by simp
    hence "u\<in>?S" using \<open>v\<in>?S\<close> cf.reachableNodes_append_edge by auto
    thus False using \<open>u\<notin>?S\<close> by auto
  qed  
  hence "(\<Sum>e \<in> incoming' ?S. f e) = 0"
    unfolding cap_def by auto
  ultimately show "val = cap"
    unfolding flow_value[symmetric] netFlow_def by simp
qed
      
lemma fofu_III_I: 
  "\<exists>k. NCut c s t k \<and> val = NCut.cap c k \<Longrightarrow> isMaxFlow f"
proof clarify
  fix k
  assume "NCut c s t k"
  then interpret NCut c s t k .
  interpret NFlowCut c s t f k by intro_locales

  assume "val = cap"
  {
    fix f'
    assume "Flow c s t f'"
    then interpret fc': Flow c s t f' .
    interpret fc': NFlowCut c s t f' k by intro_locales

    have "fc'.val \<le> cap" using fc'.weak_duality .
    also note \<open>val = cap\<close>[symmetric]
    finally have "fc'.val \<le> val" .
  }
  thus "isMaxFlow f" unfolding isMaxFlow_def
    by simp unfold_locales
qed

text \<open>Finally we can state the Ford-Fulkerson theorem: \<close>
theorem ford_fulkerson: shows
  "isMaxFlow f \<longleftrightarrow> 
  \<not> Ex isAugmentingPath" and "\<not> Ex isAugmentingPath \<longleftrightarrow> 
  (\<exists>k. NCut c s t k \<and> val = NCut.cap c k)"
  using fofu_I_II fofu_II_III fofu_III_I by auto
  
subsection \<open>Corollaries\<close>

text \<open>In this subsection we present a few corollaries of the 
  flow-cut relation and the Ford-Fulkerson theorem.
\<close>

text \<open>The outgoing flow of the source is the same as the incoming flow of 
  the sink. Intuitively, this means that no flow is generated or lost in the 
  network, except at the source and sink.\<close>
corollary inflow_t_outflow_s: 
  "(\<Sum>e \<in> incoming t. f e) = (\<Sum>e \<in> outgoing s. f e)"
proof -
  txt \<open>We choose a cut between the sink and all other nodes\<close>
  let ?K = "V - {t}"
  interpret NFlowCut c s t f ?K
    using s_node s_not_t by unfold_locales auto

  txt \<open>The cut is chosen such that its outgoing edges are the incoming edges
    to the sink, and its incoming edges are the outgoing edges from the sink.
    Note that the sink has no outgoing edges.\<close>
  have "outgoing' ?K = incoming t"
   and "incoming' ?K = {}"
    using no_self_loop no_outgoing_t
    unfolding outgoing'_def incoming_def incoming'_def outgoing_def V_def  
    by auto
  hence "(\<Sum>e \<in> incoming t. f e) = netFlow" unfolding netFlow_def by auto
  also have "netFlow = val" by (rule flow_value)
  also have "val = (\<Sum>e \<in> outgoing s. f e)" by (auto simp: val_alt)
  finally show ?thesis .
qed

text \<open>As an immediate consequence of the Ford-Fulkerson theorem, we get that
  there is no augmenting path if and only if the flow is maximal.\<close>
corollary noAugPath_iff_maxFlow: "(\<nexists>p. isAugmentingPath p) \<longleftrightarrow> isMaxFlow f"
  using ford_fulkerson by blast

end \<comment> \<open>Network with flow\<close>

text \<open>The value of the maximum flow equals the capacity of the minimum cut\<close>
corollary (in Network) maxFlow_minCut: "\<lbrakk>isMaxFlow f; isMinCut c s t k\<rbrakk> 
  \<Longrightarrow> Flow.val c s f = NCut.cap c k"
proof -
  assume "isMaxFlow f" "isMinCut c s t k"
  then interpret Flow c s t f + NCut c s t k
    unfolding isMaxFlow_def isMinCut_def by simp_all
  interpret NFlowCut c s t f k by intro_locales 
  
  
  from ford_fulkerson \<open>isMaxFlow f\<close>
  obtain k' where "NCut c s t k'" and "val = NCut.cap c k'"
    by blast
  thus "val = cap"
    using \<open>isMinCut c s t k\<close> weak_duality
    unfolding isMinCut_def by auto
qed    

end \<comment> \<open>Theory\<close>
