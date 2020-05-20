section \<open>Directed Graphs\<close>
theory Graph
imports Main
begin
text \<open>
  We define a specialized graph library for graphs that are induced by 
  capacity matrices.
\<close>

lemma finite_Image: fixes R shows "\<lbrakk> finite R \<rbrakk> \<Longrightarrow> finite (R `` A)"
  by (meson Image_iff finite_Range Range.intros finite_subset subsetI)

lemma map_eq_appendE: 
  assumes "map f ls = fl@fl'"
  obtains l l' where "ls=l@l'" and "map f l=fl" and  "map f l' = fl'"
using that[of "take (length fl) ls" "drop (length fl) ls"] assms 
by(simp add: take_map[symmetric] drop_map[symmetric])

subsection \<open>Definitions\<close>

subsubsection \<open>Basic Definitions\<close>
text \<open>
  We fix the nodes to be natural numbers.
\<close>  
  type_synonym node = nat 
  type_synonym edge = "node \<times> node"

text \<open>
  The capacities are left polymorphic, however, they
  are restricted to linearly ordered domains.
\<close>
type_synonym 'capacity graph = "edge \<Rightarrow> 'capacity"
  
locale Graph = fixes c :: "'capacity::linordered_idom graph"
begin
definition E :: "edge set" \<comment> \<open>Edges of the graph\<close>
where "E \<equiv> {(u, v). c (u, v) \<noteq> 0}"

definition V :: "node set" \<comment> \<open>Nodes of the graph. Exactly the nodes 
  that have adjacent edges.\<close>
where "V \<equiv> {u. \<exists>v. (u, v) \<in> E \<or> (v, u) \<in> E}"

definition incoming :: "node \<Rightarrow> edge set" \<comment> \<open>Incoming edges into a node\<close>
where "incoming v \<equiv> {(u, v) | u. (u, v) \<in> E}"

definition outgoing :: "node \<Rightarrow> edge set" \<comment> \<open>Outgoing edges from a node\<close>
where "outgoing v \<equiv> {(v, u) | u. (v, u) \<in> E}"
  
definition adjacent :: "node \<Rightarrow> edge set" \<comment> \<open>Adjacent edges of a node\<close>
where "adjacent v \<equiv> incoming v \<union> outgoing v"

definition incoming' :: "node set \<Rightarrow> edge set" \<comment> \<open>Incoming edges into 
  a set of nodes\<close>
where "incoming' k \<equiv> {(u, v) | u v. u \<notin> k \<and> v \<in> k \<and> (u, v) \<in> E}"
  
definition outgoing' :: "node set \<Rightarrow> edge set" \<comment> \<open>Outgoing edges from 
  a set of nodes\<close>
where "outgoing' k \<equiv> {(v, u) | u v. u \<notin> k \<and> v \<in> k \<and> (v, u) \<in> E}"
  
definition adjacent' :: "node set \<Rightarrow> edge set" \<comment> \<open>Edges adjacent to a 
  set of nodes\<close>
where "adjacent' k \<equiv> incoming' k \<union> outgoing' k"

definition is_adj_map :: "(node \<Rightarrow> node list) \<Rightarrow> bool" where
  "is_adj_map ps \<equiv> (\<forall>u. distinct (ps u) \<and> set (ps u) = E``{u} \<union> E\<inverse>``{u})"

definition "adjacent_nodes u \<equiv> E``{u} \<union> E\<inverse>``{u}"
  
  
end \<comment> \<open>Graph\<close>

subsubsection \<open>Finite Graphs\<close>
locale Finite_Graph = Graph +
  assumes finite_V[simp, intro!]: "finite V"

subsubsection \<open>Paths\<close>
type_synonym path = "edge list"

context Graph
begin
  fun isPath :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
  where
    "isPath u [] v \<longleftrightarrow> u = v"
  | "isPath u ((x,y)#p) v \<longleftrightarrow> u = x \<and> (x, y) \<in> E \<and> isPath y p v"

  fun pathVertices :: "node \<Rightarrow> path \<Rightarrow> node list"
  where
    "pathVertices u [] = [u]"
  | "pathVertices u (e # es) = fst e # (pathVertices (snd e) es)"
  
  (* TODO: This characterization is probably nicer to work with! Exchange! *)
  definition (in Graph) pathVertices_fwd :: "node \<Rightarrow> edge list \<Rightarrow> node list" 
    where "pathVertices_fwd u p = u#map snd p"

  lemma (in Graph) pathVertices_fwd: 
    assumes "isPath u p v"
    shows "pathVertices u p = pathVertices_fwd u p"
    unfolding pathVertices_fwd_def
    using assms apply (induction p arbitrary: u)
    by auto


  definition connected :: "node \<Rightarrow> node \<Rightarrow> bool" 
    where "connected u v \<equiv> \<exists>p. isPath u p v" 
  
  abbreviation (input) "isReachable \<equiv> connected" (* Deprecated *)

  definition reachableNodes :: "node \<Rightarrow> node set"  
    where "reachableNodes u \<equiv> {v. connected u v}"
  
  definition isShortestPath :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
    where "isShortestPath u p v 
    \<equiv> isPath u p v \<and> (\<forall>p'. isPath u p' v \<longrightarrow> length p \<le> length p')"
      
  definition isSimplePath :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
    where "isSimplePath u p v \<equiv> isPath u p v \<and> distinct (pathVertices u p)"

  definition dist :: "node \<Rightarrow> nat \<Rightarrow> node \<Rightarrow> bool" 
    \<comment> \<open>There is a path of given length between the nodes\<close>
    where "dist v d v' \<equiv> \<exists>p. isPath v p v' \<and> length p = d"

  definition min_dist :: "node \<Rightarrow> node \<Rightarrow> nat"
    \<comment> \<open>Minimum distance between two connected nodes\<close>
    where "min_dist v v' = (LEAST d. dist v d v')"

end  


subsection \<open>Properties\<close>

subsubsection \<open>Basic Properties\<close>
context Graph
begin

lemma V_alt: "V = fst`E \<union> snd`E" unfolding V_def by force

lemma E_ss_VxV: "E \<subseteq> V\<times>V" by (auto simp: V_def)

lemma adjacent_nodes_ss_V: "adjacent_nodes u \<subseteq> V"  
  unfolding adjacent_nodes_def using E_ss_VxV by auto
    
lemma Vfin_imp_Efin[simp, intro]: assumes "finite V" shows "finite E"
  using E_ss_VxV assms by (auto intro: finite_subset)

lemma Efin_imp_Vfin: "finite E \<Longrightarrow> finite V"
  unfolding V_alt by auto

lemma zero_cap_simp[simp]: "(u,v)\<notin>E \<Longrightarrow> c (u,v) = 0"  
  by (auto simp: E_def)

lemma succ_ss_V: "E``{u} \<subseteq> V" by (auto simp: V_def)

lemma pred_ss_V: "E\<inverse>``{u} \<subseteq> V" by (auto simp: V_def)


lemma 
  incoming_edges: "incoming u \<subseteq> E" and
  outgoing_edges: "outgoing u \<subseteq> E" and
  incoming'_edges: "incoming' U \<subseteq> E" and
  outgoing'_edges: "outgoing' U \<subseteq> E"
  by (auto simp: incoming_def outgoing_def incoming'_def outgoing'_def)
  
lemma 
  incoming_alt: "incoming u = (\<lambda>v. (v,u))`(E\<inverse>``{u})" and
  outgoing_alt: "outgoing u = Pair u`(E``{u})"
  by (auto simp: incoming_def outgoing_def)

lemma 
  finite_incoming[simp, intro]: "finite V \<Longrightarrow> finite (incoming u)" and
  finite_outgoing[simp, intro]: "finite V \<Longrightarrow> finite (outgoing u)"
  by (auto simp: incoming_alt outgoing_alt intro: finite_Image)

lemma 
  finite_incoming'[simp, intro]: "finite V \<Longrightarrow> finite (incoming' U)" and
  finite_outgoing'[simp, intro]: "finite V \<Longrightarrow> finite (outgoing' U)"
  by (auto 
    intro: finite_subset[OF incoming'_edges] 
    intro: finite_subset[OF outgoing'_edges])
  
subsubsection \<open>Summations over Edges and Nodes\<close>  
text \<open>We provide useful alternative characterizations for summation over 
    all incoming or outgoing edges.\<close>
lemma sum_outgoing_pointwise: "(\<Sum>e\<in>outgoing u. g e) = (\<Sum>v\<in>E``{u}. g (u,v))"  
proof -
  have "(\<Sum>e\<in>outgoing u. g e) = (\<Sum>e\<in>(\<lambda>v. (u,v))`(E``{u}). g e)"  
    by (rule sum.cong) (auto simp: outgoing_def)
  also have "\<dots> = (\<Sum>v\<in>E``{u}. g (u,v))"  
    by (subst sum.reindex)(auto simp add: inj_on_def)
  finally show ?thesis .
qed  

lemma sum_incoming_pointwise: "(\<Sum>e\<in>incoming u. g e) = (\<Sum>v\<in>E\<inverse>``{u}. g (v,u))"  
proof -
  have "(\<Sum>e\<in>incoming u. g e) = (\<Sum>e\<in>(\<lambda>v. (v,u))`(E\<inverse>``{u}). g e)"  
    by (rule sum.cong) (auto simp: incoming_def)
  also have "\<dots> = (\<Sum>v\<in>E\<inverse>``{u}. g (v,u))"  
    by (subst sum.reindex)(auto simp add: inj_on_def)
  finally show ?thesis .
qed  

text \<open>Extend summations over incoming/outgoing edges to summations over
  all nodes, provided the summed-up function is zero for non-edges.\<close>
lemma (in Finite_Graph) sum_incoming_extend:  
  assumes "\<And>v. \<lbrakk> v\<in>V; (v,u)\<notin>E \<rbrakk> \<Longrightarrow> g (v,u) = 0"
  shows "(\<Sum>e\<in>incoming u. g e) = (\<Sum>v\<in>V. g (v,u))"
  apply (subst sum_incoming_pointwise)
  apply (rule sum.mono_neutral_left)
  using assms pred_ss_V by auto

lemma (in Finite_Graph) sum_outgoing_extend:  
  assumes "\<And>v. \<lbrakk> v\<in>V; (u,v)\<notin>E \<rbrakk> \<Longrightarrow> g (u,v) = 0"
  shows "(\<Sum>e\<in>outgoing u. g e) = (\<Sum>v\<in>V. g (u,v))"
  apply (subst sum_outgoing_pointwise)
  apply (rule sum.mono_neutral_left)
  using assms succ_ss_V by auto

text \<open>When summation is done over something that satisfies the capacity 
  constraint, e.g., a flow, the summation can be extended to all 
  outgoing/incoming edges, as the additional edges must have zero capacity.\<close>
(* TODO: Historical lemmas. Get rid of \<forall> quantifier. *)
lemma (in Finite_Graph) sum_outgoing_alt: "\<lbrakk>\<forall>e. 0 \<le> g e \<and> g e \<le> c e\<rbrakk> \<Longrightarrow>
  \<forall>v \<in> V. (\<Sum>e \<in> outgoing v. g e) = (\<Sum>u \<in> V. g (v, u))"
  apply (rule ballI)
  apply (rule sum_outgoing_extend)
  apply clarsimp
  by (metis antisym zero_cap_simp)
  
lemma (in Finite_Graph) sum_incoming_alt: "\<lbrakk>\<forall>e. 0 \<le> g e \<and> g e \<le> c e\<rbrakk> \<Longrightarrow>
  \<forall>v \<in> V. (\<Sum>e \<in> incoming v. g e) = (\<Sum>u \<in> V. g (u, v))"
  apply (rule ballI)
  apply (rule sum_incoming_extend)
  apply clarsimp
  by (metis antisym zero_cap_simp)


subsubsection \<open>Finite Graphs\<close>

lemma (in Finite_Graph) finite_E[simp,intro!]: "finite E" by simp

lemma (in Graph) Finite_Graph_EI: "finite E \<Longrightarrow> Finite_Graph c"
  apply unfold_locales
  by (rule Efin_imp_Vfin)
  
lemma (in Finite_Graph) adjacent_nodes_finite[simp, intro!]: "finite (adjacent_nodes u)"
  unfolding adjacent_nodes_def by (auto intro: finite_Image)
    
subsubsection \<open>Paths\<close>

named_theorems split_path_simps \<open>Simplification lemmas to split paths\<close>

lemma transfer_path:
  \<comment> \<open>Transfer path to another graph\<close>
  assumes "set p\<inter>E \<subseteq> Graph.E c'"
  assumes "isPath u p v"
  shows "Graph.isPath c' u p v"
  using assms
  apply (induction u p v rule: isPath.induct)
  apply (auto simp: Graph.isPath.simps)
  done

lemma isPath_append[split_path_simps]: 
  "isPath u (p1 @ p2) v \<longleftrightarrow> (\<exists>w. isPath u p1 w \<and> isPath w p2 v)"  
  by (induction p1 arbitrary: u) auto 
  
lemma isPath_head[split_path_simps]: 
  "isPath u (e#p) v \<longleftrightarrow> fst e = u \<and> e \<in> E \<and> isPath (snd e) p v"
  by (cases e) auto

lemma isPath_head2: 
  "isPath u (e#p) v \<Longrightarrow> (p = [] \<or> (p \<noteq> [] \<and> fst (hd p) = snd e))"
  by (metis Graph.isPath_head list.collapse)
  
lemma isPath_tail: 
  "isPath u (p@[e]) v \<longleftrightarrow> isPath u p (fst e) \<and> e \<in> E \<and> snd e = v"
  by (induction p) (auto simp: isPath_append isPath_head)

lemma isPath_tail2: 
  "isPath u (p@[e]) v \<Longrightarrow> (p = [] \<or> (p \<noteq> [] \<and> snd (last p) = fst e))"
  by (metis Graph.isPath_tail append_butlast_last_id)
      
(* TODO: Really needed? *)  
lemma isPath_append_edge: 
  "isPath v p v' \<Longrightarrow> (v',v'')\<in>E \<Longrightarrow> isPath v (p@[(v',v'')]) v''"  
  by (auto simp: isPath_append)

lemma isPath_edgeset: "\<lbrakk>isPath u p v; e \<in> set p\<rbrakk> \<Longrightarrow> e \<in> E"
  using E_def 
  by (metis isPath_head isPath_append in_set_conv_decomp_first)
  
lemma isPath_rtc: "isPath u p v \<Longrightarrow> (u, v) \<in> E\<^sup>*"
proof (induction p arbitrary: u)
  case Nil
  thus ?case by auto
next
  case (Cons e es)
  obtain u1 u2 where "e = (u1, u2)" apply (cases e) by auto
  then have "u = u1 \<and> isPath u2 es v \<and> (u1, u2) \<in> E"
    using isPath.simps(2) Cons.prems by auto
  then have "(u, u2) \<in> E" and "(u2, v) \<in> E\<^sup>*" using Cons.IH by auto
  thus ?case by auto 
qed
  
lemma rtc_isPath: "(u, v) \<in> E\<^sup>* \<Longrightarrow> (\<exists>p. isPath u p v)"
proof (induction rule: rtrancl.induct)
  case (rtrancl_refl a)
  have "isPath a [] a" by simp
  thus ?case by blast
next
  case (rtrancl_into_rtrancl u u' v)
  then obtain p1 where "isPath u p1 u'" by blast
  moreover have "(u', v) \<in> E" using rtrancl_into_rtrancl.hyps(2) by simp
  ultimately have "isPath u (p1 @ [(u', v)]) v" using isPath_tail by simp
  thus ?case by blast
qed
    
lemma rtci_isPath: "(v, u) \<in> (E\<inverse>)\<^sup>* \<Longrightarrow> (\<exists>p. isPath u p v)"
proof -
  assume "(v,u)\<in>(E\<inverse>)\<^sup>*" 
  hence "(u,v)\<in>E\<^sup>*" by (rule rtrancl_converseD)
  thus ?thesis by (rule rtc_isPath)
qed      
  
lemma isPath_ex_edge1: 
  assumes "isPath u p v"
  assumes "(u1, v1) \<in> set p"
  assumes "u1 \<noteq> u"
  shows "\<exists>u2. (u2, u1) \<in> set p"
proof -
  obtain w1 w2 where obt1: "p = w1 @ [(u1, v1)] @ w2" using assms(2)
    by (metis append_Cons append_Nil in_set_conv_decomp_first)
  then have "isPath u w1 u1" using assms(1) isPath_append by auto
  have "w1 \<noteq> []"
    proof (rule ccontr)
      assume "\<not> w1 \<noteq> []"
      then have "u = u1" using \<open>isPath u w1 u1\<close> by (metis isPath.simps(1))
      thus "False" using assms(3) by blast
    qed
  then obtain e w1' where obt2:"w1 = w1' @ [e]" by (metis append_butlast_last_id)
  then obtain u2 where "e = (u2, u1)" 
    using \<open>isPath u w1 u1\<close> isPath_tail by (metis prod.collapse)
  then have "p = w1' @ (u2, u1) # (u1, v1) # w2" using obt1 obt2 by auto 
  thus ?thesis by auto
qed

lemma isPath_ex_edge2: 
  assumes "isPath u p v"
  assumes "(u1, v1) \<in> set p"
  assumes "v1 \<noteq> v"
  shows "\<exists>v2. (v1, v2) \<in> set p"
proof -
  obtain w1 w2 where obt1: "p = w1 @ [(u1, v1)] @ w2" using assms(2)
    by (metis append_Cons append_Nil in_set_conv_decomp_first)
  then have "isPath v1 w2 v" using assms(1) isPath_append by auto
  have "w2 \<noteq> []"
    proof (rule ccontr)
      assume "\<not> w2 \<noteq> []"
      then have "v = v1" using \<open>isPath v1 w2 v\<close> by (metis isPath.simps(1))
      thus "False" using assms(3) by blast
    qed
  then obtain e w2' where obt2:"w2 =  e # w2'" by (metis neq_Nil_conv)
  then obtain v2 where "e = (v1, v2)" 
    using \<open>isPath v1 w2 v\<close> isPath_head by (metis prod.collapse)
  then have "p = w1 @ (u1, v1) # (v1, v2) # w2'" using obt1 obt2 by auto
  thus ?thesis by auto
qed

subsubsection \<open>Vertices of Paths\<close>

lemma (in Graph) pathVertices_fwd_simps[simp]: 
  "pathVertices_fwd s ([]) = [s]"  
  "pathVertices_fwd s (e#p) = s#pathVertices_fwd (snd e) p"  
  "pathVertices_fwd s (p@[e]) = pathVertices_fwd s p@[snd e]"
  "pathVertices_fwd s (p1@e#p2) 
    = pathVertices_fwd s p1 @ pathVertices_fwd (snd e) p2"
  "s\<in>set (pathVertices_fwd s p)"
  by (auto simp: pathVertices_fwd_def)

lemma pathVertices_alt: "p \<noteq> [] 
    \<Longrightarrow> pathVertices u p = map fst p @ [snd (last p)]"
  by (induction p arbitrary: u) auto

lemma pathVertices_singleton_iff[simp]: "pathVertices s p = [u] \<longleftrightarrow> (p=[] \<and> s=u)"
  apply (cases p rule: rev_cases)
  apply (auto simp: pathVertices_alt)
  done

lemma length_pathVertices_eq[simp]: "length (pathVertices u p) = length p + 1"
  apply (cases "p=[]")
  apply (auto simp: pathVertices_alt)
  done

lemma pathVertices_edgeset: "\<lbrakk>u\<in>V; isPath u p v\<rbrakk> \<Longrightarrow> set (pathVertices u p) \<subseteq> V"
  apply (cases p rule: rev_cases; simp)
  using isPath_edgeset[of u p v]
  apply (fastforce simp: pathVertices_alt V_def)
  done

lemma pathVertices_append: "pathVertices u (p1 @ p2) = 
butlast (pathVertices u p1) @ pathVertices (last (pathVertices u p1)) p2"
proof (induction p1 arbitrary: u)
  case Nil
    thus ?case by auto
next
  case (Cons e es)
  have "pathVertices u ((e # es) @ p2) =  fst e # pathVertices (snd e) (es @ p2)"
    by (metis Graph.pathVertices.simps(2) append_Cons)
  moreover have "pathVertices (snd e) (es @ p2) 
    = butlast (pathVertices (snd e) es) 
      @ pathVertices (last (pathVertices (snd e) es)) p2" 
    using Cons.IH by auto
  moreover have "fst e # butlast (pathVertices (snd e) es) = 
    butlast (fst e # pathVertices (snd e) es)" 
    by (metis Graph.pathVertices.simps(1)
        Graph.pathVertices_alt Nil_is_append_conv butlast.simps(2) 
        list.distinct(1))
  moreover have "fst e # pathVertices (snd e) es = pathVertices u (e # es)"
    by (metis Graph.pathVertices.simps(2))
  moreover have "last (pathVertices (snd e) es) = last (pathVertices u (e # es))"
    by (metis Graph.pathVertices.simps(1) Graph.pathVertices_alt 
    last.simps last_snoc list.distinct(1))
  ultimately show ?case by (metis append_Cons)
qed

lemma split_path_at_vertex: 
  assumes "u\<in>set (pathVertices_fwd s p)"
  assumes "isPath s p t"
  obtains p1 p2 where "p=p1@p2" "isPath s p1 u" "isPath u p2 t"
  using assms
  apply -
  (*unfolding pathVertices_fwd*)
  unfolding pathVertices_fwd_def
  apply (auto simp: in_set_conv_decomp isPath_append) 
  apply force
  by (metis Graph.isPath_append_edge append_Cons append_Nil append_assoc)


lemma split_path_at_vertex_complete: 
  assumes "isPath s p t" "pathVertices_fwd s p = pv1@u#pv2" 
  obtains p1 p2 where 
    "p=p1@p2" 
    "isPath s p1 u" "pathVertices_fwd s p1 = pv1@[u]" 
    "isPath u p2 t" "pathVertices_fwd u p2 = u#pv2" 
proof -
  from assms have PV: "pathVertices s p = pv1@u#pv2" 
    by (simp add: pathVertices_fwd)
  then obtain p1 p2 where 
    "p=p1@p2" 
    "isPath s p1 u" "pathVertices s p1 = pv1@[u]" 
    "isPath u p2 t" "pathVertices u p2 = u#pv2"
  proof -
    show thesis
    using assms(1) PV
    apply (cases p rule: rev_cases; clarsimp simp: pathVertices_alt)
      apply (rule that[of "[]" "[]"]; simp add: Cons_eq_append_conv)

      apply (cases pv2; clarsimp)
      apply (rule that[of p "[]"]; 
        auto simp add: isPath_append pathVertices_alt
      )  
      apply (clarsimp simp: append_eq_append_conv2;
        auto elim!: map_eq_appendE append_eq_Cons_conv[THEN iffD1, elim_format]
            simp: isPath_append)
      subgoal for \<dots> l
        apply (erule that) 
        apply auto [4]
        apply (case_tac l rule: rev_cases; 
          auto simp add: pathVertices_alt isPath_append)
        done

      subgoal for \<dots> l
        apply (erule that) 
        apply auto [4]
        apply (case_tac l rule: rev_cases; 
          auto simp add: pathVertices_alt isPath_append)
        done

      subgoal for \<dots> l u1 u2 u3
        apply (erule that)  
        apply auto [4]
        apply (case_tac l rule: rev_cases; 
          auto simp add: pathVertices_alt isPath_append)
        apply (auto simp: isPath_append) []
        apply (auto simp: pathVertices_alt) []
        done
        
        apply (erule that) apply(auto simp add: Cons_eq_append_conv) [4]
        subgoal for \<dots> l
          by (case_tac l rule: rev_cases; 
            auto simp add: pathVertices_alt isPath_append)
      done
  qed
  thus ?thesis apply - unfolding pathVertices_fwd using that .
qed

lemma isPath_fwd_cases: 
  assumes "isPath s p t"
  obtains "p=[]" "t=s"
    | p' u where "p=(s,u)#p'" "(s,u)\<in>E" "isPath u p' t"
    using assms by (cases p) (auto)

lemma isPath_bwd_cases: 
  assumes "isPath s p t"
  obtains "p=[]" "t=s"
    | p' u where "p=p'@[(u,t)]" "isPath s p' u" "(u,t)\<in>E"
    using assms by (cases p rule: rev_cases) (auto simp: split_path_simps)


lemma pathVertices_edge: "isPath s p t \<Longrightarrow> e \<in> set p \<Longrightarrow> 
  \<exists>vs1 vs2. pathVertices_fwd s p = vs1 @ fst e # snd e # vs2"
  apply (cases e)
  apply (auto simp: in_set_conv_decomp split_path_simps)
  apply (erule isPath_bwd_cases[where s=s]; auto)
  apply (erule isPath_fwd_cases[where t=t]; auto)
  apply (erule isPath_fwd_cases[where t=t]; auto)
  done  


(* TODO: Really needed? *)
lemma pathVertices_edge_old: "isPath u p v \<Longrightarrow> e \<in> set p \<Longrightarrow> 
  \<exists>vs1 vs2. pathVertices u p = vs1 @ fst e # snd e # vs2"
  unfolding pathVertices_fwd
  by (rule pathVertices_edge)

subsubsection \<open>Reachability\<close>

lemma connected_refl[simp, intro!]: "connected v v" 
  unfolding connected_def by (force intro: exI[where x="[]"])

lemma connected_append_edge: "connected u v \<Longrightarrow> (v,w)\<in>E \<Longrightarrow> connected u w"
  unfolding connected_def by (auto intro: isPath_append_edge)

lemma connected_inV_iff: "\<lbrakk>connected u v\<rbrakk> \<Longrightarrow> v\<in>V \<longleftrightarrow> u\<in>V"
  apply (auto simp: connected_def)
  apply (case_tac p; auto simp: V_def) []
  apply (case_tac p rule: rev_cases; auto simp: isPath_append V_def) []
  done

lemma connected_edgeRtc: "connected u v \<longleftrightarrow> (u, v) \<in> E\<^sup>*"  
  using isPath_rtc rtc_isPath
  unfolding connected_def by blast

lemma reachable_ss_V: "s \<in> V \<Longrightarrow> reachableNodes s \<subseteq> V"
proof
  assume asm: "s \<in> V"
  fix x
  assume "x \<in> reachableNodes s"
  then obtain p where "x \<in> {v. isPath s p v}"
    unfolding reachableNodes_def connected_def by blast
  thus "x \<in> V" using asm
    by (induction p arbitrary: s) (auto simp: isPath_head V_alt) 
qed

lemma reachableNodes_E_closed: "E``reachableNodes s \<subseteq> reachableNodes s"  
  unfolding reachableNodes_def by (auto intro: connected_append_edge)

corollary reachableNodes_append_edge: 
  "u\<in>reachableNodes s \<Longrightarrow> (u,v)\<in>E \<Longrightarrow> v\<in>reachableNodes s"
  using reachableNodes_E_closed by blast


subsubsection \<open>Simple Paths\<close>

lemma isSimplePath_fwd: "isSimplePath s p t 
  \<longleftrightarrow> isPath s p t \<and> distinct (pathVertices_fwd s p)"  
  by (auto simp: isSimplePath_def pathVertices_fwd)

lemma isSimplePath_singelton[split_path_simps]: 
  "isSimplePath u [e] v \<longleftrightarrow> (e=(u,v) \<and> u\<noteq>v \<and> (u,v)\<in>E)"
  by (auto simp: isSimplePath_def isPath_head)

lemma (in Graph) isSimplePath_append[split_path_simps]: 
  "isSimplePath s (p1@p2) t 
    \<longleftrightarrow> (\<exists>u. 
      isSimplePath s p1 u 
    \<and> isSimplePath u p2 t 
    \<and> set (pathVertices_fwd s p1) \<inter> set (pathVertices_fwd u p2) = {u})"  
  (is "_ \<longleftrightarrow> ?R")
  unfolding isSimplePath_fwd
  apply (cases p1 rule: rev_cases; simp; cases p2; simp)
  by (auto simp: split_path_simps)
  
lemma (in Graph) isSimplePath_cons[split_path_simps]: 
  "isSimplePath s (e#p) t 
  \<longleftrightarrow> (\<exists>u. e=(s,u) \<and> s\<noteq>u \<and> (s,u)\<in>E 
        \<and> isSimplePath u p t \<and> s\<notin>set (pathVertices_fwd u p))"
  using isSimplePath_append[of s "[e]" p t, simplified]
  by (auto simp: split_path_simps)

lemma (in Finite_Graph) simplePath_length_less_V:
  assumes UIV: "u\<in>V"
  assumes P: "isSimplePath u p v" 
  shows "length p < card V"
proof -
  from P have 1: "isPath u p v" and 2: "distinct (pathVertices u p)"
    by (auto simp: isSimplePath_def)
  from pathVertices_edgeset[OF UIV 1] have "set (pathVertices u p) \<subseteq> V" .
  with 2 finite_V have "length (pathVertices u p) \<le> card V"
    using distinct_card card_mono by metis
  hence "length p + 1 \<le> card V" by simp
  thus ?thesis by auto
qed      

lemma split_simple_path: "isSimplePath u (p1@p2) v 
  \<Longrightarrow> (\<exists>w. isSimplePath u p1 w \<and> isSimplePath w p2 v)"
  apply (auto simp: isSimplePath_def isPath_append)
  apply (rule exI; intro conjI; assumption?)
  apply (cases p1 rule: rev_cases) []
  apply simp
  apply (cases p2)
  apply simp
  apply (clarsimp simp: pathVertices_alt isPath_append)

  apply (cases p1 rule: rev_cases) []
  apply simp
  apply (cases p2  rule: rev_cases)
  apply simp
  apply (clarsimp simp: pathVertices_alt isPath_append)
  done  
      
lemma simplePath_empty_conv[simp]: "isSimplePath s [] t \<longleftrightarrow> s=t"
  by (auto simp: isSimplePath_def)

lemma simplePath_same_conv[simp]: "isSimplePath s p s \<longleftrightarrow> p=[]"  
  apply rule
  apply (cases p; simp)
  apply (rename_tac e pp)
  apply (case_tac pp rule: rev_cases; simp)
  apply (auto simp: isSimplePath_def pathVertices_alt isPath_append) [2]
  apply simp
  done

lemma isSPath_pathLE: "isPath s p t \<Longrightarrow> \<exists>p'. isSimplePath s p' t"
proof (induction p rule: length_induct)
  case (1 p)
  hence IH: "\<And>p'. \<lbrakk>length p' < length p; isPath s p' t\<rbrakk> 
    \<Longrightarrow> \<exists>p'. isSimplePath s p' t"
    and PATH: "isPath s p t"
    by auto

  show "\<exists>p. isSimplePath s p t"  
  proof cases
    assume "distinct (pathVertices_fwd s p)"
    thus ?thesis using PATH by (auto simp: isSimplePath_fwd)
  next
    assume "\<not>(distinct (pathVertices_fwd s p))"  
    then obtain pv1 pv2 pv3 u where "pathVertices_fwd s p = pv1@u#pv2@u#pv3" 
      by (auto dest: not_distinct_decomp)
    then obtain p1 p2 p3 where
      "p = p1@p2@p3" "p2\<noteq>[]" "isPath s p1 u" "isPath u p3 t"
      using PATH
      apply -
      apply (erule (1) split_path_at_vertex_complete[where s=s]; simp)
      apply (erule split_path_at_vertex_complete[of _ _ t "u#pv2" u pv3]; simp)
      apply (auto intro: that)
      done
    hence "length (p1@p3) < length p" "isPath s (p1@p3) t"  
      by (auto simp: split_path_simps)
    thus ?case by (rule IH)
  qed
qed  
      

lemma isSPath_no_selfloop: "isSimplePath u p v \<Longrightarrow> (u1, u1) \<notin> set p"
  apply (rule ccontr)
  apply (auto simp: in_set_conv_decomp split_path_simps)
  done

lemma isSPath_sg_outgoing: "\<lbrakk>isSimplePath u p v; (u1, v1) \<in> set p; v1 \<noteq> v2\<rbrakk> 
  \<Longrightarrow> (u1, v2) \<notin> set p"
  by (auto simp: in_set_conv_decomp isSimplePath_def pathVertices_alt 
      append_eq_append_conv2 Cons_eq_append_conv append_eq_Cons_conv)

lemma isSPath_sg_incoming: 
  "\<lbrakk>isSimplePath u p v; (u1, v1) \<in> set p; u1 \<noteq> u2\<rbrakk> \<Longrightarrow> (u2, v1) \<notin> set p"
  by (auto simp: in_set_conv_decomp isSimplePath_fwd pathVertices_fwd_def
      append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv)

lemma isSPath_nt_parallel:
  assumes SP: "isSimplePath s p t"
  assumes EIP: "e\<in>set p"
  shows "prod.swap e \<notin> set p"
proof -  
  from SP have P: "isPath s p t" and D: "distinct (pathVertices_fwd s p)"
    by (auto simp: isSimplePath_fwd)

  show "prod.swap e \<notin> set p"  
    apply (cases e) using D EIP
    by(auto dest!: pathVertices_edge[OF P] simp add: append_eq_append_conv2 Cons_eq_append_conv append_eq_Cons_conv)

qed

lemma isSPath_nt_parallel_old: 
  "isSimplePath u p v \<Longrightarrow> (\<forall>(u, v) \<in> set p. (v, u) \<notin> set p)"
  using isSPath_nt_parallel[of u p v] by auto

corollary isSPath_nt_parallel_pf: 
  "isSimplePath s p t \<Longrightarrow> set p \<inter> (set p)\<inverse> = {}"
  by (auto dest: isSPath_nt_parallel)
      
lemma isSPath_distinct: "isSimplePath u p v \<Longrightarrow> distinct p"
  apply (rule ccontr)
  apply (auto dest!: not_distinct_decomp simp: split_path_simps)
  done

text \<open>Edges adjacent to a node that does not lie on a path 
  are not contained in that path:\<close>  
lemma adjacent_edges_not_on_path:
  assumes PATH: "isPath s p t"
  assumes VNV: "v\<notin>set (pathVertices_fwd s p)"
  shows "adjacent v \<inter> set p = {}" 
proof -
  from VNV have "\<forall>u. (u,v)\<notin>set p \<and> (v,u)\<notin>set p"
    by (auto dest: pathVertices_edge[OF PATH])
  thus "adjacent v \<inter> set p = {}"
    by (auto simp: incoming_def outgoing_def adjacent_def)
qed    

corollary 
  assumes "isPath s p t"
  assumes "v\<notin>set (pathVertices_fwd s p)"
  shows incoming_edges_not_on_path: "incoming v \<inter> set p = {}" 
    and outgoing_edges_not_on_path: "outgoing v \<inter> set p = {}"
  using adjacent_edges_not_on_path[OF assms]
  unfolding adjacent_def by auto

text \<open>A simple path over a vertex can be split at this vertex, 
  and there are exactly two edges on the path touching this vertex.\<close>  
lemma adjacent_edges_on_simple_path:
  assumes SPATH: "isSimplePath s p t"
  assumes VNV: "v\<in>set (pathVertices_fwd s p)" "v\<noteq>s" "v\<noteq>t"
  obtains p1 u w p2 where 
    "p = p1@(u,v)#(v,w)#p2" 
    "incoming v \<inter> set p = {(u,v)}" 
    "outgoing v \<inter> set p = {(v,w)}"
proof -
  from SPATH have 
    PATH: "isPath s p t" and 
    DIST: "distinct (pathVertices_fwd s p)" 
    by (auto simp: isSimplePath_def pathVertices_fwd)
  from split_path_at_vertex[OF VNV(1) PATH] obtain p1 p2 where 
    [simp]: "p=p1@p2" and P1: "isPath s p1 v" and P2: "isPath v p2 t" .
  from \<open>v\<noteq>s\<close> P1 obtain p1' u where 
    [simp]: "p1=p1'@[(u,v)]" and P1': "isPath s p1' u" and UV: "(u,v)\<in>E"
    by (cases p1 rule: rev_cases) (auto simp: split_path_simps)
  from \<open>v\<noteq>t\<close> P2 obtain w p2' where 
    [simp]: "p2=(v,w)#p2'" and VW: "(v,w)\<in>E" and P2': "isPath w p2' t"
    by (cases p2) (auto)
  show thesis
    apply (rule that[of p1' u w p2'])
    apply simp
    using 
      isSPath_sg_outgoing[OF SPATH, of v w] 
      isSPath_sg_incoming[OF SPATH, of u v]
      isPath_edgeset[OF PATH]
    apply (fastforce simp: incoming_def outgoing_def)+
    done
qed

subsubsection \<open>Distance\<close>

lemma connected_by_dist: "connected v v' = (\<exists>d. dist v d v')"
  by (auto simp: dist_def connected_def)

lemma isPath_distD: "isPath u p v \<Longrightarrow> dist u (length p) v"
  by (auto simp: dist_def)

lemma
  shows connected_distI[intro]: "dist v d v' \<Longrightarrow> connected v v'"
    (*and connectedI_succ: "connected v v' \<Longrightarrow> (v',v'') \<in> E \<Longrightarrow> connected v v''"*)
  by (auto simp: dist_def connected_def intro: isPath_append_edge)
  
  
lemma min_distI2: 
  "\<lbrakk>connected v v'; \<And>d. \<lbrakk>dist v d v'; \<And>d'. dist v d' v' \<Longrightarrow> d \<le> d'\<rbrakk> \<Longrightarrow> Q d\<rbrakk> 
    \<Longrightarrow> Q (min_dist v v')"
  unfolding min_dist_def
  apply (rule LeastI2_wellorder[where Q=Q and a="SOME d. dist v d v'"])
  apply (auto simp: connected_by_dist intro: someI)
  done

lemma min_distI_eq:
  "\<lbrakk> dist v d v'; \<And>d'. dist v d' v' \<Longrightarrow> d \<le> d' \<rbrakk> \<Longrightarrow> min_dist v v' = d"
  by (force intro: min_distI2 simp: connected_by_dist)

text \<open>Two nodes are connected by a path of length \<open>0\<close>, 
  iff they are equal.\<close>
lemma dist_z_iff[simp]: "dist v 0 v' \<longleftrightarrow> v'=v"
  by (auto simp: dist_def)


lemma dist_z[simp, intro!]: "dist v 0 v" by simp
lemma dist_suc: "\<lbrakk>dist v d v'; (v',v'')\<in>E\<rbrakk> \<Longrightarrow> dist v (Suc d) v''"
  by (auto simp: dist_def intro: isPath_append_edge)

lemma dist_cases[case_names dist_z dist_suc, consumes 1, cases pred]:
  assumes "dist v d v'"
  obtains "v=v'" "d=0"
   | vh dd where "d=Suc dd" "dist v dd vh" "(vh,v')\<in>E"
  using assms 
  apply (cases d; clarsimp simp add: dist_def)
  subgoal for \<dots> p by(cases p rule: rev_cases)(fastforce simp add: isPath_append)+
  done


text \<open>The same holds for \<open>min_dist\<close>, i.e., 
  the shortest path between two nodes has length \<open>0\<close>, 
  iff these nodes are equal.\<close>
lemma min_dist_z[simp]: "min_dist v v = 0"
  by (rule min_distI2) auto

lemma min_dist_z_iff[simp]: "connected v v' \<Longrightarrow> min_dist v v' = 0 \<longleftrightarrow> v'=v" 
  by (rule min_distI2) (auto)
  
lemma min_dist_is_dist: "connected v v' \<Longrightarrow> dist v (min_dist v v') v'"
  by (auto intro: min_distI2)
lemma min_dist_minD: "dist v d v' \<Longrightarrow> min_dist v v' \<le> d"
  by (auto intro: min_distI2)

text \<open>We also provide introduction and destruction rules for the
  pattern \<open>min_dist v v' = Suc d\<close>.
\<close>

lemma min_dist_succ: 
  "\<lbrakk> connected v v'; (v',v'') \<in> E \<rbrakk> \<Longrightarrow> min_dist v v'' \<le> Suc (min_dist v v') "
  apply (rule min_distI2[where v'=v'])
  apply (auto intro!: min_dist_minD intro: dist_suc)
  done

lemma min_dist_suc:
  assumes c: "connected v v'" "min_dist v v' = Suc d"
  shows "\<exists>v''. connected v v'' \<and> (v'',v') \<in> E \<and> min_dist v v'' = d"
proof -
  from min_dist_is_dist[OF c(1)]
  have "min_dist v v' = Suc d \<longrightarrow> ?thesis"
  proof cases
    case (dist_suc v'' d') then show ?thesis
      using min_dist_succ[of v v'' v'] min_dist_minD[of v d v'']
      by (auto simp: connected_distI)
  qed simp
  with c show ?thesis by simp
qed

text \<open>
  If there is a node with a shortest path of length \<open>d\<close>, 
  then, for any \<open>d'<d\<close>, there is also a node with a shortest path
  of length \<open>d'\<close>.
\<close>
lemma min_dist_less:
  assumes "connected src v" "min_dist src v = d" and "d' < d"
  shows "\<exists>v'. connected src v' \<and> min_dist src v' = d'"
  using assms
proof (induct d arbitrary: v)
  case (Suc d) with min_dist_suc[of src v] show ?case
    by (cases "d' = d") auto
qed auto

text \<open>
  Lemma \<open>min_dist_less\<close> can be weakened to \<open>d'\<le>d\<close>.
\<close>

corollary min_dist_le:
  assumes c: "connected src v" and d': "d' \<le> min_dist src v"
  shows "\<exists>v'. connected src v' \<and> min_dist src v' = d'"
  using min_dist_less[OF c, of "min_dist src v" d'] d' c
  by (auto simp: le_less)


lemma dist_trans[trans]: "dist u d1 w \<Longrightarrow> dist w d2 v \<Longrightarrow> dist u (d1+d2) v"  
  apply (clarsimp simp: dist_def)
  apply (rename_tac p1 p2)
  apply (rule_tac x="p1@p2" in exI)
  by (auto simp: isPath_append)


lemma min_dist_split:
  assumes D1: "dist u d1 w" and D2: "dist w d2 v" and MIN: "min_dist u v = d1+d2"
  shows "min_dist u w = d1" "min_dist w v = d2"
  apply (metis assms ab_semigroup_add_class.add.commute add_le_cancel_left 
    dist_trans min_distI_eq min_dist_minD)
  by (metis assms add_le_cancel_left dist_trans min_distI_eq min_dist_minD)
  
lemma \<comment> \<open>Manual proof\<close>
  assumes D1: "dist u d1 w" and D2: "dist w d2 v" and MIN: "min_dist u v = d1+d2"
  shows "min_dist u w = d1" "min_dist w v = d2"
proof -
  from min_dist_minD[OF \<open>dist u d1 w\<close>] have "min_dist u w \<le> d1" .
  moreover {
    have "dist u (min_dist u w) w"
      apply (rule min_dist_is_dist)
      using D1 by auto
    also note D2
    finally have "dist u (min_dist u w + d2) v" .
    moreover assume "min_dist u w < d1"
    moreover note MIN
    ultimately have False by (auto dest: min_dist_minD)
  } ultimately show "min_dist u w = d1"
    unfolding not_less[symmetric] using nat_neq_iff by blast

  from min_dist_minD[OF \<open>dist w d2 v\<close>] have "min_dist w v \<le> d2" .
  moreover {
    note D1
    also have "dist w (min_dist w v) v"
      apply (rule min_dist_is_dist)
      using D2 by auto
    finally have "dist u (d1 + min_dist w v) v" .
    moreover assume "min_dist w v < d2"
    moreover note MIN
    ultimately have False by (auto dest: min_dist_minD)
  } ultimately show "min_dist w v = d2"
    unfolding not_less[symmetric] using nat_neq_iff by blast
qed    

subsubsection \<open>Shortest Paths\<close>

text \<open>Characterization of shortest path in terms of minimum distance\<close>
lemma isShortestPath_min_dist_def: 
  "isShortestPath u p v \<longleftrightarrow> isPath u p v \<and> length p = min_dist u v"  
  unfolding isShortestPath_def min_dist_def dist_def
  apply (rule iffI; clarsimp)
  apply (rule Least_equality[symmetric]; auto; fail)
  apply (rule Least_le; auto; fail)
  done      

lemma obtain_shortest_path: 
  assumes CONN: "connected u v"  
  obtains p where "isShortestPath u p v"
  using min_dist_is_dist[OF CONN]
  unfolding dist_def isShortestPath_min_dist_def
  by blast

lemma shortestPath_is_simple:
  assumes "isShortestPath s p t"
  shows "isSimplePath s p t"
proof (rule ccontr)
  from assms have PATH: "isPath s p t" 
    and SHORTEST: "\<forall>p'. isPath s p' t \<longrightarrow> length p \<le> length p'"
    by (auto simp: isShortestPath_def)

  assume "\<not>isSimplePath s p t"  
  with PATH have "\<not>distinct (pathVertices_fwd s p)" 
    by (auto simp: isSimplePath_fwd)

  then obtain pv1 u pv2 pv3 where PV: "pathVertices_fwd s p = pv1@u#pv2@u#pv3" 
    by (auto dest: not_distinct_decomp)

  from split_path_at_vertex_complete[OF PATH PV] obtain p1 p23 where
    [simp]: "p=p1@p23" and 
      P1: "isPath s p1 u" "pathVertices_fwd s p1 = pv1@[u]" and
      P23: "isPath u p23 t" "pathVertices_fwd u p23 = (u#pv2)@u#pv3"
      by auto
      
  from split_path_at_vertex_complete[OF P23] obtain p2 p3 where
    [simp]: "p23 = p2@p3" and
    P2: "isPath u p2 u" "pathVertices_fwd u p2 = u#pv2@[u]" and
    P3: "isPath u p3 t" "pathVertices_fwd u p3 = u#pv3"
    by auto

  from P1(1) P3(1) have SHORTER_PATH: "isPath s (p1@p3) t" 
    by (auto simp: isPath_append)
  
  from P2 have "p2\<noteq>[]" by auto
  hence LESS: "length (p1@p3) < length p" by auto
  with SHORTER_PATH SHORTEST show False by auto
qed    

text \<open>We provide yet another characterization of shortest paths:\<close>
lemma isShortestPath_alt: 
  "isShortestPath u p v \<longleftrightarrow> isSimplePath u p v \<and> length p = min_dist u v"
  using shortestPath_is_simple isShortestPath_min_dist_def
  unfolding isSimplePath_def by auto

lemma shortestPath_is_path: "isShortestPath u p v \<Longrightarrow> isPath u p v"
  by (auto simp: isShortestPath_def)
  
lemma split_shortest_path: "isShortestPath u (p1@p2) v 
  \<Longrightarrow> (\<exists>w. isShortestPath u p1 w \<and> isShortestPath w p2 v)"
  apply (auto simp: isShortestPath_min_dist_def isPath_append)
  apply (rule exI; intro conjI; assumption?)
  apply (drule isPath_distD)+ using min_dist_split apply auto []
  apply (drule isPath_distD)+ using min_dist_split apply auto []
  done

text \<open>Edges in a shortest path connect nodes with increasing 
  minimum distance from the source\<close>
lemma isShortestPath_level_edge:  
  assumes SP: "isShortestPath s p t" 
  assumes EIP: "(u,v)\<in>set p"
  shows 
    "connected s u" "connected u v" "connected v t" and
    "min_dist s v = min_dist s u + 1" (is ?G1) and
    "min_dist u t = 1 + min_dist v t" (is ?G2) and
    "min_dist s t = min_dist s u + 1 + min_dist v t" (is ?G3) 
proof -  
  \<comment> \<open>Split the original path at the edge\<close>
  from EIP obtain p1 p2 where [simp]: "p=p1@(u,v)#p2"
    by (auto simp: in_set_conv_decomp)
  from \<open>isShortestPath s p t\<close> have 
    MIN: "min_dist s t = length p" and 
      P: "isPath s p t" and 
     DV: "distinct (pathVertices s p)"
    by (auto simp: isShortestPath_alt isSimplePath_def)
  from P have DISTS: "dist s (length p1) u" "dist u 1 v" "dist v (length p2) t"
    by (auto simp: isPath_append dist_def intro: exI[where x="[(u,v)]"])
    
  from DISTS show "connected s u" "connected u v" "connected v t" by auto

  \<comment> \<open>Express the minimum distances in terms of the split original path\<close>  
  from MIN have MIN': "min_dist s t = length p1 + 1 + length p2" by auto
  
  from min_dist_split[OF dist_trans[OF DISTS(1,2)] DISTS(3) MIN'] have
      MDSV: "min_dist s v = length p1 + 1" and 
    [simp]: "length p2 = min_dist v t" 
    by simp_all
  from min_dist_split[OF DISTS(1) dist_trans[OF DISTS(2,3)]] MIN' have
      MDUT: "min_dist u t = 1 + length p2" and 
    [simp]: "length p1 = min_dist s u" 
    by simp_all

  from MDSV MDUT MIN' show ?G1 ?G2 ?G3 by auto  
qed  

end \<comment> \<open>Graph\<close>

context Finite_Graph begin

text \<open>In a finite graph, the length of a shortest path is less 
  than the number of nodes\<close>  
lemma isShortestPath_length_less_V:   
  assumes SV: "s\<in>V"
  assumes PATH: "isShortestPath s p t"
  shows "length p < card V"
  using simplePath_length_less_V[OF SV]
  using shortestPath_is_simple[OF PATH] .

corollary min_dist_less_V:
  assumes SV: "s\<in>V"
  assumes CONN: "connected s t"
  shows "min_dist s t < card V"
  apply (rule obtain_shortest_path[OF CONN])
  apply (frule isShortestPath_length_less_V[OF SV])
  unfolding isShortestPath_min_dist_def by auto

end \<comment> \<open>Finite_Graph\<close>

end \<comment> \<open>Theory\<close>
