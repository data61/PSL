section \<open>Abstract Prim Algorithm\<close>
theory Prim_Abstract
imports 
  Main 
  Common
  Undirected_Graph
  "HOL-Eisbach.Eisbach"
begin
    
subsection \<open>Generic Algorithm: Light Edges\label{sec:generic_mst}\<close>

definition "is_subset_MST w g A \<equiv> \<exists>t. is_MST w g t \<and> A \<subseteq> edges t"  

lemma is_subset_MST_empty[simp]: "connected g \<Longrightarrow> is_subset_MST w g {}"
  using exists_MST unfolding is_subset_MST_def by blast

text \<open>We fix a start node and a weighted graph\<close>
locale Prim =
  fixes w :: "'v set \<Rightarrow> nat" and g :: "'v ugraph" and r :: 'v
begin

text \<open>Reachable part of the graph\<close>
definition "rg \<equiv> component_of g r"

lemma reachable_connected[simp, intro!]: "connected rg" 
  unfolding rg_def by auto
  
lemma reachable_edges_subset: "edges rg \<subseteq> edges g" 
  unfolding rg_def by (rule component_edges_subset)

definition "light_edge C u v 
  \<equiv>   u\<in>C \<and> v\<notin>C \<and> (u,v)\<in>edges rg 
    \<and> (\<forall>(u',v')\<in>edges rg \<inter> C\<times>-C. w {u,v} \<le> w {u',v'})"  

definition "respects_cut A C \<equiv> A \<subseteq> C\<times>C \<union> (-C)\<times>(-C)"
    
lemma light_edge_is_safe:
  fixes A :: "('v\<times>'v) set" and C :: "'v set"
  assumes subset_MST: "is_subset_MST w rg A"
  assumes respects_cut: "respects_cut A C"
  assumes light_edge: "light_edge C u v"
  shows "is_subset_MST w rg ({(v,u)} \<union> A)"
proof -
  have crossing_edge: "u\<in>C" "v\<notin>C" "(u,v)\<in>edges rg"
    and min_edge: "\<forall>(u',v')\<in>edges rg \<inter> C\<times>-C. w {u,v} \<le> w {u',v'}"
    using light_edge unfolding light_edge_def by auto

  from subset_MST obtain T where T: "is_MST w rg T" "A \<subseteq> edges T" 
    unfolding is_subset_MST_def by auto
  hence "tree T" "edges T \<subseteq> edges rg" "nodes T = nodes rg" 
    by (simp_all add: is_MST_def is_spanning_tree_def)
  hence "connected T" by(simp_all add: tree_def)
  show ?thesis
  proof cases
    assume "(u,v) \<in> edges T"
    thus ?thesis unfolding is_subset_MST_def using T by (auto simp: edges_sym')
  next
    assume "(u,v) \<notin> edges T" hence "(v,u)\<notin>edges T" by (auto simp: edges_sym')
    from \<open>(u,v)\<in>edges rg\<close> obtain p where p: "path T u p v" "simple p"
      by (metis connectedD \<open>connected T\<close> \<open>nodes T = nodes rg\<close> nodesI 
          rtrancl_edges_iff_path simplify_pathE)
      
    have [simp]: "u\<noteq>v" using crossing_edge by blast
      
    from find_crossing_edge_on_path[OF p(1), where P="\<lambda>x. x\<notin>C"] 
         crossing_edge(1,2)
    obtain x y p1 p2 where xy: "(x,y) \<in> set p" "x \<in> C" "y \<notin> C"
      and ux: "path (restrict_edges T (-{(x,y),(y,x)})) u p1 x" 
      and yv: "path (restrict_edges T (-{(x,y),(y,x)})) y p2 v"
      using path_change[OF crossing_edge(1,2) p] by blast
    have "(x,y) \<in> edges T" 
      by (meson contra_subsetD p(1) path_edges xy(1))

    let ?E' = "edges T - {(x,y),(y,x)}"
      
    from split_tree[OF \<open>tree T\<close> \<open>(x,y)\<in>edges T\<close>]
      obtain T1 T2 where T12: 
        "tree T1" "tree T2" 
        and "nodes T1 \<inter> nodes T2 = {}" 
        and "nodes T = nodes T1 \<union> nodes T2"
        and "edges T1 \<union> edges T2 = ?E'"
        and "nodes T1 = { u . (x,u)\<in>?E'\<^sup>*}"
        and "nodes T2 = { u . (y,u)\<in>?E'\<^sup>*}"
        and "x\<in>nodes T1" "y\<in>nodes T2" .
    
    let ?T' = "ins_edge (u,v) (graph_join T1 T2)"    

    have "is_spanning_tree rg ?T'" proof -
      
      have E'_sym: "sym (?E'\<^sup>*)" 
        by (meson edgesT_diff_sng_inv_eq sym_conv_converse_eq sym_rtrancl)
      
      have "u\<in>nodes T1" 
        unfolding \<open>nodes T1 = _\<close>
        using path_rtrancl_edgesD[OF ux] by (auto dest: symD[OF E'_sym])
        
      have "v\<in>nodes T2" 
        unfolding \<open>nodes T2 = _\<close>
        using path_rtrancl_edgesD[OF yv] by auto
              
      have "tree ?T'" by (rule join_trees) fact+

      show "is_spanning_tree rg ?T'"
        unfolding is_spanning_tree_def
        using \<open>nodes T = nodes rg\<close> \<open>nodes T = nodes T1 \<union> nodes T2\<close>[symmetric] 
        using \<open>tree ?T'\<close> \<open>u\<noteq>v\<close>
        using \<open>edges T \<subseteq> edges rg\<close> \<open>edges T1 \<union> edges T2 = ?E'\<close>
        apply simp
        by (metis Diff_subset crossing_edge(3) edges_sym' insert_absorb 
              nodesI(2) subset_trans)
    qed
    moreover 
      
    have "weight w ?T' \<le> weight w T'" if "is_spanning_tree rg T'" for T'
    proof -
      have ww: "w {u,v} \<le> w{x,y}" 
        using min_edge \<open>(x,y)\<in>edges T\<close> \<open>edges T \<subseteq> edges rg\<close> \<open>x\<in>C\<close> \<open>y\<notin>C\<close>
        by blast
        
      have "weight w ?T' = weight w T - w {x,y} + w{u,v}"
        using \<open>(u, v) \<notin> edges T\<close> \<open>(x, y) \<in> edges T\<close> 
        using \<open>edges T1 \<union> edges T2 = edges T - {(x, y), (y, x)}\<close> \<open>u \<noteq> v\<close>
        by (smt Diff_eq Diff_subset add.commute contra_subsetD edges_join 
              edges_restrict_edges minus_inv_sym_aux sup.idem weight_cong 
              weight_del_edge weight_ins_edge)
      also have "\<dots> \<le> weight w T" 
        using weight_ge_edge[OF \<open>(x,y)\<in>edges T\<close>, of w] ww by auto
      also have "weight w T \<le> weight w T'" using T(1) \<open>is_spanning_tree rg T'\<close>
        unfolding is_MST_def by simp
      finally show ?thesis . 
    qed
    ultimately have "is_MST w rg ?T'" using is_MST_def by blast
    have "{(u,v),(v,u)} \<union> A \<subseteq> edges ?T'" 
      using T(2) respects_cut xy(2,3) \<open>edges T1 \<union> edges T2 = ?E'\<close>
      unfolding respects_cut_def 
      by auto
      
    with \<open>is_MST w rg ?T'\<close> show ?thesis unfolding is_subset_MST_def by force
  qed
qed        

end    
   
subsection \<open>Abstract Prim: Growing a Tree\label{sec:prim_algo}\<close>
context Prim begin 

text \<open>The current nodes\<close> 
definition "S A \<equiv> {r} \<union> fst`A \<union> snd`A"

lemma respects_cut': "A \<subseteq> S A \<times> S A"
  unfolding S_def by force

corollary respects_cut: "respects_cut A (S A)" 
  unfolding respects_cut_def using respects_cut' by auto
  
text \<open>Refined invariant: Adds connectedness of \<open>A\<close>\<close>
definition "prim_invar1 A \<equiv> is_subset_MST w rg A \<and> (\<forall>(u,v)\<in>A. (v,r)\<in>A\<^sup>*)"

text \<open>Measure: Number of nodes not in tree\<close>
definition "T_measure1 A = card (nodes rg - S A)"

end

text \<open>We use a locale that fixes a state and assumes the invariant\<close>
locale Prim_Invar1_loc = 
  Prim w g r for w g and r :: 'v +
  fixes A :: "('v\<times>'v) set"
  assumes invar1: "prim_invar1 A"
begin  
lemma subset_MST: "is_subset_MST w rg A" 
  using invar1 unfolding prim_invar1_def by auto
  
lemma A_connected: "(u,v)\<in>A \<Longrightarrow> (v,r)\<in>A\<^sup>*" 
  using invar1 unfolding prim_invar1_def by auto

lemma S_alt_def: "S A = {r} \<union> fst`A" 
  unfolding S_def
  apply (safe;simp)
  by (metis A_connected Domain_fst Not_Domain_rtrancl)

lemma finite_rem_nodes[simp,intro!]: "finite (nodes rg - S A)" by auto

lemma A_edges: "A \<subseteq> edges g"  
  using subset_MST
  by (meson is_MST_def is_spanning_tree_def is_subset_MST_def 
        reachable_edges_subset subset_eq)

lemma S_reachable: "S A \<subseteq> nodes rg"  
  unfolding S_alt_def
  by (smt DomainE Un_insert_left fst_eq_Domain insert_subset is_MST_def 
        is_spanning_tree_def is_subset_MST_def nodesI(1) nodes_of_component 
        reachable_nodes_refl rg_def subset_MST subset_iff sup_bot.left_neutral)
  
lemma S_edge_reachable: "\<lbrakk>u\<in>S A; (u,v)\<in>edges g \<rbrakk> \<Longrightarrow> (u,v)\<in>edges rg"  
  using S_reachable unfolding rg_def
  using reachable_nodes_step'(2) by fastforce
    
lemma edges_S_rg_edges: "edges g \<inter> S A\<times>-S A = edges rg \<inter> S A\<times>-S A"
  using S_edge_reachable reachable_edges_subset by auto
      
lemma T_measure1_less: "T_measure1 A < card (nodes rg)"
  unfolding T_measure1_def S_def
  by (metis Diff_subset S_def S_reachable Un_insert_left le_supE nodes_finite 
        psubsetI psubset_card_mono singletonI subset_Diff_insert)


lemma finite_A[simp, intro!]: "finite A"
  using A_edges finite_subset by auto

lemma finite_S[simp, intro!]: "finite (S A)" 
  using S_reachable rev_finite_subset by blast

(* TODO: Used? *)
lemma S_A_consistent[simp, intro!]: "nodes_edges_consistent (S A) (A\<union>A\<inverse>)"
  unfolding nodes_edges_consistent_def
  apply (intro conjI)
  subgoal by simp
  subgoal using A_edges irrefl_def by fastforce
  subgoal by (simp add: sym_Un_converse)
  using respects_cut' by auto
    
      
end

context Prim begin

lemma invar1_initial: "prim_invar1 {}"
  by (auto simp: is_subset_MST_def prim_invar1_def exists_MST)

lemma maintain_invar1:
  assumes invar: "prim_invar1 A"
  assumes light_edge: "light_edge (S A) u v"
  shows "prim_invar1 ({(v,u)}\<union>A) 
       \<and> T_measure1 ({(v,u)}\<union>A) < T_measure1 A" (is "?G1 \<and> ?G2")
proof

  from invar interpret Prim_Invar1_loc w g r A by unfold_locales

  from light_edge have "u\<in>S A" "v\<notin>S A" by (simp_all add: light_edge_def)
      
  show ?G1
    unfolding prim_invar1_def
  proof (intro conjI)
    show "is_subset_MST w rg ({(v, u)} \<union> A)"
      by (rule light_edge_is_safe[OF subset_MST respects_cut light_edge])
      
  next
    show "\<forall>(ua, va)\<in>{(v, u)} \<union> A. (va, r) \<in> ({(v, u)} \<union> A)\<^sup>*"
      apply safe
      subgoal
        using A_connected
        by (simp add: rtrancl_insert) 
           (metis DomainE S_alt_def converse_rtrancl_into_rtrancl \<open>u\<in>S A\<close> 
                    fst_eq_Domain insertE insert_is_Un rtrancl_eq_or_trancl)
      subgoal using A_connected by (simp add: rtrancl_insert)
      done
  qed
  then interpret N: Prim_Invar1_loc w g r "{(v,u)}\<union>A" by unfold_locales
  
  have "S A \<subset> S ({(v,u)}\<union>A)" using \<open>v\<notin>S A\<close>
    unfolding S_def by auto
  then show "?G2" unfolding T_measure1_def
    using S_reachable N.S_reachable
    by (auto intro!: psubset_card_mono)

qed  

lemma invar1_finish:
  assumes INV: "prim_invar1 A"
  assumes FIN: "edges g \<inter> S A\<times>-S A = {}"
  shows "is_MST w rg (graph {r} A)"
proof -
  from INV interpret Prim_Invar1_loc w g r A by unfold_locales

  from subset_MST obtain t where MST: "is_MST w rg t" and "A \<subseteq> edges t"
    unfolding is_subset_MST_def by auto
  
  have "S A = nodes t"
  proof safe
    fix u
    show "u\<in>S A \<Longrightarrow> u\<in>nodes t" using MST
      unfolding is_MST_def is_spanning_tree_def
      using S_reachable by auto
  next
    fix u
    assume "u\<in>nodes t"
    hence "u\<in>nodes rg"
      using MST is_MST_def is_spanning_tree_def by force
    hence 1: "(u,r)\<in>(edges rg)\<^sup>*" by (simp add: connectedD rg_def)
    have "r\<in>S A" by (simp add: S_def)
    show "u\<in>S A" proof (rule ccontr)
      assume "u\<notin>S A"
      from find_crossing_edge_rtrancl[where P="\<lambda>u. u\<in>S A", OF 1 \<open>u\<notin>S A\<close> \<open>r\<in>S A\<close>] 
        FIN reachable_edges_subset 
      show False
        by (smt ComplI IntI contra_subsetD edges_sym' emptyE mem_Sigma_iff)
        
    qed
  qed
  also have "nodes t = nodes rg" 
    using MST unfolding is_MST_def is_spanning_tree_def
    by auto
  finally have S_eq: "S A = nodes rg" .
  
  define t' where "t' = graph {r} A"
  
  have [simp]: "nodes t' = S A" and Et': "edges t' = (A\<union>A\<inverse>)" unfolding t'_def 
    using A_edges
    by (auto simp: graph_accs S_def)
  
  hence "edges t' \<subseteq> edges t"
    by (smt UnE \<open>A \<subseteq> edges t\<close> converseD edges_sym' subrelI subset_eq)
  
  have "is_spanning_tree rg t'"
  proof -
    have "connected t'"  
      apply rule
      apply (simp add: Et' S_def)
      apply safe
      apply ((simp add: A_connected converse_rtrancl_into_rtrancl 
                        in_rtrancl_UnI rtrancl_converse
             )+
      ) [4]
      apply simp_all [4]
      apply ((meson A_connected in_rtrancl_UnI r_into_rtrancl 
                rtrancl_converseI rtrancl_trans
             )+
      ) [4]
      done
  
    moreover have "cycle_free t'"
      by (meson MST \<open>edges t' \<subseteq> edges t\<close> cycle_free_antimono is_MST_def 
                is_spanning_tree_def tree_def)      
    moreover have "edges t' \<subseteq> edges rg"
      by (meson MST \<open>edges t' \<subseteq> edges t\<close> dual_order.trans is_MST_def 
            is_spanning_tree_def)
    ultimately show ?thesis
      unfolding is_spanning_tree_def tree_def
      by (auto simp: S_eq)
  qed                              
  then show ?thesis
    using MST weight_mono[OF \<open>edges t' \<subseteq> edges t\<close>]
    unfolding t'_def is_MST_def 
    using dual_order.trans by blast
qed    
        
end

subsection \<open>Prim: Using a Priority Queue\label{sec:using_pq}\<close>
text \<open>We define a new locale. Note that we could also reuse @{locale Prim}, however,
  this would complicate referencing the constants later in the theories from 
  which we generate the paper.
\<close>
locale Prim2 = Prim w g r for w :: "'v set \<Rightarrow> nat" and g :: "'v ugraph" and r :: 'v
begin  

text \<open>Abstraction to edge set\<close>
definition "A Q \<pi> \<equiv> {(u,v). \<pi> u = Some v \<and> Q u = \<infinity>}"


text \<open>Initialization\<close>
definition initQ :: "'v \<Rightarrow> enat"  where "initQ \<equiv> (\<lambda>_. \<infinity>)(r := 0)"
definition init\<pi> :: "'v \<Rightarrow> 'v option" where "init\<pi> \<equiv> Map.empty"  


text \<open>Step\<close>  
definition "upd_cond Q \<pi> u v' \<equiv> 
    (v',u) \<in> edges g 
  \<and> v'\<noteq>r \<and> (Q v' = \<infinity> \<longrightarrow> \<pi> v' = None)
  \<and> enat (w {v',u}) < Q v'"
  
text \<open>State after inner loop\<close>  
definition "Qinter Q \<pi> u v' 
  = (if upd_cond Q \<pi> u v' then enat (w {v',u}) else Q v')"

text \<open>State after one step\<close>  
definition "Q' Q \<pi> u \<equiv> (Qinter Q \<pi> u)(u:=\<infinity>)"
definition "\<pi>' Q \<pi> u v' = (if upd_cond Q \<pi> u v' then Some u else \<pi> v')"

definition "prim_invar2_init Q \<pi> \<equiv> Q=initQ \<and> \<pi>=init\<pi>"

definition "prim_invar2_ctd Q \<pi> \<equiv> let A = A Q \<pi>; S = S A in
  prim_invar1 A
\<and> \<pi> r = None \<and> Q r = \<infinity>  
\<and> (\<forall>(u,v)\<in>edges rg \<inter> (-S)\<times>S. Q u \<noteq> \<infinity>)
\<and> (\<forall>u. Q u \<noteq> \<infinity> \<longrightarrow> \<pi> u \<noteq> None)
\<and> (\<forall>u v. \<pi> u = Some v \<longrightarrow> v\<in>S \<and> (u,v)\<in>edges rg)
\<and> (\<forall>u v d. Q u = enat d \<and> \<pi> u = Some v 
      \<longrightarrow> d=w {u,v} \<and> (\<forall>v'\<in>S. (u,v')\<in>edges rg \<longrightarrow> d \<le> w {u,v'}))  
"

lemma prim_invar2_ctd_alt_aux1: 
  assumes "prim_invar1 (A Q \<pi>)"
  assumes "Q u \<noteq> \<infinity>" "u\<noteq>r"  
  shows "u\<notin>S (A Q \<pi>)"
proof -
  interpret Prim_Invar1_loc w g r "A Q \<pi>" by unfold_locales fact
  show ?thesis
    unfolding S_alt_def unfolding A_def using assms
    by auto
qed

lemma prim_invar2_ctd_alt: "prim_invar2_ctd Q \<pi> \<longleftrightarrow> (
  let A = A Q \<pi>; S = S A; cE=edges rg \<inter> (-S)\<times>S in
    prim_invar1 A
  \<and> \<pi> r = None \<and> Q r = \<infinity>  
  \<and> (\<forall>(u,v)\<in>cE. Q u \<noteq> \<infinity>)
  \<and> (\<forall>u v. \<pi> u = Some v \<longrightarrow> v\<in>S \<and> (u,v)\<in>edges rg)
  \<and> (\<forall>u d. Q u = enat d 
      \<longrightarrow> (\<exists>v. \<pi> u = Some v \<and> d=w {u,v} \<and> (\<forall>v'. (u,v')\<in>cE \<longrightarrow> d \<le> w {u,v'})))
)"
  unfolding prim_invar2_ctd_def Let_def
  using prim_invar2_ctd_alt_aux1[of Q \<pi>]
  apply safe
  subgoal by auto
  subgoal by (auto 0 3)
  subgoal by (auto 0 3)
  subgoal by clarsimp (metis (no_types,lifting) option.simps(3))
  done

definition "prim_invar2 Q \<pi> \<equiv> prim_invar2_init Q \<pi> \<or> prim_invar2_ctd Q \<pi>"
  
definition "T_measure2 Q \<pi> 
  \<equiv> if Q r = \<infinity> then T_measure1 (A Q \<pi>) else card (nodes rg)"


lemma Q'_init_eq: 
  "Q' initQ init\<pi> r = (\<lambda>u. if (u,r)\<in>edges rg then enat (w {u,r}) else \<infinity>)"
  apply (rule ext) 
  using reachable_edges_subset
  apply (simp add: Q'_def Qinter_def upd_cond_def initQ_def init\<pi>_def)
  by (auto simp: Prim.rg_def edges_sym' reachable_nodes_step'(2))

lemma \<pi>'_init_eq: 
  "\<pi>' initQ init\<pi> r = (\<lambda>u. if (u,r)\<in>edges rg then Some r else None)"  
  apply (rule ext) 
  using reachable_edges_subset
  apply (simp add: \<pi>'_def upd_cond_def initQ_def init\<pi>_def)
  by (auto simp: Prim.rg_def edges_sym' reachable_nodes_step'(2))

lemma A_init_eq: "A initQ init\<pi> = {}"  
  unfolding A_def init\<pi>_def 
  by auto

lemma S_empty: "S {} = {r}" unfolding S_def by (auto simp: A_init_eq)
      
lemma maintain_invar2_first_step: 
  assumes INV: "prim_invar2_init Q \<pi>"
  assumes UNS: "Q u = enat d"
  shows "prim_invar2_ctd (Q' Q \<pi> u) (\<pi>' Q \<pi> u)" (is ?G1)
    and "T_measure2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u) < T_measure2 Q \<pi>" (is ?G2)
proof -
  from INV have [simp]: "Q=initQ" "\<pi>=init\<pi>"
    unfolding prim_invar2_init_def by auto
  from UNS have [simp]: "u=r" by (auto simp: initQ_def split: if_splits) 
    
    
  note Q'_init_eq \<pi>'_init_eq A_init_eq 
    
  have [simp]: "(A (Q' initQ init\<pi> r) (\<pi>' initQ init\<pi> r)) = {}"
    apply (simp add: Q'_init_eq \<pi>'_init_eq)
    by (auto simp: A_def split: if_splits)
  
  show ?G1
    apply (simp add: prim_invar2_ctd_def Let_def invar1_initial)
    by (auto simp: Q'_init_eq \<pi>'_init_eq S_empty split: if_splits)
    
  have [simp]: "Q' initQ init\<pi> r r = \<infinity>"  
    by (auto simp: Q'_init_eq)
    
  have [simp]: "initQ r = 0" by (simp add: initQ_def) 
    
  show ?G2  
    unfolding T_measure2_def 
    apply simp
    apply (simp add: T_measure1_def S_empty)
    by (metis card_Diff1_less nodes_finite nodes_of_component 
          reachable_nodes_refl rg_def)
  
qed    
  
lemma maintain_invar2_first_step_presentation: 
  assumes INV: "prim_invar2_init Q \<pi>"
  assumes UNS: "Q u = enat d"
  shows "prim_invar2_ctd (Q' Q \<pi> u) (\<pi>' Q \<pi> u)
       \<and> T_measure2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u) < T_measure2 Q \<pi>"
  using maintain_invar2_first_step assms by blast

end

(*<*)
(*
  This locale is only used to present the invariant in the paper.
*)
locale Prim_Invar2_ctd_Presentation_Loc =
  fixes w g and r :: 'v and Q \<pi> A S rg cE
  assumes I: "Prim2.prim_invar2_ctd w g r Q \<pi>"
  defines local_A_def: "A \<equiv> Prim2.A Q \<pi>"
  defines local_S_def: "S \<equiv> Prim.S r A"
  defines local_rg_def: "rg \<equiv> Prim.rg g r"
  defines local_cE_def: "cE \<equiv> edges rg \<inter> (-S)\<times>S"
begin  

lemma 
      invar1: "Prim.prim_invar1 w g r A" (is ?G1)
  and root_contained: "\<pi> r = None \<and> Q r = \<infinity>" (is ?G2)
  and Q_defined: "\<forall>(u,v)\<in>cE. Q u \<noteq> \<infinity>" (is ?G3)
  and \<pi>_edges: "\<forall>u v. \<pi> u = Some v \<longrightarrow> v\<in>S \<and> (u,v)\<in>edges rg" (is ?G4)
  and Q_min: "\<forall>u d. Q u = enat d 
      \<longrightarrow> (\<exists>v. \<pi> u = Some v \<and> d=w {u,v} \<and> (\<forall>v'. (u,v')\<in>cE \<longrightarrow> d \<le> w {u,v'}))" 
      (is ?G5)
proof -
  interpret Prim2 w g r .
  
  show ?G1 ?G2 ?G3 ?G4 ?G5
    using I
    unfolding local_A_def local_S_def local_rg_def local_cE_def 
              prim_invar2_ctd_alt Let_def
    by simp_all
qed    

end

lemma (in Prim2) Prim_Invar2_ctd_Presentation_Loc_eq:
  "Prim_Invar2_ctd_Presentation_Loc w g r Q \<pi> \<longleftrightarrow> prim_invar2_ctd Q \<pi>"
  unfolding Prim_Invar2_ctd_Presentation_Loc_def ..

(*>*)

text \<open>Again, we define a locale to fix a state and assume the invariant\<close> 
locale Prim_Invar2_ctd_loc =   
  Prim2 w g r for w g and r :: 'v +
  fixes Q \<pi>
  assumes invar2: "prim_invar2_ctd Q \<pi>"
begin

sublocale Prim_Invar1_loc w g r "A Q \<pi>"
  using invar2 unfolding prim_invar2_ctd_def
  apply unfold_locales by (auto simp: Let_def)

lemma upd_cond_alt: "upd_cond Q \<pi> u v' \<longleftrightarrow> 
  (v',u) \<in> edges g \<and> v'\<notin>S (A Q \<pi>) \<and> enat (w {v',u}) < Q v'" 
  unfolding upd_cond_def S_alt_def unfolding A_def
  by (auto simp: fst_eq_Domain)
  
lemma \<pi>_root: "\<pi> r = None"
  and Q_root: "Q r = \<infinity>" 
  and Q_defined: "\<lbrakk> (u,v)\<in>edges rg; u\<notin>S (A Q \<pi>); v\<in>S (A Q \<pi>) \<rbrakk> \<Longrightarrow> Q u \<noteq> \<infinity>"
  and \<pi>_defined: "\<lbrakk> Q u \<noteq> \<infinity> \<rbrakk> \<Longrightarrow> \<pi> u \<noteq> None"
  and frontier: "\<pi> u = Some v \<Longrightarrow> v\<in>S (A Q \<pi>)"
  and edges: "\<pi> u = Some v \<Longrightarrow> (u,v)\<in>edges rg"
  and Q_\<pi>_consistent: "\<lbrakk> Q u = enat d; \<pi> u = Some v \<rbrakk> \<Longrightarrow> d = w {u,v}" 
  and Q_min: "Q u = enat d 
      \<Longrightarrow> (\<forall>v'\<in>S (A Q \<pi>). (u,v')\<in>edges rg \<longrightarrow> d \<le> w {u,v'})"
  using invar2 unfolding prim_invar2_ctd_def Let_def by auto

lemma \<pi>_def_on_S: "\<lbrakk>u\<in>S (A Q \<pi>); u\<noteq>r\<rbrakk> \<Longrightarrow> \<pi> u \<noteq> None"
  unfolding S_alt_def
  unfolding A_def
  by auto 
  
lemma \<pi>_def_on_edges_to_S: "\<lbrakk>v\<in>S (A Q \<pi>); u\<noteq>r; (u,v)\<in>edges rg\<rbrakk> \<Longrightarrow> \<pi> u \<noteq> None"
  apply (cases "u\<in>S (A Q \<pi>)")
  subgoal using \<pi>_def_on_S by auto
  subgoal by (simp add: Q_defined \<pi>_defined)
  done
  
lemma Q_min_is_light:  
  assumes UNS: "Q u = enat d"
  assumes MIN: "\<forall>v. enat d \<le> Q v"
  obtains v where "\<pi> u = Some v" "light_edge (S (A Q \<pi>)) v u"
proof -
  let ?A = "A Q \<pi>"
  let ?S = "S ?A"

  from UNS obtain v where 
    S1[simp]: "\<pi> u = Some v" "d = w {u,v}"
    using \<pi>_defined Q_\<pi>_consistent 
    by blast
          
  have "v\<in>?S" using frontier[of u v] by auto
    
  have [simp]: "u\<noteq>r" using \<pi>_root using S1 by (auto simp del: S1)
  
  have "u\<notin>?S" unfolding S_alt_def unfolding A_def using UNS by auto
  
  have "(v,u)\<in>edges rg" using edges[OF S1(1)]
    by (meson edges_sym' rev_subsetD)
  
  have M: "\<forall>(u', v')\<in>edges rg \<inter> ?S \<times> - ?S. w {v, u} \<le> w {u', v'}"
  proof safe
    fix a b
    assume "(a,b)\<in>edges rg" "a\<in>?S" "b\<notin>?S"
    hence "(b,a)\<in>edges rg" by (simp add: edges_sym')
  
    from Q_defined[OF \<open>(b,a)\<in>edges rg\<close> \<open>b\<notin>?S\<close> \<open>a\<in>?S\<close>] 
      obtain d' where 1: "Q b = enat d'" by blast 
    with \<pi>_defined obtain a' where "\<pi> b = Some a'" by auto
    from MIN 1 have "d\<le>d'" by (metis enat_ord_simps(1))
    also from Q_min[OF 1] \<open>(b,a)\<in>edges rg\<close> \<open>a\<in>?S\<close> have "d'\<le>w {b,a}" by blast  
    finally show "w {v,u} \<le> w {a,b}" by (simp add: insert_commute)
  qed  

  have LE: "light_edge ?S v u" using invar1 \<open>v\<in>?S\<close> \<open>u\<notin>?S\<close> \<open>(v,u)\<in>edges rg\<close> M
    unfolding light_edge_def by blast
  
  thus ?thesis using that by auto
qed
      
lemma maintain_invar_ctd: 
  assumes UNS: "Q u = enat d"
  assumes MIN: "\<forall>v. enat d \<le> Q v"
  shows "prim_invar2_ctd (Q' Q \<pi> u) (\<pi>' Q \<pi> u)" (is ?G1)
    and "T_measure2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u) < T_measure2 Q \<pi>" (is ?G2)
proof -
  let ?A = "A Q \<pi>"
  let ?S = "S ?A"

  from Q_min_is_light[OF UNS MIN] obtain v where 
    [simp]: "\<pi> u = Some v" and LE: "light_edge ?S v u" .

  let ?Q' = "Q' Q \<pi> u"
  let ?\<pi>' = "\<pi>' Q \<pi> u"
  let ?A' = "A ?Q' ?\<pi>'"
  let ?S' = "S ?A'"
  
  have NA: "?A' = {(u,v)} \<union> ?A"
    unfolding A_def  
    unfolding Q'_def \<pi>'_def upd_cond_def Qinter_def
    by (auto split: if_splits)
  
  from maintain_invar1[OF invar1 LE]
  have "prim_invar1 ?A'" and M1: "T_measure1 ?A' < T_measure1 ?A" 
    by (auto simp: NA) 
  then interpret N: Prim_Invar1_loc w g r ?A' by unfold_locales
              
  have [simp]: "?S' = insert u ?S"
    unfolding S_alt_def N.S_alt_def
    unfolding Q'_def Qinter_def \<pi>'_def upd_cond_def
    unfolding A_def
    by (auto split: if_splits simp: image_iff)
    
  show ?G1
    unfolding prim_invar2_ctd_def Let_def  
    apply safe
    subgoal by fact
    subgoal 
      unfolding \<pi>'_def upd_cond_def
      by (auto simp: \<pi>_root)
    subgoal 
      by (simp add: Prim2.Q'_def Prim2.Qinter_def Prim2.upd_cond_def Q_root)
    subgoal for a b
      apply simp
      apply safe
      subgoal
        unfolding Q'_def Qinter_def upd_cond_def
        apply (simp add: S_alt_def A_def)
        apply safe
        subgoal using reachable_edges_subset by blast
        subgoal by (simp add: Prim.S_def)
        subgoal by (metis (no_types) A_def Q_defined edges frontier)
        subgoal using not_infinity_eq by fastforce
        done
      subgoal
        unfolding S_alt_def N.S_alt_def 
        unfolding A_def Q'_def Qinter_def upd_cond_def
        apply (simp; safe; (auto;fail)?)
        subgoal
        proof -
          assume a1: "(a, r) \<in> edges rg"
          assume "a \<notin> fst ` {(u, v). \<pi> u = Some v \<and> Q u = \<infinity>}"
          then have "a \<notin> fst ` A Q \<pi>"
            by (simp add: A_def)
          then show ?thesis
            using a1 
            by (metis (no_types) S_alt_def Q_defined Un_insert_left 
                  edges_irrefl' insert_iff not_infinity_eq sup_bot.left_neutral)
        qed 
        subgoal by (simp add: fst_eq_Domain)
        subgoal 
          apply clarsimp
          by (smt Domain.intros Q_defined \<pi>_def_on_edges_to_S case_prod_conv 
                edges enat.exhaust frontier fst_eq_Domain mem_Collect_eq 
                option.exhaust) 
        subgoal by (simp add: fst_eq_Domain) 
        done
      done
    subgoal 
      by (metis Q'_def Qinter_def \<pi>'_def \<pi>_defined enat.distinct(2) 
            fun_upd_apply not_None_eq)
      
    subgoal
      by (metis \<open>S (A (Q' Q \<pi> u) (\<pi>' Q \<pi> u)) = insert u (S (A Q \<pi>))\<close> \<pi>'_def 
            frontier insertCI option.inject)
    subgoal
      by (metis N.S_edge_reachable upd_cond_def 
          \<open>S (A (Q' Q \<pi> u) (\<pi>' Q \<pi> u)) = insert u (S (A Q \<pi>))\<close> \<pi>'_def edges 
          edges_sym' insertI1 option.inject)
    subgoal
      by (smt Q'_def \<pi>'_def Q_\<pi>_consistent Qinter_def fun_upd_apply 
            insert_absorb not_enat_eq option.inject the_enat.simps)
    subgoal for v' d'
      apply clarsimp
      unfolding Q'_def Qinter_def upd_cond_def      
      using Q_min
      apply (clarsimp split: if_splits; safe)
      apply (all \<open>(auto;fail)?\<close>)
      subgoal by (simp add: le_less less_le_trans)
      subgoal using \<pi>_def_on_edges_to_S by auto
      subgoal using reachable_edges_subset by auto
      subgoal by (simp add: Q_root)
      done
    done       
  then interpret N: Prim_Invar2_ctd_loc w g r ?Q' ?\<pi>' by unfold_locales

  show ?G2  
    unfolding T_measure2_def
    by (auto simp: Q_root N.Q_root M1)
    
qed      

end

  
context Prim2 begin

lemma maintain_invar2_ctd: 
  assumes INV: "prim_invar2_ctd Q \<pi>"
  assumes UNS: "Q u = enat d"
  assumes MIN: "\<forall>v. enat d \<le> Q v"
  shows "prim_invar2_ctd (Q' Q \<pi> u) (\<pi>' Q \<pi> u)" (is ?G1)
    and "T_measure2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u) < T_measure2 Q \<pi>" (is ?G2)
proof -
  interpret Prim_Invar2_ctd_loc w g r Q \<pi> using INV by unfold_locales
  from maintain_invar_ctd[OF UNS MIN] show ?G1 ?G2 by auto
qed

lemma Q_min_is_light_presentation:  
  assumes INV: "prim_invar2_ctd Q \<pi>"
  assumes UNS: "Q u = enat d"
  assumes MIN: "\<forall>v. enat d \<le> Q v"
  obtains v where "\<pi> u = Some v" "light_edge (S (A Q \<pi>)) v u"
proof -
  interpret Prim_Invar2_ctd_loc w g r Q \<pi> using INV by unfold_locales
  from Q_min_is_light[OF UNS MIN] show ?thesis using that .
qed

lemma maintain_invar2_ctd_presentation: 
  assumes INV: "prim_invar2_ctd Q \<pi>"
  assumes UNS: "Q u = enat d"
  assumes MIN: "\<forall>v. enat d \<le> Q v"
  shows "prim_invar2_ctd (Q' Q \<pi> u) (\<pi>' Q \<pi> u)
       \<and> T_measure2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u) < T_measure2 Q \<pi>"
  using maintain_invar2_ctd assms by blast

lemma not_invar2_ctd_init: 
  "prim_invar2_init Q \<pi> \<Longrightarrow> \<not>prim_invar2_ctd Q \<pi>"
  unfolding prim_invar2_init_def prim_invar2_ctd_def initQ_def Let_def 
  by (auto)

lemma invar2_init_init: "prim_invar2_init initQ init\<pi>"
  unfolding prim_invar2_init_def by auto
  
lemma invar2_init: "prim_invar2 initQ init\<pi>"
  unfolding prim_invar2_def using invar2_init_init by auto

lemma maintain_invar2: 
  assumes A: "prim_invar2 Q \<pi>"  
  assumes UNS: "Q u = enat d"
  assumes MIN: "\<forall>v. enat d \<le> Q v"
  shows "prim_invar2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u)" (is ?G1)
    and "T_measure2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u) < T_measure2 Q \<pi>" (is ?G2)
  using A unfolding prim_invar2_def
  using maintain_invar2_first_step[of Q,OF _ UNS]
  using maintain_invar2_ctd[OF _ UNS MIN]
  using not_invar2_ctd_init
  apply blast+
  done

lemma invar2_ctd_finish:  
  assumes INV: "prim_invar2_ctd Q \<pi>"  
  assumes FIN: "Q = (\<lambda>_. \<infinity>)"
  shows "is_MST w rg (graph {r} {(u, v). \<pi> u = Some v})"
proof -  
  from INV interpret Prim_Invar2_ctd_loc w g r Q \<pi> by unfold_locales

  let ?A = "A Q \<pi>" let ?S="S ?A"
  
  have FC: "edges g \<inter> ?S \<times> - ?S = {}" 
  proof (safe; simp)
    fix a b
    assume "(a,b)\<in>edges g" "a\<in>?S" "b\<notin>?S"
    with Q_defined[OF edges_sym'] S_edge_reachable have "Q b \<noteq> \<infinity>" 
      by blast
    with FIN show False by auto
  qed
  
  have Aeq: "?A = {(u, v). \<pi> u = Some v}"
    unfolding A_def using FIN by auto
  
  from invar1_finish[OF invar1 FC, unfolded Aeq] show ?thesis .
qed
  
  
lemma invar2_finish:  
  assumes INV: "prim_invar2 Q \<pi>"  
  assumes FIN: "Q = (\<lambda>_. \<infinity>)"
  shows "is_MST w rg (graph {r} {(u, v). \<pi> u = Some v})"
proof -  
  from INV have "prim_invar2_ctd Q \<pi>"
    unfolding prim_invar2_def prim_invar2_init_def initQ_def
    by (auto simp: fun_eq_iff FIN split: if_splits)
  with FIN invar2_ctd_finish show ?thesis by blast  
qed
  
end


subsection \<open>Refinement of Inner Foreach Loop\label{sec:using_foreach}\<close>

context Prim2 begin

definition "foreach_body u \<equiv> \<lambda>(v,d) (Q,\<pi>).
  if v=r then (Q,\<pi>)
  else
    case (Q v, \<pi> v) of
      (\<infinity>,None) \<Rightarrow> (Q(v:=enat d), \<pi>(v\<mapsto>u))
    | (enat d',_) \<Rightarrow> if d<d' then (Q(v:=enat d), \<pi>(v\<mapsto>u)) else (Q,\<pi>)
    | (\<infinity>,Some _) \<Rightarrow> (Q,\<pi>)
  "

lemma foreach_body_alt: "foreach_body u = (\<lambda>(v,d) (Q,\<pi>). 
  if v\<noteq>r \<and> (\<pi> v = None \<or> Q v \<noteq> \<infinity>) \<and> enat d < Q v then
    (Q(v:=enat d), \<pi>(v\<mapsto>u))
  else 
    (Q,\<pi>)
)"  
  unfolding foreach_body_def S_def
  by (auto split: enat.splits option.splits simp: fst_eq_Domain fun_eq_iff)

definition foreach where
  "foreach u adjs Q\<pi> = foldr (foreach_body u) adjs Q\<pi>"

definition "\<And>Q V. 
  Qigen Q \<pi> u adjs v = (if v \<notin> fst`set adjs then Q v else Qinter Q \<pi> u v)"
definition "\<And>Q V \<pi>. 
  \<pi>'gen Q \<pi> u adjs v = (if v \<notin> fst`set adjs then \<pi> v else \<pi>' Q \<pi> u v)"

context begin

private lemma Qc: 
  "Qigen Q \<pi> u ((v, w {u, v}) # adjs) x 
  = (if x=v then Qinter Q \<pi> u v else Qigen Q \<pi> u adjs x)" for x
  unfolding Qigen_def by auto
  
private lemma \<pi>c: 
  "\<pi>'gen Q \<pi> u ((v, w {u, v}) # adjs) x 
  = (if x=v then \<pi>' Q \<pi> u v else \<pi>'gen Q \<pi> u adjs x)" for x
  unfolding \<pi>'gen_def by auto

lemma foreach_refine_gen:
  assumes "set adjs \<subseteq> {(v,d). (u,v)\<in>edges g \<and> w {u,v} = d}"          
  shows "foreach u adjs (Q,\<pi>) = (Qigen Q \<pi> u adjs,\<pi>'gen Q \<pi> u adjs)"
  using assms
  unfolding foreach_def
proof (induction adjs arbitrary: Q \<pi>)
  case Nil
  have INVAR_INIT: "Qigen Q \<pi> u [] = Q" "\<pi>'gen Q \<pi> u [] = \<pi>" for Q \<pi>
    unfolding assms Qigen_def \<pi>'gen_def 
    by (auto simp: fun_eq_iff image_def Q'_def \<pi>'_def edges_def)
  with Nil show ?case by (simp add: INVAR_INIT)
next
  case (Cons a adjs)
  obtain v d where [simp]: "a=(v,d)" by (cases a)
  
  have [simp]: "u\<noteq>v" "v\<noteq>u" using Cons.prems by auto
    
  have QinfD: "Qigen Q \<pi> u adjs v = \<infinity> \<Longrightarrow> Q v = \<infinity>"  
    unfolding Qigen_def Q'_def Qinter_def by (auto split: if_splits)
    
  show ?case using Cons.prems
    apply (cases a)
    apply (clarsimp simp: Cons.IH)
    unfolding foreach_body_def
    apply (clarsimp; safe)
    subgoal by (auto simp: Qigen_def Qinter_def upd_cond_def)
    subgoal by (auto simp: \<pi>'gen_def \<pi>'_def upd_cond_def)
    subgoal
      apply (clarsimp split: enat.split option.split simp: \<pi>c Qc fun_eq_iff)
      unfolding Qinter_def Qigen_def \<pi>'_def \<pi>'gen_def upd_cond_def
      apply (safe; simp split: if_splits add: insert_commute)
      by (auto dest: edges_sym')
    done
    
qed
      
lemma foreach_refine:
  assumes "set adjs = {(v,d). (u,v)\<in>edges g \<and> w {u,v} = d}"
  shows "foreach u adjs (Q,\<pi>) = (Qinter Q \<pi> u,\<pi>' Q \<pi> u)"
proof -
  have INVAR_INIT: "Qigen Q \<pi> u [] = Q" "\<pi>'gen Q \<pi> u [] = \<pi>" for Q \<pi>
    unfolding assms Qigen_def \<pi>'gen_def 
    by (auto simp: fun_eq_iff image_def Q'_def \<pi>'_def edges_def)
  from assms have 1: "set adjs \<subseteq> {(v,d). (u,v)\<in>edges g \<and> w {u,v} = d}" 
    by simp
  have [simp]: 
    "v \<in> fst ` {(v, d). (u, v) \<in> edges g \<and> w {u, v} = d} 
    \<longleftrightarrow> (u,v)\<in>edges g" 
    for v
    by force
    
  show ?thesis 
    unfolding foreach_refine_gen[OF 1] 
    unfolding Qigen_def \<pi>'gen_def assms upd_cond_def Qinter_def \<pi>'_def
    by (auto simp: fun_eq_iff image_def dest: edges_sym')      
    
qed

end
end

end
