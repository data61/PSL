theory ShortestPathNeg

(*
  This theory uses the graph library and  
  several lemmas that were proven in the 
  shortest path theory
*)
imports ShortestPath

begin
section \<open>Shortest Path (with general edge costs)\<close>
(* 
  In this locale we assume we are given a 
  wellformed directed graph $G = (V,E)$ with 
  finite $V$ and $E$ (this is the assumption 
  $graphG$). Moreover, a source vertex $s$ in 
  $V$ . In addition, a cost function c, a function
 $num:V\to \Nat$, $parent\dash edge:V\to E \cup $*)
locale shortest_paths_locale_step1 = 
  fixes G :: "('a, 'b) pre_digraph" (structure)
  fixes s :: "'a"
  fixes c :: "'b \<Rightarrow> real"
  fixes num :: "'a \<Rightarrow> nat"
  fixes parent_edge :: "'a \<Rightarrow> 'b option"
  fixes dist :: "'a  \<Rightarrow> ereal"
  assumes graphG: "fin_digraph G"
  assumes s_assms: 
    "s \<in> verts G" 
    "dist s \<noteq> \<infinity>" 
    "parent_edge s = None" 
    "num s = 0"
  assumes  parent_num_assms: 
    "\<And>v.  \<lbrakk>v \<in> verts G; v \<noteq> s; dist v \<noteq> \<infinity>\<rbrakk> \<Longrightarrow>
    (\<exists>e \<in> arcs G. parent_edge v = Some e \<and> 
    head G e = v \<and> dist (tail G e) \<noteq> \<infinity> \<and>
    num v  = num (tail G e) + 1)"
  assumes noPedge: "\<And>e. e\<in>arcs G \<Longrightarrow> 
    dist (tail G e) \<noteq> \<infinity> \<Longrightarrow> dist (head G e) \<noteq> \<infinity>"

sublocale shortest_paths_locale_step1 \<subseteq> fin_digraph G
  using graphG by auto

definition (in shortest_paths_locale_step1) enum :: "'a \<Rightarrow> enat" where
  "enum v = (if (dist v = \<infinity> \<or> dist v = - \<infinity>) then \<infinity> else num v)"

locale shortest_paths_locale_step2 = 
  shortest_paths_locale_step1 +
  basic_just_sp G dist c s enum +
  assumes source_val: "(\<exists>v \<in> verts G. enum v \<noteq> \<infinity>) \<Longrightarrow> dist s = 0"
  assumes no_edge_Vm_Vf: 
    "\<And>e. e \<in> arcs G \<Longrightarrow> dist (tail G e) = - \<infinity> \<Longrightarrow> \<forall> r. dist (head G e) \<noteq> ereal r"

function (in shortest_paths_locale_step1) pwalk :: "'a \<Rightarrow> 'b list" 
where
  "pwalk v = 
    (if (v = s \<or> dist v = \<infinity> \<or> v \<notin> verts G)
      then [] 
      else pwalk (tail G (the (parent_edge v))) @ [the (parent_edge v)]
    )"
by auto 
termination (in shortest_paths_locale_step1) 
  using parent_num_assms
  by (relation "measure num", auto, fastforce)


lemma (in shortest_paths_locale_step1) pwalk_simps:
  "v = s \<or> dist v = \<infinity> \<or> v \<notin> verts G \<Longrightarrow> pwalk v = []"
  "v \<noteq> s \<Longrightarrow> dist v \<noteq> \<infinity> \<Longrightarrow> v \<in> verts G \<Longrightarrow> 
    pwalk v = pwalk (tail G (the (parent_edge v))) @ [the (parent_edge v)]"
by auto

definition (in shortest_paths_locale_step1) pwalk_verts :: "'a  \<Rightarrow> 'a set" where 
  "pwalk_verts v = {u. u \<in> set (awalk_verts s (pwalk v))}" 

locale shortest_paths_locale_step3 =
  shortest_paths_locale_step2 +
  fixes C :: "('a \<times>('b awalk)) set"
  assumes C_se: 
    "C \<subseteq> {(u, p). dist u \<noteq> \<infinity> \<and> awalk u p u \<and> awalk_cost c p < 0}"
  assumes int_neg_cyc: 
    "\<And>v. v \<in> verts G \<Longrightarrow> dist v = -\<infinity> \<Longrightarrow> 
      (fst ` C) \<inter> pwalk_verts v  \<noteq> {}"

locale shortest_paths_locale_step2_pred = 
  shortest_paths_locale_step1 +
  fixes pred :: "'a \<Rightarrow> 'b option" 
  assumes bj: "basic_just_sp_pred G dist c s enum pred" 
  assumes source_val: "(\<exists>v \<in> verts G. enum v \<noteq> \<infinity>) \<Longrightarrow> dist s = 0"
  assumes no_edge_Vm_Vf: 
    "\<And>e. e \<in> arcs G \<Longrightarrow> dist (tail G e) = - \<infinity> \<Longrightarrow> \<forall> r. dist (head G e) \<noteq> ereal r"
(*
sublocale shortest_paths_locale_step2_pred \<subseteq> shortest_paths_locale_step2
using shortest_paths_locale_step2_pred_axioms 
unfolding shortest_paths_locale_step2_pred_def 
   shortest_paths_locale_step2_pred_axioms_def 
   shortest_paths_locale_step2_def 
   shortest_paths_locale_step2_axioms_def
try0
*)

lemma (in shortest_paths_locale_step1) num_s_is_min:
  assumes "v \<in> verts G"
  assumes "v \<noteq> s"
  assumes "dist v \<noteq> \<infinity>"
  shows "num v > 0"
     using parent_num_assms[OF assms] by fastforce

lemma (in shortest_paths_locale_step1) path_from_root_Vr_ex:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "v \<noteq> s"
  assumes "dist v \<noteq> \<infinity>"
  shows  "\<exists>e. s \<rightarrow>\<^sup>* tail G e \<and>
          e \<in> arcs G \<and> head G e = v \<and> dist (tail G e) \<noteq> \<infinity> \<and>
          parent_edge v = Some e \<and> num v = num (tail G e) + 1"
using assms
proof(induct "num v - 1" arbitrary : v)
case 0
  obtain e where ee:
    "e \<in> arcs G" "head G e = v" "dist (tail G e) \<noteq> \<infinity>" 
    "parent_edge v = Some e" "num v = num (tail G e) + 1"
    using parent_num_assms[OF 0(2-4)] by fast
  have "tail G e = s" 
    using num_s_is_min[OF tail_in_verts [OF ee(1)] _ ee(3)] 
    ee(5) 0(1) by auto
  then show ?case using ee by auto
next
case (Suc n')
  obtain e where ee:
    "e \<in> arcs G" "head G e = v" "dist (tail G e) \<noteq> \<infinity>" 
    "parent_edge v = Some e" "num v = num (tail G e) + 1"
    using parent_num_assms[OF Suc(3-5)] by fast
  then have ss: "tail G e \<noteq> s"
    using num_s_is_min tail_in_verts
    Suc(2) s_assms(4) by force
  have nst: "n' = num (tail G e) - 1"
    using ee(5) Suc(2) by presburger
  obtain e' where reach: "s \<rightarrow>\<^sup>* tail G e'" and
    e': "e' \<in> arcs G" "head G e' = tail G e" "dist (tail G e') \<noteq> \<infinity>"
    using Suc(1)[OF nst tail_in_verts[OF ee(1)] ss ee(3)] by blast
  then have "s \<rightarrow>\<^sup>* tail G e"
    by (metis arc_implies_awalk reachable_awalk reachable_trans)
  then show ?case using e' ee by auto
qed

lemma (in shortest_paths_locale_step1) path_from_root_Vr:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "dist v \<noteq> \<infinity>"
  shows "s \<rightarrow>\<^sup>* v"
proof(cases "v = s")
case True thus ?thesis using assms by simp
next
case False
  obtain e where "s \<rightarrow>\<^sup>* tail G e" "e \<in> arcs G" "head G e = v"
      using path_from_root_Vr_ex[OF assms(1) False assms(2)] by blast
  then have "s \<rightarrow>\<^sup>* tail G e" "tail G e \<rightarrow> v"
    by (auto intro: in_arcs_imp_in_arcs_ends)
  then show ?thesis by (rule reachable_adj_trans)
qed

lemma (in shortest_paths_locale_step1) \<mu>_V_less_inf:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "dist v \<noteq> \<infinity>"
  shows "\<mu> c s v \<noteq> \<infinity>"
  using assms path_from_root_Vr \<mu>_reach_conv by force

lemma (in shortest_paths_locale_step2) enum_not0:
  assumes "v \<in> verts G"
  assumes "v \<noteq> s"
  assumes "enum v \<noteq> \<infinity>"
  shows "enum v \<noteq> enat 0"
     using parent_num_assms[OF assms(1,2)] assms unfolding enum_def by auto

lemma (in shortest_paths_locale_step2) dist_Vf_\<mu>:
  fixes v :: 'a
  assumes vG: "v \<in> verts G"
  assumes "\<exists>r. dist v = ereal r"
  shows "dist v = \<mu> c s v"
proof -
  have ds: "dist s =  0" 
    using assms source_val unfolding enum_def by force
  have ews:"awalk s [] s" 
    using s_assms(1) unfolding awalk_def by simp
  have mu: "\<mu> c s s = ereal 0" 
    using min_cost_le_walk_cost[OF ews, where c=c] 
    awalk_cost_Nil ds  dist_le_\<mu>[OF s_assms(1)] zero_ereal_def
    by simp
  thus ?thesis 
    using ds assms dist_le_\<mu>[OF vG] 
    dist_ge_\<mu>[OF vG _ _ mu ds enum_not0]
    unfolding enum_def by fastforce
qed

lemma (in shortest_paths_locale_step1) pwalk_awalk:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "dist v \<noteq> \<infinity>"
  shows "awalk s (pwalk v) v" 
proof (cases "v=s")
case True
  thus ?thesis 
    using assms pwalk.simps[where v=v] 
    awalk_Nil_iff by presburger 
next
case False
  from assms show ?thesis 
  proof (induct rule: pwalk.induct)
    fix v 
    let ?e = "the (parent_edge v)"
    let ?u = "tail G ?e"
    assume ewu: "\<not> (v = s \<or> dist v = \<infinity> \<or> v \<notin> verts G) \<Longrightarrow> 
                 ?u \<in> verts G \<Longrightarrow> dist ?u \<noteq> \<infinity> \<Longrightarrow> 
                 awalk s (pwalk ?u) ?u"
    assume vG: "v \<in> verts G" 
    assume dv: "dist v \<noteq> \<infinity>"
    thus "awalk s (pwalk v) v "
    proof (cases "v = s \<or> dist v = \<infinity> \<or> v \<notin> verts G")
    case True
      thus ?thesis 
        using pwalk.simps vG dv 
        awalk_Nil_iff by fastforce
    next
    case False
      obtain e  where ee:
        "e \<in>arcs G" 
        "parent_edge v = Some e" 
        "head G e = v" 
        "dist (tail G e) \<noteq> \<infinity>" 
        using parent_num_assms False by blast
      hence "awalk s (pwalk ?u) ?u"
        using ewu[OF False] tail_in_verts by simp
      hence "awalk s (pwalk (tail G e) @ [e]) v"
        using ee(1-3) vG
        by (auto simp: awalk_simps simp del: pwalk.simps)
      also have "pwalk (tail G e) @ [e] = pwalk v"
        using False ee(2) unfolding pwalk.simps[where v=v] by auto
      finally show ?thesis .
    qed
  qed
qed

lemma (in shortest_paths_locale_step3) \<mu>_ninf:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "dist v = - \<infinity>"
  shows "\<mu> c s v = - \<infinity>"
proof -
  have "awalk s (pwalk v) v"
    using pwalk_awalk assms by force
moreover
  obtain w where ww: "w \<in> fst ` C \<inter> pwalk_verts v"
    using int_neg_cyc[OF assms] by blast
  then obtain q where 
     "awalk w q w" 
     "awalk_cost c q < 0"
     using C_se by auto
moreover 
  have "w \<in> set (awalk_verts s (pwalk v))"
    using ww unfolding pwalk_verts_def by fast
ultimately
  show ?thesis using  neg_cycle_imp_inf_\<mu> by force
qed

lemma (in shortest_paths_locale_step3) correct_shortest_path:
  fixes v :: 'a
  assumes "v \<in> verts G"
  shows "dist v = \<mu> c s v"
proof(cases "dist v")
show " \<And>r. dist v = ereal r \<Longrightarrow> dist v = \<mu> c s v"
  using dist_Vf_\<mu>[OF assms] by simp 
next
show "dist v = \<infinity> \<Longrightarrow> dist v = \<mu> c s v"
  using \<mu>_V_less_inf[OF assms] 
  dist_le_\<mu>[OF assms] by simp
next
show "dist v = -\<infinity> \<Longrightarrow> dist v = \<mu> c s v"
  using \<mu>_ninf[OF assms] by simp
qed

end

