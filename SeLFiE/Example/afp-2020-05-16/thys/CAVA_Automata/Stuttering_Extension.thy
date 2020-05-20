theory Stuttering_Extension
imports Simulation Step_Conv
begin

  definition stutter_extend_edges :: "'v set \<Rightarrow> 'v digraph \<Rightarrow> 'v digraph"
    where "stutter_extend_edges V E \<equiv> E \<union> {(v, v) |v. v \<in> V \<and> v \<notin> Domain E}"

  lemma stutter_extend_edgesI_edge:
    assumes "(u, v) \<in> E"
    shows "(u, v) \<in> stutter_extend_edges V E"
    using assms unfolding stutter_extend_edges_def by auto
  lemma stutter_extend_edgesI_stutter:
    assumes "v \<in> V" "v \<notin> Domain E"
    shows "(v, v) \<in> stutter_extend_edges V E"
    using assms unfolding stutter_extend_edges_def by auto
  lemma stutter_extend_edgesE:
    assumes "(u, v) \<in> stutter_extend_edges V E"
    obtains (edge) "(u, v) \<in> E" | (stutter) "u \<in> V" "u \<notin> Domain E" "u = v"
    using assms unfolding stutter_extend_edges_def by auto

  lemma stutter_extend_wf: "E \<subseteq> V \<times> V \<Longrightarrow> stutter_extend_edges V E \<subseteq> V \<times> V"
    unfolding stutter_extend_edges_def by auto

  lemma stutter_extend_edges_rtrancl[simp]: "(stutter_extend_edges V E)\<^sup>* = E\<^sup>*"
    unfolding stutter_extend_edges_def by (auto intro: in_rtrancl_UnI elim: rtrancl_induct)

  lemma stutter_extend_domain: "V \<subseteq> Domain (stutter_extend_edges V E)"
    unfolding stutter_extend_edges_def by auto

  definition stutter_extend :: "('v, _) graph_rec_scheme \<Rightarrow> ('v, _) graph_rec_scheme"
    where "stutter_extend G \<equiv>
    \<lparr>
      g_V = g_V G,
      g_E = stutter_extend_edges (g_V G) (g_E G),
      g_V0 = g_V0 G,
      \<dots> = graph_rec.more G
    \<rparr>"

  lemma stutter_extend_simps[simp]:
    "g_V (stutter_extend G) = g_V G"
    "g_E (stutter_extend G) = stutter_extend_edges (g_V G) (g_E G)"
    "g_V0 (stutter_extend G) = g_V0 G"
    unfolding stutter_extend_def by auto

  lemma stutter_extend_simps_sa[simp]:
    "sa_L (stutter_extend G) = sa_L G"
    unfolding stutter_extend_def
    by (metis graph_rec.select_convs(4) sa_rec.select_convs(1) sa_rec.surjective)

  lemma (in graph) stutter_extend_graph: "graph (stutter_extend G)"
    using V0_ss E_ss by (unfold_locales, auto intro!: stutter_extend_wf)
  lemma (in sa) stutter_extend_sa: "sa (stutter_extend G)"
  proof -
    interpret graph "stutter_extend G" using stutter_extend_graph by this
    show ?thesis by unfold_locales
  qed

  lemma (in bisimulation) stutter_extend: "bisimulation R (stutter_extend A) (stutter_extend B)"
  proof -
    interpret ea: graph "stutter_extend A" by (rule a.stutter_extend_graph)
    interpret eb: graph "stutter_extend B" by (rule b.stutter_extend_graph)
    show ?thesis
    proof
      fix a b
      assume "a \<in> g_V (stutter_extend A)" "(a, b) \<in> R"
      thus "b \<in> g_V (stutter_extend B)" using s1.nodes_sim by simp
    next
      fix a
      assume "a \<in> g_V0 (stutter_extend A)"
      thus "\<exists> b. b \<in> g_V0 (stutter_extend B) \<and> (a, b) \<in> R" using s1.init_sim by simp
    next
      fix a a' b
      assume "(a, a') \<in> g_E (stutter_extend A)" "(a, b) \<in> R"
      thus "\<exists> b'. (b, b') \<in> g_E (stutter_extend B) \<and> (a', b') \<in> R"
        apply simp
        using s1.nodes_sim s1.step_sim s2.stuck_sim 
        by (blast
          intro: stutter_extend_edgesI_edge stutter_extend_edgesI_stutter
          elim: stutter_extend_edgesE)
    next
      fix b a
      assume "b \<in> g_V (stutter_extend B)" "(b, a) \<in> R\<inverse>"
      thus "a \<in> g_V (stutter_extend A)" using s2.nodes_sim by simp
    next
      fix b
      assume "b \<in> g_V0 (stutter_extend B)"
      thus "\<exists> a. a \<in> g_V0 (stutter_extend A) \<and> (b, a) \<in> R\<inverse>" using s2.init_sim by simp
    next
      fix b b' a
      assume "(b, b') \<in> g_E (stutter_extend B)" "(b, a) \<in> R\<inverse>"
      thus "\<exists> a'. (a, a') \<in> g_E (stutter_extend A) \<and> (b', a') \<in> R\<inverse>"
        apply simp
        using s2.nodes_sim s2.step_sim s1.stuck_sim
        by (blast
          intro: stutter_extend_edgesI_edge stutter_extend_edgesI_stutter
          elim: stutter_extend_edgesE)
    qed
  qed

  lemma (in lbisimulation) lstutter_extend: "lbisimulation R (stutter_extend A) (stutter_extend B)"
  proof -
    interpret se: bisimulation R "stutter_extend A" "stutter_extend B" by (rule stutter_extend)
    show ?thesis by (unfold_locales, auto simp: s1.labeling_consistent)
  qed

  definition stutter_extend_en :: "('s\<Rightarrow>'a set) \<Rightarrow> ('s \<Rightarrow> 'a option set)" where
    "stutter_extend_en en \<equiv> \<lambda>s. let as = en s in if as={} then {None} else Some`as"
  
  definition stutter_extend_ex :: "('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('a option \<Rightarrow> 's \<Rightarrow> 's)" where
    "stutter_extend_ex ex \<equiv> \<lambda>None \<Rightarrow> id | Some a \<Rightarrow> ex a"

  abbreviation stutter_extend_enex 
    :: "('s\<Rightarrow>'a set) \<times> ('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'a option set) \<times> ('a option \<Rightarrow> 's \<Rightarrow> 's)"
  where
   "stutter_extend_enex \<equiv> map_prod stutter_extend_en stutter_extend_ex"
  
  lemma stutter_extend_pred_of_enex_conv:
    "stutter_extend_edges UNIV (rel_of_enex enex) = rel_of_enex (stutter_extend_enex enex)"
    unfolding rel_of_enex_def stutter_extend_edges_def
    apply (auto simp: stutter_extend_en_def stutter_extend_ex_def split: prod.splits)
    apply force
    apply blast
    done
  
  lemma stutter_extend_en_Some_eq[simp]:
    "Some a \<in> stutter_extend_en en gc \<longleftrightarrow> a \<in> en gc"
    "stutter_extend_ex ex (Some a) gc = ex a gc"
    unfolding stutter_extend_en_def stutter_extend_ex_def by auto
  
  lemma stutter_extend_ex_None_eq[simp]:
    "stutter_extend_ex ex None = id"
    unfolding stutter_extend_ex_def by auto

end
