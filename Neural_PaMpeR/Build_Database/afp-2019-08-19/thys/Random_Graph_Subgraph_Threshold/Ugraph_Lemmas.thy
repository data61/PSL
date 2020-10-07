section\<open>Lemmas about undirected graphs\<close>

theory Ugraph_Lemmas
imports
  Prob_Lemmas
  Girth_Chromatic.Girth_Chromatic
begin

text\<open>The complete graph is a graph where all possible edges are present. It is wellformed by
definition.\<close>

definition complete :: "nat set \<Rightarrow> ugraph" where
"complete V = (V, all_edges V)"

lemma complete_wellformed: "uwellformed (complete V)"
unfolding complete_def uwellformed_def all_edges_def
by simp

text\<open>If the set of vertices is finite, the set of edges in the complete graph is finite.\<close>

lemma all_edges_finite: "finite V \<Longrightarrow> finite (all_edges V)"
unfolding all_edges_def
by simp

corollary complete_finite_edges: "finite V \<Longrightarrow> finite (uedges (complete V))"
unfolding complete_def using all_edges_finite
by simp

text\<open>The sets of possible edges of disjoint sets of vertices are disjoint.\<close>

lemma all_edges_disjoint: "S \<inter> T = {} \<Longrightarrow> all_edges S \<inter> all_edges T = {}"
unfolding all_edges_def
by force

text\<open>A graph is called `finite' if its set of edges and its set of vertices are finite.\<close>

definition "finite_graph G \<equiv> finite (uverts G) \<and> finite (uedges G)"

text\<open>The complete graph is finite.\<close>

corollary complete_finite: "finite V \<Longrightarrow> finite_graph (complete V)"
using complete_finite_edges unfolding finite_graph_def complete_def
by simp

text\<open>A graph is called `nonempty' if it contains at least one vertex and at least one edge.\<close>

definition "nonempty_graph G \<equiv> uverts G \<noteq> {} \<and> uedges G \<noteq> {}"

text\<open>A random graph is both wellformed and finite.\<close>

lemma (in edge_space) wellformed_and_finite:
  assumes "E \<in> Pow S_edges"
  shows "finite_graph (edge_ugraph E)" "uwellformed (edge_ugraph E)"
unfolding finite_graph_def
proof
  show "finite (uverts (edge_ugraph E))"
    unfolding edge_ugraph_def S_verts_def by simp
next
  show "finite (uedges (edge_ugraph E))"
    using assms unfolding edge_ugraph_def S_edges_def by (auto intro: all_edges_finite)
next
  show "uwellformed (edge_ugraph E)"
    using complete_wellformed unfolding edge_ugraph_def S_edges_def complete_def uwellformed_def by force
qed

text\<open>The probability for a random graph to have $e$ edges is $p ^ e$.\<close>

lemma (in edge_space) cylinder_empty_prob:
  "A \<subseteq> S_edges \<Longrightarrow> prob (cylinder S_edges A {}) = p ^ (card A)"
using cylinder_prob by auto

subsection\<open>Subgraphs\<close>

definition subgraph :: "ugraph \<Rightarrow> ugraph \<Rightarrow> bool" where
"subgraph G' G \<equiv> uverts G' \<subseteq> uverts G \<and> uedges G' \<subseteq> uedges G"

lemma subgraph_refl: "subgraph G G"
unfolding subgraph_def
by simp

lemma subgraph_trans: "subgraph G'' G' \<Longrightarrow> subgraph G' G \<Longrightarrow> subgraph G'' G"
unfolding subgraph_def
by auto

lemma subgraph_antisym: "subgraph G G' \<Longrightarrow> subgraph G' G \<Longrightarrow> G = G'"
unfolding subgraph_def
by (auto simp add: Product_Type.prod_eqI)

lemma subgraph_complete:
  assumes "uwellformed G"
  shows "subgraph G (complete (uverts G))"
proof -
  {
    fix e
    assume "e \<in> uedges G"
    with assms have "card e = 2" and u: "\<And>u. u \<in> e \<Longrightarrow> u \<in> uverts G"
      unfolding uwellformed_def by auto
    moreover then obtain u v where "e = {u, v}" "u \<noteq> v"
      by (metis card_2_elements)
    ultimately have "e = mk_uedge (u, v)" "u \<in> uverts G" "v \<in> uverts G"
      by auto
    hence "e \<in> all_edges (uverts G)"
      unfolding all_edges_def using \<open>u \<noteq> v\<close> by fastforce
  }
  thus ?thesis
    unfolding complete_def subgraph_def by auto
qed

corollary wellformed_all_edges: "uwellformed G \<Longrightarrow> uedges G \<subseteq> all_edges (uverts G)"
using subgraph_complete subgraph_def complete_def by simp

lemma subgraph_finite: "\<lbrakk> finite_graph G; subgraph G' G \<rbrakk> \<Longrightarrow> finite_graph G'"
unfolding finite_graph_def subgraph_def
by (metis rev_finite_subset)

corollary wellformed_finite:
  assumes "finite (uverts G)" and "uwellformed G"
  shows "finite_graph G"
proof (rule subgraph_finite[where G = "complete (uverts G)"])
  show "subgraph G (complete (uverts G))"
    using assms by (simp add: subgraph_complete)
next
  have "finite (uedges (complete (uverts G)))"
    using complete_finite_edges[OF assms(1)] .
  thus "finite_graph (complete (uverts G))"
    unfolding finite_graph_def complete_def using assms(1) by auto
qed

definition subgraphs :: "ugraph \<Rightarrow> ugraph set" where
"subgraphs G = {G'. subgraph G' G}"

definition nonempty_subgraphs :: "ugraph \<Rightarrow> ugraph set" where
"nonempty_subgraphs G = {G'. uwellformed G' \<and> subgraph G' G \<and> nonempty_graph G'}"

lemma subgraphs_finite:
  assumes "finite_graph G"
  shows "finite (subgraphs G)"
proof -
  have "subgraphs G = {(V', E'). V' \<subseteq> uverts G \<and> E' \<subseteq> uedges G}"
    unfolding subgraphs_def subgraph_def by force
  moreover have "finite (uverts G)" "finite (uedges G)"
    using assms unfolding finite_graph_def by auto
  ultimately show ?thesis
    by simp
qed

corollary nonempty_subgraphs_finite: "finite_graph G \<Longrightarrow> finite (nonempty_subgraphs G)"
using subgraphs_finite
unfolding nonempty_subgraphs_def subgraphs_def
by auto

subsection\<open>Induced subgraphs\<close>

definition induced_subgraph :: "uvert set \<Rightarrow> ugraph \<Rightarrow> ugraph" where
"induced_subgraph V G = (V, uedges G \<inter> all_edges V)"

lemma induced_is_subgraph:
  "V \<subseteq> uverts G \<Longrightarrow> subgraph (induced_subgraph V G) G"
  "V \<subseteq> uverts G \<Longrightarrow> subgraph (induced_subgraph V G) (complete V)"
unfolding subgraph_def induced_subgraph_def complete_def
by simp+

lemma induced_wellformed: "uwellformed G \<Longrightarrow> V \<subseteq> uverts G \<Longrightarrow> uwellformed (induced_subgraph V G)"
unfolding uwellformed_def induced_subgraph_def all_edges_def
by force

lemma subgraph_union_induced:
  assumes "uverts H\<^sub>1 \<subseteq> S" and "uverts H\<^sub>2 \<subseteq> T"
  assumes "uwellformed H\<^sub>1" and "uwellformed H\<^sub>2"
  shows "subgraph H\<^sub>1 (induced_subgraph S G) \<and> subgraph H\<^sub>2 (induced_subgraph T G) \<longleftrightarrow>
         subgraph (uverts H\<^sub>1 \<union> uverts H\<^sub>2, uedges H\<^sub>1 \<union> uedges H\<^sub>2) (induced_subgraph (S \<union> T) G)"
unfolding induced_subgraph_def subgraph_def
apply auto
using all_edges_mono apply blast
using all_edges_mono apply blast
using assms(1,2) wellformed_all_edges[OF assms(3)] wellformed_all_edges[OF assms(4)] all_edges_mono[OF assms(1)] all_edges_mono[OF assms(2)]
apply auto
done

lemma (in edge_space) induced_subgraph_prob:
  assumes "uverts H \<subseteq> V" and "uwellformed H" and "V \<subseteq> S_verts"
  shows "prob {es \<in> space P. subgraph H (induced_subgraph V (edge_ugraph es))} = p ^ card (uedges H)" (is "prob ?A = _")
proof -
  have "prob ?A = prob (cylinder S_edges (uedges H) {})"
    unfolding cylinder_def space_eq subgraph_def induced_subgraph_def edge_ugraph_def S_edges_def
    by (rule arg_cong[OF Collect_cong]) (metis (no_types) assms(1,2) Pow_iff all_edges_mono fst_conv inf_absorb1 inf_bot_left le_inf_iff snd_conv wellformed_all_edges)
  also have "\<dots> = p ^ card (uedges H)"
    proof (rule cylinder_empty_prob)
      have "uedges H \<subseteq> all_edges (uverts H)"
        by (rule wellformed_all_edges[OF assms(2)])
      also have "all_edges (uverts H) \<subseteq> all_edges S_verts"
        using assms by (auto simp: all_edges_mono[OF subset_trans])
      finally show "uedges H \<subseteq> S_edges"
        unfolding S_edges_def .
    qed
  finally show ?thesis
    .
qed

subsection\<open>Graph isomorphism\<close>

text\<open>We define graph isomorphism slightly different than in the literature. The usual definition
is that two graphs are isomorphic iff there exists a bijection between the vertex sets which
preserves the adjacency. However, this complicates many proofs.

Instead, we define the intuitive mapping operation on graphs. An isomorphism between two graphs
arises if there is a suitable mapping function from the first to the second graph. Later, we show
that this operation can be inverted.\<close>

fun map_ugraph :: "(nat \<Rightarrow> nat) \<Rightarrow> ugraph \<Rightarrow> ugraph" where
"map_ugraph f (V, E) = (f ` V, (\<lambda>e. f ` e) ` E)"

definition isomorphism :: "ugraph \<Rightarrow> ugraph \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
"isomorphism G\<^sub>1 G\<^sub>2 f \<equiv> bij_betw f (uverts G\<^sub>1) (uverts G\<^sub>2) \<and> G\<^sub>2 = map_ugraph f G\<^sub>1"

abbreviation isomorphic :: "ugraph \<Rightarrow> ugraph \<Rightarrow> bool" ("_ \<simeq> _") where
"G\<^sub>1 \<simeq> G\<^sub>2 \<equiv> uwellformed G\<^sub>1 \<and> uwellformed G\<^sub>2 \<and> (\<exists>f. isomorphism G\<^sub>1 G\<^sub>2 f)"

lemma map_ugraph_id: "map_ugraph id = id"
unfolding fun_eq_iff
by simp

lemma map_ugraph_trans: "map_ugraph (g \<circ> f) = (map_ugraph g) \<circ> (map_ugraph f)"
  by (simp add: fun_eq_iff image_image)

lemma map_ugraph_wellformed:
  assumes "uwellformed G" and "inj_on f (uverts G)"
  shows "uwellformed (map_ugraph f G)"
unfolding uwellformed_def
proof safe
  fix e'
  assume "e' \<in> uedges (map_ugraph f G)"
  hence "e' \<in> (\<lambda>e. f ` e) ` (uedges G)"
    by (metis map_ugraph.simps snd_conv surjective_pairing)
  then obtain e where e: "e' = f ` e" "e \<in> uedges G"
    by blast
  hence "card e = 2" "e \<subseteq> uverts G"
    using assms(1) unfolding uwellformed_def by blast+
  thus "card e' = 2"
    using e(1) by (simp add: card_inj_subs[OF assms(2)])

  fix u'
  assume "u' \<in> e'"
  hence "u' \<in> f ` e"
    using e by force
  then obtain u where u: "u' = f u" "u \<in> e"
    by blast
  hence "u \<in> uverts G"
    using assms(1) e(2) unfolding uwellformed_def by blast
  hence "u' \<in> f ` uverts G"
    using u(1) by simp
  thus "u' \<in> uverts (map_ugraph f G)"
    by (metis map_ugraph.simps fst_conv surjective_pairing)
qed

lemma map_ugraph_finite: "finite_graph G \<Longrightarrow> finite_graph (map_ugraph f G)"
unfolding finite_graph_def
by (metis finite_imageI fst_conv map_ugraph.simps snd_conv surjective_pairing)

lemma map_ugraph_preserves_sub:
  assumes "subgraph G\<^sub>1 G\<^sub>2"
  shows "subgraph (map_ugraph f G\<^sub>1) (map_ugraph f G\<^sub>2)"
proof -
  have "f ` uverts G\<^sub>1 \<subseteq> f ` uverts G\<^sub>2" "(\<lambda>e. f ` e) ` uedges G\<^sub>1 \<subseteq> (\<lambda>e. f ` e) ` uedges G\<^sub>2"
    using assms(1) unfolding subgraph_def by auto
  thus ?thesis
    unfolding subgraph_def by (metis map_ugraph.simps fst_conv snd_conv surjective_pairing)
qed

lemma isomorphic_refl: "uwellformed G \<Longrightarrow> G \<simeq> G"
unfolding isomorphism_def
by (metis bij_betw_id id_def map_ugraph_id)

lemma isomorphic_trans:
  assumes "G\<^sub>1 \<simeq> G\<^sub>2" and "G\<^sub>2 \<simeq> G\<^sub>3"
  shows "G\<^sub>1 \<simeq> G\<^sub>3"
proof -
  from assms obtain f\<^sub>1 f\<^sub>2 where
    bij: "bij_betw f\<^sub>1 (uverts G\<^sub>1) (uverts G\<^sub>2)" "bij_betw f\<^sub>2 (uverts G\<^sub>2) (uverts G\<^sub>3)" and
    map: "G\<^sub>2 = map_ugraph f\<^sub>1 G\<^sub>1" "G\<^sub>3 = map_ugraph f\<^sub>2 G\<^sub>2"
    unfolding isomorphism_def by blast

  let ?f = "f\<^sub>2 \<circ> f\<^sub>1"
  have "bij_betw ?f (uverts G\<^sub>1) (uverts G\<^sub>3)"
    using bij by (simp add: bij_betw_comp_iff)
  moreover have "G\<^sub>3 = map_ugraph ?f G\<^sub>1"
    using map by (simp add: map_ugraph_trans)
  moreover have "uwellformed G\<^sub>1" "uwellformed G\<^sub>3"
    using assms unfolding isomorphism_def by simp+
  ultimately show "G\<^sub>1 \<simeq> G\<^sub>3"
    unfolding isomorphism_def by blast
qed

lemma isomorphic_sym:
  assumes "G\<^sub>1 \<simeq> G\<^sub>2"
  shows "G\<^sub>2 \<simeq> G\<^sub>1"
proof safe
  from assms obtain f where "isomorphism G\<^sub>1 G\<^sub>2 f"
    by blast
  hence bij: "bij_betw f (uverts G\<^sub>1) (uverts G\<^sub>2)" and map: "G\<^sub>2 = map_ugraph f G\<^sub>1"
    unfolding isomorphism_def by auto

  let ?f' = "inv_into (uverts G\<^sub>1) f"
  have bij': "bij_betw ?f' (uverts G\<^sub>2) (uverts G\<^sub>1)"
    by (rule bij_betw_inv_into) fact
  moreover have "uverts G\<^sub>1 = ?f' ` uverts G\<^sub>2"
    using bij' unfolding bij_betw_def by force
  moreover have "uedges G\<^sub>1 = (\<lambda>e. ?f' ` e) ` uedges G\<^sub>2"
    proof -
      have "uedges G\<^sub>1 = id ` uedges G\<^sub>1"
        by simp
      also have "\<dots> = (\<lambda>e. ?f' ` (f ` e)) ` uedges G\<^sub>1"
        proof (rule image_cong)
          fix a
          assume "a \<in> uedges G\<^sub>1"
          hence "a \<subseteq> uverts G\<^sub>1"
            using assms unfolding isomorphism_def uwellformed_def by blast
          thus "id a = inv_into (uverts G\<^sub>1) f ` f ` a"
            by (metis (full_types) id_def bij bij_betw_imp_inj_on inv_into_image_cancel)
        qed simp
      also have "\<dots> = (\<lambda>e. ?f' ` e) ` ((\<lambda>e. f ` e) ` uedges G\<^sub>1)"
        by (rule image_image[symmetric])
      also have "\<dots> = (\<lambda>e. ?f' ` e) ` uedges G\<^sub>2"
        using bij map by (metis map_ugraph.simps prod.collapse snd_eqD)
      finally show ?thesis
        .
    qed
  ultimately have "isomorphism G\<^sub>2 G\<^sub>1 ?f'"
    unfolding isomorphism_def by (metis map_ugraph.simps split_pairs)
  thus "\<exists>f. isomorphism G\<^sub>2 G\<^sub>1 f"
    by blast
qed (auto simp: assms)

lemma isomorphic_cards:
  assumes "G\<^sub>1 \<simeq> G\<^sub>2"
  shows
    "card (uverts G\<^sub>1) = card (uverts G\<^sub>2)" (is "?V")
    "card (uedges G\<^sub>1) = card (uedges G\<^sub>2)" (is "?E")
proof -
  from assms obtain f where
    bij: "bij_betw f (uverts G\<^sub>1) (uverts G\<^sub>2)" and
    map: "G\<^sub>2 = map_ugraph f G\<^sub>1"
    unfolding isomorphism_def by blast
  from assms have wellformed: "uwellformed G\<^sub>1" "uwellformed G\<^sub>2"
    by simp+

  show ?V
    by (rule bij_betw_same_card[OF bij])

  let ?g = "\<lambda>e. f ` e"
  have "bij_betw ?g (Pow (uverts G\<^sub>1)) (Pow (uverts G\<^sub>2))"
    by (rule bij_lift[OF bij])
  moreover have "uedges G\<^sub>1 \<subseteq> Pow (uverts G\<^sub>1)"
    using wellformed(1) unfolding uwellformed_def by blast
  ultimately have "card (?g ` uedges G\<^sub>1) = card (uedges G\<^sub>1)"
    unfolding bij_betw_def by (metis card_inj_subs)
  thus ?E
    by (metis map map_ugraph.simps snd_conv surjective_pairing)
qed

subsection\<open>Isomorphic subgraphs\<close>

text\<open>The somewhat sloppy term `isomorphic subgraph' denotes a subgraph which is isomorphic to a
fixed other graph. For example, saying that a graph contains a triangle usually means that it
contains \emph{any} triangle, not the specific triangle with the nodes $1$, $2$ and $3$. Hence, such
a graph would have a triangle as an isomorphic subgraph.\<close>

definition subgraph_isomorphic :: "ugraph \<Rightarrow> ugraph \<Rightarrow> bool" ("_ \<sqsubseteq> _") where
"G' \<sqsubseteq> G \<equiv> uwellformed G \<and> (\<exists>G''. G' \<simeq> G'' \<and> subgraph G'' G)"

lemma subgraph_is_subgraph_isomorphic: "\<lbrakk> uwellformed G'; uwellformed G; subgraph G' G \<rbrakk> \<Longrightarrow> G' \<sqsubseteq> G"
unfolding subgraph_isomorphic_def
by (metis isomorphic_refl)

lemma isomorphic_is_subgraph_isomorphic: "G\<^sub>1 \<simeq> G\<^sub>2 \<Longrightarrow> G\<^sub>1 \<sqsubseteq> G\<^sub>2"
unfolding subgraph_isomorphic_def
by (metis subgraph_refl)

lemma subgraph_isomorphic_refl: "uwellformed G \<Longrightarrow> G \<sqsubseteq> G"
unfolding subgraph_isomorphic_def
by (metis isomorphic_refl subgraph_refl)

lemma subgraph_isomorphic_pre_iso_closed:
  assumes "G\<^sub>1 \<simeq> G\<^sub>2" and "G\<^sub>2 \<sqsubseteq> G\<^sub>3"
  shows "G\<^sub>1 \<sqsubseteq> G\<^sub>3"
unfolding subgraph_isomorphic_def
proof
  show "uwellformed G\<^sub>3"
    using assms unfolding subgraph_isomorphic_def by blast
next
  from assms(2) obtain G\<^sub>2' where "G\<^sub>2 \<simeq> G\<^sub>2'" "subgraph G\<^sub>2' G\<^sub>3"
    unfolding subgraph_isomorphic_def by blast
  moreover with assms(1) have "G\<^sub>1 \<simeq> G\<^sub>2'"
    by (metis isomorphic_trans)
  ultimately show "\<exists>G''. G\<^sub>1 \<simeq> G'' \<and> subgraph G'' G\<^sub>3"
    by blast
qed

lemma subgraph_isomorphic_pre_subgraph_closed:
  assumes "uwellformed G\<^sub>1" and "subgraph G\<^sub>1 G\<^sub>2" and "G\<^sub>2 \<sqsubseteq> G\<^sub>3"
  shows "G\<^sub>1 \<sqsubseteq> G\<^sub>3"
unfolding subgraph_isomorphic_def
proof
  show "uwellformed G\<^sub>3"
    using assms unfolding subgraph_isomorphic_def by blast
next
  from assms(3) obtain G\<^sub>2' where "G\<^sub>2 \<simeq> G\<^sub>2'" "subgraph G\<^sub>2' G\<^sub>3"
    unfolding subgraph_isomorphic_def by blast
  then obtain f where bij: "bij_betw f (uverts G\<^sub>2) (uverts G\<^sub>2')" "G\<^sub>2' = map_ugraph f G\<^sub>2"
    unfolding isomorphism_def by blast
  let ?G\<^sub>1' = "map_ugraph f G\<^sub>1"

  have "bij_betw f (uverts G\<^sub>1) (f ` uverts G\<^sub>1)"
    using bij(1) assms(2) unfolding subgraph_def by (auto intro: bij_betw_subset)
  moreover hence "uwellformed ?G\<^sub>1'"
    using map_ugraph_wellformed[OF assms(1)] unfolding bij_betw_def ..
  ultimately have "G\<^sub>1 \<simeq> ?G\<^sub>1'"
    using assms(1) unfolding isomorphism_def by (metis map_ugraph.simps fst_conv surjective_pairing)
  moreover have "subgraph ?G\<^sub>1' G\<^sub>3" (* Yes, I will TOTALLY understand that step tomorrow. *)
    using subgraph_trans[OF map_ugraph_preserves_sub[OF assms(2)]] bij(2) \<open>subgraph G\<^sub>2' G\<^sub>3\<close> by simp
  ultimately show "\<exists>G''. G\<^sub>1 \<simeq> G'' \<and> subgraph G'' G\<^sub>3"
    by blast
qed

lemmas subgraph_isomorphic_pre_closed = subgraph_isomorphic_pre_subgraph_closed subgraph_isomorphic_pre_iso_closed

lemma subgraph_isomorphic_trans[trans]:
  assumes "G\<^sub>1 \<sqsubseteq> G\<^sub>2" and "G\<^sub>2 \<sqsubseteq> G\<^sub>3"
  shows "G\<^sub>1 \<sqsubseteq> G\<^sub>3"
proof -
  from assms(1) obtain G where "G\<^sub>1 \<simeq> G" "subgraph G G\<^sub>2"
    unfolding subgraph_isomorphic_def by blast
  thus ?thesis
    using assms(2) by (metis subgraph_isomorphic_pre_closed)
qed

lemma subgraph_isomorphic_post_iso_closed: "\<lbrakk> H \<sqsubseteq> G; G \<simeq> G' \<rbrakk> \<Longrightarrow> H \<sqsubseteq> G'"
using isomorphic_is_subgraph_isomorphic subgraph_isomorphic_trans
by blast

lemmas subgraph_isomorphic_post_closed = subgraph_isomorphic_post_iso_closed

lemmas subgraph_isomorphic_closed = subgraph_isomorphic_pre_closed subgraph_isomorphic_post_closed

subsection\<open>Density\<close>

text\<open>The density of a graph is the quotient of the number of edges and the number of vertices of
a graph.\<close>

definition density :: "ugraph \<Rightarrow> real" where
"density G = card (uedges G) / card (uverts G)"

text\<open>The maximum density of a graph is the density of its densest nonempty subgraph.\<close>

definition max_density :: "ugraph \<Rightarrow> real" where
"max_density G = Lattices_Big.Max (density ` nonempty_subgraphs G)"

text\<open>We prove some obvious results about the maximum density, such as that there is a subgraph
which has the maximum density and that the (maximum) density is preserved by isomorphisms. The
proofs are a bit complicated by the fact that most facts about @{term Lattices_Big.Max} require
non-emptiness of the target set, but we need that anyway to get a value out of it.\<close>

lemma subgraph_has_max_density:
  assumes "finite_graph G" and "nonempty_graph G" and "uwellformed G"
  shows "\<exists>G'. density G' = max_density G \<and> subgraph G' G \<and> nonempty_graph G' \<and> finite_graph G' \<and> uwellformed G'"
proof -
  have "G \<in> nonempty_subgraphs G"
    unfolding nonempty_subgraphs_def using subgraph_refl assms by simp
  hence "density G \<in> density ` nonempty_subgraphs G"
    by simp
  hence "(density ` nonempty_subgraphs G) \<noteq> {}"
    by fast
  hence "max_density G \<in> (density ` nonempty_subgraphs G)"
    unfolding max_density_def by (auto simp add: nonempty_subgraphs_finite[OF assms(1)] Max.closed)
  thus ?thesis
    unfolding nonempty_subgraphs_def using subgraph_finite[OF assms(1)] by force
qed

lemma max_density_is_max:
  assumes "finite_graph G" and "finite_graph G'" and "nonempty_graph G'" and "uwellformed G'" and "subgraph G' G"
  shows "density G' \<le> max_density G"
unfolding max_density_def
proof (rule Max_ge)
  show "finite (density ` nonempty_subgraphs G)"
    using assms(1) by (simp add: nonempty_subgraphs_finite)
next
  show "density G' \<in> density ` nonempty_subgraphs G"
    unfolding nonempty_subgraphs_def using assms by blast
qed

lemma max_density_gr_zero:
  assumes "finite_graph G" and "nonempty_graph G" and "uwellformed G"
  shows "0 < max_density G"
proof -
  have "0 < card (uverts G)" "0 < card (uedges G)"
    using assms unfolding finite_graph_def nonempty_graph_def by auto
  hence "0 < density G"
    unfolding density_def by simp
  also have "density G \<le> max_density G"
    using assms by (simp add: max_density_is_max subgraph_refl)
  finally show ?thesis
    .
qed

lemma isomorphic_density:
  assumes "G\<^sub>1 \<simeq> G\<^sub>2"
  shows "density G\<^sub>1 = density G\<^sub>2"
unfolding density_def
using isomorphic_cards[OF assms]
by simp

lemma isomorphic_max_density:
  assumes "G\<^sub>1 \<simeq> G\<^sub>2" and "nonempty_graph G\<^sub>1" and "nonempty_graph G\<^sub>2" and "finite_graph G\<^sub>1" and "finite_graph G\<^sub>2"
  shows "max_density G\<^sub>1 = max_density G\<^sub>2"
proof -
  \<comment> \<open>The proof strategy is not completely straightforward. We first show that if two graphs are
       isomorphic, the maximum density of one graph is less or equal than the maximum density of
       the other graph. The reason is that this proof is quite long and the desired result directly
       follows from the symmetry of the isomorphism relation.\footnote{Some famous mathematician
       once said that if you prove that $a \le b$ and $b \le a$, you know \emph{that} these
       numbers are equal, but not \emph{why}. Since many proofs in this work are mostly opaque to
       me, I can live with that.}\<close>
  {
    fix A B
    assume A: "nonempty_graph A" "finite_graph A"
    assume iso: "A \<simeq> B"

    then obtain f where f: "B = map_ugraph f A" "bij_betw f (uverts A) (uverts B)"
      unfolding isomorphism_def by blast
    have wellformed: "uwellformed A"
      using iso unfolding isomorphism_def by simp
    \<comment> \<open>We observe that the set of densities of the subgraphs does not change if we map the
         subgraphs first.\<close>
    have "density ` nonempty_subgraphs A = density ` (map_ugraph f ` nonempty_subgraphs A)"
      proof (rule image_comp_cong)
        fix G
        assume "G \<in> nonempty_subgraphs A"
        hence "uverts G \<subseteq> uverts A" "uwellformed G"
          unfolding nonempty_subgraphs_def subgraph_def by simp+
        hence "inj_on f (uverts G)"
          using f(2) unfolding bij_betw_def by (metis subset_inj_on)
        hence "G \<simeq> map_ugraph f G"
          unfolding isomorphism_def bij_betw_def
          by (metis map_ugraph.simps fst_conv surjective_pairing map_ugraph_wellformed \<open>uwellformed G\<close>)
        thus "density G = density (map_ugraph f G)"
          by (fact isomorphic_density)
      qed
    \<comment> \<open>Additionally, we show that the operations @{term nonempty_subgraphs} and @{term map_ugraph}
         can be swapped without changing the densities. This is an obvious result, because
         @{term map_ugraph} does not change the structure of a graph. Still, the proof is a bit
         hairy, which is why we only show inclusion in one direction and use symmetry of isomorphism
         later.\<close>
    also have "\<dots> \<subseteq> density ` nonempty_subgraphs (map_ugraph f A)"
      proof (rule image_mono, rule subsetI)
        fix G''
        assume "G'' \<in> map_ugraph f ` nonempty_subgraphs A"
        then obtain G' where G_subst: "G'' = map_ugraph f G'" "G' \<in> nonempty_subgraphs A"
          by blast
        hence G': "subgraph G' A" "nonempty_graph G'" "uwellformed G'"
          unfolding nonempty_subgraphs_def by auto
        hence "inj_on f (uverts G')"
          using f unfolding bij_betw_def subgraph_def by (metis subset_inj_on)
        hence "uwellformed G''"
          using map_ugraph_wellformed G' G_subst by simp
        moreover have "nonempty_graph G''"
          using G' G_subst unfolding nonempty_graph_def by (metis map_ugraph.simps fst_conv snd_conv surjective_pairing empty_is_image)
        moreover have "subgraph G'' (map_ugraph f A)"
          using map_ugraph_preserves_sub G' G_subst by simp
        ultimately show "G'' \<in> nonempty_subgraphs (map_ugraph f A)"
          unfolding nonempty_subgraphs_def by simp
      qed
    finally have "density ` nonempty_subgraphs A \<subseteq> density ` nonempty_subgraphs (map_ugraph f A)"
      .
    hence "max_density A \<le> max_density (map_ugraph f A)"
      unfolding max_density_def
      proof (rule Max_mono)
        have "A \<in> nonempty_subgraphs A"
          using A iso unfolding nonempty_subgraphs_def by (simp add: subgraph_refl)
        thus "density ` nonempty_subgraphs A \<noteq> {}"
          by blast
      next
        have "finite (nonempty_subgraphs (map_ugraph f A))"
          by (rule nonempty_subgraphs_finite[OF map_ugraph_finite[OF A(2)]])
        thus "finite (density ` nonempty_subgraphs (map_ugraph f A))"
          by blast
      qed
    hence "max_density A \<le> max_density B"
      by (subst f)
  }
  note le = this

  show ?thesis
    using le[OF assms(2) assms(4) assms(1)] le[OF assms(3) assms(5) isomorphic_sym[OF assms(1)]]
    by (fact antisym)
qed

subsection\<open>Fixed selectors\<close>

text\<open>\label{sec:selector}
In the proof of the main theorem in the lecture notes, the concept of a ``fixed copy'' of a graph is
fundamental.

Let $H$ be a fixed graph. A `fixed selector' is basically a function mapping a set with the same
size as the vertex set of $H$ to a new graph which is isomorphic to $H$ and its vertex set is the
same as the input set.\footnote{We call such a selector \emph{fixed} because its result is
deterministic.}\<close>

definition "is_fixed_selector H f = (\<forall>V. finite V \<and> card (uverts H) = card V \<longrightarrow> H \<simeq> f V \<and> uverts (f V) = V)"

text\<open>Obviously, there may be many possible fixed selectors for a given graph. First, we show
that there is always at least one. This is sufficient, because we can always obtain that one and
use its properties without knowing exactly which one we chose.\<close>

lemma ex_fixed_selector:
  assumes "uwellformed H" and "finite_graph H"
  obtains f where "is_fixed_selector H f"
proof
  \<comment> \<open>I guess this is the only place in the whole work where we make use of a nifty little HOL
       feature called \emph{SOME}, which is basically Hilbert's choice operator. The reason is that
       any bijection between the the vertex set of @{term H} and the input set gives rise to a
       fixed selector function. In the lecture notes, a specific bijection was defined, but this
       is shorter and more elegant.\<close>
  let ?bij = "\<lambda>V. SOME g. bij_betw g (uverts H) V"
  let ?f = "\<lambda>V. map_ugraph (?bij V) H"
  {
    fix V :: "uvert set"
    assume "finite V" "card (uverts H) = card V"
    moreover have "finite (uverts H)"
      using assms unfolding finite_graph_def by simp
    ultimately have "bij_betw (?bij V) (uverts H) V"
      by (metis finite_same_card_bij someI_ex)
    moreover hence *: "uverts (?f V) = V \<and> uwellformed (?f V)"
      using map_ugraph_wellformed[OF assms(1)]
      by (metis bij_betw_def map_ugraph.simps fst_conv surjective_pairing)
    ultimately have **: "H \<simeq> ?f V"
      unfolding isomorphism_def using assms(1) by auto
    note * **
  }
  thus "is_fixed_selector H ?f"
    unfolding is_fixed_selector_def by blast
qed

lemma fixed_selector_induced_subgraph:
  assumes "is_fixed_selector H f" and "card (uverts H) = card V" and "finite V"
  assumes sub: "subgraph (f V) (induced_subgraph V G)" and V: "V \<subseteq> uverts G" and G: "uwellformed G"
  shows "H \<sqsubseteq> G"
proof -
  have post: "H \<simeq> f V" "uverts (f V) = V"
    using assms unfolding is_fixed_selector_def by auto

  have "H \<sqsubseteq> f V"
    by (rule isomorphic_is_subgraph_isomorphic)
       (simp add: post)
  also have "f V \<sqsubseteq> induced_subgraph V G"
    by (rule subgraph_is_subgraph_isomorphic)
       (auto simp: induced_wellformed[OF G V] post sub)
  also have "\<dots> \<sqsubseteq> G"
    by (rule subgraph_is_subgraph_isomorphic[OF induced_wellformed])
       (auto simp: G V induced_is_subgraph(1)[OF V])
  finally show "H \<sqsubseteq> G"
    .
qed

end
