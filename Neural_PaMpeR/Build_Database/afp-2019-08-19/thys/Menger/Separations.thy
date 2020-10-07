section \<open>Separations\<close>

theory Separations imports Helpers Graph begin

locale Separation = v0_v1_Digraph +
  fixes S :: "'a set"
  assumes S_V: "S \<subseteq> V"
    and v0_notin_S: "v0 \<notin> S"
    and v1_notin_S: "v1 \<notin> S"
    and S_separates: "\<And>xs. v0\<leadsto>xs\<leadsto>v1 \<Longrightarrow> set xs \<inter> S \<noteq> {}"

lemma (in Separation) finite_S [simp]: "finite S" using S_V finite_subset finite_vertex_set by auto

lemma (in v0_v1_Digraph) subgraph_separation_extend:
  assumes "v \<noteq> v0" "v \<noteq> v1" "v \<in> V"
    and "Separation (remove_vertex v) v0 v1 S"
  shows "Separation G v0 v1 (insert v S)"
proof (rule Separation.intro)
  interpret G: Separation "remove_vertex v" v0 v1 S using assms(4) .
  show "v0_v1_Digraph G v0 v1" using v0_v1_Digraph_axioms .
  show "Separation_axioms G v0 v1 (insert v S)" proof
    show "insert v S \<subseteq> V" by (meson G.S_V assms(3) insert_subsetI remove_vertex_V' subset_trans)
    show "v0 \<notin> insert v S" using G.v0_notin_S assms(1) by blast
    show "v1 \<notin> insert v S" using G.v1_notin_S assms(2) by blast
  next
    fix xs assume "v0 \<leadsto>xs\<leadsto> v1"
    show "set xs \<inter> insert v S \<noteq> {}" proof (cases)
      assume "v \<notin> set xs"
      then have "v0 \<leadsto>xs\<leadsto>\<^bsub>remove_vertex v\<^esub> v1"
        using remove_vertex_path_from_to \<open>v0 \<leadsto>xs\<leadsto> v1\<close> assms(3) by blast
      then show ?thesis by (simp add: G.S_separates)
    qed simp
  qed
qed

lemma (in v0_v1_Digraph) subgraph_separation_min_size:
  assumes "v \<noteq> v0" "v \<noteq> v1" "v \<in> V"
    and no_small_separation: "\<And>S. Separation G v0 v1 S \<Longrightarrow> card S \<ge> Suc n"
    and "Separation (remove_vertex v) v0 v1 S"
  shows "card S \<ge> n"
  using subgraph_separation_extend
  by (metis Separation.finite_S Suc_leD assms card_insert_disjoint insert_absorb not_less_eq_eq)

lemma (in v0_v1_Digraph) path_exists_if_no_separation:
  assumes "S \<subseteq> V" "v0 \<notin> S" "v1 \<notin> S" "\<not>Separation G v0 v1 S"
  shows "\<exists>xs. v0\<leadsto>xs\<leadsto>v1 \<and> set xs \<inter> S = {}"
  by (meson assms Separation.intro Separation_axioms.intro v0_v1_Digraph_axioms)

end
