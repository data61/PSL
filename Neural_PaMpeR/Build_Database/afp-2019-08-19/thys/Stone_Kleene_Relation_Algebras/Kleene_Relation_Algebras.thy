(* Title:      Kleene Relation Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Kleene Relation Algebras\<close>

text \<open>
This theory combines Kleene algebras with Stone relation algebras.
Relation algebras with transitive closure have been studied by \cite{Ng1984}.
The weakening to Stone relation algebras allows us to talk about reachability in weighted graphs, for example.

Many results in this theory are used in the correctness proof of Prim's minimum spanning tree algorithm.
In particular, they are concerned with the exchange property, preservation of parts of the invariant and with establishing parts of the postcondition.
\<close>

theory Kleene_Relation_Algebras

imports Stone_Relation_Algebras.Relation_Algebras Kleene_Algebras

begin

text \<open>
We first note that bounded distributive lattices can be expanded to Kleene algebras by reusing some of the operations.
\<close>

sublocale bounded_distrib_lattice < comp_inf: bounded_kleene_algebra where star = "\<lambda>x . top" and one = top and times = inf
  apply unfold_locales
  apply (simp add: inf.assoc)
  apply simp
  apply simp
  apply (simp add: le_infI2)
  apply (simp add: inf_sup_distrib2)
  apply simp
  apply simp
  apply simp
  apply simp
  apply simp
  apply (simp add: inf_sup_distrib1)
  apply simp
  apply simp
  by (simp add: inf_assoc)

text \<open>
We add the Kleene star operation to each of bounded distributive allegories, pseudocomplemented distributive allegories and Stone relation algebras.
We start with single-object bounded distributive allegories.
\<close>

class bounded_distrib_kleene_allegory = bounded_distrib_allegory + kleene_algebra
begin

subclass bounded_kleene_algebra ..

lemma conv_star_conv:
  "x\<^sup>\<star> \<le> x\<^sup>T\<^sup>\<star>\<^sup>T"
proof -
  have "x\<^sup>T\<^sup>\<star> * x\<^sup>T \<le> x\<^sup>T\<^sup>\<star>"
    by (simp add: star.right_plus_below_circ)
  hence 1: "x * x\<^sup>T\<^sup>\<star>\<^sup>T \<le> x\<^sup>T\<^sup>\<star>\<^sup>T"
    using conv_dist_comp conv_isotone by fastforce
  have "1 \<le> x\<^sup>T\<^sup>\<star>\<^sup>T"
    by (simp add: reflexive_conv_closed star.circ_reflexive)
  hence "1 \<squnion> x * x\<^sup>T\<^sup>\<star>\<^sup>T \<le> x\<^sup>T\<^sup>\<star>\<^sup>T"
    using 1 by simp
  thus ?thesis
    using star_left_induct by fastforce
qed

text \<open>
It follows that star and converse commute.
\<close>

lemma conv_star_commute:
  "x\<^sup>\<star>\<^sup>T = x\<^sup>T\<^sup>\<star>"
proof (rule antisym)
  show "x\<^sup>\<star>\<^sup>T \<le> x\<^sup>T\<^sup>\<star>"
    using conv_star_conv conv_isotone by fastforce
next
  show "x\<^sup>T\<^sup>\<star> \<le> x\<^sup>\<star>\<^sup>T"
    by (metis conv_star_conv conv_involutive)
qed

lemma conv_plus_commute:
  "x\<^sup>+\<^sup>T = x\<^sup>T\<^sup>+"
  by (simp add: conv_dist_comp conv_star_commute star_plus)

text \<open>
The following results are variants of a separation lemma of Kleene algebras.
\<close>

lemma cancel_separate_2:
  assumes "x * y \<le> 1"
    shows "((w \<sqinter> x) \<squnion> (z \<sqinter> y))\<^sup>\<star> = (z \<sqinter> y)\<^sup>\<star> * (w \<sqinter> x)\<^sup>\<star>"
proof -
  have "(w \<sqinter> x) * (z \<sqinter> y) \<le> 1"
    by (meson assms comp_isotone order.trans inf.cobounded2)
  thus ?thesis
    using cancel_separate_1 sup_commute by simp
qed

lemma cancel_separate_3:
  assumes "x * y \<le> 1"
    shows "(w \<sqinter> x)\<^sup>\<star> * (z \<sqinter> y)\<^sup>\<star> = (w \<sqinter> x)\<^sup>\<star> \<squnion> (z \<sqinter> y)\<^sup>\<star>"
proof -
  have "(w \<sqinter> x) * (z \<sqinter> y) \<le> 1"
    by (meson assms comp_isotone order.trans inf.cobounded2)
  thus ?thesis
    by (simp add: cancel_separate_eq)
qed

lemma cancel_separate_4:
  assumes "z * y \<le> 1"
      and "w \<le> y \<squnion> z"
      and "x \<le> y \<squnion> z"
    shows "w\<^sup>\<star> * x\<^sup>\<star> = (w \<sqinter> y)\<^sup>\<star> * ((w \<sqinter> z)\<^sup>\<star> \<squnion> (x \<sqinter> y)\<^sup>\<star>) * (x \<sqinter> z)\<^sup>\<star>"
proof -
  have "w\<^sup>\<star> * x\<^sup>\<star> = ((w \<sqinter> y) \<squnion> (w \<sqinter> z))\<^sup>\<star> * ((x \<sqinter> y) \<squnion> (x \<sqinter> z))\<^sup>\<star>"
    by (metis assms(2,3) inf.orderE inf_sup_distrib1)
  also have "... = (w \<sqinter> y)\<^sup>\<star> * ((w \<sqinter> z)\<^sup>\<star> * (x \<sqinter> y)\<^sup>\<star>) * (x \<sqinter> z)\<^sup>\<star>"
    by (metis assms(1) cancel_separate_2 sup_commute mult_assoc)
  finally show ?thesis
    by (simp add: assms(1) cancel_separate_3)
qed

lemma cancel_separate_5:
  assumes "w * z\<^sup>T \<le> 1"
    shows "w \<sqinter> x * (y \<sqinter> z) \<le> y"
proof -
  have "w \<sqinter> x * (y \<sqinter> z) \<le> (x \<sqinter> w * (y \<sqinter> z)\<^sup>T) * (y \<sqinter> z)"
    by (metis dedekind_2 inf_commute)
  also have "... \<le> w * z\<^sup>T * (y \<sqinter> z)"
    by (simp add: conv_dist_inf inf.coboundedI2 mult_left_isotone mult_right_isotone)
  also have "... \<le> y \<sqinter> z"
    by (metis assms mult_1_left mult_left_isotone)
  finally show ?thesis
    by simp
qed

lemma cancel_separate_6:
  assumes "z * y \<le> 1"
      and "w \<le> y \<squnion> z"
      and "x \<le> y \<squnion> z"
      and "v * z\<^sup>T \<le> 1"
      and "v \<sqinter> y\<^sup>\<star> = bot"
    shows "v \<sqinter> w\<^sup>\<star> * x\<^sup>\<star> \<le> x \<squnion> w"
proof -
  have "v \<sqinter> (w \<sqinter> y)\<^sup>\<star> * (x \<sqinter> y)\<^sup>\<star> \<le> v \<sqinter> y\<^sup>\<star> * (x \<sqinter> y)\<^sup>\<star>"
    using comp_inf.mult_right_isotone mult_left_isotone star_isotone by simp
  also have "... \<le> v \<sqinter> y\<^sup>\<star>"
    by (simp add: inf.coboundedI2 star.circ_increasing star.circ_mult_upper_bound star_right_induct_mult)
  finally have 1: "v \<sqinter> (w \<sqinter> y)\<^sup>\<star> * (x \<sqinter> y)\<^sup>\<star> = bot"
    using assms(5) le_bot by simp
  have "v \<sqinter> w\<^sup>\<star> * x\<^sup>\<star> = v \<sqinter> (w \<sqinter> y)\<^sup>\<star> * ((w \<sqinter> z)\<^sup>\<star> \<squnion> (x \<sqinter> y)\<^sup>\<star>) * (x \<sqinter> z)\<^sup>\<star>"
    using assms(1-3) cancel_separate_4 by simp
  also have "... = (v \<sqinter> (w \<sqinter> y)\<^sup>\<star> * ((w \<sqinter> z)\<^sup>\<star> \<squnion> (x \<sqinter> y)\<^sup>\<star>) * (x \<sqinter> z)\<^sup>\<star> * (x \<sqinter> z)) \<squnion> (v \<sqinter> (w \<sqinter> y)\<^sup>\<star> * ((w \<sqinter> z)\<^sup>\<star> \<squnion> (x \<sqinter> y)\<^sup>\<star>))"
    by (metis inf_sup_distrib1 star.circ_back_loop_fixpoint)
  also have "... \<le> x \<squnion> (v \<sqinter> (w \<sqinter> y)\<^sup>\<star> * ((w \<sqinter> z)\<^sup>\<star> \<squnion> (x \<sqinter> y)\<^sup>\<star>))"
    using assms(4) cancel_separate_5 semiring.add_right_mono by simp
  also have "... = x \<squnion> (v \<sqinter> (w \<sqinter> y)\<^sup>\<star> * (w \<sqinter> z)\<^sup>\<star>)"
    using 1 by (simp add: inf_sup_distrib1 mult_left_dist_sup sup_monoid.add_assoc)
  also have "... = x \<squnion> (v \<sqinter> (w \<sqinter> y)\<^sup>\<star> * (w \<sqinter> z)\<^sup>\<star> * (w \<sqinter> z)) \<squnion> (v \<sqinter> (w \<sqinter> y)\<^sup>\<star>)"
    by (metis comp_inf.semiring.distrib_left star.circ_back_loop_fixpoint sup_assoc)
  also have "... \<le> x \<squnion> w \<squnion> (v \<sqinter> (w \<sqinter> y)\<^sup>\<star>)"
    using assms(4) cancel_separate_5 sup_left_isotone sup_right_isotone by simp
  also have "... \<le> x \<squnion> w \<squnion> (v \<sqinter> y\<^sup>\<star>)"
    using comp_inf.mult_right_isotone star_isotone sup_right_isotone by simp
  finally show ?thesis
    using assms(5) le_bot by simp
qed

text \<open>
We show several results about the interaction of vectors and the Kleene star.
\<close>

lemma vector_star_1:
  assumes "vector x"
    shows "x\<^sup>T * (x * x\<^sup>T)\<^sup>\<star> \<le> x\<^sup>T"
proof -
  have "x\<^sup>T * (x * x\<^sup>T)\<^sup>\<star> = (x\<^sup>T * x)\<^sup>\<star> * x\<^sup>T"
    by (simp add: star_slide)
  also have "... \<le> top * x\<^sup>T"
    by (simp add: mult_left_isotone)
  also have "... = x\<^sup>T"
    using assms vector_conv_covector by auto
  finally show ?thesis
    .
qed

lemma vector_star_2:
  "vector x \<Longrightarrow> x\<^sup>T * (x * x\<^sup>T)\<^sup>\<star> \<le> x\<^sup>T * bot\<^sup>\<star>"
  by (simp add: star_absorb vector_star_1)

lemma vector_vector_star:
  "vector v \<Longrightarrow> (v * v\<^sup>T)\<^sup>\<star> = 1 \<squnion> v * v\<^sup>T"
  by (simp add: transitive_star vv_transitive)

text \<open>
The following equivalence relation characterises the component trees of a forest.
This is a special case of undirected reachability in a directed graph.
\<close>

abbreviation "forest_components f \<equiv> f\<^sup>T\<^sup>\<star> * f\<^sup>\<star>"

lemma forest_components_equivalence:
  "injective x \<Longrightarrow> equivalence (forest_components x)"
  apply (intro conjI)
  apply (simp add: reflexive_mult_closed star.circ_reflexive)
  apply (metis cancel_separate_1 eq_iff star.circ_transitive_equal)
  by (simp add: conv_dist_comp conv_star_commute)

lemma forest_components_increasing:
  "x \<le> forest_components x"
  by (metis order.trans mult_left_isotone mult_left_one star.circ_increasing star.circ_reflexive)

lemma forest_components_isotone:
  "x \<le> y \<Longrightarrow> forest_components x \<le> forest_components y"
  by (simp add: comp_isotone conv_isotone star_isotone)

lemma forest_components_idempotent:
  "injective x \<Longrightarrow> forest_components (forest_components x) = forest_components x"
  by (metis forest_components_equivalence cancel_separate_1 star.circ_transitive_equal star_involutive)

lemma forest_components_star:
  "injective x \<Longrightarrow> (forest_components x)\<^sup>\<star> = forest_components x"
  using forest_components_equivalence forest_components_idempotent star.circ_transitive_equal by simp

text \<open>
The following lemma shows that the nodes reachable in the graph can be reached by only using edges between reachable nodes.
\<close>

lemma reachable_restrict:
  assumes "vector r"
    shows "r\<^sup>T * g\<^sup>\<star> = r\<^sup>T * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g)\<^sup>\<star>"
proof -
  have 1: "r\<^sup>T \<le> r\<^sup>T * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g)\<^sup>\<star>"
    using mult_right_isotone mult_1_right star.circ_reflexive by fastforce
  have 2: "covector (r\<^sup>T * g\<^sup>\<star>)"
    using assms covector_mult_closed vector_conv_covector by auto
  have "r\<^sup>T * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g)\<^sup>\<star> * g \<le> r\<^sup>T * g\<^sup>\<star> * g"
    by (simp add: mult_left_isotone mult_right_isotone star_isotone)
  also have "... \<le> r\<^sup>T * g\<^sup>\<star>"
    by (simp add: mult_assoc mult_right_isotone star.left_plus_below_circ star_plus)
  finally have "r\<^sup>T * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g)\<^sup>\<star> * g = r\<^sup>T * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g)\<^sup>\<star> * g \<sqinter> r\<^sup>T * g\<^sup>\<star>"
    by (simp add: le_iff_inf)
  also have "... = r\<^sup>T * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g)\<^sup>\<star> * (g \<sqinter> r\<^sup>T * g\<^sup>\<star>)"
    using assms covector_comp_inf covector_mult_closed vector_conv_covector by auto
  also have "... = (r\<^sup>T * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g)\<^sup>\<star> \<sqinter> r\<^sup>T * g\<^sup>\<star>) * (g \<sqinter> r\<^sup>T * g\<^sup>\<star>)"
    by (simp add: inf.absorb2 inf_commute mult_right_isotone star_isotone)
  also have "... = r\<^sup>T * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g)\<^sup>\<star> * (g \<sqinter> r\<^sup>T * g\<^sup>\<star> \<sqinter> (r\<^sup>T * g\<^sup>\<star>)\<^sup>T)"
    using 2 by (metis comp_inf_vector_1)
  also have "... = r\<^sup>T * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g)\<^sup>\<star> * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T \<sqinter> r\<^sup>T * g\<^sup>\<star> \<sqinter> g)"
    using inf_commute inf_assoc by simp
  also have "... = r\<^sup>T * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g)\<^sup>\<star> * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g)"
    using 2 by (metis covector_conv_vector inf_top.right_neutral vector_inf_comp)
  also have "... \<le> r\<^sup>T * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g)\<^sup>\<star>"
    by (simp add: mult_assoc mult_right_isotone star.left_plus_below_circ star_plus)
  finally have "r\<^sup>T * g\<^sup>\<star> \<le> r\<^sup>T * ((r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g)\<^sup>\<star>"
    using 1 star_right_induct by auto
  thus ?thesis
    by (simp add: inf.eq_iff mult_right_isotone star_isotone)
qed

lemma kruskal_acyclic_inv_1:
  assumes "injective f"
      and "e * forest_components f * e = bot"
    shows "(f \<sqinter> top * e * f\<^sup>T\<^sup>\<star>)\<^sup>T * f\<^sup>\<star> * e = bot"
proof -
  let ?q = "top * e * f\<^sup>T\<^sup>\<star>"
  let ?F = "forest_components f"
  have "(f \<sqinter> ?q)\<^sup>T * f\<^sup>\<star> * e = ?q\<^sup>T \<sqinter> f\<^sup>T * f\<^sup>\<star> * e"
    by (metis (mono_tags) comp_associative conv_dist_inf covector_conv_vector inf_vector_comp vector_top_closed)
  also have "... \<le> ?q\<^sup>T \<sqinter> ?F * e"
    using comp_inf.mult_right_isotone mult_left_isotone star.circ_increasing by simp
  also have "... = f\<^sup>\<star> * e\<^sup>T * top \<sqinter> ?F * e"
    by (simp add: conv_dist_comp conv_star_commute mult_assoc)
  also have "... \<le> ?F * e\<^sup>T * top \<sqinter> ?F * e"
    by (metis conv_dist_comp conv_star_commute conv_top inf.sup_left_isotone star.circ_right_top star_outer_increasing mult_assoc)
  also have "... = ?F * (e\<^sup>T * top \<sqinter> ?F * e)"
    by (metis assms(1) forest_components_equivalence equivalence_comp_dist_inf mult_assoc)
  also have "... = (?F \<sqinter> top * e) * ?F * e"
    by (simp add: comp_associative comp_inf_vector_1 conv_dist_comp inf_vector_comp)
  also have "... \<le> top * e * ?F * e"
    by (simp add: mult_left_isotone)
  also have "... = bot"
    using assms(2) mult_assoc by simp
  finally show ?thesis
    by (simp add: bot_unique)
qed

lemma kruskal_forest_components_inf_1:
  assumes "f \<le> w \<squnion> w\<^sup>T"
      and "injective w"
      and "f \<le> forest_components g"
    shows "f * forest_components (forest_components g \<sqinter> w) \<le> forest_components (forest_components g \<sqinter> w)"
proof -
  let ?f = "forest_components g"
  let ?w = "forest_components (?f \<sqinter> w)"
  have "f * ?w = (f \<sqinter> (w \<squnion> w\<^sup>T)) * ?w"
    by (simp add: assms(1) inf.absorb1)
  also have "... = (f \<sqinter> w) * ?w \<squnion> (f \<sqinter> w\<^sup>T) * ?w"
    by (simp add: inf_sup_distrib1 semiring.distrib_right)
  also have "... \<le> (?f \<sqinter> w) * ?w \<squnion> (f \<sqinter> w\<^sup>T) * ?w"
    using assms(3) inf.sup_left_isotone mult_left_isotone sup_left_isotone by simp
  also have "... \<le> (?f \<sqinter> w) * ?w \<squnion> (?f \<sqinter> w\<^sup>T) * ?w"
    using assms(3) inf.sup_left_isotone mult_left_isotone sup_right_isotone by simp
  also have "... = (?f \<sqinter> w) * ?w \<squnion> (?f \<sqinter> w)\<^sup>T * ?w"
    by (simp add: conv_dist_comp conv_dist_inf conv_star_commute)
  also have "... \<le> (?f \<sqinter> w) * ?w \<squnion> ?w"
    by (metis star.circ_loop_fixpoint sup_ge1 sup_right_isotone)
  also have "... = ?w \<squnion> (?f \<sqinter> w) * (?f \<sqinter> w)\<^sup>\<star> \<squnion> (?f \<sqinter> w) * (?f \<sqinter> w)\<^sup>T\<^sup>+ * (?f \<sqinter> w)\<^sup>\<star>"
    by (metis comp_associative mult_left_dist_sup star.circ_loop_fixpoint sup_commute sup_assoc)
  also have "... \<le> ?w \<squnion> (?f \<sqinter> w)\<^sup>\<star> \<squnion> (?f \<sqinter> w) * (?f \<sqinter> w)\<^sup>T\<^sup>+ * (?f \<sqinter> w)\<^sup>\<star>"
    using star.left_plus_below_circ sup_left_isotone sup_right_isotone by auto
  also have "... = ?w \<squnion> (?f \<sqinter> w) * (?f \<sqinter> w)\<^sup>T\<^sup>+ * (?f \<sqinter> w)\<^sup>\<star>"
    by (metis star.circ_loop_fixpoint sup.right_idem)
  also have "... \<le> ?w \<squnion> w * w\<^sup>T * ?w"
    using comp_associative conv_dist_inf mult_isotone sup_right_isotone by simp
  also have "... = ?w"
    by (metis assms(2) coreflexive_comp_top_inf inf.cobounded2 sup.orderE)
  finally show ?thesis
    by simp
qed

lemma kruskal_forest_components_inf:
  assumes "f \<le> w \<squnion> w\<^sup>T"
      and "injective w"
    shows "forest_components f \<le> forest_components (forest_components f \<sqinter> w)"
proof -
  let ?f = "forest_components f"
  let ?w = "forest_components (?f \<sqinter> w)"
  have 1: "1 \<le> ?w"
    by (simp add: reflexive_mult_closed star.circ_reflexive)
  have "f * ?w \<le> ?w"
    using assms forest_components_increasing kruskal_forest_components_inf_1 by simp
  hence 2: "f\<^sup>\<star> \<le> ?w"
    using 1 star_left_induct by fastforce
  have "f\<^sup>T * ?w \<le> ?w"
    apply (rule kruskal_forest_components_inf_1)
    apply (metis assms(1) conv_dist_sup conv_involutive conv_isotone sup_commute)
    apply (simp add: assms(2))
    by (metis le_supI2 star.circ_back_loop_fixpoint star.circ_increasing)
  thus "?f \<le> ?w"
    using 2 star_left_induct by simp
qed

end

text \<open>
We next add the Kleene star to single-object pseudocomplemented distributive allegories.
\<close>

class pd_kleene_allegory = pd_allegory + bounded_distrib_kleene_allegory
begin

text \<open>
The following definitions and results concern acyclic graphs and forests.
\<close>

abbreviation acyclic :: "'a \<Rightarrow> bool" where "acyclic x \<equiv> x\<^sup>+ \<le> -1"

abbreviation forest :: "'a \<Rightarrow> bool" where "forest x \<equiv> injective x \<and> acyclic x"

lemma forest_bot:
  "forest bot"
  by simp

lemma acyclic_star_below_complement:
  "acyclic w \<longleftrightarrow> w\<^sup>T\<^sup>\<star> \<le> -w"
  by (simp add: conv_star_commute schroeder_4_p)

lemma acyclic_star_below_complement_1:
  "acyclic w \<longleftrightarrow> w\<^sup>\<star> \<sqinter> w\<^sup>T = bot"
  using pseudo_complement schroeder_5_p by force

lemma acyclic_star_inf_conv:
  assumes "acyclic w"
  shows "w\<^sup>\<star> \<sqinter> w\<^sup>T\<^sup>\<star> = 1"
proof -
  have "w\<^sup>+ \<sqinter> w\<^sup>T\<^sup>\<star> \<le> (w \<sqinter> w\<^sup>T\<^sup>\<star>) * w\<^sup>\<star>"
    by (metis conv_star_commute dedekind_2 star.circ_transitive_equal)
  also have "... = bot"
    by (metis assms conv_star_commute p_antitone_iff pseudo_complement schroeder_4_p semiring.mult_not_zero star.circ_circ_mult star_involutive star_one)
  finally have "w\<^sup>\<star> \<sqinter> w\<^sup>T\<^sup>\<star> \<le> 1"
    by (metis eq_iff le_bot mult_left_zero star.circ_plus_one star.circ_zero star_left_unfold_equal sup_inf_distrib1)
  thus ?thesis
    by (simp add: inf.antisym star.circ_reflexive)
qed

lemma acyclic_asymmetric:
  "acyclic w \<Longrightarrow> asymmetric w"
  by (simp add: local.dual_order.trans local.pseudo_complement local.schroeder_5_p local.star.circ_increasing)

lemma forest_separate:
  assumes "forest x"
    shows "x\<^sup>\<star> * x\<^sup>T\<^sup>\<star> \<sqinter> x\<^sup>T * x \<le> 1"
proof -
  have "x\<^sup>\<star> * 1 \<le> -x\<^sup>T"
    using assms schroeder_5_p by force
  hence 1: "x\<^sup>\<star> \<sqinter> x\<^sup>T = bot"
    by (simp add: pseudo_complement)
  have "x\<^sup>\<star> \<sqinter> x\<^sup>T * x = (1 \<squnion> x\<^sup>\<star> * x) \<sqinter> x\<^sup>T * x"
    using star.circ_right_unfold_1 by simp
  also have "... = (1 \<sqinter> x\<^sup>T * x) \<squnion> (x\<^sup>\<star> * x \<sqinter> x\<^sup>T * x)"
    by (simp add: inf_sup_distrib2)
  also have "... \<le> 1 \<squnion> (x\<^sup>\<star> * x \<sqinter> x\<^sup>T * x)"
    using sup_left_isotone by simp
  also have "... = 1 \<squnion> (x\<^sup>\<star> \<sqinter> x\<^sup>T) * x"
    by (simp add: assms injective_comp_right_dist_inf)
  also have "... = 1"
    using 1 by simp
  finally have 2: "x\<^sup>\<star> \<sqinter> x\<^sup>T * x \<le> 1"
    .
  hence 3: "x\<^sup>T\<^sup>\<star> \<sqinter> x\<^sup>T * x \<le> 1"
    by (metis (mono_tags, lifting) conv_star_commute conv_dist_comp conv_dist_inf conv_involutive coreflexive_symmetric)
  have "x\<^sup>\<star> * x\<^sup>T\<^sup>\<star> \<sqinter> x\<^sup>T * x \<le> (x\<^sup>\<star> \<squnion> x\<^sup>T\<^sup>\<star>) \<sqinter> x\<^sup>T * x"
    using assms cancel_separate inf.sup_left_isotone by simp
  also have "... \<le> 1"
    using 2 3 by (simp add: inf_sup_distrib2)
  finally show ?thesis
    .
qed

text \<open>
The following definition captures the components of undirected weighted graphs.
\<close>

abbreviation "components g \<equiv> (--g)\<^sup>\<star>"

lemma components_equivalence:
  "symmetric x \<Longrightarrow> equivalence (components x)"
  by (simp add: conv_star_commute conv_complement star.circ_reflexive star.circ_transitive_equal)

lemma components_increasing:
  "x \<le> components x"
  using order_trans pp_increasing star.circ_increasing by blast

lemma components_isotone:
  "x \<le> y \<Longrightarrow> components x \<le> components y"
  by (simp add: pp_isotone star_isotone)

lemma cut_reachable:
  assumes "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
      and "t \<le> g"
    shows "v * -v\<^sup>T \<sqinter> g \<le> (r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>)"
proof -
  have "v * -v\<^sup>T \<sqinter> g \<le> v * top \<sqinter> g"
    using inf.sup_left_isotone mult_right_isotone top_greatest by blast
  also have "... = (r\<^sup>T * t\<^sup>\<star>)\<^sup>T * top \<sqinter> g"
    by (metis assms(1) conv_involutive)
  also have "... \<le> (r\<^sup>T * g\<^sup>\<star>)\<^sup>T * top \<sqinter> g"
    using assms(2) conv_isotone inf.sup_left_isotone mult_left_isotone mult_right_isotone star_isotone by auto
  also have "... \<le> (r\<^sup>T * g\<^sup>\<star>)\<^sup>T * ((r\<^sup>T * g\<^sup>\<star>) * g)"
    by (metis conv_involutive dedekind_1 inf_top.left_neutral)
  also have "... \<le> (r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>)"
    by (simp add: mult_assoc mult_right_isotone star.left_plus_below_circ star_plus)
  finally show ?thesis
    .
qed

text \<open>
The following lemma shows that the predecessors of visited nodes in the minimum spanning tree extending the current tree have all been visited.
\<close>

lemma predecessors_reachable:
  assumes "vector r"
      and "injective r"
      and "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
      and "forest w"
      and "t \<le> w"
      and "w \<le> (r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g"
      and "r\<^sup>T * g\<^sup>\<star> \<le> r\<^sup>T * w\<^sup>\<star>"
    shows "w * v \<le> v"
proof -
  have "w * r \<le> (r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) * r"
    using assms(6) mult_left_isotone by auto
  also have "... \<le> (r\<^sup>T * g\<^sup>\<star>)\<^sup>T * top"
    by (simp add: mult_assoc mult_right_isotone)
  also have "... = (r\<^sup>T * g\<^sup>\<star>)\<^sup>T"
    by (simp add: assms(1) comp_associative conv_dist_comp)
  also have "... \<le> (r\<^sup>T * w\<^sup>\<star>)\<^sup>T"
    by (simp add: assms(7) conv_isotone)
  also have "... = w\<^sup>T\<^sup>\<star> * r"
    by (simp add: conv_dist_comp conv_star_commute)
  also have "... \<le> -w * r"
    using assms(4) by (simp add: mult_left_isotone acyclic_star_below_complement)
  also have "... \<le> -(w * r)"
    by (simp add: assms(2) comp_injective_below_complement)
  finally have 1: "w * r = bot"
    by (simp add: le_iff_inf)
  have "v = t\<^sup>T\<^sup>\<star> * r"
    by (metis assms(3) conv_dist_comp conv_involutive conv_star_commute)
  also have "... = t\<^sup>T * v \<squnion> r"
    by (simp add: calculation star.circ_loop_fixpoint)
  also have "... \<le> w\<^sup>T * v \<squnion> r"
    using assms(5) comp_isotone conv_isotone semiring.add_right_mono by auto
  finally have "w * v \<le> w * w\<^sup>T * v \<squnion> w * r"
    by (simp add: comp_left_dist_sup mult_assoc mult_right_isotone)
  also have "... = w * w\<^sup>T * v"
    using 1 by simp
  also have "... \<le> v"
    using assms(4) by (simp add: star_left_induct_mult_iff star_sub_one)
  finally show ?thesis
    .
qed

subsection \<open>Prim's Algorithm\<close>

text \<open>
The following results are used for proving the correctness of Prim's minimum spanning tree algorithm.
\<close>

subsubsection \<open>Preservation of Invariant\<close>

text \<open>
We first treat the preservation of the invariant.
The following lemma shows that the while-loop preserves that \<open>v\<close> represents the nodes of the constructed tree.
The remaining lemmas in this section show that \<open>t\<close> is a spanning tree.
The exchange property is treated in the following two sections.
\<close>

lemma reachable_inv:
  assumes "vector v"
      and "e \<le> v * -v\<^sup>T"
      and "e * t = bot"
      and "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
    shows "(v \<squnion> e\<^sup>T * top)\<^sup>T = r\<^sup>T * (t \<squnion> e)\<^sup>\<star>"
proof -
  have 1: "v\<^sup>T \<le> r\<^sup>T * (t \<squnion> e)\<^sup>\<star>"
    by (simp add: assms(4) mult_right_isotone star.circ_sub_dist)
  have 2: "(e\<^sup>T * top)\<^sup>T = top * e"
    by (simp add: conv_dist_comp)
  also have "... = top * (v * -v\<^sup>T \<sqinter> e)"
    by (simp add: assms(2) inf_absorb2)
  also have "... \<le> top * (v * top \<sqinter> e)"
    using inf.sup_left_isotone mult_right_isotone top_greatest by blast
  also have "... = top * v\<^sup>T * e"
    by (simp add: comp_inf_vector inf.sup_monoid.add_commute)
  also have "... = v\<^sup>T * e"
    using assms(1) vector_conv_covector by auto
  also have "... \<le> r\<^sup>T * (t \<squnion> e)\<^sup>\<star> * e"
    using 1 by (simp add: mult_left_isotone)
  also have "... \<le> r\<^sup>T * (t \<squnion> e)\<^sup>\<star> * (t \<squnion> e)"
    by (simp add: mult_right_isotone)
  also have "... \<le> r\<^sup>T * (t \<squnion> e)\<^sup>\<star>"
    by (simp add: comp_associative mult_right_isotone star.right_plus_below_circ)
  finally have 3: "(v \<squnion> e\<^sup>T * top)\<^sup>T \<le> r\<^sup>T * (t \<squnion> e)\<^sup>\<star>"
    using 1 by (simp add: conv_dist_sup)
  have "r\<^sup>T \<le> r\<^sup>T * t\<^sup>\<star>"
    using sup.bounded_iff star.circ_back_loop_prefixpoint by blast
  also have "... \<le> (v \<squnion> e\<^sup>T * top)\<^sup>T"
    by (metis assms(4) conv_isotone sup_ge1)
  finally have 4: "r\<^sup>T \<le> (v \<squnion> e\<^sup>T * top)\<^sup>T"
    .
  have "(v \<squnion> e\<^sup>T * top)\<^sup>T * (t \<squnion> e) = (v \<squnion> e\<^sup>T * top)\<^sup>T * t \<squnion> (v \<squnion> e\<^sup>T * top)\<^sup>T * e"
    by (simp add: mult_left_dist_sup)
  also have "... \<le> (v \<squnion> e\<^sup>T * top)\<^sup>T * t \<squnion> top * e"
    using comp_isotone semiring.add_left_mono by auto
  also have "... = v\<^sup>T * t \<squnion> top * e * t \<squnion> top * e"
    using 2 by (simp add: conv_dist_sup mult_right_dist_sup)
  also have "... = v\<^sup>T * t \<squnion> top * e"
    by (simp add: assms(3) comp_associative)
  also have "... \<le> r\<^sup>T * t\<^sup>\<star> \<squnion> top * e"
    by (metis assms(4) star.circ_back_loop_fixpoint sup_ge1 sup_left_isotone)
  also have "... = v\<^sup>T \<squnion> top * e"
    by (simp add: assms(4))
  finally have 5: "(v \<squnion> e\<^sup>T * top)\<^sup>T * (t \<squnion> e) \<le> (v \<squnion> e\<^sup>T * top)\<^sup>T"
    using 2 by (simp add: conv_dist_sup)
  have "r\<^sup>T * (t \<squnion> e)\<^sup>\<star> \<le> (v \<squnion> e\<^sup>T * top)\<^sup>T * (t \<squnion> e)\<^sup>\<star>"
    using 4 by (simp add: mult_left_isotone)
  also have "... \<le> (v \<squnion> e\<^sup>T * top)\<^sup>T"
    using 5 by (simp add: star_right_induct_mult)
  finally show ?thesis
    using 3 by (simp add: inf.eq_iff)
qed

text \<open>
The next result is used to show that the while-loop preserves acyclicity of the constructed tree.
\<close>

lemma acyclic_inv:
  assumes "acyclic t"
      and "vector v"
      and "e \<le> v * -v\<^sup>T"
      and "t \<le> v * v\<^sup>T"
    shows "acyclic (t \<squnion> e)"
proof -
  have "t\<^sup>+ * e \<le> t\<^sup>+ * v * -v\<^sup>T"
    by (simp add: assms(3) comp_associative mult_right_isotone)
  also have "... \<le> v * v\<^sup>T * t\<^sup>\<star> * v * -v\<^sup>T"
    by (simp add: assms(4) mult_left_isotone)
  also have "... \<le> v * top * -v\<^sup>T"
    by (metis mult_assoc mult_left_isotone mult_right_isotone top_greatest)
  also have "... = v * -v\<^sup>T"
    by (simp add: assms(2))
  also have "... \<le> -1"
    by (simp add: pp_increasing schroeder_3_p)
  finally have 1: "t\<^sup>+ * e \<le> -1"
    .
  have 2: "e * t\<^sup>\<star> = e"
    using assms(2-4) et(1) star_absorb by blast
  have "e\<^sup>\<star> = 1 \<squnion> e \<squnion> e * e * e\<^sup>\<star>"
    by (metis star.circ_loop_fixpoint star_square_2 sup_commute)
  also have "... = 1 \<squnion> e"
    using assms(2,3) ee comp_left_zero bot_least sup_absorb1 by simp
  finally have 3: "e\<^sup>\<star> = 1 \<squnion> e"
    .
  have "e \<le> v * -v\<^sup>T"
    by (simp add: assms(3))
  also have "... \<le> -1"
    by (simp add: pp_increasing schroeder_3_p)
  finally have 4: "t\<^sup>+ * e \<squnion> e \<le> -1"
    using 1 by simp
  have "(t \<squnion> e)\<^sup>+ = (t \<squnion> e) * t\<^sup>\<star> * (e * t\<^sup>\<star>)\<^sup>\<star>"
    using star_sup_1 mult_assoc by simp
  also have "... = (t \<squnion> e) * t\<^sup>\<star> * (1 \<squnion> e)"
    using 2 3 by simp
  also have "... = t\<^sup>+ * (1 \<squnion> e) \<squnion> e * t\<^sup>\<star> * (1 \<squnion> e)"
    by (simp add: comp_right_dist_sup)
  also have "... = t\<^sup>+ * (1 \<squnion> e) \<squnion> e * (1 \<squnion> e)"
    using 2 by simp
  also have "... = t\<^sup>+ * (1 \<squnion> e) \<squnion> e"
    using 3 by (metis star_absorb assms(2,3) ee)
  also have "... = t\<^sup>+ \<squnion> t\<^sup>+ * e \<squnion> e"
    by (simp add: mult_left_dist_sup)
  also have "... \<le> -1"
    using 4 by (metis assms(1) sup.absorb1 sup.orderI sup_assoc)
  finally show ?thesis
    .
qed

text \<open>
The following lemma shows that the extended tree is in the component reachable from the root.
\<close>

lemma mst_subgraph_inv_2:
  assumes "regular (v * v\<^sup>T)"
      and "t \<le> v * v\<^sup>T \<sqinter> --g"
      and "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
      and "e \<le> v * -v\<^sup>T \<sqinter> --g"
      and "vector v"
      and "regular ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T)"
    shows "t \<squnion> e \<le> (r\<^sup>T * (--((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g))\<^sup>\<star>)\<^sup>T * (r\<^sup>T * (--((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g))\<^sup>\<star>)"
proof -
  let ?v = "v \<squnion> e\<^sup>T * top"
  let ?G = "?v * ?v\<^sup>T \<sqinter> g"
  let ?c = "r\<^sup>T * (--?G)\<^sup>\<star>"
  have "v\<^sup>T \<le> r\<^sup>T * (--(v * v\<^sup>T \<sqinter> g))\<^sup>\<star>"
    using assms(1-3) inf_pp_commute mult_right_isotone star_isotone by auto
  also have "... \<le> ?c"
    using comp_inf.mult_right_isotone comp_isotone conv_isotone inf.commute mult_right_isotone pp_isotone star_isotone sup.cobounded1 by presburger
  finally have 2: "v\<^sup>T \<le> ?c \<and> v \<le> ?c\<^sup>T"
    by (metis conv_isotone conv_involutive)
  have "t \<le> v * v\<^sup>T"
    using assms(2) by auto
  hence 3: "t \<le> ?c\<^sup>T * ?c"
    using 2 order_trans mult_isotone by blast
  have "e \<le> v * top \<sqinter> --g"
    by (metis assms(4,5) inf.bounded_iff inf.sup_left_divisibility mult_right_isotone top.extremum)
  hence "e \<le> v * top \<sqinter> top * e \<sqinter> --g"
    by (simp add: top_left_mult_increasing inf.boundedI)
  hence "e \<le> v * top * e \<sqinter> --g"
    by (metis comp_inf_covector inf.absorb2 mult_assoc top.extremum)
  hence "t \<squnion> e \<le> (v * v\<^sup>T \<sqinter> --g) \<squnion> (v * top * e \<sqinter> --g)"
    using assms(2) sup_mono by blast
  also have "... = v * ?v\<^sup>T \<sqinter> --g"
    by (simp add: inf_sup_distrib2 mult_assoc mult_left_dist_sup conv_dist_comp conv_dist_sup)
  also have "... \<le> --?G"
    using assms(6) comp_left_increasing_sup inf.sup_left_isotone pp_dist_inf by auto
  finally have 4: "t \<squnion> e \<le> --?G"
    .
  have "e \<le> e * e\<^sup>T * e"
    by (simp add: ex231c)
  also have "... \<le> v * -v\<^sup>T * -v * v\<^sup>T * e"
    by (metis assms(4) mult_left_isotone conv_isotone conv_dist_comp mult_assoc mult_isotone conv_involutive conv_complement inf.boundedE)
  also have "... \<le> v * top * v\<^sup>T * e"
    by (metis mult_assoc mult_left_isotone mult_right_isotone top.extremum)
  also have "... = v * r\<^sup>T * t\<^sup>\<star> * e"
    using assms(3,5) by (simp add: mult_assoc)
  also have "... \<le> v * r\<^sup>T * (t \<squnion> e)\<^sup>\<star>"
    by (simp add: comp_associative mult_right_isotone star.circ_mult_upper_bound star.circ_sub_dist_1 star_isotone sup_commute)
  also have "... \<le> v * ?c"
    using 4 by (simp add: mult_assoc mult_right_isotone star_isotone)
  also have "... \<le> ?c\<^sup>T * ?c"
    using 2 by (simp add: mult_left_isotone)
  finally show ?thesis
    using 3 by simp
qed

lemma span_inv:
  assumes "e \<le> v * -v\<^sup>T"
      and "vector v"
      and "arc e"
      and "t \<le> (v * v\<^sup>T) \<sqinter> g"
      and "g\<^sup>T = g"
      and "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
      and "injective r"
      and "r\<^sup>T \<le> v\<^sup>T"
      and "r\<^sup>T * ((v * v\<^sup>T) \<sqinter> g)\<^sup>\<star> \<le> r\<^sup>T * t\<^sup>\<star>"
    shows "r\<^sup>T * (((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T) \<sqinter> g)\<^sup>\<star> \<le> r\<^sup>T * (t \<squnion> e)\<^sup>\<star>"
proof -
  let ?d = "(v * v\<^sup>T) \<sqinter> g"
  have 1: "(v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T = v * v\<^sup>T \<squnion> v * v\<^sup>T * e \<squnion> e\<^sup>T * v * v\<^sup>T \<squnion> e\<^sup>T * e"
    using assms(1-3) ve_dist by simp
  have "t\<^sup>T \<le> ?d\<^sup>T"
    using assms(4) conv_isotone by simp
  also have "... = (v * v\<^sup>T) \<sqinter> g\<^sup>T"
    by (simp add: conv_dist_comp conv_dist_inf)
  also have "... = ?d"
    by (simp add: assms(5))
  finally have 2: "t\<^sup>T \<le> ?d"
    .
  have "v * v\<^sup>T = (r\<^sup>T * t\<^sup>\<star>)\<^sup>T * (r\<^sup>T * t\<^sup>\<star>)"
    by (metis assms(6) conv_involutive)
  also have "... = t\<^sup>T\<^sup>\<star> * (r * r\<^sup>T) * t\<^sup>\<star>"
    by (simp add: comp_associative conv_dist_comp conv_star_commute)
  also have "... \<le> t\<^sup>T\<^sup>\<star> * 1 * t\<^sup>\<star>"
    by (simp add: assms(7) mult_left_isotone star_right_induct_mult_iff star_sub_one)
  also have "... = t\<^sup>T\<^sup>\<star> * t\<^sup>\<star>"
    by simp
  also have "... \<le> ?d\<^sup>\<star> * t\<^sup>\<star>"
    using 2 by (simp add: comp_left_isotone star.circ_isotone)
  also have "... \<le> ?d\<^sup>\<star> * ?d\<^sup>\<star>"
    using assms(4) mult_right_isotone star_isotone by simp
  also have 3: "... = ?d\<^sup>\<star>"
    by (simp add: star.circ_transitive_equal)
  finally have 4: "v * v\<^sup>T \<le> ?d\<^sup>\<star>"
    .
  have 5: "r\<^sup>T * ?d\<^sup>\<star> * (v * v\<^sup>T \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star>"
    by (simp add: comp_associative mult_right_isotone star.circ_plus_same star.left_plus_below_circ)
  have "r\<^sup>T * ?d\<^sup>\<star> * (v * v\<^sup>T * e \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star> * v * v\<^sup>T * e"
    by (simp add: comp_associative comp_right_isotone)
  also have "... \<le> r\<^sup>T * ?d\<^sup>\<star> * e"
    using 3 4 by (metis comp_associative comp_isotone eq_refl)
  finally have 6: "r\<^sup>T * ?d\<^sup>\<star> * (v * v\<^sup>T * e \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star> * e"
    .
  have 7: "\<forall>x . r\<^sup>T * (1 \<squnion> v * v\<^sup>T) * e\<^sup>T * x = bot"
  proof
    fix x
    have "r\<^sup>T * (1 \<squnion> v * v\<^sup>T) * e\<^sup>T * x \<le> r\<^sup>T * (1 \<squnion> v * v\<^sup>T) * e\<^sup>T * top"
      by (simp add: mult_right_isotone)
    also have "... = r\<^sup>T * e\<^sup>T * top \<squnion> r\<^sup>T * v * v\<^sup>T * e\<^sup>T * top"
      by (simp add: comp_associative mult_left_dist_sup mult_right_dist_sup)
    also have "... = r\<^sup>T * e\<^sup>T * top"
      by (metis assms(1,2) mult_assoc mult_right_dist_sup mult_right_zero sup_bot_right vTeT)
    also have "... \<le> v\<^sup>T * e\<^sup>T * top"
      by (simp add: assms(8) comp_isotone)
    also have "... = bot"
      using vTeT assms(1,2) by simp
    finally show "r\<^sup>T * (1 \<squnion> v * v\<^sup>T) * e\<^sup>T * x = bot"
      by (simp add: le_bot)
  qed
  have "r\<^sup>T * ?d\<^sup>\<star> * (e\<^sup>T * v * v\<^sup>T \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star> * e\<^sup>T * v * v\<^sup>T"
    by (simp add: comp_associative comp_right_isotone)
  also have "... \<le> r\<^sup>T * (1 \<squnion> v * v\<^sup>T) * e\<^sup>T * v * v\<^sup>T"
    by (metis assms(2) star.circ_isotone vector_vector_star inf_le1 comp_associative comp_right_isotone comp_left_isotone)
  also have "... = bot"
    using 7 by simp
  finally have 8: "r\<^sup>T * ?d\<^sup>\<star> * (e\<^sup>T * v * v\<^sup>T \<sqinter> g) = bot"
    by (simp add: le_bot)
  have "r\<^sup>T * ?d\<^sup>\<star> * (e\<^sup>T * e \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star> * e\<^sup>T * e"
    by (simp add: comp_associative comp_right_isotone)
  also have "... \<le> r\<^sup>T * (1 \<squnion> v * v\<^sup>T) * e\<^sup>T * e"
    by (metis assms(2) star.circ_isotone vector_vector_star inf_le1 comp_associative comp_right_isotone comp_left_isotone)
  also have "... = bot"
    using 7 by simp
  finally have 9: "r\<^sup>T * ?d\<^sup>\<star> * (e\<^sup>T * e \<sqinter> g) = bot"
    by (simp add: le_bot)
  have "r\<^sup>T * ?d\<^sup>\<star> * ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g) = r\<^sup>T * ?d\<^sup>\<star> * ((v * v\<^sup>T \<squnion> v * v\<^sup>T * e \<squnion> e\<^sup>T * v * v\<^sup>T \<squnion> e\<^sup>T * e) \<sqinter> g)"
    using 1 by simp
  also have "... = r\<^sup>T * ?d\<^sup>\<star> * ((v * v\<^sup>T \<sqinter> g) \<squnion> (v * v\<^sup>T * e \<sqinter> g) \<squnion> (e\<^sup>T * v * v\<^sup>T \<sqinter> g) \<squnion> (e\<^sup>T * e \<sqinter> g))"
    by (simp add: inf_sup_distrib2)
  also have "... = r\<^sup>T * ?d\<^sup>\<star> * (v * v\<^sup>T \<sqinter> g) \<squnion> r\<^sup>T * ?d\<^sup>\<star> * (v * v\<^sup>T * e \<sqinter> g) \<squnion> r\<^sup>T * ?d\<^sup>\<star> * (e\<^sup>T * v * v\<^sup>T \<sqinter> g) \<squnion> r\<^sup>T * ?d\<^sup>\<star> * (e\<^sup>T * e \<sqinter> g)"
    by (simp add: comp_left_dist_sup)
  also have "... = r\<^sup>T * ?d\<^sup>\<star> * (v * v\<^sup>T \<sqinter> g) \<squnion> r\<^sup>T * ?d\<^sup>\<star> * (v * v\<^sup>T * e \<sqinter> g)"
    using 8 9 by simp
  also have "... \<le> r\<^sup>T * ?d\<^sup>\<star> \<squnion> r\<^sup>T * ?d\<^sup>\<star> * e"
    using 5 6 sup.mono by simp
  also have "... = r\<^sup>T * ?d\<^sup>\<star> * (1 \<squnion> e)"
    by (simp add: mult_left_dist_sup)
  finally have 10: "r\<^sup>T * ?d\<^sup>\<star> * ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star> * (1 \<squnion> e)"
    by simp
  have "r\<^sup>T * ?d\<^sup>\<star> * e * (v * v\<^sup>T \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star> * e * v * v\<^sup>T"
    by (simp add: comp_associative comp_right_isotone)
  also have "... = bot"
    by (metis assms(1,2) comp_associative comp_right_zero ev comp_left_zero)
  finally have 11: "r\<^sup>T * ?d\<^sup>\<star> * e * (v * v\<^sup>T \<sqinter> g) = bot"
    by (simp add: le_bot)
  have "r\<^sup>T * ?d\<^sup>\<star> * e * (v * v\<^sup>T * e \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star> * e * v * v\<^sup>T * e"
    by (simp add: comp_associative comp_right_isotone)
  also have "... = bot"
    by (metis assms(1,2) comp_associative comp_right_zero ev comp_left_zero)
  finally have 12: "r\<^sup>T * ?d\<^sup>\<star> * e * (v * v\<^sup>T * e \<sqinter> g) = bot"
    by (simp add: le_bot)
  have "r\<^sup>T * ?d\<^sup>\<star> * e * (e\<^sup>T * v * v\<^sup>T \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star> * e * e\<^sup>T * v * v\<^sup>T"
    by (simp add: comp_associative comp_right_isotone)
  also have "... \<le> r\<^sup>T * ?d\<^sup>\<star> * 1 * v * v\<^sup>T"
    by (metis assms(3) arc_injective comp_associative comp_left_isotone comp_right_isotone)
  also have "... = r\<^sup>T * ?d\<^sup>\<star> * v * v\<^sup>T"
    by simp
  also have "... \<le> r\<^sup>T * ?d\<^sup>\<star> * ?d\<^sup>\<star>"
    using 4 by (simp add: mult_right_isotone mult_assoc)
  also have "... = r\<^sup>T * ?d\<^sup>\<star>"
    by (simp add: star.circ_transitive_equal comp_associative)
  finally have 13: "r\<^sup>T * ?d\<^sup>\<star> * e * (e\<^sup>T * v * v\<^sup>T \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star>"
    .
  have "r\<^sup>T * ?d\<^sup>\<star> * e * (e\<^sup>T * e \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star> * e * e\<^sup>T * e"
    by (simp add: comp_associative comp_right_isotone)
  also have "... \<le> r\<^sup>T * ?d\<^sup>\<star> * 1 * e"
    by (metis assms(3) arc_injective comp_associative comp_left_isotone comp_right_isotone)
  also have "... = r\<^sup>T * ?d\<^sup>\<star> * e"
    by simp
  finally have 14: "r\<^sup>T * ?d\<^sup>\<star> * e * (e\<^sup>T * e \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star> * e"
    .
  have "r\<^sup>T * ?d\<^sup>\<star> * e * ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g) = r\<^sup>T * ?d\<^sup>\<star> * e * ((v * v\<^sup>T \<squnion> v * v\<^sup>T * e \<squnion> e\<^sup>T * v * v\<^sup>T \<squnion> e\<^sup>T * e) \<sqinter> g)"
    using 1 by simp
  also have "... = r\<^sup>T * ?d\<^sup>\<star> * e * ((v * v\<^sup>T \<sqinter> g) \<squnion> (v * v\<^sup>T * e \<sqinter> g) \<squnion> (e\<^sup>T * v * v\<^sup>T \<sqinter> g) \<squnion> (e\<^sup>T * e \<sqinter> g))"
    by (simp add: inf_sup_distrib2)
  also have "... = r\<^sup>T * ?d\<^sup>\<star> * e * (v * v\<^sup>T \<sqinter> g) \<squnion> r\<^sup>T * ?d\<^sup>\<star> * e * (v * v\<^sup>T * e \<sqinter> g) \<squnion> r\<^sup>T * ?d\<^sup>\<star> * e * (e\<^sup>T * v * v\<^sup>T \<sqinter> g) \<squnion> r\<^sup>T * ?d\<^sup>\<star> * e * (e\<^sup>T * e \<sqinter> g)"
    by (simp add: comp_left_dist_sup)
  also have "... = r\<^sup>T * ?d\<^sup>\<star> * e * (e\<^sup>T * v * v\<^sup>T \<sqinter> g) \<squnion> r\<^sup>T * ?d\<^sup>\<star> * e * (e\<^sup>T * e \<sqinter> g)"
    using 11 12 by simp
  also have "... \<le> r\<^sup>T * ?d\<^sup>\<star> \<squnion> r\<^sup>T * ?d\<^sup>\<star> * e"
    using 13 14 sup_mono by simp
  also have "... = r\<^sup>T * ?d\<^sup>\<star> * (1 \<squnion> e)"
    by (simp add: mult_left_dist_sup)
  finally have 15: "r\<^sup>T * ?d\<^sup>\<star> * e * ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star> * (1 \<squnion> e)"
    by simp
  have "r\<^sup>T \<le> r\<^sup>T * ?d\<^sup>\<star>"
    using mult_right_isotone star.circ_reflexive by fastforce
  also have "... \<le> r\<^sup>T * ?d\<^sup>\<star> * (1 \<squnion> e)"
    by (simp add: semiring.distrib_left)
  finally have 16: "r\<^sup>T \<le> r\<^sup>T * ?d\<^sup>\<star> * (1 \<squnion> e)"
    .
  have "r\<^sup>T * ?d\<^sup>\<star> * (1 \<squnion> e) * ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g) = r\<^sup>T * ?d\<^sup>\<star> * ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g) \<squnion> r\<^sup>T * ?d\<^sup>\<star> * e * ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g)"
    by (simp add: semiring.distrib_left semiring.distrib_right)
  also have "... \<le> r\<^sup>T * ?d\<^sup>\<star> * (1 \<squnion> e)"
    using 10 15 le_supI by simp
  finally have "r\<^sup>T * ?d\<^sup>\<star> * (1 \<squnion> e) * ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star> * (1 \<squnion> e)"
    .
  hence "r\<^sup>T \<squnion> r\<^sup>T * ?d\<^sup>\<star> * (1 \<squnion> e) * ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g) \<le> r\<^sup>T * ?d\<^sup>\<star> * (1 \<squnion> e)"
    using 16 sup_least by simp
  hence "r\<^sup>T * ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g)\<^sup>\<star> \<le> r\<^sup>T * ?d\<^sup>\<star> * (1 \<squnion> e)"
    by (simp add: star_right_induct)
  also have "... \<le> r\<^sup>T * t\<^sup>\<star> * (1 \<squnion> e)"
    by (simp add: assms(9) mult_left_isotone)
  also have "... \<le> r\<^sup>T * (t \<squnion> e)\<^sup>\<star>"
    by (simp add: star_one_sup_below)
  finally show ?thesis
    .
qed

subsubsection \<open>Exchange gives Spanning Trees\<close>

text \<open>
The following abbreviations are used in the spanning tree application using Prim's algorithm to construct the new tree for the exchange property.
It is obtained by replacing an edge with one that has minimal weight and reversing the path connecting these edges.
Here, w represents a weighted graph, v represents a set of nodes and e represents an edge.
\<close>

abbreviation prim_E :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where "prim_E w v e \<equiv> w \<sqinter> --v * -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>\<star>"
abbreviation prim_P :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where "prim_P w v e \<equiv> w \<sqinter> -v * -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>\<star>"
abbreviation prim_EP :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where "prim_EP w v e \<equiv> w \<sqinter> -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>\<star>"
abbreviation prim_W :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where "prim_W w v e \<equiv> (w \<sqinter> -(prim_EP w v e)) \<squnion> (prim_P w v e)\<^sup>T \<squnion> e"

text \<open>
The lemmas in this section are used to show that the relation after exchange represents a spanning tree.
The results in the next section are used to show that it is a minimum spanning tree.
\<close>

lemma exchange_injective_3:
  assumes "e \<le> v * -v\<^sup>T"
      and "vector v"
    shows "(w \<sqinter> -(prim_EP w v e)) * e\<^sup>T = bot"
proof -
  have 1: "top * e \<le> -v\<^sup>T"
    by (simp add: assms schroeder_4_p vTeT)
  have "top * e \<le> top * e * w\<^sup>T\<^sup>\<star>"
    using sup_right_divisibility star.circ_back_loop_fixpoint by blast
  hence "top * e \<le> -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>\<star>"
    using 1 by simp
  hence "top * e \<le> -(w \<sqinter> -prim_EP w v e)"
    by (metis inf.assoc inf_import_p le_infI2 p_antitone p_antitone_iff)
  hence "(w \<sqinter> -(prim_EP w v e)) * e\<^sup>T \<le> bot"
    using p_top schroeder_4_p by blast
  thus ?thesis
    using le_bot by simp
qed

lemma exchange_injective_6:
  assumes "arc e"
      and "forest w"
    shows "(prim_P w v e)\<^sup>T * e\<^sup>T = bot"
proof -
  have "e\<^sup>T * top * e \<le> --1"
    by (simp add: assms(1) local.p_antitone local.p_antitone_iff local.point_injective)
  hence 1: "e * -1 * e\<^sup>T \<le> bot"
    by (metis conv_involutive p_top triple_schroeder_p)
  have "(prim_P w v e)\<^sup>T * e\<^sup>T \<le> (w \<sqinter> top * e * w\<^sup>T\<^sup>\<star>)\<^sup>T * e\<^sup>T"
    using comp_inf.mult_left_isotone conv_dist_inf mult_left_isotone by simp
  also have "... = (w\<^sup>T \<sqinter> w\<^sup>T\<^sup>\<star>\<^sup>T * e\<^sup>T * top) * e\<^sup>T"
    by (simp add: comp_associative conv_dist_comp conv_dist_inf)
  also have "... = w\<^sup>\<star> * e\<^sup>T * top \<sqinter> w\<^sup>T * e\<^sup>T"
    by (simp add: conv_star_commute inf_vector_comp)
  also have "... \<le> (w\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top * e) * (e\<^sup>T \<sqinter> w\<^sup>+ * e\<^sup>T * top)"
    by (metis dedekind mult_assoc conv_involutive inf_commute)
  also have "... \<le> (w\<^sup>\<star> * e\<^sup>T * top * e) * (w\<^sup>+ * e\<^sup>T * top)"
    by (simp add: mult_isotone)
  also have "... \<le> (top * e) * (w\<^sup>+ * e\<^sup>T * top)"
    by (simp add: mult_left_isotone)
  also have "... = top * e * w\<^sup>+ * e\<^sup>T * top"
    using mult_assoc by simp
  also have "... \<le> top * e * -1 * e\<^sup>T * top"
    using assms(2) mult_left_isotone mult_right_isotone by simp
  also have "... \<le> bot"
    using 1 by (metis le_bot semiring.mult_not_zero mult_assoc)
  finally show ?thesis
    using le_bot by simp
qed

text \<open>
The graph after exchanging is injective.
\<close>

lemma exchange_injective:
  assumes "arc e"
      and "e \<le> v * -v\<^sup>T"
      and "forest w"
      and "vector v"
    shows "injective (prim_W w v e)"
proof -
  have 1: "(w \<sqinter> -(prim_EP w v e)) * (w \<sqinter> -(prim_EP w v e))\<^sup>T \<le> 1"
  proof -
    have "(w \<sqinter> -(prim_EP w v e)) * (w \<sqinter> -(prim_EP w v e))\<^sup>T \<le> w * w\<^sup>T"
      by (simp add: comp_isotone conv_isotone)
    also have "... \<le> 1"
      by (simp add: assms(3))
    finally show ?thesis
      .
  qed
  have 2: "(w \<sqinter> -(prim_EP w v e)) * (prim_P w v e)\<^sup>T\<^sup>T \<le> 1"
  proof -
    have "top * (prim_P w v e)\<^sup>T = top * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>T\<^sup>\<star>\<^sup>T * e\<^sup>T * top)"
      by (simp add: comp_associative conv_complement conv_dist_comp conv_dist_inf)
    also have "... = top * e * w\<^sup>T\<^sup>\<star> * (w\<^sup>T \<sqinter> -v * -v\<^sup>T)"
      by (metis comp_inf_vector conv_dist_comp conv_involutive inf_top_left mult_assoc)
    also have "... \<le> top * e * w\<^sup>T\<^sup>\<star> * (w\<^sup>T \<sqinter> top * -v\<^sup>T)"
      using comp_inf.mult_right_isotone mult_left_isotone mult_right_isotone by simp
    also have "... = top * e * w\<^sup>T\<^sup>\<star> * w\<^sup>T \<sqinter> -v\<^sup>T"
      by (metis assms(4) comp_inf_covector vector_conv_compl)
    also have "... \<le> -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>\<star>"
      by (simp add: comp_associative comp_isotone inf.coboundedI1 star.circ_plus_same star.left_plus_below_circ)
    finally have "top * (prim_P w v e)\<^sup>T \<le> -(w \<sqinter> -prim_EP w v e)"
      by (metis inf.assoc inf_import_p le_infI2 p_antitone p_antitone_iff)
    hence "(w \<sqinter> -(prim_EP w v e)) * (prim_P w v e)\<^sup>T\<^sup>T \<le> bot"
      using p_top schroeder_4_p by blast
    thus ?thesis
      by (simp add: bot_unique)
  qed
  have 3: "(w \<sqinter> -(prim_EP w v e)) * e\<^sup>T \<le> 1"
    by (metis assms(2,4) exchange_injective_3 bot_least)
  have 4: "(prim_P w v e)\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>T \<le> 1"
    using 2 conv_dist_comp coreflexive_symmetric by fastforce
  have 5: "(prim_P w v e)\<^sup>T * (prim_P w v e)\<^sup>T\<^sup>T \<le> 1"
  proof -
    have "(prim_P w v e)\<^sup>T * (prim_P w v e)\<^sup>T\<^sup>T \<le> (top * e * w\<^sup>T\<^sup>\<star>)\<^sup>T * (top * e * w\<^sup>T\<^sup>\<star>)"
      by (simp add: conv_dist_inf mult_isotone)
    also have "... = w\<^sup>\<star> * e\<^sup>T * top * top * e * w\<^sup>T\<^sup>\<star>"
      using conv_star_commute conv_dist_comp conv_involutive conv_top mult_assoc by presburger
    also have "... = w\<^sup>\<star> * e\<^sup>T * top * e * w\<^sup>T\<^sup>\<star>"
      by (simp add: comp_associative)
    also have "... \<le> w\<^sup>\<star> * 1 * w\<^sup>T\<^sup>\<star>"
      by (metis comp_left_isotone comp_right_isotone mult_assoc assms(1) point_injective)
    finally have "(prim_P w v e)\<^sup>T * (prim_P w v e)\<^sup>T\<^sup>T \<le> w\<^sup>\<star> * w\<^sup>T\<^sup>\<star> \<sqinter> w\<^sup>T * w"
      by (simp add: conv_isotone inf.left_commute inf.sup_monoid.add_commute mult_isotone)
    also have "... \<le> 1"
      by (simp add: assms(3) forest_separate)
    finally show ?thesis
      .
  qed
  have 6: "(prim_P w v e)\<^sup>T * e\<^sup>T \<le> 1"
    using assms exchange_injective_6 bot_least by simp
  have 7: "e * (w \<sqinter> -(prim_EP w v e))\<^sup>T \<le> 1"
    using 3 by (metis conv_dist_comp conv_involutive coreflexive_symmetric)
  have 8: "e * (prim_P w v e)\<^sup>T\<^sup>T \<le> 1"
    using 6 conv_dist_comp coreflexive_symmetric by fastforce
  have 9: "e * e\<^sup>T \<le> 1"
    by (simp add: assms(1) arc_injective)
  have "(prim_W w v e) * (prim_W w v e)\<^sup>T = (w \<sqinter> -(prim_EP w v e)) * (w \<sqinter> -(prim_EP w v e))\<^sup>T \<squnion> (w \<sqinter> -(prim_EP w v e)) * (prim_P w v e)\<^sup>T\<^sup>T \<squnion> (w \<sqinter> -(prim_EP w v e)) * e\<^sup>T \<squnion> (prim_P w v e)\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>T \<squnion> (prim_P w v e)\<^sup>T * (prim_P w v e)\<^sup>T\<^sup>T \<squnion> (prim_P w v e)\<^sup>T * e\<^sup>T  \<squnion> e * (w \<sqinter> -(prim_EP w v e))\<^sup>T \<squnion> e * (prim_P w v e)\<^sup>T\<^sup>T \<squnion> e * e\<^sup>T"
    using comp_left_dist_sup comp_right_dist_sup conv_dist_sup sup.assoc by simp
  also have "... \<le> 1"
    using 1 2 3 4 5 6 7 8 9 by simp
  finally show ?thesis
    .
qed

lemma pv:
  assumes "vector v"
    shows "(prim_P w v e)\<^sup>T * v = bot"
proof -
  have "(prim_P w v e)\<^sup>T * v \<le> (-v * -v\<^sup>T)\<^sup>T * v"
    by (meson conv_isotone inf_le1 inf_le2 mult_left_isotone order_trans)
  also have "... = -v * -v\<^sup>T * v"
    by (simp add: conv_complement conv_dist_comp)
  also have "... = bot"
    by (simp add: assms covector_vector_comp mult_assoc)
  finally show ?thesis
    by (simp add: antisym)
qed

lemma vector_pred_inv:
  assumes "arc e"
      and "e \<le> v * -v\<^sup>T"
      and "forest w"
      and "vector v"
      and "w * v \<le> v"
    shows "(prim_W w v e) * (v \<squnion> e\<^sup>T * top) \<le> v \<squnion> e\<^sup>T * top"
proof -
  have "(prim_W w v e) * e\<^sup>T * top = (w \<sqinter> -(prim_EP w v e)) * e\<^sup>T * top \<squnion> (prim_P w v e)\<^sup>T * e\<^sup>T * top \<squnion> e * e\<^sup>T * top"
    by (simp add: mult_right_dist_sup)
  also have "... = e * e\<^sup>T * top"
   using assms exchange_injective_3 exchange_injective_6 comp_left_zero by simp
  also have "... \<le> v * -v\<^sup>T * e\<^sup>T * top"
    by (simp add: assms(2) comp_isotone)
  also have "... \<le> v * top"
    by (simp add: comp_associative mult_right_isotone)
  also have "... = v"
    by (simp add: assms(4))
  finally have 1: "(prim_W w v e) * e\<^sup>T * top \<le> v"
    .
  have "(prim_W w v e) * v = (w \<sqinter> -(prim_EP w v e)) * v \<squnion> (prim_P w v e)\<^sup>T * v \<squnion> e * v"
    by (simp add: mult_right_dist_sup)
  also have "... = (w \<sqinter> -(prim_EP w v e)) * v"
    by (metis assms(2,4) pv ev sup_bot_right)
  also have "... \<le> w * v"
    by (simp add: mult_left_isotone)
  finally have 2: "(prim_W w v e) * v \<le> v"
    using assms(5) order_trans by blast
  have "(prim_W w v e) * (v \<squnion> e\<^sup>T * top) = (prim_W w v e) * v \<squnion> (prim_W w v e) * e\<^sup>T * top"
    by (simp add: semiring.distrib_left mult_assoc)
  also have "... \<le> v"
    using 1 2 by simp
  also have "... \<le> v \<squnion> e\<^sup>T * top"
    by simp
  finally show ?thesis
    .
qed

text \<open>
The graph after exchanging is acyclic.
\<close>

lemma exchange_acyclic:
  assumes "vector v"
      and "e \<le> v * -v\<^sup>T"
      and "w * v \<le> v"
      and "acyclic w"
    shows "acyclic (prim_W w v e)"
proof -
  have 1: "(prim_P w v e)\<^sup>T * e = bot"
  proof -
    have "(prim_P w v e)\<^sup>T * e \<le> (-v * -v\<^sup>T)\<^sup>T * e"
      by (meson conv_order dual_order.trans inf.cobounded1 inf.cobounded2 mult_left_isotone)
    also have "... = -v * -v\<^sup>T * e"
      by (simp add: conv_complement conv_dist_comp)
    also have "... \<le> -v * -v\<^sup>T * v * -v\<^sup>T"
      by (simp add: assms(2) comp_associative mult_right_isotone)
    also have "... = bot"
      by (simp add: assms(1) covector_vector_comp mult_assoc)
    finally show ?thesis
      by (simp add: bot_unique)
  qed
  have 2: "e * e = bot"
    using assms(1,2) ee by auto
  have 3: "(w \<sqinter> -(prim_EP w v e)) * (prim_P w v e)\<^sup>T = bot"
  proof -
    have "top * (prim_P w v e) \<le> top * (-v * -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>\<star>)"
      using comp_inf.mult_semi_associative mult_right_isotone by auto
    also have "... \<le> top * -v * -v\<^sup>T \<sqinter> top * top * e * w\<^sup>T\<^sup>\<star>"
      by (simp add: comp_inf_covector mult_assoc)
    also have "... \<le> top * -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>\<star>"
      using mult_left_isotone top.extremum local.inf_mono by presburger
    also have "... = -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>\<star>"
      by (simp add: assms(1) vector_conv_compl)
    finally have "top * (prim_P w v e) \<le> -(w \<sqinter> -prim_EP w v e)"
      by (metis inf.assoc inf_import_p le_infI2 p_antitone p_antitone_iff)
    hence "(w \<sqinter> -(prim_EP w v e)) * (prim_P w v e)\<^sup>T \<le> bot"
      using p_top schroeder_4_p by blast
    thus ?thesis
      using bot_unique by blast
  qed
  hence 4: "(w \<sqinter> -(prim_EP w v e)) * (prim_P w v e)\<^sup>T\<^sup>\<star> = w \<sqinter> -(prim_EP w v e)"
    using star_absorb by blast
  hence 5: "(w \<sqinter> -(prim_EP w v e))\<^sup>+ * (prim_P w v e)\<^sup>T\<^sup>\<star> = (w \<sqinter> -(prim_EP w v e))\<^sup>+"
    by (metis star_plus mult_assoc)
  hence 6: "(w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * (prim_P w v e)\<^sup>T\<^sup>\<star> = (w \<sqinter> -(prim_EP w v e))\<^sup>+ \<squnion> (prim_P w v e)\<^sup>T\<^sup>\<star>"
    by (metis star.circ_loop_fixpoint mult_assoc)
  have 7: "(w \<sqinter> -(prim_EP w v e))\<^sup>+ * e \<le> v * top"
  proof -
    have "e \<le> v * top"
      using assms(2) dual_order.trans mult_right_isotone top_greatest by blast
    hence 8: "e \<squnion> w * v * top \<le> v * top"
      by (simp add: assms(1,3) comp_associative)
    have "(w \<sqinter> -(prim_EP w v e))\<^sup>+ * e \<le> w\<^sup>+ * e"
      by (simp add: comp_isotone star_isotone)
    also have "... \<le> w\<^sup>\<star> * e"
      by (simp add: mult_left_isotone star.left_plus_below_circ)
    also have "... \<le> v * top"
      using 8 by (simp add: comp_associative star_left_induct)
    finally show ?thesis
      .
  qed
  have 9: "(prim_P w v e)\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>+ * e = bot"
  proof -
    have "(prim_P w v e)\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>+ * e \<le> (prim_P w v e)\<^sup>T * v * top"
      using 7 by (simp add: mult_assoc mult_right_isotone)
    also have "... = bot"
      by (simp add: assms(1) pv)
    finally show ?thesis
      using bot_unique by blast
  qed
  have 10: "e * (w \<sqinter> -(prim_EP w v e))\<^sup>+ * e = bot"
  proof -
    have "e * (w \<sqinter> -(prim_EP w v e))\<^sup>+ * e \<le> e * v * top"
      using 7 by (simp add: mult_assoc mult_right_isotone)
    also have "... \<le> v * -v\<^sup>T * v * top"
      by (simp add: assms(2) mult_left_isotone)
    also have "... = bot"
      by (simp add: assms(1) covector_vector_comp mult_assoc)
    finally show ?thesis
      using bot_unique by blast
  qed
  have 11: "e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<le> v * -v\<^sup>T"
  proof -
    have 12: "-v\<^sup>T * w \<le> -v\<^sup>T"
      by (metis assms(3) conv_complement order_lesseq_imp pp_increasing schroeder_6_p)
    have "v * -v\<^sup>T * (w \<sqinter> -(prim_EP w v e)) \<le> v * -v\<^sup>T * w"
      by (simp add: comp_isotone star_isotone)
    also have "... \<le> v * -v\<^sup>T"
      using 12 by (simp add: comp_isotone comp_associative)
    finally have 13: "v * -v\<^sup>T * (w \<sqinter> -(prim_EP w v e)) \<le> v * -v\<^sup>T"
      .
    have 14: "(prim_P w v e)\<^sup>T \<le> -v * -v\<^sup>T"
      by (metis conv_complement conv_dist_comp conv_involutive conv_order inf_le1 inf_le2 order_trans)
    have "e * (prim_P w v e)\<^sup>T\<^sup>\<star> \<le> v * -v\<^sup>T * (prim_P w v e)\<^sup>T\<^sup>\<star>"
      by (simp add: assms(2) mult_left_isotone)
    also have "... = v * -v\<^sup>T \<squnion> v * -v\<^sup>T * (prim_P w v e)\<^sup>T\<^sup>+"
      by (metis mult_assoc star.circ_back_loop_fixpoint star_plus sup_commute)
    also have "... = v * -v\<^sup>T \<squnion> v * -v\<^sup>T * (prim_P w v e)\<^sup>T\<^sup>\<star> * (prim_P w v e)\<^sup>T"
      by (simp add: mult_assoc star_plus)
    also have "... \<le> v * -v\<^sup>T \<squnion> v * -v\<^sup>T * (prim_P w v e)\<^sup>T\<^sup>\<star> * -v * -v\<^sup>T"
      using 14 mult_assoc mult_right_isotone sup_right_isotone by simp
    also have "... \<le> v * -v\<^sup>T \<squnion> v * top * -v\<^sup>T"
      by (metis top_greatest mult_right_isotone mult_left_isotone mult_assoc sup_right_isotone)
    also have "... = v * -v\<^sup>T"
      by (simp add: assms(1))
    finally have "e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<le> v * -v\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>"
      by (simp add: mult_left_isotone)
    also have "... \<le> v * -v\<^sup>T"
      using 13 by (simp add: star_right_induct_mult)
    finally show ?thesis
      .
  qed
  have 15: "(w \<sqinter> -(prim_EP w v e))\<^sup>+ * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<le> -1"
  proof -
    have "(w \<sqinter> -(prim_EP w v e))\<^sup>+ * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> = (w \<sqinter> -(prim_EP w v e))\<^sup>+ * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>"
      using 5 by simp
    also have "... = (w \<sqinter> -(prim_EP w v e))\<^sup>+"
      by (simp add: mult_assoc star.circ_transitive_equal)
    also have "... \<le> w\<^sup>+"
      by (simp add: comp_isotone star_isotone)
    finally show ?thesis
      using assms(4) by simp
  qed
  have 16: "(prim_P w v e)\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<le> -1"
  proof -
    have "(w \<sqinter> -(prim_EP w v e))\<^sup>+ * (prim_P w v e)\<^sup>T\<^sup>+ \<le> (w \<sqinter> -(prim_EP w v e))\<^sup>+ * (prim_P w v e)\<^sup>T\<^sup>\<star>"
      by (simp add: mult_right_isotone star.left_plus_below_circ)
    also have "... = (w \<sqinter> -(prim_EP w v e))\<^sup>+"
      using 5 by simp
    also have "... \<le> w\<^sup>+"
      by (simp add: comp_isotone star_isotone)
    finally have "(w \<sqinter> -(prim_EP w v e))\<^sup>+ * (prim_P w v e)\<^sup>T\<^sup>+ \<le> -1"
      using assms(4) by simp
    hence 17: "(prim_P w v e)\<^sup>T\<^sup>+ * (w \<sqinter> -(prim_EP w v e))\<^sup>+ \<le> -1"
      by (simp add: comp_commute_below_diversity)
    have "(prim_P w v e)\<^sup>T\<^sup>+ \<le> w\<^sup>T\<^sup>+"
      by (simp add: comp_isotone conv_dist_inf inf.left_commute inf.sup_monoid.add_commute star_isotone)
    also have "... = w\<^sup>+\<^sup>T"
      by (simp add: conv_dist_comp conv_star_commute star_plus)
    also have "... \<le> -1"
      using assms(4) conv_complement conv_isotone by force
    finally have 18: "(prim_P w v e)\<^sup>T\<^sup>+ \<le> -1"
      .
    have "(prim_P w v e)\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> = (prim_P w v e)\<^sup>T * ((w \<sqinter> -(prim_EP w v e))\<^sup>+ \<squnion> (prim_P w v e)\<^sup>T\<^sup>\<star>) * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>"
      using 6 by (simp add: comp_associative)
    also have "... = (prim_P w v e)\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>+ * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<squnion> (prim_P w v e)\<^sup>T\<^sup>+ * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>"
      by (simp add: mult_left_dist_sup mult_right_dist_sup)
    also have "... = (prim_P w v e)\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>+ \<squnion> (prim_P w v e)\<^sup>T\<^sup>+ * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>"
      by (simp add: mult_assoc star.circ_transitive_equal)
    also have "... = (prim_P w v e)\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>+ \<squnion> (prim_P w v e)\<^sup>T\<^sup>+ * (1 \<squnion> (w \<sqinter> -(prim_EP w v e))\<^sup>+)"
      using star_left_unfold_equal by simp
    also have "... = (prim_P w v e)\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>+ \<squnion> (prim_P w v e)\<^sup>T\<^sup>+ * (w \<sqinter> -(prim_EP w v e))\<^sup>+ \<squnion> (prim_P w v e)\<^sup>T\<^sup>+"
      by (simp add: mult_left_dist_sup sup.left_commute sup_commute)
    also have "... = ((prim_P w v e)\<^sup>T \<squnion> (prim_P w v e)\<^sup>T\<^sup>+) * (w \<sqinter> -(prim_EP w v e))\<^sup>+ \<squnion> (prim_P w v e)\<^sup>T\<^sup>+"
      by (simp add: mult_right_dist_sup)
    also have "... = (prim_P w v e)\<^sup>T\<^sup>+ * (w \<sqinter> -(prim_EP w v e))\<^sup>+ \<squnion> (prim_P w v e)\<^sup>T\<^sup>+"
      using star.circ_mult_increasing by (simp add: le_iff_sup)
    also have "... \<le> -1"
      using 17 18 by simp
    finally show ?thesis
      .
  qed
  have 19: "e * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<le> -1"
  proof -
    have "e * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> = e * ((w \<sqinter> -(prim_EP w v e))\<^sup>+ \<squnion> (prim_P w v e)\<^sup>T\<^sup>\<star>) * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>"
      using 6 by (simp add: mult_assoc)
    also have "... = e * (w \<sqinter> -(prim_EP w v e))\<^sup>+ * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<squnion> e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>"
      by (simp add: mult_left_dist_sup mult_right_dist_sup)
    also have "... = e * (w \<sqinter> -(prim_EP w v e))\<^sup>+ \<squnion> e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>"
      by (simp add: mult_assoc star.circ_transitive_equal)
    also have "... \<le> e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>+ \<squnion> e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>"
      by (metis mult_right_sub_dist_sup_right semiring.add_right_mono star.circ_back_loop_fixpoint)
    also have "... \<le> e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>"
      using mult_right_isotone star.left_plus_below_circ by auto
    also have "... \<le> v * -v\<^sup>T"
      using 11 by simp
    also have "... \<le> -1"
      by (simp add: pp_increasing schroeder_3_p)
    finally show ?thesis
      .
  qed
  have 20: "(prim_W w v e) * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<le> -1"
    using 15 16 19 by (simp add: comp_right_dist_sup)
  have 21: "(w \<sqinter> -(prim_EP w v e))\<^sup>+ * e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<le> -1"
  proof -
    have "(w \<sqinter> -(prim_EP w v e)) * v * -v\<^sup>T \<le> w * v * -v\<^sup>T"
      by (simp add: comp_isotone star_isotone)
    also have "... \<le> v * -v\<^sup>T"
      by (simp add: assms(3) mult_left_isotone)
    finally have 22: "(w \<sqinter> -(prim_EP w v e)) * v * -v\<^sup>T \<le> v * -v\<^sup>T"
      .
    have "(w \<sqinter> -(prim_EP w v e))\<^sup>+ * e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<le> (w \<sqinter> -(prim_EP w v e))\<^sup>+ * v * -v\<^sup>T"
      using 11 by (simp add: mult_right_isotone mult_assoc)
    also have "... \<le> (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * v * -v\<^sup>T"
      using mult_left_isotone star.left_plus_below_circ by blast
    also have "... \<le> v * -v\<^sup>T"
      using 22 by (simp add: star_left_induct_mult mult_assoc)
    also have "... \<le> -1"
      by (simp add: pp_increasing schroeder_3_p)
    finally show ?thesis
      .
  qed
  have 23: "(prim_P w v e)\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<le> -1"
  proof -
    have "(prim_P w v e)\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * e = (prim_P w v e)\<^sup>T * e \<squnion> (prim_P w v e)\<^sup>T * (w \<sqinter> -(prim_EP w v e))\<^sup>+ * e"
      using comp_left_dist_sup mult_assoc star.circ_loop_fixpoint sup_commute by auto
    also have "... = bot"
      using 1 9 by simp
    finally show ?thesis
      by simp
  qed
  have 24: "e * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<le> -1"
  proof -
    have "e * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * e = e * e \<squnion> e * (w \<sqinter> -(prim_EP w v e))\<^sup>+ * e"
      using comp_left_dist_sup mult_assoc star.circ_loop_fixpoint sup_commute by auto
    also have "... = bot"
      using 2 10 by simp
    finally show ?thesis
      by simp
  qed
  have 25: "(prim_W w v e) * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<le> -1"
    using 21 23 24 by (simp add: comp_right_dist_sup)
  have "(prim_W w v e)\<^sup>\<star> = ((prim_P w v e)\<^sup>T \<squnion> e)\<^sup>\<star> * ((w \<sqinter> -(prim_EP w v e)) * ((prim_P w v e)\<^sup>T \<squnion> e)\<^sup>\<star>)\<^sup>\<star>"
    by (metis star_sup_1 sup.left_commute sup_commute)
  also have "... = ((prim_P w v e)\<^sup>T\<^sup>\<star> \<squnion> e * (prim_P w v e)\<^sup>T\<^sup>\<star>) * ((w \<sqinter> -(prim_EP w v e)) * ((prim_P w v e)\<^sup>T\<^sup>\<star> \<squnion> e * (prim_P w v e)\<^sup>T\<^sup>\<star>))\<^sup>\<star>"
    using 1 2 star_separate by auto
  also have "... = ((prim_P w v e)\<^sup>T\<^sup>\<star> \<squnion> e * (prim_P w v e)\<^sup>T\<^sup>\<star>) * ((w \<sqinter> -(prim_EP w v e)) * (1 \<squnion> e * (prim_P w v e)\<^sup>T\<^sup>\<star>))\<^sup>\<star>"
    using 4 mult_left_dist_sup by auto
  also have "... = (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * ((prim_P w v e)\<^sup>T\<^sup>\<star> \<squnion> e * (prim_P w v e)\<^sup>T\<^sup>\<star>) * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>"
    using 3 9 10 star_separate_2 by blast
  also have "... = (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<squnion> (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>"
    by (simp add: semiring.distrib_left semiring.distrib_right mult_assoc)
  finally have "(prim_W w v e)\<^sup>+ = (prim_W w v e) * ((w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<squnion> (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>)"
    by simp
  also have "... = (prim_W w v e) * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> \<squnion> (prim_W w v e) * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star> * e * (prim_P w v e)\<^sup>T\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e))\<^sup>\<star>"
    by (simp add: comp_left_dist_sup comp_associative)
  also have "... \<le> -1"
    using 20 25 by simp
  finally show ?thesis
    .
qed

text \<open>
The following lemma shows that an edge across the cut between visited nodes and unvisited nodes does not leave the component of visited nodes.
\<close>

lemma mst_subgraph_inv:
  assumes "e \<le> v * -v\<^sup>T \<sqinter> g"
      and "t \<le> g"
      and "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
    shows "e \<le> (r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g"
proof -
  have "e \<le> v * -v\<^sup>T \<sqinter> g"
    by (rule assms(1))
  also have "... \<le> v * (-v\<^sup>T \<sqinter> v\<^sup>T * g) \<sqinter> g"
    by (simp add: dedekind_1)
  also have "... \<le> v * v\<^sup>T * g \<sqinter> g"
    by (simp add: comp_associative comp_right_isotone inf_commute le_infI2)
  also have "... = v * (r\<^sup>T * t\<^sup>\<star>) * g \<sqinter> g"
    by (simp add: assms(3))
  also have "... = (r\<^sup>T * t\<^sup>\<star>)\<^sup>T * (r\<^sup>T * t\<^sup>\<star>) * g \<sqinter> g"
    by (metis assms(3) conv_involutive)
  also have "... \<le> (r\<^sup>T * t\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) * g \<sqinter> g"
    using assms(2) comp_inf.mult_left_isotone comp_isotone star_isotone by auto
  also have "... \<le> (r\<^sup>T * t\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g"
    using inf.sup_right_isotone inf_commute mult_assoc mult_right_isotone star.left_plus_below_circ star_plus by presburger
  also have "... \<le> (r\<^sup>T * g\<^sup>\<star>)\<^sup>T * (r\<^sup>T * g\<^sup>\<star>) \<sqinter> g"
    using assms(2) comp_inf.mult_left_isotone conv_dist_comp conv_isotone mult_left_isotone star_isotone by auto
  finally show ?thesis
    .
qed

text \<open>
The following lemmas show that the tree after exchanging contains the currently constructed and tree and its extension by the chosen edge.
\<close>

lemma mst_extends_old_tree:
  assumes "t \<le> w"
      and "t \<le> v * v\<^sup>T"
      and "vector v"
    shows "t \<le> prim_W w v e"
proof -
  have "t \<sqinter> prim_EP w v e \<le> t \<sqinter> -v\<^sup>T"
    by (simp add: inf.coboundedI2 inf.sup_monoid.add_assoc)
  also have "... \<le> v * v\<^sup>T \<sqinter> -v\<^sup>T"
    by (simp add: assms(2) inf.coboundedI1)
  also have "... \<le> bot"
    by (simp add: assms(3) covector_vector_comp eq_refl schroeder_2)
  finally have "t \<le> -(prim_EP w v e)"
    using le_bot pseudo_complement by blast
  hence "t \<le> w \<sqinter> -(prim_EP w v e)"
    using assms(1) by simp
  thus ?thesis
    using local.le_supI1 by blast
qed

lemma mst_extends_new_tree:
  "t \<le> w \<Longrightarrow> t \<le> v * v\<^sup>T \<Longrightarrow> vector v \<Longrightarrow> t \<squnion> e \<le> prim_W w v e"
  using mst_extends_old_tree by auto

end

text \<open>
We finally add the Kleene star to Stone relation algebras.
Kleene star and the relational operations are reasonably independent.
The only additional axiom we need in the generalisation to Stone-Kleene relation algebras is that star distributes over double complement.
\<close>

class stone_kleene_relation_algebra = stone_relation_algebra + pd_kleene_allegory +
  assumes pp_dist_star: "--(x\<^sup>\<star>) = (--x)\<^sup>\<star>"
begin

lemma regular_closed_star:
  "regular x \<Longrightarrow> regular (x\<^sup>\<star>)"
  by (simp add: pp_dist_star)

lemma components_idempotent:
  "components (components x) = components x"
  using pp_dist_star star_involutive by auto

text \<open>
The following lemma shows that the nodes reachable in the tree after exchange contain the nodes reachable in the tree before exchange.
\<close>

lemma mst_reachable_inv:
  assumes "regular (prim_EP w v e)"
      and "vector r"
      and "e \<le> v * -v\<^sup>T"
      and "vector v"
      and "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
      and "t \<le> w"
      and "t \<le> v * v\<^sup>T"
      and "w * v \<le> v"
    shows "r\<^sup>T * w\<^sup>\<star> \<le> r\<^sup>T * (prim_W w v e)\<^sup>\<star>"
proof -
  have 1: "r\<^sup>T \<le> r\<^sup>T * (prim_W w v e)\<^sup>\<star>"
    using sup.bounded_iff star.circ_back_loop_prefixpoint by blast
  have "top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star> * w\<^sup>T \<sqinter> -v\<^sup>T = top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star> * (w\<^sup>T \<sqinter> -v\<^sup>T)"
    by (simp add: assms(4) covector_comp_inf vector_conv_compl)
  also have "... \<le> top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star>"
    by (simp add: comp_isotone mult_assoc star.circ_plus_same star.left_plus_below_circ)
  finally have 2: "top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star> * w\<^sup>T \<le> top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star> \<squnion> --v\<^sup>T"
    by (simp add: shunting_var_p)
  have 3: "--v\<^sup>T * w\<^sup>T \<le> top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star> \<squnion> --v\<^sup>T"
    by (metis assms(8) conv_dist_comp conv_order mult_assoc order.trans pp_comp_semi_commute pp_isotone sup.coboundedI1 sup_commute)
  have 4: "top * e \<le> top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star> \<squnion> --v\<^sup>T"
    using sup_right_divisibility star.circ_back_loop_fixpoint le_supI1 by blast
  have "(top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star> \<squnion> --v\<^sup>T) * w\<^sup>T = top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star> * w\<^sup>T \<squnion> --v\<^sup>T * w\<^sup>T"
    by (simp add: comp_right_dist_sup)
  also have "... \<le> top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star> \<squnion> --v\<^sup>T"
    using 2 3 by simp
  finally have "top * e \<squnion> (top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star> \<squnion> --v\<^sup>T) * w\<^sup>T \<le> top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star> \<squnion> --v\<^sup>T"
    using 4 by simp
  hence 5: "top * e * w\<^sup>T\<^sup>\<star> \<le> top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star> \<squnion> --v\<^sup>T"
    by (simp add: star_right_induct)
  have 6: "top * e \<le> top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star>"
    using sup_right_divisibility star.circ_back_loop_fixpoint by blast
  have "(top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star>)\<^sup>T \<le> (top * e * w\<^sup>T\<^sup>\<star>)\<^sup>T"
    by (simp add: star_isotone mult_right_isotone conv_isotone inf_assoc)
  also have "... = w\<^sup>\<star> * e\<^sup>T * top"
    by (simp add: conv_dist_comp conv_star_commute mult_assoc)
  finally have 7: "(top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star>)\<^sup>T \<le> w\<^sup>\<star> * e\<^sup>T * top"
    .
  have "(top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star>)\<^sup>T \<le> (top * e * (-v * -v\<^sup>T)\<^sup>\<star>)\<^sup>T"
    by (simp add: conv_isotone inf_commute mult_right_isotone star_isotone le_infI2)
  also have "... \<le> (top * v * -v\<^sup>T * (-v * -v\<^sup>T)\<^sup>\<star>)\<^sup>T"
    by (metis assms(3) conv_isotone mult_left_isotone mult_right_isotone mult_assoc)
  also have "... = (top * v * (-v\<^sup>T * -v)\<^sup>\<star> * -v\<^sup>T)\<^sup>T"
    by (simp add: mult_assoc star_slide)
  also have "... \<le> (top * -v\<^sup>T)\<^sup>T"
    using conv_order mult_left_isotone by auto
  also have "... = -v"
    by (simp add: assms(4) conv_complement vector_conv_compl)
  finally have 8: "(top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star>)\<^sup>T \<le> w\<^sup>\<star> * e\<^sup>T * top \<sqinter> -v"
    using 7 by simp
  have "covector (top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star>)"
    by (simp add: covector_mult_closed)
  hence "top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star> * (w\<^sup>T \<sqinter> -v\<^sup>T) = top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star> * (w\<^sup>T \<sqinter> -v\<^sup>T \<sqinter> (top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star>)\<^sup>T)"
    by (metis comp_inf_vector_1 inf.idem)
  also have "... \<le> top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star> * (w\<^sup>T \<sqinter> -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top \<sqinter> -v)"
    using 8 mult_right_isotone inf.sup_right_isotone inf_assoc by simp
  also have "... = top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star> * (w\<^sup>T \<sqinter> (-v \<sqinter> -v\<^sup>T) \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)"
    using inf_assoc inf_commute by (simp add: inf_assoc)
  also have "... = top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star> * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)"
    using assms(4) conv_complement vector_complement_closed vector_covector by fastforce
  also have "... \<le> top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star>"
    by (simp add: comp_associative comp_isotone star.circ_plus_same star.left_plus_below_circ)
  finally have 9: "top * e \<squnion> top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star> * (w\<^sup>T \<sqinter> -v\<^sup>T) \<le> top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star>"
    using 6 by simp
  have "prim_EP w v e \<le> -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>\<star>"
    using inf.sup_left_isotone by auto
  also have "... \<le> top * e * (w\<^sup>T \<sqinter> -v\<^sup>T)\<^sup>\<star>"
    using 5 by (metis inf_commute shunting_var_p)
  also have "... \<le> top * e * (w\<^sup>T \<sqinter> -v * -v\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>\<star>"
    using 9 by (simp add: star_right_induct)
  finally have 10: "prim_EP w v e \<le> top * e * (prim_P w v e)\<^sup>T\<^sup>\<star>"
    by (simp add: conv_complement conv_dist_comp conv_dist_inf conv_star_commute mult_assoc)
  have "top * e = top * (v * -v\<^sup>T \<sqinter> e)"
    by (simp add: assms(3) inf.absorb2)
  also have "... \<le> top * (v * top \<sqinter> e)"
    using inf.sup_right_isotone inf_commute mult_right_isotone top_greatest by presburger
  also have "... = (top \<sqinter> (v * top)\<^sup>T) * e"
    using assms(4) covector_inf_comp_3 by presburger
  also have "... = top * v\<^sup>T * e"
    by (simp add: conv_dist_comp)
  also have "... = top * r\<^sup>T * t\<^sup>\<star> * e"
    by (simp add: assms(5) comp_associative)
  also have "... \<le> top * r\<^sup>T * (prim_W w v e)\<^sup>\<star> * e"
    by (metis assms(4,6,7) mst_extends_old_tree star_isotone mult_left_isotone mult_right_isotone)
  finally have 11: "top * e \<le> top * r\<^sup>T * (prim_W w v e)\<^sup>\<star> * e"
    .
  have "r\<^sup>T * (prim_W w v e)\<^sup>\<star> * (prim_EP w v e) \<le> r\<^sup>T * (prim_W w v e)\<^sup>\<star> * (top * e * (prim_P w v e)\<^sup>T\<^sup>\<star>)"
    using 10 mult_right_isotone by blast
  also have "... = r\<^sup>T * (prim_W w v e)\<^sup>\<star> * top * e * (prim_P w v e)\<^sup>T\<^sup>\<star>"
    by (simp add: mult_assoc)
  also have "... \<le> top * e * (prim_P w v e)\<^sup>T\<^sup>\<star>"
    by (metis comp_associative comp_inf_covector inf.idem inf.sup_right_divisibility)
  also have "... \<le> top * r\<^sup>T * (prim_W w v e)\<^sup>\<star> * e * (prim_P w v e)\<^sup>T\<^sup>\<star>"
    using 11 by (simp add: mult_left_isotone)
  also have "... = r\<^sup>T * (prim_W w v e)\<^sup>\<star> * e * (prim_P w v e)\<^sup>T\<^sup>\<star>"
    using assms(2) vector_conv_covector by auto
  also have "... \<le> r\<^sup>T * (prim_W w v e)\<^sup>\<star> * (prim_W w v e) * (prim_P w v e)\<^sup>T\<^sup>\<star>"
    by (simp add: mult_left_isotone mult_right_isotone)
  also have "... \<le> r\<^sup>T * (prim_W w v e)\<^sup>\<star> * (prim_W w v e) * (prim_W w v e)\<^sup>\<star>"
    by (meson dual_order.trans mult_right_isotone star_isotone sup_ge1 sup_ge2)
  also have "... \<le> r\<^sup>T * (prim_W w v e)\<^sup>\<star>"
    by (metis mult_assoc mult_right_isotone star.circ_transitive_equal star.left_plus_below_circ)
  finally have 12: "r\<^sup>T * (prim_W w v e)\<^sup>\<star> * (prim_EP w v e) \<le> r\<^sup>T * (prim_W w v e)\<^sup>\<star>"
    .
  have "r\<^sup>T * (prim_W w v e)\<^sup>\<star> * w \<le> r\<^sup>T * (prim_W w v e)\<^sup>\<star> * (w \<squnion> prim_EP w v e)"
    by (simp add: inf_assoc)
  also have "... = r\<^sup>T * (prim_W w v e)\<^sup>\<star> * ((w \<squnion> prim_EP w v e) \<sqinter> (-(prim_EP w v e) \<squnion> prim_EP w v e))"
    by (metis assms(1) inf_top_right stone)
  also have "... = r\<^sup>T * (prim_W w v e)\<^sup>\<star> * ((w \<sqinter> -(prim_EP w v e)) \<squnion> prim_EP w v e)"
    by (simp add: sup_inf_distrib2)
  also have "... = r\<^sup>T * (prim_W w v e)\<^sup>\<star> * (w \<sqinter> -(prim_EP w v e)) \<squnion> r\<^sup>T * (prim_W w v e)\<^sup>\<star> * (prim_EP w v e)"
    by (simp add: comp_left_dist_sup)
  also have "... \<le> r\<^sup>T * (prim_W w v e)\<^sup>\<star> * (prim_W w v e) \<squnion> r\<^sup>T * (prim_W w v e)\<^sup>\<star> * (prim_EP w v e)"
    using mult_right_isotone sup_left_isotone by auto
  also have "... \<le> r\<^sup>T * (prim_W w v e)\<^sup>\<star> \<squnion> r\<^sup>T * (prim_W w v e)\<^sup>\<star> * (prim_EP w v e)"
    using mult_assoc mult_right_isotone star.circ_plus_same star.left_plus_below_circ sup_left_isotone by auto
  also have "... = r\<^sup>T * (prim_W w v e)\<^sup>\<star>"
    using 12 sup.absorb1 by blast
  finally have "r\<^sup>T \<squnion> r\<^sup>T * (prim_W w v e)\<^sup>\<star> * w \<le> r\<^sup>T * (prim_W w v e)\<^sup>\<star>"
    using 1 by simp
  thus ?thesis
    by (simp add: star_right_induct)
qed

text \<open>
Some of the following lemmas already hold in pseudocomplemented distributive Kleene allegories.
\<close>

subsubsection \<open>Exchange gives Minimum Spanning Trees\<close>

text \<open>
The lemmas in this section are used to show that the after exchange we obtain a minimum spanning tree.
The following lemmas show various interactions between the three constituents of the tree after exchange.
\<close>

lemma epm_1:
  "vector v \<Longrightarrow> prim_E w v e \<squnion> prim_P w v e = prim_EP w v e"
  by (metis inf_commute inf_sup_distrib1 mult_assoc mult_right_dist_sup regular_closed_p regular_complement_top vector_conv_compl)

lemma epm_2:
  assumes "regular (prim_EP w v e)"
      and "vector v"
    shows "(w \<sqinter> -(prim_EP w v e)) \<squnion> prim_P w v e \<squnion> prim_E w v e = w"
proof -
  have "(w \<sqinter> -(prim_EP w v e)) \<squnion> prim_P w v e \<squnion> prim_E w v e = (w \<sqinter> -(prim_EP w v e)) \<squnion> prim_EP w v e"
    using epm_1 sup_assoc sup_commute assms(2) by (simp add: inf_sup_distrib1)
  also have "... = w \<squnion> prim_EP w v e"
    by (metis assms(1) inf_top.right_neutral regular_complement_top sup_inf_distrib2)
  also have "... = w"
    by (simp add: sup_inf_distrib1)
  finally show ?thesis
    .
qed

lemma epm_4:
  assumes "e \<le> w"
      and "injective w"
      and "w * v \<le> v"
      and "e \<le> v * -v\<^sup>T"
    shows "top * e * w\<^sup>T\<^sup>+ \<le> top * v\<^sup>T"
proof -
  have "w\<^sup>\<star> * v \<le> v"
    by (simp add: assms(3) star_left_induct_mult)
  hence 1: "v\<^sup>T * w\<^sup>T\<^sup>\<star> \<le> v\<^sup>T"
    using conv_star_commute conv_dist_comp conv_isotone by fastforce
  have "e * w\<^sup>T \<le> w * w\<^sup>T \<sqinter> e * w\<^sup>T"
    by (simp add: assms(1) mult_left_isotone)
  also have "... \<le> 1 \<sqinter> e * w\<^sup>T"
    using assms(2) inf.sup_left_isotone by auto
  also have "... = 1 \<sqinter> w * e\<^sup>T"
    using calculation conv_dist_comp conv_involutive coreflexive_symmetric by fastforce
  also have "... \<le> w * e\<^sup>T"
    by simp
  also have "... \<le> w * -v * v\<^sup>T"
    by (metis assms(4) conv_complement conv_dist_comp conv_involutive conv_order mult_assoc mult_right_isotone)
  also have "... \<le> top * v\<^sup>T"
    by (simp add: mult_left_isotone)
  finally have "top * e * w\<^sup>T\<^sup>+ \<le> top * v\<^sup>T * w\<^sup>T\<^sup>\<star>"
    by (metis antisym comp_associative comp_isotone dense_top_closed mult_left_isotone transitive_top_closed)
  also have "... \<le> top * v\<^sup>T"
    using 1 by (simp add: mult_assoc mult_right_isotone)
  finally show ?thesis
    .
qed

lemma epm_5:
  assumes "e \<le> w"
      and "injective w"
      and "w * v \<le> v"
      and "e \<le> v * -v\<^sup>T"
      and "vector v"
    shows "prim_P w v e = bot"
proof -
  have 1: "e = w \<sqinter> top * e"
    by (simp add: assms(1,2) epm_3)
  have 2: "top * e * w\<^sup>T\<^sup>+ \<le> top * v\<^sup>T"
    by (simp add: assms(1-4) epm_4)
  have 3: "-v * -v\<^sup>T \<sqinter> top * v\<^sup>T = bot"
    by (simp add: assms(5) comp_associative covector_vector_comp inf.sup_monoid.add_commute schroeder_2)
  have "prim_P w v e = (w \<sqinter> -v * -v\<^sup>T \<sqinter> top * e) \<squnion> (w \<sqinter> -v * -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>+)"
    by (metis inf_sup_distrib1 mult_assoc star.circ_back_loop_fixpoint star_plus sup_commute)
  also have "... \<le> (e \<sqinter> -v * -v\<^sup>T) \<squnion> (w \<sqinter> -v * -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>+)"
    using 1 by (metis comp_inf.mult_semi_associative inf.sup_monoid.add_commute semiring.add_right_mono)
  also have "... \<le> (e \<sqinter> -v * -v\<^sup>T) \<squnion> (w \<sqinter> -v * -v\<^sup>T \<sqinter> top * v\<^sup>T)"
    using 2 by (metis sup_right_isotone inf.sup_right_isotone)
  also have "... \<le> (e \<sqinter> -v * -v\<^sup>T) \<squnion> (-v * -v\<^sup>T \<sqinter> top * v\<^sup>T)"
    using inf.assoc le_infI2 by auto
  also have "... \<le> v * -v\<^sup>T \<sqinter> -v * -v\<^sup>T"
    using 3 assms(4) inf.sup_left_isotone by auto
  also have "... \<le> v * top \<sqinter> -v * top"
    using inf.sup_mono mult_right_isotone top_greatest by blast
  also have "... = bot"
    using assms(5) inf_compl_bot vector_complement_closed by auto
  finally show ?thesis
    by (simp add: le_iff_inf)
qed

lemma epm_6:
  assumes "e \<le> w"
      and "injective w"
      and "w * v \<le> v"
      and "e \<le> v * -v\<^sup>T"
      and "vector v"
    shows "prim_E w v e = e"
proof -
  have 1: "e \<le> --v * -v\<^sup>T"
    using assms(4) mult_isotone order_lesseq_imp pp_increasing by blast
  have 2: "top * e * w\<^sup>T\<^sup>+ \<le> top * v\<^sup>T"
    by (simp add: assms(1-4) epm_4)
  have 3: "e = w \<sqinter> top * e"
    by (simp add: assms(1,2) epm_3)
  hence "e \<le> top * e * w\<^sup>T\<^sup>\<star>"
    by (metis le_infI2 star.circ_back_loop_fixpoint sup.commute sup_ge1)
  hence 4: "e \<le> prim_E w v e"
    using 1 by (simp add: assms(1))
  have 5: "--v * -v\<^sup>T \<sqinter> top * v\<^sup>T = bot"
    by (simp add: assms(5) comp_associative covector_vector_comp inf.sup_monoid.add_commute schroeder_2)
  have "prim_E w v e = (w \<sqinter> --v * -v\<^sup>T \<sqinter> top * e) \<squnion> (w \<sqinter> --v * -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>+)"
    by (metis inf_sup_distrib1 mult_assoc star.circ_back_loop_fixpoint star_plus sup_commute)
  also have "... \<le> (e \<sqinter> --v * -v\<^sup>T) \<squnion> (w \<sqinter> --v * -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>+)"
    using 3 by (metis comp_inf.mult_semi_associative inf.sup_monoid.add_commute semiring.add_right_mono)
  also have "... \<le> (e \<sqinter> --v * -v\<^sup>T) \<squnion> (w \<sqinter> --v * -v\<^sup>T \<sqinter> top * v\<^sup>T)"
    using 2 by (metis sup_right_isotone inf.sup_right_isotone)
  also have "... \<le> (e \<sqinter> --v * -v\<^sup>T) \<squnion> (--v * -v\<^sup>T \<sqinter> top * v\<^sup>T)"
    using inf.assoc le_infI2 by auto
  also have "... \<le> e"
    by (simp add: "5")
  finally show ?thesis
    using 4 by (simp add: antisym)
qed

lemma epm_7:
  "regular (prim_EP w v e) \<Longrightarrow> e \<le> w \<Longrightarrow> injective w \<Longrightarrow> w * v \<le> v \<Longrightarrow> e \<le> v * -v\<^sup>T \<Longrightarrow> vector v \<Longrightarrow> prim_W w v e = w"
  by (metis conv_bot epm_2 epm_5 epm_6)

lemma epm_8:
  assumes "acyclic w"
    shows "(w \<sqinter> -(prim_EP w v e)) \<sqinter> (prim_P w v e)\<^sup>T = bot"
proof -
  have "(w \<sqinter> -(prim_EP w v e)) \<sqinter> (prim_P w v e)\<^sup>T \<le> w \<sqinter> w\<^sup>T"
    by (meson conv_isotone inf_le1 inf_mono order_trans)
  thus ?thesis
    by (metis assms acyclic_asymmetric inf.commute le_bot)
qed

lemma epm_9:
  assumes "e \<le> v * -v\<^sup>T"
      and "vector v"
    shows "(w \<sqinter> -(prim_EP w v e)) \<sqinter> e = bot"
proof -
  have 1: "e \<le> -v\<^sup>T"
    by (metis assms complement_conv_sub vector_conv_covector ev p_antitone_iff p_bot)
  have "(w \<sqinter> -(prim_EP w v e)) \<sqinter> e = (w \<sqinter> --v\<^sup>T \<sqinter> e) \<squnion> (w \<sqinter> -(top * e * w\<^sup>T\<^sup>\<star>) \<sqinter> e)"
    by (simp add: inf_commute inf_sup_distrib1)
  also have "... \<le> (--v\<^sup>T \<sqinter> e) \<squnion> (-(top * e * w\<^sup>T\<^sup>\<star>) \<sqinter> e)"
    using comp_inf.mult_left_isotone inf.cobounded2 semiring.add_mono by blast
  also have "... = -(top * e * w\<^sup>T\<^sup>\<star>) \<sqinter> e"
    using 1 by (metis inf.sup_relative_same_increasing inf_commute inf_sup_distrib1 maddux_3_13 regular_closed_p)
  also have "... = bot"
    by (metis inf.sup_relative_same_increasing inf_bot_right inf_commute inf_p mult_left_isotone star_outer_increasing top_greatest)
  finally show ?thesis
    by (simp add: le_iff_inf)
qed

lemma epm_10:
  assumes "e \<le> v * -v\<^sup>T"
      and "vector v"
    shows "(prim_P w v e)\<^sup>T \<sqinter> e = bot"
proof -
  have "(prim_P w v e)\<^sup>T \<le> -v * -v\<^sup>T"
    by (simp add: conv_complement conv_dist_comp conv_dist_inf inf.absorb_iff1 inf.left_commute inf_commute)
  hence "(prim_P w v e)\<^sup>T \<sqinter> e \<le> -v * -v\<^sup>T \<sqinter> v * -v\<^sup>T"
    using assms(1) inf_mono by blast
  also have "... \<le> -v * top \<sqinter> v * top"
    using inf.sup_mono mult_right_isotone top_greatest by blast
  also have "... = bot"
    using assms(2) inf_compl_bot vector_complement_closed by auto
  finally show ?thesis
    by (simp add: le_iff_inf)
qed

lemma epm_11:
  assumes "vector v"
    shows "(w \<sqinter> -(prim_EP w v e)) \<sqinter> prim_P w v e = bot"
proof -
  have "prim_P w v e \<le> prim_EP w v e"
    by (metis assms comp_isotone inf.sup_left_isotone inf.sup_right_isotone order.refl top_greatest vector_conv_compl)
  thus ?thesis
    using inf_le2 order_trans p_antitone pseudo_complement by blast
qed

lemma epm_12:
  assumes "vector v"
    shows "(w \<sqinter> -(prim_EP w v e)) \<sqinter> prim_E w v e = bot"
proof -
  have "prim_E w v e \<le> prim_EP w v e"
    by (metis assms comp_isotone inf.sup_left_isotone inf.sup_right_isotone order.refl top_greatest vector_conv_compl)
  thus ?thesis
    using inf_le2 order_trans p_antitone pseudo_complement by blast
qed

lemma epm_13:
  assumes "vector v"
    shows "prim_P w v e \<sqinter> prim_E w v e = bot"
proof -
  have "prim_P w v e \<sqinter> prim_E w v e \<le> -v * -v\<^sup>T \<sqinter> --v * -v\<^sup>T"
    by (meson dual_order.trans inf.cobounded1 inf.sup_mono inf_le2)
  also have "... \<le> -v * top \<sqinter> --v * top"
    using inf.sup_mono mult_right_isotone top_greatest by blast
  also have "... = bot"
    using assms inf_compl_bot vector_complement_closed by auto
  finally show ?thesis
    by (simp add: le_iff_inf)
qed

text \<open>
The following lemmas show that the relation characterising the edge across the cut is an arc.
\<close>

lemma arc_edge_1:
  assumes "e \<le> v * -v\<^sup>T \<sqinter> g"
      and "vector v"
      and "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
      and "t \<le> g"
      and "r\<^sup>T * g\<^sup>\<star> \<le> r\<^sup>T * w\<^sup>\<star>"
    shows "top * e \<le> v\<^sup>T * w\<^sup>\<star>"
proof -
  have "top * e \<le> top * (v * -v\<^sup>T \<sqinter> g)"
    using assms(1) mult_right_isotone by auto
  also have "... \<le> top * (v * top \<sqinter> g)"
    using inf.sup_right_isotone inf_commute mult_right_isotone top_greatest by presburger
  also have "... = v\<^sup>T * g"
    by (metis assms(2) covector_inf_comp_3 inf_top.left_neutral)
  also have "... = r\<^sup>T * t\<^sup>\<star> * g"
    by (simp add: assms(3))
  also have "... \<le> r\<^sup>T * g\<^sup>\<star> * g"
    by (simp add: assms(4) mult_left_isotone mult_right_isotone star_isotone)
  also have "... \<le> r\<^sup>T * g\<^sup>\<star>"
    by (simp add: mult_assoc mult_right_isotone star.right_plus_below_circ)
  also have "... \<le> r\<^sup>T * w\<^sup>\<star>"
    by (simp add: assms(5))
  also have "... \<le> v\<^sup>T * w\<^sup>\<star>"
    by (metis assms(3) mult_left_isotone mult_right_isotone mult_1_right star.circ_reflexive)
  finally show ?thesis
    .
qed

lemma arc_edge_2:
  assumes "e \<le> v * -v\<^sup>T \<sqinter> g"
      and "vector v"
      and "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
      and "t \<le> g"
      and "r\<^sup>T * g\<^sup>\<star> \<le> r\<^sup>T * w\<^sup>\<star>"
      and "w * v \<le> v"
      and "injective w"
    shows "top * e * w\<^sup>T\<^sup>\<star> \<le> v\<^sup>T * w\<^sup>\<star>"
proof -
  have 1: "top * e \<le> v\<^sup>T * w\<^sup>\<star>"
    using assms(1-5) arc_edge_1 by blast
  have "v\<^sup>T * w\<^sup>\<star> * w\<^sup>T = v\<^sup>T * w\<^sup>T \<squnion> v\<^sup>T * w\<^sup>+ * w\<^sup>T"
    by (metis mult_assoc mult_left_dist_sup star.circ_loop_fixpoint sup_commute)
  also have "... \<le> v\<^sup>T \<squnion> v\<^sup>T * w\<^sup>+ * w\<^sup>T"
    by (metis assms(6) conv_dist_comp conv_isotone sup_left_isotone)
  also have "... = v\<^sup>T \<squnion> v\<^sup>T * w\<^sup>\<star> * (w * w\<^sup>T)"
    by (metis mult_assoc star_plus)
  also have "... \<le> v\<^sup>T \<squnion> v\<^sup>T * w\<^sup>\<star>"
    by (metis assms(7) mult_right_isotone mult_1_right sup_right_isotone)
  also have "... = v\<^sup>T * w\<^sup>\<star>"
    by (metis star.circ_back_loop_fixpoint sup_absorb2 sup_ge2)
  finally show ?thesis
    using 1 star_right_induct by auto
qed

lemma arc_edge_3:
  assumes "e \<le> v * -v\<^sup>T \<sqinter> g"
      and "vector v"
      and "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
      and "t \<le> g"
      and "r\<^sup>T * g\<^sup>\<star> \<le> r\<^sup>T * w\<^sup>\<star>"
      and "w * v \<le> v"
      and "injective w"
      and "prim_E w v e = bot"
    shows "e = bot"
proof -
  have "bot = prim_E w v e"
    by (simp add: assms(8))
  also have "... = w \<sqinter> --v * top \<sqinter> top * -v\<^sup>T \<sqinter> top * e * w\<^sup>T\<^sup>\<star>"
    by (metis assms(2) comp_inf_covector inf.assoc inf_top.left_neutral vector_conv_compl)
  also have "... = w \<sqinter> top * e * w\<^sup>T\<^sup>\<star> \<sqinter> -v\<^sup>T \<sqinter> --v"
    using assms(2) inf.assoc inf.commute vector_conv_compl vector_complement_closed by (simp add: inf_assoc)
  finally have 1: "w \<sqinter> top * e * w\<^sup>T\<^sup>\<star> \<sqinter> -v\<^sup>T \<le> -v"
    using shunting_1_pp by force
  have "w\<^sup>\<star> * e\<^sup>T * top = (top * e * w\<^sup>T\<^sup>\<star>)\<^sup>T"
    by (simp add: conv_star_commute comp_associative conv_dist_comp)
  also have "... \<le> (v\<^sup>T * w\<^sup>\<star>)\<^sup>T"
    using assms(1-7) arc_edge_2 by (simp add: conv_isotone)
  also have "... = w\<^sup>T\<^sup>\<star> * v"
    by (simp add: conv_star_commute conv_dist_comp)
  finally have 2: "w\<^sup>\<star> * e\<^sup>T * top \<le> w\<^sup>T\<^sup>\<star> * v"
    .
  have "(w\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top)\<^sup>T * -v = (w \<sqinter> top * e * w\<^sup>T\<^sup>\<star>) * -v"
    by (simp add: conv_dist_comp conv_dist_inf conv_star_commute mult_assoc)
  also have "... = (w \<sqinter> top * e * w\<^sup>T\<^sup>\<star> \<sqinter> -v\<^sup>T) * top"
    by (metis assms(2) conv_complement covector_inf_comp_3 inf_top.right_neutral vector_complement_closed)
  also have "... \<le> -v * top"
    using 1 by (simp add: comp_isotone)
  also have "... = -v"
    using assms(2) vector_complement_closed by auto
  finally have "(w\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top) * --v \<le> --v"
    using p_antitone_iff schroeder_3_p by auto
  hence "w\<^sup>\<star> * e\<^sup>T * top \<sqinter> w\<^sup>T * --v \<le> --v"
    by (simp add: inf_vector_comp)
  hence 3: "w\<^sup>T * --v \<le> --v \<squnion> -(w\<^sup>\<star> * e\<^sup>T * top)"
    by (simp add: inf.commute shunting_p)
  have "w\<^sup>T * -(w\<^sup>\<star> * e\<^sup>T * top) \<le> -(w\<^sup>\<star> * e\<^sup>T * top)"
    by (metis mult_assoc p_antitone p_antitone_iff schroeder_3_p star.circ_loop_fixpoint sup_commute sup_right_divisibility)
  also have "... \<le> --v \<squnion> -(w\<^sup>\<star> * e\<^sup>T * top)"
    by simp
  finally have "w\<^sup>T * (--v \<squnion> -(w\<^sup>\<star> * e\<^sup>T * top)) \<le> --v \<squnion> -(w\<^sup>\<star> * e\<^sup>T * top)"
    using 3 by (simp add: mult_left_dist_sup)
  hence "w\<^sup>T\<^sup>\<star> * (--v \<squnion> -(w\<^sup>\<star> * e\<^sup>T * top)) \<le> --v \<squnion> -(w\<^sup>\<star> * e\<^sup>T * top)"
    using star_left_induct_mult_iff by blast
  hence "w\<^sup>T\<^sup>\<star> * --v \<le> --v \<squnion> -(w\<^sup>\<star> * e\<^sup>T * top)"
    by (simp add: semiring.distrib_left)
  hence "w\<^sup>\<star> * e\<^sup>T * top \<sqinter> w\<^sup>T\<^sup>\<star> * --v \<le> --v"
    by (simp add: inf_commute shunting_p)
  hence "w\<^sup>\<star> * e\<^sup>T * top \<le> --v"
    using 2 by (metis inf.absorb1 p_antitone_iff p_comp_pp vector_export_comp)
  hence 4: "e\<^sup>T * top \<le> --v"
    by (metis mult_assoc star.circ_loop_fixpoint sup.bounded_iff)
  have "e\<^sup>T * top \<le> (v * -v\<^sup>T)\<^sup>T * top"
    using assms(1) comp_isotone conv_isotone by auto
  also have "... \<le> -v * top"
    by (simp add: conv_complement conv_dist_comp mult_assoc mult_right_isotone)
  also have "... = -v"
    using assms(2) vector_complement_closed by auto
  finally have "e\<^sup>T * top \<le> bot"
    using 4 shunting_1_pp by auto
  hence "e\<^sup>T = bot"
    using antisym bot_least top_right_mult_increasing by blast
  thus ?thesis
    using conv_bot by fastforce
qed

lemma arc_edge_4:
  assumes "e \<le> v * -v\<^sup>T \<sqinter> g"
      and "vector v"
      and "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
      and "t \<le> g"
      and "r\<^sup>T * g\<^sup>\<star> \<le> r\<^sup>T * w\<^sup>\<star>"
      and "arc e"
    shows "top * prim_E w v e * top = top"
proof -
  have "--v\<^sup>T * w = (--v\<^sup>T * w \<sqinter> -v\<^sup>T) \<squnion> (--v\<^sup>T * w \<sqinter> --v\<^sup>T)"
    by (simp add: maddux_3_11_pp)
  also have "... \<le> (--v\<^sup>T * w \<sqinter> -v\<^sup>T) \<squnion> --v\<^sup>T"
    using sup_right_isotone by auto
  also have "... = --v\<^sup>T * (w \<sqinter> -v\<^sup>T) \<squnion> --v\<^sup>T"
    using assms(2) covector_comp_inf covector_complement_closed vector_conv_covector by auto
  also have "... \<le> --v\<^sup>T * (w \<sqinter> -v\<^sup>T) * w\<^sup>\<star> \<squnion> --v\<^sup>T"
    by (metis star.circ_back_loop_fixpoint sup.cobounded2 sup_left_isotone)
  finally have 1: "--v\<^sup>T * w \<le> --v\<^sup>T * (w \<sqinter> -v\<^sup>T) * w\<^sup>\<star> \<squnion> --v\<^sup>T"
    .
  have "--v\<^sup>T * (w \<sqinter> -v\<^sup>T) * w\<^sup>\<star> * w \<le> --v\<^sup>T * (w \<sqinter> -v\<^sup>T) * w\<^sup>\<star> \<squnion> --v\<^sup>T"
    by (simp add: le_supI1 mult_assoc mult_right_isotone star.circ_plus_same star.left_plus_below_circ)
  hence 2: "(--v\<^sup>T * (w \<sqinter> -v\<^sup>T) * w\<^sup>\<star> \<squnion> --v\<^sup>T) * w \<le> --v\<^sup>T * (w \<sqinter> -v\<^sup>T) * w\<^sup>\<star> \<squnion> --v\<^sup>T"
    using 1 by (simp add: inf.orderE mult_right_dist_sup)
  have "v\<^sup>T \<le> --v\<^sup>T * (w \<sqinter> -v\<^sup>T) * w\<^sup>\<star> \<squnion> --v\<^sup>T"
    by (simp add: pp_increasing sup.coboundedI2)
  hence "v\<^sup>T * w\<^sup>\<star> \<le> --v\<^sup>T * (w \<sqinter> -v\<^sup>T) * w\<^sup>\<star> \<squnion> --v\<^sup>T"
    using 2 by (simp add: star_right_induct)
  hence 3: "-v\<^sup>T \<sqinter> v\<^sup>T * w\<^sup>\<star> \<le> --v\<^sup>T * (w \<sqinter> -v\<^sup>T) * w\<^sup>\<star>"
    by (metis inf_commute shunting_var_p)
  have "top * e = top * e \<sqinter> v\<^sup>T * w\<^sup>\<star>"
    by (meson assms(1-5) arc_edge_1 inf.orderE)
  also have "... \<le> top * v * -v\<^sup>T \<sqinter> v\<^sup>T * w\<^sup>\<star>"
    using assms(1) inf.sup_left_isotone mult_assoc mult_right_isotone by auto
  also have "... \<le> top * -v\<^sup>T \<sqinter> v\<^sup>T * w\<^sup>\<star>"
    using inf.sup_left_isotone mult_left_isotone top_greatest by blast
  also have "... = -v\<^sup>T \<sqinter> v\<^sup>T * w\<^sup>\<star>"
    by (simp add: assms(2) vector_conv_compl)
  also have "... \<le> --v\<^sup>T * (w \<sqinter> -v\<^sup>T) * w\<^sup>\<star>"
    using 3 by simp
  also have "... = (top \<sqinter> (--v)\<^sup>T) * (w \<sqinter> -v\<^sup>T) * w\<^sup>\<star>"
    by (simp add: conv_complement)
  also have "... = top * (w \<sqinter> --v \<sqinter> -v\<^sup>T) * w\<^sup>\<star>"
    using assms(2) covector_inf_comp_3 inf_assoc inf_left_commute vector_complement_closed by presburger
  also have "... = top * (w \<sqinter> --v * -v\<^sup>T) * w\<^sup>\<star>"
    by (metis assms(2) vector_complement_closed conv_complement inf_assoc vector_covector)
  finally have "top * (e\<^sup>T * top)\<^sup>T \<le> top * (w \<sqinter> --v * -v\<^sup>T) * w\<^sup>\<star>"
    by (metis conv_dist_comp conv_involutive conv_top mult_assoc top_mult_top)
  hence "top \<le> top * (w \<sqinter> --v * -v\<^sup>T) * w\<^sup>\<star> * (e\<^sup>T * top)"
    using assms(6) shunt_bijective by blast
  also have "... = top * (w \<sqinter> --v * -v\<^sup>T) * (top * e * w\<^sup>\<star>\<^sup>T)\<^sup>T"
    by (simp add: conv_dist_comp mult_assoc)
  also have "... = top * (w \<sqinter> --v * -v\<^sup>T \<sqinter> top * e * w\<^sup>\<star>\<^sup>T) * top"
    by (simp add: comp_inf_vector_1 mult_assoc)
  finally show ?thesis
    by (simp add: conv_star_commute top_le)
qed

lemma arc_edge_5:
  assumes "vector v"
      and "w * v \<le> v"
      and "injective w"
      and "arc e"
    shows "(prim_E w v e)\<^sup>T * top * prim_E w v e \<le> 1"
proof -
  have 1: "e\<^sup>T * top * e \<le> 1"
    by (simp add: assms(4) point_injective)
  have "prim_E w v e \<le> --v * top"
    by (simp add: inf_commute le_infI2 mult_right_isotone)
  hence 2: "prim_E w v e \<le> --v"
    by (simp add: assms(1) vector_complement_closed)
  have 3: "w * --v \<le> --v"
    by (simp add: assms(2) p_antitone p_antitone_iff)
  have "w \<sqinter> top * prim_E w v e \<le> w * (prim_E w v e)\<^sup>T * prim_E w v e"
    by (metis dedekind_2 inf.commute inf_top.left_neutral)
  also have "... \<le> w * w\<^sup>T * prim_E w v e"
    by (simp add: conv_isotone le_infI1 mult_left_isotone mult_right_isotone)
  also have "... \<le> prim_E w v e"
    by (metis assms(3) mult_left_isotone mult_left_one)
  finally have 4: "w \<sqinter> top * prim_E w v e \<le> prim_E w v e"
    .
  have "w\<^sup>+ \<sqinter> top * prim_E w v e = w\<^sup>\<star> * (w \<sqinter> top * prim_E w v e)"
    by (simp add: comp_inf_covector star_plus)
  also have "... \<le> w\<^sup>\<star> * prim_E w v e"
    using 4 by (simp add: mult_right_isotone)
  also have "... \<le> --v"
    using 2 3 star_left_induct sup.bounded_iff by blast
  finally have 5: "w\<^sup>+ \<sqinter> top * prim_E w v e \<sqinter> -v = bot"
    using shunting_1_pp by blast
  hence 6: "w\<^sup>+\<^sup>T \<sqinter> (prim_E w v e)\<^sup>T * top \<sqinter> -v\<^sup>T = bot"
    using conv_complement conv_dist_comp conv_dist_inf conv_top conv_bot by force
  have "(prim_E w v e)\<^sup>T * top * prim_E w v e \<le> (top * e * w\<^sup>T\<^sup>\<star>)\<^sup>T * top * (top * e * w\<^sup>T\<^sup>\<star>)"
    by (simp add: conv_isotone mult_isotone)
  also have "... = w\<^sup>\<star> * e\<^sup>T * top * e * w\<^sup>T\<^sup>\<star>"
    by (metis conv_star_commute conv_dist_comp conv_involutive conv_top mult_assoc top_mult_top)
  also have "... \<le> w\<^sup>\<star> * w\<^sup>T\<^sup>\<star>"
    using 1 by (metis mult_assoc mult_1_right mult_right_isotone mult_left_isotone)
  also have "... = w\<^sup>\<star> \<squnion> w\<^sup>T\<^sup>\<star>"
    by (metis assms(3) cancel_separate inf.eq_iff star.circ_sup_sub_sup_one_1 star.circ_plus_one star_involutive)
  also have "... = w\<^sup>+ \<squnion> w\<^sup>T\<^sup>+ \<squnion> 1"
    by (metis star.circ_plus_one star_left_unfold_equal sup.assoc sup.commute)
  finally have 7: "(prim_E w v e)\<^sup>T * top * prim_E w v e \<le> w\<^sup>+ \<squnion> w\<^sup>T\<^sup>+ \<squnion> 1"
    .
  have "prim_E w v e \<le> --v * -v\<^sup>T"
    by (simp add: le_infI1)
  also have "... \<le> top * -v\<^sup>T"
    by (simp add: mult_left_isotone)
  also have "... = -v\<^sup>T"
    by (simp add: assms(1) vector_conv_compl)
  finally have 8: "prim_E w v e \<le> -v\<^sup>T"
    .
  hence 9: "(prim_E w v e)\<^sup>T \<le> -v"
    by (metis conv_complement conv_involutive conv_isotone)
  have "(prim_E w v e)\<^sup>T * top * prim_E w v e = (w\<^sup>+ \<squnion> w\<^sup>T\<^sup>+ \<squnion> 1) \<sqinter> (prim_E w v e)\<^sup>T * top * prim_E w v e"
    using 7 by (simp add: inf.absorb_iff2)
  also have "... = (1 \<sqinter> (prim_E w v e)\<^sup>T * top * prim_E w v e) \<squnion> (w\<^sup>+ \<sqinter> (prim_E w v e)\<^sup>T * top * prim_E w v e) \<squnion> (w\<^sup>T\<^sup>+ \<sqinter> (prim_E w v e)\<^sup>T * top * prim_E w v e)"
    using comp_inf.mult_right_dist_sup sup_assoc sup_commute by auto
  also have "... \<le> 1 \<squnion> (w\<^sup>+ \<sqinter> (prim_E w v e)\<^sup>T * top * prim_E w v e) \<squnion> (w\<^sup>T\<^sup>+ \<sqinter> (prim_E w v e)\<^sup>T * top * prim_E w v e)"
    using inf_le1 sup_left_isotone by blast
  also have "... \<le> 1 \<squnion> (w\<^sup>+ \<sqinter> (prim_E w v e)\<^sup>T * top * prim_E w v e) \<squnion> (w\<^sup>T\<^sup>+ \<sqinter> (prim_E w v e)\<^sup>T * top * -v\<^sup>T)"
    using 8 inf.sup_right_isotone mult_right_isotone sup_right_isotone by blast
  also have "... \<le> 1 \<squnion> (w\<^sup>+ \<sqinter> -v * top * prim_E w v e) \<squnion> (w\<^sup>T\<^sup>+ \<sqinter> (prim_E w v e)\<^sup>T * top * -v\<^sup>T)"
    using 9 by (metis inf.sup_right_isotone mult_left_isotone sup.commute sup_right_isotone)
  also have "... = 1 \<squnion> (w\<^sup>+ \<sqinter> -v * top \<sqinter> top * prim_E w v e) \<squnion> (w\<^sup>T\<^sup>+ \<sqinter> (prim_E w v e)\<^sup>T * top \<sqinter> top * -v\<^sup>T)"
    by (metis (no_types) vector_export_comp inf_top_right inf_assoc)
  also have "... = 1 \<squnion> (w\<^sup>+ \<sqinter> -v \<sqinter> top * prim_E w v e) \<squnion> (w\<^sup>T\<^sup>+ \<sqinter> (prim_E w v e)\<^sup>T * top \<sqinter> -v\<^sup>T)"
    using assms(1) vector_complement_closed vector_conv_compl by auto
  also have "... = 1"
    using 5 6 by (simp add: conv_star_commute conv_dist_comp inf.commute inf_assoc star.circ_plus_same)
  finally show ?thesis
    .
qed

lemma arc_edge_6:
  assumes "vector v"
      and "w * v \<le> v"
      and "injective w"
      and "arc e"
    shows "prim_E w v e * top * (prim_E w v e)\<^sup>T \<le> 1"
proof -
  have "prim_E w v e * 1 * (prim_E w v e)\<^sup>T \<le> w * w\<^sup>T"
    using comp_isotone conv_order inf.coboundedI1 mult_one_associative by auto
  also have "... \<le> 1"
    by (simp add: assms(3))
  finally have 1: "prim_E w v e * 1 * (prim_E w v e)\<^sup>T \<le> 1"
    .
  have "(prim_E w v e)\<^sup>T * top * prim_E w v e \<le> 1"
    by (simp add: assms arc_edge_5)
  also have "... \<le> --1"
    by (simp add: pp_increasing)
  finally have 2: "prim_E w v e * -1 * (prim_E w v e)\<^sup>T \<le> bot"
    by (metis conv_involutive regular_closed_bot regular_dense_top triple_schroeder_p)
  have "prim_E w v e * top * (prim_E w v e)\<^sup>T = prim_E w v e * 1 * (prim_E w v e)\<^sup>T \<squnion> prim_E w v e * -1 * (prim_E w v e)\<^sup>T"
    by (metis mult_left_dist_sup mult_right_dist_sup regular_complement_top regular_one_closed)
  also have "... \<le> 1"
    using 1 2 by (simp add: bot_unique)
  finally show ?thesis
    .
qed

lemma arc_edge:
  assumes "e \<le> v * -v\<^sup>T \<sqinter> g"
      and "vector v"
      and "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
      and "t \<le> g"
      and "r\<^sup>T * g\<^sup>\<star> \<le> r\<^sup>T * w\<^sup>\<star>"
      and "w * v \<le> v"
      and "injective w"
      and "arc e"
    shows "arc (prim_E w v e)"
proof (intro conjI)
  have "prim_E w v e * top * (prim_E w v e)\<^sup>T \<le> 1"
    using assms(2,6-8) arc_edge_6 by simp
  thus "injective (prim_E w v e * top)"
    by (metis conv_dist_comp conv_top mult_assoc top_mult_top)
next
  show "surjective (prim_E w v e * top)"
    using assms(1-5,8) arc_edge_4 mult_assoc by simp
next
  have "(prim_E w v e)\<^sup>T * top * prim_E w v e \<le> 1"
    using assms(2,6-8) arc_edge_5 by simp
  thus "injective ((prim_E w v e)\<^sup>T * top)"
    by (metis conv_dist_comp conv_involutive conv_top mult_assoc top_mult_top)
next
  have "top * prim_E w v e * top = top"
    using assms(1-5,8) arc_edge_4 by simp
  thus "surjective ((prim_E w v e)\<^sup>T * top)"
    by (metis mult_assoc conv_dist_comp conv_top)
qed

subsubsection \<open>Invariant implies Postcondition\<close>

text \<open>
The lemmas in this section are used to show that the invariant implies the postcondition at the end of the algorithm.
The following lemma shows that the nodes reachable in the graph are the same as those reachable in the constructed tree.
\<close>

lemma span_post:
  assumes "regular v"
      and "vector v"
      and "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
      and "v * -v\<^sup>T \<sqinter> g = bot"
      and "t \<le> v * v\<^sup>T \<sqinter> g"
      and "r\<^sup>T * (v * v\<^sup>T \<sqinter> g)\<^sup>\<star> \<le> r\<^sup>T * t\<^sup>\<star>"
    shows "v\<^sup>T = r\<^sup>T * g\<^sup>\<star>"
proof -
  let ?vv = "v * v\<^sup>T \<sqinter> g"
  have 1: "r\<^sup>T \<le> v\<^sup>T"
    using assms(3) mult_right_isotone mult_1_right star.circ_reflexive by fastforce
  have "v * top \<sqinter> g = (v * v\<^sup>T \<squnion> v * -v\<^sup>T) \<sqinter> g"
    by (metis assms(1) conv_complement mult_left_dist_sup regular_complement_top)
  also have "... = ?vv \<squnion> (v * -v\<^sup>T \<sqinter> g)"
    by (simp add: inf_sup_distrib2)
  also have "... = ?vv"
    by (simp add: assms(4))
  finally have 2: "v * top \<sqinter> g = ?vv"
    by simp
  have "r\<^sup>T * ?vv\<^sup>\<star> \<le> v\<^sup>T * ?vv\<^sup>\<star>"
    using 1 by (simp add: comp_left_isotone)
  also have "... \<le> v\<^sup>T * (v * v\<^sup>T)\<^sup>\<star>"
    by (simp add: comp_right_isotone star.circ_isotone)
  also have "... \<le> v\<^sup>T"
    by (simp add: assms(2) vector_star_1)
  finally have "r\<^sup>T * ?vv\<^sup>\<star> \<le> v\<^sup>T"
    by simp
  hence "r\<^sup>T * ?vv\<^sup>\<star> * g = (r\<^sup>T * ?vv\<^sup>\<star> \<sqinter> v\<^sup>T) * g"
    by (simp add: inf.absorb1)
  also have "... = r\<^sup>T * ?vv\<^sup>\<star> * (v * top \<sqinter> g)"
    by (simp add: assms(2) covector_inf_comp_3)
  also have "... = r\<^sup>T * ?vv\<^sup>\<star> * ?vv"
    using 2 by simp
  also have "... \<le> r\<^sup>T * ?vv\<^sup>\<star>"
    by (simp add: comp_associative comp_right_isotone star.left_plus_below_circ star_plus)
  finally have "r\<^sup>T \<squnion> r\<^sup>T * ?vv\<^sup>\<star> * g \<le> r\<^sup>T * ?vv\<^sup>\<star>"
    using star.circ_back_loop_prefixpoint by auto
  hence "r\<^sup>T * g\<^sup>\<star> \<le> r\<^sup>T * ?vv\<^sup>\<star>"
    using star_right_induct by blast
  hence "r\<^sup>T * g\<^sup>\<star> = r\<^sup>T * ?vv\<^sup>\<star>"
    by (simp add: antisym mult_right_isotone star_isotone)
  also have "... = r\<^sup>T * t\<^sup>\<star>"
    using assms(5,6) antisym mult_right_isotone star_isotone by auto
  also have "... = v\<^sup>T"
    by (simp add: assms(3))
  finally show ?thesis
    by simp
qed

text \<open>
The following lemma shows that the minimum spanning tree extending a tree is the same as the tree at the end of the algorithm.
\<close>

lemma mst_post:
  assumes "vector r"
      and "injective r"
      and "v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
      and "forest w"
      and "t \<le> w"
      and "w \<le> v * v\<^sup>T"
    shows "w = t"
proof -
  have 1: "vector v"
    using assms(1,3) covector_mult_closed vector_conv_covector by auto
  have "w * v \<le> v * v\<^sup>T * v"
    by (simp add: assms(6) mult_left_isotone)
  also have "... \<le> v"
    using 1 by (metis mult_assoc mult_right_isotone top_greatest)
  finally have 2: "w * v \<le> v"
    .
  have 3: "r \<le> v"
    by (metis assms(3) conv_order mult_right_isotone mult_1_right star.circ_reflexive)
  have 4: "v \<sqinter> -r = t\<^sup>T\<^sup>\<star> * r \<sqinter> -r"
    by (metis assms(3) conv_dist_comp conv_involutive conv_star_commute)
  also have "... = (r \<squnion> t\<^sup>T\<^sup>+ * r) \<sqinter> -r"
    using mult_assoc star.circ_loop_fixpoint sup_commute by auto
  also have "... \<le> t\<^sup>T\<^sup>+ * r"
    by (simp add: shunting)
  also have "... \<le> t\<^sup>T * top"
    by (simp add: comp_isotone mult_assoc)
  finally have "1 \<sqinter> (v \<sqinter> -r) * (v \<sqinter> -r)\<^sup>T \<le> 1 \<sqinter> t\<^sup>T * top * (t\<^sup>T * top)\<^sup>T"
    using conv_order inf.sup_right_isotone mult_isotone by auto
  also have "... = 1 \<sqinter> t\<^sup>T * top * t"
    by (metis conv_dist_comp conv_involutive conv_top mult_assoc top_mult_top)
  also have "... \<le> t\<^sup>T * (top * t \<sqinter> t * 1)"
    by (metis conv_involutive dedekind_1 inf.commute mult_assoc)
  also have "... \<le> t\<^sup>T * t"
    by (simp add: mult_right_isotone)
  finally have 5: "1 \<sqinter> (v \<sqinter> -r) * (v \<sqinter> -r)\<^sup>T \<le> t\<^sup>T * t"
    .
  have "w * w\<^sup>+ \<le> -1"
    by (metis assms(4) mult_right_isotone order_trans star.circ_increasing star.left_plus_circ)
  hence 6: "w\<^sup>T\<^sup>+ \<le> -w"
    by (metis conv_star_commute mult_assoc mult_1_left triple_schroeder_p)
  have "w * r \<sqinter> w\<^sup>T\<^sup>+ * r = (w \<sqinter> w\<^sup>T\<^sup>+) * r"
    using assms(2) by (simp add: injective_comp_right_dist_inf)
  also have "... = bot"
    using 6 p_antitone pseudo_complement_pp semiring.mult_not_zero by blast
  finally have 7: "w * r \<sqinter> w\<^sup>T\<^sup>+ * r = bot"
    .
  have "-1 * r \<le> -r"
    using assms(2) local.dual_order.trans local.pp_increasing local.schroeder_4_p by blast
  hence "-1 * r * top \<le> -r"
    by (simp add: assms(1) comp_associative)
  hence 8: "r\<^sup>T * -1 * r \<le> bot"
    by (simp add: mult_assoc schroeder_6_p)
  have "r\<^sup>T * w * r \<le> r\<^sup>T * w\<^sup>+ * r"
    by (simp add: mult_left_isotone mult_right_isotone star.circ_mult_increasing)
  also have "... \<le> r\<^sup>T * -1 * r"
    by (simp add: assms(4) comp_isotone)
  finally have "r\<^sup>T * w * r \<le> bot"
    using 8 by simp
  hence "w * r * top \<le> -r"
    by (simp add: mult_assoc schroeder_6_p)
  hence "w * r \<le> -r"
    by (simp add: assms(1) comp_associative)
  hence "w * r \<le> -r \<sqinter> w * v"
    using 3 by (simp add: mult_right_isotone)
  also have "... \<le> -r \<sqinter> v"
    using 2 by (simp add: le_infI2)
  also have "... = -r \<sqinter> t\<^sup>T\<^sup>\<star> * r"
    using 4 by (simp add: inf_commute)
  also have "... \<le> -r \<sqinter> w\<^sup>T\<^sup>\<star> * r"
    using assms(5) comp_inf.mult_right_isotone conv_isotone mult_left_isotone star_isotone by auto
  also have "... = -r \<sqinter> (r \<squnion> w\<^sup>T\<^sup>+ * r)"
    using mult_assoc star.circ_loop_fixpoint sup_commute by auto
  also have "... \<le> w\<^sup>T\<^sup>+ * r"
    using inf.commute maddux_3_13 by auto
  finally have "w * r = bot"
    using 7 by (simp add: le_iff_inf)
  hence "w = w \<sqinter> top * -r\<^sup>T"
    by (metis complement_conv_sub conv_dist_comp conv_involutive conv_bot inf.assoc inf.orderE regular_closed_bot regular_dense_top top_left_mult_increasing)
  also have "... = w \<sqinter> v * v\<^sup>T \<sqinter> top * -r\<^sup>T"
    by (simp add: assms(6) inf_absorb1)
  also have "... \<le> w \<sqinter> top * v\<^sup>T \<sqinter> top * -r\<^sup>T"
    using comp_inf.mult_left_isotone comp_inf.mult_right_isotone mult_left_isotone by auto
  also have "... = w \<sqinter> top * (v\<^sup>T \<sqinter> -r\<^sup>T)"
    using 1 assms(1) covector_inf_closed inf_assoc vector_conv_compl vector_conv_covector by auto
  also have "... = w * (1 \<sqinter> (v \<sqinter> -r) * top)"
    by (simp add: comp_inf_vector conv_complement conv_dist_inf)
  also have "... = w * (1 \<sqinter> (v \<sqinter> -r) * (v \<sqinter> -r)\<^sup>T)"
    by (metis conv_top dedekind_eq inf_commute inf_top_left mult_1_left mult_1_right)
  also have "... \<le> w * t\<^sup>T * t"
    using 5 by (simp add: comp_isotone mult_assoc)
  also have "... \<le> w * w\<^sup>T * t"
    by (simp add: assms(5) comp_isotone conv_isotone)
  also have "... \<le> t"
    using assms(4) mult_left_isotone mult_1_left by fastforce
  finally show ?thesis
    by (simp add: assms(5) antisym)
qed

subsection \<open>Kruskal's Algorithm\<close>

text \<open>
The following results are used for proving the correctness of Kruskal's minimum spanning tree algorithm.
\<close>

subsubsection \<open>Preservation of Invariant\<close>

text \<open>
We first treat the preservation of the invariant.
The following lemmas show conditions necessary for preserving that \<open>f\<close> is a forest.
\<close>

lemma kruskal_injective_inv_2:
  assumes "arc e"
      and "acyclic f"
    shows "top * e * f\<^sup>T\<^sup>\<star> * f\<^sup>T \<le> -e"
proof -
  have "f \<le> -f\<^sup>T\<^sup>\<star>"
    using assms(2) acyclic_star_below_complement p_antitone_iff by simp
  hence "e * f \<le> top * e * -f\<^sup>T\<^sup>\<star>"
    by (simp add: comp_isotone top_left_mult_increasing)
  also have "... = -(top * e * f\<^sup>T\<^sup>\<star>)"
    by (metis assms(1) comp_mapping_complement conv_dist_comp conv_involutive conv_top)
  finally show ?thesis
    using schroeder_4_p by simp
qed

lemma kruskal_injective_inv_3:
  assumes "arc e"
      and "forest f"
    shows "(top * e * f\<^sup>T\<^sup>\<star>)\<^sup>T * (top * e * f\<^sup>T\<^sup>\<star>) \<sqinter> f\<^sup>T * f \<le> 1"
proof -
  have "(top * e * f\<^sup>T\<^sup>\<star>)\<^sup>T * (top * e * f\<^sup>T\<^sup>\<star>) = f\<^sup>\<star> * e\<^sup>T * top * e * f\<^sup>T\<^sup>\<star>"
    by (metis conv_dist_comp conv_involutive conv_star_commute conv_top vector_top_closed mult_assoc)
  also have "... \<le> f\<^sup>\<star> * f\<^sup>T\<^sup>\<star>"
    by (metis assms(1) arc_expanded mult_left_isotone mult_right_isotone mult_1_left mult_assoc)
  finally have "(top * e * f\<^sup>T\<^sup>\<star>)\<^sup>T * (top * e * f\<^sup>T\<^sup>\<star>) \<sqinter> f\<^sup>T * f \<le> f\<^sup>\<star> * f\<^sup>T\<^sup>\<star> \<sqinter> f\<^sup>T * f"
    using inf.sup_left_isotone by simp
  also have "... \<le> 1"
    using assms(2) forest_separate by simp
  finally show ?thesis
    by simp
qed

lemma kruskal_acyclic_inv:
  assumes "acyclic f"
      and "covector q"
      and "(f \<sqinter> q)\<^sup>T * f\<^sup>\<star> * e = bot"
      and "e * f\<^sup>\<star> * e = bot"
      and "f\<^sup>T\<^sup>\<star> * f\<^sup>\<star> \<le> -e"
    shows "acyclic ((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T \<squnion> e)"
proof -
  have "(f \<sqinter> -q) * (f \<sqinter> q)\<^sup>T = (f \<sqinter> -q) * (f\<^sup>T \<sqinter> q\<^sup>T)"
    by (simp add: conv_dist_inf)
  hence 1: "(f \<sqinter> -q) * (f \<sqinter> q)\<^sup>T = bot"
    by (metis assms(2) comp_inf.semiring.mult_zero_right comp_inf_vector_1 conv_bot covector_bot_closed inf.sup_monoid.add_assoc p_inf)
  hence 2: "(f \<sqinter> -q)\<^sup>\<star> * (f \<sqinter> q)\<^sup>T = (f \<sqinter> q)\<^sup>T"
    using mult_right_zero star_absorb star_simulation_right_equal by fastforce
  hence 3: "((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T)\<^sup>+ = (f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>+ \<squnion> (f \<sqinter> q)\<^sup>T\<^sup>+"
    by (simp add: plus_sup)
  have 4: "((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T)\<^sup>\<star> = (f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>\<star>"
    using 2 by (simp add: star.circ_sup_9)
  have "(f \<sqinter> q)\<^sup>T * (f \<sqinter> -q)\<^sup>\<star> * e \<le> (f \<sqinter> q)\<^sup>T * f\<^sup>\<star> * e"
    by (simp add: mult_left_isotone mult_right_isotone star_isotone)
  hence "(f \<sqinter> q)\<^sup>T * (f \<sqinter> -q)\<^sup>\<star> * e = bot"
    using assms(3) le_bot by simp
  hence 5: "(f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>\<star> * e = (f \<sqinter> -q)\<^sup>\<star> * e"
    by (metis comp_associative conv_bot conv_dist_comp conv_involutive conv_star_commute star_absorb)
  have "e * (f \<sqinter> -q)\<^sup>\<star> * e \<le> e * f\<^sup>\<star> * e"
    by (simp add: mult_left_isotone mult_right_isotone star_isotone)
  hence "e * (f \<sqinter> -q)\<^sup>\<star> * e = bot"
    using assms(4) le_bot by simp
  hence 6: "((f \<sqinter> -q)\<^sup>\<star> * e)\<^sup>+ = (f \<sqinter> -q)\<^sup>\<star> * e"
    by (simp add: comp_associative star_absorb)
  have "f\<^sup>T\<^sup>\<star> * 1 * f\<^sup>T\<^sup>\<star> * f\<^sup>\<star> \<le> -e"
    by (simp add: assms(5) star.circ_transitive_equal)
  hence 7: "f\<^sup>\<star> * e * f\<^sup>T\<^sup>\<star> * f\<^sup>\<star> \<le> -1"
    by (metis comp_right_one conv_involutive conv_one conv_star_commute triple_schroeder_p)
  have "(f \<sqinter> -q)\<^sup>+ * (f \<sqinter> q)\<^sup>T\<^sup>+ \<le> -1"
    using 1 2 by (metis forest_bot mult_left_zero mult_assoc)
  hence 8: "(f \<sqinter> q)\<^sup>T\<^sup>+ * (f \<sqinter> -q)\<^sup>+ \<le> -1"
    using comp_commute_below_diversity by simp
  have 9: "f\<^sup>T\<^sup>+ \<le> -1"
    using assms(1) acyclic_star_below_complement schroeder_5_p by force
  have "((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T \<squnion> e)\<^sup>+ = (((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T)\<^sup>\<star> * e)\<^sup>\<star> * ((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T)\<^sup>+ \<squnion> (((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T)\<^sup>\<star> * e)\<^sup>+"
    by (simp add: plus_sup)
  also have "... = ((f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>\<star> * e)\<^sup>\<star> * ((f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>+ \<squnion> (f \<sqinter> q)\<^sup>T\<^sup>+) \<squnion> ((f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>\<star> * e)\<^sup>+"
    using 3 4 by simp
  also have "... = ((f \<sqinter> -q)\<^sup>\<star> * e)\<^sup>\<star> * ((f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>+ \<squnion> (f \<sqinter> q)\<^sup>T\<^sup>+) \<squnion> ((f \<sqinter> -q)\<^sup>\<star> * e)\<^sup>+"
    using 5 by simp
  also have "... = ((f \<sqinter> -q)\<^sup>\<star> * e \<squnion> 1) * ((f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>+ \<squnion> (f \<sqinter> q)\<^sup>T\<^sup>+) \<squnion> (f \<sqinter> -q)\<^sup>\<star> * e"
    using 6 by (metis star_left_unfold_equal sup_monoid.add_commute)
  also have "... = (f \<sqinter> -q)\<^sup>\<star> * e \<squnion> (f \<sqinter> -q)\<^sup>\<star> * e * (f \<sqinter> q)\<^sup>T\<^sup>+ \<squnion> (f \<sqinter> -q)\<^sup>\<star> * e * (f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>+ \<squnion> (f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>+ \<squnion> (f \<sqinter> q)\<^sup>T\<^sup>+"
    using comp_associative mult_left_dist_sup mult_right_dist_sup sup_assoc sup_commute by simp
  also have "... = (f \<sqinter> -q)\<^sup>\<star> * e * (f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>\<star> \<squnion> (f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>+ \<squnion> (f \<sqinter> q)\<^sup>T\<^sup>+"
    by (metis star.circ_back_loop_fixpoint star_plus sup_monoid.add_commute mult_assoc)
  also have "... \<le> f\<^sup>\<star> * e * f\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>\<star> \<squnion> (f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>+ \<squnion> (f \<sqinter> q)\<^sup>T\<^sup>+"
    using mult_left_isotone mult_right_isotone star_isotone sup_left_isotone conv_isotone order_trans inf_le1 by meson
  also have "... \<le> f\<^sup>\<star> * e * f\<^sup>T\<^sup>\<star> * f\<^sup>\<star> \<squnion> (f \<sqinter> q)\<^sup>T\<^sup>\<star> * (f \<sqinter> -q)\<^sup>+ \<squnion> f\<^sup>T\<^sup>+"
    using mult_left_isotone mult_right_isotone star_isotone sup_left_isotone sup_right_isotone conv_isotone order_trans inf_le1 by meson
  also have "... = f\<^sup>\<star> * e * f\<^sup>T\<^sup>\<star> * f\<^sup>\<star> \<squnion> (f \<sqinter> q)\<^sup>T\<^sup>+ * (f \<sqinter> -q)\<^sup>+ \<squnion> (f \<sqinter> -q)\<^sup>+ \<squnion> f\<^sup>T\<^sup>+"
    by (simp add: star.circ_loop_fixpoint sup_monoid.add_assoc mult_assoc)
  also have "... \<le> f\<^sup>\<star> * e * f\<^sup>T\<^sup>\<star> * f\<^sup>\<star> \<squnion> (f \<sqinter> q)\<^sup>T\<^sup>+ * (f \<sqinter> -q)\<^sup>+ \<squnion> f\<^sup>+ \<squnion> f\<^sup>T\<^sup>+"
    using mult_left_isotone mult_right_isotone star_isotone sup_left_isotone sup_right_isotone order_trans inf_le1 by meson
  also have "... \<le> -1"
    using 7 8 9 assms(1) by simp
  finally show ?thesis
    by simp
qed

lemma kruskal_exchange_acyclic_inv_1:
  assumes "acyclic f"
      and "covector q"
    shows "acyclic ((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T)"
  using kruskal_acyclic_inv[where e=bot] by (simp add: assms)

lemma kruskal_exchange_acyclic_inv_2:
  assumes "acyclic w"
      and "injective w"
      and "d \<le> w"
      and "bijective (d\<^sup>T * top)"
      and "bijective (e * top)"
      and "d \<le> top * e\<^sup>T * w\<^sup>T\<^sup>\<star>"
      and "w * e\<^sup>T * top = bot"
    shows "acyclic ((w \<sqinter> -d) \<squnion> e)"
proof -
  let ?v = "w \<sqinter> -d"
  let ?w = "?v \<squnion> e"
  have "d\<^sup>T * top \<le> w\<^sup>\<star> * e * top"
    by (metis assms(6) comp_associative comp_inf.star.circ_decompose_9 comp_inf.star_star_absorb comp_isotone conv_dist_comp conv_involutive conv_order conv_star_commute conv_top inf.cobounded1 vector_top_closed)
  hence 1: "e * top \<le> w\<^sup>T\<^sup>\<star> * d\<^sup>T * top"
    by (metis assms(4,5) bijective_reverse comp_associative conv_star_commute)
  have 2: "?v * d\<^sup>T * top = bot"
    by (simp add: assms(2,3) kruskal_exchange_acyclic_inv_3)
  have "?v * w\<^sup>T\<^sup>+ * d\<^sup>T * top \<le> w * w\<^sup>T\<^sup>+ * d\<^sup>T * top"
    by (simp add: mult_left_isotone)
  also have "... \<le> w\<^sup>T\<^sup>\<star> * d\<^sup>T * top"
    by (metis assms(2) mult_left_isotone mult_1_left mult_assoc)
  finally have "?v * w\<^sup>T\<^sup>\<star> * d\<^sup>T * top \<le> w\<^sup>T\<^sup>\<star> * d\<^sup>T * top"
    using 2 by (metis bot_least comp_associative mult_right_dist_sup star.circ_back_loop_fixpoint star.circ_plus_same sup_least)
  hence 3: "?v\<^sup>\<star> * e * top \<le> w\<^sup>T\<^sup>\<star> * d\<^sup>T * top"
    using 1 by (simp add: comp_associative star_left_induct sup_least)
  have "d * e\<^sup>T \<le> bot"
    by (metis assms(3,7) conv_bot conv_dist_comp conv_involutive conv_top order.trans inf.absorb2 inf.cobounded2 inf_commute le_bot p_antitone_iff p_top schroeder_4_p top_left_mult_increasing)
  hence 4: "e\<^sup>T * top \<le> -(d\<^sup>T * top)"
    by (metis (no_types) comp_associative inf.cobounded2 le_bot p_antitone_iff schroeder_3_p semiring.mult_zero_left)
  have "?v\<^sup>T * -(d\<^sup>T * top) \<le> -(d\<^sup>T * top)"
    using schroeder_3_p mult_assoc 2 by simp
  hence "?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top \<le> -(d\<^sup>T * top)"
    using 4 by (simp add: comp_associative star_left_induct sup_least)
  hence 5: "d\<^sup>T * top \<le> -(?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top)"
    by (simp add: p_antitone_iff)
  have "w * ?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top = w * e\<^sup>T * top \<squnion> w * ?v\<^sup>T\<^sup>+ * e\<^sup>T * top"
    by (metis star_left_unfold_equal mult_right_dist_sup mult_left_dist_sup mult_1_right mult_assoc)
  also have "... = w * ?v\<^sup>T\<^sup>+ * e\<^sup>T * top"
    using assms(7) by simp
  also have "... \<le> w * w\<^sup>T * ?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top"
    by (simp add: comp_associative conv_isotone mult_left_isotone mult_right_isotone)
  also have "... \<le> ?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top"
    by (metis assms(2) mult_1_left mult_left_isotone)
  finally have "w * ?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top \<le> --(?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top)"
    by (simp add: p_antitone p_antitone_iff)
  hence "w\<^sup>T * -(?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top) \<le> -(?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top)"
    using comp_associative schroeder_3_p by simp
  hence 6: "w\<^sup>T\<^sup>\<star> * d\<^sup>T * top \<le> -(?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top)"
    using 5 by (simp add: comp_associative star_left_induct sup_least)
  have "e * ?v\<^sup>\<star> * e \<le> e * ?v\<^sup>\<star> * e * top"
    by (simp add: top_right_mult_increasing)
  also have "... \<le> e * w\<^sup>T\<^sup>\<star> * d\<^sup>T * top"
    using 3 by (simp add: comp_associative mult_right_isotone)
  also have "... \<le> e * -(?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top)"
    using 6 by (simp add: comp_associative mult_right_isotone)
  also have "... \<le> bot"
    by (metis conv_complement_sub_leq conv_dist_comp conv_involutive conv_star_commute le_bot mult_right_sub_dist_sup_right p_bot regular_closed_bot star.circ_back_loop_fixpoint)
  finally have 7: "e * ?v\<^sup>\<star> * e = bot"
    by (simp add: antisym)
  hence "?v\<^sup>\<star> * e \<le> -1"
    by (metis bot_least comp_associative comp_commute_below_diversity ex231d order_lesseq_imp semiring.mult_zero_left star.circ_left_top)
  hence 8: "?v\<^sup>\<star> * e * ?v\<^sup>\<star> \<le> -1"
    by (metis comp_associative comp_commute_below_diversity star.circ_transitive_equal)
  have "1 \<sqinter> ?w\<^sup>+ = 1 \<sqinter> ?w * ?v\<^sup>\<star> * (e * ?v\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: star_sup_1 mult_assoc)
  also have "... = 1 \<sqinter> ?w * ?v\<^sup>\<star> * (e * ?v\<^sup>\<star> \<squnion> 1)"
    using 7 by (metis star.circ_mult_1 star_absorb sup_monoid.add_commute mult_assoc)
  also have "... = 1 \<sqinter> (?v\<^sup>+ * e * ?v\<^sup>\<star> \<squnion> ?v\<^sup>+ \<squnion> e * ?v\<^sup>\<star> * e * ?v\<^sup>\<star> \<squnion> e * ?v\<^sup>\<star>)"
    by (simp add: comp_associative mult_left_dist_sup mult_right_dist_sup sup_assoc sup_commute sup_left_commute)
  also have "... = 1 \<sqinter> (?v\<^sup>+ * e * ?v\<^sup>\<star> \<squnion> ?v\<^sup>+ \<squnion> e * ?v\<^sup>\<star>)"
    using 7 by simp
  also have "... = 1 \<sqinter> (?v\<^sup>\<star> * e * ?v\<^sup>\<star> \<squnion> ?v\<^sup>+)"
    by (metis (mono_tags, hide_lams) comp_associative star.circ_loop_fixpoint sup_assoc sup_commute)
  also have "... \<le> 1 \<sqinter> (?v\<^sup>\<star> * e * ?v\<^sup>\<star> \<squnion> w\<^sup>+)"
    using comp_inf.mult_right_isotone comp_isotone semiring.add_right_mono star_isotone sup_commute by simp
  also have "... = (1 \<sqinter> ?v\<^sup>\<star> * e * ?v\<^sup>\<star>) \<squnion> (1 \<sqinter> w\<^sup>+)"
    by (simp add: inf_sup_distrib1)
  also have "... = 1 \<sqinter> ?v\<^sup>\<star> * e * ?v\<^sup>\<star>"
    by (metis assms(1) inf_commute pseudo_complement sup_bot_right)
  also have "... = bot"
    using 8 p_antitone_iff pseudo_complement by simp
  finally show ?thesis
    using le_bot p_antitone_iff pseudo_complement by auto
qed

subsubsection \<open>Exchange gives Spanning Trees\<close>

text \<open>
The lemmas in this section are used to show that the relation after exchange represents a spanning tree.
\<close>

lemma inf_star_import:
  assumes "x \<le> z"
      and "univalent z"
      and "reflexive y"
      and "regular z"
    shows "x\<^sup>\<star> * y \<sqinter> z\<^sup>\<star> \<le> x\<^sup>\<star> * (y \<sqinter> z\<^sup>\<star>)"
proof -
  have 1: "y \<le> x\<^sup>\<star> * (y \<sqinter> z\<^sup>\<star>) \<squnion> -z\<^sup>\<star>"
    by (metis assms(4) pp_dist_star shunting_var_p star.circ_loop_fixpoint sup.cobounded2)
  have "x * -z\<^sup>\<star> \<sqinter> z\<^sup>+ \<le> x * (-z\<^sup>\<star> \<sqinter> x\<^sup>T * z\<^sup>+)"
    by (simp add: dedekind_1)
  also have "... \<le> x * (-z\<^sup>\<star> \<sqinter> z\<^sup>T * z\<^sup>+)"
    using assms(1) comp_inf.mult_right_isotone conv_isotone mult_left_isotone mult_right_isotone by simp
  also have "... \<le> x * (-z\<^sup>\<star> \<sqinter> 1 * z\<^sup>\<star>)"
    by (metis assms(2) comp_associative comp_inf.mult_right_isotone mult_left_isotone mult_right_isotone)
  finally have 2: "x * -z\<^sup>\<star> \<sqinter> z\<^sup>+ = bot"
    by (simp add: antisym)
  have "x * -z\<^sup>\<star> \<sqinter> z\<^sup>\<star> = (x * -z\<^sup>\<star> \<sqinter> z\<^sup>+) \<squnion> (x * -z\<^sup>\<star> \<sqinter> 1)"
    by (metis comp_inf.semiring.distrib_left star_left_unfold_equal sup_commute)
  also have "... \<le> x\<^sup>\<star> * (y \<sqinter> z\<^sup>\<star>)"
    using 2 by (simp add: assms(3) inf.coboundedI2 reflexive_mult_closed star.circ_reflexive)
  finally have "x * -z\<^sup>\<star> \<le> x\<^sup>\<star> * (y \<sqinter> z\<^sup>\<star>) \<squnion> -z\<^sup>\<star>"
    by (metis assms(4) pp_dist_star shunting_var_p)
  hence "x * (x\<^sup>\<star> * (y \<sqinter> z\<^sup>\<star>) \<squnion> -z\<^sup>\<star>) \<le> x\<^sup>\<star> * (y \<sqinter> z\<^sup>\<star>) \<squnion> -z\<^sup>\<star>"
    by (metis le_supE le_supI mult_left_dist_sup star.circ_loop_fixpoint sup.cobounded1)
  hence "x\<^sup>\<star> * y \<le> x\<^sup>\<star> * (y \<sqinter> z\<^sup>\<star>) \<squnion> -z\<^sup>\<star>"
    using 1 by (simp add: star_left_induct)
  hence "x\<^sup>\<star> * y \<sqinter> --z\<^sup>\<star> \<le> x\<^sup>\<star> * (y \<sqinter> z\<^sup>\<star>)"
    using shunting_var_p by simp
  thus ?thesis
    using order.trans inf.sup_right_isotone pp_increasing by blast
qed

lemma kruskal_exchange_forest_components_inv:
  assumes "injective ((w \<sqinter> -d) \<squnion> e)"
      and "regular d"
      and "e * top * e = e"
      and "d \<le> top * e\<^sup>T * w\<^sup>T\<^sup>\<star>"
      and "w * e\<^sup>T * top = bot"
      and "injective w"
      and "d \<le> w"
      and "d \<le> (w \<sqinter> -d)\<^sup>T\<^sup>\<star> * e\<^sup>T * top"
    shows "forest_components w \<le> forest_components ((w \<sqinter> -d) \<squnion> e)"
proof -
  let ?v = "w \<sqinter> -d"
  let ?w = "?v \<squnion> e"
  let ?f = "forest_components ?w"
  have 1: "?v * d\<^sup>T * top = bot"
    by (simp add: assms(6,7) kruskal_exchange_acyclic_inv_3)
  have 2: "d * e\<^sup>T \<le> bot"
    by (metis assms(5,7) conv_bot conv_dist_comp conv_involutive conv_top order.trans inf.absorb2 inf.cobounded2 inf_commute le_bot p_antitone_iff p_top schroeder_4_p top_left_mult_increasing)
  have "w\<^sup>\<star> * e\<^sup>T * top = e\<^sup>T * top"
    by (metis assms(5) conv_bot conv_dist_comp conv_involutive conv_star_commute star.circ_top star_absorb)
  hence "w\<^sup>\<star> * e\<^sup>T * top \<le> -(d\<^sup>T * top)"
    using 2 by (metis (no_types) comp_associative inf.cobounded2 le_bot p_antitone_iff schroeder_3_p semiring.mult_zero_left)
  hence 3: "e\<^sup>T * top \<le> -(w\<^sup>T\<^sup>\<star> * d\<^sup>T * top)"
    by (metis conv_star_commute p_antitone_iff schroeder_3_p mult_assoc)
  have "?v * w\<^sup>T\<^sup>\<star> * d\<^sup>T * top = ?v * d\<^sup>T * top \<squnion> ?v * w\<^sup>T\<^sup>+ * d\<^sup>T * top"
    by (metis comp_associative mult_left_dist_sup star.circ_loop_fixpoint sup_commute)
  also have "... \<le> w * w\<^sup>T\<^sup>+ * d\<^sup>T * top"
    using 1 by (simp add: mult_left_isotone)
  also have "... \<le> w\<^sup>T\<^sup>\<star> * d\<^sup>T * top"
    by (metis assms(6) mult_assoc mult_1_left mult_left_isotone)
  finally have "?v * w\<^sup>T\<^sup>\<star> * d\<^sup>T * top \<le> --(w\<^sup>T\<^sup>\<star> * d\<^sup>T * top)"
    using p_antitone p_antitone_iff by auto
  hence 4: "?v\<^sup>T * -(w\<^sup>T\<^sup>\<star> * d\<^sup>T * top) \<le> -(w\<^sup>T\<^sup>\<star> * d\<^sup>T * top)"
    using comp_associative schroeder_3_p by simp
  have 5: "injective ?v"
    using assms(1) conv_dist_sup mult_left_dist_sup mult_right_dist_sup by simp
  have "?v * ?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top = ?v * e\<^sup>T * top \<squnion> ?v * ?v\<^sup>T\<^sup>+ * e\<^sup>T * top"
    by (metis comp_associative mult_left_dist_sup star.circ_loop_fixpoint sup_commute)
  also have "... \<le> w * e\<^sup>T * top \<squnion> ?v * ?v\<^sup>T\<^sup>+ * e\<^sup>T * top"
    using mult_left_isotone sup_left_isotone by simp
  also have "... \<le> w * e\<^sup>T * top \<squnion> ?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top"
    using 5 by (metis mult_assoc mult_1_left mult_left_isotone sup_right_isotone)
  finally have "?v * ?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top \<le> ?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top"
    by (simp add: assms(5))
  hence "?v\<^sup>\<star> * d * top \<le> ?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top"
    by (metis assms(8) star_left_induct sup_least comp_associative mult_right_sub_dist_sup_right sup.orderE vector_top_closed)
  also have "... \<le> -(w\<^sup>T\<^sup>\<star> * d\<^sup>T * top)"
    using 3 4 by (simp add: comp_associative star_left_induct)
  also have "... \<le> -(d\<^sup>T * top)"
    by (metis p_antitone star.circ_left_top star_outer_increasing mult_assoc)
  finally have 6: "?v\<^sup>\<star> * d * top \<le> -(d\<^sup>T * top)"
    by simp
  have "d\<^sup>T * top \<le> w\<^sup>\<star> * e * top"
    by (metis assms(4) comp_associative comp_inf.star.circ_sup_2 comp_isotone conv_dist_comp conv_involutive conv_order conv_star_commute conv_top vector_top_closed)
  also have "... \<le> (?v \<squnion> d)\<^sup>\<star> * e * top"
    by (metis assms(2) comp_inf.semiring.distrib_left maddux_3_11_pp mult_left_isotone star_isotone sup.cobounded2 sup_commute sup_inf_distrib1)
  also have "... = ?v\<^sup>\<star> * (d * ?v\<^sup>\<star>)\<^sup>\<star> * e * top"
    by (simp add: star_sup_1)
  also have "... = ?v\<^sup>\<star> * e * top \<squnion> ?v\<^sup>\<star> * d * ?v\<^sup>\<star> * (d * ?v\<^sup>\<star>)\<^sup>\<star> * e * top"
    by (metis semiring.distrib_right star.circ_unfold_sum star_decompose_1 star_decompose_3 mult_assoc)
  also have "... \<le> ?v\<^sup>\<star> * e * top \<squnion> ?v\<^sup>\<star> * d * top"
    by (metis comp_associative comp_isotone le_supI mult_left_dist_sup mult_right_dist_sup mult_right_isotone star.circ_decompose_5 star_decompose_3 sup.cobounded1 sup_commute top.extremum)
  finally have "d\<^sup>T * top \<le> ?v\<^sup>\<star> * e * top \<squnion> (d\<^sup>T * top \<sqinter> ?v\<^sup>\<star> * d * top)"
    using sup_inf_distrib2 sup_monoid.add_commute by simp
  hence "d\<^sup>T * top \<le> ?v\<^sup>\<star> * e * top"
    using 6 by (metis inf_commute pseudo_complement sup_monoid.add_0_right)
  hence 7: "d \<le> top * e\<^sup>T * ?v\<^sup>T\<^sup>\<star>"
    by (metis comp_associative conv_dist_comp conv_involutive conv_isotone conv_star_commute conv_top order.trans top_right_mult_increasing)
  have 8: "?v \<le> ?f"
    using forest_components_increasing le_supE by blast
  have "d \<le> ?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top \<sqinter> top * e\<^sup>T * ?v\<^sup>T\<^sup>\<star>"
    using 7 assms(8) by simp
  also have "... = ?v\<^sup>T\<^sup>\<star> * e\<^sup>T * top * e\<^sup>T * ?v\<^sup>T\<^sup>\<star>"
    by (metis inf_top_right vector_inf_comp vector_top_closed mult_assoc)
  also have "... = ?v\<^sup>T\<^sup>\<star> * e\<^sup>T * ?v\<^sup>T\<^sup>\<star>"
    by (metis assms(3) comp_associative conv_dist_comp conv_top)
  also have "... \<le> ?v\<^sup>T\<^sup>\<star> * e\<^sup>T * ?f"
    using 8 by (metis assms(1) forest_components_equivalence cancel_separate_1 conv_dist_comp conv_order mult_left_isotone star_involutive star_isotone)
  also have "... \<le> ?v\<^sup>T\<^sup>\<star> * ?f * ?f"
    by (metis assms(1) forest_components_equivalence forest_components_increasing conv_isotone le_supE mult_left_isotone mult_right_isotone)
  also have "... \<le> ?f * ?f * ?f"
    by (metis comp_associative comp_isotone conv_dist_sup star.circ_loop_fixpoint star_isotone sup.cobounded1 sup.cobounded2)
  also have "... = ?f"
    by (simp add: assms(1) forest_components_equivalence preorder_idempotent)
  finally have "w \<le> ?f"
    using 8 by (metis assms(2) shunting_var_p sup.orderE)
  thus ?thesis
    using assms(1) forest_components_idempotent forest_components_isotone by fastforce
qed

lemma kruskal_spanning_inv:
  assumes "injective ((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T \<squnion> e)"
      and "regular q"
      and "regular e"
      and "(-h \<sqinter> --g)\<^sup>\<star> \<le> forest_components f"
    shows "components (-(h \<sqinter> -e \<sqinter> -e\<^sup>T) \<sqinter> g) \<le> forest_components ((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T \<squnion> e)"
proof -
  let ?f = "(f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T \<squnion> e"
  let ?h = "h \<sqinter> -e \<sqinter> -e\<^sup>T"
  let ?F = "forest_components f"
  let ?FF = "forest_components ?f"
  have 1: "equivalence ?FF"
    using assms(1) forest_components_equivalence by simp
  hence 2: "?f * ?FF \<le> ?FF"
    using order.trans forest_components_increasing mult_left_isotone by blast
  have 3: "?f\<^sup>T * ?FF \<le> ?FF"
    using 1 by (metis forest_components_increasing mult_left_isotone conv_isotone preorder_idempotent)
  have "(f \<sqinter> q) * ?FF \<le> ?f\<^sup>T * ?FF"
    using conv_dist_sup conv_involutive sup_assoc sup_left_commute mult_left_isotone by simp
  hence 4: "(f \<sqinter> q) * ?FF \<le> ?FF"
    using 3 order.trans by blast
  have "(f \<sqinter> -q) * ?FF \<le> ?f * ?FF"
    using le_supI1 mult_left_isotone by simp
  hence "(f \<sqinter> -q) * ?FF \<le> ?FF"
    using 2 order.trans by blast
  hence "((f \<sqinter> q) \<squnion> (f \<sqinter> -q)) * ?FF \<le> ?FF"
    using 4 mult_right_dist_sup by simp
  hence "f * ?FF \<le> ?FF"
    by (metis assms(2) maddux_3_11_pp)
  hence 5: "f\<^sup>\<star> * ?FF \<le> ?FF"
    using star_left_induct_mult_iff by simp
  have "(f \<sqinter> -q)\<^sup>T * ?FF \<le> ?f\<^sup>T * ?FF"
    by (meson conv_isotone order.trans mult_left_isotone sup.cobounded1)
  hence 6: "(f \<sqinter> -q)\<^sup>T * ?FF \<le> ?FF"
    using 3 order.trans by blast
  have "(f \<sqinter> q)\<^sup>T * ?FF \<le> ?f * ?FF"
    by (simp add: mult_left_isotone sup.left_commute sup_assoc)
  hence "(f \<sqinter> q)\<^sup>T * ?FF \<le> ?FF"
    using 2 order.trans by blast
  hence "((f \<sqinter> -q)\<^sup>T \<squnion> (f \<sqinter> q)\<^sup>T) * ?FF \<le> ?FF"
    using 6 mult_right_dist_sup by simp
  hence "f\<^sup>T * ?FF \<le> ?FF"
    by (metis assms(2) conv_dist_sup maddux_3_11_pp)
  hence 7: "?F * ?FF \<le> ?FF"
    using 5 star_left_induct mult_assoc by simp
  have 8: "e * ?FF \<le> ?FF"
    using 2 by (simp add: mult_right_dist_sup mult_left_isotone)
  have "e\<^sup>T * ?FF \<le> ?f\<^sup>T * ?FF"
    by (simp add: mult_left_isotone conv_isotone)
  also have "... \<le> ?FF * ?FF"
    using 1 by (metis forest_components_increasing mult_left_isotone conv_isotone)
  finally have "e\<^sup>T * ?FF \<le> ?FF"
    using 1 preorder_idempotent by auto
  hence 9: "(?F \<squnion> e \<squnion> e\<^sup>T) * ?FF \<le> ?FF"
    using 7 8 mult_right_dist_sup by simp
  have "components (-?h \<sqinter> g) \<le> ((-h \<sqinter> --g) \<squnion> e \<squnion> e\<^sup>T)\<^sup>\<star>"
    by (metis assms(3) comp_inf.mult_left_sub_dist_sup_left conv_complement p_dist_inf pp_dist_inf regular_closed_p star_isotone sup_inf_distrib2 sup_monoid.add_assoc)
  also have "... \<le> ((-h \<sqinter> --g)\<^sup>\<star> \<squnion> e \<squnion> e\<^sup>T)\<^sup>\<star>"
    using star.circ_increasing star_isotone sup_left_isotone by simp
  also have "... \<le> (?F \<squnion> e \<squnion> e\<^sup>T)\<^sup>\<star>"
    using assms(4) sup_left_isotone star_isotone by simp
  also have "... \<le> ?FF"
    using 1 9 star_left_induct by force
  finally show ?thesis
    by simp
qed

lemma kruskal_exchange_spanning_inv_1:
  assumes "injective ((w \<sqinter> -q) \<squnion> (w \<sqinter> q)\<^sup>T)"
      and "regular (w \<sqinter> q)"
      and "components g \<le> forest_components w"
    shows "components g \<le> forest_components ((w \<sqinter> -q) \<squnion> (w \<sqinter> q)\<^sup>T)"
proof -
  let ?p = "w \<sqinter> q"
  let ?w = "(w \<sqinter> -q) \<squnion> ?p\<^sup>T"
  have 1: "w \<sqinter> -?p \<le> forest_components ?w"
    by (metis forest_components_increasing inf_import_p le_supE)
  have "w \<sqinter> ?p \<le> ?w\<^sup>T"
    by (simp add: conv_dist_sup)
  also have "... \<le> forest_components ?w"
    by (metis assms(1) conv_isotone forest_components_equivalence forest_components_increasing)
  finally have "w \<sqinter> (?p \<squnion> -?p) \<le> forest_components ?w"
    using 1 inf_sup_distrib1 by simp
  hence "w \<le> forest_components ?w"
    by (metis assms(2) inf_top_right stone)
  hence 2: "w\<^sup>\<star> \<le> forest_components ?w"
    using assms(1) star_isotone forest_components_star by force
  hence 3: "w\<^sup>T\<^sup>\<star> \<le> forest_components ?w"
    using assms(1) conv_isotone conv_star_commute forest_components_equivalence by force
  have "components g \<le> forest_components w"
    using assms(3) by simp
  also have "... \<le> forest_components ?w * forest_components ?w"
    using 2 3 mult_isotone by simp
  also have "... = forest_components ?w"
    using assms(1) forest_components_equivalence preorder_idempotent by simp
  finally show ?thesis
    by simp
qed

lemma kruskal_exchange_spanning_inv_2:
  assumes "injective w"
      and "w\<^sup>\<star> * e\<^sup>T = e\<^sup>T"
      and "f \<squnion> f\<^sup>T \<le> (w \<sqinter> -d \<sqinter> -d\<^sup>T) \<squnion> (w\<^sup>T \<sqinter> -d \<sqinter> -d\<^sup>T)"
      and "d \<le> forest_components f * e\<^sup>T * top"
    shows "d \<le> (w \<sqinter> -d)\<^sup>T\<^sup>\<star> * e\<^sup>T * top"
proof -
  have 1: "(w \<sqinter> -d \<sqinter> -d\<^sup>T) * (w\<^sup>T \<sqinter> -d \<sqinter> -d\<^sup>T) \<le> 1"
    using assms(1) comp_isotone order.trans inf.cobounded1 by blast
  have "d \<le> forest_components f * e\<^sup>T * top"
    using assms(4) by simp
  also have "... \<le> (f \<squnion> f\<^sup>T)\<^sup>\<star> * (f \<squnion> f\<^sup>T)\<^sup>\<star> * e\<^sup>T * top"
    by (simp add: comp_isotone star_isotone)
  also have "... = (f \<squnion> f\<^sup>T)\<^sup>\<star> * e\<^sup>T * top"
    by (simp add: star.circ_transitive_equal)
  also have "... \<le> ((w \<sqinter> -d \<sqinter> -d\<^sup>T) \<squnion> (w\<^sup>T \<sqinter> -d \<sqinter> -d\<^sup>T))\<^sup>\<star> * e\<^sup>T * top"
    using assms(3) by (simp add: comp_isotone star_isotone)
  also have "... = (w\<^sup>T \<sqinter> -d \<sqinter> -d\<^sup>T)\<^sup>\<star> * (w \<sqinter> -d \<sqinter> -d\<^sup>T)\<^sup>\<star> * e\<^sup>T * top"
    using 1 cancel_separate_1 by simp
  also have "... \<le> (w\<^sup>T \<sqinter> -d \<sqinter> -d\<^sup>T)\<^sup>\<star> * w\<^sup>\<star> * e\<^sup>T * top"
    by (simp add: inf_assoc mult_left_isotone mult_right_isotone star_isotone)
  also have "... = (w\<^sup>T \<sqinter> -d \<sqinter> -d\<^sup>T)\<^sup>\<star> * e\<^sup>T * top"
    using assms(2) mult_assoc by simp
  also have "... \<le> (w\<^sup>T \<sqinter> -d\<^sup>T)\<^sup>\<star> * e\<^sup>T * top"
    using mult_left_isotone conv_isotone star_isotone comp_inf.mult_right_isotone inf.cobounded2 inf.left_commute inf.sup_monoid.add_commute by presburger
  also have "... = (w \<sqinter> -d)\<^sup>T\<^sup>\<star> * e\<^sup>T * top"
    using conv_complement conv_dist_inf by presburger
  finally show ?thesis
    by simp
qed

lemma kruskal_spanning_inv_1:
  assumes "e \<le> F"
      and "regular e"
      and "components (-h \<sqinter> g) \<le> F"
      and "equivalence F"
    shows "components (-(h \<sqinter> -e \<sqinter> -e\<^sup>T) \<sqinter> g) \<le> F"
proof -
  have 1: "F * F \<le> F"
    using assms(4) by simp
  hence 2: "e * F \<le> F"
    using assms(1) mult_left_isotone order_lesseq_imp by blast
  have "e\<^sup>T * F \<le> F"
    by (metis assms(1,4) conv_isotone mult_left_isotone preorder_idempotent)
  hence 3: "(F \<squnion> e \<squnion> e\<^sup>T) * F \<le> F"
    using 1 2 mult_right_dist_sup by simp
  have "components (-(h \<sqinter> -e \<sqinter> -e\<^sup>T) \<sqinter> g) \<le> ((-h \<sqinter> --g) \<squnion> e \<squnion> e\<^sup>T)\<^sup>\<star>"
    by (metis assms(2) comp_inf.mult_left_sub_dist_sup_left conv_complement p_dist_inf pp_dist_inf regular_closed_p star_isotone sup_inf_distrib2 sup_monoid.add_assoc)
  also have "... \<le> ((-h \<sqinter> --g)\<^sup>\<star> \<squnion> e \<squnion> e\<^sup>T)\<^sup>\<star>"
    using sup_left_isotone star.circ_increasing star_isotone by simp
  also have "... \<le> (F \<squnion> e \<squnion> e\<^sup>T)\<^sup>\<star>"
    using assms(3) sup_left_isotone star_isotone by simp
  also have "... \<le> F"
    using 3 assms(4) star_left_induct by force
  finally show ?thesis
    by simp
qed

lemma kruskal_reroot_edge:
  assumes "injective (e\<^sup>T * top)"
      and "acyclic w"
    shows "((w \<sqinter> -(top * e * w\<^sup>T\<^sup>\<star>)) \<squnion> (w \<sqinter> top * e * w\<^sup>T\<^sup>\<star>)\<^sup>T) * e\<^sup>T = bot"
proof -
  let ?q = "top * e * w\<^sup>T\<^sup>\<star>"
  let ?p = "w \<sqinter> ?q"
  let ?w = "(w \<sqinter> -?q) \<squnion> ?p\<^sup>T"
  have "(w \<sqinter> -?q) * e\<^sup>T * top = w * (e\<^sup>T * top \<sqinter> -?q\<^sup>T)"
    by (metis comp_associative comp_inf_vector_1 conv_complement covector_complement_closed vector_top_closed)
  also have "... = w * (e\<^sup>T * top \<sqinter> -(w\<^sup>\<star> * e\<^sup>T * top))"
    by (simp add: conv_dist_comp conv_star_commute mult_assoc)
  also have "... = bot"
    by (metis comp_associative comp_inf.semiring.mult_not_zero inf.sup_relative_same_increasing inf_p mult_right_zero star.circ_loop_fixpoint sup_commute sup_left_divisibility)
  finally have 1: "(w \<sqinter> -?q) * e\<^sup>T * top = bot"
    by simp
  have "?p\<^sup>T * e\<^sup>T * top = (w\<^sup>T \<sqinter> w\<^sup>\<star> * e\<^sup>T * top) * e\<^sup>T * top"
    by (simp add: conv_dist_comp conv_star_commute mult_assoc conv_dist_inf)
  also have "... = w\<^sup>\<star> * e\<^sup>T * top \<sqinter> w\<^sup>T * e\<^sup>T * top"
    by (simp add: inf_vector_comp vector_export_comp)
  also have "... = (w\<^sup>\<star> \<sqinter> w\<^sup>T) * e\<^sup>T * top"
    using assms(1) injective_comp_right_dist_inf mult_assoc by simp
  also have "... = bot"
    using assms(2) acyclic_star_below_complement_1 semiring.mult_not_zero by blast
  finally have "?w * e\<^sup>T * top = bot"
    using 1 mult_right_dist_sup by simp
  thus ?thesis
    by (metis star.circ_top star_absorb)
qed

subsubsection \<open>Exchange gives Minimum Spanning Trees\<close>

text \<open>
The lemmas in this section are used to show that the after exchange we obtain a minimum spanning tree.
The following lemmas show that the relation characterising the edge across the cut is an arc.
\<close>

lemma kruskal_edge_arc:
  assumes "equivalence F"
      and "forest w"
      and "arc e"
      and "regular F"
      and "F \<le> forest_components (F \<sqinter> w)"
      and "regular w"
      and "w * e\<^sup>T = bot"
      and "e * F * e = bot"
      and "e\<^sup>T \<le> w\<^sup>\<star>"
    shows "arc (w \<sqinter> top * e\<^sup>T * w\<^sup>T\<^sup>\<star> \<sqinter> F * e\<^sup>T * top \<sqinter> top * e * -F)"
proof (unfold arc_expanded, intro conjI)
  let ?E = "top * e\<^sup>T * w\<^sup>T\<^sup>\<star>"
  let ?F = "F * e\<^sup>T * top"
  let ?G = "top * e * -F"
  let ?FF = "F * e\<^sup>T * e * F"
  let ?GG = "-F * e\<^sup>T * e * -F"
  let ?w = "forest_components (F \<sqinter> w)"
  have "F \<sqinter> w\<^sup>T\<^sup>\<star> \<le> forest_components (F \<sqinter> w) \<sqinter> w\<^sup>T\<^sup>\<star>"
    by (simp add: assms(5) inf.coboundedI1)
  also have "... \<le> (F \<sqinter> w)\<^sup>T\<^sup>\<star> * ((F \<sqinter> w)\<^sup>\<star> \<sqinter> w\<^sup>T\<^sup>\<star>)"
    apply (rule inf_star_import)
    apply (simp add: conv_isotone)
    apply (simp add: assms(2))
    apply (simp add: star.circ_reflexive)
    by (metis assms(6) conv_complement)
  also have "... \<le> (F \<sqinter> w)\<^sup>T\<^sup>\<star> * (w\<^sup>\<star> \<sqinter> w\<^sup>T\<^sup>\<star>)"
    using comp_inf.mult_left_isotone mult_right_isotone star_isotone by simp
  also have "... = (F \<sqinter> w)\<^sup>T\<^sup>\<star>"
    by (simp add: assms(2) acyclic_star_inf_conv)
  finally have "w * (F \<sqinter> w\<^sup>T\<^sup>\<star>) * e\<^sup>T * e \<le> w * (F \<sqinter> w)\<^sup>T\<^sup>\<star> * e\<^sup>T * e"
    by (simp add: mult_left_isotone mult_right_isotone)
  also have "... = w * e\<^sup>T * e \<squnion> w * (F \<sqinter> w)\<^sup>T\<^sup>+ * e\<^sup>T * e"
    by (metis comp_associative mult_left_dist_sup star.circ_loop_fixpoint sup_commute)
  also have "... = w * (F \<sqinter> w)\<^sup>T\<^sup>+ * e\<^sup>T * e"
    by (simp add: assms(7))
  also have "... \<le> w * (F \<sqinter> w)\<^sup>T\<^sup>+"
    by (metis assms(3) arc_univalent mult_assoc mult_1_right mult_right_isotone)
  also have "... \<le> w * w\<^sup>T * (F \<sqinter> w)\<^sup>T\<^sup>\<star>"
    by (simp add: comp_associative conv_isotone mult_left_isotone mult_right_isotone)
  also have "... \<le> (F \<sqinter> w)\<^sup>T\<^sup>\<star>"
    using assms(2) coreflexive_comp_top_inf inf.sup_right_divisibility by auto
  also have "... \<le> F\<^sup>T\<^sup>\<star>"
    by (simp add: conv_dist_inf star_isotone)
  finally have 1: "w * (F \<sqinter> w\<^sup>T\<^sup>\<star>) * e\<^sup>T * e \<le> F"
    by (metis assms(1) antisym mult_1_left mult_left_isotone star.circ_plus_same star.circ_reflexive star.left_plus_below_circ star_left_induct_mult_iff)
  have "F * e\<^sup>T * e \<le> forest_components (F \<sqinter> w) * e\<^sup>T * e"
    by (simp add: assms(5) mult_left_isotone)
  also have "... \<le> forest_components w * e\<^sup>T * e"
    by (simp add: comp_isotone conv_dist_inf star_isotone)
  also have "... = w\<^sup>T\<^sup>\<star> * e\<^sup>T * e"
    by (metis (no_types) assms(7) comp_associative conv_bot conv_dist_comp conv_involutive conv_star_commute star_absorb)
  also have "... \<le> w\<^sup>T\<^sup>\<star>"
    by (metis assms(3) arc_univalent mult_assoc mult_1_right mult_right_isotone)
  finally have 2: "F * e\<^sup>T * e \<le> w\<^sup>T\<^sup>\<star>"
    by simp
  have "w * F * e\<^sup>T * e \<le> w * F * e\<^sup>T * e * e\<^sup>T * e"
    using comp_associative ex231c mult_right_isotone by simp
  also have "... = w * (F * e\<^sup>T * e \<sqinter> w\<^sup>T\<^sup>\<star>) * e\<^sup>T * e"
    using 2 by (simp add: comp_associative inf.absorb1)
  also have "... \<le> w * (F \<sqinter> w\<^sup>T\<^sup>\<star>) * e\<^sup>T * e"
    by (metis assms(3) arc_univalent mult_assoc mult_1_right mult_right_isotone mult_left_isotone inf.sup_left_isotone)
  also have "... \<le> F"
    using 1 by simp
  finally have 3: "w * F * e\<^sup>T * e \<le> F"
    by simp
  hence "e\<^sup>T * e * F * w\<^sup>T \<le> F"
    by (metis assms(1) conv_dist_comp conv_dist_inf conv_involutive inf.absorb_iff1 mult_assoc)
  hence "e\<^sup>T * e * F * w\<^sup>T \<le> e\<^sup>T * top \<sqinter> F"
    by (simp add: comp_associative mult_right_isotone)
  also have "... \<le> e\<^sup>T * e * F"
    by (metis conv_involutive dedekind_1 inf_top_left mult_assoc)
  finally have 4: "e\<^sup>T * e * F * w\<^sup>T \<le> e\<^sup>T * e * F"
    by simp
  have "(top * e)\<^sup>T * (?F \<sqinter> w\<^sup>T\<^sup>\<star>) = e\<^sup>T * top * e * F * w\<^sup>T\<^sup>\<star>"
    by (metis assms(1) comp_inf.star.circ_decompose_9 comp_inf.star_star_absorb conv_dist_comp conv_involutive conv_top covector_inf_comp_3 vector_top_closed mult_assoc)
  also have "... = e\<^sup>T * e * F * w\<^sup>T\<^sup>\<star>"
    by (simp add: assms(3) arc_top_edge)
  also have "... \<le> e\<^sup>T * e * F"
    using 4 star_right_induct_mult by simp
  also have "... \<le> F"
    by (metis assms(3) arc_injective conv_involutive mult_1_left mult_left_isotone)
  finally have 5: "(top * e)\<^sup>T * (?F \<sqinter> w\<^sup>T\<^sup>\<star>) \<le> F"
    by simp
  have "(?F \<sqinter> w) * w\<^sup>T\<^sup>+ = ?F \<sqinter> w * w\<^sup>T\<^sup>+"
    by (simp add: vector_export_comp)
  also have "... \<le> ?F \<sqinter> w\<^sup>T\<^sup>\<star>"
    by (metis assms(2) comp_associative inf.sup_right_isotone mult_left_isotone star.circ_transitive_equal star_left_unfold_equal sup.absorb_iff2 sup_monoid.add_assoc)
  also have 6: "... \<le> top * e * F"
    using 5 by (metis assms(3) shunt_mapping conv_dist_comp conv_involutive conv_top)
  finally have 7: "(?F \<sqinter> w) * w\<^sup>T\<^sup>+ \<le> top * e * F"
    by simp
  have "e\<^sup>T * top * e \<le> 1"
    by (simp add: assms(3) point_injective)
  also have "... \<le> F"
    by (simp add: assms(1))
  finally have 8: "e * -F * e\<^sup>T \<le> bot"
    by (metis p_antitone p_antitone_iff p_bot regular_closed_bot schroeder_3_p schroeder_4_p mult_assoc)
  have "?FF \<sqinter> w * (w\<^sup>T\<^sup>+ \<sqinter> ?GG) * w\<^sup>T \<le> ?F \<sqinter> w * (w\<^sup>T\<^sup>+ \<sqinter> ?GG) * w\<^sup>T"
    using comp_inf.mult_left_isotone mult_isotone mult_assoc by simp
  also have "... \<le> ?F \<sqinter> w * (w\<^sup>T\<^sup>+ \<sqinter> ?G) * w\<^sup>T"
    by (metis assms(3) arc_top_edge comp_inf.star.circ_decompose_9 comp_inf_covector inf.sup_right_isotone inf_le2 mult_left_isotone mult_right_isotone vector_top_closed mult_assoc)
  also have "... = (?F \<sqinter> w) * (w\<^sup>T\<^sup>+ \<sqinter> ?G) * w\<^sup>T"
    by (simp add: vector_export_comp)
  also have "... = (?F \<sqinter> w) * w\<^sup>T\<^sup>+ * (?G\<^sup>T \<sqinter> w\<^sup>T)"
    by (simp add: covector_comp_inf covector_comp_inf_1 covector_mult_closed)
  also have "... \<le> top * e * F * (?G\<^sup>T \<sqinter> w\<^sup>T)"
    using 7 mult_left_isotone by simp
  also have "... \<le> top * e * F * ?G\<^sup>T"
    by (simp add: mult_right_isotone)
  also have "... = top * e * -F * e\<^sup>T * top"
    by (metis assms(1) conv_complement conv_dist_comp conv_top equivalence_comp_left_complement mult_assoc)
  finally have 9: "?FF \<sqinter> w * (w\<^sup>T\<^sup>+ \<sqinter> ?GG) * w\<^sup>T = bot"
    using 8 by (metis comp_associative covector_bot_closed le_bot vector_bot_closed)
  hence 10: "?FF \<sqinter> w * (w\<^sup>+ \<sqinter> ?GG) * w\<^sup>T = bot"
    using assms(1) comp_associative conv_bot conv_complement conv_dist_comp conv_dist_inf conv_star_commute star.circ_plus_same by fastforce
  have "(w \<sqinter> ?E \<sqinter> ?F \<sqinter> ?G) * top * (w \<sqinter> ?E \<sqinter> ?F \<sqinter> ?G)\<^sup>T = (?F \<sqinter> (w \<sqinter> ?E \<sqinter> ?G)) * top * ((w \<sqinter> ?E \<sqinter> ?G)\<^sup>T \<sqinter> ?F\<^sup>T)"
    by (simp add: conv_dist_inf inf_commute inf_left_commute)
  also have "... = (?F \<sqinter> (w \<sqinter> ?E \<sqinter> ?G)) * top * (w \<sqinter> ?E \<sqinter> ?G)\<^sup>T \<sqinter> ?F\<^sup>T"
    using covector_comp_inf vector_conv_covector vector_mult_closed vector_top_closed by simp
  also have "... = ?F \<sqinter> (w \<sqinter> ?E \<sqinter> ?G) * top * (w \<sqinter> ?E \<sqinter> ?G)\<^sup>T \<sqinter> ?F\<^sup>T"
    by (simp add: vector_export_comp)
  also have "... = ?F \<sqinter> top * e * F \<sqinter> (w \<sqinter> ?E \<sqinter> ?G) * top * (w \<sqinter> ?E \<sqinter> ?G)\<^sup>T"
    by (simp add: assms(1) conv_dist_comp inf_assoc inf_commute mult_assoc)
  also have "... = ?F * e * F \<sqinter> (w \<sqinter> ?E \<sqinter> ?G) * top * (w \<sqinter> ?E \<sqinter> ?G)\<^sup>T"
    by (metis comp_associative comp_inf_covector inf_top.left_neutral)
  also have "... = ?FF \<sqinter> (w \<sqinter> ?E \<sqinter> ?G) * (top * (w \<sqinter> ?E \<sqinter> ?G)\<^sup>T)"
    using assms(3) arc_top_edge comp_associative by simp
  also have "... = ?FF \<sqinter> (w \<sqinter> ?E \<sqinter> ?G) * (top * (?G\<^sup>T \<sqinter> (?E\<^sup>T \<sqinter> w\<^sup>T)))"
    by (simp add: conv_dist_inf inf_assoc inf_commute inf_left_commute)
  also have "... = ?FF \<sqinter> (w \<sqinter> ?E \<sqinter> ?G) * (?G * (?E\<^sup>T \<sqinter> w\<^sup>T))"
    by (metis covector_comp_inf_1 covector_top_closed covector_mult_closed inf_top_left)
  also have "... = ?FF \<sqinter> (w \<sqinter> ?E \<sqinter> ?G) * (?G \<sqinter> ?E) * w\<^sup>T"
    by (metis covector_comp_inf_1 covector_top_closed mult_assoc)
  also have "... = ?FF \<sqinter> (w \<sqinter> ?E) * (?G\<^sup>T \<sqinter> ?G \<sqinter> ?E) * w\<^sup>T"
    by (metis covector_comp_inf_1 covector_mult_closed inf.sup_monoid.add_assoc vector_top_closed)
  also have "... = ?FF \<sqinter> w * (?E\<^sup>T \<sqinter> ?G\<^sup>T \<sqinter> ?G \<sqinter> ?E) * w\<^sup>T"
    by (metis covector_comp_inf_1 covector_mult_closed inf.sup_monoid.add_assoc vector_top_closed)
  also have "... = ?FF \<sqinter> w * (?E\<^sup>T \<sqinter> ?E \<sqinter> (?G\<^sup>T \<sqinter> ?G)) * w\<^sup>T"
    by (simp add: inf_commute inf_left_commute)
  also have "... = ?FF \<sqinter> w * (?E\<^sup>T \<sqinter> ?E \<sqinter> (-F * e\<^sup>T * top \<sqinter> ?G)) * w\<^sup>T"
    by (simp add: assms(1) conv_complement conv_dist_comp mult_assoc)
  also have "... = ?FF \<sqinter> w * (?E\<^sup>T \<sqinter> ?E \<sqinter> (-F * e\<^sup>T * ?G)) * w\<^sup>T"
    by (metis comp_associative comp_inf_covector inf_top.left_neutral)
  also have "... = ?FF \<sqinter> w * (?E\<^sup>T \<sqinter> ?E \<sqinter> ?GG) * w\<^sup>T"
    by (metis assms(3) arc_top_edge comp_associative)
  also have "... = ?FF \<sqinter> w * (w\<^sup>\<star> * e * top \<sqinter> ?E \<sqinter> ?GG) * w\<^sup>T"
    by (simp add: comp_associative conv_dist_comp conv_star_commute)
  also have "... = ?FF \<sqinter> w * (w\<^sup>\<star> * e * ?E \<sqinter> ?GG) * w\<^sup>T"
    by (metis comp_associative comp_inf_covector inf_top.left_neutral)
  also have "... \<le> ?FF \<sqinter> w * (w\<^sup>\<star> * w\<^sup>T\<^sup>\<star> \<sqinter> ?GG) * w\<^sup>T"
    by (metis assms(3) mult_assoc mult_1_right mult_left_isotone mult_right_isotone inf.sup_left_isotone inf.sup_right_isotone arc_expanded)
  also have "... = ?FF \<sqinter> w * ((w\<^sup>+ \<squnion> 1 \<squnion> w\<^sup>T\<^sup>\<star>) \<sqinter> ?GG) * w\<^sup>T"
    by (simp add: assms(2) cancel_separate_eq star_left_unfold_equal sup_monoid.add_commute)
  also have "... = ?FF \<sqinter> w * ((w\<^sup>+ \<squnion> 1 \<squnion> w\<^sup>T\<^sup>+) \<sqinter> ?GG) * w\<^sup>T"
    using star.circ_plus_one star_left_unfold_equal sup_assoc by presburger
  also have "... = (?FF \<sqinter> w * (w\<^sup>+ \<sqinter> ?GG) * w\<^sup>T) \<squnion> (?FF \<sqinter> w * (1 \<sqinter> ?GG) * w\<^sup>T) \<squnion> (?FF \<sqinter> w * (w\<^sup>T\<^sup>+ \<sqinter> ?GG) * w\<^sup>T)"
    by (simp add: inf_sup_distrib1 inf_sup_distrib2 semiring.distrib_left semiring.distrib_right)
  also have "... \<le> w * (1 \<sqinter> ?GG) * w\<^sup>T"
    using 9 10 by simp
  also have "... \<le> w * w\<^sup>T"
    by (metis inf.cobounded1 mult_1_right mult_left_isotone mult_right_isotone)
  also have "... \<le> 1"
    by (simp add: assms(2))
  finally show "(w \<sqinter> ?E \<sqinter> ?F \<sqinter> ?G) * top * (w \<sqinter> ?E \<sqinter> ?F \<sqinter> ?G)\<^sup>T \<le> 1"
    by simp
  have "w\<^sup>T\<^sup>+ \<sqinter> -F * e\<^sup>T * e * -F \<sqinter> w\<^sup>T * F * e\<^sup>T * e * F * w \<le> w\<^sup>T\<^sup>+ \<sqinter> ?G \<sqinter> w\<^sup>T * F * e\<^sup>T * e * F * w"
    using top_greatest inf.sup_left_isotone inf.sup_right_isotone mult_left_isotone by simp
  also have "... \<le> w\<^sup>T\<^sup>+ \<sqinter> ?G \<sqinter> w\<^sup>T * ?F"
    using comp_associative inf.sup_right_isotone mult_right_isotone top.extremum by presburger
  also have "... = w\<^sup>T * (w\<^sup>T\<^sup>\<star> \<sqinter> ?F) \<sqinter> ?G"
    using assms(2) inf_assoc inf_commute inf_left_commute univalent_comp_left_dist_inf by simp
  also have "... \<le> w\<^sup>T * (top * e * F) \<sqinter> ?G"
    using 6 by (metis inf.sup_monoid.add_commute inf.sup_right_isotone mult_right_isotone)
  also have "... \<le> top * e * F \<sqinter> ?G"
    by (metis comp_associative comp_inf_covector mult_left_isotone top.extremum)
  also have "... = bot"
    by (metis assms(3) conv_dist_comp conv_involutive conv_top inf_p mult_right_zero univalent_comp_left_dist_inf)
  finally have 11: "w\<^sup>T\<^sup>+ \<sqinter> -F * e\<^sup>T * e * -F \<sqinter> w\<^sup>T * F * e\<^sup>T * e * F * w = bot"
    by (simp add: antisym)
  hence 12: "w\<^sup>+ \<sqinter> -F * e\<^sup>T * e * -F \<sqinter> w\<^sup>T * F * e\<^sup>T * e * F * w = bot"
    using assms(1) comp_associative conv_bot conv_complement conv_dist_comp conv_dist_inf conv_star_commute star.circ_plus_same by fastforce
  have "(w \<sqinter> ?E \<sqinter> ?F \<sqinter> ?G)\<^sup>T * top * (w \<sqinter> ?E \<sqinter> ?F \<sqinter> ?G) = ((w \<sqinter> ?E \<sqinter> ?G)\<^sup>T \<sqinter> ?F\<^sup>T) * top * (?F \<sqinter> (w \<sqinter> ?E \<sqinter> ?G))"
    by (simp add: conv_dist_inf inf_commute inf_left_commute)
  also have "... = (w \<sqinter> ?E \<sqinter> ?G)\<^sup>T * ?F * (?F \<sqinter> (w \<sqinter> ?E \<sqinter> ?G))"
    by (simp add: covector_inf_comp_3 vector_mult_closed)
  also have "... = (w \<sqinter> ?E \<sqinter> ?G)\<^sup>T * (?F \<sqinter> ?F\<^sup>T) * (w \<sqinter> ?E \<sqinter> ?G)"
    using covector_comp_inf covector_inf_comp_3 vector_conv_covector vector_mult_closed by simp
  also have "... = (w \<sqinter> ?E \<sqinter> ?G)\<^sup>T * (?F \<sqinter> ?F\<^sup>T) * (w \<sqinter> ?E) \<sqinter> ?G"
    by (simp add: comp_associative comp_inf_covector)
  also have "... = (w \<sqinter> ?E \<sqinter> ?G)\<^sup>T * (?F \<sqinter> ?F\<^sup>T) * w \<sqinter> ?E \<sqinter> ?G"
    by (simp add: comp_associative comp_inf_covector)
  also have "... = (?G\<^sup>T \<sqinter> (?E\<^sup>T \<sqinter> w\<^sup>T)) * (?F \<sqinter> ?F\<^sup>T) * w \<sqinter> ?E \<sqinter> ?G"
    by (simp add: conv_dist_inf inf.left_commute inf.sup_monoid.add_commute)
  also have "... = ?G\<^sup>T \<sqinter> (?E\<^sup>T \<sqinter> w\<^sup>T) * (?F \<sqinter> ?F\<^sup>T) * w \<sqinter> ?E \<sqinter> ?G"
    by (metis (no_types) comp_associative conv_dist_comp conv_top vector_export_comp)
  also have "... = ?G\<^sup>T \<sqinter> ?E\<^sup>T \<sqinter> w\<^sup>T * (?F \<sqinter> ?F\<^sup>T) * w \<sqinter> ?E \<sqinter> ?G"
    by (metis (no_types) comp_associative inf_assoc conv_dist_comp conv_top vector_export_comp)
  also have "... = ?E\<^sup>T \<sqinter> ?E \<sqinter> (?G\<^sup>T \<sqinter> ?G) \<sqinter> w\<^sup>T * (?F \<sqinter> ?F\<^sup>T) * w"
    by (simp add: inf_assoc inf.left_commute inf.sup_monoid.add_commute)
  also have "... = w\<^sup>\<star> * e * top \<sqinter> ?E \<sqinter> (?G\<^sup>T \<sqinter> ?G) \<sqinter> w\<^sup>T * (?F \<sqinter> ?F\<^sup>T) * w"
    by (simp add: comp_associative conv_dist_comp conv_star_commute)
  also have "... = w\<^sup>\<star> * e * ?E \<sqinter> (?G\<^sup>T \<sqinter> ?G) \<sqinter> w\<^sup>T * (?F \<sqinter> ?F\<^sup>T) * w"
    by (metis comp_associative comp_inf_covector inf_top.left_neutral)
  also have "... \<le> w\<^sup>\<star> * w\<^sup>T\<^sup>\<star> \<sqinter> (?G\<^sup>T \<sqinter> ?G) \<sqinter> w\<^sup>T * (?F \<sqinter> ?F\<^sup>T) * w"
    by (metis assms(3) mult_assoc mult_1_right mult_left_isotone mult_right_isotone inf.sup_left_isotone arc_expanded)
  also have "... = w\<^sup>\<star> * w\<^sup>T\<^sup>\<star> \<sqinter> (-F * e\<^sup>T * top \<sqinter> ?G) \<sqinter> w\<^sup>T * (?F \<sqinter> ?F\<^sup>T) * w"
    by (simp add: assms(1) conv_complement conv_dist_comp mult_assoc)
  also have "... = w\<^sup>\<star> * w\<^sup>T\<^sup>\<star> \<sqinter> -F * e\<^sup>T * ?G \<sqinter> w\<^sup>T * (?F \<sqinter> ?F\<^sup>T) * w"
    by (metis comp_associative comp_inf_covector inf_top.left_neutral)
  also have "... = w\<^sup>\<star> * w\<^sup>T\<^sup>\<star> \<sqinter> -F * e\<^sup>T * e * -F \<sqinter> w\<^sup>T * (?F \<sqinter> ?F\<^sup>T) * w"
    by (metis assms(3) arc_top_edge mult_assoc)
  also have "... = w\<^sup>\<star> * w\<^sup>T\<^sup>\<star> \<sqinter> -F * e\<^sup>T * e * -F \<sqinter> w\<^sup>T * (?F \<sqinter> top * e * F) * w"
    by (simp add: assms(1) conv_dist_comp mult_assoc)
  also have "... = w\<^sup>\<star> * w\<^sup>T\<^sup>\<star> \<sqinter> -F * e\<^sup>T * e * -F \<sqinter> w\<^sup>T * (?F * e * F) * w"
    by (metis comp_associative comp_inf_covector inf_top.left_neutral)
  also have "... = w\<^sup>\<star> * w\<^sup>T\<^sup>\<star> \<sqinter> -F * e\<^sup>T * e * -F \<sqinter> w\<^sup>T * F * e\<^sup>T * e * F * w"
    by (metis assms(3) arc_top_edge mult_assoc)
  also have "... = (w\<^sup>+ \<squnion> 1 \<squnion> w\<^sup>T\<^sup>\<star>) \<sqinter> -F * e\<^sup>T * e * -F \<sqinter> w\<^sup>T * F * e\<^sup>T * e * F * w"
    by (simp add: assms(2) cancel_separate_eq star_left_unfold_equal sup_monoid.add_commute)
  also have "... = (w\<^sup>+ \<squnion> 1 \<squnion> w\<^sup>T\<^sup>+) \<sqinter> -F * e\<^sup>T * e * -F \<sqinter> w\<^sup>T * F * e\<^sup>T * e * F * w"
    using star.circ_plus_one star_left_unfold_equal sup_assoc by presburger
  also have "... = (w\<^sup>+ \<sqinter> -F * e\<^sup>T * e * -F \<sqinter> w\<^sup>T * F * e\<^sup>T * e * F * w) \<squnion> (1 \<sqinter> -F * e\<^sup>T * e * -F \<sqinter> w\<^sup>T * F * e\<^sup>T * e * F * w) \<squnion> (w\<^sup>T\<^sup>+ \<sqinter> -F * e\<^sup>T * e * -F \<sqinter> w\<^sup>T * F * e\<^sup>T * e * F * w)"
    by (simp add: inf_sup_distrib2)
  also have "... \<le> 1"
    using 11 12 by (simp add: inf.coboundedI1)
  finally show "(w \<sqinter> ?E \<sqinter> ?F \<sqinter> ?G)\<^sup>T * top * (w \<sqinter> ?E \<sqinter> ?F \<sqinter> ?G) \<le> 1"
    by simp
  have "(w \<sqinter> -F) * (F \<sqinter> w\<^sup>T) \<le> w * w\<^sup>T \<sqinter> -F * F"
    by (simp add: mult_isotone)
  also have "... \<le> 1 \<sqinter> -F"
    using assms(1,2) comp_inf.comp_isotone equivalence_comp_right_complement by auto
  also have "... = bot"
    using assms(1) bot_unique pp_isotone pseudo_complement_pp by blast
  finally have 13: "(w \<sqinter> -F) * (F \<sqinter> w\<^sup>T) = bot"
    by (simp add: antisym)
  have "w \<sqinter> ?G \<le> F * (w \<sqinter> ?G)"
    by (metis assms(1) mult_1_left mult_right_dist_sup sup.absorb_iff2)
  also have "... \<le> F * (w \<sqinter> ?G) * w\<^sup>\<star>"
    by (metis eq_refl le_supE star.circ_back_loop_fixpoint)
  finally have 14: "w \<sqinter> ?G \<le> F * (w \<sqinter> ?G) * w\<^sup>\<star>"
    by simp
  have "w \<sqinter> top * e * F \<le> w * (e * F)\<^sup>T * e * F"
    by (metis (no_types) comp_inf.star_slide dedekind_2 inf_left_commute inf_top_right mult_assoc)
  also have "... \<le> F"
    using 3 assms(1) by (metis comp_associative conv_dist_comp mult_left_isotone preorder_idempotent)
  finally have "w \<sqinter> -F \<le> -(top * e * F)"
    using order.trans p_shunting_swap pp_increasing by blast
  also have "... = ?G"
    by (metis assms(3) comp_mapping_complement conv_dist_comp conv_involutive conv_top)
  finally have "(w \<sqinter> -F) * F * (w \<sqinter> ?G) = (w \<sqinter> -F \<sqinter> ?G) * F * (w \<sqinter> ?G)"
    by (simp add: inf.absorb1)
  also have "... \<le> (w \<sqinter> -F \<sqinter> ?G) * F * w"
    by (simp add: comp_isotone)
  also have "... \<le> (w \<sqinter> -F \<sqinter> ?G) * forest_components (F \<sqinter> w) * w"
    by (simp add: assms(5) mult_left_isotone mult_right_isotone)
  also have "... \<le> (w \<sqinter> -F \<sqinter> ?G) * (F \<sqinter> w)\<^sup>T\<^sup>\<star> * w\<^sup>\<star> * w"
    by (simp add: mult_left_isotone mult_right_isotone star_isotone mult_assoc)
  also have "... \<le> (w \<sqinter> -F \<sqinter> ?G) * (F \<sqinter> w)\<^sup>T\<^sup>\<star> * w\<^sup>\<star>"
    by (simp add: comp_associative mult_right_isotone star.circ_plus_same star.left_plus_below_circ)
  also have "... = (w \<sqinter> -F \<sqinter> ?G) * w\<^sup>\<star> \<squnion> (w \<sqinter> -F \<sqinter> ?G) * (F \<sqinter> w)\<^sup>T\<^sup>+ * w\<^sup>\<star>"
    by (metis comp_associative inf.sup_monoid.add_assoc mult_left_dist_sup star.circ_loop_fixpoint sup_commute)
  also have "... \<le> (w \<sqinter> -F \<sqinter> ?G) * w\<^sup>\<star> \<squnion> (w \<sqinter> -F \<sqinter> ?G) * (F \<sqinter> w)\<^sup>T * top"
    by (metis mult_assoc top_greatest mult_right_isotone sup_right_isotone)
  also have "... \<le> (w \<sqinter> -F \<sqinter> ?G) * w\<^sup>\<star> \<squnion> (w \<sqinter> -F) * (F \<sqinter> w)\<^sup>T * top"
    using inf.cobounded1 mult_left_isotone sup_right_isotone by blast
  also have "... \<le> (w \<sqinter> ?G) * w\<^sup>\<star> \<squnion> (w \<sqinter> -F) * (F \<sqinter> w)\<^sup>T * top"
    using inf.sup_monoid.add_assoc inf.sup_right_isotone mult_left_isotone sup_commute sup_right_isotone by simp
  also have "... = (w \<sqinter> ?G) * w\<^sup>\<star> \<squnion> (w \<sqinter> -F) * (F \<sqinter> w\<^sup>T) * top"
    by (simp add: assms(1) conv_dist_inf)
  also have "... \<le> 1 * (w \<sqinter> ?G) * w\<^sup>\<star>"
    using 13 by simp
  also have "... \<le> F * (w \<sqinter> ?G) * w\<^sup>\<star>"
    using assms(1) mult_left_isotone by blast
  finally have 15: "(w \<sqinter> -F) * F * (w \<sqinter> ?G) \<le> F * (w \<sqinter> ?G) * w\<^sup>\<star>"
    by simp
  have "(w \<sqinter> F) * F * (w \<sqinter> ?G) \<le> F * F * (w \<sqinter> ?G)"
    by (simp add: mult_left_isotone)
  also have "... = F * (w \<sqinter> ?G)"
    by (simp add: assms(1) preorder_idempotent)
  also have "... \<le> F * (w \<sqinter> ?G) * w\<^sup>\<star>"
    by (metis eq_refl le_supE star.circ_back_loop_fixpoint)
  finally have "(w \<sqinter> F) * F * (w \<sqinter> ?G) \<le> F * (w \<sqinter> ?G) * w\<^sup>\<star>"
    by simp
  hence "((w \<sqinter> F) \<squnion> (w \<sqinter> -F)) * F * (w \<sqinter> ?G) \<le> F * (w \<sqinter> ?G) * w\<^sup>\<star>"
    using 15 by (simp add: semiring.distrib_right)
  hence "w * F * (w \<sqinter> ?G) \<le> F * (w \<sqinter> ?G) * w\<^sup>\<star>"
    by (metis assms(4) maddux_3_11_pp)
  hence "w * F * (w \<sqinter> ?G) * w\<^sup>\<star> \<le> F * (w \<sqinter> ?G) * w\<^sup>\<star>"
    by (metis (full_types) comp_associative mult_left_isotone star.circ_transitive_equal)
  hence "w\<^sup>\<star> * (w \<sqinter> ?G) \<le> F * (w \<sqinter> ?G) * w\<^sup>\<star>"
    using 14 by (simp add: mult_assoc star_left_induct)
  hence 16: "w\<^sup>+ \<sqinter> ?G \<le> F * (w \<sqinter> ?G) * w\<^sup>\<star>"
    by (simp add: covector_comp_inf covector_mult_closed star.circ_plus_same)
  have 17: "e\<^sup>T * top * e\<^sup>T \<le> -F"
    using assms(8) le_bot triple_schroeder_p by simp
  hence "(top * e)\<^sup>T * e\<^sup>T \<le> -F"
    by (simp add: conv_dist_comp)
  hence 18: "e\<^sup>T \<le> ?G"
    by (metis assms(3) shunt_mapping conv_dist_comp conv_involutive conv_top)
  have "e\<^sup>T \<le> -F"
    using 17 by (simp add: assms(3) arc_top_arc)
  also have "... \<le> -1"
    by (simp add: assms(1) p_antitone)
  finally have "e\<^sup>T \<le> w\<^sup>\<star> \<sqinter> -1"
    using assms(9) by simp
  also have "... \<le> w\<^sup>+"
    using shunting_var_p star_left_unfold_equal sup_commute by simp
  finally have "e\<^sup>T \<le> w\<^sup>+ \<sqinter> ?G"
    using 18 by simp
  hence "e\<^sup>T \<le> F * (w \<sqinter> ?G) * w\<^sup>\<star>"
    using 16 order_trans by blast
  also have "... = (F * w \<sqinter> ?G) * w\<^sup>\<star>"
    by (simp add: comp_associative comp_inf_covector)
  finally have "e\<^sup>T * top * e\<^sup>T \<le> (F * w \<sqinter> ?G) * w\<^sup>\<star>"
    by (simp add: assms(3) arc_top_arc)
  hence "e\<^sup>T * top * (e * top)\<^sup>T \<le> (F * w \<sqinter> ?G) * w\<^sup>\<star>"
    by (metis conv_dist_comp conv_top vector_top_closed mult_assoc)
  hence "e\<^sup>T * top \<le> (F * w \<sqinter> ?G) * w\<^sup>\<star> * e * top"
    by (metis assms(3) shunt_bijective mult_assoc)
  hence "(top * e)\<^sup>T * top \<le> (F * w \<sqinter> ?G) * w\<^sup>\<star> * e * top"
    by (simp add: conv_dist_comp mult_assoc)
  hence "top \<le> top * e * (F * w \<sqinter> ?G) * w\<^sup>\<star> * e * top"
    by (metis assms(3) shunt_mapping conv_dist_comp conv_involutive conv_top mult_assoc)
  also have "... = top * e * F * w * (w\<^sup>\<star> * e * top \<sqinter> ?G\<^sup>T)"
    by (metis comp_associative comp_inf_vector_1)
  also have "... = top * (w \<sqinter> (top * e * F)\<^sup>T) * (w\<^sup>\<star> * e * top \<sqinter> ?G\<^sup>T)"
    by (metis comp_inf_vector_1 inf_top.left_neutral)
  also have "... = top * (w \<sqinter> ?F) * (w\<^sup>\<star> * e * top \<sqinter> ?G\<^sup>T)"
    by (simp add: assms(1) conv_dist_comp mult_assoc)
  also have "... = top * (w \<sqinter> ?F) * (?E\<^sup>T \<sqinter> ?G\<^sup>T)"
    by (simp add: comp_associative conv_dist_comp conv_star_commute)
  also have "... = top * (w \<sqinter> ?F \<sqinter> ?G) * ?E\<^sup>T"
    by (simp add: comp_associative comp_inf_vector_1)
  also have "... = top * (w \<sqinter> ?F \<sqinter> ?G \<sqinter> ?E) * top"
    using comp_inf_vector_1 mult_assoc by simp
  finally show "top * (w \<sqinter> ?E \<sqinter> ?F \<sqinter> ?G) * top = top"
    by (simp add: inf_commute inf_left_commute top_le)
qed

lemma kruskal_edge_arc_1:
  assumes "e \<le> --h"
      and "h \<le> g"
      and "symmetric h"
      and "components g \<le> forest_components w"
      and "w * e\<^sup>T = bot"
    shows "e\<^sup>T \<le> w\<^sup>\<star>"
proof -
  have "w\<^sup>T * top \<le> -(e\<^sup>T * top)"
    using assms(5) schroeder_3_p vector_bot_closed mult_assoc by fastforce
  hence 1: "w\<^sup>T * top \<sqinter> e\<^sup>T * top = bot"
    using pseudo_complement by simp
  have "e\<^sup>T \<le> e\<^sup>T * top \<sqinter> --h\<^sup>T"
    using assms(1) conv_complement conv_isotone top_right_mult_increasing by fastforce
  also have "... \<le> e\<^sup>T * top \<sqinter> --g"
    using assms(2,3) inf.sup_right_isotone pp_isotone by simp
  also have "... \<le> e\<^sup>T * top \<sqinter> components g"
    using inf.sup_right_isotone star.circ_increasing by simp
  also have "... \<le> e\<^sup>T * top \<sqinter> forest_components w"
    using assms(4) comp_inf.mult_right_isotone by simp
  also have "... = (e\<^sup>T * top \<sqinter> w\<^sup>T\<^sup>\<star>) * w\<^sup>\<star>"
    by (simp add: inf_assoc vector_export_comp)
  also have "... = (e\<^sup>T * top \<sqinter> 1) * w\<^sup>\<star> \<squnion> (e\<^sup>T * top \<sqinter> w\<^sup>T\<^sup>+) * w\<^sup>\<star>"
    by (metis inf_sup_distrib1 semiring.distrib_right star_left_unfold_equal)
  also have "... \<le> w\<^sup>\<star> \<squnion> (e\<^sup>T * top \<sqinter> w\<^sup>T\<^sup>+) * w\<^sup>\<star>"
    by (metis inf_le2 mult_1_left mult_left_isotone sup_left_isotone)
  also have "... \<le> w\<^sup>\<star> \<squnion> (e\<^sup>T * top \<sqinter> w\<^sup>T) * top"
    using comp_associative comp_inf.mult_right_isotone sup_right_isotone mult_right_isotone top.extremum vector_export_comp by presburger
  also have "... = w\<^sup>\<star>"
    using 1 inf.sup_monoid.add_commute inf_vector_comp by simp
  finally show ?thesis
    by simp
qed

lemma kruskal_edge_between_components_1:
  assumes "equivalence F"
      and "mapping (top * e)"
    shows "F \<le> -(w \<sqinter> top * e\<^sup>T * w\<^sup>T\<^sup>\<star> \<sqinter> F * e\<^sup>T * top \<sqinter> top * e * -F)"
proof -
  let ?d = "w \<sqinter> top * e\<^sup>T * w\<^sup>T\<^sup>\<star> \<sqinter> F * e\<^sup>T * top \<sqinter> top * e * -F"
  have "?d \<sqinter> F \<le> F * e\<^sup>T * top \<sqinter> F"
    by (meson inf_le1 inf_le2 le_infI order_trans)
  also have "... \<le> (F * e\<^sup>T * top)\<^sup>T * F"
    by (simp add: mult_assoc vector_restrict_comp_conv)
  also have "... = top * e * F * F"
    by (simp add: assms(1) comp_associative conv_dist_comp conv_star_commute)
  also have "... = top * e * F"
    using assms(1) preorder_idempotent mult_assoc by fastforce
  finally have "?d \<sqinter> F \<le> top * e * F \<sqinter> top * e * -F"
    by (simp add: le_infI1)
  also have "... = top * e * F \<sqinter> -(top * e * F)"
    using assms(2) conv_dist_comp total_conv_surjective comp_mapping_complement by simp
  finally show ?thesis
    by (metis inf_p le_bot p_antitone_iff pseudo_complement)
qed

lemma kruskal_edge_between_components_2:
  assumes "forest_components f \<le> -d"
      and "injective f"
      and "f \<squnion> f\<^sup>T \<le> w \<squnion> w\<^sup>T"
    shows "f \<squnion> f\<^sup>T \<le> (w \<sqinter> -d \<sqinter> -d\<^sup>T) \<squnion> (w\<^sup>T \<sqinter> -d \<sqinter> -d\<^sup>T)"
proof -
  let ?F = "forest_components f"
  have "?F\<^sup>T \<le> -d\<^sup>T"
    using assms(1) conv_complement conv_order by fastforce
  hence 1: "?F \<le> -d\<^sup>T"
    by (simp add: conv_dist_comp conv_star_commute)
  have "equivalence ?F"
    using assms(2) forest_components_equivalence by simp
  hence "f \<squnion> f\<^sup>T \<le> ?F"
    by (metis conv_dist_inf forest_components_increasing inf.absorb_iff2 sup.boundedI)
  also have "... \<le> -d \<sqinter> -d\<^sup>T"
    using 1 assms(1) by simp
  finally have "f \<squnion> f\<^sup>T \<le> -d \<sqinter> -d\<^sup>T"
    by simp
  thus ?thesis
    by (metis assms(3) inf_sup_distrib2 le_inf_iff)
qed

end

subsection \<open>Related Structures\<close>

text \<open>
Stone algebras can be expanded to Stone-Kleene relation algebras by reusing some operations.
\<close>

sublocale stone_algebra < comp_inf: stone_kleene_relation_algebra where star = "\<lambda>x . top" and one = top and times = inf and conv = id
  apply unfold_locales
  by simp

text \<open>
Every bounded linear order can be expanded to a Stone algebra, which can be expanded to a Stone relation algebra, which can be expanded to a Stone-Kleene relation algebra.
\<close>

class linorder_stone_kleene_relation_algebra_expansion = linorder_stone_relation_algebra_expansion + star +
  assumes star_def [simp]: "x\<^sup>\<star> = top"
begin

subclass kleene_algebra
  apply unfold_locales
  apply simp
  apply (simp add: min.coboundedI1 min.commute)
  by (simp add: min.coboundedI1)

subclass stone_kleene_relation_algebra
  apply unfold_locales
  by simp

end

text \<open>
A Kleene relation algebra is based on a relation algebra.
\<close>

class kleene_relation_algebra = relation_algebra + stone_kleene_relation_algebra

end

