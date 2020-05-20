(* Title:      Minimum Spanning Tree Algorithms
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Minimum Spanning Tree Algorithms\<close>

text \<open>
In this theory we prove the total-correctness of Kruskal's and Prim's minimum spanning tree algorithms.
Specifications and algorithms work in Stone-Kleene relation algebras extended by operations for aggregation and minimisation.
The algorithms are implemented in a simple imperative language and their proof uses Hoare Logic.
The correctness proofs are discussed in \cite{Guttmann2016c,Guttmann2018a,Guttmann2018b}.
\<close>

theory Minimum_Spanning_Trees

imports Hoare_Logic Aggregation_Algebras

begin

no_notation
  trancl ("(_\<^sup>+)" [1000] 999)

context m_kleene_algebra
begin

subsection \<open>Kruskal's Minimum Spanning Tree Algorithm\<close>

text \<open>
The total-correctness proof of Kruskal's minimum spanning tree algorithm uses the following steps \cite{Guttmann2018b}.
We first establish that the algorithm terminates and constructs a spanning tree.
This is a constructive proof of the existence of a spanning tree; any spanning tree algorithm could be used for this.
We then conclude that a minimum spanning tree exists.
This is necessary to establish the invariant for the actual correctness proof, which shows that Kruskal's algorithm produces a minimum spanning tree.
\<close>

definition "spanning_forest f g \<equiv> forest f \<and> f \<le> --g \<and> components g \<le> forest_components f \<and> regular f"
definition "minimum_spanning_forest f g \<equiv> spanning_forest f g \<and> (\<forall>u . spanning_forest u g \<longrightarrow> sum (f \<sqinter> g) \<le> sum (u \<sqinter> g))"
definition "kruskal_spanning_invariant f g h \<equiv> symmetric g \<and> h = h\<^sup>T \<and> g \<sqinter> --h = h \<and> spanning_forest f (-h \<sqinter> g)"
definition "kruskal_invariant f g h \<equiv> kruskal_spanning_invariant f g h \<and> (\<exists>w . minimum_spanning_forest w g \<and> f \<le> w \<squnion> w\<^sup>T)"

text \<open>
We first show two verification conditions which are used in both correctness proofs.
\<close>

lemma kruskal_vc_1:
  assumes "symmetric g"
    shows "kruskal_spanning_invariant bot g g"
proof (unfold kruskal_spanning_invariant_def, intro conjI)
  show "symmetric g"
    using assms by simp
next
  show "g = g\<^sup>T"
    using assms by simp
next
  show "g \<sqinter> --g = g"
    using inf.sup_monoid.add_commute selection_closed_id by simp
next
  show "spanning_forest bot (-g \<sqinter> g)"
    using star.circ_transitive_equal spanning_forest_def by simp
qed

lemma kruskal_vc_2:
  assumes "kruskal_spanning_invariant f g h"
      and "h \<noteq> bot"
      and "card { x . regular x \<and> x \<le> --h } = n"
    shows "(minarc h \<le> -forest_components f \<longrightarrow> kruskal_spanning_invariant ((f \<sqinter> -(top * minarc h * f\<^sup>T\<^sup>\<star>)) \<squnion> (f \<sqinter> top * minarc h * f\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> minarc h) g (h \<sqinter> -minarc h \<sqinter> -minarc h\<^sup>T)
                                               \<and> card { x . regular x \<and> x \<le> --h \<and> x \<le> -minarc h \<and> x \<le> -minarc h\<^sup>T } < n) \<and>
           (\<not> minarc h \<le> -forest_components f \<longrightarrow> kruskal_spanning_invariant f g (h \<sqinter> -minarc h \<sqinter> -minarc h\<^sup>T)
                                                 \<and> card { x . regular x \<and> x \<le> --h \<and> x \<le> -minarc h \<and> x \<le> -minarc h\<^sup>T } < n)"
proof -
  let ?e = "minarc h"
  let ?f = "(f \<sqinter> -(top * ?e * f\<^sup>T\<^sup>\<star>)) \<squnion> (f \<sqinter> top * ?e * f\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> ?e"
  let ?h = "h \<sqinter> -?e \<sqinter> -?e\<^sup>T"
  let ?F = "forest_components f"
  let ?n1 = "card { x . regular x \<and> x \<le> --h }"
  let ?n2 = "card { x . regular x \<and> x \<le> --h \<and> x \<le> -?e \<and> x \<le> -?e\<^sup>T }"
  have 1: "regular f \<and> regular ?e"
    by (metis assms(1) kruskal_spanning_invariant_def spanning_forest_def minarc_regular)
  hence 2: "regular ?f \<and> regular ?F \<and> regular (?e\<^sup>T)"
    using regular_closed_star regular_conv_closed regular_mult_closed by simp
  have 3: "\<not> ?e \<le> -?e"
    using assms(2) inf.orderE minarc_bot_iff by fastforce
  have "?n2 < ?n1"
    apply (rule psubset_card_mono)
    using finite_regular apply simp
    using 1 3 kruskal_spanning_invariant_def minarc_below by auto
  hence 4: "?n2 < n"
    using assms(3) by simp
  show "(?e \<le> -?F \<longrightarrow> kruskal_spanning_invariant ?f g ?h \<and> ?n2 < n) \<and> (\<not> ?e \<le> -?F \<longrightarrow> kruskal_spanning_invariant f g ?h \<and> ?n2 < n)"
  proof (rule conjI)
    have 5: "injective ?f"
      apply (rule kruskal_injective_inv)
      using assms(1) kruskal_spanning_invariant_def spanning_forest_def apply simp
      apply (simp add: covector_mult_closed)
      apply (simp add: comp_associative comp_isotone star.right_plus_below_circ)
      apply (meson mult_left_isotone order_lesseq_imp star_outer_increasing top.extremum)
      using assms(1,2) kruskal_spanning_invariant_def kruskal_injective_inv_2 minarc_arc spanning_forest_def apply simp
      using assms(2) arc_injective minarc_arc apply blast
      using assms(1,2) kruskal_spanning_invariant_def kruskal_injective_inv_3 minarc_arc spanning_forest_def by simp
    show "?e \<le> -?F \<longrightarrow> kruskal_spanning_invariant ?f g ?h \<and> ?n2 < n"
    proof
      assume 6: "?e \<le> -?F"
      have 7: "equivalence ?F"
        using assms(1) kruskal_spanning_invariant_def forest_components_equivalence spanning_forest_def by simp
      have "?e\<^sup>T * top * ?e\<^sup>T = ?e\<^sup>T"
        using assms(2) by (simp add: arc_top_arc minarc_arc)
      hence "?e\<^sup>T * top * ?e\<^sup>T \<le> -?F"
        using 6 7 conv_complement conv_isotone by fastforce
      hence 8: "?e * ?F * ?e = bot"
        using le_bot triple_schroeder_p by simp
      show "kruskal_spanning_invariant ?f g ?h \<and> ?n2 < n"
      proof (unfold kruskal_spanning_invariant_def, intro conjI)
        show "symmetric g"
          using assms(1) kruskal_spanning_invariant_def by simp
      next
        show "?h = ?h\<^sup>T"
          using assms(1) by (simp add: conv_complement conv_dist_inf inf_commute inf_left_commute kruskal_spanning_invariant_def)
      next
        show "g \<sqinter> --?h = ?h"
          using 1 2 by (metis (hide_lams) assms(1) kruskal_spanning_invariant_def inf_assoc pp_dist_inf)
      next
        show "spanning_forest ?f (-?h \<sqinter> g)"
        proof (unfold spanning_forest_def, intro conjI)
          show "injective ?f"
            using 5 by simp
        next
          show "acyclic ?f"
            apply (rule kruskal_acyclic_inv)
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def apply simp
            apply (simp add: covector_mult_closed)
            using 8 assms(1) kruskal_spanning_invariant_def spanning_forest_def kruskal_acyclic_inv_1 apply simp
            using 8 apply (metis comp_associative mult_left_sub_dist_sup_left star.circ_loop_fixpoint sup_commute le_bot)
            using 6 by (simp add: p_antitone_iff)
        next
          show "?f \<le> --(-?h \<sqinter> g)"
            apply (rule kruskal_subgraph_inv)
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def apply simp
            using assms(1) apply (metis kruskal_spanning_invariant_def minarc_below order.trans pp_isotone_inf)
            using assms(1) kruskal_spanning_invariant_def apply simp
            using assms(1) kruskal_spanning_invariant_def by simp
        next
          show "components (-?h \<sqinter> g) \<le> forest_components ?f"
            apply (rule kruskal_spanning_inv)
            using 5 apply simp
            using 1 regular_closed_star regular_conv_closed regular_mult_closed apply simp
            using 1 apply simp
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def by simp
        next
          show "regular ?f"
            using 2 by simp
        qed
      next
        show "?n2 < n"
          using 4 by simp
      qed
    qed
  next
    show "\<not> ?e \<le> -?F \<longrightarrow> kruskal_spanning_invariant f g ?h \<and> ?n2 < n"
    proof
      assume "\<not> ?e \<le> -?F"
      hence 9: "?e \<le> ?F"
        using 2 assms(2) arc_in_partition minarc_arc by fastforce
      show "kruskal_spanning_invariant f g ?h \<and> ?n2 < n"
      proof (unfold kruskal_spanning_invariant_def, intro conjI)
        show "symmetric g"
          using assms(1) kruskal_spanning_invariant_def by simp
      next
        show "?h = ?h\<^sup>T"
          using assms(1) by (simp add: conv_complement conv_dist_inf inf_commute inf_left_commute kruskal_spanning_invariant_def)
      next
        show "g \<sqinter> --?h = ?h"
          using 1 2 by (metis (hide_lams) assms(1) kruskal_spanning_invariant_def inf_assoc pp_dist_inf)
      next
        show "spanning_forest f (-?h \<sqinter> g)"
        proof (unfold spanning_forest_def, intro conjI)
          show "injective f"
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def by simp
        next
          show "acyclic f"
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def by simp
        next
          have "f \<le> --(-h \<sqinter> g)"
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def by simp
          also have "... \<le> --(-?h \<sqinter> g)"
            using comp_inf.mult_right_isotone inf.sup_monoid.add_commute inf_left_commute p_antitone_inf pp_isotone by presburger
          finally show "f \<le> --(-?h \<sqinter> g)"
            by simp
        next
          show "components (-?h \<sqinter> g) \<le> ?F"
            apply (rule kruskal_spanning_inv_1)
            using 9 apply simp
            using 1 apply simp
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def apply simp
            using assms(1) kruskal_spanning_invariant_def forest_components_equivalence spanning_forest_def by simp
        next
          show "regular f"
            using 1 by simp
        qed
      next
        show "?n2 < n"
          using 4 by simp
      qed
    qed
  qed
qed

text \<open>
The following result shows that Kruskal's algorithm terminates and constructs a spanning tree.
We cannot yet show that this is a minimum spanning tree.
\<close>

theorem kruskal_spanning:
  "VARS e f h
  [ symmetric g ]
  f := bot;
  h := g;
  WHILE h \<noteq> bot
    INV { kruskal_spanning_invariant f g h }
    VAR { card { x . regular x \<and> x \<le> --h } }
     DO e := minarc h;
        IF e \<le> -forest_components f THEN
          f := (f \<sqinter> -(top * e * f\<^sup>T\<^sup>\<star>)) \<squnion> (f \<sqinter> top * e * f\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> e
        ELSE
          SKIP
        FI;
        h := h \<sqinter> -e \<sqinter> -e\<^sup>T
     OD
  [ spanning_forest f g ]"
  apply vcg_tc_simp
  using kruskal_vc_1 apply simp
  using kruskal_vc_2 apply blast
  using kruskal_spanning_invariant_def by auto

text \<open>
Because we have shown total correctness, we conclude that a spanning tree exists.
\<close>

lemma kruskal_exists_spanning:
  "symmetric g \<Longrightarrow> \<exists>f . spanning_forest f g"
  using tc_extract_function kruskal_spanning by blast

text \<open>
This implies that a minimum spanning tree exists, which is used in the subsequent correctness proof.
\<close>

lemma kruskal_exists_minimal_spanning:
  assumes "symmetric g"
    shows "\<exists>f . minimum_spanning_forest f g"
proof -
  let ?s = "{ f . spanning_forest f g }"
  have "\<exists>m\<in>?s . \<forall>z\<in>?s . sum (m \<sqinter> g) \<le> sum (z \<sqinter> g)"
    apply (rule finite_set_minimal)
    using finite_regular spanning_forest_def apply simp
    using assms kruskal_exists_spanning apply simp
    using sum_linear by simp
  thus ?thesis
    using minimum_spanning_forest_def by simp
qed

text \<open>
Kruskal's minimum spanning tree algorithm terminates and is correct.
This is the same algorithm that is used in the previous correctness proof, with the same precondition and variant, but with a different invariant and postcondition.
\<close>

theorem kruskal:
  "VARS e f h
  [ symmetric g ]
  f := bot;
  h := g;
  WHILE h \<noteq> bot
    INV { kruskal_invariant f g h }
    VAR { card { x . regular x \<and> x \<le> --h } }
     DO e := minarc h;
        IF e \<le> -forest_components f THEN
          f := (f \<sqinter> -(top * e * f\<^sup>T\<^sup>\<star>)) \<squnion> (f \<sqinter> top * e * f\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> e
        ELSE
          SKIP
        FI;
        h := h \<sqinter> -e \<sqinter> -e\<^sup>T
     OD
  [ minimum_spanning_forest f g ]"
proof vcg_tc_simp
  assume "symmetric g"
  thus "kruskal_invariant bot g g"
    using kruskal_vc_1 kruskal_exists_minimal_spanning kruskal_invariant_def by simp
next
  fix n f h
  let ?e = "minarc h"
  let ?f = "(f \<sqinter> -(top * ?e * f\<^sup>T\<^sup>\<star>)) \<squnion> (f \<sqinter> top * ?e * f\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> ?e"
  let ?h = "h \<sqinter> -?e \<sqinter> -?e\<^sup>T"
  let ?F = "forest_components f"
  let ?n1 = "card { x . regular x \<and> x \<le> --h }"
  let ?n2 = "card { x . regular x \<and> x \<le> --h \<and> x \<le> -?e \<and> x \<le> -?e\<^sup>T }"
  assume 1: "kruskal_invariant f g h \<and> h \<noteq> bot \<and> ?n1 = n"
  from 1 obtain w where 2: "minimum_spanning_forest w g \<and> f \<le> w \<squnion> w\<^sup>T"
    using kruskal_invariant_def by auto
  hence 3: "regular f \<and> regular w \<and> regular ?e"
    using 1 by (metis kruskal_invariant_def kruskal_spanning_invariant_def minimum_spanning_forest_def spanning_forest_def minarc_regular)
  show "(?e \<le> -?F \<longrightarrow> kruskal_invariant ?f g ?h \<and> ?n2 < n) \<and> (\<not> ?e \<le> -?F \<longrightarrow> kruskal_invariant f g ?h \<and> ?n2 < n)"
  proof (rule conjI)
    show "?e \<le> -?F \<longrightarrow> kruskal_invariant ?f g ?h \<and> ?n2 < n"
    proof
      assume 4: "?e \<le> -?F"
      have 5: "equivalence ?F"
        using 1 kruskal_invariant_def kruskal_spanning_invariant_def forest_components_equivalence spanning_forest_def by simp
      have "?e\<^sup>T * top * ?e\<^sup>T = ?e\<^sup>T"
        using 1 by (simp add: arc_top_arc minarc_arc)
      hence "?e\<^sup>T * top * ?e\<^sup>T \<le> -?F"
        using 4 5 conv_complement conv_isotone by fastforce
      hence 6: "?e * ?F * ?e = bot"
        using le_bot triple_schroeder_p by simp
      show "kruskal_invariant ?f g ?h \<and> ?n2 < n"
      proof (unfold kruskal_invariant_def, intro conjI)
        show "kruskal_spanning_invariant ?f g ?h"
          using 1 4 kruskal_vc_2 kruskal_invariant_def by simp
      next
        show "\<exists>w . minimum_spanning_forest w g \<and> ?f \<le> w \<squnion> w\<^sup>T"
        proof
          let ?p = "w \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>"
          let ?v = "(w \<sqinter> -(top * ?e * w\<^sup>T\<^sup>\<star>)) \<squnion> ?p\<^sup>T"
          have 7: "regular ?p"
            using 3 regular_closed_star regular_conv_closed regular_mult_closed by simp
          have 8: "injective ?v"
            apply (rule kruskal_exchange_injective_inv_1)
            using 2 minimum_spanning_forest_def spanning_forest_def apply simp
            apply (simp add: covector_mult_closed)
            apply (simp add: comp_associative comp_isotone star.right_plus_below_circ)
            using 1 2 kruskal_injective_inv_3 minarc_arc minimum_spanning_forest_def spanning_forest_def by simp
          have 9: "components g \<le> forest_components ?v"
            apply (rule kruskal_exchange_spanning_inv_1)
            using 8 apply simp
            using 7 apply simp
            using 2 minimum_spanning_forest_def spanning_forest_def by simp
          have 10: "spanning_forest ?v g"
          proof (unfold spanning_forest_def, intro conjI)
            show "injective ?v"
              using 8 by simp
          next
            show "acyclic ?v"
              apply (rule kruskal_exchange_acyclic_inv_1)
              using 2 minimum_spanning_forest_def spanning_forest_def apply simp
              by (simp add: covector_mult_closed)
          next
            show "?v \<le> --g"
              apply (rule sup_least)
              using 2 inf.coboundedI1 minimum_spanning_forest_def spanning_forest_def apply simp
              using 1 2 by (metis kruskal_invariant_def kruskal_spanning_invariant_def conv_complement conv_dist_inf order.trans inf.absorb2 inf.cobounded1 minimum_spanning_forest_def spanning_forest_def)
          next
            show "components g \<le> forest_components ?v"
              using 9 by simp
          next
            show "regular ?v"
              using 3 regular_closed_star regular_conv_closed regular_mult_closed by simp
          qed
          have 11: "sum (?v \<sqinter> g) = sum (w \<sqinter> g)"
          proof -
            have "sum (?v \<sqinter> g) = sum (w \<sqinter> -(top * ?e * w\<^sup>T\<^sup>\<star>) \<sqinter> g) + sum (?p\<^sup>T \<sqinter> g)"
              using 2 by (metis conv_complement conv_top epm_8 inf_import_p inf_top_right regular_closed_top vector_top_closed minimum_spanning_forest_def spanning_forest_def sum_disjoint)
            also have "... = sum (w \<sqinter> -(top * ?e * w\<^sup>T\<^sup>\<star>) \<sqinter> g) + sum (?p \<sqinter> g)"
              using 1 kruskal_invariant_def kruskal_spanning_invariant_def sum_symmetric by simp
            also have "... = sum (((w \<sqinter> -(top * ?e * w\<^sup>T\<^sup>\<star>)) \<squnion> ?p) \<sqinter> g)"
              using inf_commute inf_left_commute sum_disjoint by simp
            also have "... = sum (w \<sqinter> g)"
              using 3 7 maddux_3_11_pp by simp
            finally show ?thesis
              by simp
          qed
          have 12: "?v \<squnion> ?v\<^sup>T = w \<squnion> w\<^sup>T"
          proof -
            have "?v \<squnion> ?v\<^sup>T = (w \<sqinter> -?p) \<squnion> ?p\<^sup>T \<squnion> (w\<^sup>T \<sqinter> -?p\<^sup>T) \<squnion> ?p"
              using conv_complement conv_dist_inf conv_dist_sup inf_import_p sup_assoc by simp
            also have "... = w \<squnion> w\<^sup>T"
              using 3 7 conv_complement conv_dist_inf inf_import_p maddux_3_11_pp sup_monoid.add_assoc sup_monoid.add_commute by simp
            finally show ?thesis
              by simp
          qed
          have 13: "?v * ?e\<^sup>T = bot"
            apply (rule kruskal_reroot_edge)
            using 1 apply (simp add: minarc_arc)
            using 2 minimum_spanning_forest_def spanning_forest_def by simp
          have "?v \<sqinter> ?e \<le> ?v \<sqinter> top * ?e"
            using inf.sup_right_isotone top_left_mult_increasing by simp
          also have "... \<le> ?v * (top * ?e)\<^sup>T"
            using covector_restrict_comp_conv covector_mult_closed vector_top_closed by simp
          finally have 14: "?v \<sqinter> ?e = bot"
            using 13 by (metis conv_dist_comp mult_assoc le_bot mult_left_zero)
          let ?d = "?v \<sqinter> top * ?e\<^sup>T * ?v\<^sup>T\<^sup>\<star> \<sqinter> ?F * ?e\<^sup>T * top \<sqinter> top * ?e * -?F"
          let ?w = "(?v \<sqinter> -?d) \<squnion> ?e"
          have 15: "regular ?d"
            using 3 regular_closed_star regular_conv_closed regular_mult_closed by simp
          have 16: "?F \<le> -?d"
            apply (rule kruskal_edge_between_components_1)
            using 5 apply simp
            using 1 conv_dist_comp minarc_arc mult_assoc by simp
          have 17: "f \<squnion> f\<^sup>T \<le> (?v \<sqinter> -?d \<sqinter> -?d\<^sup>T) \<squnion> (?v\<^sup>T \<sqinter> -?d \<sqinter> -?d\<^sup>T)"
            apply (rule kruskal_edge_between_components_2)
            using 16 apply simp
            using 1 kruskal_invariant_def kruskal_spanning_invariant_def spanning_forest_def apply simp
            using 2 12 by (metis conv_dist_sup conv_involutive conv_isotone le_supI sup_commute)
          show "minimum_spanning_forest ?w g \<and> ?f \<le> ?w \<squnion> ?w\<^sup>T"
          proof (intro conjI)
            have 18: "?e\<^sup>T \<le> ?v\<^sup>\<star>"
              apply (rule kruskal_edge_arc_1[where g=g and h=h])
              using minarc_below apply simp
              using 1 apply (metis kruskal_invariant_def kruskal_spanning_invariant_def inf_le1)
              using 1 kruskal_invariant_def kruskal_spanning_invariant_def apply simp
              using 9 apply simp
              using 13 by simp
            have 19: "arc ?d"
              apply (rule kruskal_edge_arc)
              using 5 apply simp
              using 10 spanning_forest_def apply blast
              using 1 apply (simp add: minarc_arc)
              using 3 apply (metis conv_complement pp_dist_star regular_mult_closed)
              using 2 8 12 apply (simp add: kruskal_forest_components_inf)
              using 10 spanning_forest_def apply simp
              using 13 apply simp
              using 6 apply simp
              using 18 by simp
            show "minimum_spanning_forest ?w g"
            proof (unfold minimum_spanning_forest_def, intro conjI)
              have "(?v \<sqinter> -?d) * ?e\<^sup>T \<le> ?v * ?e\<^sup>T"
                using inf_le1 mult_left_isotone by simp
              hence "(?v \<sqinter> -?d) * ?e\<^sup>T = bot"
                using 13 le_bot by simp
              hence 20: "?e * (?v \<sqinter> -?d)\<^sup>T = bot"
                using conv_dist_comp conv_involutive conv_bot by force
              have 21: "injective ?w"
                apply (rule injective_sup)
                using 8 apply (simp add: injective_inf_closed)
                using 20 apply simp
                using 1 arc_injective minarc_arc by blast
              show "spanning_forest ?w g"
              proof (unfold spanning_forest_def, intro conjI)
                show "injective ?w"
                  using 21 by simp
              next
                show "acyclic ?w"
                  apply (rule kruskal_exchange_acyclic_inv_2)
                  using 10 spanning_forest_def apply blast
                  using 8 apply simp
                  using inf.coboundedI1 apply simp
                  using 19 apply simp
                  using 1 apply (simp add: minarc_arc)
                  using inf.cobounded2 inf.coboundedI1 apply simp
                  using 13 by simp
              next
                have "?w \<le> ?v \<squnion> ?e"
                  using inf_le1 sup_left_isotone by simp
                also have "... \<le> --g \<squnion> ?e"
                  using 10 sup_left_isotone spanning_forest_def by blast
                also have "... \<le> --g \<squnion> --h"
                  by (simp add: le_supI2 minarc_below)
                also have "... = --g"
                  using 1 by (metis kruskal_invariant_def kruskal_spanning_invariant_def pp_isotone_inf sup.orderE)
                finally show "?w \<le> --g"
                  by simp
              next
                have 22: "?d \<le> (?v \<sqinter> -?d)\<^sup>T\<^sup>\<star> * ?e\<^sup>T * top"
                  apply (rule kruskal_exchange_spanning_inv_2)
                  using 8 apply simp
                  using 13 apply (metis semiring.mult_not_zero star_absorb star_simulation_right_equal)
                  using 17 apply simp
                  by (simp add: inf.coboundedI1)
                have "components g \<le> forest_components ?v"
                  using 10 spanning_forest_def by auto
                also have "... \<le> forest_components ?w"
                  apply (rule kruskal_exchange_forest_components_inv)
                  using 21 apply simp
                  using 15 apply simp
                  using 1 apply (simp add: arc_top_arc minarc_arc)
                  apply (simp add: inf.coboundedI1)
                  using 13 apply simp
                  using 8 apply simp
                  apply (simp add: le_infI1)
                  using 22 by simp
                finally show "components g \<le> forest_components ?w"
                  by simp
              next
                show "regular ?w"
                  using 3 7 regular_conv_closed by simp
              qed
            next
              have 23: "?e \<sqinter> g \<noteq> bot"
                using 1 by (metis kruskal_invariant_def kruskal_spanning_invariant_def comp_inf.semiring.mult_zero_right inf.sup_monoid.add_assoc inf.sup_monoid.add_commute minarc_bot_iff minarc_meet_bot)
              have "g \<sqinter> -h \<le> (g \<sqinter> -h)\<^sup>\<star>"
                using star.circ_increasing by simp
              also have "... \<le> (--(g \<sqinter> -h))\<^sup>\<star>"
                using pp_increasing star_isotone by blast
              also have "... \<le> ?F"
                using 1 kruskal_invariant_def kruskal_spanning_invariant_def inf.sup_monoid.add_commute spanning_forest_def by simp
              finally have 24: "g \<sqinter> -h \<le> ?F"
                by simp
              have "?d \<le> --g"
                using 10 inf.coboundedI1 spanning_forest_def by blast
              hence "?d \<le> --g \<sqinter> -?F"
                using 16 inf.boundedI p_antitone_iff by simp
              also have "... = --(g \<sqinter> -?F)"
                by simp
              also have "... \<le> --h"
                using 24 p_shunting_swap pp_isotone by fastforce
              finally have 25: "?d \<le> --h"
                by simp
              have "?d = bot \<longrightarrow> top = bot"
                using 19 by (metis mult_left_zero mult_right_zero)
              hence "?d \<noteq> bot"
                using 1 le_bot by auto
              hence 26: "?d \<sqinter> h \<noteq> bot"
                using 25 by (metis inf.absorb_iff2 inf_commute pseudo_complement)
              have "sum (?e \<sqinter> g) = sum (?e \<sqinter> --h \<sqinter> g)"
                by (simp add: inf.absorb1 minarc_below)
              also have "... = sum (?e \<sqinter> h)"
                using 1 by (metis kruskal_invariant_def kruskal_spanning_invariant_def inf.left_commute inf.sup_monoid.add_commute)
              also have "... \<le> sum (?d \<sqinter> h)"
                using 19 26 minarc_min by simp
              also have "... = sum (?d \<sqinter> (--h \<sqinter> g))"
                using 1 kruskal_invariant_def kruskal_spanning_invariant_def inf_commute by simp
              also have "... = sum (?d \<sqinter> g)"
                using 25 by (simp add: inf.absorb2 inf_assoc inf_commute)
              finally have 27: "sum (?e \<sqinter> g) \<le> sum (?d \<sqinter> g)"
                by simp
              have "?v \<sqinter> ?e \<sqinter> -?d = bot"
                using 14 by simp
              hence "sum (?w \<sqinter> g) = sum (?v \<sqinter> -?d \<sqinter> g) + sum (?e \<sqinter> g)"
                using sum_disjoint inf_commute inf_assoc by simp
              also have "... \<le> sum (?v \<sqinter> -?d \<sqinter> g) + sum (?d \<sqinter> g)"
                using 23 27 sum_plus_right_isotone by simp
              also have "... = sum (((?v \<sqinter> -?d) \<squnion> ?d) \<sqinter> g)"
                using sum_disjoint inf_le2 pseudo_complement by simp
              also have "... = sum ((?v \<squnion> ?d) \<sqinter> (-?d \<squnion> ?d) \<sqinter> g)"
                by (simp add: sup_inf_distrib2)
              also have "... = sum ((?v \<squnion> ?d) \<sqinter> g)"
                using 15 by (metis inf_top_right stone)
              also have "... = sum (?v \<sqinter> g)"
                by (simp add: inf.sup_monoid.add_assoc)
              finally have "sum (?w \<sqinter> g) \<le> sum (?v \<sqinter> g)"
                by simp
              thus "\<forall>u . spanning_forest u g \<longrightarrow> sum (?w \<sqinter> g) \<le> sum (u \<sqinter> g)"
                using 2 11 minimum_spanning_forest_def by auto
            qed
          next
            have "?f \<le> f \<squnion> f\<^sup>T \<squnion> ?e"
              using conv_dist_inf inf_le1 sup_left_isotone sup_mono by presburger
            also have "... \<le> (?v \<sqinter> -?d \<sqinter> -?d\<^sup>T) \<squnion> (?v\<^sup>T \<sqinter> -?d \<sqinter> -?d\<^sup>T) \<squnion> ?e"
              using 17 sup_left_isotone by simp
            also have "... \<le> (?v \<sqinter> -?d) \<squnion> (?v\<^sup>T \<sqinter> -?d \<sqinter> -?d\<^sup>T) \<squnion> ?e"
              using inf.cobounded1 sup_inf_distrib2 by presburger
            also have "... = ?w \<squnion> (?v\<^sup>T \<sqinter> -?d \<sqinter> -?d\<^sup>T)"
              by (simp add: sup_assoc sup_commute)
            also have "... \<le> ?w \<squnion> (?v\<^sup>T \<sqinter> -?d\<^sup>T)"
              using inf.sup_right_isotone inf_assoc sup_right_isotone by simp
            also have "... \<le> ?w \<squnion> ?w\<^sup>T"
              using conv_complement conv_dist_inf conv_dist_sup sup_right_isotone by simp
            finally show "?f \<le> ?w \<squnion> ?w\<^sup>T"
              by simp
          qed
        qed
      next
        show "?n2 < n"
          using 1 kruskal_vc_2 kruskal_invariant_def by auto
      qed
    qed
  next
    show "\<not> ?e \<le> -?F \<longrightarrow> kruskal_invariant f g ?h \<and> ?n2 < n"
      using 1 kruskal_vc_2 kruskal_invariant_def by auto
  qed
next
  fix f g h
  assume 28: "kruskal_invariant f g h \<and> h = bot"
  hence 29: "spanning_forest f g"
    using kruskal_invariant_def kruskal_spanning_invariant_def by auto
  from 28 obtain w where 30: "minimum_spanning_forest w g \<and> f \<le> w \<squnion> w\<^sup>T"
    using kruskal_invariant_def by auto
  hence "w = w \<sqinter> --g"
    by (simp add: inf.absorb1 minimum_spanning_forest_def spanning_forest_def)
  also have "... \<le> w \<sqinter> components g"
    by (metis inf.sup_right_isotone star.circ_increasing)
  also have "... \<le> w \<sqinter> f\<^sup>T\<^sup>\<star> * f\<^sup>\<star>"
    using 29 spanning_forest_def inf.sup_right_isotone by simp
  also have "... \<le> f \<squnion> f\<^sup>T"
    apply (rule cancel_separate_6[where z=w and y="w\<^sup>T"])
    using 30 minimum_spanning_forest_def spanning_forest_def apply simp
    using 30 apply (metis conv_dist_inf conv_dist_sup conv_involutive inf.cobounded2 inf.orderE)
    using 30 apply (simp add: sup_commute)
    using 30 minimum_spanning_forest_def spanning_forest_def apply simp
    using 30 by (metis acyclic_star_below_complement comp_inf.mult_right_isotone inf_p le_bot minimum_spanning_forest_def spanning_forest_def)
  finally have 31: "w \<le> f \<squnion> f\<^sup>T"
    by simp
  have "sum (f \<sqinter> g) = sum ((w \<squnion> w\<^sup>T) \<sqinter> (f \<sqinter> g))"
    using 30 by (metis inf_absorb2 inf.assoc)
  also have "... = sum (w \<sqinter> (f \<sqinter> g)) + sum (w\<^sup>T \<sqinter> (f \<sqinter> g))"
    using 30 inf.commute acyclic_asymmetric sum_disjoint minimum_spanning_forest_def spanning_forest_def by simp
  also have "... = sum (w \<sqinter> (f \<sqinter> g)) + sum (w \<sqinter> (f\<^sup>T \<sqinter> g\<^sup>T))"
    by (metis conv_dist_inf conv_involutive sum_conv)
  also have "... = sum (f \<sqinter> (w \<sqinter> g)) + sum (f\<^sup>T \<sqinter> (w \<sqinter> g))"
    using 28 inf.commute inf.assoc kruskal_invariant_def kruskal_spanning_invariant_def by simp
  also have "... = sum ((f \<squnion> f\<^sup>T) \<sqinter> (w \<sqinter> g))"
    using 29 acyclic_asymmetric inf.sup_monoid.add_commute sum_disjoint spanning_forest_def by simp
  also have "... = sum (w \<sqinter> g)"
    using 31 by (metis inf_absorb2 inf.assoc)
  finally show "minimum_spanning_forest f g"
    using 29 30 minimum_spanning_forest_def by simp
qed

subsection \<open>Prim's Minimum Spanning Tree Algorithm\<close>

text \<open>
The total-correctness proof of Prim's minimum spanning tree algorithm has the same overall structure as the proof of Kruskal's algorithm.
The partial-correctness proof is discussed in \cite{Guttmann2016c,Guttmann2018a}.
\<close>

abbreviation "component g r \<equiv> r\<^sup>T * (--g)\<^sup>\<star>"
definition "spanning_tree t g r \<equiv> forest t \<and> t \<le> (component g r)\<^sup>T * (component g r) \<sqinter> --g \<and> component g r \<le> r\<^sup>T * t\<^sup>\<star> \<and> regular t"
definition "minimum_spanning_tree t g r \<equiv> spanning_tree t g r \<and> (\<forall>u . spanning_tree u g r \<longrightarrow> sum (t \<sqinter> g) \<le> sum (u \<sqinter> g))"
definition "prim_precondition g r \<equiv> g = g\<^sup>T \<and> injective r \<and> vector r \<and> regular r"
definition "prim_spanning_invariant t v g r \<equiv> prim_precondition g r \<and> v\<^sup>T = r\<^sup>T * t\<^sup>\<star> \<and> spanning_tree t (v * v\<^sup>T \<sqinter> g) r"
definition "prim_invariant t v g r \<equiv> prim_spanning_invariant t v g r \<and> (\<exists>w . minimum_spanning_tree w g r \<and> t \<le> w)"

lemma span_tree_split:
  assumes "vector r"
    shows "t \<le> (component g r)\<^sup>T * (component g r) \<sqinter> --g \<longleftrightarrow> (t \<le> (component g r)\<^sup>T \<and> t \<le> component g r \<and> t \<le> --g)"
proof -
  have "(component g r)\<^sup>T * (component g r) = (component g r)\<^sup>T \<sqinter> component g r"
    by (metis assms conv_involutive covector_mult_closed vector_conv_covector vector_covector)
  thus ?thesis
    by simp
qed

lemma span_tree_component:
  assumes "spanning_tree t g r"
    shows "component g r = component t r"
  using assms by (simp add: antisym mult_right_isotone star_isotone spanning_tree_def)

text \<open>
We first show three verification conditions which are used in both correctness proofs.
\<close>

lemma prim_vc_1:
  assumes "prim_precondition g r"
    shows "prim_spanning_invariant bot r g r"
proof (unfold prim_spanning_invariant_def, intro conjI)
  show "prim_precondition g r"
    using assms by simp
next
  show "r\<^sup>T = r\<^sup>T * bot\<^sup>\<star>"
    by (simp add: star_absorb)
next
  let ?ss = "r * r\<^sup>T \<sqinter> g"
  show "spanning_tree bot ?ss r"
  proof (unfold spanning_tree_def, intro conjI)
    show "injective bot"
      by simp
  next
    show "acyclic bot"
      by simp
  next
    show "bot \<le> (component ?ss r)\<^sup>T * (component ?ss r) \<sqinter> --?ss"
      by simp
  next
    have "component ?ss r \<le> component (r * r\<^sup>T) r"
      by (simp add: mult_right_isotone star_isotone)
    also have "... \<le> r\<^sup>T * 1\<^sup>\<star>"
      using assms by (metis inf.eq_iff p_antitone regular_one_closed star_sub_one prim_precondition_def)
    also have "... = r\<^sup>T * bot\<^sup>\<star>"
      by (simp add: star.circ_zero star_one)
    finally show "component ?ss r \<le> r\<^sup>T * bot\<^sup>\<star>"
      .
  next
    show "regular bot"
      by simp
  qed
qed

lemma prim_vc_2:
  assumes "prim_spanning_invariant t v g r"
      and "v * -v\<^sup>T \<sqinter> g \<noteq> bot"
      and "card { x . regular x \<and> x \<le> component g r \<and> x \<le> -v\<^sup>T } = n"
    shows "prim_spanning_invariant (t \<squnion> minarc (v * -v\<^sup>T \<sqinter> g)) (v \<squnion> minarc (v * -v\<^sup>T \<sqinter> g)\<^sup>T * top) g r \<and> card { x . regular x \<and> x \<le> component g r \<and> x \<le> -(v \<squnion> minarc (v * -v\<^sup>T \<sqinter> g)\<^sup>T * top)\<^sup>T } < n"
proof -
  let ?vcv = "v * -v\<^sup>T \<sqinter> g"
  let ?e = "minarc ?vcv"
  let ?t = "t \<squnion> ?e"
  let ?v = "v \<squnion> ?e\<^sup>T * top"
  let ?c = "component g r"
  let ?g = "--g"
  let ?n1 = "card { x . regular x \<and> x \<le> ?c \<and> x \<le> -v\<^sup>T }"
  let ?n2 = "card { x . regular x \<and> x \<le> ?c \<and> x \<le> -?v\<^sup>T }"
  have 1: "regular v \<and> regular (v * v\<^sup>T) \<and> regular (?v * ?v\<^sup>T) \<and> regular (top * ?e)"
    using assms(1) by (metis prim_spanning_invariant_def spanning_tree_def prim_precondition_def regular_conv_closed regular_closed_star regular_mult_closed conv_involutive regular_closed_top regular_closed_sup minarc_regular)
  hence 2: "t \<le> v * v\<^sup>T \<sqinter> ?g"
    using assms(1) by (metis prim_spanning_invariant_def spanning_tree_def inf_pp_commute inf.boundedE)
  hence 3: "t \<le> v * v\<^sup>T"
    by simp
  have 4: "t \<le> ?g"
    using 2 by simp
  have 5: "?e \<le> v * -v\<^sup>T \<sqinter> ?g"
    using 1 by (metis minarc_below pp_dist_inf regular_mult_closed regular_closed_p)
  hence 6: "?e \<le> v * -v\<^sup>T"
    by simp
  have 7: "vector v"
    using assms(1) prim_spanning_invariant_def prim_precondition_def by (simp add: covector_mult_closed vector_conv_covector)
  hence 8: "?e \<le> v"
    using 6 by (metis conv_complement inf.boundedE vector_complement_closed vector_covector)
  have 9: "?e * t = bot"
    using 3 6 7 et(1) by blast
  have 10: "?e * t\<^sup>T = bot"
    using 3 6 7 et(2) by simp
  have 11: "arc ?e"
    using assms(2) minarc_arc by simp
  have "r\<^sup>T \<le> r\<^sup>T * t\<^sup>\<star>"
    by (metis mult_right_isotone order_refl semiring.mult_not_zero star.circ_separate_mult_1 star_absorb)
  hence 12: "r\<^sup>T \<le> v\<^sup>T"
    using assms(1) by (simp add: prim_spanning_invariant_def)
  have 13: "vector r \<and> injective r \<and> v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
    using assms(1) prim_spanning_invariant_def prim_precondition_def minimum_spanning_tree_def spanning_tree_def reachable_restrict by simp
  have "g = g\<^sup>T"
    using assms(1) prim_invariant_def prim_spanning_invariant_def prim_precondition_def by simp
  hence 14: "?g\<^sup>T = ?g"
    using conv_complement by simp
  show "prim_spanning_invariant ?t ?v g r \<and> ?n2 < n"
  proof (rule conjI)
    show "prim_spanning_invariant ?t ?v g r"
    proof (unfold prim_spanning_invariant_def, intro conjI)
      show "prim_precondition g r"
        using assms(1) prim_spanning_invariant_def by simp
    next
      show "?v\<^sup>T = r\<^sup>T * ?t\<^sup>\<star>"
        using assms(1) 6 7 9 by (simp add: reachable_inv prim_spanning_invariant_def prim_precondition_def spanning_tree_def)
    next
      let ?G = "?v * ?v\<^sup>T \<sqinter> g"
      show "spanning_tree ?t ?G r"
      proof (unfold spanning_tree_def, intro conjI)
        show "injective ?t"
          using assms(1) 10 11 by (simp add: injective_inv prim_spanning_invariant_def spanning_tree_def)
      next
        show "acyclic ?t"
          using assms(1) 3 6 7 acyclic_inv prim_spanning_invariant_def spanning_tree_def by simp
      next
        show "?t \<le> (component ?G r)\<^sup>T * (component ?G r) \<sqinter> --?G"
          using 1 2 5 7 13 prim_subgraph_inv inf_pp_commute mst_subgraph_inv_2 by auto
      next
        show "component (?v * ?v\<^sup>T \<sqinter> g) r \<le> r\<^sup>T * ?t\<^sup>\<star>"
        proof -
          have 15: "r\<^sup>T * (v * v\<^sup>T \<sqinter> ?g)\<^sup>\<star> \<le> r\<^sup>T * t\<^sup>\<star>"
            using assms(1) 1 by (metis prim_spanning_invariant_def spanning_tree_def inf_pp_commute)
          have "component (?v * ?v\<^sup>T \<sqinter> g) r = r\<^sup>T * (?v * ?v\<^sup>T \<sqinter> ?g)\<^sup>\<star>"
            using 1 by simp
          also have "... \<le> r\<^sup>T * ?t\<^sup>\<star>"
            using 2 6 7 11 12 13 14 15 by (metis span_inv)
          finally show ?thesis
            .
        qed
      next
        show "regular ?t"
          using assms(1) by (metis prim_spanning_invariant_def spanning_tree_def regular_closed_sup minarc_regular)
      qed
    qed
  next
    have 16: "top * ?e \<le> ?c"
    proof -
      have "top * ?e = top * ?e\<^sup>T * ?e"
        using 11 by (metis arc_top_edge mult_assoc)
      also have "... \<le> v\<^sup>T * ?e"
        using 7 8 by (metis conv_dist_comp conv_isotone mult_left_isotone symmetric_top_closed)
      also have "... \<le> v\<^sup>T * ?g"
        using 5 mult_right_isotone by auto
      also have "... = r\<^sup>T * t\<^sup>\<star> * ?g"
        using 13 by simp
      also have "... \<le> r\<^sup>T * ?g\<^sup>\<star> * ?g"
        using 4 by (simp add: mult_left_isotone mult_right_isotone star_isotone)
      also have "... \<le> ?c"
        by (simp add: comp_associative mult_right_isotone star.right_plus_below_circ)
      finally show ?thesis
        by simp
    qed
    have 17: "top * ?e \<le> -v\<^sup>T"
      using 6 7 by (simp add: schroeder_4_p vTeT)
    have 18: "\<not> top * ?e \<le> -(top * ?e)"
      by (metis assms(2) inf.orderE minarc_bot_iff conv_complement_sub_inf inf_p inf_top.left_neutral p_bot symmetric_top_closed vector_top_closed)
    have 19: "-?v\<^sup>T = -v\<^sup>T \<sqinter> -(top * ?e)"
      by (simp add: conv_dist_comp conv_dist_sup)
    hence 20: "\<not> top * ?e \<le> -?v\<^sup>T"
      using 18 by simp
    have "?n2 < ?n1"
      apply (rule psubset_card_mono)
      using finite_regular apply simp
      using 1 16 17 19 20 by auto
    thus "?n2 < n"
      using assms(3) by simp
  qed
qed

lemma prim_vc_3:
  assumes "prim_spanning_invariant t v g r"
      and "v * -v\<^sup>T \<sqinter> g = bot"
    shows "spanning_tree t g r"
proof -
  let ?g = "--g"
  have 1: "regular v \<and> regular (v * v\<^sup>T)"
    using assms(1) by (metis prim_spanning_invariant_def spanning_tree_def prim_precondition_def regular_conv_closed regular_closed_star regular_mult_closed conv_involutive)
  have 2: "v * -v\<^sup>T \<sqinter> ?g = bot"
    using assms(2) pp_inf_bot_iff pp_pp_inf_bot_iff by simp
  have 3: "v\<^sup>T = r\<^sup>T * t\<^sup>\<star> \<and> vector v"
    using assms(1) by (simp add: covector_mult_closed prim_invariant_def prim_spanning_invariant_def vector_conv_covector prim_precondition_def)
  have 4: "t \<le> v * v\<^sup>T \<sqinter> ?g"
    using assms(1) 1 by (metis prim_spanning_invariant_def inf_pp_commute spanning_tree_def inf.boundedE)
  have "r\<^sup>T * (v * v\<^sup>T \<sqinter> ?g)\<^sup>\<star> \<le> r\<^sup>T * t\<^sup>\<star>"
    using assms(1) 1 by (metis prim_spanning_invariant_def inf_pp_commute spanning_tree_def)
  hence 5: "component g r = v\<^sup>T"
    using 1 2 3 4 by (metis span_post)
  have "regular (v * v\<^sup>T)"
    using assms(1) by (metis prim_spanning_invariant_def spanning_tree_def prim_precondition_def regular_conv_closed regular_closed_star regular_mult_closed conv_involutive)
  hence 6: "t \<le> v * v\<^sup>T \<sqinter> ?g"
    by (metis assms(1) prim_spanning_invariant_def spanning_tree_def inf_pp_commute inf.boundedE)
  show "spanning_tree t g r"
    apply (unfold spanning_tree_def, intro conjI)
    using assms(1) prim_spanning_invariant_def spanning_tree_def apply simp
    using assms(1) prim_spanning_invariant_def spanning_tree_def apply simp
    using 5 6 apply simp
    using assms(1) 5 prim_spanning_invariant_def apply simp
    using assms(1) prim_spanning_invariant_def spanning_tree_def by simp
qed

text \<open>
The following result shows that Prim's algorithm terminates and constructs a spanning tree.
We cannot yet show that this is a minimum spanning tree.
\<close>

theorem prim_spanning:
  "VARS t v e
  [ prim_precondition g r ]
  t := bot;
  v := r;
  WHILE v * -v\<^sup>T \<sqinter> g \<noteq> bot
    INV { prim_spanning_invariant t v g r }
    VAR { card { x . regular x \<and> x \<le> component g r \<sqinter> -v\<^sup>T } }
     DO e := minarc (v * -v\<^sup>T \<sqinter> g);
        t := t \<squnion> e;
        v := v \<squnion> e\<^sup>T * top
     OD
  [ spanning_tree t g r ]"
  apply vcg_tc_simp
  apply (simp add: prim_vc_1)
  using prim_vc_2 apply blast
  using prim_vc_3 by auto

text \<open>
Because we have shown total correctness, we conclude that a spanning tree exists.
\<close>

lemma prim_exists_spanning:
  "prim_precondition g r \<Longrightarrow> \<exists>t . spanning_tree t g r"
  using tc_extract_function prim_spanning by blast

text \<open>
This implies that a minimum spanning tree exists, which is used in the subsequent correctness proof.
\<close>

lemma prim_exists_minimal_spanning:
  assumes "prim_precondition g r"
    shows "\<exists>t . minimum_spanning_tree t g r"
proof -
  let ?s = "{ t . spanning_tree t g r }"
  have "\<exists>m\<in>?s . \<forall>z\<in>?s . sum (m \<sqinter> g) \<le> sum (z \<sqinter> g)"
    apply (rule finite_set_minimal)
    using finite_regular spanning_tree_def apply simp
    using assms prim_exists_spanning apply simp
    using sum_linear by simp
  thus ?thesis
    using minimum_spanning_tree_def by simp
qed

text \<open>
Prim's minimum spanning tree algorithm terminates and is correct.
This is the same algorithm that is used in the previous correctness proof, with the same precondition and variant, but with a different invariant and postcondition.
\<close>

theorem prim:
  "VARS t v e
  [ prim_precondition g r \<and> (\<exists>w . minimum_spanning_tree w g r) ]
  t := bot;
  v := r;
  WHILE v * -v\<^sup>T \<sqinter> g \<noteq> bot
    INV { prim_invariant t v g r }
    VAR { card { x . regular x \<and> x \<le> component g r \<sqinter> -v\<^sup>T } }
     DO e := minarc (v * -v\<^sup>T \<sqinter> g);
        t := t \<squnion> e;
        v := v \<squnion> e\<^sup>T * top
     OD
  [ minimum_spanning_tree t g r ]"
proof vcg_tc_simp
  assume "prim_precondition g r \<and> (\<exists>w . minimum_spanning_tree w g r)"
  thus "prim_invariant bot r g r"
    using prim_invariant_def prim_vc_1 by simp
next
  fix t v n
  let ?vcv = "v * -v\<^sup>T \<sqinter> g"
  let ?vv = "v * v\<^sup>T \<sqinter> g"
  let ?e = "minarc ?vcv"
  let ?t = "t \<squnion> ?e"
  let ?v = "v \<squnion> ?e\<^sup>T * top"
  let ?c = "component g r"
  let ?g = "--g"
  let ?n1 = "card { x . regular x \<and> x \<le> ?c \<and> x \<le> -v\<^sup>T }"
  let ?n2 = "card { x . regular x \<and> x \<le> ?c \<and> x \<le> -?v\<^sup>T }"
  assume 1: "prim_invariant t v g r \<and> ?vcv \<noteq> bot \<and> ?n1 = n"
  hence 2: "regular v \<and> regular (v * v\<^sup>T)"
    by (metis (no_types, hide_lams) prim_invariant_def prim_spanning_invariant_def spanning_tree_def prim_precondition_def regular_conv_closed regular_closed_star regular_mult_closed conv_involutive)
  have 3: "t \<le> v * v\<^sup>T \<sqinter> ?g"
    using 1 2 by (metis (no_types, hide_lams) prim_invariant_def prim_spanning_invariant_def spanning_tree_def inf_pp_commute inf.boundedE)
  hence 4: "t \<le> v * v\<^sup>T"
    by simp
  have 5: "t \<le> ?g"
    using 3 by simp
  have 6: "?e \<le> v * -v\<^sup>T \<sqinter> ?g"
    using 2 by (metis minarc_below pp_dist_inf regular_mult_closed regular_closed_p)
  hence 7: "?e \<le> v * -v\<^sup>T"
    by simp
  have 8: "vector v"
    using 1 prim_invariant_def prim_spanning_invariant_def prim_precondition_def by (simp add: covector_mult_closed vector_conv_covector)
  have 9: "arc ?e"
    using 1 minarc_arc by simp
  from 1 obtain w where 10: "minimum_spanning_tree w g r \<and> t \<le> w"
    by (metis prim_invariant_def)
  hence 11: "vector r \<and> injective r \<and> v\<^sup>T = r\<^sup>T * t\<^sup>\<star> \<and> forest w \<and> t \<le> w \<and> w \<le> ?c\<^sup>T * ?c \<sqinter> ?g \<and> r\<^sup>T * (?c\<^sup>T * ?c \<sqinter> ?g)\<^sup>\<star> \<le> r\<^sup>T * w\<^sup>\<star>"
    using 1 2 prim_invariant_def prim_spanning_invariant_def prim_precondition_def minimum_spanning_tree_def spanning_tree_def reachable_restrict by simp
  hence 12: "w * v \<le> v"
    using predecessors_reachable reachable_restrict by auto
  have 13: "g = g\<^sup>T"
    using 1 prim_invariant_def prim_spanning_invariant_def prim_precondition_def by simp
  hence 14: "?g\<^sup>T = ?g"
    using conv_complement by simp
  show "prim_invariant ?t ?v g r \<and> ?n2 < n"
  proof (unfold prim_invariant_def, intro conjI)
    show "prim_spanning_invariant ?t ?v g r"
      using 1 prim_invariant_def prim_vc_2 by blast
  next
    show "\<exists>w . minimum_spanning_tree w g r \<and> ?t \<le> w"
    proof
      let ?f = "w \<sqinter> v * -v\<^sup>T \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>"
      let ?p = "w \<sqinter> -v * -v\<^sup>T \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>"
      let ?fp = "w \<sqinter> -v\<^sup>T \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>"
      let ?w = "(w \<sqinter> -?fp) \<squnion> ?p\<^sup>T \<squnion> ?e"
      have 15: "regular ?f \<and> regular ?fp \<and> regular ?w"
        using 2 10 by (metis regular_conv_closed regular_closed_star regular_mult_closed regular_closed_top regular_closed_inf regular_closed_sup minarc_regular minimum_spanning_tree_def spanning_tree_def)
      show "minimum_spanning_tree ?w g r \<and> ?t \<le> ?w"
      proof (intro conjI)
        show "minimum_spanning_tree ?w g r"
        proof (unfold minimum_spanning_tree_def, intro conjI)
          show "spanning_tree ?w g r"
          proof (unfold spanning_tree_def, intro conjI)
            show "injective ?w"
              using 7 8 9 11 exchange_injective by blast
          next
            show "acyclic ?w"
              using 7 8 11 12 exchange_acyclic by blast
          next
            show "?w \<le> ?c\<^sup>T * ?c \<sqinter> --g"
            proof -
              have 16: "w \<sqinter> -?fp \<le> ?c\<^sup>T * ?c \<sqinter> --g"
                using 10 by (simp add: le_infI1 minimum_spanning_tree_def spanning_tree_def)
              have "?p\<^sup>T \<le> w\<^sup>T"
                by (simp add: conv_isotone inf.sup_monoid.add_assoc)
              also have "... \<le> (?c\<^sup>T * ?c \<sqinter> --g)\<^sup>T"
                using 11 conv_order by simp
              also have "... = ?c\<^sup>T * ?c \<sqinter> --g"
                using 2 14 conv_dist_comp conv_dist_inf by simp
              finally have 17: "?p\<^sup>T \<le> ?c\<^sup>T * ?c \<sqinter> --g"
                .
              have "?e \<le> ?c\<^sup>T * ?c \<sqinter> ?g"
                using 5 6 11 mst_subgraph_inv by auto
              thus ?thesis
                using 16 17 by simp
            qed
          next
            show "?c \<le> r\<^sup>T * ?w\<^sup>\<star>"
            proof -
              have "?c \<le> r\<^sup>T * w\<^sup>\<star>"
                using 10 minimum_spanning_tree_def spanning_tree_def by simp
              also have "... \<le> r\<^sup>T * ?w\<^sup>\<star>"
                using 4 7 8 10 11 12 15 by (metis mst_reachable_inv)
              finally show ?thesis
                .
            qed
          next
            show "regular ?w"
              using 15 by simp
          qed
        next
          have 18: "?f \<squnion> ?p = ?fp"
            using 2 8 epm_1 by fastforce
          have "arc (w \<sqinter> --v * -v\<^sup>T \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>)"
            using 5 6 8 9 11 12 reachable_restrict arc_edge by auto
          hence 19: "arc ?f"
            using 2 by simp
          hence "?f = bot \<longrightarrow> top = bot"
            by (metis mult_left_zero mult_right_zero)
          hence "?f \<noteq> bot"
            using 1 le_bot by auto
          hence "?f \<sqinter> v * -v\<^sup>T \<sqinter> ?g \<noteq> bot"
            using 2 11 by (simp add: inf.absorb1 le_infI1)
          hence "g \<sqinter> (?f \<sqinter> v * -v\<^sup>T) \<noteq> bot"
            using inf_commute pp_inf_bot_iff by simp
          hence 20: "?f \<sqinter> ?vcv \<noteq> bot"
            by (simp add: inf_assoc inf_commute)
          hence 21: "?f \<sqinter> g = ?f \<sqinter> ?vcv"
            using 2 by (simp add: inf_assoc inf_commute inf_left_commute)
          have 22: "?e \<sqinter> g = minarc ?vcv \<sqinter> ?vcv"
            using 7 by (simp add: inf.absorb2 inf.assoc inf.commute)
          hence 23: "sum (?e \<sqinter> g) \<le> sum (?f \<sqinter> g)"
            using 15 19 20 21 by (simp add: minarc_min)
          have "?e \<noteq> bot"
            using 20 comp_inf.semiring.mult_not_zero semiring.mult_not_zero by blast
          hence 24: "?e \<sqinter> g \<noteq> bot"
            using 22 minarc_meet_bot by auto
          have "sum (?w \<sqinter> g) = sum (w \<sqinter> -?fp \<sqinter> g) + sum (?p\<^sup>T \<sqinter> g) + sum (?e \<sqinter> g)"
            using 7 8 10 by (metis sum_disjoint_3 epm_8 epm_9 epm_10 minimum_spanning_tree_def spanning_tree_def)
          also have "... = sum (((w \<sqinter> -?fp) \<squnion> ?p\<^sup>T) \<sqinter> g) + sum (?e \<sqinter> g)"
            using 11 by (metis epm_8 sum_disjoint)
          also have "... \<le> sum (((w \<sqinter> -?fp) \<squnion> ?p\<^sup>T) \<sqinter> g) + sum (?f \<sqinter> g)"
            using 23 24 by (simp add: sum_plus_right_isotone)
          also have "... = sum (w \<sqinter> -?fp \<sqinter> g) + sum (?p\<^sup>T \<sqinter> g) + sum (?f \<sqinter> g)"
            using 11 by (metis epm_8 sum_disjoint)
          also have "... = sum (w \<sqinter> -?fp \<sqinter> g) + sum (?p \<sqinter> g) + sum (?f \<sqinter> g)"
            using 13 sum_symmetric by auto
          also have "... = sum (((w \<sqinter> -?fp) \<squnion> ?p \<squnion> ?f) \<sqinter> g)"
            using 2 8 by (metis sum_disjoint_3 epm_11 epm_12 epm_13)
          also have "... = sum (w \<sqinter> g)"
            using 2 8 15 18 epm_2 by force
          finally have "sum (?w \<sqinter> g) \<le> sum (w \<sqinter> g)"
            .
          thus "\<forall>u . spanning_tree u g r \<longrightarrow> sum (?w \<sqinter> g) \<le> sum (u \<sqinter> g)"
            using 10 order_lesseq_imp minimum_spanning_tree_def by auto
        qed
      next
        show "?t \<le> ?w"
          using 4 8 10 mst_extends_new_tree by simp
      qed
    qed
  next
    show "?n2 < n"
      using 1 prim_invariant_def prim_vc_2 by auto
  qed
next
  fix t v
  let ?g = "--g"
  assume 25: "prim_invariant t v g r \<and> v * -v\<^sup>T \<sqinter> g = bot"
  hence 26: "regular v"
    by (metis prim_invariant_def prim_spanning_invariant_def spanning_tree_def prim_precondition_def regular_conv_closed regular_closed_star regular_mult_closed conv_involutive)
  from 25 obtain w where 27: "minimum_spanning_tree w g r \<and> t \<le> w"
    by (metis prim_invariant_def)
  have "spanning_tree t g r"
    using 25 prim_invariant_def prim_vc_3 by blast
  hence "component g r = v\<^sup>T"
    by (metis 25 prim_invariant_def span_tree_component prim_spanning_invariant_def spanning_tree_def)
  hence 28: "w \<le> v * v\<^sup>T"
    using 26 27 by (simp add: minimum_spanning_tree_def spanning_tree_def inf_pp_commute)
  have "vector r \<and> injective r \<and> forest w"
    using 25 27 by (simp add: prim_invariant_def prim_spanning_invariant_def prim_precondition_def minimum_spanning_tree_def spanning_tree_def)
  hence "w = t"
    using 25 27 28 prim_invariant_def prim_spanning_invariant_def mst_post by blast
  thus "minimum_spanning_tree t g r"
    using 27 by simp
qed

end

end

