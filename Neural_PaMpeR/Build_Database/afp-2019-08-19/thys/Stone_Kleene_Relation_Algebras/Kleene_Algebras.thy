(* Title:      Kleene Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Kleene Algebras\<close>

text \<open>
Kleene algebras have been axiomatised by Kozen to describe the equational theory of regular languages \cite{Kozen1994}.
Binary relations are another important model.
This theory implements variants of Kleene algebras based on idempotent left semirings \cite{Moeller2007}.
The weakening of some semiring axioms allows the treatment of further computation models.
The presented algebras are special cases of iterings, so many results can be inherited.
\<close>

theory Kleene_Algebras

imports Iterings

begin

text \<open>
We start with left Kleene algebras, which use the left unfold and left induction axioms of Kleene algebras.
\<close>

class star =
  fixes star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [100] 100)

class left_kleene_algebra = idempotent_left_semiring + star +
  assumes star_left_unfold : "1 \<squnion> y * y\<^sup>\<star> \<le> y\<^sup>\<star>"
  assumes star_left_induct : "z \<squnion> y * x \<le> x \<longrightarrow> y\<^sup>\<star> * z \<le> x"
begin

no_notation
  trancl ("(_\<^sup>+)" [1000] 999)

abbreviation tc ("_\<^sup>+" [100] 100) where "tc x \<equiv> x * x\<^sup>\<star>"

lemma star_left_unfold_equal:
  "1 \<squnion> x * x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis sup_right_isotone antisym mult_right_isotone mult_1_right star_left_induct star_left_unfold)

text \<open>
This means that for some properties of Kleene algebras, only one inequality can be derived, as exemplified by the following sliding rule.
\<close>

lemma star_left_slide:
  "(x * y)\<^sup>\<star> * x \<le> x * (y * x)\<^sup>\<star>"
  by (metis mult_assoc mult_left_sub_dist_sup mult_1_right star_left_induct star_left_unfold_equal)

lemma star_isotone:
  "x \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
  by (metis sup_right_isotone mult_left_isotone order_trans star_left_unfold mult_1_right star_left_induct)

lemma star_sup_1:
  "(x \<squnion> y)\<^sup>\<star> = x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star>"
proof (rule antisym)
  have "y * x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star> \<le> (y * x\<^sup>\<star>)\<^sup>\<star>"
    using sup_right_divisibility star_left_unfold_equal by auto
  also have "... \<le> x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star>"
    using mult_left_isotone sup_left_divisibility star_left_unfold_equal by fastforce
  finally have "(x \<squnion> y) * (x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star>) \<le> x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star>"
    by (metis le_supI mult_right_dist_sup mult_right_sub_dist_sup_right mult_assoc star_left_unfold_equal)
  hence "1 \<squnion> (x \<squnion> y) * (x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star>) \<le> x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star>"
    using reflexive_mult_closed star_left_unfold by auto
  thus "(x \<squnion> y)\<^sup>\<star> \<le> x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star>"
    using star_left_induct by force
next
  have "x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> * (y * (x \<squnion> y)\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: mult_right_isotone star_isotone)
  also have "... \<le> x\<^sup>\<star> * ((x \<squnion> y) * (x \<squnion> y)\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: mult_right_isotone mult_right_sub_dist_sup_right star_isotone)
  also have "... \<le> x\<^sup>\<star> * (x \<squnion> y)\<^sup>\<star>\<^sup>\<star>"
    using mult_right_isotone star_left_unfold star_isotone by auto
  also have "... \<le> (x \<squnion> y)\<^sup>\<star> * (x \<squnion> y)\<^sup>\<star>\<^sup>\<star>"
    by (simp add: mult_left_isotone star_isotone)
  also have "... \<le> (x \<squnion> y)\<^sup>\<star>"
    by (metis sup.bounded_iff mult_1_right star_left_induct star_left_unfold)
  finally show "x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star> \<le> (x \<squnion> y)\<^sup>\<star>"
    by simp
qed

end

text \<open>
We now show that left Kleene algebras form iterings.
A sublocale is used instead of a subclass, because iterings use a different iteration operation.
\<close>

sublocale left_kleene_algebra < star: left_conway_semiring where circ = star
  apply unfold_locales
  apply (rule star_left_unfold_equal)
  apply (rule star_left_slide)
  by (rule star_sup_1)

context left_kleene_algebra
begin

text \<open>
A number of lemmas in this class are taken from Georg Struth's Kleene algebra theory \cite{ArmstrongGomesStruthWeber2016}.
\<close>

lemma star_sub_one:
  "x \<le> 1 \<Longrightarrow> x\<^sup>\<star> = 1"
  by (metis sup_right_isotone eq_iff le_iff_sup mult_1_right star.circ_plus_one star_left_induct)

lemma star_one:
  "1\<^sup>\<star> = 1"
  by (simp add: star_sub_one)

lemma star_left_induct_mult:
  "x * y \<le> y \<Longrightarrow> x\<^sup>\<star> * y \<le> y"
  by (simp add: star_left_induct)

lemma star_left_induct_mult_iff:
  "x * y \<le> y \<longleftrightarrow> x\<^sup>\<star> * y \<le> y"
  using mult_left_isotone order_trans star.circ_increasing star_left_induct_mult by blast

lemma star_involutive:
  "x\<^sup>\<star> = x\<^sup>\<star>\<^sup>\<star>"
  using star.circ_circ_sup star_sup_1 star_one by auto

lemma star_sup_one:
  "(1 \<squnion> x)\<^sup>\<star> = x\<^sup>\<star>"
  using star.circ_circ_sup star_involutive by auto

lemma star_left_induct_equal:
  "z \<squnion> x * y = y \<Longrightarrow> x\<^sup>\<star> * z \<le> y"
  by (simp add: star_left_induct)

lemma star_left_induct_mult_equal:
  "x * y = y \<Longrightarrow> x\<^sup>\<star> * y \<le> y"
  by (simp add: star_left_induct_mult)

lemma star_star_upper_bound:
  "x\<^sup>\<star> \<le> z\<^sup>\<star> \<Longrightarrow> x\<^sup>\<star>\<^sup>\<star> \<le> z\<^sup>\<star>"
  using star_involutive by auto

lemma star_simulation_left:
  assumes "x * z \<le> z * y"
    shows "x\<^sup>\<star> * z \<le> z * y\<^sup>\<star>"
proof -
  have "x * z * y\<^sup>\<star> \<le> z * y * y\<^sup>\<star>"
    by (simp add: assms mult_left_isotone)
  also have "... \<le> z * y\<^sup>\<star>"
    by (simp add: mult_right_isotone star.left_plus_below_circ mult_assoc)
  finally have "z \<squnion> x * z * y\<^sup>\<star> \<le> z * y\<^sup>\<star>"
    using star.circ_back_loop_prefixpoint by auto
  thus ?thesis
    by (simp add: star_left_induct mult_assoc)
qed

lemma quasicomm_1:
  "y * x \<le> x * (x \<squnion> y)\<^sup>\<star> \<longleftrightarrow> y\<^sup>\<star> * x \<le> x * (x \<squnion> y)\<^sup>\<star>"
  by (metis mult_isotone order_refl order_trans star.circ_increasing star_involutive star_simulation_left)

lemma star_rtc_3:
  "1 \<squnion> x \<squnion> y * y = y \<Longrightarrow> x\<^sup>\<star> \<le> y"
  by (metis sup.bounded_iff le_iff_sup mult_left_sub_dist_sup_left mult_1_right star_left_induct_mult_iff star.circ_sub_dist)

lemma star_decompose_1:
  "(x \<squnion> y)\<^sup>\<star> = (x\<^sup>\<star> * y\<^sup>\<star>)\<^sup>\<star>"
  apply (rule antisym)
  apply (simp add: star.circ_sup_2)
  using star.circ_sub_dist_3 star_isotone star_involutive by fastforce

lemma star_sum:
  "(x \<squnion> y)\<^sup>\<star> = (x\<^sup>\<star> \<squnion> y\<^sup>\<star>)\<^sup>\<star>"
  using star_decompose_1 star_involutive by auto

lemma star_decompose_3:
  "(x\<^sup>\<star> * y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star>"
  using star_sup_1 star_decompose_1 by auto

text \<open>
In contrast to iterings, we now obtain that the iteration operation results in least fixpoints.
\<close>

lemma star_loop_least_fixpoint:
  "y * x \<squnion> z = x \<Longrightarrow> y\<^sup>\<star> * z \<le> x"
  by (simp add: sup_commute star_left_induct_equal)

lemma star_loop_is_least_fixpoint:
  "is_least_fixpoint (\<lambda>x . y * x \<squnion> z) (y\<^sup>\<star> * z)"
  by (simp add: is_least_fixpoint_def star.circ_loop_fixpoint star_loop_least_fixpoint)

lemma star_loop_mu:
  "\<mu> (\<lambda>x . y * x \<squnion> z) = y\<^sup>\<star> * z"
  by (metis least_fixpoint_same star_loop_is_least_fixpoint)

lemma affine_has_least_fixpoint:
  "has_least_fixpoint (\<lambda>x . y * x \<squnion> z)"
  by (metis has_least_fixpoint_def star_loop_is_least_fixpoint)

lemma star_outer_increasing:
  "x \<le> y\<^sup>\<star> * x * y\<^sup>\<star>"
  by (metis star.circ_back_loop_prefixpoint star.circ_loop_fixpoint sup.boundedE)

(*
lemma circ_sup: "(x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star> = (x \<squnion> y)\<^sup>\<star>" nitpick [expect=genuine,card=7] oops
lemma circ_mult: "1 \<squnion> x * (y * x)\<^sup>\<star> * y = (x * y)\<^sup>\<star>" nitpick [expect=genuine] oops
lemma circ_plus_same: "x\<^sup>\<star> * x = x * x\<^sup>\<star>" nitpick [expect=genuine] oops
lemma circ_unfold_sum: "(x \<squnion> y)\<^sup>\<star> = x\<^sup>\<star> \<squnion> x\<^sup>\<star> * y * (x \<squnion> y)\<^sup>\<star>" nitpick [expect=genuine,card=7] oops
lemma mult_zero_sup_circ_2: "(x \<squnion> y * bot)\<^sup>\<star> = x\<^sup>\<star> \<squnion> x\<^sup>\<star> * y * bot" nitpick [expect=genuine,card=7] oops
lemma circ_simulate_left: "x * z \<le> z * y \<squnion> w \<longrightarrow> x\<^sup>\<star> * z \<le> (z \<squnion> x\<^sup>\<star> * w) * y\<^sup>\<star>" nitpick [expect=genuine] oops
lemma circ_simulate_1: "y * x \<le> x * y \<longrightarrow> y\<^sup>\<star> * x\<^sup>\<star> \<le> x\<^sup>\<star> * y\<^sup>\<star>" nitpick [expect=genuine,card=7] oops
lemma circ_separate_1: "y * x \<le> x * y \<longrightarrow> (x \<squnion> y)\<^sup>\<star> = x\<^sup>\<star> * y\<^sup>\<star>" nitpick [expect=genuine,card=7] oops
lemma atomicity_refinement: "s = s * q \<and> x = q * x \<and> q * b = bot \<and> r * b \<le> b * r \<and> r * l \<le> l * r \<and> x * l \<le> l * x \<and> b * l \<le> l * b \<and> q * l \<le> l * q \<and> r\<^sup>\<star> * q \<le> q * r\<^sup>\<star> \<and> q \<le> 1 \<longrightarrow> s * (x \<squnion> b \<squnion> r \<squnion> l)\<^sup>\<star> * q \<le> s * (x * b\<^sup>\<star> * q \<squnion> r \<squnion> l)\<^sup>\<star>" nitpick [expect=genuine] oops
lemma circ_simulate_left_plus: "x * z \<le> z * y\<^sup>\<star> \<squnion> w \<longrightarrow> x\<^sup>\<star> * z \<le> (z \<squnion> x\<^sup>\<star> * w) * y\<^sup>\<star>" nitpick [expect=genuine] oops
lemma circ_separate_unfold: "(y * x\<^sup>\<star>)\<^sup>\<star> = y\<^sup>\<star> \<squnion> y\<^sup>\<star> * y * x * x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star>" nitpick [expect=genuine] oops
lemma separation: "y * x \<le> x * y\<^sup>\<star> \<longrightarrow> (x \<squnion> y)\<^sup>\<star> = x\<^sup>\<star> * y\<^sup>\<star>" nitpick [expect=genuine,card=7] oops
lemma circ_simulate_4: "y * x \<le> x * x\<^sup>\<star> * (1 \<squnion> y) \<longrightarrow> y\<^sup>\<star> * x\<^sup>\<star> \<le> x\<^sup>\<star> * y\<^sup>\<star>" nitpick [expect=genuine,card=7] oops
lemma circ_simulate_5: "y * x \<le> x * x\<^sup>\<star> * (x \<squnion> y) \<longrightarrow> y\<^sup>\<star> * x\<^sup>\<star> \<le> x\<^sup>\<star> * y\<^sup>\<star>" nitpick [expect=genuine,card=7] oops
lemma circ_simulate_6: "y * x \<le> x * (x \<squnion> y) \<longrightarrow> y\<^sup>\<star> * x\<^sup>\<star> \<le> x\<^sup>\<star> * y\<^sup>\<star>" nitpick [expect=genuine,card=7] oops
lemma circ_separate_4: "y * x \<le> x * x\<^sup>\<star> * (1 \<squnion> y) \<longrightarrow> (x \<squnion> y)\<^sup>\<star> = x\<^sup>\<star> * y\<^sup>\<star>" nitpick [expect=genuine,card=7] oops
lemma circ_separate_5: "y * x \<le> x * x\<^sup>\<star> * (x \<squnion> y) \<longrightarrow> (x \<squnion> y)\<^sup>\<star> = x\<^sup>\<star> * y\<^sup>\<star>" nitpick [expect=genuine,card=7] oops
lemma circ_separate_6: "y * x \<le> x * (x \<squnion> y) \<longrightarrow> (x \<squnion> y)\<^sup>\<star> = x\<^sup>\<star> * y\<^sup>\<star>" nitpick [expect=genuine,card=7] oops
*)

end

text \<open>
We next add the right induction rule, which allows us to strengthen many inequalities of left Kleene algebras to equalities.
\<close>

class strong_left_kleene_algebra = left_kleene_algebra +
  assumes star_right_induct: "z \<squnion> x * y \<le> x \<longrightarrow> z * y\<^sup>\<star> \<le> x"
begin

lemma star_plus:
  "y\<^sup>\<star> * y = y * y\<^sup>\<star>"
proof (rule antisym)
  show "y\<^sup>\<star> * y \<le> y * y\<^sup>\<star>"
    by (simp add: star.circ_plus_sub)
next
  have "y\<^sup>\<star> * y * y \<le> y\<^sup>\<star> * y"
    by (simp add: mult_left_isotone star.right_plus_below_circ)
  hence "y \<squnion> y\<^sup>\<star> * y * y \<le> y\<^sup>\<star> * y"
    by (simp add: star.circ_mult_increasing_2)
  thus "y * y\<^sup>\<star> \<le> y\<^sup>\<star> * y"
    using star_right_induct by blast
qed

lemma star_slide:
  "(x * y)\<^sup>\<star> * x = x * (y * x)\<^sup>\<star>"
proof (rule antisym)
  show "(x * y)\<^sup>\<star> * x \<le> x * (y * x)\<^sup>\<star>"
    by (rule star_left_slide)
next
  have "x \<squnion> (x * y)\<^sup>\<star> * x * y * x \<le> (x * y)\<^sup>\<star> * x"
    by (metis (full_types) sup.commute eq_refl star.circ_loop_fixpoint mult.assoc star_plus)
  thus "x * (y * x)\<^sup>\<star> \<le> (x * y)\<^sup>\<star> * x"
    by (simp add: mult_assoc star_right_induct)
qed

lemma star_simulation_right:
  assumes "z * x \<le> y * z"
    shows "z * x\<^sup>\<star> \<le> y\<^sup>\<star> * z"
proof -
  have "y\<^sup>\<star> * z * x \<le> y\<^sup>\<star> * z"
    by (metis assms dual_order.trans mult_isotone mult_left_sub_dist_sup_right star.circ_loop_fixpoint star.circ_transitive_equal sup.cobounded1 mult_assoc)
  thus ?thesis
    by (metis le_supI star.circ_loop_fixpoint star_right_induct sup.cobounded2)
qed

end

text \<open>
Again we inherit results from the itering hierarchy.
\<close>

sublocale strong_left_kleene_algebra < star: itering_1 where circ = star
  apply unfold_locales
  apply (simp add: star_slide)
  by (simp add: star_simulation_right)

context strong_left_kleene_algebra
begin

lemma star_right_induct_mult:
  "y * x \<le> y \<Longrightarrow> y * x\<^sup>\<star> \<le> y"
  by (simp add: star_right_induct)

lemma star_right_induct_mult_iff:
  "y * x \<le> y \<longleftrightarrow> y * x\<^sup>\<star> \<le> y"
  using mult_right_isotone order_trans star.circ_increasing star_right_induct_mult by blast

lemma star_simulation_right_equal:
  "z * x = y * z \<Longrightarrow> z * x\<^sup>\<star> = y\<^sup>\<star> * z"
  by (metis eq_iff star_simulation_left star_simulation_right)

lemma star_simulation_star:
  "x * y \<le> y * x \<Longrightarrow> x\<^sup>\<star> * y\<^sup>\<star> \<le> y\<^sup>\<star> * x\<^sup>\<star>"
  by (simp add: star_simulation_left star_simulation_right)

lemma star_right_induct_equal:
  "z \<squnion> y * x = y \<Longrightarrow> z * x\<^sup>\<star> \<le> y"
  by (simp add: star_right_induct)

lemma star_right_induct_mult_equal:
  "y * x = y \<Longrightarrow> y * x\<^sup>\<star> \<le> y"
  by (simp add: star_right_induct_mult)

lemma star_back_loop_least_fixpoint:
  "x * y \<squnion> z = x \<Longrightarrow> z * y\<^sup>\<star> \<le> x"
  by (simp add: sup_commute star_right_induct_equal)

lemma star_back_loop_is_least_fixpoint:
  "is_least_fixpoint (\<lambda>x . x * y \<squnion> z) (z * y\<^sup>\<star>)"
proof (unfold is_least_fixpoint_def, rule conjI)
  have "(z * y\<^sup>\<star> * y \<squnion> z) * y \<le> z * y\<^sup>\<star> * y \<squnion> z"
    using le_supI1 mult_left_isotone star.circ_back_loop_prefixpoint by auto
  hence "z * y\<^sup>\<star> \<le> z * y\<^sup>\<star> * y \<squnion> z"
    by (simp add: star_right_induct)
  thus "z * y\<^sup>\<star> * y \<squnion> z = z * y\<^sup>\<star>"
    using antisym star.circ_back_loop_prefixpoint by auto
next
  show "\<forall>x. x * y \<squnion> z = x \<longrightarrow> z * y\<^sup>\<star> \<le> x"
    by (simp add: star_back_loop_least_fixpoint)
qed

lemma star_back_loop_mu:
  "\<mu> (\<lambda>x . x * y \<squnion> z) = z * y\<^sup>\<star>"
  by (metis least_fixpoint_same star_back_loop_is_least_fixpoint)

lemma star_square:
  "x\<^sup>\<star> = (1 \<squnion> x) * (x * x)\<^sup>\<star>"
proof -
  let ?f = "\<lambda>y . y * x \<squnion> 1"
  have 1: "isotone ?f"
    by (metis sup_left_isotone isotone_def mult_left_isotone)
  have "?f \<circ> ?f = (\<lambda>y . y * (x * x) \<squnion> (1 \<squnion> x))"
    by (simp add: sup_assoc sup_commute mult_assoc mult_right_dist_sup o_def)
  thus ?thesis
    using 1 by (metis mu_square mult_left_one star_back_loop_mu has_least_fixpoint_def star_back_loop_is_least_fixpoint)
qed

lemma star_square_2:
  "x\<^sup>\<star> = (x * x)\<^sup>\<star> * (x \<squnion> 1)"
proof -
  have "(1 \<squnion> x) * (x * x)\<^sup>\<star> = (x * x)\<^sup>\<star> * 1 \<squnion> x * (x * x)\<^sup>\<star>"
    using mult_right_dist_sup by force
  thus ?thesis
    by (metis (no_types) antisym mult_left_sub_dist_sup star.circ_square_2 star_slide sup_commute star_square)
qed

lemma star_circ_simulate_right_plus:
  assumes "z * x \<le> y * y\<^sup>\<star> * z \<squnion> w"
    shows "z * x\<^sup>\<star> \<le> y\<^sup>\<star> * (z \<squnion> w * x\<^sup>\<star>)"
proof -
  have "(z \<squnion> w * x\<^sup>\<star>) * x \<le> z * x \<squnion> w * x\<^sup>\<star>"
    using mult_right_dist_sup star.circ_back_loop_prefixpoint sup_right_isotone by auto
  also have "... \<le> y * y\<^sup>\<star> * z \<squnion> w \<squnion> w * x\<^sup>\<star>"
    using assms sup_left_isotone by blast
  also have "... \<le> y * y\<^sup>\<star> * z \<squnion> w * x\<^sup>\<star>"
    using le_supI1 star.circ_back_loop_prefixpoint sup_commute by auto
  also have "... \<le> y\<^sup>\<star> * (z \<squnion> w * x\<^sup>\<star>)"
    by (metis sup.bounded_iff mult_isotone mult_left_isotone mult_left_one mult_left_sub_dist_sup_left star.circ_reflexive star.left_plus_below_circ)
  finally have "y\<^sup>\<star> * (z \<squnion> w * x\<^sup>\<star>) * x \<le> y\<^sup>\<star> * (z \<squnion> w * x\<^sup>\<star>)"
    by (metis mult_assoc mult_right_isotone star.circ_transitive_equal)
  thus ?thesis
    by (metis sup.bounded_iff star_right_induct mult_left_sub_dist_sup_left star.circ_loop_fixpoint)
qed

lemma transitive_star:
  "x * x \<le> x \<Longrightarrow> x\<^sup>\<star> = 1 \<squnion> x"
  by (metis order.antisym star.circ_mult_increasing_2 star.circ_plus_same star_left_induct_mult star_left_unfold_equal)

(*
lemma star_circ_simulate_left_plus: "x * z \<le> z * y\<^sup>\<star> \<squnion> w \<longrightarrow> x\<^sup>\<star> * z \<le> (z \<squnion> x\<^sup>\<star> * w) * y\<^sup>\<star>" nitpick [expect=genuine,card=7] oops
*)

end

text \<open>
The following class contains a generalisation of Kleene algebras, which lacks the right zero axiom.
\<close>

class left_zero_kleene_algebra = idempotent_left_zero_semiring + strong_left_kleene_algebra
begin

lemma star_star_absorb:
  "y\<^sup>\<star> * (y\<^sup>\<star> * x)\<^sup>\<star> * y\<^sup>\<star> = (y\<^sup>\<star> * x)\<^sup>\<star> * y\<^sup>\<star>"
  by (metis star.circ_transitive_equal star_slide mult_assoc)

lemma star_circ_simulate_left_plus:
  assumes "x * z \<le> z * y\<^sup>\<star> \<squnion> w"
    shows "x\<^sup>\<star> * z \<le> (z \<squnion> x\<^sup>\<star> * w) * y\<^sup>\<star>"
proof -
  have "x * (x\<^sup>\<star> * (w * y\<^sup>\<star>)) \<le> x\<^sup>\<star> * (w * y\<^sup>\<star>)"
    by (metis (no_types) mult_right_sub_dist_sup_left star.circ_loop_fixpoint mult_assoc)
  hence "x * ((z \<squnion> x\<^sup>\<star> * w) * y\<^sup>\<star>) \<le> x * z * y\<^sup>\<star> \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    using mult_left_dist_sup mult_right_dist_sup sup_right_isotone mult_assoc by presburger
  also have "... \<le> (z * y\<^sup>\<star> \<squnion> w) * y\<^sup>\<star> \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    using assms mult_isotone semiring.add_right_mono by blast
  also have "... = z * y\<^sup>\<star> \<squnion> w * y\<^sup>\<star> \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (simp add: mult_right_dist_sup star.circ_transitive_equal mult_assoc)
  also have "... = (z \<squnion> w \<squnion> x\<^sup>\<star> * w) * y\<^sup>\<star>"
    by (simp add: mult_right_dist_sup)
  also have "... = (z \<squnion> x\<^sup>\<star> * w) * y\<^sup>\<star>"
    by (metis sup_assoc sup_ge2 le_iff_sup star.circ_loop_fixpoint)
  finally show ?thesis
    by (metis sup.bounded_iff mult_left_sub_dist_sup_left mult_1_right star.circ_right_unfold_1 star_left_induct)
qed

lemma star_one_sup_below:
  "x * y\<^sup>\<star> * (1 \<squnion> z) \<le> x * (y \<squnion> z)\<^sup>\<star>"
proof -
  have "y\<^sup>\<star> * z \<le> (y \<squnion> z)\<^sup>\<star>"
    using sup_ge2 order_trans star.circ_increasing star.circ_mult_upper_bound star.circ_sub_dist by blast
  hence "y\<^sup>\<star> \<squnion> y\<^sup>\<star> * z \<le> (y \<squnion> z)\<^sup>\<star>"
    by (simp add: star.circ_sup_upper_bound star.circ_sub_dist)
  hence "y\<^sup>\<star> * (1 \<squnion> z) \<le> (y \<squnion> z)\<^sup>\<star>"
    by (simp add: mult_left_dist_sup)
  thus ?thesis
    by (metis mult_right_isotone mult_assoc)
qed

text \<open>
The following theorem is similar to the puzzle where persons insert themselves always in the middle between two groups of people in a line.
Here, however, items in the middle annihilate each other, leaving just one group of items behind.
\<close>

lemma cancel_separate:
  assumes "x * y \<le> 1"
    shows "x\<^sup>\<star> * y\<^sup>\<star> \<le> x\<^sup>\<star> \<squnion> y\<^sup>\<star>"
proof -
  have "x * y\<^sup>\<star> = x \<squnion> x * y * y\<^sup>\<star>"
    by (metis mult_assoc mult_left_dist_sup mult_1_right star_left_unfold_equal)
  also have "... \<le> x \<squnion> y\<^sup>\<star>"
    by (meson assms dual_order.trans order.refl star.circ_mult_upper_bound star.circ_reflexive sup_right_isotone)
  also have "... \<le> x\<^sup>\<star> \<squnion> y\<^sup>\<star>"
    using star.circ_increasing sup_left_isotone by auto
  finally have 1: "x * y\<^sup>\<star> \<le> x\<^sup>\<star> \<squnion> y\<^sup>\<star>"
    .
  have "x * (x\<^sup>\<star> \<squnion> y\<^sup>\<star>) = x * x\<^sup>\<star> \<squnion> x * y\<^sup>\<star>"
    by (simp add: mult_left_dist_sup)
  also have "... \<le> x\<^sup>\<star> \<squnion> y\<^sup>\<star>"
    using 1 by (metis sup.bounded_iff sup_ge1 order_trans star.left_plus_below_circ)
  finally have 2: "x * (x\<^sup>\<star> \<squnion> y\<^sup>\<star>) \<le> x\<^sup>\<star> \<squnion> y\<^sup>\<star>"
    .
  have "y\<^sup>\<star> \<le> x\<^sup>\<star> \<squnion> y\<^sup>\<star>"
    by simp
  hence "y\<^sup>\<star> \<squnion> x * (x\<^sup>\<star> \<squnion> y\<^sup>\<star>) \<le> x\<^sup>\<star> \<squnion> y\<^sup>\<star>"
    using 2 sup.bounded_iff by blast
  thus ?thesis
    by (metis star_left_induct)
qed

lemma star_separate:
  assumes "x * y = bot"
      and "y * y = bot"
    shows "(x \<squnion> y)\<^sup>\<star> = x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>"
proof -
  have 1: "y\<^sup>\<star> = 1 \<squnion> y"
    using assms(2) by (simp add: transitive_star)
  have "(x \<squnion> y)\<^sup>\<star> = y\<^sup>\<star> * (x * y\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: star.circ_decompose_6 star_sup_1)
  also have "... = y\<^sup>\<star> * (x * (1 \<squnion> y * y\<^sup>\<star>))\<^sup>\<star>"
    by (simp add: star_left_unfold_equal)
  also have "... = (1 \<squnion> y) * x\<^sup>\<star>"
    using 1 by (simp add: assms mult_left_dist_sup)
  also have "... = x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>"
    by (simp add: mult_right_dist_sup)
  finally show ?thesis
    .
qed

end

text \<open>
We can now inherit from the strongest variant of iterings.
\<close>

sublocale left_zero_kleene_algebra < star: itering where circ = star
  apply unfold_locales
  apply (metis star.circ_sup_9)
  apply (metis star.circ_mult_1)
  apply (simp add: star_circ_simulate_right_plus)
  by (simp add: star_circ_simulate_left_plus)

context left_zero_kleene_algebra
begin

lemma star_absorb:
  "x * y = bot \<Longrightarrow> x * y\<^sup>\<star> = x"
  by (metis sup.bounded_iff antisym_conv star.circ_back_loop_prefixpoint star.circ_elimination)

lemma star_separate_2:
  assumes "x * z\<^sup>+ * y = bot"
      and "y * z\<^sup>+ * y = bot"
      and "z * x = bot"
    shows "(x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * (z * (1 \<squnion> y * x\<^sup>\<star>))\<^sup>\<star> = z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>\<star>"
proof -
  have 1: "x\<^sup>\<star> * z\<^sup>+ * y = z\<^sup>+ * y"
    by (metis assms mult_assoc mult_1_left mult_left_zero star.circ_zero star_simulation_right_equal)
  have 2: "z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>+ \<le> z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>\<star>"
    by (simp add: mult_right_isotone star.left_plus_below_circ)
  have "z\<^sup>\<star> * z\<^sup>+ * y * x\<^sup>\<star> \<le> z\<^sup>\<star> * y * x\<^sup>\<star>"
    by (metis mult_left_isotone star.left_plus_below_circ star.right_plus_circ star_plus)
  also have "... \<le> z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>)"
    by (simp add: mult_assoc mult_left_sub_dist_sup_right)
  also have "... \<le> z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>\<star>"
    using sup_right_divisibility star.circ_back_loop_fixpoint by blast
  finally have 3: "z\<^sup>\<star> * z\<^sup>+ * y * x\<^sup>\<star> \<le> z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>\<star>"
    .
  have "z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>\<star> * (z * (1 \<squnion> y * x\<^sup>\<star>)) = z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>+ \<squnion> z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>+ * y * x\<^sup>\<star>"
    by (metis mult_1_right semiring.distrib_left star.circ_plus_same mult_assoc)
  also have "... = z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>+ \<squnion> z\<^sup>\<star> * (1 \<squnion> y) * x\<^sup>\<star> * z\<^sup>+ * y * x\<^sup>\<star>"
    by (simp add: semiring.distrib_right mult_assoc)
  also have "... = z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>+ \<squnion> z\<^sup>\<star> * (1 \<squnion> y) * z\<^sup>+ * y * x\<^sup>\<star>"
    using 1 by (simp add: mult_assoc)
  also have "... = z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>+ \<squnion> z\<^sup>\<star> * z\<^sup>+ * y * x\<^sup>\<star> \<squnion> z\<^sup>\<star> * y * z\<^sup>+ * y * x\<^sup>\<star>"
    using mult_left_dist_sup mult_right_dist_sup sup_assoc by auto
  also have "... = z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>+ \<squnion> z\<^sup>\<star> * z\<^sup>+ * y * x\<^sup>\<star>"
    by (metis assms(2) mult_left_dist_sup mult_left_zero sup_commute sup_monoid.add_0_left mult_assoc)
  also have "... \<le> z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>\<star>"
    using 2 3 by simp
  finally have "(x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) \<squnion> z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>\<star> * (z * (1 \<squnion> y * x\<^sup>\<star>)) \<le> z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>\<star>"
    by (simp add: star_outer_increasing)
  hence 4: "(x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * (z * (1 \<squnion> y * x\<^sup>\<star>))\<^sup>\<star> \<le> z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>\<star>"
    by (simp add: star_right_induct)
  have 5: "(x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>\<star> \<le> (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * (z * (1 \<squnion> y * x\<^sup>\<star>))\<^sup>\<star>"
    by (metis sup_ge1 mult_right_isotone mult_1_right star_isotone)
  have "z * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) = z * x\<^sup>\<star> \<squnion> z * y * x\<^sup>\<star>"
    by (simp add: mult_assoc mult_left_dist_sup)
  also have "... = z \<squnion> z * y * x\<^sup>\<star>"
    by (simp add: assms star_absorb)
  also have "... = z * (1 \<squnion> y * x\<^sup>\<star>)"
    by (simp add: mult_assoc mult_left_dist_sup)
  also have "... \<le> (z * (1 \<squnion> y * x\<^sup>\<star>))\<^sup>\<star>"
    by (simp add: star.circ_increasing)
  also have "... \<le> (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * (z * (1 \<squnion> y * x\<^sup>\<star>))\<^sup>\<star>"
    by (metis le_supE mult_right_sub_dist_sup_left star.circ_loop_fixpoint)
  finally have "z * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) \<le> (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * (z * (1 \<squnion> y * x\<^sup>\<star>))\<^sup>\<star>"
    .
  hence "z * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * (z * (1 \<squnion> y * x\<^sup>\<star>))\<^sup>\<star> \<le> (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * (z * (1 \<squnion> y * x\<^sup>\<star>))\<^sup>\<star>"
    by (metis mult_assoc mult_left_isotone star.circ_transitive_equal)
  hence "z\<^sup>\<star> * (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * z\<^sup>\<star> \<le> (x\<^sup>\<star> \<squnion> y * x\<^sup>\<star>) * (z * (1 \<squnion> y * x\<^sup>\<star>))\<^sup>\<star>"
    using 5 by (metis star_left_induct sup.bounded_iff mult_assoc)
  thus ?thesis
    using 4 by (simp add: antisym)
qed

lemma cancel_separate_eq:
  "x * y \<le> 1 \<Longrightarrow> x\<^sup>\<star> * y\<^sup>\<star> = x\<^sup>\<star> \<squnion> y\<^sup>\<star>"
  by (metis antisym cancel_separate star.circ_plus_one star.circ_sup_sub_sup_one_1 star_involutive)

lemma cancel_separate_1:
  assumes "x * y \<le> 1"
    shows "(x \<squnion> y)\<^sup>\<star> = y\<^sup>\<star> * x\<^sup>\<star>"
proof -
  have "y\<^sup>\<star> * x\<^sup>\<star> * y = y\<^sup>\<star> * x\<^sup>\<star> * x * y \<squnion> y\<^sup>\<star> * y"
    by (metis mult_right_dist_sup star.circ_back_loop_fixpoint)
  also have "... \<le> y\<^sup>\<star> * x\<^sup>\<star> \<squnion> y\<^sup>\<star> * y"
    by (metis assms semiring.add_right_mono mult_right_isotone mult_1_right mult_assoc)
  also have "... \<le> y\<^sup>\<star> * x\<^sup>\<star> \<squnion> y\<^sup>\<star>"
    using semiring.add_left_mono star.right_plus_below_circ by simp
  also have "... = y\<^sup>\<star> * x\<^sup>\<star>"
    by (metis star.circ_back_loop_fixpoint sup.left_idem sup_commute)
  finally have "y\<^sup>\<star> * x\<^sup>\<star> * y \<le> y\<^sup>\<star> * x\<^sup>\<star>"
    by simp
  hence "y\<^sup>\<star> * x\<^sup>\<star> * (x \<squnion> y) \<le> y\<^sup>\<star> * x\<^sup>\<star> * x \<squnion> y\<^sup>\<star> * x\<^sup>\<star>"
    using mult_left_dist_sup order_lesseq_imp by fastforce
  also have "... = y\<^sup>\<star> * x\<^sup>\<star>"
    by (metis star.circ_back_loop_fixpoint sup.left_idem)
  finally have "(x \<squnion> y)\<^sup>\<star> \<le> y\<^sup>\<star> * x\<^sup>\<star>"
    by (metis star.circ_decompose_7 star_right_induct_mult sup_commute)
  thus ?thesis
    using antisym star.circ_sub_dist_3 sup_commute by fastforce
qed

lemma plus_sup:
  "(x \<squnion> y)\<^sup>+ = (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>+ \<squnion> (x\<^sup>\<star> * y)\<^sup>+"
  by (metis semiring.distrib_left star.circ_sup_9 star_plus mult_assoc)

lemma plus_half_bot:
  "x * y * x = bot \<Longrightarrow> (x * y)\<^sup>+ = x * y"
  by (metis star_absorb star_slide mult_assoc)

lemma cancel_separate_1_sup:
  assumes "x * y \<le> 1"
      and "y * x \<le> 1"
  shows "(x \<squnion> y)\<^sup>\<star> = x\<^sup>\<star> \<squnion> y\<^sup>\<star>"
  by (simp add: assms cancel_separate_1 cancel_separate_eq local.sup_commute)

end

text \<open>
A Kleene algebra is obtained by requiring an idempotent semiring.
\<close>

class kleene_algebra = left_zero_kleene_algebra + idempotent_semiring

text \<open>
The following classes are variants of Kleene algebras expanded by an additional iteration operation.
This is useful to study the Kleene star in computation models that do not use least fixpoints in the refinement order as the semantics of recursion.
\<close>

class left_kleene_conway_semiring = left_kleene_algebra + left_conway_semiring
begin

lemma star_below_circ:
  "x\<^sup>\<star> \<le> x\<^sup>\<circ>"
  by (metis circ_left_unfold mult_1_right order_refl star_left_induct)

lemma star_zero_below_circ_mult:
  "x\<^sup>\<star> * bot \<le> x\<^sup>\<circ> * y"
  by (simp add: mult_isotone star_below_circ)

lemma star_mult_circ:
  "x\<^sup>\<star> * x\<^sup>\<circ> = x\<^sup>\<circ>"
  by (metis sup_right_divisibility antisym circ_left_unfold star_left_induct_mult star.circ_loop_fixpoint)

lemma circ_mult_star:
  "x\<^sup>\<circ> * x\<^sup>\<star> = x\<^sup>\<circ>"
  by (metis sup_assoc sup.bounded_iff circ_left_unfold circ_rtc_2 eq_iff left_plus_circ star.circ_sup_sub star.circ_back_loop_prefixpoint star.circ_increasing star_below_circ star_mult_circ star_sup_one)

lemma circ_star:
  "x\<^sup>\<circ>\<^sup>\<star> = x\<^sup>\<circ>"
  by (metis antisym circ_reflexive circ_transitive_equal star.circ_increasing star.circ_sup_one_right_unfold star_left_induct_mult_equal)

lemma star_circ:
  "x\<^sup>\<star>\<^sup>\<circ> = x\<^sup>\<circ>\<^sup>\<circ>"
  by (metis antisym circ_circ_sup circ_sub_dist le_iff_sup star.circ_rtc_2 star_below_circ)

lemma circ_sup_3:
  "(x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<star> \<le> (x \<squnion> y)\<^sup>\<circ>"
  using circ_star circ_sub_dist_3 star_isotone by fastforce

end

class left_zero_kleene_conway_semiring = left_zero_kleene_algebra + itering
begin

subclass left_kleene_conway_semiring ..

lemma circ_isolate:
  "x\<^sup>\<circ> = x\<^sup>\<circ> * bot \<squnion> x\<^sup>\<star>"
  by (metis sup_commute antisym circ_sup_upper_bound circ_mult_star circ_simulate_absorb star.left_plus_below_circ star_below_circ zero_right_mult_decreasing)

lemma circ_isolate_mult:
  "x\<^sup>\<circ> * y = x\<^sup>\<circ> * bot \<squnion> x\<^sup>\<star> * y"
  by (metis circ_isolate mult_assoc mult_left_zero mult_right_dist_sup)

lemma circ_isolate_mult_sub:
  "x\<^sup>\<circ> * y \<le> x\<^sup>\<circ> \<squnion> x\<^sup>\<star> * y"
  by (metis sup_left_isotone circ_isolate_mult zero_right_mult_decreasing)

lemma circ_sub_decompose:
  "(x\<^sup>\<circ> * y)\<^sup>\<circ> \<le> (x\<^sup>\<star> * y)\<^sup>\<circ> * x\<^sup>\<circ>"
proof -
  have "x\<^sup>\<star> * y \<squnion> x\<^sup>\<circ> * bot = x\<^sup>\<circ> * y"
    by (metis sup.commute circ_isolate_mult)
  hence "(x\<^sup>\<star> * y)\<^sup>\<circ> * x\<^sup>\<circ> = ((x\<^sup>\<circ> * y)\<^sup>\<circ> \<squnion> x\<^sup>\<circ>)\<^sup>\<star>"
    by (metis circ_star circ_sup_9 circ_sup_mult_zero star_decompose_1)
  thus ?thesis
    by (metis circ_star le_iff_sup star.circ_decompose_7 star.circ_unfold_sum)
qed

lemma circ_sup_4:
  "(x \<squnion> y)\<^sup>\<circ> = (x\<^sup>\<star> * y)\<^sup>\<circ> * x\<^sup>\<circ>"
  apply (rule antisym)
  apply (metis circ_sup circ_sub_decompose circ_transitive_equal mult_assoc mult_left_isotone)
  by (metis circ_sup circ_isotone mult_left_isotone star_below_circ)

lemma circ_sup_5:
  "(x\<^sup>\<circ> * y)\<^sup>\<circ> * x\<^sup>\<circ> = (x\<^sup>\<star> * y)\<^sup>\<circ> * x\<^sup>\<circ>"
  using circ_sup_4 circ_sup_9 by auto

lemma plus_circ:
  "(x\<^sup>\<star> * x)\<^sup>\<circ> = x\<^sup>\<circ>"
  by (metis sup_idem circ_sup_4 circ_decompose_7 circ_star star.circ_decompose_5 star.right_plus_circ)

(*
lemma "(x\<^sup>\<star> * y * x\<^sup>\<star>)\<^sup>\<circ> = (x\<^sup>\<star> * y)\<^sup>\<circ>" nitpick [expect=genuine] oops
*)

end

text \<open>
The following classes add a greatest element.
\<close>

class bounded_left_kleene_algebra = bounded_idempotent_left_semiring + left_kleene_algebra

sublocale bounded_left_kleene_algebra < star: bounded_left_conway_semiring where circ = star ..

class bounded_left_zero_kleene_algebra = bounded_idempotent_left_semiring + left_zero_kleene_algebra

sublocale bounded_left_zero_kleene_algebra < star: bounded_itering where circ = star ..

class bounded_kleene_algebra = bounded_idempotent_semiring + kleene_algebra

sublocale bounded_kleene_algebra < star: bounded_itering where circ = star ..

text \<open>
We conclude with an alternative axiomatisation of Kleene algebras.
\<close>

class kleene_algebra_var = idempotent_semiring + star +
  assumes star_left_unfold_var : "1 \<squnion> y * y\<^sup>\<star> \<le> y\<^sup>\<star>"
  assumes star_left_induct_var : "y * x \<le> x \<longrightarrow> y\<^sup>\<star> * x \<le> x"
  assumes star_right_induct_var : "x * y \<le> x \<longrightarrow> x * y\<^sup>\<star> \<le> x"
begin

subclass kleene_algebra
  apply unfold_locales
  apply (rule star_left_unfold_var)
  apply (meson sup.bounded_iff mult_right_isotone order_trans star_left_induct_var)
  by (meson sup.bounded_iff mult_left_isotone order_trans star_right_induct_var)

end

end

