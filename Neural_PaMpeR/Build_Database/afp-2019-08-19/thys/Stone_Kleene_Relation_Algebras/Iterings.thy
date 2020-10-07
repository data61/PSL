(* Title:      Iterings
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Iterings\<close>

text \<open>
This theory introduces algebraic structures with an operation that describes iteration in various relational computation models.
An iteration describes the repeated sequential execution of a computation.
This is typically modelled by fixpoints, but different computation models use different fixpoints in the refinement order.
We therefore look at equational and simulation axioms rather than induction axioms.
Our development is based on \cite{Guttmann2012c} and the proposed algebras generalise Kleene algebras.

We first consider a variant of Conway semirings \cite{BloomEsik1993a} based on idempotent left semirings.
Conway semirings expand semirings by an iteration operation satisfying Conway's sumstar and productstar axioms \cite{Conway1971}.
Many properties of iteration follow already from these equational axioms.

Next we introduce iterings, which use generalised versions of simulation axioms in addition to sumstar and productstar.
Unlike the induction axioms of the Kleene star, which hold only in partial-correctness models, the simulation axioms are also valid in total and general correctness models.
They are still powerful enough to prove the correctness of complex results such as separation theorems of \cite{Cohen2000} and Back's atomicity refinement theorem \cite{BackWright1999,Wright2004}.
\<close>

theory Iterings

imports Stone_Relation_Algebras.Semirings

begin

subsection \<open>Conway Semirings\<close>

text \<open>
In this section, we consider equational axioms for iteration.
The algebraic structures are based on idempotent left semirings, which are expanded by a unary iteration operation.
We start with an unfold property, one inequality of the sliding rule and distributivity over joins, which is similar to Conway's sumstar.
\<close>

class circ =
  fixes circ :: "'a \<Rightarrow> 'a" ("_\<^sup>\<circ>" [100] 100)

class left_conway_semiring = idempotent_left_semiring + circ +
  assumes circ_left_unfold: "1 \<squnion> x * x\<^sup>\<circ> = x\<^sup>\<circ>"
  assumes circ_left_slide: "(x * y)\<^sup>\<circ> * x \<le> x * (y * x)\<^sup>\<circ>"
  assumes circ_sup_1: "(x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> * (y * x\<^sup>\<circ>)\<^sup>\<circ>"
begin

text \<open>
We obtain one inequality of Conway's productstar, as well as of the other unfold rule.
\<close>

lemma circ_mult_sub:
  "1 \<squnion> x * (y * x)\<^sup>\<circ> * y \<le> (x * y)\<^sup>\<circ>"
  by (metis sup_right_isotone circ_left_slide circ_left_unfold mult_assoc mult_right_isotone)

lemma circ_right_unfold_sub:
  "1 \<squnion> x\<^sup>\<circ> * x \<le> x\<^sup>\<circ>"
  by (metis circ_mult_sub mult_1_left mult_1_right)

lemma circ_zero:
  "bot\<^sup>\<circ> = 1"
  by (metis sup_monoid.add_0_right circ_left_unfold mult_left_zero)

lemma circ_increasing:
  "x \<le> x\<^sup>\<circ>"
  by (metis le_supI2 circ_left_unfold circ_right_unfold_sub mult_1_left mult_right_sub_dist_sup_left order_trans)

lemma circ_reflexive:
  "1 \<le> x\<^sup>\<circ>"
  by (metis sup_left_divisibility circ_left_unfold)

lemma circ_mult_increasing:
  "x \<le> x * x\<^sup>\<circ>"
  by (metis circ_reflexive mult_right_isotone mult_1_right)

lemma circ_mult_increasing_2:
  "x \<le> x\<^sup>\<circ> * x"
  by (metis circ_reflexive mult_left_isotone mult_1_left)

lemma circ_transitive_equal:
  "x\<^sup>\<circ> * x\<^sup>\<circ> = x\<^sup>\<circ>"
  by (metis sup_idem circ_sup_1 circ_left_unfold mult_assoc)

text \<open>
While iteration is not idempotent, a fixpoint is reached after applying this operation twice.
Iteration is idempotent for the unit.
\<close>

lemma circ_circ_circ:
  "x\<^sup>\<circ>\<^sup>\<circ>\<^sup>\<circ> = x\<^sup>\<circ>\<^sup>\<circ>"
  by (metis sup_idem circ_sup_1 circ_increasing circ_transitive_equal le_iff_sup)

lemma circ_one:
  "1\<^sup>\<circ> = 1\<^sup>\<circ>\<^sup>\<circ>"
  by (metis circ_circ_circ circ_zero)

lemma circ_sup_sub:
  "(x\<^sup>\<circ> * y)\<^sup>\<circ> * x\<^sup>\<circ> \<le> (x \<squnion> y)\<^sup>\<circ>"
  by (metis circ_sup_1 circ_left_slide)

lemma circ_plus_one:
  "x\<^sup>\<circ> = 1 \<squnion> x\<^sup>\<circ>"
  by (metis le_iff_sup circ_reflexive)

text \<open>
Iteration satisfies a characteristic property of reflexive transitive closures.
\<close>

lemma circ_rtc_2:
  "1 \<squnion> x \<squnion> x\<^sup>\<circ> * x\<^sup>\<circ> = x\<^sup>\<circ>"
  by (metis sup_assoc circ_increasing circ_plus_one circ_transitive_equal le_iff_sup)

lemma mult_zero_circ:
  "(x * bot)\<^sup>\<circ> = 1 \<squnion> x * bot"
  by (metis circ_left_unfold mult_assoc mult_left_zero)

lemma mult_zero_sup_circ:
  "(x \<squnion> y * bot)\<^sup>\<circ> = x\<^sup>\<circ> * (y * bot)\<^sup>\<circ>"
  by (metis circ_sup_1 mult_assoc mult_left_zero)

lemma circ_plus_sub:
  "x\<^sup>\<circ> * x \<le> x * x\<^sup>\<circ>"
  by (metis circ_left_slide mult_1_left mult_1_right)

lemma circ_loop_fixpoint:
  "y * (y\<^sup>\<circ> * z) \<squnion> z = y\<^sup>\<circ> * z"
  by (metis sup_commute circ_left_unfold mult_assoc mult_1_left mult_right_dist_sup)

lemma left_plus_below_circ:
  "x * x\<^sup>\<circ> \<le> x\<^sup>\<circ>"
  by (metis sup.cobounded2 circ_left_unfold)

lemma right_plus_below_circ:
  "x\<^sup>\<circ> * x \<le> x\<^sup>\<circ>"
  using circ_right_unfold_sub by auto

lemma circ_sup_upper_bound:
  "x \<le> z\<^sup>\<circ> \<Longrightarrow> y \<le> z\<^sup>\<circ> \<Longrightarrow> x \<squnion> y \<le> z\<^sup>\<circ>"
  by simp

lemma circ_mult_upper_bound:
  "x \<le> z\<^sup>\<circ> \<Longrightarrow> y \<le> z\<^sup>\<circ> \<Longrightarrow> x * y \<le> z\<^sup>\<circ>"
  by (metis mult_isotone circ_transitive_equal)

lemma circ_sub_dist:
  "x\<^sup>\<circ> \<le> (x \<squnion> y)\<^sup>\<circ>"
  by (metis circ_sup_sub circ_plus_one mult_1_left mult_right_sub_dist_sup_left order_trans)

lemma circ_sub_dist_1:
  "x \<le> (x \<squnion> y)\<^sup>\<circ>"
  using circ_increasing le_supE by blast

lemma circ_sub_dist_2:
  "x * y \<le> (x \<squnion> y)\<^sup>\<circ>"
  by (metis sup_commute circ_mult_upper_bound circ_sub_dist_1)

lemma circ_sub_dist_3:
  "x\<^sup>\<circ> * y\<^sup>\<circ> \<le> (x \<squnion> y)\<^sup>\<circ>"
  by (metis sup_commute circ_mult_upper_bound circ_sub_dist)

lemma circ_isotone:
  "x \<le> y \<Longrightarrow> x\<^sup>\<circ> \<le> y\<^sup>\<circ>"
  by (metis circ_sub_dist le_iff_sup)

lemma circ_sup_2:
  "(x \<squnion> y)\<^sup>\<circ> \<le> (x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<circ>"
  by (metis sup.bounded_iff circ_increasing circ_isotone circ_reflexive mult_isotone mult_1_left mult_1_right)

lemma circ_sup_one_left_unfold:
  "1 \<le> x \<Longrightarrow> x * x\<^sup>\<circ> = x\<^sup>\<circ>"
  by (metis antisym le_iff_sup mult_1_left mult_right_sub_dist_sup_left left_plus_below_circ)

lemma circ_sup_one_right_unfold:
  "1 \<le> x \<Longrightarrow> x\<^sup>\<circ> * x = x\<^sup>\<circ>"
  by (metis antisym le_iff_sup mult_left_sub_dist_sup_left mult_1_right right_plus_below_circ)

lemma circ_decompose_4:
  "(x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<circ> = x\<^sup>\<circ> * (y\<^sup>\<circ> * x\<^sup>\<circ>)\<^sup>\<circ>"
  by (metis sup_assoc sup_commute circ_sup_1 circ_loop_fixpoint circ_plus_one circ_rtc_2 circ_transitive_equal mult_assoc)

lemma circ_decompose_5:
  "(x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<circ> = (y\<^sup>\<circ> * x\<^sup>\<circ>)\<^sup>\<circ>"
  by (metis circ_decompose_4 circ_loop_fixpoint antisym mult_right_sub_dist_sup_right mult_assoc)

lemma circ_decompose_6:
  "x\<^sup>\<circ> * (y * x\<^sup>\<circ>)\<^sup>\<circ> = y\<^sup>\<circ> * (x * y\<^sup>\<circ>)\<^sup>\<circ>"
  by (metis sup_commute circ_sup_1)

lemma circ_decompose_7:
  "(x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> * y\<^sup>\<circ> * (x \<squnion> y)\<^sup>\<circ>"
  by (metis circ_sup_1 circ_decompose_6 circ_transitive_equal mult_assoc)

lemma circ_decompose_8:
  "(x \<squnion> y)\<^sup>\<circ> = (x \<squnion> y)\<^sup>\<circ> * x\<^sup>\<circ> * y\<^sup>\<circ>"
  by (metis antisym eq_refl mult_assoc mult_isotone mult_1_right circ_mult_upper_bound circ_reflexive circ_sub_dist_3)

lemma circ_decompose_9:
  "(x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<circ> = x\<^sup>\<circ> * y\<^sup>\<circ> * (x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<circ>"
  by (metis circ_decompose_4 mult_assoc)

lemma circ_decompose_10:
  "(x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<circ> = (x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<circ> * x\<^sup>\<circ> * y\<^sup>\<circ>"
  by (metis sup_ge2 circ_loop_fixpoint circ_reflexive circ_sup_one_right_unfold mult_assoc order_trans)

lemma circ_back_loop_prefixpoint:
  "(z * y\<^sup>\<circ>) * y \<squnion> z \<le> z * y\<^sup>\<circ>"
  by (metis sup.bounded_iff circ_left_unfold mult_assoc mult_left_sub_dist_sup_left mult_right_isotone mult_1_right right_plus_below_circ)

text \<open>
We obtain the fixpoint and prefixpoint properties of iteration, but not least or greatest fixpoint properties.
\<close>

lemma circ_loop_is_fixpoint:
  "is_fixpoint (\<lambda>x . y * x \<squnion> z) (y\<^sup>\<circ> * z)"
  by (metis circ_loop_fixpoint is_fixpoint_def)

lemma circ_back_loop_is_prefixpoint:
  "is_prefixpoint (\<lambda>x . x * y \<squnion> z) (z * y\<^sup>\<circ>)"
  by (metis circ_back_loop_prefixpoint is_prefixpoint_def)

lemma circ_circ_sup:
  "(1 \<squnion> x)\<^sup>\<circ> = x\<^sup>\<circ>\<^sup>\<circ>"
  by (metis sup_commute circ_sup_1 circ_decompose_4 circ_zero mult_1_right)

lemma circ_circ_mult_sub:
  "x\<^sup>\<circ> * 1\<^sup>\<circ> \<le> x\<^sup>\<circ>\<^sup>\<circ>"
  by (metis circ_increasing circ_isotone circ_mult_upper_bound circ_reflexive)

lemma left_plus_circ:
  "(x * x\<^sup>\<circ>)\<^sup>\<circ> = x\<^sup>\<circ>"
  by (metis circ_left_unfold circ_sup_1 mult_1_right mult_sub_right_one sup.absorb1 mult_assoc)

lemma right_plus_circ:
  "(x\<^sup>\<circ> * x)\<^sup>\<circ> = x\<^sup>\<circ>"
  by (metis sup_commute circ_isotone circ_loop_fixpoint circ_plus_sub circ_sub_dist eq_iff left_plus_circ)

lemma circ_square:
  "(x * x)\<^sup>\<circ> \<le> x\<^sup>\<circ>"
  by (metis circ_increasing circ_isotone left_plus_circ mult_right_isotone)

lemma circ_mult_sub_sup:
  "(x * y)\<^sup>\<circ> \<le> (x \<squnion> y)\<^sup>\<circ>"
  by (metis sup_ge1 sup_ge2 circ_isotone circ_square mult_isotone order_trans)

lemma circ_sup_mult_zero:
  "x\<^sup>\<circ> * y = (x \<squnion> y * bot)\<^sup>\<circ> * y"
proof -
  have "(x \<squnion> y * bot)\<^sup>\<circ> * y = x\<^sup>\<circ> * (1 \<squnion> y * bot) * y"
    by (metis mult_zero_sup_circ mult_zero_circ)
  also have "... = x\<^sup>\<circ> * (y \<squnion> y * bot)"
    by (metis mult_assoc mult_1_left mult_left_zero mult_right_dist_sup)
  also have "... = x\<^sup>\<circ> * y"
    by (metis sup_commute le_iff_sup zero_right_mult_decreasing)
  finally show ?thesis
    by simp
qed

lemma troeger_1:
  "(x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> * (1 \<squnion> y * (x \<squnion> y)\<^sup>\<circ>)"
  by (metis circ_sup_1 circ_left_unfold mult_assoc)

lemma troeger_2:
  "(x \<squnion> y)\<^sup>\<circ> * z = x\<^sup>\<circ> * (y * (x \<squnion> y)\<^sup>\<circ> * z \<squnion> z)"
  by (metis circ_sup_1 circ_loop_fixpoint mult_assoc)

lemma troeger_3:
  "(x \<squnion> y * bot)\<^sup>\<circ> = x\<^sup>\<circ> * (1 \<squnion> y * bot)"
  by (metis mult_zero_sup_circ mult_zero_circ)

lemma circ_sup_sub_sup_one_1:
  "x \<squnion> y \<le> x\<^sup>\<circ> * (1 \<squnion> y)"
  by (metis circ_increasing circ_left_unfold mult_1_left mult_1_right mult_left_sub_dist_sup mult_right_sub_dist_sup_left order_trans sup_mono)

lemma circ_sup_sub_sup_one_2:
  "x\<^sup>\<circ> * (x \<squnion> y) \<le> x\<^sup>\<circ> * (1 \<squnion> y)"
  by (metis circ_sup_sub_sup_one_1 circ_transitive_equal mult_assoc mult_right_isotone)

lemma circ_sup_sub_sup_one:
  "x * x\<^sup>\<circ> * (x \<squnion> y) \<le> x * x\<^sup>\<circ> * (1 \<squnion> y)"
  by (metis circ_sup_sub_sup_one_2 mult_assoc mult_right_isotone)

lemma circ_square_2:
  "(x * x)\<^sup>\<circ> * (x \<squnion> 1) \<le> x\<^sup>\<circ>"
  by (metis sup.bounded_iff circ_increasing circ_mult_upper_bound circ_reflexive circ_square)

lemma circ_extra_circ:
  "(y * x\<^sup>\<circ>)\<^sup>\<circ> = (y * y\<^sup>\<circ> * x\<^sup>\<circ>)\<^sup>\<circ>"
  by (metis circ_decompose_6 circ_transitive_equal left_plus_circ mult_assoc)

lemma circ_circ_sub_mult:
  "1\<^sup>\<circ> * x\<^sup>\<circ> \<le> x\<^sup>\<circ>\<^sup>\<circ>"
  by (metis circ_increasing circ_isotone circ_mult_upper_bound circ_reflexive)

lemma circ_decompose_11:
  "(x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<circ> = (x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<circ> * x\<^sup>\<circ>"
  by (metis circ_decompose_10 circ_decompose_4 circ_decompose_5 circ_decompose_9 left_plus_circ)

lemma circ_mult_below_circ_circ:
  "(x * y)\<^sup>\<circ> \<le> (x\<^sup>\<circ> * y)\<^sup>\<circ> * x\<^sup>\<circ>"
  by (metis circ_increasing circ_isotone circ_reflexive dual_order.trans mult_left_isotone mult_right_isotone mult_1_right)

(*
lemma circ_right_unfold: "1 \<squnion> x\<^sup>\<circ> * x = x\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma circ_mult: "1 \<squnion> x * (y * x)\<^sup>\<circ> * y = (x * y)\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma circ_slide: "(x * y)\<^sup>\<circ> * x = x * (y * x)\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma circ_plus_same: "x\<^sup>\<circ> * x = x * x\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma "1\<^sup>\<circ> * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * 1\<^sup>\<circ>" nitpick [expect=genuine,card=7] oops
lemma circ_circ_mult_1: "x\<^sup>\<circ> * 1\<^sup>\<circ> = x\<^sup>\<circ>\<^sup>\<circ>" nitpick [expect=genuine,card=7] oops
lemma "x\<^sup>\<circ> * 1\<^sup>\<circ> \<le> 1\<^sup>\<circ> * x\<^sup>\<circ>" nitpick [expect=genuine,card=7] oops
lemma circ_circ_mult: "1\<^sup>\<circ> * x\<^sup>\<circ> = x\<^sup>\<circ>\<^sup>\<circ>" nitpick [expect=genuine,card=7] oops
lemma circ_sup: "(x\<^sup>\<circ> * y)\<^sup>\<circ> * x\<^sup>\<circ> = (x \<squnion> y)\<^sup>\<circ>" nitpick [expect=genuine,card=8] oops
lemma circ_unfold_sum: "(x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> \<squnion> x\<^sup>\<circ> * y * (x \<squnion> y)\<^sup>\<circ>" nitpick [expect=genuine,card=7] oops

lemma mult_zero_sup_circ_2: "(x \<squnion> y * bot)\<^sup>\<circ> = x\<^sup>\<circ> \<squnion> x\<^sup>\<circ> * y * bot" nitpick [expect=genuine,card=7] oops
lemma sub_mult_one_circ: "x * 1\<^sup>\<circ> \<le> 1\<^sup>\<circ> * x" nitpick [expect=genuine] oops
lemma circ_back_loop_fixpoint: "(z * y\<^sup>\<circ>) * y \<squnion> z = z * y\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma circ_back_loop_is_fixpoint: "is_fixpoint (\<lambda>x . x * y \<squnion> z) (z * y\<^sup>\<circ>)" nitpick [expect=genuine] oops
lemma "x\<^sup>\<circ> * y\<^sup>\<circ> \<le> (x\<^sup>\<circ> * y)\<^sup>\<circ> * x\<^sup>\<circ>" nitpick [expect=genuine,card=7] oops
*)

end

text \<open>
The next class considers the interaction of iteration with a greatest element.
\<close>

class bounded_left_conway_semiring = bounded_idempotent_left_semiring + left_conway_semiring
begin

lemma circ_top:
  "top\<^sup>\<circ> = top"
  by (simp add: antisym circ_increasing)

lemma circ_right_top:
  "x\<^sup>\<circ> * top = top"
  by (metis sup_right_top circ_loop_fixpoint)

lemma circ_left_top:
  "top * x\<^sup>\<circ> = top"
  by (metis circ_right_top circ_top circ_decompose_11)

lemma mult_top_circ:
  "(x * top)\<^sup>\<circ> = 1 \<squnion> x * top"
  by (metis circ_left_top circ_left_unfold mult_assoc)

end

class left_zero_conway_semiring = idempotent_left_zero_semiring + left_conway_semiring
begin

lemma mult_zero_sup_circ_2:
  "(x \<squnion> y * bot)\<^sup>\<circ> = x\<^sup>\<circ> \<squnion> x\<^sup>\<circ> * y * bot"
  by (metis mult_assoc mult_left_dist_sup mult_1_right troeger_3)

lemma circ_unfold_sum:
  "(x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> \<squnion> x\<^sup>\<circ> * y * (x \<squnion> y)\<^sup>\<circ>"
  by (metis mult_assoc mult_left_dist_sup mult_1_right troeger_1)

end

text \<open>
The next class assumes the full sliding equation.
\<close>

class left_conway_semiring_1 = left_conway_semiring +
  assumes circ_right_slide: "x * (y * x)\<^sup>\<circ> \<le> (x * y)\<^sup>\<circ> * x"
begin

lemma circ_slide_1:
  "x * (y * x)\<^sup>\<circ> = (x * y)\<^sup>\<circ> * x"
  by (metis antisym circ_left_slide circ_right_slide)

text \<open>
This implies the full unfold rules and Conway's productstar.
\<close>

lemma circ_right_unfold_1:
  "1 \<squnion> x\<^sup>\<circ> * x = x\<^sup>\<circ>"
  by (metis circ_left_unfold circ_slide_1 mult_1_left mult_1_right)

lemma circ_mult_1:
  "(x * y)\<^sup>\<circ> = 1 \<squnion> x * (y * x)\<^sup>\<circ> * y"
  by (metis circ_left_unfold circ_slide_1 mult_assoc)

lemma circ_sup_9:
  "(x \<squnion> y)\<^sup>\<circ> = (x\<^sup>\<circ> * y)\<^sup>\<circ> * x\<^sup>\<circ>"
  by (metis circ_sup_1 circ_slide_1)

lemma circ_plus_same:
  "x\<^sup>\<circ> * x = x * x\<^sup>\<circ>"
  by (metis circ_slide_1 mult_1_left mult_1_right)

lemma circ_decompose_12:
  "x\<^sup>\<circ> * y\<^sup>\<circ> \<le> (x\<^sup>\<circ> * y)\<^sup>\<circ> * x\<^sup>\<circ>"
  by (metis circ_sup_9 circ_sub_dist_3)

end

class left_zero_conway_semiring_1 = left_zero_conway_semiring + left_conway_semiring_1
begin

lemma circ_back_loop_fixpoint:
  "(z * y\<^sup>\<circ>) * y \<squnion> z = z * y\<^sup>\<circ>"
  by (metis sup_commute circ_left_unfold circ_plus_same mult_assoc mult_left_dist_sup mult_1_right)

lemma circ_back_loop_is_fixpoint:
  "is_fixpoint (\<lambda>x . x * y \<squnion> z) (z * y\<^sup>\<circ>)"
  by (metis circ_back_loop_fixpoint is_fixpoint_def)

lemma circ_elimination:
  "x * y = bot \<Longrightarrow> x * y\<^sup>\<circ> \<le> x"
  by (metis sup_monoid.add_0_left circ_back_loop_fixpoint circ_plus_same mult_assoc mult_left_zero order_refl)

end

subsection \<open>Iterings\<close>

text \<open>
This section adds simulation axioms to Conway semirings.
We consider several classes with increasingly general simulation axioms.
\<close>

class itering_1 = left_conway_semiring_1 +
  assumes circ_simulate: "z * x \<le> y * z \<longrightarrow> z * x\<^sup>\<circ> \<le> y\<^sup>\<circ> * z"
begin

lemma circ_circ_mult:
  "1\<^sup>\<circ> * x\<^sup>\<circ> = x\<^sup>\<circ>\<^sup>\<circ>"
  by (metis antisym circ_circ_sup circ_reflexive circ_simulate circ_sub_dist_3 circ_sup_one_left_unfold circ_transitive_equal mult_1_left order_refl)

lemma sub_mult_one_circ:
  "x * 1\<^sup>\<circ> \<le> 1\<^sup>\<circ> * x"
  by (metis circ_simulate mult_1_left mult_1_right order_refl)

text \<open>
The left simulation axioms is enough to prove a basic import property of tests.
\<close>

lemma circ_import:
  assumes "p \<le> p * p"
      and "p \<le> 1"
      and "p * x \<le> x * p"
    shows "p * x\<^sup>\<circ> = p * (p * x)\<^sup>\<circ>"
proof -
  have "p * x \<le> p * (p * x * p) * p"
    by (metis assms coreflexive_transitive eq_iff test_preserves_equation mult_assoc)
  hence "p * x\<^sup>\<circ> \<le> p * (p * x)\<^sup>\<circ>"
    by (metis (no_types) assms circ_simulate circ_slide_1 test_preserves_equation)
  thus ?thesis
    by (metis assms(2) circ_isotone mult_left_isotone mult_1_left mult_right_isotone antisym)
qed

end

text \<open>
Including generalisations of both simulation axioms allows us to prove separation rules.
\<close>

class itering_2 = left_conway_semiring_1 +
  assumes circ_simulate_right: "z * x \<le> y * z \<squnion> w \<longrightarrow> z * x\<^sup>\<circ> \<le> y\<^sup>\<circ> * (z \<squnion> w * x\<^sup>\<circ>)"
  assumes circ_simulate_left: "x * z \<le> z * y \<squnion> w \<longrightarrow> x\<^sup>\<circ> * z \<le> (z \<squnion> x\<^sup>\<circ> * w) * y\<^sup>\<circ>"
begin

subclass itering_1
  apply unfold_locales
  by (metis sup_monoid.add_0_right circ_simulate_right mult_left_zero)

lemma circ_simulate_left_1:
  "x * z \<le> z * y \<Longrightarrow> x\<^sup>\<circ> * z \<le> z * y\<^sup>\<circ> \<squnion> x\<^sup>\<circ> * bot"
  by (metis sup_monoid.add_0_right circ_simulate_left mult_assoc mult_left_zero mult_right_dist_sup)

lemma circ_separate_1:
  assumes "y * x \<le> x * y"
    shows "(x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> * y\<^sup>\<circ>"
proof -
  have "y\<^sup>\<circ> * x \<le> x * y\<^sup>\<circ> \<squnion> y\<^sup>\<circ> * bot"
    by (metis assms circ_simulate_left_1)
  hence "y\<^sup>\<circ> * x * y\<^sup>\<circ> \<le> x * y\<^sup>\<circ> * y\<^sup>\<circ> \<squnion> y\<^sup>\<circ> * bot * y\<^sup>\<circ>"
    by (metis mult_assoc mult_left_isotone mult_right_dist_sup)
  also have "... = x * y\<^sup>\<circ> \<squnion> y\<^sup>\<circ> * bot"
    by (metis circ_transitive_equal mult_assoc mult_left_zero)
  finally have "y\<^sup>\<circ> * (x * y\<^sup>\<circ>)\<^sup>\<circ> \<le> x\<^sup>\<circ> * (y\<^sup>\<circ> \<squnion> y\<^sup>\<circ> * bot)"
    using circ_simulate_right mult_assoc by fastforce
  also have "... = x\<^sup>\<circ> * y\<^sup>\<circ>"
    by (simp add: sup_absorb1 zero_right_mult_decreasing)
  finally have "(x \<squnion> y)\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ>"
    by (simp add: circ_decompose_6 circ_sup_1)
  thus ?thesis
    by (simp add: antisym circ_sub_dist_3)
qed

lemma circ_circ_mult_1:
  "x\<^sup>\<circ> * 1\<^sup>\<circ> = x\<^sup>\<circ>\<^sup>\<circ>"
  by (metis sup_commute circ_circ_sup circ_separate_1 mult_1_left mult_1_right order_refl)

end

text \<open>
With distributivity, we also get Back's atomicity refinement theorem.
\<close>

class itering_3 = itering_2 + left_zero_conway_semiring_1
begin

lemma circ_simulate_1:
  assumes "y * x \<le> x * y"
    shows "y\<^sup>\<circ> * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ>"
proof -
  have "y * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * y"
    by (metis assms circ_simulate)
  hence "y\<^sup>\<circ> * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ> \<squnion> y\<^sup>\<circ> * bot"
    by (metis circ_simulate_left_1)
  thus ?thesis
    by (metis sup_assoc sup_monoid.add_0_right circ_loop_fixpoint mult_assoc mult_left_zero mult_zero_sup_circ_2)
qed

lemma atomicity_refinement:
  assumes "s = s * q"
      and "x = q * x"
      and "q * b = bot"
      and "r * b \<le> b * r"
      and "r * l \<le> l * r"
      and "x * l \<le> l * x"
      and "b * l \<le> l * b"
      and "q * l \<le> l * q"
      and "r\<^sup>\<circ> * q \<le> q * r\<^sup>\<circ>"
      and "q \<le> 1"
    shows "s * (x \<squnion> b \<squnion> r \<squnion> l)\<^sup>\<circ> * q \<le> s * (x * b\<^sup>\<circ> * q \<squnion> r \<squnion> l)\<^sup>\<circ>"
proof -
  have "(x \<squnion> b \<squnion> r) * l \<le> l * (x \<squnion> b \<squnion> r)"
    using assms(5-7) mult_left_dist_sup mult_right_dist_sup semiring.add_mono by presburger
  hence "s * (x \<squnion> b \<squnion> r \<squnion> l)\<^sup>\<circ> * q = s * l\<^sup>\<circ> * (x \<squnion> b \<squnion> r)\<^sup>\<circ> * q"
    by (metis sup_commute circ_separate_1 mult_assoc)
  also have "... = s * l\<^sup>\<circ> * b\<^sup>\<circ> * r\<^sup>\<circ> * q * (x * b\<^sup>\<circ> * r\<^sup>\<circ> * q)\<^sup>\<circ>"
  proof -
    have "(b \<squnion> r)\<^sup>\<circ> = b\<^sup>\<circ> * r\<^sup>\<circ>"
      by (simp add: assms(4) circ_separate_1)
    hence "b\<^sup>\<circ> * r\<^sup>\<circ> * (q * (x * b\<^sup>\<circ> * r\<^sup>\<circ>))\<^sup>\<circ> = (x \<squnion> b \<squnion> r)\<^sup>\<circ>"
      by (metis (full_types) assms(2) circ_sup_1 sup_assoc sup_commute mult_assoc)
    thus ?thesis
      by (metis circ_slide_1 mult_assoc)
  qed
  also have "... \<le> s * l\<^sup>\<circ> * b\<^sup>\<circ> * r\<^sup>\<circ> * q * (x * b\<^sup>\<circ> * q * r\<^sup>\<circ>)\<^sup>\<circ>"
    by (metis assms(9) circ_isotone mult_assoc mult_right_isotone)
  also have "... \<le> s * q * l\<^sup>\<circ> * b\<^sup>\<circ> * r\<^sup>\<circ> * (x * b\<^sup>\<circ> * q * r\<^sup>\<circ>)\<^sup>\<circ>"
    by (metis assms(1,10) mult_left_isotone mult_right_isotone mult_1_right)
  also have "... \<le> s * l\<^sup>\<circ> * q * b\<^sup>\<circ> * r\<^sup>\<circ> * (x * b\<^sup>\<circ> * q * r\<^sup>\<circ>)\<^sup>\<circ>"
    by (metis assms(1,8) circ_simulate mult_assoc mult_left_isotone mult_right_isotone)
  also have "... \<le> s * l\<^sup>\<circ> * r\<^sup>\<circ> * (x * b\<^sup>\<circ> * q * r\<^sup>\<circ>)\<^sup>\<circ>"
    by (metis assms(3,10) sup_monoid.add_0_left circ_back_loop_fixpoint circ_plus_same mult_assoc mult_left_zero mult_left_isotone mult_right_isotone mult_1_right)
  also have "... \<le> s * (x * b\<^sup>\<circ> * q \<squnion> r \<squnion> l)\<^sup>\<circ>"
    by (metis sup_commute circ_sup_1 circ_sub_dist_3 mult_assoc mult_right_isotone)
  finally show ?thesis
    .
qed

end

text \<open>
The following class contains the most general simulation axioms we consider.
They allow us to prove further separation properties.
\<close>

class itering = idempotent_left_zero_semiring + circ +
  assumes circ_sup: "(x \<squnion> y)\<^sup>\<circ> = (x\<^sup>\<circ> * y)\<^sup>\<circ> * x\<^sup>\<circ>"
  assumes circ_mult: "(x * y)\<^sup>\<circ> = 1 \<squnion> x * (y * x)\<^sup>\<circ> * y"
  assumes circ_simulate_right_plus: "z * x \<le> y * y\<^sup>\<circ> * z \<squnion> w \<longrightarrow> z * x\<^sup>\<circ> \<le> y\<^sup>\<circ> * (z \<squnion> w * x\<^sup>\<circ>)"
  assumes circ_simulate_left_plus: "x * z \<le> z * y\<^sup>\<circ> \<squnion> w \<longrightarrow> x\<^sup>\<circ> * z \<le> (z \<squnion> x\<^sup>\<circ> * w) * y\<^sup>\<circ>"
begin

lemma circ_right_unfold:
  "1 \<squnion> x\<^sup>\<circ> * x = x\<^sup>\<circ>"
  by (metis circ_mult mult_1_left mult_1_right)

lemma circ_slide:
  "x * (y * x)\<^sup>\<circ> = (x * y)\<^sup>\<circ> * x"
proof -
  have "x * (y * x)\<^sup>\<circ> = Rf x (y * 1 \<squnion> y * (x * (y * x)\<^sup>\<circ> * y)) * x"
    by (metis (no_types) circ_mult mult_1_left mult_1_right mult_left_dist_sup mult_right_dist_sup mult_assoc)
  thus ?thesis
    by (metis (no_types) circ_mult mult_1_right mult_left_dist_sup mult_assoc)
qed

subclass itering_3
  apply unfold_locales
  apply (metis circ_mult mult_1_left mult_1_right)
  apply (metis circ_slide order_refl)
  apply (metis circ_sup circ_slide)
  apply (metis circ_slide order_refl)
  apply (metis sup_left_isotone circ_right_unfold mult_left_isotone mult_left_sub_dist_sup_left mult_1_right order_trans circ_simulate_right_plus)
  by (metis sup_commute sup_ge1 sup_right_isotone circ_mult mult_right_isotone mult_1_right order_trans circ_simulate_left_plus)

lemma circ_simulate_right_plus_1:
  "z * x \<le> y * y\<^sup>\<circ> * z \<Longrightarrow> z * x\<^sup>\<circ> \<le> y\<^sup>\<circ> * z"
  by (metis sup_monoid.add_0_right circ_simulate_right_plus mult_left_zero)

lemma circ_simulate_left_plus_1:
  "x * z \<le> z * y\<^sup>\<circ> \<Longrightarrow> x\<^sup>\<circ> * z \<le> z * y\<^sup>\<circ> \<squnion> x\<^sup>\<circ> * bot"
  by (metis sup_monoid.add_0_right circ_simulate_left_plus mult_assoc mult_left_zero mult_right_dist_sup)

lemma circ_simulate_2:
  "y * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ> \<longleftrightarrow> y\<^sup>\<circ> * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ>"
  apply (rule iffI)
  apply (metis sup_assoc sup_monoid.add_0_right circ_loop_fixpoint circ_simulate_left_plus_1 mult_assoc mult_left_zero mult_zero_sup_circ_2)
  by (metis circ_increasing mult_left_isotone order_trans)

lemma circ_simulate_absorb:
  "y * x \<le> x \<Longrightarrow> y\<^sup>\<circ> * x \<le> x \<squnion> y\<^sup>\<circ> * bot"
  by (metis circ_simulate_left_plus_1 circ_zero mult_1_right)

lemma circ_simulate_3:
  "y * x\<^sup>\<circ> \<le> x\<^sup>\<circ> \<Longrightarrow> y\<^sup>\<circ> * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ>"
  by (metis sup.bounded_iff circ_reflexive circ_simulate_2 le_iff_sup mult_right_isotone mult_1_right)

lemma circ_separate_mult_1:
  "y * x \<le> x * y \<Longrightarrow> (x * y)\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ>"
  by (metis circ_mult_sub_sup circ_separate_1)

lemma circ_separate_unfold:
  "(y * x\<^sup>\<circ>)\<^sup>\<circ> = y\<^sup>\<circ> \<squnion> y\<^sup>\<circ> * y * x * x\<^sup>\<circ> * (y * x\<^sup>\<circ>)\<^sup>\<circ>"
  by (metis circ_back_loop_fixpoint circ_plus_same circ_unfold_sum sup_commute mult_assoc)

lemma separation:
  assumes "y * x \<le> x * y\<^sup>\<circ>"
    shows "(x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> * y\<^sup>\<circ>"
proof -
  have "y\<^sup>\<circ> * x * y\<^sup>\<circ> \<le> x * y\<^sup>\<circ> \<squnion> y\<^sup>\<circ> * bot"
    by (metis assms circ_simulate_left_plus_1 circ_transitive_equal mult_assoc mult_left_isotone)
  thus ?thesis
    by (metis sup_commute circ_sup_1 circ_simulate_right circ_sub_dist_3 le_iff_sup mult_assoc mult_left_zero zero_right_mult_decreasing)
qed

lemma simulation:
  "y * x \<le> x * y\<^sup>\<circ> \<Longrightarrow> y\<^sup>\<circ> * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ>"
  by (metis sup_ge2 circ_isotone circ_mult_upper_bound circ_sub_dist separation)

lemma circ_simulate_4:
  assumes "y * x \<le> x * x\<^sup>\<circ> * (1 \<squnion> y)"
    shows "y\<^sup>\<circ> * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ>"
proof -
  have "x \<squnion> (x * x\<^sup>\<circ> * x * x \<squnion> x * x) = x * x\<^sup>\<circ>"
    by (metis (no_types) circ_back_loop_fixpoint mult_right_dist_sup sup_commute)
  hence "x \<le> x * x\<^sup>\<circ> * 1 \<squnion> x * x\<^sup>\<circ> * y"
    by (metis mult_1_right sup_assoc sup_ge1)
  hence "(1 \<squnion> y) * x \<le> x * x\<^sup>\<circ> * (1 \<squnion> y)"
    using assms mult_left_dist_sup mult_right_dist_sup by force
  hence "y * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ>"
    by (metis circ_sup_upper_bound circ_increasing circ_reflexive circ_simulate_right_plus_1 mult_right_isotone mult_right_sub_dist_sup_right order_trans)
  thus ?thesis
    by (metis circ_simulate_2)
qed

lemma circ_simulate_5:
  "y * x \<le> x * x\<^sup>\<circ> * (x \<squnion> y) \<Longrightarrow> y\<^sup>\<circ> * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ>"
  by (metis circ_sup_sub_sup_one circ_simulate_4 order_trans)

lemma circ_simulate_6:
  "y * x \<le> x * (x \<squnion> y) \<Longrightarrow> y\<^sup>\<circ> * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ>"
  by (metis sup_commute circ_back_loop_fixpoint circ_simulate_5 mult_right_sub_dist_sup_left order_trans)

lemma circ_separate_4:
  assumes "y * x \<le> x * x\<^sup>\<circ> * (1 \<squnion> y)"
    shows "(x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> * y\<^sup>\<circ>"
proof -
  have "y * x * x\<^sup>\<circ> \<le> x * x\<^sup>\<circ> * (1 \<squnion> y) * x\<^sup>\<circ>"
    by (simp add: assms mult_left_isotone)
  also have "... = x * x\<^sup>\<circ> \<squnion> x * x\<^sup>\<circ> * y * x\<^sup>\<circ>"
    by (simp add: circ_transitive_equal mult_left_dist_sup mult_right_dist_sup mult_assoc)
  also have "... \<le> x * x\<^sup>\<circ> \<squnion> x * x\<^sup>\<circ> * x\<^sup>\<circ> * y\<^sup>\<circ>"
    by (metis assms sup_right_isotone circ_simulate_2 circ_simulate_4 mult_assoc mult_right_isotone)
  finally have "y * x * x\<^sup>\<circ> \<le> x * x\<^sup>\<circ> * y\<^sup>\<circ>"
    by (metis circ_reflexive circ_transitive_equal le_iff_sup mult_assoc mult_right_isotone mult_1_right)
  thus ?thesis
    by (metis circ_sup_1 left_plus_circ mult_assoc separation)
qed

lemma circ_separate_5:
  "y * x \<le> x * x\<^sup>\<circ> * (x \<squnion> y) \<Longrightarrow> (x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> * y\<^sup>\<circ>"
  by (metis circ_sup_sub_sup_one circ_separate_4 order_trans)

lemma circ_separate_6:
  "y * x \<le> x * (x \<squnion> y) \<Longrightarrow> (x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> * y\<^sup>\<circ>"
  by (metis sup_commute circ_back_loop_fixpoint circ_separate_5 mult_right_sub_dist_sup_left order_trans)

end

class bounded_itering = bounded_idempotent_left_zero_semiring + itering
begin

subclass bounded_left_conway_semiring ..

(*
lemma "1 = x\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma "x = x\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma "x = x * x\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma "x * x\<^sup>\<circ> = x\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma "x\<^sup>\<circ> = x\<^sup>\<circ>\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma "(x * y)\<^sup>\<circ> = (x \<squnion> y)\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma "x\<^sup>\<circ> * y\<^sup>\<circ> = (x \<squnion> y)\<^sup>\<circ>" nitpick [expect=genuine,card=6] oops
lemma "(x \<squnion> y)\<^sup>\<circ> = (x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma "1 = 1\<^sup>\<circ>" nitpick [expect=genuine] oops

lemma "1 = (x * bot)\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma "1 \<squnion> x * bot = x\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma "x\<^sup>\<circ> = x\<^sup>\<circ> * 1\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma "z \<squnion> y * x = x \<longrightarrow> y\<^sup>\<circ> * z \<le> x" nitpick [expect=genuine] oops
lemma "y * x = x \<longrightarrow> y\<^sup>\<circ> * x \<le> x" nitpick [expect=genuine] oops
lemma "z \<squnion> x * y = x \<longrightarrow> z * y\<^sup>\<circ> \<le> x" nitpick [expect=genuine] oops
lemma "x * y = x \<longrightarrow> x * y\<^sup>\<circ> \<le> x" nitpick [expect=genuine] oops
lemma "x = z \<squnion> y * x \<longrightarrow> x \<le> y\<^sup>\<circ> * z" nitpick [expect=genuine] oops
lemma "x = y * x \<longrightarrow> x \<le> y\<^sup>\<circ>" nitpick [expect=genuine] oops
lemma "x * z = z * y \<longrightarrow> x\<^sup>\<circ> * z \<le> z * y\<^sup>\<circ>" nitpick [expect=genuine] oops

lemma "x\<^sup>\<circ> = (x * x)\<^sup>\<circ> * (x \<squnion> 1)" oops
lemma "y\<^sup>\<circ> * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ> \<longrightarrow> (x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> * y\<^sup>\<circ>" oops
lemma "y * x \<le> (1 \<squnion> x) * y\<^sup>\<circ> \<longrightarrow> (x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> * y\<^sup>\<circ>" oops
lemma "y * x \<le> x \<longrightarrow> y\<^sup>\<circ> * x \<le> 1\<^sup>\<circ> * x" oops
*)

end

text \<open>
We finally expand Conway semirings and iterings by an element that corresponds to the endless loop.
\<close>

class L =
  fixes L :: "'a"

class left_conway_semiring_L = left_conway_semiring + L +
  assumes one_circ_mult_split: "1\<^sup>\<circ> * x = L \<squnion> x"
  assumes L_split_sup: "x * (y \<squnion> L) \<le> x * y \<squnion> L"
begin

lemma L_def:
  "L = 1\<^sup>\<circ> * bot"
  by (metis sup_monoid.add_0_right one_circ_mult_split)

lemma one_circ_split:
  "1\<^sup>\<circ> = L \<squnion> 1"
  by (metis mult_1_right one_circ_mult_split)

lemma one_circ_circ_split:
  "1\<^sup>\<circ>\<^sup>\<circ> = L \<squnion> 1"
  by (metis circ_one one_circ_split)

lemma sub_mult_one_circ:
  "x * 1\<^sup>\<circ> \<le> 1\<^sup>\<circ> * x"
  by (metis L_split_sup sup_commute mult_1_right one_circ_mult_split)

lemma one_circ_mult_split_2:
  "1\<^sup>\<circ> * x = x * 1\<^sup>\<circ> \<squnion> L"
proof -
  have 1: "x * 1\<^sup>\<circ> \<le> L \<squnion> x"
    using one_circ_mult_split sub_mult_one_circ by presburger
  have "x \<squnion> x * 1\<^sup>\<circ> = x * 1\<^sup>\<circ>"
    by (meson circ_back_loop_prefixpoint le_iff_sup sup.boundedE)
  thus ?thesis
    using 1 by (simp add: le_iff_sup one_circ_mult_split sup_assoc sup_commute)
qed

lemma sub_mult_one_circ_split:
  "x * 1\<^sup>\<circ> \<le> x \<squnion> L"
  by (metis sup_commute one_circ_mult_split sub_mult_one_circ)

lemma sub_mult_one_circ_split_2:
  "x * 1\<^sup>\<circ> \<le> x \<squnion> 1\<^sup>\<circ>"
  by (metis L_def sup_right_isotone order_trans sub_mult_one_circ_split zero_right_mult_decreasing)

lemma L_split:
  "x * L \<le> x * bot \<squnion> L"
  by (metis L_split_sup sup_monoid.add_0_left)

lemma L_left_zero:
  "L * x = L"
  by (metis L_def mult_assoc mult_left_zero)

lemma one_circ_L:
  "1\<^sup>\<circ> * L = L"
  by (metis L_def circ_transitive_equal mult_assoc)

lemma mult_L_circ:
  "(x * L)\<^sup>\<circ> = 1 \<squnion> x * L"
  by (metis L_left_zero circ_left_unfold mult_assoc)

lemma mult_L_circ_mult:
  "(x * L)\<^sup>\<circ> * y = y \<squnion> x * L"
  by (metis L_left_zero mult_L_circ mult_assoc mult_1_left mult_right_dist_sup)

lemma circ_L:
  "L\<^sup>\<circ> = L \<squnion> 1"
  by (metis L_left_zero sup_commute circ_left_unfold)

lemma L_below_one_circ:
  "L \<le> 1\<^sup>\<circ>"
  by (metis L_def zero_right_mult_decreasing)

lemma circ_circ_mult_1:
  "x\<^sup>\<circ> * 1\<^sup>\<circ> = x\<^sup>\<circ>\<^sup>\<circ>"
  by (metis L_left_zero sup_commute circ_sup_1 circ_circ_sup mult_zero_circ one_circ_split)

lemma circ_circ_mult:
  "1\<^sup>\<circ> * x\<^sup>\<circ> = x\<^sup>\<circ>\<^sup>\<circ>"
  by (metis antisym circ_circ_mult_1 circ_circ_sub_mult sub_mult_one_circ)

lemma circ_circ_split:
  "x\<^sup>\<circ>\<^sup>\<circ> = L \<squnion> x\<^sup>\<circ>"
  by (metis circ_circ_mult one_circ_mult_split)

lemma circ_sup_6:
  "L \<squnion> (x \<squnion> y)\<^sup>\<circ> = (x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<circ>"
  by (metis sup_assoc sup_commute circ_sup_1 circ_circ_sup circ_circ_split circ_decompose_4)

end

class itering_L = itering + L +
  assumes L_def: "L = 1\<^sup>\<circ> * bot"
begin

lemma one_circ_split:
  "1\<^sup>\<circ> = L \<squnion> 1"
  by (metis L_def sup_commute antisym circ_sup_upper_bound circ_reflexive circ_simulate_absorb mult_1_right order_refl zero_right_mult_decreasing)

lemma one_circ_mult_split:
  "1\<^sup>\<circ> * x = L \<squnion> x"
  by (metis L_def sup_commute circ_loop_fixpoint mult_assoc mult_left_zero mult_zero_circ one_circ_split)

lemma sub_mult_one_circ_split:
  "x * 1\<^sup>\<circ> \<le> x \<squnion> L"
  by (metis sup_commute one_circ_mult_split sub_mult_one_circ)

lemma sub_mult_one_circ_split_2:
  "x * 1\<^sup>\<circ> \<le> x \<squnion> 1\<^sup>\<circ>"
  by (metis L_def sup_right_isotone order_trans sub_mult_one_circ_split zero_right_mult_decreasing)

lemma L_split:
  "x * L \<le> x * bot \<squnion> L"
  by (metis L_def mult_assoc mult_left_isotone mult_right_dist_sup sub_mult_one_circ_split_2)

subclass left_conway_semiring_L
  apply unfold_locales
  apply (metis L_def sup_commute circ_loop_fixpoint mult_assoc mult_left_zero mult_zero_circ one_circ_split)
  by (metis sup_commute mult_assoc mult_left_isotone one_circ_mult_split sub_mult_one_circ)

lemma circ_left_induct_mult_L:
  "L \<le> x \<Longrightarrow> x * y \<le> x \<Longrightarrow> x * y\<^sup>\<circ> \<le> x"
  by (metis circ_one circ_simulate le_iff_sup one_circ_mult_split)

lemma circ_left_induct_mult_iff_L:
  "L \<le> x \<Longrightarrow> x * y \<le> x \<longleftrightarrow> x * y\<^sup>\<circ> \<le> x"
  by (metis sup.bounded_iff circ_back_loop_fixpoint circ_left_induct_mult_L le_iff_sup)

lemma circ_left_induct_L:
  "L \<le> x \<Longrightarrow> x * y \<squnion> z \<le> x \<Longrightarrow> z * y\<^sup>\<circ> \<le> x"
  by (metis sup.bounded_iff circ_left_induct_mult_L le_iff_sup mult_right_dist_sup)

end

end

