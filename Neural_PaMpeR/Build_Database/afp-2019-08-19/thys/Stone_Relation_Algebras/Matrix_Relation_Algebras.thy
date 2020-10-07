(* Title:      Matrix Relation Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Matrix Relation Algebras\<close>

text \<open>
This theory gives matrix models of Stone relation algebras and more general structures.
We consider only square matrices.
The main result is that matrices over Stone relation algebras form a Stone relation algebra.

We use the monoid structure underlying semilattices to provide finite sums, which are necessary for defining the composition of two matrices.
See \cite{ArmstrongFosterStruthWeber2016,ArmstrongGomesStruthWeber2016} for similar liftings to matrices for semirings and relation algebras.
A technical difference is that those theories are mostly based on semirings whereas our hierarchy is mostly based on lattices (and our semirings directly inherit from semilattices).

Relation algebras have both a semiring and a lattice structure such that semiring addition and lattice join coincide.
In particular, finite sums and finite suprema coincide.
Isabelle/HOL has separate theories for semirings and lattices, based on separate addition and join operations and different operations for finite sums and finite suprema.
Reusing results from both theories is beneficial for relation algebras, but not always easy to realise.
\<close>

theory Matrix_Relation_Algebras

imports Relation_Algebras

begin

subsection \<open>Finite Suprema\<close>

text \<open>
We consider finite suprema in idempotent semirings and Stone relation algebras.
We mostly use the first of the following notations, which denotes the supremum of expressions \<open>t(x)\<close> over all \<open>x\<close> from the type of \<open>x\<close>.
For finite types, this is implemented in Isabelle/HOL as the repeated application of binary suprema.
\<close>

syntax
  "_sum_sup_monoid" :: "idt \<Rightarrow> 'a::bounded_semilattice_sup_bot \<Rightarrow> 'a" ("(\<Squnion>\<^sub>_ _)" [0,10] 10)
  "_sum_sup_monoid_bounded" :: "idt \<Rightarrow> 'b set \<Rightarrow> 'a::bounded_semilattice_sup_bot \<Rightarrow> 'a" ("(\<Squnion>\<^bsub>_\<in>_\<^esub> _)" [0,51,10] 10)
translations
  "\<Squnion>\<^sub>x t" => "XCONST sup_monoid.sum (\<lambda>x . t) { x . CONST True }"
  "\<Squnion>\<^bsub>x\<in>X\<^esub> t" => "XCONST sup_monoid.sum (\<lambda>x . t) X"

context idempotent_semiring
begin

text \<open>
The following induction principles are useful for comparing two suprema.
The first principle works because types are not empty.
\<close>

lemma one_sup_induct [case_names one sup]:
  fixes f g :: "'b::finite \<Rightarrow> 'a"
  assumes one: "\<And>i . P (f i) (g i)"
      and sup: "\<And>j I . j \<notin> I \<Longrightarrow> P (\<Squnion>\<^bsub>i\<in>I\<^esub> f i) (\<Squnion>\<^bsub>i\<in>I\<^esub> g i) \<Longrightarrow> P (f j \<squnion> (\<Squnion>\<^bsub>i\<in>I\<^esub> f i)) (g j \<squnion> (\<Squnion>\<^bsub>i\<in>I\<^esub> g i))"
    shows "P (\<Squnion>\<^sub>k f k) (\<Squnion>\<^sub>k g k)"
proof -
  let ?X = "{ k::'b . True }"
  have "finite ?X" and "?X \<noteq> {}"
    by auto
  thus ?thesis
  proof (induct rule: finite_ne_induct)
    case (singleton i) thus ?case
      using one by simp
  next
    case (insert j I) thus ?case
      using sup by simp
  qed
qed

lemma bot_sup_induct [case_names bot sup]:
  fixes f g :: "'b::finite \<Rightarrow> 'a"
  assumes bot: "P bot bot"
      and sup: "\<And>j I . j \<notin> I \<Longrightarrow> P (\<Squnion>\<^bsub>i\<in>I\<^esub> f i) (\<Squnion>\<^bsub>i\<in>I\<^esub> g i) \<Longrightarrow> P (f j \<squnion> (\<Squnion>\<^bsub>i\<in>I\<^esub> f i)) (g j \<squnion> (\<Squnion>\<^bsub>i\<in>I\<^esub> g i))"
    shows "P (\<Squnion>\<^sub>k f k) (\<Squnion>\<^sub>k g k)"
  apply (induct rule: one_sup_induct)
  using bot sup apply fastforce
  using sup by blast

text \<open>
Now many properties of finite suprema follow by simple applications of the above induction rules.
In particular, we show distributivity of composition, isotonicity and the upper-bound property.
\<close>

lemma comp_right_dist_sum:
  fixes f :: "'b::finite \<Rightarrow> 'a"
  shows "(\<Squnion>\<^sub>k f k * x) = (\<Squnion>\<^sub>k f k) * x"
proof (induct rule: one_sup_induct)
  case one show ?case
    by simp
next
  case (sup j I) thus ?case
    using mult_right_dist_sup by auto
qed

lemma comp_left_dist_sum:
  fixes f :: "'b::finite \<Rightarrow> 'a"
  shows "(\<Squnion>\<^sub>k x * f k) = x * (\<Squnion>\<^sub>k f k)"
proof (induct rule: one_sup_induct)
  case one show ?case
    by simp
next
  case (sup j I) thus ?case
    by (simp add: mult_left_dist_sup)
qed

lemma leq_sum:
  fixes f g :: "'b::finite \<Rightarrow> 'a"
  shows "(\<forall>k . f k \<le> g k) \<Longrightarrow> (\<Squnion>\<^sub>k f k) \<le> (\<Squnion>\<^sub>k g k)"
proof (induct rule: one_sup_induct)
  case one thus ?case
    by simp
next
  case (sup j I) thus ?case
    using sup_mono by blast
qed

lemma ub_sum:
  fixes f :: "'b::finite \<Rightarrow> 'a"
  shows "f i \<le> (\<Squnion>\<^sub>k f k)"
proof -
  have "i \<in> { k . True }"
    by simp
  thus "f i \<le> (\<Squnion>\<^sub>k f (k::'b))"
    by (metis finite_code sup_monoid.sum.insert sup_ge1 mk_disjoint_insert)
qed

lemma lub_sum:
  fixes f :: "'b::finite \<Rightarrow> 'a"
  assumes "\<forall>k . f k \<le> x"
    shows "(\<Squnion>\<^sub>k f k) \<le> x"
proof (induct rule: one_sup_induct)
  case one show ?case
    by (simp add: assms)
next
  case (sup j I) thus ?case
    using assms le_supI by blast
qed

lemma lub_sum_iff:
  fixes f :: "'b::finite \<Rightarrow> 'a"
  shows "(\<forall>k . f k \<le> x) \<longleftrightarrow> (\<Squnion>\<^sub>k f k) \<le> x"
  using order.trans ub_sum lub_sum by blast

end

context stone_relation_algebra
begin

text \<open>
In Stone relation algebras, we can also show that converse,  double complement and meet distribute over finite suprema.
\<close>

lemma conv_dist_sum:
  fixes f :: "'b::finite \<Rightarrow> 'a"
  shows "(\<Squnion>\<^sub>k (f k)\<^sup>T) = (\<Squnion>\<^sub>k f k)\<^sup>T"
proof (induct rule: one_sup_induct)
  case one show ?case
    by simp
next
  case (sup j I) thus ?case
    by (simp add: conv_dist_sup)
qed

lemma pp_dist_sum:
  fixes f :: "'b::finite \<Rightarrow> 'a"
  shows "(\<Squnion>\<^sub>k --f k) = --(\<Squnion>\<^sub>k f k)"
proof (induct rule: one_sup_induct)
  case one show ?case
    by simp
next
  case (sup j I) thus ?case
    by simp
qed

lemma inf_right_dist_sum:
  fixes f :: "'b::finite \<Rightarrow> 'a"
  shows "(\<Squnion>\<^sub>k f k \<sqinter> x) = (\<Squnion>\<^sub>k f k) \<sqinter> x"
  by (rule comp_inf.comp_right_dist_sum)

end

subsection \<open>Square Matrices\<close>

text \<open>
Because our semiring and relation algebra type classes only work for homogeneous relations, we only look at square matrices.
\<close>

type_synonym ('a,'b) square = "'a \<times> 'a \<Rightarrow> 'b"

text \<open>
We use standard matrix operations.
The Stone algebra structure is lifted componentwise.
Composition is matrix multiplication using given composition and supremum operations.
Its unit lifts given zero and one elements into an identity matrix.
Converse is matrix transpose with an additional componentwise transpose.
\<close>

definition less_eq_matrix :: "('a,'b::ord) square \<Rightarrow> ('a,'b) square \<Rightarrow> bool"                                           (infix "\<preceq>" 50)   where "f \<preceq> g = (\<forall>e . f e \<le> g e)"
definition less_matrix    :: "('a,'b::ord) square \<Rightarrow> ('a,'b) square \<Rightarrow> bool"                                           (infix "\<prec>" 50)   where "f \<prec> g = (f \<preceq> g \<and> \<not> g \<preceq> f)"
definition sup_matrix     :: "('a,'b::sup) square \<Rightarrow> ('a,'b) square \<Rightarrow> ('a,'b) square"                                 (infixl "\<oplus>" 65)  where "f \<oplus> g = (\<lambda>e . f e \<squnion> g e)"
definition inf_matrix     :: "('a,'b::inf) square \<Rightarrow> ('a,'b) square \<Rightarrow> ('a,'b) square"                                 (infixl "\<otimes>" 67)  where "f \<otimes> g = (\<lambda>e . f e \<sqinter> g e)"
definition minus_matrix   :: "('a,'b::{uminus,inf}) square \<Rightarrow> ('a,'b) square \<Rightarrow> ('a,'b) square"                        (infixl "\<ominus>" 65)  where "f \<ominus> g = (\<lambda>e . f e \<sqinter> -g e)"
definition implies_matrix :: "('a,'b::implies) square \<Rightarrow> ('a,'b) square \<Rightarrow> ('a,'b) square"                             (infixl "\<oslash>" 65)  where "f \<oslash> g = (\<lambda>e . f e \<leadsto> g e)"
definition times_matrix   :: "('a,'b::{times,bounded_semilattice_sup_bot}) square \<Rightarrow> ('a,'b) square \<Rightarrow> ('a,'b) square" (infixl "\<odot>" 70)  where "f \<odot> g = (\<lambda>(i,j) . \<Squnion>\<^sub>k f (i,k) * g (k,j))"
definition uminus_matrix  :: "('a,'b::uminus) square \<Rightarrow> ('a,'b) square"                                                ("\<ominus> _" [80] 80)  where "\<ominus>f    = (\<lambda>e . -f e)"
definition conv_matrix    :: "('a,'b::conv) square \<Rightarrow> ('a,'b) square"                                                  ("_\<^sup>t" [100] 100) where "f\<^sup>t      = (\<lambda>(i,j) . (f (j,i))\<^sup>T)"
definition bot_matrix     :: "('a,'b::bot) square"                                                                     ("mbot")         where "mbot   = (\<lambda>e . bot)"
definition top_matrix     :: "('a,'b::top) square"                                                                     ("mtop")         where "mtop   = (\<lambda>e . top)"
definition one_matrix     :: "('a,'b::{one,bot}) square"                                                               ("mone")         where "mone   = (\<lambda>(i,j) . if i = j then 1 else bot)"

subsection \<open>Stone Algebras\<close>

text \<open>
We first lift the Stone algebra structure.
Because all operations are componentwise, this also works for infinite matrices.
\<close>

interpretation matrix_order: order where less_eq = less_eq_matrix and less = "less_matrix :: ('a,'b::order) square \<Rightarrow> ('a,'b) square \<Rightarrow> bool"
  apply unfold_locales
  apply (simp add: less_matrix_def)
  apply (simp add: less_eq_matrix_def)
  apply (meson less_eq_matrix_def order_trans)
  by (meson less_eq_matrix_def antisym ext)

interpretation matrix_semilattice_sup: semilattice_sup where sup = sup_matrix and less_eq = less_eq_matrix and less = "less_matrix :: ('a,'b::semilattice_sup) square \<Rightarrow> ('a,'b) square \<Rightarrow> bool"
  apply unfold_locales
  apply (simp add: sup_matrix_def less_eq_matrix_def)
  apply (simp add: sup_matrix_def less_eq_matrix_def)
  by (simp add: sup_matrix_def less_eq_matrix_def)

interpretation matrix_semilattice_inf: semilattice_inf where inf = inf_matrix and less_eq = less_eq_matrix and less = "less_matrix :: ('a,'b::semilattice_inf) square \<Rightarrow> ('a,'b) square \<Rightarrow> bool"
  apply unfold_locales
  apply (simp add: inf_matrix_def less_eq_matrix_def)
  apply (simp add: inf_matrix_def less_eq_matrix_def)
  by (simp add: inf_matrix_def less_eq_matrix_def)

interpretation matrix_bounded_semilattice_sup_bot: bounded_semilattice_sup_bot where sup = sup_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a,'b::bounded_semilattice_sup_bot) square"
  apply unfold_locales
  by (simp add: bot_matrix_def less_eq_matrix_def)

interpretation matrix_bounded_semilattice_inf_top: bounded_semilattice_inf_top where inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and top = "top_matrix :: ('a,'b::bounded_semilattice_inf_top) square"
  apply unfold_locales
  by (simp add: less_eq_matrix_def top_matrix_def)

interpretation matrix_lattice: lattice where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = "less_matrix :: ('a,'b::lattice) square \<Rightarrow> ('a,'b) square \<Rightarrow> bool" ..

interpretation matrix_distrib_lattice: distrib_lattice where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = "less_matrix :: ('a,'b::distrib_lattice) square \<Rightarrow> ('a,'b) square \<Rightarrow> bool"
  apply unfold_locales
  by (simp add: sup_inf_distrib1 sup_matrix_def inf_matrix_def)

interpretation matrix_bounded_lattice: bounded_lattice where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a,'b::bounded_lattice) square" and top = top_matrix ..

interpretation matrix_bounded_distrib_lattice: bounded_distrib_lattice where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a,'b::bounded_distrib_lattice) square" and top = top_matrix ..

interpretation matrix_p_algebra: p_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a,'b::p_algebra) square" and top = top_matrix and uminus = uminus_matrix
  apply unfold_locales
  apply (unfold inf_matrix_def bot_matrix_def less_eq_matrix_def uminus_matrix_def)
  by (meson pseudo_complement)

interpretation matrix_pd_algebra: pd_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a,'b::pd_algebra) square" and top = top_matrix and uminus = uminus_matrix ..

text \<open>
In particular, matrices over Stone algebras form a Stone algebra.
\<close>

interpretation matrix_stone_algebra: stone_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a,'b::stone_algebra) square" and top = top_matrix and uminus = uminus_matrix
  by unfold_locales (simp add: sup_matrix_def uminus_matrix_def top_matrix_def)

interpretation matrix_heyting_stone_algebra: heyting_stone_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a,'b::heyting_stone_algebra) square" and top = top_matrix and uminus = uminus_matrix and implies = implies_matrix
  apply unfold_locales
  apply (unfold inf_matrix_def sup_matrix_def bot_matrix_def top_matrix_def less_eq_matrix_def uminus_matrix_def implies_matrix_def)
  apply (simp add: implies_galois)
  apply (simp add: uminus_eq)
  by simp

interpretation matrix_boolean_algebra: boolean_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a,'b::boolean_algebra) square" and top = top_matrix and uminus = uminus_matrix and minus = minus_matrix
  apply unfold_locales
  apply simp
  apply (simp add: sup_matrix_def uminus_matrix_def top_matrix_def)
  by (simp add: inf_matrix_def uminus_matrix_def minus_matrix_def)

subsection \<open>Semirings\<close>

text \<open>
Next, we lift the semiring structure.
Because of composition, this requires a restriction to finite matrices.
\<close>

interpretation matrix_monoid: monoid_mult where times = times_matrix and one = "one_matrix :: ('a::finite,'b::idempotent_semiring) square"
proof
  fix f g h :: "('a,'b) square"
  show "(f \<odot> g) \<odot> h = f \<odot> (g \<odot> h)"
  proof (rule ext, rule prod_cases)
    fix i j
    have "((f \<odot> g) \<odot> h) (i,j) = (\<Squnion>\<^sub>l (f \<odot> g) (i,l) * h (l,j))"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>l (\<Squnion>\<^sub>k f (i,k) * g (k,l)) * h (l,j))"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>l \<Squnion>\<^sub>k (f (i,k) * g (k,l)) * h (l,j))"
      by (metis (no_types) comp_right_dist_sum)
    also have "... = (\<Squnion>\<^sub>l \<Squnion>\<^sub>k f (i,k) * (g (k,l) * h (l,j)))"
      by (simp add: mult.assoc)
    also have "... = (\<Squnion>\<^sub>k \<Squnion>\<^sub>l f (i,k) * (g (k,l) * h (l,j)))"
      using sup_monoid.sum.swap by auto
    also have "... = (\<Squnion>\<^sub>k f (i,k) * (\<Squnion>\<^sub>l g (k,l) * h (l,j)))"
      by (metis (no_types) comp_left_dist_sum)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * (g \<odot> h) (k,j))"
      by (simp add: times_matrix_def)
    also have "... = (f \<odot> (g \<odot> h)) (i,j)"
      by (simp add: times_matrix_def)
    finally show "((f \<odot> g) \<odot> h) (i,j) = (f \<odot> (g \<odot> h)) (i,j)"
      .
  qed
next
  fix f :: "('a,'b) square"
  show "mone \<odot> f = f"
  proof (rule ext, rule prod_cases)
    fix i j
    have "(mone \<odot> f) (i,j) = (\<Squnion>\<^sub>k mone (i,k) * f (k,j))"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>k (if i = k then 1 else bot) * f (k,j))"
      by (simp add: one_matrix_def)
    also have "... = (\<Squnion>\<^sub>k if i = k then 1 * f (k,j) else bot * f (k,j))"
      by (metis (full_types, hide_lams))
    also have "... = (\<Squnion>\<^sub>k if i = k then f (k,j) else bot)"
      by (meson mult_left_one mult_left_zero)
    also have "... = f (i,j)"
      by simp
    finally show "(mone \<odot> f) (i,j) = f (i,j)"
      .
  qed
next
  fix f :: "('a,'b) square"
  show "f \<odot> mone = f"
  proof (rule ext, rule prod_cases)
    fix i j
    have "(f \<odot> mone) (i,j) = (\<Squnion>\<^sub>k f (i,k) * mone (k,j))"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * (if k = j then 1 else bot))"
      by (simp add: one_matrix_def)
    also have "... = (\<Squnion>\<^sub>k if k = j then f (i,k) * 1 else f (i,k) * bot)"
      by (metis (full_types, hide_lams))
    also have "... = (\<Squnion>\<^sub>k if k = j then f (i,k) else bot)"
      by (meson mult.right_neutral semiring.mult_zero_right)
    also have "... = f (i,j)"
      by simp
    finally show "(f \<odot> mone) (i,j) = f (i,j)"
      .
  qed
qed

interpretation matrix_idempotent_semiring: idempotent_semiring where sup = sup_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a::finite,'b::idempotent_semiring) square" and one = one_matrix and times = times_matrix
proof
  fix f g h :: "('a,'b) square"
  show "f \<odot> g \<oplus> f \<odot> h \<preceq> f \<odot> (g \<oplus> h)"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix i j
    have "(f \<odot> g \<oplus> f \<odot> h) (i,j) = (f \<odot> g) (i,j) \<squnion> (f \<odot> h) (i,j)"
      by (simp add: sup_matrix_def)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * g (k,j)) \<squnion> (\<Squnion>\<^sub>k f (i,k) * h (k,j))"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * g (k,j) \<squnion> f (i,k) * h (k,j))"
      by (simp add: sup_monoid.sum.distrib)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * (g (k,j) \<squnion> h (k,j)))"
      by (simp add: mult_left_dist_sup)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * (g \<oplus> h) (k,j))"
      by (simp add: sup_matrix_def)
    also have "... = (f \<odot> (g \<oplus> h)) (i,j)"
      by (simp add: times_matrix_def)
    finally show "(f \<odot> g \<oplus> f \<odot> h) (i,j) \<le> (f \<odot> (g \<oplus> h)) (i,j)"
      by simp
  qed
next
  fix f g h :: "('a,'b) square"
  show "(f \<oplus> g) \<odot> h = f \<odot> h \<oplus> g \<odot> h"
  proof (rule ext, rule prod_cases)
    fix i j
    have "((f \<oplus> g) \<odot> h) (i,j) = (\<Squnion>\<^sub>k (f \<oplus> g) (i,k) * h (k,j))"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>k (f (i,k) \<squnion> g (i,k)) * h (k,j))"
      by (simp add: sup_matrix_def)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * h (k,j) \<squnion> g (i,k) * h (k,j))"
      by (meson mult_right_dist_sup)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * h (k,j)) \<squnion> (\<Squnion>\<^sub>k g (i,k) * h (k,j))"
      by (simp add: sup_monoid.sum.distrib)
    also have "... = (f \<odot> h) (i,j) \<squnion> (g \<odot> h) (i,j)"
      by (simp add: times_matrix_def)
    also have "... = (f \<odot> h \<oplus> g \<odot> h) (i,j)"
      by (simp add: sup_matrix_def)
    finally show "((f \<oplus> g) \<odot> h) (i,j) = (f \<odot> h \<oplus> g \<odot> h) (i,j)"
      .
  qed
next
  fix f :: "('a,'b) square"
  show "mbot \<odot> f = mbot"
  proof (rule ext, rule prod_cases)
    fix i j
    have "(mbot \<odot> f) (i,j) = (\<Squnion>\<^sub>k mbot (i,k) * f (k,j))"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>k bot * f (k,j))"
      by (simp add: bot_matrix_def)
    also have "... = bot"
      by simp
    also have "... = mbot (i,j)"
      by (simp add: bot_matrix_def)
    finally show "(mbot \<odot> f) (i,j) = mbot (i,j)"
      .
  qed
next
  fix f :: "('a,'b) square"
  show "mone \<odot> f = f"
    by simp
next
  fix f :: "('a,'b) square"
  show "f \<preceq> f \<odot> mone"
    by simp
next
  fix f g h :: "('a,'b) square"
  show "f \<odot> (g \<oplus> h) = f \<odot> g \<oplus> f \<odot> h"
  proof (rule ext, rule prod_cases)
    fix i j
    have "(f \<odot> (g \<oplus> h)) (i,j) = (\<Squnion>\<^sub>k f (i,k) * (g \<oplus> h) (k,j))"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * (g (k,j) \<squnion> h (k,j)))"
      by (simp add: sup_matrix_def)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * g (k,j) \<squnion> f (i,k) * h (k,j))"
      by (meson mult_left_dist_sup)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * g (k,j)) \<squnion> (\<Squnion>\<^sub>k f (i,k) * h (k,j))"
      by (simp add: sup_monoid.sum.distrib)
    also have "... = (f \<odot> g) (i,j) \<squnion> (f \<odot> h) (i,j)"
      by (simp add: times_matrix_def)
    also have "... = (f \<odot> g \<oplus> f \<odot> h) (i,j)"
      by (simp add: sup_matrix_def)
    finally show "(f \<odot> (g \<oplus> h)) (i,j) = (f \<odot> g \<oplus> f \<odot> h) (i,j)"
      .
  qed
next
  fix f :: "('a,'b) square"
  show "f \<odot> mbot = mbot"
  proof (rule ext, rule prod_cases)
    fix i j
    have "(f \<odot> mbot) (i,j) = (\<Squnion>\<^sub>k f (i,k) * mbot (k,j))"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * bot)"
      by (simp add: bot_matrix_def)
    also have "... = bot"
      by simp
    also have "... = mbot (i,j)"
      by (simp add: bot_matrix_def)
    finally show "(f \<odot> mbot) (i,j) = mbot (i,j)"
      .
  qed
qed

interpretation matrix_bounded_idempotent_semiring: bounded_idempotent_semiring where sup = sup_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a::finite,'b::bounded_idempotent_semiring) square" and top = top_matrix and one = one_matrix and times = times_matrix
proof
  fix f :: "('a,'b) square"
  show "f \<oplus> mtop = mtop"
  proof
    fix e
    have "(f \<oplus> mtop) e = f e \<squnion> mtop e"
      by (simp add: sup_matrix_def)
    also have "... = f e \<squnion> top"
      by (simp add: top_matrix_def)
    also have "... = top"
      by simp
    also have "... = mtop e"
      by (simp add: top_matrix_def)
    finally show "(f \<oplus> mtop) e = mtop e"
      .
  qed
qed

subsection \<open>Stone Relation Algebras\<close>

text \<open>
Finally, we show that matrices over Stone relation algebras form a Stone relation algebra.
\<close>

interpretation matrix_stone_relation_algebra: stone_relation_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a::finite,'b::stone_relation_algebra) square" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix
proof
  fix f g h :: "('a,'b) square"
  show "(f \<odot> g) \<odot> h = f \<odot> (g \<odot> h)"
    by (simp add: matrix_monoid.mult_assoc)
next
  fix f g h :: "('a,'b) square"
  show "(f \<oplus> g) \<odot> h = f \<odot> h \<oplus> g \<odot> h"
    by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
next
  fix f :: "('a,'b) square"
  show "mbot \<odot> f = mbot"
    by simp
next
  fix f :: "('a,'b) square"
  show "mone \<odot> f = f"
    by simp
next
  fix f :: "('a,'b) square"
  show "f\<^sup>t\<^sup>t = f"
  proof (rule ext, rule prod_cases)
    fix i j
    have "(f\<^sup>t\<^sup>t) (i,j) = ((f\<^sup>t) (j,i))\<^sup>T"
      by (simp add: conv_matrix_def)
    also have "... = f (i,j)"
      by (simp add: conv_matrix_def)
    finally show "(f\<^sup>t\<^sup>t) (i,j) = f (i,j)"
      .
  qed
next
  fix f g :: "('a,'b) square"
  show "(f \<oplus> g)\<^sup>t = f\<^sup>t \<oplus> g\<^sup>t"
  proof (rule ext, rule prod_cases)
    fix i j
    have "((f \<oplus> g)\<^sup>t) (i,j) = ((f \<oplus> g) (j,i))\<^sup>T"
      by (simp add: conv_matrix_def)
    also have "... = (f (j,i) \<squnion> g (j,i))\<^sup>T"
      by (simp add: sup_matrix_def)
    also have "... = (f\<^sup>t) (i,j) \<squnion> (g\<^sup>t) (i,j)"
      by (simp add: conv_matrix_def conv_dist_sup)
    also have "... = (f\<^sup>t \<oplus> g\<^sup>t) (i,j)"
      by (simp add: sup_matrix_def)
    finally show "((f \<oplus> g)\<^sup>t) (i,j) = (f\<^sup>t \<oplus> g\<^sup>t) (i,j)"
      .
  qed
next
  fix f g :: "('a,'b) square"
  show "(f \<odot> g)\<^sup>t = g\<^sup>t \<odot> f\<^sup>t"
  proof (rule ext, rule prod_cases)
    fix i j
    have "((f \<odot> g)\<^sup>t) (i,j) = ((f \<odot> g) (j,i))\<^sup>T"
      by (simp add: conv_matrix_def)
    also have "... = (\<Squnion>\<^sub>k f (j,k) * g (k,i))\<^sup>T"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>k (f (j,k) * g (k,i))\<^sup>T)"
      by (metis (no_types) conv_dist_sum)
    also have "... = (\<Squnion>\<^sub>k (g (k,i))\<^sup>T * (f (j,k))\<^sup>T)"
      by (simp add: conv_dist_comp)
    also have "... = (\<Squnion>\<^sub>k (g\<^sup>t) (i,k) * (f\<^sup>t) (k,j))"
      by (simp add: conv_matrix_def)
    also have "... = (g\<^sup>t \<odot> f\<^sup>t) (i,j)"
      by (simp add: times_matrix_def)
    finally show "((f \<odot> g)\<^sup>t) (i,j) = (g\<^sup>t \<odot> f\<^sup>t) (i,j)"
      .
  qed
next
  fix f g h :: "('a,'b) square"
  show "(f \<odot> g) \<otimes> h \<preceq> f \<odot> (g \<otimes> (f\<^sup>t \<odot> h))"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix i j
    have "((f \<odot> g) \<otimes> h) (i,j) = (f \<odot> g) (i,j) \<sqinter> h (i,j)"
      by (simp add: inf_matrix_def)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * g (k,j)) \<sqinter> h (i,j)"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * g (k,j) \<sqinter> h (i,j))"
      by (metis (no_types) inf_right_dist_sum)
    also have "... \<le> (\<Squnion>\<^sub>k f (i,k) * (g (k,j) \<sqinter> (f (i,k))\<^sup>T * h (i,j)))"
      by (rule leq_sum, meson dedekind_1)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * (g (k,j) \<sqinter> (f\<^sup>t) (k,i) * h (i,j)))"
      by (simp add: conv_matrix_def)
    also have "... \<le> (\<Squnion>\<^sub>k f (i,k) * (g (k,j) \<sqinter> (\<Squnion>\<^sub>l (f\<^sup>t) (k,l) * h (l,j))))"
      by (rule leq_sum, rule allI, rule comp_right_isotone, rule inf.sup_right_isotone, rule ub_sum)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * (g (k,j) \<sqinter> (f\<^sup>t \<odot> h) (k,j)))"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>k f (i,k) * (g \<otimes> (f\<^sup>t \<odot> h)) (k,j))"
      by (simp add: inf_matrix_def)
    also have "... = (f \<odot> (g \<otimes> (f\<^sup>t \<odot> h))) (i,j)"
      by (simp add: times_matrix_def)
    finally show "((f \<odot> g) \<otimes> h) (i,j) \<le> (f \<odot> (g \<otimes> (f\<^sup>t \<odot> h))) (i,j)"
      .
  qed
next
  fix f g :: "('a,'b) square"
  show "\<ominus>\<ominus>(f \<odot> g) = \<ominus>\<ominus>f \<odot> \<ominus>\<ominus>g"
  proof (rule ext, rule prod_cases)
    fix i j
    have "(\<ominus>\<ominus>(f \<odot> g)) (i,j) = --((f \<odot> g) (i,j))"
      by (simp add: uminus_matrix_def)
    also have "... = --(\<Squnion>\<^sub>k f (i,k) * g (k,j))"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>k --(f (i,k) * g (k,j)))"
      by (metis (no_types) pp_dist_sum)
    also have "... = (\<Squnion>\<^sub>k --(f (i,k)) * --(g (k,j)))"
      by (meson pp_dist_comp)
    also have "... = (\<Squnion>\<^sub>k (\<ominus>\<ominus>f) (i,k) * (\<ominus>\<ominus>g) (k,j))"
      by (simp add: uminus_matrix_def)
    also have "... = (\<ominus>\<ominus>f \<odot> \<ominus>\<ominus>g) (i,j)"
      by (simp add: times_matrix_def)
    finally show "(\<ominus>\<ominus>(f \<odot> g)) (i,j) = (\<ominus>\<ominus>f \<odot> \<ominus>\<ominus>g) (i,j)"
      .
  qed
next
  let ?o = "mone :: ('a,'b) square"
  show "\<ominus>\<ominus>?o = ?o"
  proof (rule ext, rule prod_cases)
    fix i j
    have "(\<ominus>\<ominus>?o) (i,j) = --(?o (i,j))"
      by (simp add: uminus_matrix_def)
    also have "... = --(if i = j then 1 else bot)"
      by (simp add: one_matrix_def)
    also have "... = (if i = j then --1 else --bot)"
      by simp
    also have "... = (if i = j then 1 else bot)"
      by auto
    also have "... = ?o (i,j)"
      by (simp add: one_matrix_def)
    finally show "(\<ominus>\<ominus>?o) (i,j) = ?o (i,j)"
      .
  qed
qed

end

