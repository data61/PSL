(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

theory Functional_Spaces
imports "HOL-Analysis.Analysis" Ergodic_Theory.SG_Library_Complement
begin



section \<open>Functions as a real vector space\<close>

text \<open>Many functional spaces are spaces of functions. To be able to use the following
framework, spaces of functions thus need to be endowed with a vector space
structure, coming from pointwise addition and multiplication.

Some instantiations for \verb+fun+ are already given in \verb+Lattices.thy+, we add several.\<close>

instantiation "fun" :: (type, plus) plus
begin

definition plus_fun_def: "f + g = (\<lambda>x. f x + g x)"

lemma plus_apply [simp, code]: "(f + g) x = f x + g x"
  by (simp add: plus_fun_def)

instance ..
end

text \<open>\verb+minus_fun+ is already defined, in \verb+Lattices.thy+, but under the strange name
\verb+fun_Compl_def+. We restate the definition so that \verb+unfolding minus_fun_def+ works.
Same thing for \verb+minus_fun_def+. A better solution would be to have a coherent naming scheme
in \verb+Lattices.thy+.\<close>

lemmas uminus_fun_def = fun_Compl_def
lemmas minus_fun_def = fun_diff_def

instantiation "fun" :: (type, zero) zero
begin

definition zero_fun_def: "0 = (\<lambda>x. 0)"

lemma zero_fun [simp, code]:
  "0 x = 0"
by (simp add: zero_fun_def)

instance..
end

instance "fun"::(type, semigroup_add) semigroup_add
by (standard, rule ext, auto simp add: add.assoc)

instance "fun"::(type, ab_semigroup_add) ab_semigroup_add
by (standard, rule ext, auto simp add: add_ac)

instance "fun"::(type, monoid_add) monoid_add
by (standard, rule ext, auto)

instance "fun"::(type, comm_monoid_add) comm_monoid_add
by (standard, rule ext, auto)

lemma fun_sum_apply:
  fixes u::"'i \<Rightarrow> 'a \<Rightarrow> ('b::comm_monoid_add)"
  shows "(sum u I) x = sum (\<lambda>i. u i x) I"
by (induction I rule: infinite_finite_induct, auto)

instance "fun"::(type, cancel_semigroup_add) cancel_semigroup_add
proof
  fix a b c::"'a \<Rightarrow> 'b" assume "a + b = a + c"
  then have "a x + b x = a x + c x" for x by (metis plus_fun_def)
  then show "b = c" by (intro ext, auto)
next
  fix b a c::"'a \<Rightarrow> 'b" assume "b + a = c + a"
  then have "b x + a x = c x + a x" for x by (metis plus_fun_def)
  then show "b = c" by (intro ext, auto)
qed

instance "fun"::(type, cancel_ab_semigroup_add) cancel_ab_semigroup_add
by (standard, rule ext, auto, rule ext, auto simp add: diff_diff_add)

instance "fun"::(type, cancel_comm_monoid_add) cancel_comm_monoid_add
by standard

instance "fun"::(type, group_add) group_add
by (standard, auto)

instance "fun"::(type, ab_group_add) ab_group_add
by (standard, auto)

instantiation "fun" :: (type, real_vector) real_vector
begin

definition scaleR_fun::"real \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "scaleR_fun = (\<lambda>c f. (\<lambda>x. c *\<^sub>R f x))"

lemma scaleR_apply [simp, code]: "(c *\<^sub>R f) x = c *\<^sub>R (f x)"
  by (simp add: scaleR_fun_def)

instance by (standard, auto simp add: scaleR_add_right scaleR_add_left)
end

lemmas divideR_apply = scaleR_apply

lemma [measurable]:
  "0 \<in> borel_measurable M"
unfolding zero_fun_def by auto

lemma borel_measurable_const_scaleR' [measurable (raw)]:
  "(f::('a \<Rightarrow> 'b::real_normed_vector)) \<in> borel_measurable M \<Longrightarrow> c *\<^sub>R f \<in> borel_measurable M"
unfolding scaleR_fun_def using borel_measurable_add by auto

lemma borel_measurable_add'[measurable (raw)]:
  fixes f g :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_vector}"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "f + g \<in> borel_measurable M"
unfolding plus_fun_def using assms by auto

lemma borel_measurable_uminus'[measurable (raw)]:
  fixes f g :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_vector}"
  assumes f: "f \<in> borel_measurable M"
  shows "-f \<in> borel_measurable M"
unfolding fun_Compl_def using assms by auto

lemma borel_measurable_diff'[measurable (raw)]:
  fixes f g :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_vector}"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "f - g \<in> borel_measurable M"
unfolding fun_diff_def using assms by auto

lemma borel_measurable_sum'[measurable (raw)]:
  fixes f::"'i \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology, real_normed_vector}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<Sum>i\<in>I. f i) \<in> borel_measurable M"
using borel_measurable_sum[of I f, OF assms] unfolding fun_sum_apply[symmetric] by simp

lemma zero_applied_to [simp]:
  "(0::('a \<Rightarrow> ('b::real_vector))) x = 0"
unfolding zero_fun_def by simp



section \<open>Quasinorms on function spaces\<close>

text \<open>A central feature of modern analysis is the use of various functional
spaces, and of results of functional analysis on them. Think for instance of
$L^p$ spaces, of Sobolev or Besov spaces, or variations around them. Here are
several relevant facts about this point of view:
\begin{itemize}
\item These spaces typically depend on one or several parameters.
This makes it difficult to play with type classes in a system without dependent
types.
\item The $L^p$ spaces are not spaces of functions (their elements are
equivalence classes of functions, where two functions are identified if they
coincide almost everywhere). However, in usual analysis proofs, one takes a
definite representative and works with it, never going to the equivalence class
point of view (which only becomes relevant when one wants to use the fact that
one has a Banach space at our disposal, to apply functional analytic tools).
\item It is important to describe how the spaces are related to each other,
with respect to inclusions or compact inclusions. For instance, one of the most
important theorems in analysis is Sobolev embedding theorem, describing when
one Sobolev space is included in another one. One also needs to be able to
take intersections or sums of Banach spaces, for instance to develop
interpolation theory.
\item Some other spaces play an important role in analysis, for instance the
weak $L^1$ space. This space only has a quasi-norm (i.e., its norm satisfies the
triangular inequality up to a fixed multiplicative constant). A general enough setting
should also encompass this kind of space. (One could argue that one should also consider more
general topologies such as Frechet spaces, to deal with Gevrey or analytic functions.
This is true, but considering quasi-norms already gives a wealth of applications).
\end{itemize}

Given these points, it seems that the most effective way of formalizing this
kind of question in Isabelle/HOL is to think of such a functional space not as
an abstract space or type, but as a subset of the space of all functions or of
all distributions. Functions that do not belong to the functional space
under consideration will then have infinite norm. Then inclusions, intersections,
and so on, become trivial to implement. Since the same object contains both the information
about the norm and the space where the norm is finite, it conforms to the customary habit in
mathematics of identifying the two of them, talking for instance about the $L^p$ space and the
$L^p$ norm.

All in all, this approach seems quite promising for ``real life analysis''.
\<close>

subsection \<open>Definition of quasinorms\<close>

typedef (overloaded) ('a::real_vector) quasinorm = "{(C::real, N::('a \<Rightarrow> ennreal)). (C \<ge> 1)
      \<and> (\<forall> x c. N (c *\<^sub>R x) = ennreal \<bar>c\<bar> * N(x)) \<and> (\<forall> x y. N(x+y) \<le> C * N x + C * N y)}"
morphisms Rep_quasinorm quasinorm_of
proof
  show "(1,(\<lambda>x. 0)) \<in> {(C::real, N::('a \<Rightarrow> ennreal)). (C \<ge> 1)
      \<and> (\<forall> x c. N (c *\<^sub>R x) = ennreal \<bar>c\<bar> * N x) \<and> (\<forall> x y. N (x+y) \<le> C * N x + C * N y)}"
    by auto
qed

definition eNorm::"'a quasinorm \<Rightarrow> ('a::real_vector) \<Rightarrow> ennreal"
  where "eNorm N x = (snd (Rep_quasinorm N)) x"

definition defect::"('a::real_vector) quasinorm \<Rightarrow> real"
  where "defect N = fst (Rep_quasinorm N)"

lemma eNorm_triangular_ineq:
  "eNorm N (x + y) \<le> defect N * eNorm N x + defect N * eNorm N y"
unfolding eNorm_def defect_def using Rep_quasinorm[of N] by auto

lemma defect_ge_1:
  "defect N \<ge> 1"
unfolding defect_def using Rep_quasinorm[of N] by auto

lemma eNorm_cmult:
  "eNorm N (c *\<^sub>R x) = ennreal \<bar>c\<bar> * eNorm N x"
unfolding eNorm_def using Rep_quasinorm[of N] by auto

lemma eNorm_zero [simp]:
  "eNorm N 0 = 0"
by (metis eNorm_cmult abs_zero ennreal_0 mult_zero_left real_vector.scale_zero_left)

lemma eNorm_uminus [simp]:
  "eNorm N (-x) = eNorm N x"
using eNorm_cmult[of N "-1" x] by auto

lemma eNorm_sum:
  "eNorm N (\<Sum>i\<in>{..<n}. u i) \<le> (\<Sum>i\<in>{..<n}. (defect N)^(Suc i) * eNorm N (u i))"
proof (cases "n=0")
  case True
  then show ?thesis by simp
next
  case False
  then obtain m where "n = Suc m" using not0_implies_Suc by blast
  have "\<And>v. eNorm N (\<Sum>i\<in>{..n}. v i) \<le> (\<Sum>i\<in>{..<n}. (defect N)^(Suc i) * eNorm N (v i)) + (defect N)^n * eNorm N (v n)" for n
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    have *: "(defect N)^(Suc n) = (defect N)^n * ennreal(defect N)"
      by (metis defect_ge_1 ennreal_le_iff ennreal_neg ennreal_power less_le not_less not_one_le_zero semiring_normalization_rules(28))
    fix v::"nat \<Rightarrow> 'a"
    define w where "w = (\<lambda>i. if i = n then v n + v (Suc n) else v i)"
    have "(\<Sum>i\<in>{..Suc n}. v i) = (\<Sum>i\<in>{..<n}. v i) + v n + v (Suc n)"
      using lessThan_Suc_atMost sum.lessThan_Suc by auto
    also have "... = (\<Sum>i\<in>{..<n}. w i) + w n" unfolding w_def by auto
    finally have "(\<Sum>i\<in>{..Suc n}. v i) = (\<Sum>i\<in>{..n}. w i)"
      by (metis lessThan_Suc_atMost sum.lessThan_Suc)
    then have "eNorm N (\<Sum>i\<in>{..Suc n}. v i) = eNorm N (\<Sum>i\<in>{..n}. w i)" by simp
    also have "... \<le> (\<Sum>i\<in>{..<n}. (defect N)^(Suc i) * eNorm N (w i)) + (defect N)^n * eNorm N (w n)"
      using Suc.IH by auto
    also have "... = (\<Sum>i\<in>{..<n}. (defect N)^(Suc i) * eNorm N (v i)) + (defect N)^n * eNorm N (v n + v (Suc n))"
      unfolding w_def by auto
    also have "... \<le> (\<Sum>i\<in>{..<n}. (defect N)^(Suc i) * eNorm N (v i)) +
          (defect N)^n * (defect N * eNorm N (v n) + defect N * eNorm N (v (Suc n)))"
      by (rule add_mono, simp, rule mult_left_mono, auto simp add: eNorm_triangular_ineq)
    also have "... = (\<Sum>i\<in>{..<n}. (defect N)^(Suc i) * eNorm N (v i))
        + (defect N)^(Suc n) * eNorm N (v n) + (defect N)^(Suc n) * eNorm N (v (Suc n))"
      unfolding * by (simp add: distrib_left semiring_normalization_rules(18))
    also have "... = (\<Sum>i\<in>{..<Suc n}. (defect N)^(Suc i) * eNorm N (v i)) + (defect N)^(Suc n) * eNorm N (v (Suc n))"
      by auto
    finally show "eNorm N (\<Sum>i\<in>{..Suc n}. v i)
            \<le> (\<Sum>i<Suc n. ennreal (defect N ^ Suc i) * eNorm N (v i)) + ennreal (defect N ^ Suc n) * eNorm N (v (Suc n)) "
      by simp
  qed
  then have "eNorm N (\<Sum>i\<in>{..<Suc m}. u i)
      \<le> (\<Sum>i\<in>{..<m}. (defect N)^(Suc i) * eNorm N (u i)) + (defect N)^m * eNorm N (u m)"
    using lessThan_Suc_atMost by auto
  also have "... \<le> (\<Sum>i\<in>{..<m}. (defect N)^(Suc i) * eNorm N (u i)) + (defect N)^(Suc m) * eNorm N (u m)"
    apply (rule add_mono, auto intro!: mult_right_mono ennreal_leI)
    using defect_ge_1 by (metis atMost_iff le_less lessThan_Suc_atMost lessThan_iff power_Suc power_increasing)
  also have "... = (\<Sum>i\<in>{..<Suc m}. (defect N)^(Suc i) * eNorm N (u i))"
    by auto
  finally show "eNorm N (\<Sum>i\<in>{..<n}. u i) \<le> (\<Sum>i<n. ennreal (defect N ^ Suc i) * eNorm N (u i))"
    unfolding \<open>n = Suc m\<close> by auto
qed


text \<open>Quasinorms are often defined by taking a meaningful formula on a vector subspace,
and then extending by infinity elsewhere. Let us show that this results in a quasinorm on the
whole space.\<close>

definition quasinorm_on::"('a set) \<Rightarrow> real \<Rightarrow> (('a::real_vector) \<Rightarrow> ennreal) \<Rightarrow> bool"
  where "quasinorm_on F C N = (
    (\<forall>x y. (x \<in> F \<and> y \<in> F) \<longrightarrow> (x + y \<in> F) \<and> N (x+y) \<le> C * N x + C * N y)
    \<and> (\<forall>c x. x \<in> F \<longrightarrow> c *\<^sub>R x \<in> F \<and> N(c *\<^sub>R x) = \<bar>c\<bar> * N x)
    \<and> C \<ge> 1 \<and> 0 \<in> F)"

lemma quasinorm_of:
  fixes N::"('a::real_vector) \<Rightarrow> ennreal" and C::real
  assumes "quasinorm_on UNIV C N"
  shows "eNorm (quasinorm_of (C,N)) x = N x"
        "defect (quasinorm_of (C,N)) = C"
using assms unfolding eNorm_def defect_def quasinorm_on_def by (auto simp add: quasinorm_of_inverse)

lemma quasinorm_onI:
  fixes N::"('a::real_vector) \<Rightarrow> ennreal" and C::real and F::"'a set"
  assumes "\<And>x y. x \<in> F \<Longrightarrow> y \<in> F \<Longrightarrow> x + y \<in> F"
          "\<And>x y. x \<in> F \<Longrightarrow> y \<in> F \<Longrightarrow> N (x + y) \<le> C * N x + C * N y"
          "\<And>c x. c \<noteq> 0 \<Longrightarrow> x \<in> F \<Longrightarrow> c *\<^sub>R x \<in> F"
          "\<And>c x. c \<noteq> 0 \<Longrightarrow> x \<in> F \<Longrightarrow> N (c *\<^sub>R x) \<le> ennreal \<bar>c\<bar> * N x"
          "0 \<in> F" "N(0) = 0" "C \<ge> 1"
  shows "quasinorm_on F C N"
proof -
  have "N(c *\<^sub>R x) = ennreal \<bar>c\<bar> * N x" if "x \<in> F" for c x
  proof (cases "c = 0")
    case True
    then show ?thesis using \<open>N 0 = 0\<close> by auto
  next
    case False
    have "N((1/c) *\<^sub>R (c *\<^sub>R x)) \<le> ennreal (abs (1/c)) * N (c *\<^sub>R x)"
      apply (rule \<open>\<And>c x. c \<noteq> 0 \<Longrightarrow> x \<in> F \<Longrightarrow> N(c *\<^sub>R x) \<le> ennreal \<bar>c\<bar> * N x\<close>) using False assms that by auto
    then have "N x \<le> ennreal (abs (1/c)) * N (c *\<^sub>R x)" using False by auto
    then have "ennreal \<bar>c\<bar> * N x \<le> ennreal \<bar>c\<bar> * ennreal (abs (1/c)) * N (c *\<^sub>R x)"
      by (simp add: mult.assoc mult_left_mono)
    also have "... = N (c *\<^sub>R x)" using ennreal_mult' abs_mult False
      by (metis abs_ge_zero abs_one comm_monoid_mult_class.mult_1 ennreal_1 eq_divide_eq_1 field_class.field_divide_inverse)
    finally show ?thesis
      using \<open>\<And>c x. c \<noteq> 0 \<Longrightarrow> x \<in> F \<Longrightarrow> N(c *\<^sub>R x) \<le> ennreal \<bar>c\<bar> * N x\<close>[OF False \<open>x \<in> F\<close>] by auto
  qed
  then show ?thesis
    unfolding quasinorm_on_def using assms by (auto, metis real_vector.scale_zero_left)
qed

lemma extend_quasinorm:
  assumes "quasinorm_on F C N"
  shows "quasinorm_on UNIV C (\<lambda>x. if x \<in> F then N x else \<infinity>)"
proof -
  have *: "(if x + y \<in> F then N (x + y) else \<infinity>)
    \<le> ennreal C * (if x \<in> F then N x else \<infinity>) + ennreal C * (if y \<in> F then N y else \<infinity>)" for x y
  proof (cases "x \<in> F \<and> y \<in> F")
    case True
    then show ?thesis using assms unfolding quasinorm_on_def by auto
  next
    case False
    moreover have "C \<ge> 1" using assms unfolding quasinorm_on_def by auto
    ultimately have *: "ennreal C * (if x \<in> F then N x else \<infinity>) + ennreal C * (if y \<in> F then N y else \<infinity>) = \<infinity>"
      using ennreal_mult_eq_top_iff by auto
    show ?thesis by (simp add: *)
  qed
  show ?thesis
    apply (rule quasinorm_onI)
    using assms * unfolding quasinorm_on_def apply (auto simp add: ennreal_top_mult mult.commute)
    by (metis abs_zero ennreal_0 mult_zero_right real_vector.scale_zero_right)
qed


subsection \<open>The space and the zero space of a quasinorm\<close>

text \<open>The space of a quasinorm is the vector subspace where it is meaningful, i.e., finite.\<close>

definition space\<^sub>N::"('a::real_vector) quasinorm \<Rightarrow> 'a set"
  where "space\<^sub>N N = {f. eNorm N f < \<infinity>}"

lemma spaceN_iff:
  "x \<in> space\<^sub>N N \<longleftrightarrow> eNorm N x < \<infinity>"
unfolding space\<^sub>N_def by simp

lemma spaceN_cmult [simp]:
  assumes "x \<in> space\<^sub>N N"
  shows "c *\<^sub>R x \<in> space\<^sub>N N"
using assms unfolding spaceN_iff using eNorm_cmult[of N c x] by (simp add: ennreal_mult_less_top)

lemma spaceN_add [simp]:
  assumes "x \<in> space\<^sub>N N" "y \<in> space\<^sub>N N"
  shows "x + y \<in> space\<^sub>N N"
proof -
  have "eNorm N x < \<infinity>" "eNorm N y < \<infinity>" using assms unfolding space\<^sub>N_def by auto
  then have "defect N * eNorm N x + defect N * eNorm N y < \<infinity>"
    by (simp add: ennreal_mult_less_top)
  then show ?thesis
    unfolding space\<^sub>N_def using eNorm_triangular_ineq[of N x y] le_less_trans by blast
qed

lemma spaceN_diff [simp]:
  assumes "x \<in> space\<^sub>N N" "y \<in> space\<^sub>N N"
  shows "x - y \<in> space\<^sub>N N"
using spaceN_add[OF assms(1) spaceN_cmult[OF assms(2), of "-1"]] by auto

lemma spaceN_contains_zero [simp]:
  "0 \<in> space\<^sub>N N"
unfolding space\<^sub>N_def by auto

lemma spaceN_sum [simp]:
  assumes "\<And>i. i \<in> I \<Longrightarrow> x i \<in> space\<^sub>N N"
  shows "(\<Sum>i\<in>I. x i) \<in> space\<^sub>N N"
using assms by (induction I rule: infinite_finite_induct, auto)


text \<open>The zero space of a quasinorm is the vector subspace of vectors with zero norm. If one wants
to get a true metric space, one should quotient the space by the zero space.\<close>

definition zero_space\<^sub>N::"('a::real_vector) quasinorm \<Rightarrow> 'a set"
  where "zero_space\<^sub>N N = {f. eNorm N f = 0}"

lemma zero_spaceN_iff:
  "x \<in> zero_space\<^sub>N N \<longleftrightarrow> eNorm N x = 0"
unfolding zero_space\<^sub>N_def by simp

lemma zero_spaceN_cmult:
  assumes "x \<in> zero_space\<^sub>N N"
  shows "c *\<^sub>R x \<in> zero_space\<^sub>N N"
using assms unfolding zero_spaceN_iff using eNorm_cmult[of N c x] by simp

lemma zero_spaceN_add:
  assumes "x \<in> zero_space\<^sub>N N" "y \<in> zero_space\<^sub>N N"
  shows "x + y \<in> zero_space\<^sub>N N"
proof -
  have "eNorm N x = 0" "eNorm N y = 0" using assms unfolding zero_space\<^sub>N_def by auto
  then have "defect N * eNorm N x + defect N * eNorm N y = 0" by auto
  then show ?thesis
    unfolding zero_spaceN_iff using eNorm_triangular_ineq[of N x y] by auto
qed

lemma zero_spaceN_diff:
  assumes "x \<in> zero_space\<^sub>N N" "y \<in> zero_space\<^sub>N N"
  shows "x - y \<in> zero_space\<^sub>N N"
using zero_spaceN_add[OF assms(1) zero_spaceN_cmult[OF assms(2), of "-1"]] by auto

lemma zero_spaceN_subset_spaceN:
  "zero_space\<^sub>N N \<subseteq> space\<^sub>N N"
by (simp add: spaceN_iff zero_spaceN_iff subset_eq)

text \<open>On the space, the norms are finite. Hence, it is much more convenient to work there with
a real valued version of the norm. We use Norm with a capital N to distinguish it from norms
in a (type class) banach space.\<close>

definition Norm::"'a quasinorm \<Rightarrow> ('a::real_vector) \<Rightarrow> real"
  where "Norm N x = enn2real (eNorm N x)"

lemma Norm_nonneg [simp]:
  "Norm N x \<ge> 0"
unfolding Norm_def by auto

lemma Norm_zero [simp]:
  "Norm N 0 = 0"
unfolding Norm_def by auto

lemma Norm_uminus [simp]:
  "Norm N (-x) = Norm N x"
unfolding Norm_def by auto

lemma eNorm_Norm:
  assumes "x \<in> space\<^sub>N N"
  shows "eNorm N x = ennreal (Norm N x)"
  using assms unfolding Norm_def by (simp add: spaceN_iff)

lemma eNorm_Norm':
  assumes "x \<notin> space\<^sub>N N"
  shows "Norm N x = 0"
using assms unfolding Norm_def apply (auto simp add: spaceN_iff)
using top.not_eq_extremum by fastforce

lemma Norm_cmult:
  "Norm N (c *\<^sub>R x) = abs c * Norm N x"
unfolding Norm_def unfolding eNorm_cmult by (simp add: enn2real_mult)

lemma Norm_triangular_ineq:
  assumes "x \<in> space\<^sub>N N"
  shows "Norm N (x + y) \<le> defect N * Norm N x + defect N * Norm N y"
proof (cases "y \<in> space\<^sub>N N")
  case True
  have *: "defect N * Norm N x + defect N * Norm N y \<ge> 1 * 0 + 1 * 0"
    apply (rule add_mono) by (rule mult_mono'[OF defect_ge_1 Norm_nonneg], simp, simp)+
  have "ennreal (Norm N (x + y)) = eNorm N (x+y)"
    using eNorm_Norm[OF spaceN_add[OF assms True]] by auto
  also have "... \<le> defect N * eNorm N x + defect N * eNorm N y"
    using eNorm_triangular_ineq[of N x y] by auto
  also have "... = defect N * ennreal(Norm N x) + defect N * ennreal(Norm N y)"
    using eNorm_Norm assms True by metis
  also have "... = ennreal(defect N * Norm N x + defect N * Norm N y)"
    using ennreal_mult ennreal_plus Norm_nonneg defect_ge_1
    by (metis (no_types, hide_lams) ennreal_eq_0_iff less_le ennreal_ge_1 ennreal_mult' le_less_linear not_one_le_zero semiring_normalization_rules(34))
  finally show ?thesis
    apply (subst ennreal_le_iff[symmetric]) using * by auto
next
  case False
  have "x + y \<notin> space\<^sub>N N"
  proof (rule ccontr)
    assume "\<not> (x + y \<notin> space\<^sub>N N)"
    then have "x + y \<in> space\<^sub>N N" by simp
    have "y \<in> space\<^sub>N N" using spaceN_diff[OF \<open>x + y \<in> space\<^sub>N N\<close> assms] by auto
    then show False using False by simp
  qed
  then have "Norm N (x+y) = 0" unfolding Norm_def using spaceN_iff top.not_eq_extremum by force
  moreover have "defect N * Norm N x + defect N * Norm N y \<ge> 1 * 0 + 1 * 0"
    apply (rule add_mono) by (rule mult_mono'[OF defect_ge_1 Norm_nonneg], simp, simp)+
  ultimately show ?thesis by simp
qed

lemma Norm_triangular_ineq_diff:
  assumes "x \<in> space\<^sub>N N"
  shows "Norm N (x - y) \<le> defect N * Norm N x + defect N * Norm N y"
using Norm_triangular_ineq[OF assms, of "-y"] by auto

lemma zero_spaceN_iff':
  "x \<in> zero_space\<^sub>N N \<longleftrightarrow> (x \<in> space\<^sub>N N \<and> Norm N x = 0)"
using eNorm_Norm unfolding space\<^sub>N_def zero_space\<^sub>N_def by (auto simp add: Norm_def, fastforce)

lemma Norm_sum:
  assumes "\<And>i. i < n \<Longrightarrow> u i \<in> space\<^sub>N N"
  shows "Norm N (\<Sum>i\<in>{..<n}. u i) \<le> (\<Sum>i\<in>{..<n}. (defect N)^(Suc i) * Norm N (u i))"
proof -
  have *: "0 \<le> defect N * defect N ^ i * Norm N (u i)" for i
    by (meson Norm_nonneg defect_ge_1 dual_order.trans linear mult_nonneg_nonneg not_one_le_zero zero_le_power)

  have "ennreal (Norm N (\<Sum>i\<in>{..<n}. u i)) = eNorm N (\<Sum>i\<in>{..<n}. u i)"
    apply (rule eNorm_Norm[symmetric], rule spaceN_sum) using assms by auto
  also have "... \<le> (\<Sum>i\<in>{..<n}. (defect N)^(Suc i) * eNorm N (u i))"
    using eNorm_sum by simp
  also have "... = (\<Sum>i\<in>{..<n}. (defect N)^(Suc i) * ennreal (Norm N (u i)))"
    using eNorm_Norm[OF assms] by auto
  also have "... = (\<Sum>i\<in>{..<n}. ennreal((defect N)^(Suc i) * Norm N (u i)))"
    by (subst ennreal_mult'', auto)
  also have "... = ennreal (\<Sum>i\<in>{..<n}. (defect N)^(Suc i) * Norm N (u i))"
    by (auto intro!: sum_ennreal simp add: *)
  finally have **: "ennreal (Norm N (\<Sum>i\<in>{..<n}. u i)) \<le> ennreal (\<Sum>i\<in>{..<n}. (defect N)^(Suc i) * Norm N (u i))"
    by simp
  show ?thesis
    apply (subst ennreal_le_iff[symmetric], rule sum_nonneg) using * ** by auto
qed

subsection \<open>An example: the ambient norm in a normed vector space\<close>

definition N_of_norm::"'a::real_normed_vector quasinorm"
  where "N_of_norm = quasinorm_of (1, \<lambda>f. norm f)"

lemma N_of_norm:
  "eNorm N_of_norm f = ennreal (norm f)"
  "Norm N_of_norm f = norm f"
  "defect (N_of_norm) = 1"
proof -
  have *: "quasinorm_on UNIV 1 (\<lambda>f. norm f)"
    by (rule quasinorm_onI, auto simp add: ennreal_mult', metis ennreal_leI ennreal_plus norm_imp_pos_and_ge norm_triangle_ineq)
  show "eNorm N_of_norm f = ennreal (norm f)"
       "defect (N_of_norm) = 1"
    unfolding N_of_norm_def using quasinorm_of[OF *] by auto
  then show "Norm N_of_norm f = norm f" unfolding Norm_def by auto
qed

lemma N_of_norm_space [simp]:
  "space\<^sub>N N_of_norm = UNIV"
unfolding space\<^sub>N_def apply auto unfolding N_of_norm(1) by auto

lemma N_of_norm_zero_space [simp]:
  "zero_space\<^sub>N N_of_norm = {0}"
unfolding zero_space\<^sub>N_def apply auto unfolding N_of_norm(1) by auto


subsection \<open>An example: the space of bounded continuous functions from a topological space to a normed
real vector space\<close>

text \<open>The Banach space of bounded continuous functions is defined in
\verb+Bounded_Continuous_Function.thy+, as a type \verb+bcontfun+. We import very quickly the
results proved in this file to the current framework.\<close>

definition bcontfun\<^sub>N::"('a::topological_space \<Rightarrow> 'b::real_normed_vector) quasinorm"
  where "bcontfun\<^sub>N = quasinorm_of (1, \<lambda>f. if f \<in> bcontfun then norm(Bcontfun f) else (\<infinity>::ennreal))"

lemma bcontfun\<^sub>N:
  fixes f::"('a::topological_space \<Rightarrow> 'b::real_normed_vector)"
  shows "eNorm bcontfun\<^sub>N f = (if f \<in> bcontfun then norm(Bcontfun f) else (\<infinity>::ennreal))"
        "Norm bcontfun\<^sub>N f = (if f \<in> bcontfun then norm(Bcontfun f) else 0)"
        "defect (bcontfun\<^sub>N::(('a \<Rightarrow> 'b) quasinorm)) = 1"
proof -
  have *: "quasinorm_on bcontfun 1 (\<lambda>(f::('a \<Rightarrow> 'b)). norm(Bcontfun f))"
  proof (rule quasinorm_onI, auto)
    fix f g::"'a \<Rightarrow> 'b" assume H: "f \<in> bcontfun" "g \<in> bcontfun"
    then show "f + g \<in> bcontfun" unfolding plus_fun_def by (simp add: plus_cont)
    have *: "Bcontfun(f + g) = Bcontfun f + Bcontfun g"
      using H
      by (auto simp: eq_onp_def plus_fun_def bcontfun_def intro!: plus_bcontfun.abs_eq[symmetric])
    show "ennreal (norm (Bcontfun (f + g))) \<le> ennreal (norm (Bcontfun f)) + ennreal (norm (Bcontfun g))"
      unfolding * using ennreal_leI[OF norm_triangle_ineq] by auto
  next
    fix c::real and f::"'a \<Rightarrow> 'b" assume H: "f \<in> bcontfun"
    then show "c *\<^sub>R f \<in> bcontfun" unfolding scaleR_fun_def by (simp add: scaleR_cont)
    have *: "Bcontfun(c *\<^sub>R f) = c *\<^sub>R Bcontfun f"
      using H
      by (auto simp: eq_onp_def scaleR_fun_def bcontfun_def intro!: scaleR_bcontfun.abs_eq[symmetric])
    show "ennreal (norm (Bcontfun (c *\<^sub>R f))) \<le> ennreal \<bar>c\<bar> * ennreal (norm (Bcontfun f))"
      unfolding * by (simp add: ennreal_mult'')
  next
    show "(0::'a\<Rightarrow>'b) \<in> bcontfun" "Bcontfun 0 = 0"
      unfolding zero_fun_def zero_bcontfun_def by (auto simp add: const_bcontfun)
  qed
  have **: "quasinorm_on UNIV 1 (\<lambda>(f::'a\<Rightarrow>'b). if f \<in> bcontfun then norm(Bcontfun f) else (\<infinity>::ennreal))"
    by (rule extend_quasinorm[OF *])
  show "eNorm bcontfun\<^sub>N f = (if f \<in> bcontfun then norm(Bcontfun f) else (\<infinity>::ennreal))"
       "defect (bcontfun\<^sub>N::('a \<Rightarrow> 'b) quasinorm) = 1"
    using quasinorm_of[OF **] unfolding bcontfun\<^sub>N_def by auto
  then show "Norm bcontfun\<^sub>N f = (if f \<in> bcontfun then norm(Bcontfun f) else 0)"
    unfolding Norm_def by auto
qed

lemma bcontfun\<^sub>N_space:
  "space\<^sub>N bcontfun\<^sub>N = bcontfun"
using bcontfun\<^sub>N(1) by (metis (no_types, lifting) Collect_cong bcontfun_def enn2real_top ennreal_0
  ennreal_enn2real ennreal_less_top ennreal_zero_neq_top infinity_ennreal_def mem_Collect_eq space\<^sub>N_def)

lemma bcontfun\<^sub>N_zero_space:
  "zero_space\<^sub>N bcontfun\<^sub>N = {0}"
  apply (auto simp add: zero_spaceN_iff)
  by (metis Bcontfun_inject bcontfun\<^sub>N(1) eNorm_zero ennreal_eq_zero_iff ennreal_zero_neq_top infinity_ennreal_def norm_eq_zero norm_imp_pos_and_ge)

lemma bcontfun\<^sub>ND:
  assumes "f \<in> space\<^sub>N bcontfun\<^sub>N"
  shows "continuous_on UNIV f"
        "\<And>x. norm(f x) \<le> Norm bcontfun\<^sub>N f"
proof-
  have "f \<in> bcontfun" using assms unfolding bcontfun\<^sub>N_space by simp
  then show "continuous_on UNIV f" unfolding bcontfun_def by auto
  show "\<And>x. norm(f x) \<le> Norm bcontfun\<^sub>N f"
    using norm_bounded bcontfun\<^sub>N(2) \<open>f \<in> bcontfun\<close> by (metis Bcontfun_inverse)
qed

lemma bcontfun\<^sub>NI:
  assumes "continuous_on UNIV f"
          "\<And>x. norm(f x) \<le> C"
  shows "f \<in> space\<^sub>N bcontfun\<^sub>N"
        "Norm bcontfun\<^sub>N f \<le> C"
proof -
  have "f \<in> bcontfun" using assms bcontfun_normI by blast
  then show "f \<in> space\<^sub>N bcontfun\<^sub>N" unfolding bcontfun\<^sub>N_space by simp
  show "Norm bcontfun\<^sub>N f \<le> C" unfolding bcontfun\<^sub>N(2) using \<open>f \<in> bcontfun\<close> apply auto
    using assms(2) by (metis apply_bcontfun_cases apply_bcontfun_inverse norm_bound)
qed


subsection \<open>Continuous inclusions between functional spaces\<close>

text \<open>Continuous inclusions between functional spaces are now defined\<close>

instantiation quasinorm:: (real_vector) preorder
begin

definition less_eq_quasinorm::"'a quasinorm \<Rightarrow> 'a quasinorm \<Rightarrow> bool"
  where "less_eq_quasinorm N1 N2 = (\<exists>C\<ge>(0::real). \<forall>f. eNorm N2 f \<le> C * eNorm N1 f)"

definition less_quasinorm::"'a quasinorm \<Rightarrow> 'a quasinorm \<Rightarrow> bool"
  where "less_quasinorm N1 N2 = (less_eq N1 N2 \<and> (\<not> less_eq N2 N1))"

instance proof -
  have E: "N \<le> N" for N::"'a quasinorm"
    unfolding less_eq_quasinorm_def by (rule exI[of _ 1], auto)
  have T: "N1 \<le> N3" if "N1 \<le> N2" "N2 \<le> N3" for N1 N2 N3::"'a quasinorm"
  proof -
    obtain C C' where *: "\<And>f. eNorm N2 f \<le> ennreal C * eNorm N1 f"
                         "\<And>f. eNorm N3 f \<le> ennreal C' * eNorm N2 f"
                         "C \<ge> 0" "C' \<ge> 0"
      using \<open>N1 \<le> N2\<close> \<open>N2 \<le> N3\<close> unfolding less_eq_quasinorm_def by metis
    {
      fix f
      have "eNorm N3 f \<le> ennreal C' * ennreal C * eNorm N1 f"
        by (metis *(1)[of f] *(2)[of f] mult.commute mult.left_commute mult_left_mono order_trans zero_le)
      also have "... = ennreal(C' * C) * eNorm N1 f"
        using \<open>C \<ge> 0\<close> \<open>C' \<ge> 0\<close> ennreal_mult by auto
      finally have "eNorm N3 f \<le> ennreal(C' * C) * eNorm N1 f" by simp
    }
    then show ?thesis
      unfolding less_eq_quasinorm_def using \<open>C \<ge> 0\<close> \<open>C' \<ge> 0\<close> zero_le_mult_iff by auto
  qed

  show "OFCLASS('a quasinorm, preorder_class)"
    apply standard
    unfolding less_quasinorm_def apply simp
    using E apply fast
    using T apply fast
    done
qed
end

abbreviation quasinorm_subset :: "('a::real_vector) quasinorm \<Rightarrow> 'a quasinorm \<Rightarrow> bool"
  where "quasinorm_subset \<equiv> less"

abbreviation quasinorm_subset_eq :: "('a::real_vector) quasinorm \<Rightarrow> 'a quasinorm \<Rightarrow> bool"
  where "quasinorm_subset_eq \<equiv> less_eq"

notation
  quasinorm_subset ("'(\<subset>\<^sub>N')") and
  quasinorm_subset ("(_/ \<subset>\<^sub>N _)" [51, 51] 50) and
  quasinorm_subset_eq ("'(\<subseteq>\<^sub>N')") and
  quasinorm_subset_eq ("(_/ \<subseteq>\<^sub>N _)" [51, 51] 50)


lemma quasinorm_subsetD:
  assumes "N1 \<subseteq>\<^sub>N N2"
  shows "\<exists>C\<ge>(0::real). \<forall>f. eNorm N2 f \<le> C * eNorm N1 f"
using assms unfolding less_eq_quasinorm_def by auto

lemma quasinorm_subsetI:
  assumes "\<And>f. f \<in> space\<^sub>N N1 \<Longrightarrow> eNorm N2 f \<le> ennreal C * eNorm N1 f"
  shows "N1 \<subseteq>\<^sub>N N2"
proof -
  have "eNorm N2 f \<le> ennreal (max C 1) * eNorm N1 f" for f
  proof (cases "f \<in> space\<^sub>N N1")
    case True
    then show ?thesis using assms[OF \<open>f \<in> space\<^sub>N N1\<close>]
      by (metis (no_types, hide_lams) dual_order.trans ennreal_leI max.cobounded2 max.commute
      mult.commute ordered_comm_semiring_class.comm_mult_left_mono zero_le)
  next
    case False
    then show ?thesis using spaceN_iff
      by (metis ennreal_ge_1 ennreal_mult_less_top infinity_ennreal_def max.cobounded1
      max.commute not_le not_one_le_zero top.not_eq_extremum)
  qed
  then show ?thesis unfolding less_eq_quasinorm_def
    by (metis ennreal_max_0' max.cobounded2)
qed

lemma quasinorm_subsetI':
  assumes "\<And>f. f \<in> space\<^sub>N N1 \<Longrightarrow> f \<in> space\<^sub>N N2"
          "\<And>f. f \<in> space\<^sub>N N1 \<Longrightarrow> Norm N2 f \<le> C * Norm N1 f"
  shows "N1 \<subseteq>\<^sub>N N2"
proof (rule quasinorm_subsetI)
  fix f assume "f \<in> space\<^sub>N N1"
  then have "f \<in> space\<^sub>N N2" using assms(1) by simp
  then have "eNorm N2 f = ennreal(Norm N2 f)" using eNorm_Norm by auto
  also have "... \<le> ennreal(C * Norm N1 f)"
    using assms(2)[OF \<open>f \<in> space\<^sub>N N1\<close>] ennreal_leI by blast
  also have "... = ennreal C * ennreal(Norm N1 f)"
    using ennreal_mult'' by auto
  also have "... = ennreal C * eNorm N1 f"
    using eNorm_Norm[OF \<open>f \<in> space\<^sub>N N1\<close>] by auto
  finally show "eNorm N2 f \<le> ennreal C * eNorm N1 f"
    by simp
qed

lemma quasinorm_subset_space:
  assumes "N1 \<subseteq>\<^sub>N N2"
  shows "space\<^sub>N N1 \<subseteq> space\<^sub>N N2"
using assms unfolding space\<^sub>N_def less_eq_quasinorm_def
by (auto, metis ennreal_mult_eq_top_iff ennreal_neq_top less_le top.extremum_strict top.not_eq_extremum)

lemma quasinorm_subset_Norm_eNorm:
  assumes "f \<in> space\<^sub>N N1 \<Longrightarrow> Norm N2 f \<le> C * Norm N1 f"
          "N1 \<subseteq>\<^sub>N N2"
          "C > 0"
  shows "eNorm N2 f \<le> ennreal C * eNorm N1 f"
proof (cases "f \<in> space\<^sub>N N1")
  case True
  then have "f \<in> space\<^sub>N N2" using quasinorm_subset_space[OF \<open>N1 \<subseteq>\<^sub>N N2\<close>] by auto
  then show ?thesis
    using eNorm_Norm[OF True] eNorm_Norm assms(1)[OF True] by (metis Norm_nonneg ennreal_leI ennreal_mult'')
next
  case False
  then show ?thesis using \<open>C > 0\<close>
    by (metis ennreal_eq_zero_iff ennreal_mult_eq_top_iff infinity_ennreal_def less_imp_le neq_top_trans not_le spaceN_iff)
qed

lemma quasinorm_subset_zero_space:
  assumes "N1 \<subseteq>\<^sub>N N2"
  shows "zero_space\<^sub>N N1 \<subseteq> zero_space\<^sub>N N2"
using assms unfolding zero_space\<^sub>N_def less_eq_quasinorm_def
by (auto, metis le_zero_eq mult_zero_right)

text \<open>We would like to define the equivalence relation associated to the above order, i.e., the
equivalence between norms. This is not equality, so we do not have a true order, but nevertheless
this is handy, and not standard in a preorder in Isabelle. The file Library/Preorder.thy defines
such an equivalence relation, but including it breaks some proofs so we go the naive way.\<close>

definition quasinorm_equivalent::"('a::real_vector) quasinorm \<Rightarrow> 'a quasinorm \<Rightarrow> bool" (infix "=\<^sub>N" 60)
  where "quasinorm_equivalent N1 N2 = ((N1 \<subseteq>\<^sub>N N2) \<and> (N2 \<subseteq>\<^sub>N N1))"

lemma quasinorm_equivalent_sym [sym]:
  assumes "N1 =\<^sub>N N2"
  shows "N2 =\<^sub>N N1"
using assms unfolding quasinorm_equivalent_def by auto

lemma quasinorm_equivalent_trans [trans]:
  assumes "N1 =\<^sub>N N2" "N2 =\<^sub>N N3"
  shows "N1 =\<^sub>N N3"
using assms order_trans unfolding quasinorm_equivalent_def by blast

subsection \<open>The intersection and the sum of two functional spaces\<close>

text \<open>In this paragraph, we define the intersection and the sum of two functional spaces.
In terms of the order introduced above, this corresponds to the minimum and the maximum.
More important, these are the first two examples of interpolation spaces between two
functional spaces, and they are central as all the other ones are built using them.\<close>

definition quasinorm_intersection::"('a::real_vector) quasinorm \<Rightarrow> 'a quasinorm \<Rightarrow> 'a quasinorm" (infix "\<inter>\<^sub>N" 70)
  where "quasinorm_intersection N1 N2 = quasinorm_of (max (defect N1) (defect N2), \<lambda>f. eNorm N1 f + eNorm N2 f)"

lemma quasinorm_intersection:
  "eNorm (N1 \<inter>\<^sub>N N2) f = eNorm N1 f + eNorm N2 f"
  "defect (N1 \<inter>\<^sub>N N2) = max (defect N1) (defect N2)"
proof -
  have T: "eNorm N1 (x + y) + eNorm N2 (x + y) \<le>
    ennreal (max (defect N1) (defect N2)) * (eNorm N1 x + eNorm N2 x) + ennreal (max (defect N1) (defect N2)) * (eNorm N1 y + eNorm N2 y)" for x y
  proof -
    have "eNorm N1 (x + y) \<le> ennreal (max (defect N1) (defect N2)) * eNorm N1 x + ennreal (max (defect N1) (defect N2)) * eNorm N1 y"
      using eNorm_triangular_ineq[of N1 x y] by (metis (no_types) max_def distrib_left ennreal_leI mult_right_mono order_trans zero_le)
    moreover have "eNorm N2 (x + y) \<le> ennreal (max (defect N1) (defect N2)) * eNorm N2 x + ennreal (max (defect N1) (defect N2)) * eNorm N2 y"
      using eNorm_triangular_ineq[of N2 x y] by (metis (no_types) max_def max.commute distrib_left ennreal_leI mult_right_mono order_trans zero_le)
    ultimately have "eNorm N1 (x + y) + eNorm N2 (x + y) \<le> ennreal (max (defect N1) (defect N2)) * (eNorm N1 x + eNorm N1 y + (eNorm N2 x + eNorm N2 y))"
      by (simp add: add_mono_thms_linordered_semiring(1) distrib_left)
    then show ?thesis
      by (simp add: ab_semigroup_add_class.add_ac(1) add.left_commute distrib_left)
  qed

  have H: "eNorm N1 (c *\<^sub>R x) + eNorm N2 (c *\<^sub>R x) \<le> ennreal \<bar>c\<bar> * (eNorm N1 x + eNorm N2 x)" for c x
    by (simp add: eNorm_cmult[of N1 c x] eNorm_cmult[of N2 c x] distrib_left)
  have *: "quasinorm_on UNIV (max (defect N1) (defect N2)) (\<lambda>f. eNorm N1 f + eNorm N2 f)"
    apply (rule quasinorm_onI) using T H defect_ge_1[of N1] defect_ge_1[of N2] by auto
  show "defect (N1 \<inter>\<^sub>N N2) = max (defect N1) (defect N2)"
       "eNorm (N1 \<inter>\<^sub>N N2) f = eNorm N1 f + eNorm N2 f"
    unfolding quasinorm_intersection_def using quasinorm_of[OF *] by auto
qed

lemma quasinorm_intersection_commute:
  "N1 \<inter>\<^sub>N N2 = N2 \<inter>\<^sub>N N1"
unfolding quasinorm_intersection_def max.commute[of "defect N1"] add.commute[of "eNorm N1 _"] by simp

lemma quasinorm_intersection_space:
  "space\<^sub>N (N1 \<inter>\<^sub>N N2) = space\<^sub>N N1 \<inter> space\<^sub>N N2"
apply auto unfolding quasinorm_intersection(1) spaceN_iff by auto

lemma quasinorm_intersection_zero_space:
  "zero_space\<^sub>N (N1 \<inter>\<^sub>N N2) = zero_space\<^sub>N N1 \<inter> zero_space\<^sub>N N2"
apply auto unfolding quasinorm_intersection(1) zero_spaceN_iff by (auto simp add: add_eq_0_iff_both_eq_0)

lemma quasinorm_intersection_subset:
  "N1 \<inter>\<^sub>N N2 \<subseteq>\<^sub>N N1" "N1 \<inter>\<^sub>N N2 \<subseteq>\<^sub>N N2"
by (rule quasinorm_subsetI[of _ _ 1], auto simp add: quasinorm_intersection(1))+

lemma quasinorm_intersection_minimum:
  assumes "N \<subseteq>\<^sub>N N1" "N \<subseteq>\<^sub>N N2"
  shows "N \<subseteq>\<^sub>N N1 \<inter>\<^sub>N N2"
proof -
  obtain C1 C2::real where *: "\<And>f. eNorm N1 f \<le> C1 * eNorm N f"
                              "\<And>f. eNorm N2 f \<le> C2 * eNorm N f"
                              "C1 \<ge> 0" "C2 \<ge> 0"
    using quasinorm_subsetD[OF assms(1)] quasinorm_subsetD[OF assms(2)] by blast
  have **: "eNorm (N1 \<inter>\<^sub>N N2) f \<le> (C1 + C2) * eNorm N f" for f
    unfolding quasinorm_intersection(1) using add_mono[OF *(1) *(2)] by (simp add: distrib_right *)
  show ?thesis
    apply (rule quasinorm_subsetI) using ** by auto
qed

lemma quasinorm_intersection_assoc:
  "(N1 \<inter>\<^sub>N N2) \<inter>\<^sub>N N3 =\<^sub>N N1 \<inter>\<^sub>N (N2 \<inter>\<^sub>N N3)"
unfolding quasinorm_equivalent_def by (meson order_trans quasinorm_intersection_minimum quasinorm_intersection_subset)



definition quasinorm_sum::"('a::real_vector) quasinorm \<Rightarrow> 'a quasinorm \<Rightarrow> 'a quasinorm" (infix "+\<^sub>N" 70)
  where "quasinorm_sum N1 N2 = quasinorm_of (max (defect N1) (defect N2), \<lambda>f. Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2})"

lemma quasinorm_sum:
  "eNorm (N1 +\<^sub>N N2) f = Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}"
  "defect (N1 +\<^sub>N N2) = max (defect N1) (defect N2)"
proof -
  define N where "N = (\<lambda>f. Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2})"
  have T: "N (f+g) \<le>
    ennreal (max (defect N1) (defect N2)) * N f + ennreal (max (defect N1) (defect N2)) * N g" for f g
  proof -
    have "\<exists>u. (\<forall>n. u n \<in> {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}) \<and> u \<longlonglongrightarrow> Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}"
      by (rule Inf_as_limit, auto, rule exI[of _ "f"], rule exI[of _ 0], auto)
    then obtain uf where uf: "\<And>n. uf n \<in> {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}"
                             "uf \<longlonglongrightarrow> Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}"
      by blast
    have "\<exists>f1 f2. \<forall>n. uf n = eNorm N1 (f1 n) + eNorm N2 (f2 n) \<and> f = f1 n + f2 n"
      apply (rule SMT.choices(1)) using uf(1) by blast
    then obtain f1 f2 where F: "\<And>n. uf n = eNorm N1 (f1 n) + eNorm N2 (f2 n)" "\<And>n. f = f1 n + f2 n"
      by blast

    have "\<exists>u. (\<forall>n. u n \<in> {eNorm N1 g1 + eNorm N2 g2| g1 g2. g = g1 + g2}) \<and> u \<longlonglongrightarrow> Inf {eNorm N1 g1 + eNorm N2 g2| g1 g2. g = g1 + g2}"
      by (rule Inf_as_limit, auto, rule exI[of _ "g"], rule exI[of _ 0], auto)
    then obtain ug where ug: "\<And>n. ug n \<in> {eNorm N1 g1 + eNorm N2 g2| g1 g2. g = g1 + g2}"
                             "ug \<longlonglongrightarrow> Inf {eNorm N1 g1 + eNorm N2 g2| g1 g2. g = g1 + g2}"
      by blast
    have "\<exists>g1 g2. \<forall>n. ug n = eNorm N1 (g1 n) + eNorm N2 (g2 n) \<and> g = g1 n + g2 n"
      apply (rule SMT.choices(1)) using ug(1) by blast
    then obtain g1 g2 where G: "\<And>n. ug n = eNorm N1 (g1 n) + eNorm N2 (g2 n)" "\<And>n. g = g1 n + g2 n"
      by blast

    define h1 where "h1 = (\<lambda>n. f1 n + g1 n)"
    define h2 where "h2 = (\<lambda>n. f2 n + g2 n)"
    have *: "f + g = h1 n + h2 n" for n
      unfolding h1_def h2_def using F(2) G(2) by (auto simp add: algebra_simps)
    have "N (f+g) \<le> ennreal (max (defect N1) (defect N2)) * (uf n + ug n)" for n
    proof -
      have "N (f+g) \<le> eNorm N1 (h1 n) + eNorm N2 (h2 n)"
        unfolding N_def apply (rule Inf_lower, auto, rule exI[of _ "h1 n"], rule exI[of _ "h2 n"])
        using * by auto
      also have "... \<le> ennreal (defect N1) * eNorm N1 (f1 n) + ennreal (defect N1) * eNorm N1 (g1 n)
                      + (ennreal (defect N2) * eNorm N2 (f2 n) + ennreal (defect N2) * eNorm N2 (g2 n))"
        unfolding h1_def h2_def apply (rule add_mono) using eNorm_triangular_ineq by auto
      also have "... \<le> (ennreal (max (defect N1) (defect N2)) * eNorm N1 (f1 n) + ennreal (max (defect N1) (defect N2)) * eNorm N1 (g1 n))
                      + (ennreal (max (defect N1) (defect N2)) * eNorm N2 (f2 n) + ennreal (max (defect N1) (defect N2)) * eNorm N2 (g2 n))"
        by (auto intro!: add_mono mult_mono ennreal_leI)
      also have "... = ennreal (max (defect N1) (defect N2)) * (uf n + ug n)"
        unfolding F(1) G(1) by (auto simp add: algebra_simps)
      finally show ?thesis by simp
    qed
    moreover have "... \<longlonglongrightarrow> ennreal (max (defect N1) (defect N2)) * (N f + N g)"
      unfolding N_def by (auto intro!: tendsto_intros simp add: uf(2) ug(2))
    ultimately have "N (f+g) \<le> ennreal (max (defect N1) (defect N2)) * (N f + N g)"
      using LIMSEQ_le_const by blast
    then show ?thesis by (auto simp add: algebra_simps)
  qed

  have H: "N (c *\<^sub>R f) \<le> ennreal \<bar>c\<bar> * N f" for c f
  proof -
    have "\<exists>u. (\<forall>n. u n \<in> {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}) \<and> u \<longlonglongrightarrow> Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}"
      by (rule Inf_as_limit, auto, rule exI[of _ "f"], rule exI[of _ 0], auto)
    then obtain uf where uf: "\<And>n. uf n \<in> {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}"
                             "uf \<longlonglongrightarrow> Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}"
      by blast
    have "\<exists>f1 f2. \<forall>n. uf n = eNorm N1 (f1 n) + eNorm N2 (f2 n) \<and> f = f1 n + f2 n"
      apply (rule SMT.choices(1)) using uf(1) by blast
    then obtain f1 f2 where F: "\<And>n. uf n = eNorm N1 (f1 n) + eNorm N2 (f2 n)" "\<And>n. f = f1 n + f2 n"
      by blast

    have "N (c *\<^sub>R f) \<le> \<bar>c\<bar> * uf n" for n
    proof -
      have "N (c *\<^sub>R f) \<le> eNorm N1 (c *\<^sub>R f1 n) + eNorm N2 (c *\<^sub>R f2 n)"
        unfolding N_def apply (rule Inf_lower, auto, rule exI[of _ "c *\<^sub>R f1 n"], rule exI[of _ "c *\<^sub>R f2 n"])
        using F(2)[of n] scaleR_add_right by auto
      also have "... = \<bar>c\<bar> * (eNorm N1 (f1 n) + eNorm N2 (f2 n))"
        by (auto simp add: algebra_simps eNorm_cmult)
      finally show ?thesis using F(1) by simp
    qed
    moreover have "... \<longlonglongrightarrow> \<bar>c\<bar> * N f"
      unfolding N_def by (auto intro!: tendsto_intros simp add: uf(2))
    ultimately show ?thesis
      using LIMSEQ_le_const by blast
  qed

  have "Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. 0 = f1 + f2} \<le> 0"
    by (rule Inf_lower, auto, rule exI[of _ 0], auto)
  then have Z: "Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. 0 = f1 + f2} = 0"
    by auto

  have *: "quasinorm_on UNIV (max (defect N1) (defect N2)) (\<lambda>f. Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2})"
    apply (rule quasinorm_onI) using T H Z defect_ge_1[of N1] defect_ge_1[of N2] unfolding N_def by auto
  show "defect (N1 +\<^sub>N N2) = max (defect N1) (defect N2)"
       "eNorm (N1 +\<^sub>N N2) f = Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}"
    unfolding quasinorm_sum_def using quasinorm_of[OF *] by auto
qed

lemma quasinorm_sum_limit:
  "\<exists>f1 f2. (\<forall>n. f = f1 n + f2 n) \<and> (\<lambda>n. eNorm N1 (f1 n) + eNorm N2 (f2 n)) \<longlonglongrightarrow> eNorm (N1 +\<^sub>N N2) f"
proof -
  have "\<exists>u. (\<forall>n. u n \<in> {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}) \<and> u \<longlonglongrightarrow> Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}"
    by (rule Inf_as_limit, auto, rule exI[of _ "f"], rule exI[of _ 0], auto)
  then obtain uf where uf: "\<And>n. uf n \<in> {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}"
                           "uf \<longlonglongrightarrow> Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. f = f1 + f2}"
    by blast
  have "\<exists>f1 f2. \<forall>n. uf n = eNorm N1 (f1 n) + eNorm N2 (f2 n) \<and> f = f1 n + f2 n"
    apply (rule SMT.choices(1)) using uf(1) by blast
  then obtain f1 f2 where F: "\<And>n. uf n = eNorm N1 (f1 n) + eNorm N2 (f2 n)" "\<And>n. f = f1 n + f2 n"
    by blast
  have "(\<lambda>n. eNorm N1 (f1 n) + eNorm N2 (f2 n)) \<longlonglongrightarrow> eNorm (N1 +\<^sub>N N2) f"
    using F(1) uf(2) unfolding quasinorm_sum(1) by presburger
  then show ?thesis using F(2) by auto
qed

lemma quasinorm_sum_space:
  "space\<^sub>N (N1 +\<^sub>N N2) = {f + g|f g. f \<in> space\<^sub>N N1 \<and> g \<in> space\<^sub>N N2}"
proof (auto)
  fix x assume "x \<in> space\<^sub>N (N1 +\<^sub>N N2)"
  then have "Inf {eNorm N1 f + eNorm N2 g| f g. x = f + g} < \<infinity>"
    unfolding quasinorm_sum(1) spaceN_iff.
  then have "\<exists>z \<in> {eNorm N1 f + eNorm N2 g| f g. x = f + g}. z < \<infinity>"
    by (simp add: Inf_less_iff)
  then show "\<exists>f g. x = f + g \<and> f \<in> space\<^sub>N N1 \<and> g \<in> space\<^sub>N N2"
    using spaceN_iff by force
next
  fix f g assume H: "f \<in> space\<^sub>N N1" "g \<in> space\<^sub>N N2"
  have "Inf {eNorm N1 u + eNorm N2 v| u v. f + g = u + v} \<le> eNorm N1 f + eNorm N2 g"
    by (rule Inf_lower, auto)
  also have "... < \<infinity>" using spaceN_iff H by auto
  finally show "f + g \<in> space\<^sub>N (N1 +\<^sub>N N2)"
    unfolding spaceN_iff quasinorm_sum(1).
qed

lemma quasinorm_sum_zerospace:
  "{f + g |f g. f \<in> zero_space\<^sub>N N1 \<and> g \<in> zero_space\<^sub>N N2} \<subseteq> zero_space\<^sub>N (N1 +\<^sub>N N2)"
proof (auto, unfold zero_spaceN_iff)
  fix f g assume H: "eNorm N1 f = 0" "eNorm N2 g = 0"
  have "Inf {eNorm N1 f1 + eNorm N2 f2| f1 f2. f + g = f1 + f2} \<le> 0"
    by (rule Inf_lower, auto, rule exI[of _ f], auto simp add: H)
  then show "eNorm (N1 +\<^sub>N N2) (f + g) = 0" unfolding quasinorm_sum(1) by auto
qed

lemma quasinorm_sum_subset:
  "N1 \<subseteq>\<^sub>N N1 +\<^sub>N N2" "N2 \<subseteq>\<^sub>N N1 +\<^sub>N N2"
by (rule quasinorm_subsetI[of _ _ 1], auto simp add: quasinorm_sum(1), rule Inf_lower, auto,
  metis add.commute add.left_neutral eNorm_zero)+

lemma quasinorm_sum_maximum:
  assumes "N1 \<subseteq>\<^sub>N N" "N2 \<subseteq>\<^sub>N N"
  shows "N1 +\<^sub>N N2 \<subseteq>\<^sub>N N"
proof -
  obtain C1 C2::real where *: "\<And>f. eNorm N f \<le> C1 * eNorm N1 f"
                              "\<And>f. eNorm N f \<le> C2 * eNorm N2 f"
                              "C1 \<ge> 0" "C2 \<ge> 0"
    using quasinorm_subsetD[OF assms(1)] quasinorm_subsetD[OF assms(2)] by blast
  have **: "eNorm N f \<le> (defect N * max C1 C2) * eNorm (N1 +\<^sub>N N2) f" for f
  proof -
    obtain f1 f2 where F: "\<And>n. f = f1 n + f2 n"
                          "(\<lambda>n. eNorm N1 (f1 n) + eNorm N2 (f2 n)) \<longlonglongrightarrow> eNorm (N1 +\<^sub>N N2) f"
      using quasinorm_sum_limit by blast
    have "eNorm N f \<le> ennreal (defect N * max C1 C2) * (eNorm N1 (f1 n) + eNorm N2 (f2 n))" for n
    proof -
      have "eNorm N f \<le> ennreal(defect N) * eNorm N (f1 n) + ennreal(defect N) * eNorm N (f2 n)"
        unfolding \<open>f = f1 n + f2 n\<close> using eNorm_triangular_ineq by auto
      also have "... \<le> ennreal(defect N) * (C1 * eNorm N1 (f1 n)) + ennreal(defect N) * (C2 * eNorm N2 (f2 n))"
        apply (rule add_mono) by (rule mult_mono, simp, simp add: *, simp, simp)+
      also have "... \<le> ennreal(defect N) * (max C1 C2 * eNorm N1 (f1 n)) + ennreal(defect N) * (max C1 C2 * eNorm N2 (f2 n))"
        by (auto intro!:add_mono mult_mono ennreal_leI)
      also have "... = ennreal (defect N * max C1 C2) * (eNorm N1 (f1 n) + eNorm N2 (f2 n))"
        apply (subst ennreal_mult') using defect_ge_1 order_trans zero_le_one apply blast
        by (auto simp add: algebra_simps)
      finally show ?thesis by simp
    qed
    moreover have "... \<longlonglongrightarrow> (defect N * max C1 C2) * eNorm (N1 +\<^sub>N N2) f"
      by (auto intro!:tendsto_intros F(2))
    ultimately show ?thesis
      using LIMSEQ_le_const by blast
  qed
  then show ?thesis
    using quasinorm_subsetI by force
qed

lemma quasinorm_sum_assoc:
  "(N1 +\<^sub>N N2) +\<^sub>N N3 =\<^sub>N N1 +\<^sub>N (N2 +\<^sub>N N3)"
unfolding quasinorm_equivalent_def by (meson order_trans quasinorm_sum_maximum quasinorm_sum_subset)


subsection \<open>Topology\<close>

definition topology\<^sub>N::"('a::real_vector) quasinorm \<Rightarrow> 'a topology"
  where "topology\<^sub>N N = topology (\<lambda>U. \<forall>x\<in>U. \<exists>e>0. \<forall>y. eNorm N (y-x) < e \<longrightarrow> y \<in> U)"

lemma istopology_topology\<^sub>N:
  "istopology (\<lambda>U. \<forall>x\<in>U. \<exists>e>0. \<forall>y. eNorm N (y-x) < e \<longrightarrow> y \<in> U)"
unfolding istopology_def by (auto, metis dual_order.strict_trans less_linear, meson)

lemma openin_topology\<^sub>N:
  "openin (topology\<^sub>N N) U \<longleftrightarrow> (\<forall>x\<in>U. \<exists>e>0. \<forall>y. eNorm N (y-x) < e \<longrightarrow> y \<in> U)"
unfolding topology\<^sub>N_def using istopology_topology\<^sub>N[of N] by (simp add: topology_inverse')

lemma openin_topology\<^sub>N_I:
  assumes "\<And>x. x \<in> U \<Longrightarrow> \<exists>e>0. \<forall>y. eNorm N (y-x) < e \<longrightarrow> y \<in> U"
  shows "openin (topology\<^sub>N N) U"
using assms unfolding openin_topology\<^sub>N by auto

lemma openin_topology\<^sub>N_D:
  assumes "openin (topology\<^sub>N N) U"
          "x \<in> U"
  shows "\<exists>e>0. \<forall>y. eNorm N (y-x) < e \<longrightarrow> y \<in> U"
  using assms unfolding openin_topology\<^sub>N by auto

text \<open>One should then use this topology to define limits and so on. This is not something
specific to quasinorms, but to all topologies defined in this way, not using type classes.
However, there is no such body of material (yet?) in Isabelle-HOL, where topology is
essentially done with type classes. So, we do not go any further for now.

One exception is the notion of completeness, as it is so important in functional analysis.
We give a naive definition, which will be sufficient for the proof of completeness
of several spaces. Usually, the most convenient criterion to prove completeness of
a normed vector space is in terms of converging series. This criterion
is the only nontrivial thing we prove here. We will apply it to prove the
completeness of $L^p$ spaces.\<close>

definition cauchy_ine\<^sub>N::"('a::real_vector) quasinorm \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "cauchy_ine\<^sub>N N u = (\<forall>e>0. \<exists>M. \<forall>n\<ge>M. \<forall>m\<ge>M. eNorm N (u n - u m) < e)"


definition tendsto_ine\<^sub>N::"('a::real_vector) quasinorm \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a => bool"
  where "tendsto_ine\<^sub>N N u x = (\<lambda>n. eNorm N (u n - x)) \<longlonglongrightarrow> 0"

definition complete\<^sub>N::"('a::real_vector) quasinorm \<Rightarrow> bool"
  where "complete\<^sub>N N = (\<forall>u. cauchy_ine\<^sub>N N u \<longrightarrow> (\<exists>x. tendsto_ine\<^sub>N N u x))"

text \<open>The above definitions are in terms of eNorms, but usually the nice definitions
only make sense on the space of the norm, and are expressed in terms of Norms. We formulate
the same definitions with norms, they will be more convenient for the proofs.\<close>

definition cauchy_in\<^sub>N::"('a::real_vector) quasinorm \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "cauchy_in\<^sub>N N u = (\<forall>e>0. \<exists>M. \<forall>n\<ge>M. \<forall>m\<ge>M. Norm N (u n - u m) < e)"

definition tendsto_in\<^sub>N::"('a::real_vector) quasinorm \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a => bool"
  where "tendsto_in\<^sub>N N u x = (\<lambda>n. Norm N (u n - x)) \<longlonglongrightarrow> 0"

lemma cauchy_ine\<^sub>N_I:
  assumes "\<And>e. e > 0 \<Longrightarrow> (\<exists>M. \<forall>n\<ge>M. \<forall>m\<ge>M. eNorm N (u n - u m) < e)"
  shows "cauchy_ine\<^sub>N N u"
using assms unfolding cauchy_ine\<^sub>N_def by auto

lemma cauchy_in\<^sub>N_I:
  assumes "\<And>e. e > 0 \<Longrightarrow> (\<exists>M. \<forall>n\<ge>M. \<forall>m\<ge>M. Norm N (u n - u m) < e)"
  shows "cauchy_in\<^sub>N N u"
using assms unfolding cauchy_in\<^sub>N_def by auto

lemma cauchy_ine_in:
  assumes "\<And>n. u n \<in> space\<^sub>N N"
  shows "cauchy_ine\<^sub>N N u \<longleftrightarrow> cauchy_in\<^sub>N N u"
proof
  assume "cauchy_in\<^sub>N N u"
  show "cauchy_ine\<^sub>N N u"
  proof (rule cauchy_ine\<^sub>N_I)
    fix e::ennreal assume "e > 0"
    define e2 where "e2 = min e 1"
    then obtain r where "e2 = ennreal r" "r > 0" unfolding e2_def using \<open>e > 0\<close>
      by (metis ennreal_eq_1 ennreal_less_zero_iff le_ennreal_iff le_numeral_extra(1) min_def zero_less_one)
    then obtain M where *: "\<forall>n\<ge>M. \<forall>m\<ge>M. Norm N (u n - u m) < r"
      using \<open>cauchy_in\<^sub>N N u\<close> \<open>r > 0\<close> unfolding cauchy_in\<^sub>N_def by auto
    then have "\<forall>n\<ge>M. \<forall>m\<ge>M. eNorm N (u n - u m) < r"
      by (auto simp add: assms eNorm_Norm \<open>0 < r\<close> ennreal_lessI)
    then have "\<forall>n\<ge>M. \<forall>m\<ge>M. eNorm N (u n - u m) < e"
      unfolding \<open>e2 = ennreal r\<close>[symmetric] e2_def by auto
    then show "\<exists>M. \<forall>n\<ge>M. \<forall>m\<ge>M. eNorm N (u n - u m) < e"
      by auto
  qed
next
  assume "cauchy_ine\<^sub>N N u"
  show "cauchy_in\<^sub>N N u"
  proof (rule cauchy_in\<^sub>N_I)
    fix e::real assume "e > 0"
    then obtain M where *: "\<forall>n\<ge>M. \<forall>m\<ge>M. eNorm N (u n - u m) < e"
      using \<open>cauchy_ine\<^sub>N N u\<close> \<open>e > 0\<close> ennreal_less_zero_iff unfolding cauchy_ine\<^sub>N_def by blast
    then have "\<forall>n\<ge>M. \<forall>m\<ge>M. Norm N (u n - u m) < e"
      by (auto, metis Norm_def \<open>0 < e\<close> eNorm_Norm eNorm_Norm' enn2real_nonneg ennreal_less_iff)
    then show "\<exists>M. \<forall>n\<ge>M. \<forall>m\<ge>M. Norm N (u n - u m) < e"
      by auto
  qed
qed

lemma tendsto_ine_in:
  assumes "\<And>n. u n \<in> space\<^sub>N N" "x \<in> space\<^sub>N N"
  shows "tendsto_ine\<^sub>N N u x \<longleftrightarrow> tendsto_in\<^sub>N N u x"
proof -
  have *: "eNorm N (u n - x) = Norm N (u n - x)" for n
    using assms eNorm_Norm spaceN_diff by blast
  show ?thesis unfolding tendsto_in\<^sub>N_def tendsto_ine\<^sub>N_def *
    apply (auto)
    apply (metis (full_types) Norm_nonneg ennreal_0 eventually_sequentiallyI order_refl tendsto_ennreal_iff)
    using tendsto_ennrealI by fastforce
qed

lemma complete\<^sub>N_I:
  assumes "\<And>u. cauchy_in\<^sub>N N u \<Longrightarrow> (\<forall>n. u n \<in> space\<^sub>N N) \<Longrightarrow> (\<exists>x\<in> space\<^sub>N N. tendsto_in\<^sub>N N u x)"
  shows "complete\<^sub>N N"
proof -
  have "\<exists>x. tendsto_ine\<^sub>N N u x" if "cauchy_ine\<^sub>N N u" for u
  proof -
    obtain M::nat where *: "\<And>n m. n \<ge> M \<Longrightarrow> m \<ge> M \<Longrightarrow> eNorm N (u n - u m) < 1"
      using \<open>cauchy_ine\<^sub>N N u\<close> ennreal_zero_less_one unfolding cauchy_ine\<^sub>N_def by presburger
    define v where "v = (\<lambda>n. u (n+M) - u M)"
    have "eNorm N (v n) < 1" for n unfolding v_def using * by auto
    then have "v n \<in> space\<^sub>N N" for n using spaceN_iff[of _ N]
      by (metis dual_order.strict_trans ennreal_1 ennreal_less_top infinity_ennreal_def)
    have "cauchy_ine\<^sub>N N v"
    proof (rule cauchy_ine\<^sub>N_I)
      fix e::ennreal assume "e > 0"
      then obtain P::nat where *: "\<And>n m. n \<ge> P \<Longrightarrow> m \<ge> P \<Longrightarrow> eNorm N (u n - u m) < e"
        using \<open>cauchy_ine\<^sub>N N u\<close> unfolding cauchy_ine\<^sub>N_def by presburger
      have "eNorm N (v n - v m) < e" if "n \<ge> P" "m \<ge> P" for m n
        unfolding v_def by (auto, rule *, insert that, auto)
      then show "\<exists>M. \<forall>n\<ge>M. \<forall>m\<ge>M. eNorm N (v n - v m) < e" by auto
    qed
    then have "cauchy_in\<^sub>N N v" using cauchy_ine_in[OF \<open>\<And>n. v n \<in> space\<^sub>N N\<close>] by auto
    then obtain y where "tendsto_in\<^sub>N N v y" "y \<in> space\<^sub>N N"
      using assms \<open>\<And>n. v n \<in> space\<^sub>N N\<close> by auto
    then have *: "tendsto_ine\<^sub>N N v y"
      using tendsto_ine_in \<open>\<And>n. v n \<in> space\<^sub>N N\<close> by auto
    have "tendsto_ine\<^sub>N N u (y + u M)"
      unfolding tendsto_ine\<^sub>N_def apply (rule LIMSEQ_offset[of _ M])
      using * unfolding v_def tendsto_ine\<^sub>N_def by (auto simp add: algebra_simps)
    then show ?thesis by auto
  qed
  then show ?thesis unfolding complete\<^sub>N_def by auto
qed

lemma cauchy_tendsto_in_subseq:
  assumes "\<And>n. u n \<in> space\<^sub>N N"
          "cauchy_in\<^sub>N N u"
          "strict_mono r"
          "tendsto_in\<^sub>N N (u o r) x"
  shows "tendsto_in\<^sub>N N u x"
proof -
  have "\<exists>M. \<forall>n\<ge>M. Norm N (u n - x) < e" if "e > 0" for e
  proof -
    define f where "f = e / (2 * defect N)"
    have "f > 0" unfolding f_def using \<open>e > 0\<close> defect_ge_1[of N] by (auto simp add: divide_simps)
    obtain M1 where M1: "\<And>m n. m \<ge> M1 \<Longrightarrow> n \<ge> M1 \<Longrightarrow> Norm N (u n - u m) < f"
      using \<open>cauchy_in\<^sub>N N u\<close> unfolding cauchy_in\<^sub>N_def using \<open>f > 0\<close> by meson
    obtain M2 where M2: "\<And>n. n \<ge> M2 \<Longrightarrow> Norm N ((u o r) n - x) < f"
      using \<open>tendsto_in\<^sub>N N (u o r) x\<close> \<open>f > 0\<close> unfolding tendsto_in\<^sub>N_def order_tendsto_iff eventually_sequentially by blast
    define M where "M = max M1 M2"
    have "Norm N (u n - x) < e" if "n \<ge> M" for n
    proof -
      have "Norm N (u n - x) = Norm N ((u n - u (r M)) + (u (r M) - x))" by auto
      also have "... \<le> defect N * Norm N (u n - u (r M)) + defect N * Norm N (u (r M) - x)"
        apply (rule Norm_triangular_ineq) using \<open>\<And>n. u n \<in> space\<^sub>N N\<close> by simp
      also have "... < defect N * f + defect N * f"
        apply (auto intro!: add_strict_mono mult_mono simp only:)
        using defect_ge_1[of N] \<open>n \<ge> M\<close> seq_suble[OF \<open>strict_mono r\<close>, of M] M1 M2 o_def unfolding M_def by auto
      finally show ?thesis
        unfolding f_def using \<open>e > 0\<close> defect_ge_1[of N] by (auto simp add: divide_simps)
    qed
    then show ?thesis by auto
  qed
  then show ?thesis
    unfolding tendsto_in\<^sub>N_def order_tendsto_iff eventually_sequentially using Norm_nonneg less_le_trans by blast
qed

proposition complete\<^sub>N_I':
  assumes "\<And>n. c n > 0"
          "\<And>u. (\<forall>n. u n \<in> space\<^sub>N N) \<Longrightarrow> (\<forall>n. Norm N (u n) \<le> c n) \<Longrightarrow> \<exists>x\<in> space\<^sub>N N. tendsto_in\<^sub>N N (\<lambda>n. (\<Sum>i\<in>{0..<n}. u i)) x"
  shows "complete\<^sub>N N"
proof (rule complete\<^sub>N_I)
  fix v assume "cauchy_in\<^sub>N N v" "\<forall>n. v n \<in> space\<^sub>N N"
  have *: "\<exists>y. (\<forall>m\<ge>y. \<forall>p\<ge>y. Norm N (v m - v p) < c (Suc n)) \<and> x < y" if "\<forall>m\<ge>x. \<forall>p\<ge>x. Norm N (v m - v p) < c n" for x n
  proof -
    obtain M where i: "\<forall>m\<ge>M. \<forall>p\<ge>M. Norm N (v m - v p) < c (Suc n)"
      using \<open>cauchy_in\<^sub>N N v\<close> \<open>c (Suc n) > 0\<close> unfolding cauchy_in\<^sub>N_def by (meson zero_less_power)
    then show ?thesis
      apply (intro exI[of _ "max M (x+1)"]) by auto
  qed
  have "\<exists>r. \<forall>n. (\<forall>m\<ge>r n. \<forall>p\<ge>r n. Norm N (v m - v p) < c n) \<and> r n < r (Suc n)"
    apply (intro dependent_nat_choice) using \<open>cauchy_in\<^sub>N N v\<close> \<open>\<And>n. c n > 0\<close> * unfolding cauchy_in\<^sub>N_def by auto
  then obtain r where r: "strict_mono r" "\<And>n. \<forall>m\<ge>r n. \<forall>p\<ge>r n. Norm N (v m - v p) < c n"
    by (auto simp: strict_mono_Suc_iff)
  define u where "u = (\<lambda>n. v (r (Suc n)) - v (r n))"
  have "u n \<in> space\<^sub>N N" for n
    unfolding u_def using \<open>\<forall>n. v n \<in> space\<^sub>N N\<close> by simp
  moreover have "Norm N (u n) \<le> c n" for n
    unfolding u_def using r by (simp add: less_imp_le strict_mono_def)
  ultimately obtain y where y: "y \<in> space\<^sub>N N" "tendsto_in\<^sub>N N (\<lambda>n. (\<Sum>i\<in>{0..<n}. u i)) y"
    using assms(2) by blast
  define x where "x = y + v (r 0)"
  have "x \<in> space\<^sub>N N"
    unfolding x_def using \<open>y \<in> space\<^sub>N N\<close> \<open>\<forall>n. v n \<in> space\<^sub>N N\<close> by simp
  have "Norm N (v (r n) - x) = Norm N ((\<Sum>i\<in>{0..<n}. u i) - y)" for n
  proof -
    have "v (r n) = (\<Sum>i\<in>{0..<n}. u i) + v (r 0)" for n
      unfolding u_def by (induct n, auto)
    then show ?thesis unfolding x_def by (metis add_diff_cancel_right)
  qed
  then have "(\<lambda>n. Norm N (v (r n) - x)) \<longlonglongrightarrow> 0"
    using y(2) unfolding tendsto_in\<^sub>N_def by auto
  then have "tendsto_in\<^sub>N N (v o r) x"
    unfolding tendsto_in\<^sub>N_def comp_def by force
  then have "tendsto_in\<^sub>N N v x"
    using \<open>\<forall>n. v n \<in> space\<^sub>N N\<close> 
    by (intro cauchy_tendsto_in_subseq[OF _ \<open>cauchy_in\<^sub>N N v\<close> \<open>strict_mono r\<close>], auto)
  then show "\<exists>x\<in>space\<^sub>N N. tendsto_in\<^sub>N N v x"
    using \<open>x \<in> space\<^sub>N N\<close> by blast
qed

text \<open>Next, we show when the two examples of norms we have introduced before, the ambient norm
in a Banach space, and the norm on bounded continuous functions, are complete. We just have to
translate in our setting the already known completeness of these spaces.\<close>

lemma complete_N_of_norm:
  "complete\<^sub>N (N_of_norm::'a::banach quasinorm)"
proof (rule complete\<^sub>N_I)
  fix u::"nat \<Rightarrow> 'a" assume "cauchy_in\<^sub>N N_of_norm u"
  then have "Cauchy u" unfolding Cauchy_def cauchy_in\<^sub>N_def N_of_norm(2) by (simp add: dist_norm)
  then obtain x where "u \<longlonglongrightarrow> x" using convergent_eq_Cauchy by blast
  then have "tendsto_in\<^sub>N N_of_norm u x" unfolding tendsto_in\<^sub>N_def N_of_norm(2)
    using Lim_null tendsto_norm_zero_iff by fastforce
  moreover have "x \<in> space\<^sub>N N_of_norm" by auto
  ultimately show "\<exists>x\<in>space\<^sub>N N_of_norm. tendsto_in\<^sub>N N_of_norm u x" by auto
qed

text \<open>In the next statement, the assumption that \verb+'a+ is a metric space is not necessary,
a topological space would be enough, but a statement about uniform convergence is not available
in this setting.
TODO: fix it.
\<close>

lemma complete_bcontfunN:
  "complete\<^sub>N (bcontfun\<^sub>N::('a::metric_space \<Rightarrow> 'b::banach) quasinorm)"
proof (rule complete\<^sub>N_I)
  fix u::"nat \<Rightarrow> ('a \<Rightarrow> 'b)" assume H: "cauchy_in\<^sub>N bcontfun\<^sub>N u" "\<forall>n. u n \<in> space\<^sub>N bcontfun\<^sub>N"
  then have H2: "u n \<in> bcontfun" for n using bcontfun\<^sub>N_space by auto
  then have **: "Bcontfun(u n - u m) = Bcontfun (u n) - Bcontfun (u m)" for m n
    unfolding minus_fun_def minus_bcontfun_def by (simp add: Bcontfun_inverse)
  have *: "Norm bcontfun\<^sub>N (u n - u m) = norm (Bcontfun (u n - u m))" for n m
    unfolding bcontfun\<^sub>N(2) using H(2) bcontfun\<^sub>N_space by auto
  have "Cauchy (\<lambda>n. Bcontfun (u n))"
    using H(1) unfolding Cauchy_def cauchy_in\<^sub>N_def dist_norm * ** by simp
  then obtain v where v: "(\<lambda>n. Bcontfun (u n)) \<longlonglongrightarrow> v"
    using convergent_eq_Cauchy by blast
  have v_space: "apply_bcontfun v \<in> space\<^sub>N bcontfun\<^sub>N" unfolding bcontfun\<^sub>N_space by (simp add: apply_bcontfun)
  have ***: "Norm bcontfun\<^sub>N (u n - v) = norm(Bcontfun (u n) - v)" for n
  proof -
    have "Norm bcontfun\<^sub>N (u n - v) = norm (Bcontfun(u n - v))"
      unfolding bcontfun\<^sub>N(2) using H(2) bcontfun\<^sub>N_space v_space by auto
    moreover have "Bcontfun(u n - v) = Bcontfun (u n) - v"
      unfolding minus_fun_def minus_bcontfun_def by (simp add: Bcontfun_inverse H2)
    ultimately show ?thesis by simp
  qed
  have "tendsto_in\<^sub>N bcontfun\<^sub>N u v"
    unfolding tendsto_in\<^sub>N_def *** using v Lim_null tendsto_norm_zero_iff by fastforce
  then show "\<exists>v\<in>space\<^sub>N bcontfun\<^sub>N. tendsto_in\<^sub>N bcontfun\<^sub>N u v" using v_space by auto
qed

end
