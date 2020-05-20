(* Title:      Semirings
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Semirings\<close>

text \<open>
This theory develops a hierarchy of idempotent semirings.
All kinds of semiring considered here are bounded semilattices, but many lack additional properties typically assumed for semirings.
In particular, we consider the variants of semirings, in which
\begin{itemize}
\item multiplication is not required to be associative;
\item a right zero and unit of multiplication need not exist;
\item multiplication has a left residual;
\item multiplication from the left is not required to distribute over addition;
\item the semilattice order has a greatest element.
\end{itemize}
We have applied results from this theory a number of papers for unifying computation models.
For example, see \cite{Guttmann2012c} for various relational and matrix-based computation models and \cite{BerghammerGuttmann2015b} for multirelational models.

The main results in this theory relate different ways of defining reflexive-transitive closures as discussed in \cite{BerghammerGuttmann2015b}.
\<close>

theory Semirings

imports Fixpoints

begin

subsection \<open>Idempotent Semirings\<close>

text \<open>
The following definitions are standard for relations.
Putting them into a general class that depends only on the signature facilitates reuse.
Coreflexives are sometimes called partial identities, subidentities, monotypes or tests.
\<close>

class times_one_ord = times + one + ord
begin

abbreviation reflexive   :: "'a \<Rightarrow> bool" where "reflexive x   \<equiv> 1 \<le> x"
abbreviation coreflexive :: "'a \<Rightarrow> bool" where "coreflexive x \<equiv> x \<le> 1"

abbreviation transitive  :: "'a \<Rightarrow> bool" where "transitive x  \<equiv> x * x \<le> x"
abbreviation dense_rel   :: "'a \<Rightarrow> bool" where "dense_rel x   \<equiv> x \<le> x * x"
abbreviation idempotent  :: "'a \<Rightarrow> bool" where "idempotent x  \<equiv> x * x = x"

abbreviation preorder    :: "'a \<Rightarrow> bool" where "preorder x    \<equiv> reflexive x \<and> transitive x"

abbreviation "coreflexives \<equiv> { x . coreflexive x }"

end

text \<open>
The first algebra is a very weak idempotent semiring, in which multiplication is not necessarily associative.
\<close>

class non_associative_left_semiring = bounded_semilattice_sup_bot + times + one +
  assumes mult_left_sub_dist_sup: "x * y \<squnion> x * z \<le> x * (y \<squnion> z)"
  assumes mult_right_dist_sup: "(x \<squnion> y) * z = x * z \<squnion> y * z"
  assumes mult_left_zero [simp]: "bot * x = bot"
  assumes mult_left_one [simp]: "1 * x = x"
  assumes mult_sub_right_one: "x \<le> x * 1"
begin

subclass times_one_ord .

text \<open>
We first show basic isotonicity and subdistributivity properties of multiplication.
\<close>

lemma mult_left_isotone:
  "x \<le> y \<Longrightarrow> x * z \<le> y * z"
  using mult_right_dist_sup sup_right_divisibility by auto

lemma mult_right_isotone:
  "x \<le> y \<Longrightarrow> z * x \<le> z * y"
  using mult_left_sub_dist_sup sup.bounded_iff sup_right_divisibility by auto

lemma mult_isotone:
  "w \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> w * x \<le> y * z"
  using order_trans mult_left_isotone mult_right_isotone by blast

lemma affine_isotone:
  "isotone (\<lambda>x . y * x \<squnion> z)"
  using isotone_def mult_right_isotone sup_left_isotone by auto

lemma mult_left_sub_dist_sup_left:
  "x * y \<le> x * (y \<squnion> z)"
  by (simp add: mult_right_isotone)

lemma mult_left_sub_dist_sup_right:
  "x * z \<le> x * (y \<squnion> z)"
  by (simp add: mult_right_isotone)

lemma mult_right_sub_dist_sup_left:
  "x * z \<le> (x \<squnion> y) * z"
  by (simp add: mult_left_isotone)

lemma mult_right_sub_dist_sup_right:
  "y * z \<le> (x \<squnion> y) * z"
  by (simp add: mult_left_isotone)

lemma case_split_left:
  assumes "1 \<le> w \<squnion> z"
      and "w * x \<le> y"
      and "z * x \<le> y"
    shows "x \<le> y"
proof -
  have "(w \<squnion> z) * x \<le> y"
    by (simp add: assms(2-3) mult_right_dist_sup)
  thus ?thesis
    by (metis assms(1) dual_order.trans mult_left_one mult_left_isotone)
qed

lemma case_split_left_equal:
  "w \<squnion> z = 1 \<Longrightarrow> w * x = w * y \<Longrightarrow> z * x = z * y \<Longrightarrow> x = y"
  by (metis mult_left_one mult_right_dist_sup)

text \<open>
Next we consider under which semiring operations the above properties are closed.
\<close>

lemma reflexive_one_closed:
  "reflexive 1"
  by simp

lemma reflexive_sup_closed:
  "reflexive x \<Longrightarrow> reflexive (x \<squnion> y)"
  by (simp add: le_supI1)

lemma reflexive_mult_closed:
  "reflexive x \<Longrightarrow> reflexive y \<Longrightarrow> reflexive (x * y)"
  using mult_isotone by fastforce

lemma coreflexive_bot_closed:
  "coreflexive bot"
  by simp

lemma coreflexive_one_closed:
  "coreflexive 1"
  by simp

lemma coreflexive_sup_closed:
  "coreflexive x \<Longrightarrow> coreflexive y \<Longrightarrow> coreflexive (x \<squnion> y)"
  by simp

lemma coreflexive_mult_closed:
  "coreflexive x \<Longrightarrow> coreflexive y \<Longrightarrow> coreflexive (x * y)"
  using mult_isotone by fastforce

lemma transitive_bot_closed:
  "transitive bot"
  by simp

lemma transitive_one_closed:
  "transitive 1"
  by simp

lemma dense_bot_closed:
  "dense_rel bot"
  by simp

lemma dense_one_closed:
  "dense_rel 1"
  by simp

lemma dense_sup_closed:
  "dense_rel x \<Longrightarrow> dense_rel y \<Longrightarrow> dense_rel (x \<squnion> y)"
  by (metis mult_right_dist_sup order_lesseq_imp sup.mono mult_left_sub_dist_sup_left mult_left_sub_dist_sup_right)

lemma idempotent_bot_closed:
  "idempotent bot"
  by simp

lemma idempotent_one_closed:
  "idempotent 1"
  by simp

lemma preorder_one_closed:
  "preorder 1"
  by simp

lemma coreflexive_transitive:
  "coreflexive x \<Longrightarrow> transitive x"
  using mult_left_isotone by fastforce

lemma preorder_idempotent:
  "preorder x \<Longrightarrow> idempotent x"
  using antisym mult_isotone by fastforce

text \<open>
We study the following three ways of defining reflexive-transitive closures.
Each of them is given as a least prefixpoint, but the underlying functions are different.
They implement left recursion, right recursion and symmetric recursion, respectively.
\<close>

abbreviation Lf :: "'a \<Rightarrow> ('a \<Rightarrow> 'a)" where "Lf y \<equiv> (\<lambda>x . 1 \<squnion> x * y)"
abbreviation Rf :: "'a \<Rightarrow> ('a \<Rightarrow> 'a)" where "Rf y \<equiv> (\<lambda>x . 1 \<squnion> y * x)"
abbreviation Sf :: "'a \<Rightarrow> ('a \<Rightarrow> 'a)" where "Sf y \<equiv> (\<lambda>x . 1 \<squnion> y \<squnion> x * x)"

abbreviation lstar :: "'a \<Rightarrow> 'a" where "lstar y \<equiv> p\<mu> (Lf y)"
abbreviation rstar :: "'a \<Rightarrow> 'a" where "rstar y \<equiv> p\<mu> (Rf y)"
abbreviation sstar :: "'a \<Rightarrow> 'a" where "sstar y \<equiv> p\<mu> (Sf y)"

text \<open>
All functions are isotone and, therefore, if the prefixpoints exist they are also fixpoints.
\<close>

lemma lstar_rec_isotone:
  "isotone (Lf y)"
  using isotone_def sup_right_divisibility sup_right_isotone mult_right_sub_dist_sup_right by auto

lemma rstar_rec_isotone:
  "isotone (Rf y)"
  using isotone_def sup_right_divisibility sup_right_isotone mult_left_sub_dist_sup_right by auto

lemma sstar_rec_isotone:
  "isotone (Sf y)"
  using isotone_def sup_right_isotone mult_isotone by auto

lemma lstar_fixpoint:
  "has_least_prefixpoint (Lf y) \<Longrightarrow> lstar y = \<mu> (Lf y)"
  by (simp add: pmu_mu lstar_rec_isotone)

lemma rstar_fixpoint:
  "has_least_prefixpoint (Rf y) \<Longrightarrow> rstar y = \<mu> (Rf y)"
  by (simp add: pmu_mu rstar_rec_isotone)

lemma sstar_fixpoint:
  "has_least_prefixpoint (Sf y) \<Longrightarrow> sstar y = \<mu> (Sf y)"
  by (simp add: pmu_mu sstar_rec_isotone)

lemma sstar_increasing:
  "has_least_prefixpoint (Sf y) \<Longrightarrow> y \<le> sstar y"
  using order_trans pmu_unfold sup_ge1 sup_ge2 by blast

text \<open>
The fixpoint given by right recursion is always below the one given by symmetric recursion.
\<close>

lemma rstar_below_sstar:
  assumes "has_least_prefixpoint (Rf y)"
      and "has_least_prefixpoint (Sf y)"
    shows "rstar y \<le> sstar y"
proof -
  have "y \<le> sstar y"
    using assms(2) pmu_unfold by force
  hence "Rf y (sstar y) \<le> Sf y (sstar y)"
    by (meson sup.cobounded1 sup.mono mult_left_isotone)
  also have "... \<le> sstar y"
    using assms(2) pmu_unfold by blast
  finally show ?thesis
    using assms(1) is_least_prefixpoint_def least_prefixpoint by auto
qed

end

text \<open>
Our next structure adds one half of the associativity property.
This inequality holds, for example, for multirelations under the compositions defined by Parikh and Peleg \cite{Parikh1983,Peleg1987}.
The converse inequality requires up-closed multirelations for Parikh's composition.
\<close>

class pre_left_semiring = non_associative_left_semiring +
  assumes mult_semi_associative: "(x * y) * z \<le> x * (y * z)"
begin

lemma mult_one_associative [simp]:
  "x * 1 * y = x * y"
  by (metis dual_order.antisym mult_left_isotone mult_left_one mult_semi_associative mult_sub_right_one)

lemma mult_sup_associative_one:
  "(x * (y * 1)) * z \<le> x * (y * z)"
  by (metis mult_semi_associative mult_one_associative)

lemma rstar_increasing:
  assumes "has_least_prefixpoint (Rf y)"
    shows "y \<le> rstar y"
proof -
  have "Rf y (rstar y) \<le> rstar y"
    using assms pmu_unfold by blast
  thus ?thesis
    by (metis le_supE mult_right_isotone mult_sub_right_one sup.absorb_iff2)
qed

end

text \<open>
For the next structure we add a left residual operation.
Such a residual is available, for example, for multirelations.

The operator notation for binary division is introduced in a class that requires a unary inverse.
This is appropriate for fields, but too strong in the present context of semirings.
We therefore reintroduce it without requiring a unary inverse.
\<close>

no_notation
  inverse_divide (infixl "'/" 70)

notation
  divide (infixl "'/" 70)

class residuated_pre_left_semiring = pre_left_semiring + divide +
  assumes lres_galois: "x * y \<le> z \<longleftrightarrow> x \<le> z / y"
begin

text \<open>
We first derive basic properties of left residuals from the Galois connection.
\<close>

lemma lres_left_isotone:
  "x \<le> y \<Longrightarrow> x / z \<le> y / z"
  using dual_order.trans lres_galois by blast

lemma lres_right_antitone:
  "x \<le> y \<Longrightarrow> z / y \<le> z / x"
  using dual_order.trans lres_galois mult_right_isotone by blast

lemma lres_inverse:
  "(x / y) * y \<le> x"
  by (simp add: lres_galois)

lemma lres_one:
  "x / 1 \<le> x"
  using mult_sub_right_one order_trans lres_inverse by blast

lemma lres_mult_sub_lres_lres:
  "x / (z * y) \<le> (x / y) / z"
  using lres_galois mult_semi_associative order.trans by blast

lemma mult_lres_sub_assoc:
  "x * (y / z) \<le> (x * y) / z"
  by (meson dual_order.trans lres_galois mult_right_isotone lres_inverse lres_mult_sub_lres_lres)

text \<open>
With the help of a left residual, it follows that left recursion is below right recursion.
\<close>

lemma lstar_below_rstar:
  assumes "has_least_prefixpoint (Lf y)"
      and "has_least_prefixpoint (Rf y)"
    shows "lstar y \<le> rstar y"
proof -
  have "y * (rstar y / y) * y \<le> y * rstar y"
    using lres_galois mult_lres_sub_assoc by auto
  also have "... \<le> rstar y"
    using assms(2) le_supE pmu_unfold by blast
  finally have "y * (rstar y / y) \<le> rstar y / y"
    by (simp add: lres_galois)
  hence "Rf y (rstar y / y) \<le> rstar y / y"
    using assms(2) lres_galois rstar_increasing by fastforce
  hence "rstar y \<le> rstar y / y"
    using assms(2) is_least_prefixpoint_def least_prefixpoint by auto
  hence "Lf y (rstar y) \<le> rstar y"
    using assms(2) lres_galois pmu_unfold by fastforce
  thus ?thesis
    using assms(1) is_least_prefixpoint_def least_prefixpoint by auto
qed

text \<open>
Moreover, right recursion gives the same result as symmetric recursion.
The next proof follows an argument of \cite[Satz 10.1.5]{Berghammer2012}.
\<close>

lemma rstar_sstar:
  assumes "has_least_prefixpoint (Rf y)"
      and "has_least_prefixpoint (Sf y)"
    shows "rstar y = sstar y"
proof -
  have "Rf y (rstar y / rstar y) * rstar y \<le> rstar y \<squnion> y * ((rstar y / rstar y) * rstar y)"
    using mult_right_dist_sup mult_semi_associative sup_right_isotone by auto
  also have "... \<le> rstar y \<squnion> y * rstar y"
    using mult_right_isotone sup_right_isotone lres_inverse by blast
  also have "... \<le> rstar y"
    using assms(1) pmu_unfold by fastforce
  finally have "Rf y (rstar y / rstar y) \<le> rstar y / rstar y"
    by (simp add: lres_galois)
  hence "rstar y * rstar y \<le> rstar y"
    using assms(1) is_least_prefixpoint_def least_prefixpoint lres_galois by auto
  hence "y \<squnion> rstar y * rstar y \<le> rstar y"
    by (simp add: assms(1) rstar_increasing)
  hence "Sf y (rstar y) \<le> rstar y"
    using assms(1) pmu_unfold by force
  hence "sstar y \<le> rstar y"
    using assms(2) is_least_prefixpoint_def least_prefixpoint by auto
  thus ?thesis
    by (simp add: assms antisym rstar_below_sstar)
qed

end

text \<open>
In the next structure we add full associativity of multiplication, as well as a right unit.
Still, multiplication does not need to have a right zero and does not need to distribute over addition from the left.
\<close>

class idempotent_left_semiring = non_associative_left_semiring + monoid_mult
begin

subclass pre_left_semiring
  by unfold_locales (simp add: mult_assoc)

lemma zero_right_mult_decreasing:
  "x * bot \<le> x"
  by (metis bot_least mult_1_right mult_right_isotone)

text \<open>
The following result shows that for dense coreflexives there are two equivalent ways to express that a property is preserved.
In the setting of Kleene algebras, this is well known for tests, which form a Boolean subalgebra.
The point here is that only very few properties of tests are needed to show the equivalence.
\<close>

lemma test_preserves_equation:
  assumes "dense_rel p"
      and "coreflexive p"
    shows "p * x \<le> x * p \<longleftrightarrow> p * x = p * x * p"
proof
  assume 1: "p * x \<le> x * p"
  have "p * x \<le> p * p * x"
    by (simp add: assms(1) mult_left_isotone)
  also have "... \<le> p * x * p"
    using 1 by (simp add: mult_right_isotone mult_assoc)
  finally show "p * x = p * x * p"
    using assms(2) antisym mult_right_isotone by fastforce
next
  assume "p * x = p * x * p"
  thus "p * x \<le> x * p"
    by (metis assms(2) mult_left_isotone mult_left_one)
qed

end

text \<open>
The next structure has both distributivity properties of multiplication.
Only a right zero is missing from full semirings.
This is important as many computation models do not have a right zero of sequential composition.
\<close>

class idempotent_left_zero_semiring = idempotent_left_semiring +
  assumes mult_left_dist_sup: "x * (y \<squnion> z) = x * y \<squnion> x * z"
begin

lemma case_split_right:
  assumes "1 \<le> w \<squnion> z"
      and "x * w \<le> y"
      and "x * z \<le> y"
    shows "x \<le> y"
proof -
  have "x * (w \<squnion> z) \<le> y"
    by (simp add: assms(2-3) mult_left_dist_sup)
  thus ?thesis
    by (metis assms(1) dual_order.trans mult_1_right mult_right_isotone)
qed

lemma case_split_right_equal:
  "w \<squnion> z = 1 \<Longrightarrow> x * w = y * w \<Longrightarrow> x * z = y * z \<Longrightarrow> x = y"
  by (metis mult_1_right mult_left_dist_sup)

text \<open>
This is the first structure we can connect to the semirings provided by Isabelle/HOL.
\<close>

sublocale semiring: ordered_semiring sup bot less_eq less times
  apply unfold_locales
  using sup_right_isotone apply blast
  apply (simp add: mult_right_dist_sup)
  apply (simp add: mult_left_dist_sup)
  apply (simp add: mult_right_isotone)
  by (simp add: mult_left_isotone)

sublocale semiring: semiring_numeral 1 times sup ..

end

text \<open>
Completing this part of the hierarchy, we obtain idempotent semirings by adding a right zero of multiplication.
\<close>

class idempotent_semiring = idempotent_left_zero_semiring +
  assumes mult_right_zero [simp]: "x * bot = bot"
begin

sublocale semiring: semiring_0 sup bot times
  by unfold_locales simp_all

end

subsection \<open>Bounded Idempotent Semirings\<close>

text \<open>
All of the following semirings have a greatest element in the underlying semilattice order.
With this element, we can express further standard properties of relations.
We extend each class in the above hierarchy in turn.
\<close>

class times_top = times + top
begin

abbreviation vector     :: "'a \<Rightarrow> bool" where "vector x     \<equiv> x * top = x"
abbreviation covector   :: "'a \<Rightarrow> bool" where "covector x   \<equiv> top * x = x"
abbreviation total      :: "'a \<Rightarrow> bool" where "total x      \<equiv> x * top = top"
abbreviation surjective :: "'a \<Rightarrow> bool" where "surjective x \<equiv> top * x = top"

abbreviation "vectors   \<equiv> { x . vector x }"
abbreviation "covectors \<equiv> { x . covector x }"

end

class bounded_non_associative_left_semiring = non_associative_left_semiring + top +
  assumes sup_right_top [simp]: "x \<squnion> top = top"
begin

subclass times_top .

text \<open>
We first give basic properties of the greatest element.
\<close>

lemma sup_left_top [simp]:
  "top \<squnion> x = top"
  using sup_right_top sup.commute by fastforce

lemma top_greatest [simp]:
  "x \<le> top"
  by (simp add: le_iff_sup)

lemma top_left_mult_increasing:
  "x \<le> top * x"
  by (metis mult_left_isotone mult_left_one top_greatest)

lemma top_right_mult_increasing:
  "x \<le> x * top"
  using mult_right_isotone mult_sub_right_one order_trans top_greatest by blast

lemma top_mult_top [simp]:
  "top * top = top"
  by (simp add: antisym top_left_mult_increasing)

text \<open>
Closure of the above properties under the semiring operations is considered next.
\<close>

lemma vector_bot_closed:
  "vector bot"
  by simp

lemma vector_top_closed:
  "vector top"
  by simp

lemma vector_sup_closed:
  "vector x \<Longrightarrow> vector y \<Longrightarrow> vector (x \<squnion> y)"
  by (simp add: mult_right_dist_sup)

lemma covector_top_closed:
  "covector top"
  by simp

lemma total_one_closed:
  "total 1"
  by simp

lemma total_top_closed:
  "total top"
  by simp

lemma total_sup_closed:
  "total x \<Longrightarrow> total (x \<squnion> y)"
  by (simp add: mult_right_dist_sup)

lemma surjective_one_closed:
  "surjective 1"
  by (simp add: antisym mult_sub_right_one)

lemma surjective_top_closed:
  "surjective top"
  by simp

lemma surjective_sup_closed:
  "surjective x \<Longrightarrow> surjective (x \<squnion> y)"
  by (metis le_iff_sup mult_left_sub_dist_sup_left sup_left_top)

lemma reflexive_top_closed:
  "reflexive top"
  by simp

lemma transitive_top_closed:
  "transitive top"
  by simp

lemma dense_top_closed:
  "dense_rel top"
  by simp

lemma idempotent_top_closed:
  "idempotent top"
  by simp

lemma preorder_top_closed:
  "preorder top"
  by simp

end

text \<open>
Some closure properties require at least half of associativity.
\<close>

class bounded_pre_left_semiring = pre_left_semiring + bounded_non_associative_left_semiring
begin

lemma vector_mult_closed:
  "vector y \<Longrightarrow> vector (x * y)"
  by (metis antisym mult_semi_associative top_right_mult_increasing)

lemma surjective_mult_closed:
  "surjective x \<Longrightarrow> surjective y \<Longrightarrow> surjective (x * y)"
  by (metis antisym mult_semi_associative top_greatest)

end

text \<open>
We next consider residuals with the greatest element.
\<close>

class bounded_residuated_pre_left_semiring = residuated_pre_left_semiring + bounded_pre_left_semiring
begin

lemma lres_top_decreasing:
  "x / top \<le> x"
  using lres_inverse order.trans top_right_mult_increasing by blast

lemma top_lres_absorb [simp]:
  "top / x = top"
  using antisym lres_galois top_greatest by blast

lemma covector_lres_closed:
  "covector x \<Longrightarrow> covector (x / y)"
  by (metis antisym mult_lres_sub_assoc top_left_mult_increasing)

end

text \<open>
Some closure properties require full associativity.
\<close>

class bounded_idempotent_left_semiring = bounded_pre_left_semiring + idempotent_left_semiring
begin

lemma covector_mult_closed:
  "covector x \<Longrightarrow> covector (x * y)"
  by (metis mult_assoc)

lemma total_mult_closed:
  "total x \<Longrightarrow> total y \<Longrightarrow> total (x * y)"
  by (simp add: mult_assoc)

end

text \<open>
Some closure properties require distributivity from the left.
\<close>

class bounded_idempotent_left_zero_semiring = bounded_idempotent_left_semiring + idempotent_left_zero_semiring
begin

lemma covector_sup_closed:
  "covector x \<Longrightarrow> covector y \<Longrightarrow> covector (x \<squnion> y)"
  by (simp add: mult_left_dist_sup)

end

text \<open>
Our final structure is an idempotent semiring with a greatest element.
\<close>

class bounded_idempotent_semiring = bounded_idempotent_left_zero_semiring + idempotent_semiring
begin

lemma covector_bot_closed:
  "covector bot"
  by simp

end

end

