(*
  File:   Zeta_3_Irrational.thy
  Author: Manuel Eberl, TU München
*)
section \<open>The Irrationality of $\zeta(3)$\<close>
theory Zeta_3_Irrational
imports
  "E_Transcendental.E_Transcendental"
  "Prime_Number_Theorem.Prime_Number_Theorem"
  "Prime_Distribution_Elementary.PNT_Consequences"
begin

text \<open>
  Ap\'{e}ry's original proof of the irrationality of $\zeta(3)$ contained several
  tricky identities of sums involving binomial coefficients that are difficult to
  prove. I instead follow Beukers's proof, which consists of several fairly
  straightforward manipulations of integrals with absolutely no caveats.

  Both Ap\'{e}ry and Beukers make use of an asymptotic upper bound on
  $\text{lcm}\{1\ldots n\}$ -- namely $\text{lcm}\{1\ldots n\} \in o(c^n)$ for
  any $c > e$, which is a consequence of the Prime Number Theorem (which, fortunately,
  is available in the \emph{Archive of Formal Proofs}~\cite{afp_primes1,afp_primes2}).

  I follow the concise presentation of Beukers's proof in Filaseta's lecture
  notes~\cite{filaseta}, which turned out to be very amenable to formalisation.

  There is another earlier formalisation of the irrationality of $\zeta(3)$ by
  Mahboubi\ \emph{et al.}~\cite{mahboubi}, who followed Ap\'{e}ry's original proof,
  but were ultimately forced to find a more elementary way to prove the asymptotics
  of $\text{lcm}\{1\ldots n\}$ than the Prime Number Theorem.

  First, we will require some auxiliary material before we get started with the actual
  proof.
\<close>

(* TODO: A lot of this (if not all of it) should really be in the library *)
subsection \<open>Auxiliary facts about polynomials\<close>

lemma degree_higher_pderiv: "degree ((pderiv ^^ n) p) = degree p - n"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
  by (induction n arbitrary: p) (auto simp: degree_pderiv)

lemma pcompose_power_left: "pcompose (p ^ n) q = pcompose p q ^ n"
  by (induction n) (auto simp: pcompose_mult pcompose_1)

lemma pderiv_sum: "pderiv (\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. pderiv (f x))"
  by (induction A rule: infinite_finite_induct) (auto simp: pderiv_add)

lemma higher_pderiv_minus: "(pderiv ^^ n) (-p :: 'a :: idom poly) = -(pderiv ^^ n) p"
  by (induction n) (auto simp: pderiv_minus)

lemma pderiv_power: "pderiv (p ^ n) = smult (of_nat n) (p ^ (n - 1)) * pderiv p"
  by (cases n) (simp_all add: pderiv_power_Suc del: power_Suc)

lemma pderiv_monom: "pderiv (monom c n) = monom (of_nat n * c) (n - 1)"
  by (simp add: monom_altdef pderiv_smult pderiv_power pderiv_pCons mult_ac)

lemma higher_pderiv_monom:
  "k \<le> n \<Longrightarrow> (pderiv ^^ k) (monom c n) = monom (of_nat (pochhammer (n - k + 1) k) * c) (n - k)"
  by (induction k) (auto simp: pderiv_monom pochhammer_rec Suc_diff_le Suc_diff_Suc mult_ac)

lemma higher_pderiv_mult:
  "(pderiv ^^ n) (p * q) =
     (\<Sum>k\<le>n. Polynomial.smult (of_nat (n choose k)) ((pderiv ^^ k) p * (pderiv ^^ (n - k)) q))"
proof (induction n)
  case (Suc n)
  have eq: "(Suc n choose k) = (n choose k) + (n choose (k-1))" if "k > 0" for k
    using that by (cases k) auto
  have "(pderiv ^^ Suc n) (p * q) =
          (\<Sum>k\<le>n. smult (of_nat (n choose k)) ((pderiv ^^ k) p * (pderiv ^^ (Suc n - k)) q)) +
          (\<Sum>k\<le>n. smult (of_nat (n choose k)) ((pderiv ^^ Suc k) p * (pderiv ^^ (n - k)) q))"
    by (simp add: Suc pderiv_sum pderiv_smult pderiv_mult sum.distrib smult_add_right algebra_simps Suc_diff_le)
  also have "(\<Sum>k\<le>n. smult (of_nat (n choose k)) ((pderiv ^^ k) p * (pderiv ^^ (Suc n - k)) q)) =
             (\<Sum>k\<in>insert 0 {1..n}. smult (of_nat (n choose k)) ((pderiv ^^ k) p * (pderiv ^^ (Suc n - k)) q))"
    by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>k=1..n. smult (of_nat (n choose k)) ((pderiv ^^ k) p * (pderiv ^^ (Suc n - k)) q)) + p * (pderiv ^^ Suc n) q"
    by (subst sum.insert) (auto simp: add_ac)
  also have "(\<Sum>k\<le>n. smult (of_nat (n choose k)) ((pderiv ^^ Suc k) p * (pderiv ^^ (n - k)) q)) =
             (\<Sum>k=1..n+1. smult (of_nat (n choose (k-1))) ((pderiv ^^ k) p * (pderiv ^^ (Suc n - k)) q))"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>k. k - 1" Suc]) auto
  also have "\<dots> = (\<Sum>k\<in>insert (n+1) {1..n}. smult (of_nat (n choose (k-1))) ((pderiv ^^ k) p * (pderiv ^^ (Suc n - k)) q))"
    by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>k=1..n. smult (of_nat (n choose (k-1))) ((pderiv ^^ k) p * (pderiv ^^ (Suc n - k)) q)) + (pderiv ^^ Suc n) p * q"
    by (subst sum.insert) (auto simp: add_ac)
  also have "(\<Sum>k=1..n. smult (of_nat (n choose k)) ((pderiv ^^ k) p * (pderiv ^^ (Suc n - k)) q)) +
                 p * (pderiv ^^ Suc n) q + \<dots> =
             (\<Sum>k=1..n. smult (of_nat (Suc n choose k)) ((pderiv ^^ k) p * (pderiv ^^ (Suc n - k)) q)) +
                 p * (pderiv ^^ Suc n) q + (pderiv ^^ Suc n) p * q"
    by (simp add: sum.distrib algebra_simps smult_add_right eq smult_add_left)
  also have "\<dots> = (\<Sum>k\<in>{1..n}\<union>{0,Suc n}. smult (of_nat (Suc n choose k)) ((pderiv ^^ k) p * (pderiv ^^ (Suc n - k)) q))"
    by (subst sum.union_disjoint) (auto simp: algebra_simps)
  also have "{1..n}\<union>{0,Suc n} = {..Suc n}" by auto
  finally show ?case .
qed auto

subsection \<open>Auxiliary facts about integrals\<close>

theorem (in pair_sigma_finite) Fubini_set_integrable:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f[measurable]: "set_borel_measurable (M1 \<Otimes>\<^sub>M M2) (A \<times> B) f"
    and integ1: "set_integrable M1 A (\<lambda>x. \<integral>y\<in>B. norm (f (x, y)) \<partial>M2)"
    and integ2: "AE x\<in>A in M1. set_integrable M2 B (\<lambda>y. f (x, y))"
  shows "set_integrable (M1 \<Otimes>\<^sub>M M2) (A \<times> B) f"
  unfolding set_integrable_def
proof (rule Fubini_integrable)
  note integ1
  also have "set_integrable M1 A (\<lambda>x. \<integral>y\<in>B. norm (f (x, y)) \<partial>M2) \<longleftrightarrow>
        integrable M1 (\<lambda>x. LINT y|M2. norm (indicat_real (A \<times> B) (x, y) *\<^sub>R f (x, y)))"
    unfolding set_integrable_def
    by (intro integrable_cong) (auto simp: indicator_def set_lebesgue_integral_def)
  finally show \<dots> .
next
  from integ2 show "AE x in M1. integrable M2 (\<lambda>y. indicat_real (A \<times> B) (x, y) *\<^sub>R f (x, y))"
  proof eventually_elim
    case (elim x)
    show "integrable M2 (\<lambda>y. indicat_real (A \<times> B) (x, y) *\<^sub>R f (x, y))"
    proof (cases "x \<in> A")
      case True
      with elim have "set_integrable M2 B (\<lambda>y. f (x, y))" by simp
      also have "?this \<longleftrightarrow> ?thesis"
        unfolding set_integrable_def using True
        by (intro integrable_cong) (auto simp: indicator_def)
      finally show ?thesis .
    qed auto
  qed
qed (insert assms, auto simp: set_borel_measurable_def)

lemma (in pair_sigma_finite) set_integral_fst':
  fixes f :: "_ \<Rightarrow> 'c :: {second_countable_topology, banach}"
  assumes "set_integrable (M1 \<Otimes>\<^sub>M M2) (A \<times> B) f"
  shows   "set_lebesgue_integral (M1 \<Otimes>\<^sub>M M2) (A \<times> B) f =
             (\<integral>x\<in>A. (\<integral>y\<in>B. f (x, y) \<partial>M2) \<partial>M1)"
proof -
  have "set_lebesgue_integral (M1 \<Otimes>\<^sub>M M2) (A \<times> B) f =
          (\<integral>z. indicator (A \<times> B) z *\<^sub>R f z \<partial>(M1 \<Otimes>\<^sub>M M2))"
    by (simp add: set_lebesgue_integral_def)
  also have "\<dots> = (\<integral>x. \<integral>y. indicator (A \<times> B) (x,y) *\<^sub>R f (x,y) \<partial>M2 \<partial>M1)"
    using assms by (subst integral_fst' [symmetric]) (auto simp: set_integrable_def)
  also have "\<dots> = (\<integral>x\<in>A. (\<integral>y\<in>B. f (x,y) \<partial>M2) \<partial>M1)"
    unfolding set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_cong refl) (auto simp: indicator_def)
  finally show ?thesis .
qed

lemma (in pair_sigma_finite) set_integral_snd:
  fixes f :: "_ \<Rightarrow> 'c :: {second_countable_topology, banach}"
  assumes "set_integrable (M1 \<Otimes>\<^sub>M M2) (A \<times> B) f"
  shows   "set_lebesgue_integral (M1 \<Otimes>\<^sub>M M2) (A \<times> B) f =
             (\<integral>y\<in>B. (\<integral>x\<in>A. f (x, y) \<partial>M1) \<partial>M2)"
proof -
  have "set_lebesgue_integral (M1 \<Otimes>\<^sub>M M2) (A \<times> B) f =
          (\<integral>z. indicator (A \<times> B) z *\<^sub>R f z \<partial>(M1 \<Otimes>\<^sub>M M2))"
    by (simp add: set_lebesgue_integral_def)
  also have "\<dots> = (\<integral>y. \<integral>x. indicator (A \<times> B) (x,y) *\<^sub>R f (x,y) \<partial>M1 \<partial>M2)"
    using assms by (subst integral_snd) (auto simp: set_integrable_def case_prod_unfold)
  also have "\<dots> = (\<integral>y\<in>B. (\<integral>x\<in>A. f (x,y) \<partial>M1) \<partial>M2)"
    unfolding set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_cong refl) (auto simp: indicator_def)
  finally show ?thesis .
qed

proposition (in pair_sigma_finite) Fubini_set_integral:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes f: "set_integrable (M1 \<Otimes>\<^sub>M M2) (A \<times> B) (case_prod f)"
  shows "(\<integral>y\<in>B. (\<integral>x\<in>A. f x y \<partial>M1) \<partial>M2) = (\<integral>x\<in>A. (\<integral>y\<in>B. f x y \<partial>M2) \<partial>M1)"
proof -
  have "(\<integral>y\<in>B. (\<integral>x\<in>A. f x y \<partial>M1) \<partial>M2) = (\<integral>y. (\<integral>x. indicator (A \<times> B) (x, y) *\<^sub>R f x y \<partial>M1) \<partial>M2)"
    unfolding set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_cong) (auto simp: indicator_def)
  also have "\<dots> = (\<integral>x. (\<integral>y. indicator (A \<times> B) (x, y) *\<^sub>R f x y \<partial>M2) \<partial>M1)"
    using assms by (intro Fubini_integral) (auto simp: set_integrable_def case_prod_unfold)
  also have "\<dots> = (\<integral>x\<in>A. (\<integral>y\<in>B. f x y \<partial>M2) \<partial>M1)"
    unfolding set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_cong) (auto simp: indicator_def)
  finally show ?thesis .
qed

lemma (in pair_sigma_finite) nn_integral_swap:
  assumes [measurable]: "f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
  shows "(\<integral>\<^sup>+x. f x \<partial>(M1 \<Otimes>\<^sub>M M2)) = (\<integral>\<^sup>+(y,x). f (x,y) \<partial>(M2 \<Otimes>\<^sub>M M1))"
  by (subst distr_pair_swap, subst nn_integral_distr) (auto simp: case_prod_unfold)

lemma set_integrable_bound:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
    and g :: "'a \<Rightarrow> 'c::{banach, second_countable_topology}"
  shows "set_integrable M A f \<Longrightarrow> set_borel_measurable M A g \<Longrightarrow>
           (AE x in M. x \<in> A \<longrightarrow> norm (g x) \<le> norm (f x)) \<Longrightarrow> set_integrable M A g"
  unfolding set_integrable_def
  apply (erule Bochner_Integration.integrable_bound)
   apply (simp add: set_borel_measurable_def)
  apply (erule eventually_mono)
  apply (auto simp: indicator_def)
  done

lemma set_integrableI_nonneg:
  fixes f :: "'a \<Rightarrow> real"
  assumes "set_borel_measurable M A f"
  assumes "AE x in M. x \<in> A \<longrightarrow> 0 \<le> f x" "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) < \<infinity>"
  shows "set_integrable M A f"
  unfolding set_integrable_def
proof (rule integrableI_nonneg)
  from assms show "(\<lambda>x. indicator A x *\<^sub>R f x) \<in> borel_measurable M"
    by (simp add: set_borel_measurable_def)
  from assms(2) show "AE x in M. 0 \<le> indicat_real A x *\<^sub>R f x"
    by eventually_elim (auto simp: indicator_def)
  have "(\<integral>\<^sup>+x. ennreal (indicator A x *\<^sub>R f x) \<partial>M) = (\<integral>\<^sup>+x\<in>A. f x \<partial>M)"
    by (intro nn_integral_cong) (auto simp: indicator_def)
  also have "\<dots> < \<infinity>" by fact
  finally show "(\<integral>\<^sup>+x. ennreal (indicator A x *\<^sub>R f x) \<partial>M) < \<infinity>" .
qed

lemma set_integral_eq_nn_integral:
  assumes "set_borel_measurable M A f"
  assumes "set_nn_integral M A f = ennreal x" "x \<ge> 0"
  assumes "AE x in M. x \<in> A \<longrightarrow> f x \<ge> 0"
  shows   "set_integrable M A f"
    and   "set_lebesgue_integral M A f = x"
proof -
  have eq: "(\<lambda>x. (if x \<in> A then 1 else 0) * f x) = (\<lambda>x. if x \<in> A then f x else 0)"
           "(\<lambda>x. if x \<in> A then ennreal (f x) else 0) =
              (\<lambda>x. ennreal (f x) * (if x \<in> A then 1 else 0))"
           "(\<lambda>x. ennreal (f x * (if x \<in> A then 1 else 0))) =
              (\<lambda>x. ennreal (f x) * (if x \<in> A then 1 else 0))"
    by auto
  from assms show *: "set_integrable M A f"
    by (intro set_integrableI_nonneg) auto

  have "set_lebesgue_integral M A f = enn2real (set_nn_integral M A f)"
    unfolding set_lebesgue_integral_def using assms(1,4) * eq
    by (subst integral_eq_nn_integral)
       (auto intro!: nn_integral_cong simp: indicator_def set_integrable_def mult_ac)
  also have "\<dots> = x" using assms by simp
  finally show "set_lebesgue_integral M A f = x" .
qed

lemma set_integral_0 [simp, intro]: "set_integrable M A (\<lambda>y. 0)"
  by (simp add: set_integrable_def)

lemma set_integrable_sum:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "finite B"
  assumes "\<And>x. x \<in> B \<Longrightarrow> set_integrable M A (f x)"
  shows "set_integrable M A (\<lambda>y. \<Sum>x\<in>B. f x y)"
  using assms by (induction rule: finite_induct) (auto intro!: set_integral_add)

lemma set_integral_sum:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "finite B"
  assumes "\<And>x. x \<in> B \<Longrightarrow> set_integrable M A (f x)"
  shows "set_lebesgue_integral M A (\<lambda>y. \<Sum>x\<in>B. f x y) = (\<Sum>x\<in>B. set_lebesgue_integral M A (f x))"
  using assms
  apply (induction rule: finite_induct)
  apply simp
  apply simp
  apply (subst set_integral_add)
    apply (auto intro!: set_integrable_sum)
  done

lemma set_nn_integral_cong:
  assumes "M = M'" "A = B" "\<And>x. x \<in> space M \<inter> A \<Longrightarrow> f x = g x"
  shows   "set_nn_integral M A f = set_nn_integral M' B g"
  using assms unfolding assms(1,2) by (intro nn_integral_cong) (auto simp: indicator_def)

lemma set_nn_integral_mono:
  assumes "\<And>x. x \<in> space M \<inter> A \<Longrightarrow> f x \<le> g x"
  shows   "set_nn_integral M A f \<le> set_nn_integral M A g"
  using assms by (intro nn_integral_mono) (auto simp: indicator_def)

lemma
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b"
  assumes deriv: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (F has_field_derivative f x) (at x within {a..b})"
  assumes cont: "continuous_on {a..b} f"
  shows has_bochner_integral_FTC_Icc_real:
      "has_bochner_integral lborel (\<lambda>x. f x * indicator {a .. b} x) (F b - F a)" (is ?has)
    and integral_FTC_Icc_real: "(\<integral>x. f x * indicator {a .. b} x \<partial>lborel) = F b - F a" (is ?eq)
proof -
  have 1: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (F has_vector_derivative f x) (at x within {a .. b})"
    unfolding has_field_derivative_iff_has_vector_derivative[symmetric]
    using deriv by auto
  show ?has ?eq
    using has_bochner_integral_FTC_Icc[OF \<open>a \<le> b\<close> 1 cont] integral_FTC_Icc[OF \<open>a \<le> b\<close> 1 cont]
    by (auto simp: mult.commute)
qed

lemma integral_by_parts_integrable:
  fixes f g F G::"real \<Rightarrow> real"
  assumes "a \<le> b"
  assumes cont_f[intro]: "continuous_on {a..b} f"
  assumes cont_g[intro]: "continuous_on {a..b} g"
  assumes [intro]: "\<And>x. x \<in> {a..b} \<Longrightarrow> (F has_field_derivative f x) (at x within {a..b})"
  assumes [intro]: "\<And>x. x \<in> {a..b} \<Longrightarrow> (G has_field_derivative g x) (at x within {a..b})"
  shows  "integrable lborel (\<lambda>x.((F x) * (g x) + (f x) * (G x)) * indicator {a .. b} x)"
proof -
  have "integrable lborel (\<lambda>x. indicator {a..b} x *\<^sub>R ((F x) * (g x) + (f x) * (G x)))"
    by (intro borel_integrable_compact continuous_intros assms)
       (auto intro!: DERIV_continuous_on assms)
  thus ?thesis by (simp add: mult_ac)
qed

lemma integral_by_parts:
  fixes f g F G::"real \<Rightarrow> real"
  assumes [arith]: "a \<le> b"
  assumes cont_f[intro]: "continuous_on {a..b} f"
  assumes cont_g[intro]: "continuous_on {a..b} g"
  assumes [intro]: "\<And>x. x \<in> {a..b} \<Longrightarrow> (F has_field_derivative f x) (at x within {a..b})"
  assumes [intro]: "\<And>x. x \<in> {a..b} \<Longrightarrow> (G has_field_derivative g x) (at x within {a..b})"
  shows "(\<integral>x. (F x * g x) * indicator {a .. b} x \<partial>lborel)
            =  F b * G b - F a * G a - \<integral>x. (f x * G x) * indicator {a .. b} x \<partial>lborel"
proof-
  have 0: "(\<integral>x. (F x * g x + f x * G x) * indicator {a .. b} x \<partial>lborel) = F b * G b - F a * G a"
    by (rule integral_FTC_Icc_real, auto intro!: derivative_eq_intros continuous_intros)
       (auto intro!: assms DERIV_continuous_on)
  have [continuous_intros]: "continuous_on {a..b} F"
    by (rule DERIV_continuous_on assms)+
  have [continuous_intros]: "continuous_on {a..b} G"
    by (rule DERIV_continuous_on assms)+

  have "(\<integral>x. indicator {a..b} x *\<^sub>R (F x * g x + f x * G x) \<partial>lborel) =
    (\<integral>x. indicator {a..b} x *\<^sub>R(F x * g x) \<partial>lborel) + \<integral>x. indicator {a..b} x *\<^sub>R (f x * G x) \<partial>lborel"
    apply (subst Bochner_Integration.integral_add[symmetric])
      apply (rule borel_integrable_compact; force intro!: continuous_intros assms)
     apply (rule borel_integrable_compact; force intro!: continuous_intros assms)
    apply (simp add: algebra_simps)
    done

  thus ?thesis using 0 by (simp add: algebra_simps)
qed

lemma interval_lebesgue_integral_by_parts:
  assumes "a \<le> b"
  assumes cont_f[intro]: "continuous_on {a..b} f"
  assumes cont_g[intro]: "continuous_on {a..b} g"
  assumes [intro]: "\<And>x. x \<in> {a..b} \<Longrightarrow> (F has_field_derivative f x) (at x within {a..b})"
  assumes [intro]: "\<And>x. x \<in> {a..b} \<Longrightarrow> (G has_field_derivative g x) (at x within {a..b})"
  shows "(LBINT x=a..b. F x * g x) = F b * G b - F a * G a - (LBINT x=a..b. f x * G x)"
  using integral_by_parts[of a b f g F G] assms
  by (simp add: interval_integral_Icc set_lebesgue_integral_def mult_ac)

lemma interval_lebesgue_integral_by_parts_01:
  assumes cont_f[intro]: "continuous_on {0..1} f"
  assumes cont_g[intro]: "continuous_on {0..1} g"
  assumes [intro]: "\<And>x. x \<in> {0..1} \<Longrightarrow> (F has_field_derivative f x) (at x within {0..1})"
  assumes [intro]: "\<And>x. x \<in> {0..1} \<Longrightarrow> (G has_field_derivative g x) (at x within {0..1})"
  shows "(LBINT x=0..1. F x * g x) = F 1 * G 1 - F 0 * G 0 - (LBINT x=0..1. f x * G x)"
  using interval_lebesgue_integral_by_parts[of 0 1 f g F G] assms
  by (simp add: zero_ereal_def one_ereal_def)

lemma continuous_on_imp_set_integrable_cbox:
  fixes h :: "'a :: euclidean_space \<Rightarrow> real"
  assumes "continuous_on (cbox a b) h"
  shows   "set_integrable lborel (cbox a b) h"
proof -
  from assms have "h absolutely_integrable_on cbox a b"
    by (rule absolutely_integrable_continuous)
  moreover have "(\<lambda>x. indicat_real (cbox a b) x *\<^sub>R h x) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_on_indicator) (use assms in auto)
  ultimately show ?thesis
    unfolding set_integrable_def using assms by (subst (asm) integrable_completion) auto
qed


subsection \<open>Shifted Legendre polynomials\<close>

text \<open>
  The first ingredient we need to show Apéry's theorem is the \<^emph>\<open>shifted
  Legendre polynomials\<close>
    \[P_n(X) = \frac{1}{n!} \frac{\partial^n}{\partial X^n} (X^n(1-X)^n)\]
  and the auxiliary polynomials
    \[Q_{n,k}(X) = \frac{\partial^k}{\partial X^k} (X^n(1-X)^n)\ .\]
  Note that $P_n$ is in fact an \emph{integer} polynomial.

  Only some very basic properties of these will be proven, since that is all we will need.
\<close>

context
  fixes n :: nat
begin

definition gen_shleg_poly :: "nat \<Rightarrow> int poly" where
  "gen_shleg_poly k = (pderiv ^^ k) ([:0, 1, -1:] ^ n)"

definition shleg_poly where "shleg_poly = gen_shleg_poly n div [:fact n:]"

text \<open>
  We can easily prove the following more explicit formula for $Q_{n,k}$:
  \[Q_{n,k}(X) = \sum_{i=0}^k (-1)^{k-1} {k \choose i}
      n^{\underline{i}}\, n^{\underline{k-i}}\, X^{n-i}\, (1-X)^{n-k+i}\]
\<close>
lemma gen_shleg_poly_altdef:
  assumes "k \<le> n"
  shows "gen_shleg_poly k =
            (\<Sum>i\<le>k. smult ((-1)^(k-i) * of_nat (k choose i) *
                    pochhammer (n-i+1) i * pochhammer (n-k+i+1) (k-i))
                    ([:0, 1:] ^ (n - i) * [:1, -1:] ^ (n-k+i)))"
proof -
  have *: "(pderiv ^^ i) (x \<circ>\<^sub>p [:1, -1:]) =
          smult ((-1) ^ i) ((pderiv ^^ i) x \<circ>\<^sub>p [:1, -1:])" for i and x :: "int poly"
    by (induction i arbitrary: x)
       (auto simp: pderiv_smult pderiv_pcompose funpow_Suc_right pderiv_pCons
                   higher_pderiv_minus simp del: funpow.simps(2))

  have "gen_shleg_poly k = (pderiv ^^ k) ([:0, 1, -1:] ^ n)"
    by (simp add: gen_shleg_poly_def)
  also have "[:0, 1, -1::int:] = [:0, 1:] * [:1, -1:]"
    by simp
  also have "\<dots> ^ n = [:0, 1:] ^ n * [:1, -1:] ^ n"
    by (simp flip: power_mult_distrib)
  also have "(pderiv ^^ k) \<dots> =
               (\<Sum>i\<le>k. smult (of_nat (k choose i)) ((pderiv ^^ i)
                 ([:0, 1:] ^ n) * (pderiv ^^ (k - i)) ([:1, -1:] ^ n)))"
    by (simp add: higher_pderiv_mult)
  also have "\<dots> = (\<Sum>i\<le>k. smult (of_nat (k choose i))
                    ((pderiv ^^ i) (monom 1 n) * (pderiv ^^ (k - i)) (monom 1 n \<circ>\<^sub>p [:1, -1:])))"
    by (simp add: monom_altdef pcompose_pCons pcompose_power_left)
  also have "\<dots> = (\<Sum>i\<le>k. smult ((-1) ^ (k - i) * of_nat (k choose i))
                   ((pderiv ^^ i) (monom 1 n) * ((pderiv ^^ (k - i)) (monom 1 n) \<circ>\<^sub>p [:1, -1:])))"
    by (simp add: * mult_ac)
  also have "\<dots> = (\<Sum>i\<le>k. smult ((-1) ^ (k - i) * of_nat (k choose i))
                   (monom (pochhammer (n - i + 1) i) (n - i) *
                    monom (pochhammer (n - k + i + 1) (k - i)) (n - k + i) \<circ>\<^sub>p [:1, -1:]))"
    using assms by (simp add: higher_pderiv_monom)
  also have "\<dots> = (\<Sum>i\<le>k. smult ((-1) ^ (k - i) * of_nat (k choose i) * pochhammer (n - i + 1) i * pochhammer (n - k + i + 1) (k - i))
                   ([:0, 1:] ^ (n - i) * [:1, -1:] ^ (n - k + i)))"
    by (simp add: monom_altdef algebra_simps pcompose_smult pcompose_power_left pcompose_pCons)
  finally show ?thesis .
qed

lemma degree_gen_shleg_poly [simp]: "degree (gen_shleg_poly k) = 2 * n - k"
  by (simp add: gen_shleg_poly_def degree_higher_pderiv degree_power_eq)

lemma gen_shleg_poly_n: "gen_shleg_poly n = smult (fact n) shleg_poly"
proof -
  obtain r where r: "gen_shleg_poly n = [:fact n:] * r"
    unfolding gen_shleg_poly_def using fact_dvd_higher_pderiv[of n "[:0,1,-1:]^n"] by blast
  have "smult (fact n) shleg_poly = smult (fact n) (gen_shleg_poly n div [:fact n:])"
    by (simp add: shleg_poly_def)
  also note r
  also have "[:fact n:] * r div [:fact n:] = r"
    by (rule nonzero_mult_div_cancel_left) auto
  finally show ?thesis
    by (simp add: r)
qed

lemma degree_shleg_poly [simp]: "degree shleg_poly = n"
  using degree_gen_shleg_poly[of n] by (simp add: gen_shleg_poly_n)

lemma pderiv_gen_shleg_poly [simp]: "pderiv (gen_shleg_poly k) = gen_shleg_poly (Suc k)"
  by (simp add: gen_shleg_poly_def)


text \<open>
  The following functions are the interpretation of the shifted Legendre polynomials
  and the auxiliary polynomials as a function from reals to reals.
\<close>
definition Gen_Shleg :: "nat \<Rightarrow> real \<Rightarrow> real"
  where "Gen_Shleg k x = poly (of_int_poly (gen_shleg_poly k)) x"

definition Shleg :: "real \<Rightarrow> real" where "Shleg = poly (of_int_poly shleg_poly)"

lemma Gen_Shleg_altdef:
  assumes "k \<le> n"
  shows   "Gen_Shleg k x = (\<Sum>i\<le>k. (-1)^(k-i) * of_nat (k choose i) *
                            of_int (pochhammer (n-i+1) i * pochhammer (n-k+i+1) (k-i)) *
                            x ^ (n - i) * (1 - x) ^ (n-k+i))"
  using assms by (simp add: Gen_Shleg_def gen_shleg_poly_altdef poly_sum mult_ac)

lemma Gen_Shleg_0 [simp]: "k < n \<Longrightarrow> Gen_Shleg k 0 = 0"
  by (simp add: Gen_Shleg_altdef zero_power)

lemma Gen_Shleg_1 [simp]: "k < n \<Longrightarrow> Gen_Shleg k 1 = 0"
  by (simp add: Gen_Shleg_altdef zero_power)

lemma Gen_Shleg_n_0 [simp]: "Gen_Shleg n 0 = fact n"
proof -
  have "Gen_Shleg n 0 = (\<Sum>i\<le>n. (-1) ^ (n-i) * real (n choose i) *
        (real (pochhammer (Suc (n-i)) i) *
         real (pochhammer (Suc i) (n-i))) * 0 ^ (n - i))"
    by (simp add: Gen_Shleg_altdef)
  also have "\<dots> = (\<Sum>i\<in>{n}. (-1) ^ (n-i) * real (n choose i) *
        (real (pochhammer (Suc (n-i)) i) *
         real (pochhammer (Suc i) (n-i))) * 0 ^ (n - i))"
    by (intro sum.mono_neutral_right) auto
  also have "\<dots> = fact n"
    by (simp add: pochhammer_fact flip: pochhammer_of_nat)
  finally show ?thesis .
qed

lemma Gen_Shleg_n_1 [simp]: "Gen_Shleg n 1 = (-1) ^ n * fact n"
proof -
  have "Gen_Shleg n 1 = (\<Sum>i\<le>n. (-1) ^ (n-i) * real (n choose i) *
        (real (pochhammer (Suc (n-i)) i) *
         real (pochhammer (Suc i) (n-i))) * 0 ^ i)"
    by (simp add: Gen_Shleg_altdef)
  also have "\<dots> = (\<Sum>i\<in>{0}. (-1) ^ (n-i) * real (n choose i) *
        (real (pochhammer (Suc (n-i)) i) *
         real (pochhammer (Suc i) (n-i))) * 0 ^ i)"
    by (intro sum.mono_neutral_right) auto
  also have "\<dots> = (-1) ^ n * fact n"
    by (simp add: pochhammer_fact flip: pochhammer_of_nat)
  finally show ?thesis .
qed

lemma Shleg_altdef: "Shleg x = Gen_Shleg n x / fact n"
  by (simp add: Shleg_def Gen_Shleg_def gen_shleg_poly_n)

lemma Shleg_0 [simp]: "Shleg 0 = 1" and Shleg_1 [simp]: "Shleg 1 = (-1) ^ n"
  by (simp_all add: Shleg_altdef)

lemma Gen_Shleg_0_left: "Gen_Shleg 0 x = x ^ n * (1 - x) ^ n"
  by (simp add: Gen_Shleg_def gen_shleg_poly_def power_mult_distrib)

lemma has_field_derivative_Gen_Shleg:
  "(Gen_Shleg k has_field_derivative Gen_Shleg (Suc k) x) (at x)"
proof -
  note [derivative_intros] = poly_DERIV
  show ?thesis unfolding Gen_Shleg_def
    by (rule derivative_eq_intros) auto
qed

lemma continuous_on_Gen_Shleg: "continuous_on A (Gen_Shleg k)"
  by (auto simp: Gen_Shleg_def intro!: continuous_intros)

lemma continuous_on_Gen_Shleg' [continuous_intros]:
  "continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>x. Gen_Shleg k (f x))"
  by (rule continuous_on_compose2[OF continuous_on_Gen_Shleg[of UNIV]]) auto

lemma continuous_on_Shleg: "continuous_on A Shleg"
  by (auto simp: Shleg_def intro!: continuous_intros)

lemma continuous_on_Shleg' [continuous_intros]:
  "continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>x. Shleg (f x))"
  by (rule continuous_on_compose2[OF continuous_on_Shleg[of UNIV]]) auto

lemma measurable_Gen_Shleg [measurable]: "Gen_Shleg n \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_on_Gen_Shleg)

lemma measurable_Shleg [measurable]: "Shleg \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_on_Shleg)

end


subsection \<open>Auxiliary facts about the \<open>\<zeta>\<close> function\<close>

lemma Re_zeta_ge_1:
  assumes "x > 1"
  shows   "Re (zeta (of_real x)) \<ge> 1"
proof -
  have *: "(\<lambda>n. real (Suc n) powr -x) sums Re (zeta (complex_of_real x))"
    using sums_Re[OF sums_zeta[of "of_real x"]] assms by (simp add: powr_Reals_eq)
  show "Re (zeta (of_real x)) \<ge> 1"
  proof (rule sums_le[OF _ _ *])
    show "(\<lambda>n. if n = 0 then 1 else 0) sums 1"
      by (rule sums_single)
  qed auto
qed

lemma sums_zeta_of_nat_offset:
  fixes r :: nat
  assumes n: "n > 1"
  shows "(\<lambda>k. 1 / (r + k + 1) ^ n) sums (zeta (of_nat n) - (\<Sum>k=1..r. 1 / k ^ n))"
proof -
  have "(\<lambda>k. 1 / (k + 1) ^ n) sums zeta (of_nat n)"
    using sums_zeta[of "of_nat n"] n
    by (simp add: powr_minus field_simps flip: of_nat_Suc)
  from sums_split_initial_segment[OF this, of r]
  have "(\<lambda>k. 1 / (r + k + 1) ^ n) sums (zeta (of_nat n) - (\<Sum>k<r. 1 / Suc k ^ n))"
    by (simp add: algebra_simps)
  also have "(\<Sum>k<r. 1 / Suc k ^ n) = (\<Sum>k=1..r. 1 / k ^ n)"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>k. k - 1" Suc]) auto
  finally show ?thesis .
qed

lemma sums_Re_zeta_of_nat_offset:
  fixes r :: nat
  assumes n: "n > 1"
  shows "(\<lambda>k. 1 / (r + k + 1) ^ n) sums (Re (zeta (of_nat n)) - (\<Sum>k=1..r. 1 / k ^ n))"
proof -
  have "(\<lambda>k. Re (1 / (r + k + 1) ^ n)) sums (Re (zeta (of_nat n) - (\<Sum>k=1..r. 1 / k ^ n)))"
    by (intro sums_Re sums_zeta_of_nat_offset assms)
  thus ?thesis by simp
qed


subsection \<open>Divisor of a sum of rationals\<close>

text \<open>
  A finite sum of rationals of the form $\frac{a_1}{b_1} + \ldots + \frac{a_n}{b_n}$
  can be brought into the form $\frac{c}{d}$, where $d$ is the LCM of the $b_i$ (or
  some integer multiple thereof).
\<close>
lemma sum_rationals_common_divisor:
  fixes f g :: "'a \<Rightarrow> int"
  assumes "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> g x \<noteq> 0"
  shows   "\<exists>c. (\<Sum>x\<in>A. f x / g x) = real_of_int c / (LCM x\<in>A. g x)"
  using assms
proof (induction rule: finite_induct)
  case empty
  thus ?case by auto
next
  case (insert x A)
  define d where "d = (LCM x\<in>A. g x)"
  from insert have [simp]: "d \<noteq> 0"
    by (auto simp: d_def Lcm_0_iff)
  from insert have [simp]: "g x \<noteq> 0" by auto
  from insert obtain c where c: "(\<Sum>x\<in>A. f x / g x) = real_of_int c / real_of_int d"
    by (auto simp: d_def)
  define e1 where "e1 = lcm d (g x) div d"
  define e2 where "e2 = lcm d (g x) div g x"
  have "(\<Sum>y\<in>insert x A. f y / g y) = c / d + f x / g x"
    using insert c by simp
  also have "c / d = (c * e1) / lcm d (g x)"
    by (simp add: e1_def real_of_int_div)
  also have "f x / g x = (f x * e2) / lcm d (g x)"
    by (simp add: e2_def real_of_int_div)
  also have "(c * e1) / lcm d (g x) + \<dots> = (c * e1 + f x * e2) / (LCM x\<in>insert x A. g x)"
    using insert by (simp add: add_divide_distrib lcm.commute d_def)
  finally show ?case ..
qed

lemma sum_rationals_common_divisor':
  fixes f g :: "'a \<Rightarrow> int"
  assumes "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> g x \<noteq> 0" and "(\<And>x. x \<in> A \<Longrightarrow> g x dvd d)" and "d \<noteq> 0"
  shows   "\<exists>c. (\<Sum>x\<in>A. f x / g x) = real_of_int c / real_of_int d"
proof -
  define d' where "d' = (LCM x\<in>A. g x)"
  have "d' dvd d"
    unfolding d'_def using assms(3) by (auto simp: Lcm_dvd_iff)
  then obtain e where e: "d = d' * e" by blast
  have "\<exists>c. (\<Sum>x\<in>A. f x / g x) = real_of_int c / (LCM x\<in>A. g x)"
    by (rule sum_rationals_common_divisor) fact+
  then obtain c where c: "(\<Sum>x\<in>A. f x / g x) = real_of_int c / real_of_int d'"
    unfolding d'_def ..
  also have "\<dots> = real_of_int (c * e) / real_of_int d"
    using \<open>d \<noteq> 0\<close> by (simp add: e)
  finally show ?thesis ..
qed


subsection \<open>The first double integral\<close>

text \<open>
  We shall now investigate the double integral
  \[I_1 := \int_0^1 \int_0^1 -\frac{\ln(xy)}{1-xy}\,x^r y^s\, \text{d}x\,\text{d}y\ .\]
  Since everything is non-negative for now, we can work over the extended non-negative
  real numbers and the issues of integrability or summability do not arise at all.
\<close>

definition beukers_nn_integral1 :: "nat \<Rightarrow> nat \<Rightarrow> ennreal" where
  "beukers_nn_integral1 r s =
     (\<integral>\<^sup>+(x,y)\<in>{0<..<1}\<times>{0<..<1}. ennreal (-ln (x*y) / (1 - x*y) * x^r * y^s) \<partial>lborel)"

definition beukers_integral1 :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "beukers_integral1 r s = (\<integral>(x,y)\<in>{0<..<1}\<times>{0<..<1}. (-ln (x*y) / (1 - x*y) * x^r * y^s) \<partial>lborel)"

lemma
  fixes x y z :: real
  assumes xyz: "x \<in> {0<..<1}" "y \<in> {0<..<1}" "z \<in> {0..1}"
  shows beukers_denom_ineq: "(1 - x * y) * z < 1" and beukers_denom_neq: "(1 - x * y) * z \<noteq> 1"
proof -
  from xyz have *: "x * y < 1 * 1"
    by (intro mult_strict_mono) auto
  from * have "(1 - x * y) * z \<le> (1 - x * y) * 1"
    using xyz by (intro mult_left_mono) auto
  also have "\<dots> < 1 * 1"
    using xyz by (intro mult_strict_right_mono) auto
  finally show "(1 - x * y) * z < 1" "(1 - x * y) * z \<noteq> 1" by simp_all
qed

text \<open>
  We first evaluate the improper integral
    \[\int_0^1 -\ln x \cdot x^e\,\text{d}x = \frac{1}{(e+1)^2}\ .\]
  for any $e>-1$.
\<close>
lemma integral_0_1_ln_times_powr:
  assumes "e > -1"
  shows   "(LBINT x=0..1. -ln x * x powr e) = 1 / (e + 1)\<^sup>2"
    and   "interval_lebesgue_integrable lborel 0 1 (\<lambda>x. -ln x * x powr e)"
proof -
  define f where "f = (\<lambda>x. -ln x * x powr e)"
  define F where "F = (\<lambda>x. x powr (e + 1) * (1 - (e + 1) * ln x) / (e + 1) ^ 2)"

  have 0: "isCont f x" if "x \<in> {0<..<1}" for x
    using that by (auto intro!: continuous_intros simp: f_def)
  have 1: "(F has_real_derivative f x) (at x)" if "x \<in> {0<..<1}" for x
  proof -
    show "(F has_real_derivative f x) (at x)"
      unfolding F_def f_def using that assms
      apply (insert that assms)
      apply (rule derivative_eq_intros refl | simp)+
      apply (simp add: divide_simps)
      apply (simp add: power2_eq_square algebra_simps powr_add power_numeral_reduce)
      done
  qed
  have 2: "AE x in lborel. ereal 0 < ereal x \<longrightarrow> ereal x < ereal 1 \<longrightarrow> 0 \<le> f x"
    by (intro AE_I2) (auto simp: f_def mult_nonpos_nonneg)
  have 3: "((F \<circ> real_of_ereal) \<longlongrightarrow> 0) (at_right (ereal 0))"
    unfolding ereal_tendsto_simps F_def using assms by real_asymp
  have 4: "((F \<circ> real_of_ereal) \<longlongrightarrow> F 1) (at_left (ereal 1))"
    unfolding ereal_tendsto_simps F_def
    using assms by real_asymp (simp add: field_simps)

  have "(LBINT x=ereal 0..ereal 1. f x) = F 1 - 0"
    by (rule interval_integral_FTC_nonneg[where F = F])
       (use 0 1 2 3 4 in auto)
  thus "(LBINT x=0..1. -ln x * x powr e) = 1 / (e + 1)\<^sup>2"
    by (simp add: F_def zero_ereal_def one_ereal_def f_def)
  have "set_integrable lborel (einterval (ereal 0) (ereal 1)) f"
    by (rule interval_integral_FTC_nonneg)
       (use 0 1 2 3 4 in auto)
  thus "interval_lebesgue_integrable lborel 0 1 f"
    by (simp add: interval_lebesgue_integrable_def einterval_def)
qed

lemma interval_lebesgue_integral_lborel_01_cong:
  assumes "\<And>x. x \<in> {0<..<1} \<Longrightarrow> f x = g x"
  shows   "interval_lebesgue_integral lborel 0 1 f =
           interval_lebesgue_integral lborel 0 1 g"
  using assms
  by (subst (1 2) interval_integral_Ioo)
     (auto intro!: set_lebesgue_integral_cong assms)

lemma nn_integral_0_1_ln_times_powr:
  assumes "e > -1"
  shows    "(\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln y * y powr e) \<partial>lborel) = ennreal (1 / (e + 1)\<^sup>2)"
proof -
  have *: "(LBINT x=0..1. - ln x * x powr e = 1 / (e + 1)\<^sup>2)"
          "interval_lebesgue_integrable lborel 0 1 (\<lambda>x. - ln x * x powr e)"
    using integral_0_1_ln_times_powr[OF assms] by simp_all
  have eq: "(\<lambda>y. (if 0 < y \<and> y < 1 then 1 else 0) * ln y * y powr e) =
            (\<lambda>y. if 0 < y \<and> y < 1 then ln y * y powr e else 0)"
    by auto

  have "(\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln y * y powr e) \<partial>lborel) =
           (\<integral>\<^sup>+y. ennreal (-ln y * y powr e * indicator {0<..<1} y) \<partial>lborel)"
    by (intro nn_integral_cong) (auto simp: indicator_def)
  also have "\<dots> = ennreal (1 / (e + 1)\<^sup>2)"
    using * eq
    by (subst nn_integral_eq_integral)
       (auto intro!: AE_I2 simp: indicator_def interval_lebesgue_integrable_def
               set_integrable_def one_ereal_def zero_ereal_def interval_integral_Ioo
                mult_ac mult_nonpos_nonneg set_lebesgue_integral_def)
  finally show ?thesis .
qed

lemma nn_integral_0_1_ln_times_power:
  "(\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln y * y ^ n) \<partial>lborel) = ennreal (1 / (n + 1)\<^sup>2)"
proof -
  have "(\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln y * y ^ n) \<partial>lborel) =
          (\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln y * y powr real n) \<partial>lborel)"
    by (intro set_nn_integral_cong) (auto simp: powr_realpow)
  also have "\<dots> = ennreal (1 / (n + 1)^2)"
    by (subst nn_integral_0_1_ln_times_powr) auto
  finally show ?thesis by simp
qed

text \<open>
  Next, we also evaluate the more trivial integral
    \[\int_0^1 x^n\ \text{d}x\ .\]
\<close>
lemma nn_integral_0_1_power:
  "(\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (y ^ n) \<partial>lborel) = ennreal (1 / (n + 1))"
proof -
  have *: "((\<lambda>a. a ^ (n + 1) / real (n + 1)) has_real_derivative x ^ n) (at x)" for x
    by (rule derivative_eq_intros refl | simp)+
  have "(\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (y ^ n) \<partial>lborel) = (\<integral>\<^sup>+y\<in>{0..1}. ennreal (y ^ n) \<partial>lborel)"
    by (intro nn_integral_cong_AE AE_I[of _ _ "{0,1}"])
       (auto simp: indicator_def emeasure_lborel_countable)
  also have "\<dots> = ennreal (1 ^ (n + 1) / (n + 1) - 0 ^ (n + 1) / (n + 1))"
    using * by (intro nn_integral_FTC_Icc) auto
  also have "\<dots> = ennreal (1 / (n + 1))"
    by simp
  finally show ?thesis by simp
qed

text \<open>
  $I_1$ can alternatively be written as the triple integral
    \[\int_0^1\int_0^1\int_0^1
        \frac{x^r y^s}{1-(1-xy)w}\ \text{d}x\,\text{d}y\,\text{d}w\ .\]
\<close>
lemma beukers_nn_integral1_altdef:
  "beukers_nn_integral1 r s =
     (\<integral>\<^sup>+(w,x,y)\<in>{0<..<1}\<times>{0<..<1}\<times>{0<..<1}.
       ennreal (1 / (1-(1-x*y)*w) * x^r * y^s) \<partial>lborel)"
proof -
  have "(\<integral>\<^sup>+(w,x,y)\<in>{0<..<1}\<times>{0<..<1}\<times>{0<..<1}.
           ennreal (1 / (1-(1-x*y)*w) * x^r * y^s) \<partial>lborel) =
        (\<integral>\<^sup>+(x,y)\<in>{0<..<1}\<times>{0<..<1}. (\<integral>\<^sup>+w\<in>{0<..<1}.
           ennreal (1 / (1-(1-x*y)*w) * x^r * y^s) \<partial>lborel) \<partial>lborel)"
    by (subst lborel_prod [symmetric], subst lborel_pair.nn_integral_snd [symmetric])
       (auto simp: case_prod_unfold indicator_def simp flip: lborel_prod intro!: nn_integral_cong)
  also have "\<dots> = (\<integral>\<^sup>+(x,y)\<in>{0<..<1}\<times>{0<..<1}. ennreal (-ln (x*y)/(1-x*y) * x^r * y^s) \<partial>lborel)"
  proof (intro nn_integral_cong, clarify)
    fix x y :: real
    have "(\<integral>\<^sup>+w\<in>{0<..<1}. ennreal (1/(1-(1-x*y)*w)*x^r*y^s) \<partial>lborel) =
             ennreal (-ln (x*y)*x^r*y^s/(1-x*y))"
      if xy: "(x, y) \<in> {0<..<1} \<times> {0<..<1}"
    proof -
      from xy have "x * y < 1"
        using mult_strict_mono[of x 1 y 1] by simp
      have deriv: "((\<lambda>w. -ln (1-(1-x*y)*w) / (1-x*y)) has_real_derivative
              1/(1-(1-x*y)*w)) (at w)" if w: "w \<in> {0..1}" for w
        by (insert xy w \<open>x*y<1\<close> beukers_denom_ineq[of x y w])
           (rule derivative_eq_intros refl | simp add: divide_simps)+
      have "(\<integral>\<^sup>+w\<in>{0<..<1}. ennreal (1/(1-(1-x*y)*w)*x^r*y^s) \<partial>lborel) =
              ennreal (x^r*y^s) * (\<integral>\<^sup>+w\<in>{0<..<1}. ennreal (1/(1-(1-x*y)*w)) \<partial>lborel)"
        using xy by (subst nn_integral_cmult [symmetric])
                    (auto intro!: nn_integral_cong simp: indicator_def simp flip: ennreal_mult')
      also have "(\<integral>\<^sup>+w\<in>{0<..<1}. ennreal (1/(1-(1-x*y)*w)) \<partial>lborel) =
                 (\<integral>\<^sup>+w\<in>{0..1}. ennreal (1/(1-(1-x*y)*w)) \<partial>lborel)"
        by (intro nn_integral_cong_AE AE_I[of _ _ "{0,1}"])
           (auto simp: emeasure_lborel_countable indicator_def)
      also have "(\<integral>\<^sup>+w\<in>{0..1}. ennreal (1/(1-(1-x*y)*w)) \<partial>lborel) =
                   ennreal (-ln (1-(1-x*y)*1)/(1-x*y) - (-ln (1-(1-x*y)*0)/(1-x*y)))"
        using xy deriv less_imp_le[OF beukers_denom_ineq[of x y]]
        by (intro nn_integral_FTC_Icc) auto
      finally show ?thesis using xy
        by (simp flip: ennreal_mult' ennreal_mult'' add: mult_ac)
    qed
    thus "(\<integral>\<^sup>+w\<in>{0<..<1}. ennreal (1/(1-(1-x*y)*w)*x^r*y^s) \<partial>lborel) * indicator ({0<..<1}\<times>{0<..<1}) (x, y) =
           ennreal (-ln (x*y)/(1-x*y)*x^r*y^s) * indicator ({0<..<1}\<times>{0<..<1}) (x, y)"
      by (auto simp: indicator_def)
  qed
  also have "\<dots> = beukers_nn_integral1 r s"
    by (simp add: beukers_nn_integral1_def)
  finally show ?thesis ..
qed

context
  fixes r s :: nat and I1 I2' :: real and I2 :: ennreal and D :: "(real \<times> real \<times> real) set"
  assumes rs: "s \<le> r"
  defines "D \<equiv> {0<..<1}\<times>{0<..<1}\<times>{0<..<1}"
begin

text \<open>
  By unfolding the geometric series, pulling the summation out and evaluating the integrals,
  we find that
    \[I_1 = \sum_{k=0}^\infty \frac{1}{(k+r+1)^2(k+s+1)} + \frac{1}{(k+r+1)(k+s+1)^2}\ .\]
\<close>
lemma beukers_nn_integral1_series:
  "beukers_nn_integral1 r s = (\<Sum>k. ennreal (1/((k+r+1)^2*(k+s+1)) + 1/((k+r+1)*(k+s+1)^2)))"
proof -
  have "beukers_nn_integral1 r s =
          (\<integral>\<^sup>+(x,y)\<in>{0<..<1}\<times>{0<..<1}. (\<Sum>k. ennreal (-ln (x*y) * x^(k+r) * y^(k+s))) \<partial>lborel)"
    unfolding beukers_nn_integral1_def
  proof (intro set_nn_integral_cong refl, clarify)
    fix x y :: real assume xy: "x \<in> {0<..<1}" "y \<in> {0<..<1}"
    from xy have "x * y < 1" using mult_strict_mono[of x 1 y 1] by simp
    have "(\<Sum>k. ennreal (-ln (x*y) * x^(k+r) * y^(k+s))) =
             ennreal (-ln (x*y) * x^r * y^s) * (\<Sum>k. ennreal ((x*y)^k))"
      using xy by (subst ennreal_suminf_cmult [symmetric], subst ennreal_mult'' [symmetric])
                  (auto simp: power_add mult_ac power_mult_distrib)
    also have "(\<Sum>k. ennreal ((x*y)^k)) = ennreal (1 / (1 - x*y))"
      using geometric_sums[of "x*y"] \<open>x * y < 1\<close> xy by (intro suminf_ennreal_eq) auto
    also have "ennreal (-ln (x*y) * x^r * y^s) * \<dots> =
                 ennreal (-ln (x*y) / (1 - x*y) * x^r * y^s)"
      using \<open>x * y < 1\<close> by (subst ennreal_mult'' [symmetric]) auto
    finally show "ennreal (-ln (x*y) / (1 - x*y) * x^r * y^s) =
                    (\<Sum>k. ennreal (-ln (x*y) * x^(k+r) * y^(k+s)))" ..
  qed
  also have "\<dots> = (\<Sum>k. (\<integral>\<^sup>+(x,y)\<in>{0<..<1}\<times>{0<..<1}. (ennreal (-ln (x*y) * x^(k+r) * y^(k+s))) \<partial>lborel))"
    unfolding case_prod_unfold by (subst nn_integral_suminf [symmetric]) (auto simp flip: borel_prod)
  also have "\<dots> = (\<Sum>k. ennreal (1 / ((k+r+1)^2*(k+s+1)) + 1 / ((k+r+1)*(k+s+1)^2)))"
  proof (rule suminf_cong)
    fix k :: nat
    define F where "F = (\<lambda>x y::real. x + y)"
    have "(\<integral>\<^sup>+(x,y)\<in>{0<..<1}\<times>{0<..<1}. ennreal (-ln (x*y) * x^(k+r) * y^(k+s)) \<partial>lborel) =
            (\<integral>\<^sup>+x\<in>{0<..<1}. (\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln (x*y) * x^(k+r) * y^(k+s)) \<partial>lborel) \<partial>lborel)"
      unfolding case_prod_unfold lborel_prod [symmetric]
      by (subst lborel.nn_integral_fst [symmetric]) (auto intro!: nn_integral_cong simp: indicator_def)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>{0<..<1}. ennreal (-ln x * x^(k+r) / (k+s+1) + x^(k+r)/(k+s+1)^2) \<partial>lborel)"
    proof (intro set_nn_integral_cong refl, clarify)
      fix x :: real assume x: "x \<in> {0<..<1}"
      have "(\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln (x*y) * x^(k+r) * y^(k+s)) \<partial>lborel) =
              (\<integral>\<^sup>+y\<in>{0<..<1}. (ennreal (-ln x * x^(k+r) * y^(k+s)) + ennreal (-ln y * x^(k+r) * y^(k+s))) \<partial>lborel)"
        by (intro set_nn_integral_cong)
           (use x in \<open>auto simp: ln_mult ring_distribs mult_nonpos_nonneg simp flip: ennreal_plus\<close>)
      also have "\<dots> = (\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln x * x^(k+r) * y^(k+s)) \<partial>lborel) +
                      (\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln y * x^(k+r) * y^(k+s)) \<partial>lborel)"
        by (subst nn_integral_add [symmetric]) (auto intro!: nn_integral_cong simp: indicator_def)
      also have "(\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln x * x^(k+r) * y^(k+s)) \<partial>lborel) =
                 ennreal (-ln x * x^(k+r)) * (\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (y^(k+s)) \<partial>lborel)"
        by (subst nn_integral_cmult [symmetric])
           (auto intro!: nn_integral_cong simp: indicator_def simp flip: ennreal_mult'')
      also have "(\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (y^(k+s)) \<partial>lborel) = ennreal (1/(k+s+1))"
        by (subst nn_integral_0_1_power) simp
      also have "ennreal (-ln x * x^(k+r)) * \<dots> = ennreal (-ln x * x^(k+r) / (k+s+1))"
        by (subst ennreal_mult'' [symmetric]) auto
      also have "(\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln y * x^(k+r) * y^(k+s)) \<partial>lborel) =
                   ennreal (x^(k+r)) * (\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln y * y^(k+s)) \<partial>lborel)"
        by (subst nn_integral_cmult [symmetric])
           (use x in \<open>auto intro!: nn_integral_cong simp: indicator_def mult_ac simp flip: ennreal_mult'\<close>)
      also have "(\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln y * y^(k+s)) \<partial>lborel) = ennreal (1 / (k + s + 1)\<^sup>2)"
        by (subst nn_integral_0_1_ln_times_power) simp
      also have "ennreal (x ^ (k + r)) * \<dots> = ennreal (x ^ (k + r) / (k + s + 1) ^ 2)"
        by (subst ennreal_mult'' [symmetric]) auto
      also have "ennreal (- ln x * x ^ (k + r) / (k + s + 1)) + \<dots> =
                   ennreal (-ln x * x^(k+r) / (k+s+1) + x^(k+r)/(k+s+1)^2)"
        using x by (subst ennreal_plus) (auto simp: mult_nonpos_nonneg divide_nonpos_nonneg)
      finally show "(\<integral>\<^sup>+y\<in>{0<..<1}. ennreal (-ln (x*y) * x^(k+r) * y^(k+s)) \<partial>lborel) =
                      ennreal (-ln x * x^(k+r) / (k+s+1) + x^(k+r)/(k+s+1)^2)" .
    qed
    also have "\<dots> = (\<integral>\<^sup>+x\<in>{0<..<1}. (ennreal (-ln x * x^(k+r) / (k+s+1)) +
                       ennreal (x^(k+r)/(k+s+1)^2)) \<partial>lborel)"
      by (intro set_nn_integral_cong refl, subst ennreal_plus)
         (auto simp: mult_nonpos_nonneg divide_nonpos_nonneg)
    also have "\<dots> = (\<integral>\<^sup>+x\<in>{0<..<1}. ennreal (-ln x * x^(k+r) / (k+s+1)) \<partial>lborel) +
                    (\<integral>\<^sup>+x\<in>{0<..<1}. ennreal (x^(k+r)/(k+s+1)^2) \<partial>lborel)"
      by (subst nn_integral_add [symmetric]) (auto intro!: nn_integral_cong simp: indicator_def)
    also have "(\<integral>\<^sup>+x\<in>{0<..<1}. ennreal (-ln x * x^(k+r) / (k+s+1)) \<partial>lborel) =
                  ennreal (1 / (k+s+1)) * (\<integral>\<^sup>+x\<in>{0<..<1}. ennreal (-ln x * x^(k+r)) \<partial>lborel)"
      by (subst nn_integral_cmult [symmetric])
         (auto intro!: nn_integral_cong simp: indicator_def simp flip: ennreal_mult')
    also have "\<dots> = ennreal (1 / ((k+s+1) * (k+r+1)^2))"
      by (subst nn_integral_0_1_ln_times_power, subst ennreal_mult [symmetric]) (auto simp: algebra_simps)
    also have "(\<integral>\<^sup>+x\<in>{0<..<1}. ennreal (x^(k+r)/(k+s+1)^2) \<partial>lborel) =
                  ennreal (1/(k+s+1)^2) * (\<integral>\<^sup>+x\<in>{0<..<1}. ennreal (x^(k+r)) \<partial>lborel)"
      by (subst nn_integral_cmult [symmetric])
         (auto intro!: nn_integral_cong simp: indicator_def simp flip: ennreal_mult')
    also have "\<dots> = ennreal (1/((k+r+1)*(k+s+1)^2))"
      by (subst nn_integral_0_1_power, subst ennreal_mult [symmetric]) (auto simp: algebra_simps)
    also have "ennreal (1 / ((k+s+1) * (k+r+1)^2)) + \<dots> =
                 ennreal (1/((k+r+1)^2*(k+s+1)) + 1/((k+r+1)*(k+s+1)^2))"
      by (subst ennreal_plus [symmetric]) (auto simp: algebra_simps)
    finally show "(\<integral>\<^sup>+(x,y)\<in>{0<..<1}\<times>{0<..<1}. ennreal (-ln (x*y) * x^(k+r) * y^(k+s)) \<partial>lborel) = \<dots>" .
  qed
  finally show ?thesis .
qed

text \<open>
  Remembering that $\zeta(3) = \sum k^{-3}$, it is easy to see that if $r = s$, this sum is simply
    \[2\left(\zeta(3) - \sum_{k=1}^r \frac{1}{k^3}\right)\ .\]
\<close>
lemma beukers_nn_integral1_same:
  assumes "r = s"
  shows   "beukers_nn_integral1 r s = ennreal (2 * (Re (zeta 3) - (\<Sum>k=1..r. 1 / k ^ 3)))"
    and   "2 * (Re (zeta 3) - (\<Sum>k=1..r. 1 / k ^ 3)) \<ge> 0"
proof -
  from assms have [simp]: "s = r" by simp
  have *: "Suc 2 = 3" by simp
  have "beukers_nn_integral1 r s = (\<Sum>k. ennreal (2 / (r + k + 1) ^ 3))"
    unfolding beukers_nn_integral1_series
    by (simp only: assms power_Suc [symmetric] mult.commute[of "x ^ 2" for x] *
                   times_divide_eq_right mult_1_right add_ac flip: mult_2)
  also have **: "(\<lambda>k. 2 / (r + k + 1) ^ 3) sums
              (2 * (Re (zeta 3) - (\<Sum>k=1..r. 1 / k ^ 3)))"
    using sums_mult[OF sums_Re_zeta_of_nat_offset[of 3], of 2] by simp
  hence "(\<Sum>k. ennreal (2 / (r + k + 1) ^ 3)) = ennreal \<dots>"
    by (intro suminf_ennreal_eq) auto
  finally show "beukers_nn_integral1 r s = ennreal (2 * (Re (zeta 3) - (\<Sum>k=1..r. 1 / k ^ 3)))" .
  show "2 * (Re (zeta 3) - (\<Sum>k=1..r. 1 / k ^ 3)) \<ge> 0"
    by (rule sums_le[OF _ sums_zero **]) auto
qed

lemma beukers_integral1_same:
  assumes "r = s"
  shows   "beukers_integral1 r s = 2 * (Re (zeta 3) - (\<Sum>k=1..r. 1 / k ^ 3))"
proof -
  have "ln (a * b) * a ^ r * b ^ s / (1 - a * b) \<le> 0" if "a \<in> {0<..<1}" "b \<in> {0<..<1}" for a b :: real
    using that mult_strict_mono[of a 1 b 1] by (intro mult_nonpos_nonneg divide_nonpos_nonneg) auto
  thus ?thesis
    using beukers_nn_integral1_same[OF assms]
    unfolding beukers_nn_integral1_def beukers_integral1_def
    by (intro set_integral_eq_nn_integral AE_I2)
       (auto simp flip: lborel_prod simp: case_prod_unfold set_borel_measurable_def
             intro: divide_nonpos_nonneg mult_nonpos_nonneg)
qed

text \<open>
  In contrast, for \<open>r > s\<close>, we find that
    \[I_1 = \frac{1}{r-s} \sum_{k=s+1}^r \frac{1}{k^2}\ .\]
\<close>
lemma beukers_nn_integral1_different:
  assumes "r > s"
  shows   "beukers_nn_integral1 r s = ennreal ((\<Sum>k\<in>{s<..r}. 1 / k ^ 2) / (r - s))"
proof -
  have "(\<lambda>k. 1 / (r - s) * (1 / (s + k + 1) ^ 2 - 1 / (r + k + 1) ^ 2))
          sums (1 / (r - s) * ((Re (zeta (of_nat 2)) - (\<Sum>k=1..s. 1/k^2)) -
                               (Re (zeta (of_nat 2)) - (\<Sum>k=1..r. 1/k^2))))"
    (is "_ sums ?S") by (intro sums_mult sums_diff sums_Re_zeta_of_nat_offset) auto
  also have "?S = ((\<Sum>k=1..r. 1/k^2) - (\<Sum>k=1..s. 1/k^2)) / (r - s)"
    by (simp add: algebra_simps diff_divide_distrib)
  also have "(\<Sum>k=1..r. 1/k^2) - (\<Sum>k=1..s. 1/k^2) = (\<Sum>k\<in>{1..r}-{1..s}. 1/k^2)"
    using assms by (subst Groups_Big.sum_diff) auto
  also have "{1..r} - {1..s} = {s<..r}" by auto

  also have "(\<lambda>k. 1 / (r - s) * (1 / (s + k + 1) ^ 2 - 1 / (r + k + 1) ^ 2)) =
               (\<lambda>k. 1 / ((k+r+1) * (k+s+1)^2) + 1 / ((k+r+1)^2 * (k+s+1)))"
  proof (intro ext, goal_cases)
    case (1 k)
    define x where "x = real (k + r + 1)"
    define y where "y = real (k + s + 1)"
    have [simp]: "x \<noteq> 0" "y \<noteq> 0" by (auto simp: x_def y_def)
    have "(x\<^sup>2 * y + x * y\<^sup>2) * (real r - real s) = x * y * (x\<^sup>2 - y\<^sup>2)"
      by (simp add: algebra_simps power2_eq_square x_def y_def)
    hence "1 / (x*y^2) + 1 / (x^2*y) = 1 / (r - s) * (1 / y^2 - 1 / x^2)"
      using assms by (simp add: divide_simps of_nat_diff)
    thus ?case by (simp add: x_def y_def algebra_simps)
  qed
  finally show ?thesis
    unfolding beukers_nn_integral1_series by (intro suminf_ennreal_eq) (auto simp: add_ac)
qed

lemma beukers_integral1_different:
  assumes "r > s"
  shows   "beukers_integral1 r s = (\<Sum>k\<in>{s<..r}. 1 / k ^ 2) / (r - s)"
proof -
  have "ln (a * b) * a ^ r * b ^ s / (1 - a * b) \<le> 0" if "a \<in> {0<..<1}" "b \<in> {0<..<1}" for a b :: real
    using that mult_strict_mono[of a 1 b 1] by (intro mult_nonpos_nonneg divide_nonpos_nonneg) auto
    thus ?thesis
    using beukers_nn_integral1_different[OF assms]
    unfolding beukers_nn_integral1_def beukers_integral1_def
    by (intro set_integral_eq_nn_integral AE_I2)
       (auto simp flip: lborel_prod simp: case_prod_unfold set_borel_measurable_def
             intro: divide_nonpos_nonneg mult_nonpos_nonneg intro!: sum_nonneg divide_nonneg_nonneg)
qed

end

text \<open>
  It is also easy to see that if we exchange \<open>r\<close> and \<open>s\<close>, nothing changes.
\<close>
lemma beukers_nn_integral1_swap:
  "beukers_nn_integral1 r s = beukers_nn_integral1 s r"
  unfolding beukers_nn_integral1_def lborel_prod [symmetric]
  by (subst lborel_pair.nn_integral_swap, simp)
     (intro nn_integral_cong, auto simp: indicator_def algebra_simps split: if_splits)

lemma beukers_nn_integral1_finite: "beukers_nn_integral1 r s < \<infinity>"
  using beukers_nn_integral1_different[of r s] beukers_nn_integral1_different[of s r]
  by (cases r s rule: linorder_cases)
     (simp_all add: beukers_nn_integral1_same beukers_nn_integral1_swap)

lemma beukers_integral1_integrable:
  "set_integrable lborel ({0<..<1}\<times>{0<..<1})
     (\<lambda>(x,y). (-ln (x*y) / (1 - x*y) * x^r * y^s :: real))"
proof (intro set_integrableI_nonneg AE_I2; clarify?)
  fix x y :: real assume xy: "x \<in> {0<..<1}" "y \<in> {0<..<1}"
  have "0 \<ge> ln (x * y) / (1 - x * y) * x ^ r * y ^ s"
    using mult_strict_mono[of x 1 y 1]
    by (intro mult_nonpos_nonneg divide_nonpos_nonneg) (use xy in auto)
  thus "0 \<le> - ln (x * y) / (1 - x * y) * x ^ r * y ^ s" by simp
next
  show "\<integral>\<^sup>+x\<in>{0<..<1}\<times>{0<..<1}. ennreal (case x of (x, y) \<Rightarrow>
           - ln (x * y) / (1 - x * y) * x ^ r * y ^ s) \<partial>lborel < \<infinity>"
    using beukers_nn_integral1_finite by (simp add: beukers_nn_integral1_def case_prod_unfold)
qed (simp_all flip: lborel_prod add: set_borel_measurable_def)

lemma beukers_integral1_integrable':
  "set_integrable lborel ({0<..<1}\<times>{0<..<1}\<times>{0<..<1})
     (\<lambda>(z,x,y). (x^r * y^s / (1 - (1 - x*y) * z) :: real))"
proof (intro set_integrableI_nonneg AE_I2; clarify?)
  fix x y z :: real assume xyz: "x \<in> {0<..<1}" "y \<in> {0<..<1}" "z \<in> {0<..<1}"
  show "0 \<le> x^r * y^s / (1 - (1 - x*y) * z)"
    using mult_strict_mono[of x 1 y 1] xyz beukers_denom_ineq[of x y z]
    by (intro mult_nonneg_nonneg divide_nonneg_nonneg) auto
next
  show "\<integral>\<^sup>+x\<in>{0<..<1}\<times>{0<..<1}\<times>{0<..<1}. ennreal (case x of (z,x,y) \<Rightarrow>
           x ^ r * y ^ s / (1-(1-x*y)*z)) \<partial>lborel < \<infinity>"
    using beukers_nn_integral1_finite
    by (simp add: beukers_nn_integral1_altdef case_prod_unfold)
qed (simp_all flip: lborel_prod add: set_borel_measurable_def)

lemma beukers_integral1_conv_nn_integral:
  "beukers_integral1 r s = enn2real (beukers_nn_integral1 r s)"
proof -
  have "ln (a * b) * a ^ r * b ^ s / (1 - a * b) \<le> 0" if "a \<in> {0<..<1}" "b \<in> {0<..<1}"
    for a b :: real
    using mult_strict_mono[of a 1 b 1] that by (intro divide_nonpos_nonneg mult_nonpos_nonneg) auto
  thus ?thesis unfolding beukers_integral1_def using beukers_nn_integral1_finite[of r s]
    by (intro set_integral_eq_nn_integral)
       (auto simp: case_prod_unfold beukers_nn_integral1_def
                   set_borel_measurable_def simp flip: borel_prod
             intro!: AE_I2 intro: divide_nonpos_nonneg mult_nonpos_nonneg)
qed

lemma beukers_integral1_swap: "beukers_integral1 r s = beukers_integral1 s r"
  by (simp add: beukers_integral1_conv_nn_integral beukers_nn_integral1_swap)


subsection \<open>The second double integral\<close>

context
  fixes n :: nat
  fixes D :: "(real \<times> real) set" and D' :: "(real \<times> real \<times> real) set"
  fixes P :: "real \<Rightarrow> real" and Q :: "nat \<Rightarrow> real \<Rightarrow> real"
  defines "D \<equiv> {0<..<1} \<times> {0<..<1}" and "D' \<equiv> {0<..<1} \<times> {0<..<1} \<times> {0<..<1}"
  defines "Q \<equiv> Gen_Shleg n" and "P \<equiv> Shleg n"
begin

text \<open>
  The next integral to consider is the following variant of $I_1$:
  \[I_2 :=
      \int_0^1 \int_0^1 -\frac{\ln(xy)}{1-xy} P_n(x) P_n(y)\,\text{d}x\,\text{d}y\ .\]
\<close>

definition beukers_integral2 :: real where
  "beukers_integral2 = (\<integral>(x,y)\<in>D. (-ln (x*y) / (1-x*y) * P x * P y) \<partial>lborel)"

text \<open>
  $I_2$ is simply a sum of integrals of type $I_1$, so using our results for
  $I_1$, we can write $I_2$ in the form $A \zeta(3) + \frac{B}{\text{lcm}\{1\ldots n\}^3}$
  where $A$ and $B$ are integers and $A > 0$:
\<close>
lemma beukers_integral2_conv_int_combination:
  obtains A B :: int where "A > 0" and
    "beukers_integral2 = of_int A * Re (zeta 3) + of_int B / of_nat (Lcm {1..n} ^ 3)"
proof -
  let ?I1 = "(\<lambda>i. (i, i)) ` {..n}"
  let ?I2 = "Set.filter (\<lambda>(i,j). i \<noteq> j) ({..n}\<times>{..n})"
  let ?I3 = "Set.filter (\<lambda>(i,j). i < j) ({..n}\<times>{..n})"
  let ?I4 = "Set.filter (\<lambda>(i,j). i > j) ({..n}\<times>{..n})"
  define p where "p = shleg_poly n"
  define I where "I = (SIGMA i:{..n}. {1..i})"
  define J where "J = (SIGMA (i,j):?I4. {j<..i})"
  define h where "h = beukers_integral1"
  define A :: int where "A = (\<Sum>i\<le>n. 2 * poly.coeff p i ^ 2)"
  define B1 where "B1 = (\<Sum>(i,k)\<in>I. real_of_int (-2 * coeff p i ^ 2) / real_of_int (k ^ 3))"
  define B2 where "B2 = (\<Sum>((i,j),k)\<in>J. real_of_int (2 * coeff p i * coeff p j) / real_of_int (k^2*(i-j)))"
  define d where "d = Lcm {1..n} ^ 3"

  have [simp]: "h i j = h j i" for i j
    by (simp add: h_def beukers_integral1_swap)

  have "beukers_integral2 =
        (\<integral>(x,y)\<in>D. (\<Sum>(i,j)\<in>{..n}\<times>{..n}. coeff p i * coeff p j *
           -ln (x*y) / (1-x*y) * x ^ i * y ^ j) \<partial>lborel)"
    unfolding beukers_integral2_def
    by (subst sum.cartesian_product [symmetric])
       (simp add: poly_altdef P_def Shleg_def mult_ac case_prod_unfold p_def
                  sum_distrib_left sum_distrib_right sum_negf sum_divide_distrib)
  also have "\<dots> = (\<Sum>(i,j)\<in>{..n}\<times>{..n}. coeff p i * coeff p j * h i j)"
    unfolding case_prod_unfold
  proof (subst set_integral_sum)
    fix ij :: "nat \<times> nat"
    have "set_integrable lborel D
          (\<lambda>(x,y). real_of_int (coeff p (fst ij) * coeff p (snd ij)) *
                 (-ln (x*y) / (1-x*y) * x ^ fst ij * y ^ snd ij))"
      unfolding case_prod_unfold using beukers_integral1_integrable[of "fst ij" "snd ij"]
      by (intro set_integrable_mult_right) (auto simp: D_def case_prod_unfold)
    thus "set_integrable lborel D
          (\<lambda>pa. real_of_int (coeff p (fst ij) * coeff p (snd ij)) *
                 -ln (fst pa * snd pa) / (1 - fst pa * snd pa) * fst pa ^ fst ij * snd pa ^ snd ij)"
      by (simp add: mult_ac case_prod_unfold)
  qed (auto simp: beukers_integral1_def h_def case_prod_unfold mult.assoc D_def
            simp flip: set_integral_mult_right)
  also have "\<dots> = (\<Sum>(i,j)\<in>?I1\<union>?I2. coeff p i * coeff p j * h i j)"
    by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>(i,j)\<in>?I1. coeff p i * coeff p j * h i j) +
                  (\<Sum>(i,j)\<in>?I2. coeff p i * coeff p j * h i j)"
    by (intro sum.union_disjoint) auto
  also have "(\<Sum>(i,j)\<in>?I1. coeff p i * coeff p j * h i j) =
               (\<Sum>i\<le>n. coeff p i ^ 2 * h i i)"
    by (subst sum.reindex) (auto intro: inj_onI simp: case_prod_unfold power2_eq_square)
  also have "\<dots> = (\<Sum>i\<le>n. coeff p i ^ 2 * 2 * (Re (zeta 3) - (\<Sum>k=1..i. 1 / k ^ 3)))"
    unfolding h_def D_def
    by (intro sum.cong refl, subst beukers_integral1_same) auto
  also have "\<dots> = of_int A * Re (zeta 3) -
                    (\<Sum>i\<le>n. 2 * coeff p i ^ 2 * (\<Sum>k=1..i. 1 / k ^ 3))"
    by (simp add: sum_subtractf sum_distrib_left sum_distrib_right algebra_simps A_def)
  also have "\<dots> = of_int A * Re (zeta 3) + B1"
    unfolding I_def B1_def by (subst sum.Sigma [symmetric]) (auto simp: sum_distrib_left sum_negf)
  also have "(\<Sum>(i,j)\<in>?I2. coeff p i * coeff p j * h i j) =
               (\<Sum>(i,j)\<in>?I3\<union>?I4. coeff p i * coeff p j * h i j)"
    by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>(i,j)\<in>?I3. coeff p i * coeff p j * h i j) +
                  (\<Sum>(i,j)\<in>?I4. coeff p i * coeff p j * h i j)"
    by (intro sum.union_disjoint) auto
  also have "(\<Sum>(i,j)\<in>?I3. coeff p i * coeff p j * h i j) =
               (\<Sum>(i,j)\<in>?I4. coeff p i * coeff p j * h i j)"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>(i,j). (j,i)" "\<lambda>(i,j). (j,i)"]) auto
  also have "\<dots> + \<dots> = 2 * \<dots>" by simp
  also have "\<dots> = (\<Sum>(i,j)\<in>?I4. \<Sum>k\<in>{j<..i}. 2 * coeff p i * coeff p j / k ^ 2 / (i - j))"
    unfolding sum_distrib_left
    by (intro sum.cong refl)
       (auto simp: h_def beukers_integral1_different sum_divide_distrib sum_distrib_left mult_ac)
  also have "\<dots> = B2"
    unfolding J_def B2_def by (subst sum.Sigma [symmetric]) (auto simp: case_prod_unfold)

  also have "\<exists>B1'. B1 = real_of_int B1' / real_of_int d"
    unfolding B1_def case_prod_unfold
    by (rule sum_rationals_common_divisor') (auto simp: d_def I_def)
  then obtain B1' where "B1 = real_of_int B1' / real_of_int d" ..

  also have "\<exists>B2'. B2 = real_of_int B2' / real_of_int d"
    unfolding B2_def case_prod_unfold J_def
  proof (rule sum_rationals_common_divisor'; clarsimp?)
    fix i j k :: nat assume ijk: "i \<le> n" "j < k" "k \<le> i"
    have "int (k ^ 2 * (i - j)) dvd int (Lcm {1..n} ^ 2 * Lcm {1..n})"
      unfolding int_dvd_int_iff using ijk
      by (intro mult_dvd_mono dvd_power_same dvd_Lcm) auto
    also have "\<dots> = d"
      by (simp add: d_def power_numeral_reduce)
    finally show "int k ^ 2 * int (i - j) dvd int d" by simp
  qed(auto simp: d_def J_def intro!: Nat.gr0I)
  then obtain B2' where "B2 = real_of_int B2' / real_of_int d" ..

  finally have "beukers_integral2 =
                  of_int A * Re (zeta 3) + of_int (B1' + B2') / of_nat (Lcm {1..n} ^ 3)"
    by (simp add: add_divide_distrib d_def)

  moreover have "coeff p 0 = P 0"
    unfolding P_def p_def Shleg_def by (simp add: poly_0_coeff_0)
  hence "coeff p 0 = 1"
    by (simp add: P_def)
  hence "A > 0"
    unfolding A_def by (intro sum_pos2[of _ 0]) auto

  ultimately show ?thesis
    by (intro that[of A "B1' + B2'"]) auto
qed

lemma beukers_integral2_integrable:
  "set_integrable lborel D (\<lambda>(x,y). -ln (x*y) / (1 - x*y) * P x * P y)"
proof -
  have "bounded (P ` {0..1})"
    unfolding P_def Shleg_def
    by (intro compact_imp_bounded compact_continuous_image continuous_intros) auto
  then obtain C where C: "\<And>x. x \<in> {0..1} \<Longrightarrow> norm (P x) \<le> C"
    unfolding bounded_iff by fast
  have [measurable]: "P \<in> borel_measurable borel" by (simp add: P_def)
  from C[of 0] have "C \<ge> 0" by simp
  show ?thesis
  proof (rule set_integrable_bound[OF _ _ AE_I2]; clarify?)
    show "set_integrable lborel D (\<lambda>(x,y). C ^ 2 * (-ln (x*y) / (1 - x*y)))"
      using beukers_integral1_integrable[of 0 0] unfolding case_prod_unfold
      by (intro set_integrable_mult_right) (auto simp: D_def)
  next
    fix x y :: real
    assume xy: "(x, y) \<in> D"
    from xy have "x * y < 1"
      using mult_strict_mono[of x 1 y 1] by (simp add: D_def)
    have "norm (-ln (x*y) / (1 - x*y) * P x * P y) = (-ln (x*y)) / (1 - x*y) * norm (P x) * norm (P y)"
      using xy \<open>x * y < 1\<close> by (simp add: abs_mult abs_divide D_def)
    also have "\<dots> \<le> (-ln (x*y)) / (1-x*y) * C * C"
      using xy C[of x] C[of y] \<open>x * y < 1\<close> \<open>C \<ge> 0\<close>
      by (intro mult_mono divide_left_mono)
         (auto simp: D_def divide_nonpos_nonneg mult_nonpos_nonneg)
    also have "\<dots> = norm ((-ln (x*y)) / (1-x*y) * C * C)"
      using xy \<open>x * y < 1\<close> \<open>C \<ge> 0\<close> by (simp add: abs_divide abs_mult D_def)
    finally show "norm (-ln (x*y) / (1 - x*y) * P x * P y)
           \<le> norm (case (x, y) of (x, y) \<Rightarrow> C\<^sup>2 * (- ln (x * y) / (1 - x * y)))"
      by (auto simp: algebra_simps power2_eq_square abs_mult abs_divide)
  qed (auto simp: D_def set_borel_measurable_def case_prod_unfold simp flip: lborel_prod)
qed


subsection \<open>The triple integral\<close>

text \<open>
  Lastly, we turn to the triple integral
  \[I_3 := \int_0^1 \int_0^1 \int_0^1
      \frac{(x(1-x)y(1-y)w(1-w))^n}{(1-(1-xy)w)^{n+1}}\ \text{d}x\,\text{d}y\,\text{d}w\ .\]
\<close>

definition beukers_nn_integral3 :: ennreal where
  "beukers_nn_integral3 =
     (\<integral>\<^sup>+(w,x,y)\<in>D'. ((x*(1-x)*y*(1-y)*w*(1-w))^n / (1-(1-x*y)*w)^(n+1)) \<partial>lborel)"

definition beukers_integral3 :: real where
  "beukers_integral3 =
     (\<integral>(w,x,y)\<in>D'. ((x*(1-x)*y*(1-y)*w*(1-w))^n / (1-(1-x*y)*w)^(n+1)) \<partial>lborel)"

text \<open>
  We first prove the following bound
  (which is a consequence of the arithmetic--geometric mean inequality)
  that will help us to bound the triple integral.
\<close>
lemma beukers_integral3_integrand_bound:
  fixes x y z :: real
  assumes xyz: "x \<in> {0<..<1}" "y \<in> {0<..<1}" "z \<in> {0<..<1}"
  shows   "(x*(1-x)*y*(1-y)*z*(1-z)) / (1-(1-x*y)*z) \<le> 1 / 27" (is "?lhs \<le> _")
proof -
  have ineq1: "x * (1 - x) \<le> 1 / 4" if x: "x \<in> {0..1}" for x :: real
  proof -
    have "x * (1 - x) - 1 / 4 = -((x - 1 / 2) ^ 2)"
      by (simp add: algebra_simps power2_eq_square)
    also have "\<dots> \<le> 0"
      by simp
    finally show ?thesis by simp
  qed

  have ineq2: "x * (1 - x) ^ 2 \<le> 4 / 27" if x: "x \<in> {0..1}" for x :: real
  proof -
    have "x * (1 - x) ^ 2 - 4 / 27 = (x - 4 / 3) * (x - 1 / 3) ^ 2"
      by (simp add: algebra_simps power2_eq_square)
    also have "\<dots> \<le> 0"
      by (rule mult_nonpos_nonneg) (use x in auto)
    finally show ?thesis by simp
  qed

  have "1 - (1-x*y)*z = (1 - z) + x * y * z"
    by (simp add: algebra_simps)
  also have "\<dots> \<ge> 2 * sqrt (1 - z) * sqrt x * sqrt y * sqrt z"
    using arith_geo_mean_sqrt[of "1 - z" "x * y * z"] xyz
    by (auto simp: real_sqrt_mult)

  finally have *: "?lhs \<le> (x*(1-x)*y*(1-y)*z*(1-z)) / (2 * sqrt (1 - z) * sqrt x * sqrt y * sqrt z)"
    using xyz beukers_denom_ineq[of x y z]
    by (intro divide_left_mono mult_nonneg_nonneg mult_pos_pos) auto

  have "(x*(1-x)*y*(1-y)*z*(1-z)) = (sqrt x * sqrt x * (1-x) * sqrt y * sqrt y *
               (1-y) * sqrt z * sqrt z * sqrt (1-z) * sqrt (1-z))"
    using xyz by simp
  also have "\<dots> / (2 * sqrt (1 - z) * sqrt x * sqrt y * sqrt z) =
               sqrt (x * (1 - x) ^ 2) * sqrt (y * (1 - y) ^ 2) * sqrt (z * (1 - z)) / 2"
    using xyz by (simp add: divide_simps real_sqrt_mult del: real_sqrt_mult_self)
  also have "\<dots> \<le> sqrt (4 / 27) * sqrt (4 / 27) * sqrt (1 / 4) / 2"
    using xyz by (intro divide_right_mono mult_mono real_sqrt_le_mono ineq1 ineq2) auto
  also have "\<dots> = 1 / 27"
    by (simp add: real_sqrt_divide)
  finally show ?thesis using * by argo
qed

text \<open>
  Connecting the above bound with our results of $I_1$, it is easy to see that
  $I_3 \leq 2 \cdot 27^{-n} \cdot \zeta(3)$:
\<close>
lemma beukers_nn_integral3_le:
  "beukers_nn_integral3 \<le> ennreal (2 * (1 / 27) ^ n * Re (zeta 3))"
proof -
  have D' [measurable]: "D' \<in> sets (borel \<Otimes>\<^sub>M borel \<Otimes>\<^sub>M borel)"
    unfolding D'_def by (simp flip: borel_prod)
  have "beukers_nn_integral3 =
          (\<integral>\<^sup>+(w,x,y)\<in>D'. ((x*(1-x)*y*(1-y)*w*(1-w))^n / (1-(1-x*y)*w)^(n+1)) \<partial>lborel)"
    by (simp add: beukers_nn_integral3_def)
  also have "\<dots> \<le> (\<integral>\<^sup>+(w,x,y)\<in>D'. ((1 / 27) ^ n / (1-(1-x*y)*w)) \<partial>lborel)"
  proof (intro set_nn_integral_mono ennreal_leI, clarify, goal_cases)
    case (1 w x y)
    have "(x*(1-x)*y*(1-y)*w*(1-w))^n / (1-(1-x*y)*w)^(n+1) =
            ((x*(1-x)*y*(1-y)*w*(1-w)) / (1-(1-x*y)*w)) ^ n / (1-(1-x*y)*w)"
      by (simp add: divide_simps)
    also have "\<dots> \<le> (1 / 27) ^ n / (1 - (1 - x * y) * w)"
      using beukers_denom_ineq[of x y w] 1
      by (intro divide_right_mono power_mono beukers_integral3_integrand_bound)
         (auto simp: D'_def)
    finally show ?case .
  qed
  also have "\<dots> = ennreal ((1 / 27) ^ n) * (\<integral>\<^sup>+(w,x,y)\<in>D'. (1 / (1-(1-x*y)*w)) \<partial>lborel)"
    unfolding lborel_prod [symmetric] case_prod_unfold
    by (subst nn_integral_cmult [symmetric])
       (auto intro!: nn_integral_cong simp: indicator_def simp flip: ennreal_mult')
  also have "(\<integral>\<^sup>+(w,x,y)\<in>D'. (1 / (1-(1-x*y)*w)) \<partial>lborel) =
               (\<integral>\<^sup>+(x,y)\<in>{0<..<1}\<times>{0<..<1}. ennreal (- (ln (x * y) / (1 - x * y))) \<partial>lborel)"
    using beukers_nn_integral1_altdef[of 0 0]
    by (simp add: beukers_nn_integral1_def D'_def case_prod_unfold)
  also have "\<dots> = ennreal (2 * Re (zeta 3))"
    using beukers_nn_integral1_same[of 0 0] by (simp add: D_def beukers_nn_integral1_def)
  also have "ennreal ((1 / 27) ^ n) * \<dots> = ennreal (2 * (1 / 27) ^ n * Re (zeta 3))"
    by (subst ennreal_mult' [symmetric]) (simp_all add: mult_ac)
  finally show ?thesis .
qed

lemma beukers_nn_integral3_finite: "beukers_nn_integral3 < \<infinity>"
  by (rule le_less_trans, rule beukers_nn_integral3_le) simp_all

lemma beukers_integral3_integrable:
  "set_integrable lborel D' (\<lambda>(w,x,y). (x*(1-x)*y*(1-y)*w*(1-w))^n / (1-(1-x*y)*w)^(n+1))"
  unfolding case_prod_unfold using less_imp_le[OF beukers_denom_ineq] beukers_nn_integral3_finite
  by (intro set_integrableI_nonneg AE_I2 impI)
     (auto simp: D'_def set_borel_measurable_def beukers_nn_integral3_def case_prod_unfold
           simp flip: lborel_prod intro!: divide_nonneg_nonneg mult_nonneg_nonneg)

lemma beukers_integral3_conv_nn_integral:
  "beukers_integral3 = enn2real beukers_nn_integral3"
  unfolding beukers_integral3_def using beukers_nn_integral3_finite less_imp_le[OF beukers_denom_ineq]
  by (intro set_integral_eq_nn_integral AE_I2 impI)
     (auto simp: D'_def set_borel_measurable_def beukers_nn_integral3_def case_prod_unfold
           simp flip: lborel_prod)

lemma beukers_integral3_le: "beukers_integral3 \<le> 2 * (1 / 27) ^ n * Re (zeta 3)"
proof -
  have "beukers_integral3 = enn2real beukers_nn_integral3"
    by (rule beukers_integral3_conv_nn_integral)
  also have "\<dots> \<le> enn2real (ennreal (2 * (1 / 27) ^ n * Re (zeta 3)))"
    by (intro enn2real_mono beukers_nn_integral3_le) auto
  also have "\<dots> = 2 * (1 / 27) ^ n * Re (zeta 3)"
    using Re_zeta_ge_1[of 3] by (intro enn2real_ennreal mult_nonneg_nonneg) auto
  finally show ?thesis .
qed

text \<open>
  It is also easy to see that $I_3 > 0$.
\<close>
lemma beukers_nn_integral3_pos: "beukers_nn_integral3 > 0"
proof -
  have D' [measurable]: "D' \<in> sets (borel \<Otimes>\<^sub>M borel \<Otimes>\<^sub>M borel)"
    unfolding D'_def by (simp flip: borel_prod)

  have *: "\<not>(AE (w,x,y) in lborel. ennreal ((x*(1-x)*y*(1-y)*w*(1-w))^n /
             (1-(1-x*y)*w)^(n+1)) * indicator D' (w,x,y) \<le> 0)"
            (is "\<not>(AE z in lborel. ?P z)")
  proof -
    {
      fix w x y :: real assume xyw: "(w,x,y) \<in> D'"
      hence "(x*(1-x)*y*(1-y)*w*(1-w))^n / (1-(1-x*y)*w)^(n+1) > 0"
        using beukers_denom_ineq[of x y w]
        by (intro divide_pos_pos mult_pos_pos zero_less_power) (auto simp: D'_def)
      with xyw have "\<not>?P (w,x,y)"
        by (auto simp: indicator_def D'_def)
    }
    hence *: "\<not>?P z" if "z \<in> D'" for z using that by blast
    hence "{z\<in>space lborel. \<not>?P z} = D'" by auto
    moreover have "emeasure lborel D' = 1"
    proof -
      have "D' = box (0,0,0) (1,1,1)"
        by (auto simp: D'_def box_def Basis_prod_def)
      also have "emeasure lborel \<dots> = 1"
        by (subst emeasure_lborel_box) (auto simp: Basis_prod_def)
      finally show ?thesis by simp
    qed
    ultimately show ?thesis
      by (subst AE_iff_measurable[of D']) (simp_all flip: borel_prod)
  qed

  hence "nn_integral lborel (\<lambda>_::real\<times>real\<times>real. 0) < beukers_nn_integral3"
    unfolding beukers_nn_integral3_def
    by (intro nn_integral_less) (simp_all add: case_prod_unfold flip: lborel_prod)
  thus ?thesis by simp
qed

lemma beukers_integral3_pos: "beukers_integral3 > 0"
proof -
  have "0 < enn2real beukers_nn_integral3"
    using beukers_nn_integral3_pos beukers_nn_integral3_finite
    by (subst enn2real_positive_iff) auto
  also have "\<dots> = beukers_integral3"
    by (rule beukers_integral3_conv_nn_integral [symmetric])
  finally show ?thesis .
qed


subsection \<open>Connecting the double and triple integral\<close>

text \<open>
  In this section, we will prove the most technically involved part,
  namely that $I_2 = I_3$. I will not go into detail about how this works --
  the reader is advised to simply look at Filaseta's presentation of the proof.

  The basic idea is to integrate by parts \<open>n\<close> times with respect to \<open>y\<close> to eliminate
  the factor $P(y)$, then change variables $z = \frac{1-w}{1-(1-xy)w}$, and then
  apply the same integration by parts \<open>n\<close> times to \<open>x\<close> to eliminate $P(x)$.
\<close>

text \<open>
  The first expand \[-\frac{\ln (xy)}{1-xy} = \int_0^1 \frac{1}{1-(1-xy)z}\,\text{d}z\ .\]
\<close>
lemma beukers_aux_ln_conv_integral:
  fixes x y :: real
  assumes xy: "x \<in> {0<..<1}" "y \<in> {0<..<1}"
  shows "-ln (x*y) / (1-x*y) = (LBINT z=0..1. 1 / (1-(1-x*y)*z))"
proof -
  have "x * y < 1"
    using mult_strict_mono[of x 1 y 1] xy by simp
  have less: "(1 - x * y) * u < 1" if u: "u \<in> {0..1}" for u
  proof -
    from u \<open>x * y < 1\<close> have "(1 - x * y) * u \<le> (1 - x * y) * 1"
      by (intro mult_left_mono) auto
    also have "\<dots> < 1 * 1"
      using xy by (intro mult_strict_right_mono) auto
    finally show "(1 - x * y) * u < 1" by simp
  qed
  have neq: "(1 - x * y) * u \<noteq> 1" if "u \<in> {0..1}" for u
    using less[of u] that by simp

  let ?F = "\<lambda>z. ln (1-(1-x*y)*z)/(x*y-1)"
  have "(LBINT z=ereal 0..ereal 1. 1 / (1-(1-x*y)*z)) = ?F 1 - ?F 0"
  proof (rule interval_integral_FTC_finite, goal_cases cont deriv)
    case cont
    show ?case
      using neq by (intro continuous_intros) auto
  next
    case (deriv z)
    show ?case
      unfolding has_field_derivative_iff_has_vector_derivative [symmetric]
      by (insert less[of z] xy \<open>x * y < 1\<close> deriv)
         (rule derivative_eq_intros refl | simp)+
  qed
  also have "\<dots> = -ln (x*y) / (1-x*y)"
    using \<open>x * y < 1\<close> by (simp add: field_simps)
  finally show ?thesis
    by (simp add: zero_ereal_def one_ereal_def)
qed

text \<open>
  The first part we shall show is the integration by parts.
\<close>
lemma beukers_aux_by_parts_aux:
  assumes xz: "x \<in> {0<..<1}" "z \<in> {0<..<1}" and "k \<le> n"
  shows "(LBINT y=0..1. Q n y * (1/(1-(1-x*y)*z))) =
         (LBINT y=0..1. Q (n-k) y * (fact k * (x*z)^k / (1-(1-x*y)*z) ^ (k+1)))"
  using assms(3)
proof (induction k)
  case (Suc k)
  note [derivative_intros] = DERIV_chain2[OF has_field_derivative_Gen_Shleg]
  define G where "G = (\<lambda>y. -fact k * (x*z)^k / (1-(1-x*y)*z) ^ (k+1))"
  define g where "g = (\<lambda>y. fact (Suc k) * (x*z)^Suc k / (1-(1-x*y)*z) ^ (k+2))"

  have less: "(1 - x * y) * z < 1" and neq: "(1 - x * y) * z \<noteq> 1"
    if y: "y \<in> {0..1}" for y
  proof -
    from y xz have "x * y \<le> x * 1"
      by (intro mult_left_mono) auto
    also have "\<dots> < 1"
      using xz by simp
    finally have "(1 - x * y) * z \<le> 1 * z"
      using xz y by (intro mult_right_mono) auto
    also have "\<dots> < 1"
      using xz by simp
    finally show "(1 - x * y) * z < 1" by simp
    thus "(1 - x * y) * z \<noteq> 1" by simp
  qed

  have cont: "continuous_on {0..1} g"
    using neq by (auto simp: g_def intro!: continuous_intros)
  have deriv: "(G has_real_derivative g y) (at y within {0..1})" if y: "y \<in> {0..1}" for y
    unfolding G_def
    by (insert neq xz y, (rule derivative_eq_intros refl power_not_zero)+)
       (auto simp: divide_simps g_def)
  have deriv2: "(Q (n - Suc k) has_real_derivative Q (n - k) y) (at y within {0..1})" for y
    using Suc.prems by (auto intro!: derivative_eq_intros simp: Suc_diff_Suc Q_def)

  have "(LBINT y=0..1. Q (n-Suc k) y * (fact (Suc k) * (x*z)^Suc k / (1-(1-x*y)*z) ^ (k+2))) =
        (LBINT y=0..1. Q (n-Suc k) y * g y)"
    by (simp add: g_def)
  also have "(LBINT y=0..1. Q (n-Suc k) y * g y) = -(LBINT y=0..1. Q (n-k) y * G y)"
    using Suc.prems deriv deriv2 cont
    by (subst interval_lebesgue_integral_by_parts_01[where f = "Q (n-k)" and G = G])
       (auto intro!: continuous_intros simp: Q_def)
  also have "\<dots> = (LBINT y=0..1. Q (n-k) y * (fact k * (x*z)^k / (1-(1-x*y)*z) ^ (k+1)))"
    by (simp add: G_def flip: interval_lebesgue_integral_uminus)
  finally show ?case using Suc by simp
qed auto

lemma beukers_aux_by_parts:
  assumes xz: "x \<in> {0<..<1}" "z \<in> {0<..<1}"
  shows "(LBINT y=0..1. P y / (1-(1-x*y)*z)) =
         (LBINT y=0..1. (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z) ^ (n+1))"
proof -
  have "(LBINT y=0..1. P y * (1/(1-(1-x*y)*z))) =
           1 / fact n * (LBINT y=0..1. Q n y * (1/(1-(1-x*y)*z)))"
    unfolding interval_lebesgue_integral_mult_right [symmetric]
    by (simp add: P_def Q_def Shleg_altdef)
  also have "\<dots> = (LBINT y=0..1. (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z) ^ (n+1))"
    by (subst beukers_aux_by_parts_aux[OF assms, of n], simp,
        subst interval_lebesgue_integral_mult_right [symmetric])
       (simp add: Q_def mult_ac Gen_Shleg_0_left power_mult_distrib)
  finally show ?thesis by simp
qed

text \<open>
  We then get the following by applying the integration by parts to \<open>y\<close>:
\<close>
lemma beukers_aux_integral_transform1:
  fixes z :: real
  assumes z: "z \<in> {0<..<1}"
  shows   "(LBINT (x,y):D. P x * P y / (1-(1-x*y)*z)) =
           (LBINT (x,y):D. P x * (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1))"
proof -
  have cbox: "cbox (0, 0) (1, 1) = ({0..1} \<times> {0..1} :: (real \<times> real) set)"
    by (auto simp: cbox_def Basis_prod_def inner_prod_def)
  have box: "box (0, 0) (1, 1) = ({0<..<1} \<times> {0<..<1} :: (real \<times> real) set)"
    by (auto simp: box_def Basis_prod_def inner_prod_def)
  have "set_integrable lborel (cbox (0,0) (1,1))
          (\<lambda>(x, y). P x * P y / (1 - (1 - x * y) * z))"
    unfolding lborel_prod case_prod_unfold P_def
  proof (intro continuous_on_imp_set_integrable_cbox continuous_intros ballI)
    fix p :: "real \<times> real" assume p: "p \<in> cbox (0, 0) (1, 1)"
    have "(1 - fst p * snd p) * z \<le> 1 * z"
      using mult_mono[of "fst p" 1 "snd p" 1] p z cbox by (intro mult_right_mono) auto
    also have "\<dots> < 1" using z by simp
    finally show "1 - (1 - fst p * snd p) * z \<noteq> 0" by simp
  qed
  hence integrable: "set_integrable lborel (box (0,0) (1,1))
          (\<lambda>(x, y). P x * P y / (1 - (1 - x * y) * z))"
    by (rule set_integrable_subset) (auto simp:  box simp flip: borel_prod)

  have "set_integrable lborel (cbox (0,0) (1,1))
          (\<lambda>(x, y). P x * (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1))"
    unfolding lborel_prod case_prod_unfold P_def
  proof (intro continuous_on_imp_set_integrable_cbox continuous_intros ballI)
    fix p :: "real \<times> real" assume p: "p \<in> cbox (0, 0) (1, 1)"
    have "(1 - fst p * snd p) * z \<le> 1 * z"
      using mult_mono[of "fst p" 1 "snd p" 1] p z cbox by (intro mult_right_mono) auto
    also have "\<dots> < 1" using z by simp
    finally show "(1 - (1 - fst p * snd p) * z) ^ (n + 1) \<noteq> 0" by simp
  qed
  hence integrable': "set_integrable lborel D
          (\<lambda>(x, y). P x * (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1))"
    by (rule set_integrable_subset) (auto simp: box D_def simp flip: borel_prod)

  have "(LBINT (x,y):D. P x * P y / (1-(1-x*y)*z)) =
          (LBINT x=0..1. (LBINT y=0..1. P x * P y / (1-(1-x*y)*z)))"
    unfolding D_def lborel_prod [symmetric] using box integrable
    by (subst lborel_pair.set_integral_fst') (simp_all add: interval_integral_Ioo lborel_prod)
  also have "\<dots> = (LBINT x=0..1. P x * (LBINT y=0..1. P y / (1-(1-x*y)*z)))"
    by (subst interval_lebesgue_integral_mult_right [symmetric]) (simp add: mult_ac)
  also have "\<dots> = (LBINT x=0..1. P x * (LBINT y=0..1. (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1)))"
    using z by (intro interval_lebesgue_integral_lborel_01_cong, subst beukers_aux_by_parts) auto
  also have "\<dots> = (LBINT x=0..1. (LBINT y=0..1. P x * (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1)))"
    by (subst interval_lebesgue_integral_mult_right [symmetric]) (simp add: mult_ac)
  also have "\<dots> = (LBINT (x,y):D. P x * (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1))"
    unfolding D_def lborel_prod [symmetric] using box integrable'
    by (subst lborel_pair.set_integral_fst')
       (simp_all add: D_def interval_integral_Ioo lborel_prod)
  finally show "(LBINT (x,y):D. P x * P y / (1-(1-x*y)*z)) = \<dots>" .
qed

text \<open>
  We then change variables for \<open>z\<close>:
\<close>
lemma beukers_aux_integral_transform2:
  assumes xy: "x \<in> {0<..<1}" "y \<in> {0<..<1}"
  shows "(LBINT z=0..1. (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1)) =
         (LBINT w=0..1. (1-w)^n * (1-y)^n / (1-(1-x*y)*w))"
proof -
  define g where "g = (\<lambda>z. (1 - z) / (1-(1-x*y)*z))"
  define g' where "g' = (\<lambda>z. -x*y / (1-(1-x*y)*z)^2)"
  have "x * y < 1"
    using mult_strict_mono[of x 1 y 1] xy by simp
  have less: "(1 - (x * y)) * w < 1" and neq: "(1 - (x * y)) * w \<noteq> 1"
    if w: "w \<in> {0..1}" for w
  proof -
    have "(1 - (x * y)) * w \<le> (1 - (x * y)) * 1"
      using w \<open>x * y < 1\<close> by (intro mult_left_mono) auto
    also have "\<dots> < 1"
      using xy by simp
    finally show "(1 - (x * y)) * w < 1" .
    thus "(1 - (x * y)) * w \<noteq> 1" by simp
  qed

  have deriv: "(g has_real_derivative g' w) (at w within {0..1})" if "w \<in> {0..1}" for w
    unfolding g_def g'_def
    apply (insert that xy neq)
    apply (rule derivative_eq_intros refl)+
     apply (simp_all add: divide_simps power2_eq_square)
     apply (auto simp: algebra_simps)
    done
  have "continuous_on {0..1} (\<lambda>xa. (1 - xa) ^ n / (1 - (1 - x * y) * xa))"
    using neq by (auto intro!: continuous_intros)
  moreover have "g ` {0..1} \<subseteq> {0..1}"
  proof clarify
    fix w :: real assume w: "w \<in> {0..1}"
    have "(1 - x * y) * w \<le> 1 * w"
      using \<open>x * y < 1\<close> xy w by (intro mult_right_mono) auto
    thus "g w \<in> {0..1}"
      unfolding g_def using less[of w] w by (auto simp: divide_simps)
  qed
  ultimately have cont: "continuous_on (g ` {0..1}) (\<lambda>xa. (1 - xa) ^ n / (1 - (1 - x * y) * xa))"
    by (rule continuous_on_subset)
  have cont': "continuous_on {0..1} g'"
    using neq by (auto simp: g'_def intro!: continuous_intros)

  have "(LBINT w=0..1. (1-w)^n * (1-y)^n / (1-(1-x*y)*w)) =
          (1-y)^n * (LBINT w=0..1. (1 - w)^n / (1-(1-x*y)*w))"
    unfolding interval_lebesgue_integral_mult_right [symmetric]
    by (simp add: algebra_simps power_mult_distrib)
  also have "(LBINT w=0..1. (1 - w)^n / (1-(1-x*y)*w)) =
        -(LBINT w=g 0..g 1. (1 - w)^n / (1-(1-x*y)*w))"
    by (subst interval_integral_endpoints_reverse)(simp add: g_def zero_ereal_def one_ereal_def)
  also have "(LBINT w=g 0..g 1. (1 - w)^n / (1-(1-x*y)*w)) =
             (LBINT w=0..1. g' w * ((1 - g w) ^ n / (1 - (1-x*y) * g w)))"
    using deriv cont cont'
    by (subst interval_integral_substitution_finite [symmetric, where g = g and g' = g'])
       (simp_all add: zero_ereal_def one_ereal_def)
  also have "-\<dots> = (LBINT z=0..1. ((x*y)^n * z^n / (1-(1-x*y)*z)^(n+1)))"
    unfolding interval_lebesgue_integral_uminus [symmetric] using xy
    apply (intro interval_lebesgue_integral_lborel_01_cong)
    apply (simp add: divide_simps g_def g'_def)
    apply (auto simp: algebra_simps power_mult_distrib power2_eq_square)
    done
  also have "(1-y)^n * \<dots> = (LBINT z=0..1. (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1))"
    unfolding interval_lebesgue_integral_mult_right [symmetric]
    by (simp add: algebra_simps power_mult_distrib)
  finally show "\<dots> = (LBINT w=0..1. (1-w)^n * (1-y)^n / (1-(1-x*y)*w))" ..
qed

text \<open>
  Lastly, we apply the same integration by parts to \<open>x\<close>:
\<close>
lemma beukers_aux_integral_transform3:
  assumes w: "w \<in> {0<..<1}"
  shows   "(LBINT (x,y):D. P x * (1-y)^n / (1-(1-x*y)*w)) =
           (LBINT (x,y):D. (1-y)^n * (x*y*w)^n * (1-x)^n / (1-(1-x*y)*w)^(n+1))"
proof -
  have cbox: "cbox (0, 0) (1, 1) = ({0..1} \<times> {0..1} :: (real \<times> real) set)"
    by (auto simp: cbox_def Basis_prod_def inner_prod_def)
  have box: "box (0, 0) (1, 1) = ({0<..<1} \<times> {0<..<1} :: (real \<times> real) set)"
    by (auto simp: box_def Basis_prod_def inner_prod_def)

  have "set_integrable lborel
          (cbox (0,0) (1,1)) (\<lambda>(x,y). P x * (1-y)^n/(1-(1-x*y)*w))"
    unfolding lborel_prod case_prod_unfold P_def
  proof (intro continuous_on_imp_set_integrable_cbox continuous_intros ballI)
    fix p :: "real \<times> real" assume p: "p \<in> cbox (0,0) (1,1)"
    have "(1 - fst p * snd p) * w \<le> 1 * w"
      using p cbox w by (intro mult_right_mono) auto
    also have "\<dots> < 1" using w by simp
    finally have "(1 - fst p * snd p) * w < 1" by simp
    thus "1 - (1 - fst p * snd p) * w \<noteq> 0" by simp
  qed
  hence integrable: "set_integrable lborel D (\<lambda>(x,y). P x * (1-y)^n/(1-(1-x*y)*w))"
    by (rule set_integrable_subset) (auto simp: D_def simp flip: borel_prod)

  have "set_integrable lborel (cbox (0,0) (1,1))
          (\<lambda>(x,y). (1-y)^n * (x*y*w)^n * (1-x)^n / (1-(1-x*y)*w)^(n+1))"
    unfolding lborel_prod case_prod_unfold P_def
  proof (intro continuous_on_imp_set_integrable_cbox continuous_intros ballI)
    fix p :: "real \<times> real" assume p: "p \<in> cbox (0,0) (1,1)"
    have "(1 - fst p * snd p) * w \<le> 1 * w"
      using p cbox w by (intro mult_right_mono) auto
    also have "\<dots> < 1" using w by simp
    finally have "(1 - fst p * snd p) * w < 1" by simp
    thus "(1 - (1 - fst p * snd p) * w) ^ (n + 1) \<noteq> 0" by simp
  qed
  hence integrable': "set_integrable lborel D
                        (\<lambda>(x,y). (1-y)^n * (x*y*w)^n * (1-x)^n / (1-(1-x*y)*w)^(n+1))"
    by (rule set_integrable_subset) (auto simp: D_def simp flip: borel_prod)

  have "(LBINT (x,y):D. P x * (1-y)^n / (1-(1-x*y)*w)) =
          (LBINT y=0..1. (LBINT x=0..1. P x * (1-y)^n / (1-(1-x*y)*w)))"
    using integrable unfolding case_prod_unfold D_def lborel_prod [symmetric]
    by (subst lborel_pair.set_integral_snd) (auto simp: interval_integral_Ioo)
  also have "\<dots> = (LBINT y=0..1. (1-y)^n * (LBINT x=0..1. P x / (1-(1-y*x)*w)))"
    by (subst interval_lebesgue_integral_mult_right [symmetric]) (auto simp: mult_ac)
  also have "\<dots> = (LBINT y=0..1. (1-y)^n * (LBINT x=0..1. (x*y*w)^n * (1-x)^n / (1-(1-x*y)*w)^(n+1)))"
    using w by (intro interval_lebesgue_integral_lborel_01_cong, subst beukers_aux_by_parts) (auto simp: mult_ac)
  also have "\<dots> = (LBINT y=0..1. (LBINT x=0..1.
                     (1-y)^n * (x*y*w)^n * (1-x)^n / (1-(1-x*y)*w)^(n+1)))"
    by (subst interval_lebesgue_integral_mult_right [symmetric]) (auto simp: mult_ac)
  also have "\<dots> = (LBINT (x,y):D. (1-y)^n * (x*y*w)^n * (1-x)^n / (1-(1-x*y)*w)^(n+1))"
    using integrable' unfolding case_prod_unfold D_def lborel_prod [symmetric]
    by (subst lborel_pair.set_integral_snd) (auto simp: interval_integral_Ioo)
  finally show ?thesis .
qed

text \<open>
  We need to show the existence of some of these triple integrals.
\<close>
lemma beukers_aux_integrable1:
  "set_integrable lborel (({0<..<1} \<times> {0<..<1}) \<times> {0<..<1})
     (\<lambda>((x,y),z). P x * P y / (1-(1-x*y)*z))"
proof -
  have D [measurable]: "D \<in> sets (borel \<Otimes>\<^sub>M borel)"
    unfolding D_def by (simp flip: borel_prod)
  have "bounded (P ` {0..1})"
    unfolding P_def by (intro compact_imp_bounded compact_continuous_image continuous_intros) auto
  then obtain C where C: "\<And>x. x \<in> {0..1} \<Longrightarrow> norm (P x) \<le> C"
    unfolding bounded_iff by fast
  show ?thesis unfolding D'_def case_prod_unfold
  proof (subst lborel_prod [symmetric],
         intro lborel_pair.Fubini_set_integrable AE_I2 impI; clarsimp?)
    fix x y :: real
    assume xy: "x > 0" "x < 1" "y > 0" "y < 1"
    have "x * y < 1" using xy mult_strict_mono[of x 1 y 1] by simp
    show "set_integrable lborel {0<..<1} (\<lambda>z. P x * P y / (1-(1-x*y)*z))"
      by (rule set_integrable_subset[of _ "{0..1}"], rule borel_integrable_atLeastAtMost')
         (use \<open>x*y<1\<close> beukers_denom_neq[of x y] xy in \<open>auto intro!: continuous_intros simp: P_def\<close>)
  next
    have "set_integrable lborel D
             (\<lambda>(x,y). (\<integral>z\<in>{0<..<1}. norm (P x * P y / (1-(1-x*y)*z)) \<partial>lborel))"
    proof (rule set_integrable_bound[OF _ _ AE_I2]; clarify?)
      show "set_integrable lborel D (\<lambda>(x,y). C\<^sup>2 * (-ln (x*y) / (1 - x*y)))"
        using beukers_integral1_integrable[of 0 0]
        unfolding case_prod_unfold by (intro set_integrable_mult_right) (auto simp: D_def)
    next
      fix x y assume xy: "(x, y) \<in> D"
      have "norm (LBINT z:{0<..<1}. norm (P x * P y / (1-(1-x*y)*z))) =
              norm (LBINT z:{0<..<1}. \<bar>P x\<bar> * \<bar>P y\<bar> * (1 / (1-(1-x*y)*z)))"
      proof (intro arg_cong[where f = norm] set_lebesgue_integral_cong allI impI, goal_cases)
        case (2 z)
        with beukers_denom_ineq[of x y z] xy show ?case
          by (auto simp: abs_mult D_def)
      qed (auto simp: abs_mult D_def)
      also have "\<dots> = norm (\<bar>P x\<bar> * \<bar>P y\<bar> * (LBINT z=0..1. (1 / (1-(1-x*y)*z))))"
        by (subst set_integral_mult_right) (auto simp: interval_integral_Ioo)
      also have "\<dots> = norm (norm (P x) * norm (P y) * (- ln (x * y) / (1 - x * y)))"
        using beukers_aux_ln_conv_integral[of x y] xy by (simp add: D_def)
      also have "\<dots> = norm (P x) * norm (P y) * (- ln (x * y) / (1 - x * y))"
        using xy mult_strict_mono[of x 1 y 1]
        by (auto simp: D_def divide_nonpos_nonneg abs_mult)
      also have "norm (P x) * norm (P y) * (- ln (x * y) / (1 - x * y)) \<le>
                   norm (C * C * (- ln (x * y) / (1 - x * y)))"
        using xy C[of x] C[of y] mult_strict_mono[of x 1 y 1] unfolding norm_mult norm_divide
        by (intro mult_mono C) (auto simp: D_def divide_nonpos_nonneg)
      finally show "norm (LBINT z:{0<..<1}. norm (P x * P y / (1-(1-x*y)*z)))
           \<le> norm (case (x, y) of (x, y) \<Rightarrow> C\<^sup>2 * (- ln (x * y) / (1 - x * y)))"
        by (simp add: power2_eq_square mult_ac)
    next
      show "set_borel_measurable lborel D (\<lambda>(x, y).
              LBINT z:{0<..<1}. norm (P x * P y / (1 - (1 - x * y) * z)))"
        unfolding lborel_prod [symmetric] set_borel_measurable_def
                  case_prod_unfold set_lebesgue_integral_def P_def
        by measurable
    qed
    thus "set_integrable lborel ({0<..<1} \<times> {0<..<1})
            (\<lambda>x. LBINT y:{0<..<1}. \<bar>P (fst x) * P (snd x)\<bar> / \<bar>1 - (1 - fst x * snd x) * y\<bar>)"
      by (simp add: case_prod_unfold D_def)
  qed (auto simp: case_prod_unfold lborel_prod [symmetric] set_borel_measurable_def P_def)
qed

lemma beukers_aux_integrable2:
  "set_integrable lborel D' (\<lambda>(z,x,y). P x * (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z) ^ (n+1))"
proof -
  have [measurable]: "P \<in> borel_measurable borel" unfolding P_def
    by (intro borel_measurable_continuous_onI continuous_intros)
  have "bounded (P ` {0..1})"
    unfolding P_def by (intro compact_imp_bounded compact_continuous_image continuous_intros) auto
  then obtain C where C: "\<And>x. x \<in> {0..1} \<Longrightarrow> norm (P x) \<le> C"
    unfolding bounded_iff by fast
  show ?thesis unfolding D'_def
  proof (rule set_integrable_bound[OF _ _ AE_I2]; clarify?)
    show "set_integrable lborel ({0<..<1} \<times> {0<..<1} \<times> {0<..<1})
            (\<lambda>(z,x,y). C * (1 / (1-(1-x*y)*z)))"
      unfolding case_prod_unfold
      using beukers_integral1_integrable'[of 0 0]
      by (intro set_integrable_mult_right) (auto simp: lborel_prod case_prod_unfold)
  next
    fix x y z :: real assume xyz: "x \<in> {0<..<1}" "y \<in> {0<..<1}" "z \<in> {0<..<1}"
    have "norm (P x * (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1)) =
            norm (P x) * (1-y)^n * ((x*y*z) / (1-(1-x*y)*z))^n / (1-(1-x*y)*z)"
      using xyz beukers_denom_ineq[of x y z] by (simp add: abs_mult power_divide mult_ac)
    also have "(x*y*z) / (1-(1-x*y)*z) = 1/((1-z)/(z*x*y)+1)"
      using xyz by (simp add: field_simps)
    also have "norm (P x) * (1-y)^n * \<dots>^n / (1-(1-x*y)*z) \<le>
               C * 1^n * 1^n / (1-(1-x*y)*z)"
      using xyz C[of x] beukers_denom_ineq[of x y z]
      by (intro mult_mono divide_right_mono power_mono zero_le_power mult_nonneg_nonneg divide_nonneg_nonneg)
         (auto simp: field_simps)
    also have "\<dots> \<le> \<bar>C * 1^n * 1^n / (1-(1-x*y)*z)\<bar>"
      by linarith
    finally show "norm (P x * (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1)) \<le>
                    norm (case (z,x,y) of (z,x,y) \<Rightarrow> C * (1 / (1-(1-x*y)*z)))"
      by (simp add: case_prod_unfold)
  qed (simp_all add: case_prod_unfold set_borel_measurable_def flip: borel_prod)
qed

lemma beukers_aux_integrable3:
  "set_integrable lborel D' (\<lambda>(w,x,y). P x * (1-w)^n * (1-y)^n / (1-(1-x*y)*w))"
proof -
  have [measurable]: "P \<in> borel_measurable borel" unfolding P_def
    by (intro borel_measurable_continuous_onI continuous_intros)
  have "bounded (P ` {0..1})"
    unfolding P_def by (intro compact_imp_bounded compact_continuous_image continuous_intros) auto
  then obtain C where C: "\<And>x. x \<in> {0..1} \<Longrightarrow> norm (P x) \<le> C"
    unfolding bounded_iff by fast
  show ?thesis unfolding D'_def
  proof (rule set_integrable_bound[OF _ _ AE_I2]; clarify?)
    show "set_integrable lborel ({0<..<1} \<times> {0<..<1} \<times> {0<..<1})
            (\<lambda>(z,x,y). C * (1 / (1-(1-x*y)*z)))"
      unfolding case_prod_unfold
      using beukers_integral1_integrable'[of 0 0]
      by (intro set_integrable_mult_right) (auto simp: lborel_prod case_prod_unfold)
  next
    fix x y w :: real assume xyw: "x \<in> {0<..<1}" "y \<in> {0<..<1}" "w \<in> {0<..<1}"
    have "norm (P x * (1-w)^n * (1-y)^n / (1-(1-x*y)*w)) =
            norm (P x) * (1-w)^n * (1-y)^n / (1-(1-x*y)*w)"
      using xyw beukers_denom_ineq[of x y w] by (simp add: abs_mult power_divide mult_ac)
    also have "\<dots> \<le> C * 1^n * 1^n / (1-(1-x*y)*w)"
      using xyw C[of x] beukers_denom_ineq[of x y w]
      by (intro mult_mono divide_right_mono power_mono zero_le_power mult_nonneg_nonneg divide_nonneg_nonneg)
         (auto simp: field_simps)
    also have "\<dots> \<le> \<bar>C * 1^n * 1^n / (1-(1-x*y)*w)\<bar>"
      by linarith
    finally show "norm (P x * (1-w)^n * (1-y)^n / (1-(1-x*y)*w)) \<le>
                    norm (case (w,x,y) of (z,x,y) \<Rightarrow> C * (1 / (1-(1-x*y)*z)))"
      by (simp add: case_prod_unfold)
  qed (simp_all add: case_prod_unfold set_borel_measurable_def flip: borel_prod)
qed

text \<open>
  Now we only need to put all of these results together:
\<close>
lemma beukers_integral2_conv_3: "beukers_integral2 = beukers_integral3"
proof -
  have cont_P: "continuous_on {0..1} P"
    by (auto simp: P_def intro: continuous_intros)
  have D [measurable]: "D \<in> sets borel" "D \<in> sets (borel \<Otimes>\<^sub>M borel)"
    unfolding D_def by (simp_all flip: borel_prod)
  have [measurable]: "P \<in> borel_measurable borel" unfolding P_def
    by (intro borel_measurable_continuous_onI continuous_intros)

  have "beukers_integral2 = (LBINT (x,y):D. P x * P y * (LBINT z=0..1. 1 / (1-(1-x*y)*z)))"
    unfolding beukers_integral2_def case_prod_unfold
    by (intro set_lebesgue_integral_cong allI impI, measurable)
       (subst beukers_aux_ln_conv_integral, auto simp: D_def)
  also have "\<dots> = (LBINT (x,y):D. (LBINT z=0..1. P x * P y / (1-(1-x*y)*z)))"
      by (subst interval_lebesgue_integral_mult_right [symmetric]) auto
  also have "\<dots> = (LBINT (x,y):D. (LBINT z:{0<..<1}. P x * P y / (1-(1-x*y)*z)))"
    by (simp add: interval_integral_Ioo)
  also have "\<dots> = (LBINT z:{0<..<1}. (LBINT (x,y):D. P x * P y / (1-(1-x*y)*z)))"
  proof (subst lborel_pair.Fubini_set_integral [symmetric])
    have "set_integrable lborel (({0<..<1} \<times> {0<..<1}) \<times> {0<..<1})
            (\<lambda>((x, y), z). P x * P y / (1 - (1 - x * y) * z))"
      using beukers_aux_integrable1 by simp
    also have "?this \<longleftrightarrow> set_integrable (lborel \<Otimes>\<^sub>M lborel) ({0<..<1} \<times> D)
                           (\<lambda>(z,x,y). P x * P y / (1 - (1 - x * y) * z))"
      unfolding set_integrable_def
      by (subst lborel_pair.integrable_product_swap_iff [symmetric], intro integrable_cong)
         (auto simp: indicator_def case_prod_unfold lborel_prod D_def)
    finally show \<dots> .
  qed (auto simp: case_prod_unfold)
  also have "\<dots> = (LBINT z:{0<..<1}. (LBINT (x,y):D. P x * (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1)))"
    by (rule set_lebesgue_integral_cong) (use beukers_aux_integral_transform1 in simp_all)
  also have "\<dots> = (LBINT (x,y):D. (LBINT z:{0<..<1}. P x * (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1)))"
    using beukers_aux_integrable2
    by (subst lborel_pair.Fubini_set_integral [symmetric])
       (auto simp: case_prod_unfold lborel_prod D_def D'_def)
  also have "\<dots> = (LBINT (x,y):D. (LBINT w:{0<..<1}. P x * (1-w)^n * (1-y)^n / (1-(1-x*y)*w)))"
  proof (intro set_lebesgue_integral_cong allI impI; clarify?)
    fix x y :: real
    assume xy: "(x, y) \<in> D"
    have "(LBINT z:{0<..<1}. P x * (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1)) =
            P x * (LBINT z=0..1. (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1))"
      by (subst interval_lebesgue_integral_mult_right [symmetric])
         (simp add: mult_ac interval_integral_Ioo)
    also have "\<dots> = P x * (LBINT w=0..1. (1-w)^n * (1-y)^n / (1-(1-x*y)*w))"
      using xy by (subst beukers_aux_integral_transform2) (auto simp: D_def)
    also have "\<dots> = (LBINT w:{0<..<1}. P x * (1-w)^n * (1-y)^n / (1-(1-x*y)*w))"
      by (subst interval_lebesgue_integral_mult_right [symmetric])
         (simp add: mult_ac interval_integral_Ioo)
    finally show "(LBINT z:{0<..<1}. P x * (x*y*z)^n * (1-y)^n / (1-(1-x*y)*z)^(n+1)) =
                    (LBINT w:{0<..<1}. P x * (1-w)^n * (1-y)^n / (1-(1-x*y)*w))" .
  qed (auto simp: D_def simp flip: borel_prod)
  also have "\<dots> = (LBINT w:{0<..<1}. (LBINT (x,y):D. P x * (1-w)^n * (1-y)^n / (1-(1-x*y)*w)))"
    using beukers_aux_integrable3
    by (subst lborel_pair.Fubini_set_integral [symmetric])
       (auto simp: case_prod_unfold lborel_prod D_def D'_def)
  also have "\<dots> = (LBINT w=0..1. (1-w)^n * (LBINT (x,y):D. P x * (1-y)^n / (1-(1-x*y)*w)))"
    unfolding case_prod_unfold
    by (subst set_integral_mult_right [symmetric]) (simp add: mult_ac interval_integral_Ioo)
  also have "\<dots> = (LBINT w=0..1. (1-w)^n * (LBINT (x,y):D. (x*y*w*(1-x)*(1-y))^n / (1-(1-x*y)*w)^(n+1)))"
    by (intro interval_lebesgue_integral_lborel_01_cong, subst beukers_aux_integral_transform3)
       (auto simp: mult_ac power_mult_distrib)
  also have "\<dots> = (LBINT w=0..1. (LBINT (x,y):D. (x*y*w*(1-x)*(1-y)*(1-w))^n / (1-(1-x*y)*w)^(n+1)))"
    by (subst set_integral_mult_right [symmetric])
       (auto simp: case_prod_unfold mult_ac power_mult_distrib)
  also have "\<dots> = beukers_integral3"
    using beukers_integral3_integrable unfolding D'_def D_def beukers_integral3_def
    by (subst (2) lborel_prod [symmetric], subst lborel_pair.set_integral_fst')
       (auto simp: case_prod_unfold interval_integral_Ioo lborel_prod algebra_simps)
  finally show ?thesis .
qed


subsection \<open>The main result\<close>

text \<open>
  Combining all of the results so far, we can derive the key inequalities
  \[0 < A\zeta(3) + B < 2 \zeta(3) \cdot 27^{-n} \cdot \text{lcm}\{1\ldots n\}^3\]
  for integers $A$, $B$ with $A > 0$.
\<close>
lemma zeta_3_linear_combination_bounds:
  obtains A B :: int
  where "A > 0"
        "A * Re (zeta 3) + B \<in> {0 <.. 2 * Re (zeta 3) * Lcm {1..n} ^ 3 / 27 ^ n}"
proof -
  define I where "I = beukers_integral2"
  define d where "d = Lcm {1..n} ^ 3"
  have "d > 0" by (auto simp: d_def intro!: Nat.gr0I)
  from beukers_integral2_conv_int_combination obtain A' B :: int
    where *: "A' > 0" "I = A' * Re (zeta 3) + B / d" unfolding I_def d_def .
  define A where "A = A' * d"
  from * have A: "A > 0" "I = (A * Re (zeta 3) + B) / d"
    using \<open>d > 0\<close> by (simp_all add: A_def field_simps)

  have "0 < I"
    using beukers_integral3_pos by (simp add: I_def beukers_integral2_conv_3)
  with \<open>d > 0\<close> have "A * Re (zeta 3) + B > 0"
    by (simp add: field_simps A)

  moreover have "I \<le> 2 * (1 / 27) ^ n * Re (zeta 3)"
    using beukers_integral2_conv_3 beukers_integral3_le by (simp add: I_def)
  hence "A * Re (zeta 3) + B \<le> 2 * Re (zeta 3) * d / 27 ^ n"
    using \<open>d > 0\<close> by (simp add: A field_simps)

  ultimately show ?thesis
    using A by (intro that[of A B]) (auto simp: d_def)
qed

text \<open>
  If $\zeta(3) = \frac{a}{b}$ for some integers $a$ and $b$, we can thus derive
  the inequality $2b\zeta(3) \cdot 27^{-n} \cdot \text{lcm}\{1\ldots n\}^3\geq 1$ for any
  natural number $n$.
\<close>
lemma beukers_key_inequality:
  fixes a :: int and b :: nat
  assumes "b > 0" and ab: "Re (zeta 3) = a / b"
  shows   "2 * b * Re (zeta 3) * Lcm {1..n} ^ 3 / 27 ^ n \<ge> 1"
proof -
  from zeta_3_linear_combination_bounds obtain A B :: int
    where AB: "A > 0"
              "A * Re (zeta 3) + B \<in> {0 <.. 2 * Re (zeta 3) * Lcm {1..n} ^ 3 / 27 ^ n}" .
  from AB have "0 < (A * Re (zeta 3) + B) * b"
    using \<open>b > 0\<close> by (intro mult_pos_pos) auto
  also have "\<dots> = A * (Re (zeta 3) * b) + B * b"
    using \<open>b > 0\<close> by (simp add: algebra_simps)
  also have "Re (zeta 3) * b = a"
    using \<open>b > 0\<close> by (simp add: ab)
  also have "of_int A * of_int a + of_int (B * b) = of_int (A * a + B * b)"
    by simp
  finally have "1 \<le> A * a + B * b"
    by linarith
  hence "1 \<le> real_of_int (A * a + B * b)"
    by linarith
  also have "\<dots> = (A * (a / b) + B) * b"
    using \<open>b > 0\<close> by (simp add: ring_distribs)
  also have "a / b = Re (zeta 3)"
    by (simp add: ab)
  also have "A * Re (zeta 3) + B \<le> 2 * Re (zeta 3) * Lcm {1..n} ^ 3 / 27 ^ n"
    using AB by simp
  finally show "2 * b * Re (zeta 3) * Lcm {1..n} ^ 3 / 27 ^ n \<ge> 1"
    using \<open>b > 0\<close> by (simp add: mult_ac)
qed

end

(* TODO: Move *)
lemma smallo_power: "n > 0 \<Longrightarrow> f \<in> o[F](g) \<Longrightarrow> (\<lambda>x. f x ^ n) \<in> o[F](\<lambda>x. g x ^ n)"
  by (induction n rule: nat_induct_non_zero) (auto intro: landau_o.small.mult)

text \<open>
  This is now a contradiction, since $\text{lcm}\{1\ldots n\} \in o(3^n)$ by the
  Prime Number Theorem -- hence the main result.
\<close>
theorem zeta_3_irrational: "zeta 3 \<notin> \<rat>"
proof
  assume "zeta 3 \<in> \<rat>"
  obtain a :: int and b :: nat where "b > 0" and ab': "zeta 3 = a / b"
  proof -
    from \<open>zeta 3 \<in> \<rat>\<close> obtain r where r: "zeta 3 = of_rat r"
      by (elim Rats_cases)
    also have "r = rat_of_int (fst (quotient_of r)) / rat_of_int (snd (quotient_of r))"
      by (intro quotient_of_div) auto
    also have "of_rat \<dots> = (of_int (fst (quotient_of r)) / of_int (snd (quotient_of r)) :: complex)"
      by (simp add: of_rat_divide)
    also have "of_int (snd (quotient_of r)) = of_nat (nat (snd (quotient_of r)))"
      using quotient_of_denom_pos'[of r] by auto
    finally have "zeta 3 = of_int (fst (quotient_of r)) / of_nat (nat (snd (quotient_of r)))" .
    thus ?thesis
      using quotient_of_denom_pos'[of r]
      by (intro that[of "nat (snd (quotient_of r))" "fst (quotient_of r)"]) auto
  qed
  hence ab: "Re (zeta 3) = a / b" by simp

  interpret prime_number_theorem
    by standard (rule prime_number_theorem)

  have Lcm_upto_smallo: "(\<lambda>n. real (Lcm {1..n})) \<in> o(\<lambda>n. c ^ n)" if c: "c > exp 1" for c
  proof -
    have "0 < exp (1::real)" by simp
    also note c
    finally have "c > 0" .
    have "(\<lambda>n. real (Lcm {1..n})) = (\<lambda>n. real (Lcm {1..nat \<lfloor>real n\<rfloor>}))"
      by simp
    also have "\<dots> \<in> o(\<lambda>n. c powr real n)"
      using Lcm_upto.smallo'
      by (rule landau_o.small.compose) (simp_all add: c filterlim_real_sequentially)
    also have "(\<lambda>n. c powr real n) = (\<lambda>n. c ^ n)"
      using c \<open>c > 0\<close> by (subst powr_realpow) auto
    finally show ?thesis .
  qed

  have "(\<lambda>n. 2 * b * Re (zeta 3) * real (Lcm {1..n}) ^ 3 / 27 ^ n) \<in>
          O(\<lambda>n. real (Lcm {1..n}) ^ 3 / 27 ^ n)"
    using \<open>b > 0\<close> Re_zeta_ge_1[of 3] by simp
  also have "exp 1 < (3 :: real)"
    using e_approx_32 by (simp add: abs_if split: if_splits)
  hence "(\<lambda>n. real (Lcm {1..n}) ^ 3 / 27 ^ n) \<in> o(\<lambda>n. (3 ^ n) ^ 3 / 27 ^ n)"
    unfolding of_nat_power
    by (intro landau_o.small.divide_right smallo_power Lcm_upto_smallo) auto
  also have "(\<lambda>n. (3 ^ n) ^ 3 / 27 ^ n :: real) = (\<lambda>_. 1)"
    by (simp add: power_mult [of 3, symmetric] mult.commute[of _ 3] power_mult[of _ 3])
  finally have *: "(\<lambda>n. 2 * b * Re (zeta 3) * real (Lcm {1..n}) ^ 3 / 27 ^ n) \<in> o(\<lambda>_. 1)" .
  have lim: "(\<lambda>n. 2 * b * Re (zeta 3) * real (Lcm {1..n}) ^ 3 / 27 ^ n) \<longlonglongrightarrow> 0"
    using smalloD_tendsto[OF *] by simp

  moreover have "1 \<le> real (2 * b) * Re (zeta 3) * real (Lcm {1..n} ^ 3) / 27 ^ n" for n
    using beukers_key_inequality[of b a] ab \<open>b > 0\<close> by simp

  ultimately have "1 \<le> (0 :: real)"
    by (intro tendsto_lowerbound[OF lim] always_eventually allI) auto
  thus False by simp
qed

end