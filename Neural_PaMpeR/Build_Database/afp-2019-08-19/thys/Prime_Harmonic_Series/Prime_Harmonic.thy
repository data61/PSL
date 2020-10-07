(*
  File:   Prime_Harmonic.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  A lower bound for the partial sums of the prime harmonic series, and a proof of its divergence.
  (#81 on the list of 100 mathematical theorems)
*)

section \<open>The Prime Harmonic Series\<close>
theory Prime_Harmonic
imports
  "HOL-Analysis.Analysis"
  "HOL-Number_Theory.Number_Theory"
  Prime_Harmonic_Misc
  Squarefree_Nat
begin

subsection \<open>Auxiliary equalities and inequalities\<close>

text \<open>
  First of all, we prove the following result about rearranging a product over a set into a sum
  over all subsets of that set.
\<close>
lemma prime_harmonic_aux1:
  fixes A :: "'a :: field set"
  shows "finite A \<Longrightarrow> (\<Prod>x\<in>A. 1 + 1 / x) = (\<Sum>x\<in>Pow A. 1 / \<Prod>x)"
proof (induction rule: finite_induct)
  fix a :: 'a and A :: "'a set"
  assume a: "a \<notin> A" and fin: "finite A"
  assume IH: "(\<Prod>x\<in>A. 1 + 1 / x) = (\<Sum>x\<in>Pow A. 1 / \<Prod>x)"
  from a and fin have "(\<Prod>x\<in>insert a A. 1 + 1 / x) = (1 + 1 / a) * (\<Prod>x\<in>A. 1 + 1 / x)" by simp
  also from fin have "\<dots> = (\<Sum>x\<in>Pow A. 1 / \<Prod>x) + (\<Sum>x\<in>Pow A. 1 / (a * \<Prod>x))"
    by (subst IH) (auto simp add: algebra_simps sum_divide_distrib)
  also from fin a have "(\<Sum>x\<in>Pow A. 1 / (a * \<Prod>x)) = (\<Sum>x\<in>Pow A. 1 / \<Prod>(insert a x))"
    by (intro sum.cong refl, subst prod.insert) (auto dest: finite_subset)
  also from a have "\<dots> = (\<Sum>x\<in>insert a ` Pow A. 1 / \<Prod>x)"
    by (subst sum.reindex) (auto simp: inj_on_def)
  also from fin a have "(\<Sum>x\<in>Pow A. 1 / \<Prod>x) + \<dots> = (\<Sum>x\<in>Pow A \<union> insert a ` Pow A. 1 / \<Prod>x)"
    by (intro sum.union_disjoint [symmetric]) (simp, simp, blast)
  also have "Pow A \<union> insert a ` Pow A = Pow (insert a A)" by (simp only: Pow_insert)
  finally show " (\<Prod>x\<in>insert a A. 1 + 1 / x) = (\<Sum>x\<in>Pow (insert a A). 1 / \<Prod>x)" .
qed simp

text \<open>
  Next, we prove a simple and reasonably accurate upper bound for the sum of the squares of any
  subset of the natural numbers, derived by simple telescoping. Our upper bound is approximately
  1.67; the exact value is $\frac{\pi^2}{6} \approx 1.64$. (cf. Basel problem)
\<close>
lemma prime_harmonic_aux2:
  assumes "finite (A :: nat set)"
  shows   "(\<Sum>k\<in>A. 1 / (real k ^ 2)) \<le> 5/3"
proof -
  define n where "n = max 2 (Max A)"
  have n: "n \<ge> Max A" "n \<ge> 2" by (auto simp: n_def)
  with assms have "A \<subseteq> {0..n}" by (auto intro: order.trans[OF Max_ge])
  hence "(\<Sum>k\<in>A. 1 / (real k ^ 2)) \<le> (\<Sum>k=0..n. 1 / (real k ^ 2))" by (intro sum_mono2) auto
  also from n have "\<dots> = 1 + (\<Sum>k=Suc 1..n. 1 / (real k ^ 2))" by (simp add: sum.atLeast_Suc_atMost)
  also have "(\<Sum>k=Suc 1..n. 1 / (real k ^ 2)) \<le>
          (\<Sum>k=Suc 1..n. 1 / (real k ^ 2 - 1/4))" unfolding power2_eq_square
    by (intro sum_mono divide_left_mono mult_pos_pos)
       (linarith, simp_all add: field_simps less_1_mult)
  also have "\<dots> = (\<Sum>k=Suc 1..n. 1 / (real k - 1/2) - 1 / (real (Suc k) - 1/2))"
    by (intro sum.cong refl) (simp_all add: field_simps power2_eq_square)
  also from n have "\<dots> = 2 / 3 - 1 / (1 / 2 + real n)"
    by (subst sum_telescope') simp_all
  also have "1 + \<dots> \<le> 5/3" by simp
  finally show ?thesis by - simp
qed


subsection \<open>Estimating the partial sums of the Prime Harmonic Series\<close>

text \<open>
  We are now ready to show our main result: the value of the partial prime harmonic sum over
  all primes no greater than $n$ is bounded from below by the $n$-th harmonic number
  $H_n$ minus some constant.

  In our case, this constant will be $\frac{5}{3}$. As mentioned before, using a
  proof of the Basel problem can improve this to $\frac{\pi^2}{6}$, but the improvement is very
  small and the proof of the Basel problem is a very complex one.

  The exact asymptotic behaviour of the partial sums is actually $\ln (\ln n) + M$, where $M$
  is the Meissel--Mertens constant (approximately 0.261).
\<close>
theorem prime_harmonic_lower:
  assumes n: "n \<ge> 2"
  shows "(\<Sum>p\<leftarrow>primes_upto n. 1 / real p) \<ge> ln (harm n) - ln (5/3)"
proof -
  \<comment> \<open>the set of primes that we will allow in the squarefree part\<close>
  define P where "P n = set (primes_upto n)" for n
  {
    fix n :: nat
    have "finite (P n)" by (simp add: P_def)
  } note [simp] = this

  \<comment> \<open>The function that combines the squarefree part and the square part\<close>
  define f where "f = (\<lambda>(R, s :: nat). \<Prod>R * s^2)"

  \<comment> \<open>@{term f} is injective if the squarefree part contains only primes
      and the square part is positive.\<close>
  have inj: "inj_on f (Pow (P n)\<times>{1..n})"
  proof (rule inj_onI, clarify, rule conjI)
    fix A1 A2 :: "nat set" and s1 s2 :: nat
    assume A: "A1 \<subseteq> P n" "A2 \<subseteq> P n" "s1 \<in> {1..n}" "s2 \<in> {1..n}" "f (A1, s1) = f (A2, s2)"
    have fin: "finite A1" "finite A2" by (rule A(1,2)[THEN finite_subset], simp)+
    show "A1 = A2" "s1 = s2"
      by ((rule squarefree_decomposition_unique2'[of A1 s1 A2 s2],
          insert A fin, auto simp: f_def P_def set_primes_upto)[])+
  qed

  \<comment> \<open>@{term f} hits every number between @{term "1::nat"} and @{term "n"}. It also hits a lot
      of other numbers, but we do not care about those, since we only need a lower bound.\<close>
  have surj: "{1..n} \<subseteq> f ` (Pow (P n)\<times>{1..n})"
  proof
    fix x assume x: "x \<in> {1..n}"
    have "x = f (squarefree_part x, square_part x)" by (simp add: f_def squarefree_decompose)
    moreover have "squarefree_part x \<in> Pow (P n)" using squarefree_part_subset[of x] x
      by (auto simp: P_def set_primes_upto intro: order.trans[OF squarefree_part_le[of _ x]])
    moreover have "square_part x \<in> {1..n}" using x
      by (auto simp: Suc_le_eq intro: order.trans[OF square_part_le[of x]])
    ultimately show "x \<in> f ` (Pow (P n)\<times>{1..n})" by simp
  qed

  \<comment> \<open>We now show the main result by rearranging the sum over all primes to a product over all
      all squarefree parts times a sum over all square parts, and then applying some simple-minded
      approximation\<close>
  have "harm n = (\<Sum>n=1..n. 1 / real n)" by (simp add: harm_def field_simps)
  also from surj have "\<dots> \<le> (\<Sum>n\<in>f ` (Pow (P n)\<times>{1..n}). 1 / real n)"
    by (intro sum_mono2 finite_imageI finite_cartesian_product) simp_all
  also from inj have "\<dots> = (\<Sum>x\<in>Pow (P n)\<times>{1..n}. 1 / real (f x))"
    by (subst sum.reindex) simp_all
  also have "\<dots> = (\<Sum>A\<in>Pow (P n). 1 / real (\<Prod>A)) * (\<Sum>k=1..n. 1 / (real k)^2)" unfolding f_def
    by (subst sum_product, subst sum.cartesian_product) (simp add: case_prod_beta)
  also have "\<dots> \<le> (\<Sum>A\<in>Pow (P n). 1 / real (\<Prod>A)) * (5/3)"
    by (intro mult_left_mono prime_harmonic_aux2 sum_nonneg)
       (auto simp: P_def intro!: prod_nonneg)
  also have "(\<Sum>A\<in>Pow (P n). 1 / real (\<Prod>A)) = (\<Sum>A\<in>((`) real) ` Pow (P n). 1 / \<Prod>A)"
    by (subst sum.reindex) (auto simp: inj_on_def inj_image_eq_iff prod.reindex)
  also have "((`) real) ` Pow (P n) = Pow (real ` P n)" by (intro image_Pow_surj refl)
  also have "(\<Sum>A\<in>Pow (real ` P n). 1 / \<Prod>A) = (\<Prod>x\<in>real ` P n. 1 + 1 / x)"
    by (intro prime_harmonic_aux1 [symmetric] finite_imageI) simp_all
  also have "\<dots> = (\<Prod>i\<in>P n. 1 + 1 / real i)" by (subst prod.reindex) (auto simp: inj_on_def)
  also have "\<dots> \<le> (\<Prod>i\<in>P n. exp (1 / real i))" by (intro prod_mono) auto
  also have "\<dots> = exp (\<Sum>i\<in>P n. 1 / real i)" by (simp add: exp_sum)
  finally have "ln (harm n) \<le> ln (\<dots> * (5/3))" using n
    by (subst ln_le_cancel_iff) simp_all
  hence "ln (harm n) - ln (5/3) \<le> (\<Sum>i\<in>P n. 1 / real i)"
    by (subst (asm) ln_mult) (simp_all add: algebra_simps)
  thus ?thesis unfolding P_def
    by (subst (asm) sum.distinct_set_conv_list) simp_all
qed

text \<open>
  We can use the inequality $\ln (n + 1) \le H_n$ to estimate the asymptotic growth of the partial
  prime harmonic series. Note that $H_n \sim \ln n + \gamma$ where $\gamma$ is the
  Euler--Mascheroni constant (approximately 0.577), so we lose some accuracy here.
\<close>
corollary prime_harmonic_lower':
  assumes n: "n \<ge> 2"
  shows "(\<Sum>p\<leftarrow>primes_upto n. 1 / real p) \<ge> ln (ln (n + 1)) - ln (5/3)"
proof -
  from assms ln_le_harm[of n] have "ln (ln (real n + 1)) \<le> ln (harm n)" by simp
  also from assms have "\<dots> - ln (5/3) \<le> (\<Sum>p\<leftarrow>primes_upto n. 1 / real p)"
    by (rule prime_harmonic_lower)
  finally show ?thesis by - simp
qed


(* TODO: Not needed in Isabelle 2016 *)
lemma Bseq_eventually_mono:
  assumes "eventually (\<lambda>n. norm (f n) \<le> norm (g n)) sequentially" "Bseq g"
  shows   "Bseq f"
proof -
  from assms(1) obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> norm (f n) \<le> norm (g n)"
    by (auto simp: eventually_at_top_linorder)
  from assms(2) obtain K where K: "\<And>n. norm (g n) \<le> K" by (blast elim!: BseqE)
  {
    fix n :: nat
    have "norm (f n) \<le> max K (Max {norm (f n) |n. n < N})"
      apply (cases "n < N")
      apply (rule max.coboundedI2, rule Max.coboundedI, auto) []
      apply (rule max.coboundedI1, force intro: order.trans[OF N K])
      done
  }
  thus ?thesis by (blast intro: BseqI')
qed

lemma Bseq_add:
  assumes "Bseq (f :: nat \<Rightarrow> 'a :: real_normed_vector)"
  shows   "Bseq (\<lambda>x. f x + c)"
proof -
  from assms obtain K where K: "\<And>x. norm (f x) \<le> K" unfolding Bseq_def by blast
  {
    fix x :: nat
    have "norm (f x + c) \<le> norm (f x) + norm c" by (rule norm_triangle_ineq)
    also have "norm (f x) \<le> K" by (rule K)
    finally have "norm (f x + c) \<le> K + norm c" by simp
  }
  thus ?thesis by (rule BseqI')
qed

lemma convergent_imp_Bseq: "convergent f \<Longrightarrow> Bseq f"
  by (simp add: Cauchy_Bseq convergent_Cauchy)

(* END TODO *)

text \<open>
  We now use our last estimate to show that the prime harmonic series diverges. This is obvious,
  since it is bounded from below by $\ln (\ln (n + 1))$ minus some constant, which obviously
  tends to infinite.

  Directly using the divergence of the harmonic series would also be possible and shorten this
  proof a bit..
\<close>
corollary prime_harmonic_series_unbounded:
  "\<not>Bseq (\<lambda>n. \<Sum>p\<leftarrow>primes_upto n. 1 / p)" (is "\<not>Bseq ?f")
proof
  assume "Bseq ?f"
  hence "Bseq (\<lambda>n. ?f n + ln (5/3))" by (rule Bseq_add)
  have "Bseq (\<lambda>n. ln (ln (n + 1)))"
  proof (rule Bseq_eventually_mono)
    from eventually_ge_at_top[of "2::nat"]
      show "eventually (\<lambda>n. norm (ln (ln (n + 1))) \<le> norm (?f n + ln (5/3))) sequentially"
    proof eventually_elim
      fix n :: nat assume n: "n \<ge> 2"
      hence "norm (ln (ln (real n + 1))) = ln (ln (real n + 1))"
        using ln_ln_nonneg[of "real n + 1"] by simp
      also have "\<dots> \<le> ?f n + ln (5/3)" using prime_harmonic_lower'[OF n]
        by (simp add: algebra_simps)
      also have "?f n + ln (5/3) \<ge> 0" by (intro add_nonneg_nonneg sum_list_nonneg) simp_all
      hence "?f n + ln (5/3) = norm (?f n + ln (5/3))" by simp
      finally show "norm (ln (ln (n + 1))) \<le> norm (?f n + ln (5/3))"
        by (simp add: add_ac)
    qed
  qed fact
  then obtain k where k: "k > 0" "\<And>n. norm (ln (ln (real (n::nat) + 1))) \<le> k"
    by (auto elim!: BseqE simp: add_ac)

  define N where "N = nat \<lceil>exp (exp k)\<rceil>"
  have N_pos: "N > 0" unfolding N_def by simp
  have "real N + 1 > exp (exp k)" unfolding N_def by linarith
  hence "ln (real N + 1) > ln (exp (exp k))" by (subst ln_less_cancel_iff) simp_all
  with N_pos have "ln (ln (real N + 1)) > ln (exp k)" by (subst ln_less_cancel_iff) simp_all
  hence "k < ln (ln (real N + 1))" by simp
  also have "\<dots> \<le> norm (ln (ln (real N + 1)))" by simp
  finally show False using k(2)[of N] by simp
qed

corollary prime_harmonic_series_diverges:
  "\<not>convergent (\<lambda>n. \<Sum>p\<leftarrow>primes_upto n. 1 / p)"
  using prime_harmonic_series_unbounded convergent_imp_Bseq by blast

end
