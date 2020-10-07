(*
  File:     Dirichlet_Theorem.thy
  Author:   Manuel Eberl, TU München
*)
section \<open>Dirichlet's Theorem on primes in arithmetic progressions\<close>
theory Dirichlet_Theorem
imports
  Dirichlet_L_Functions
  Bertrands_Postulate.Bertrand
  Landau_Symbols.Landau_More
begin

text \<open>
  We can now turn to the proof of the main result: Dirichlet's theorem about the infinitude
  of primes in arithmetic progressions.

  There are previous proofs of this by John Harrison in HOL Light~\cite{harrison-dirichlet} and 
  by Mario Carneiro in Metamath~\cite{carneiro16}. Both of them strive to prove Dirichlet's
  theorem with a minimum amount of auxiliary results and definitions, whereas our goal was to
  get a short and simple proof of Dirichlet's theorem built upon a large library of Analytic
  Number Theory.

  At this point, we already have the key part -- the non-vanishing of $L(1,\chi)$
  -- and the proof was relatively simple and straightforward due to the large amount of Complex
  Analysis and Analytic Number Theory we have available. The remainder will be a bit more concrete,
  but still reasonably concise.

  First, we need to re-frame some of the results from the AFP entry about Bertrand's postulate a 
  little bit.
\<close>

subsection \<open>Auxiliary results\<close>

text \<open>
  The AFP entry for Bertrand's postulate already provides a slightly stronger version of
  this for integer values of $x$, but we can easily extend this to real numbers to obtain
  a slightly nicer presentation.
\<close>
lemma sum_upto_mangoldt_le: 
  assumes "x \<ge> 0"
  shows   "sum_upto mangoldt x \<le> 3 / 2 * x"
proof -
  have "sum_upto mangoldt x = psi (nat \<lfloor>x\<rfloor>)"
    by (simp add: sum_upto_altdef psi_def atLeastSucAtMost_greaterThanAtMost)
  also have "\<dots> \<le> 551 / 256 * ln 2 * real (nat \<lfloor>x\<rfloor>)"
    by (rule psi_ubound_log)
  also have "\<dots> \<le> 3 / 2 * real (nat \<lfloor>x\<rfloor>)"
    using Bertrand.ln_2_le by (intro mult_right_mono) auto
  also have "\<dots> \<le> 3 / 2 * x" using assms by linarith
  finally show ?thesis .
qed

text \<open>
  We can also, similarly, use the results from the Bertrand's postulate entry to show
  that the sum of $\ln p / p$ over all primes grows logarithmically.
\<close>
lemma Mertens_bigo:
  "(\<lambda>x. (\<Sum>p | prime p \<and> real p \<le> x. ln p / p) - ln x) \<in> O(\<lambda>_. 1)"
proof (intro bigoI[of _ 8] eventually_mono[OF eventually_gt_at_top[of 1]], goal_cases)
  case (1 x)
  have "\<bar>(\<Sum>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. ln p / p) - ln x\<bar> =
          \<bar>(\<Sum>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. ln p / p) - ln (nat \<lfloor>x\<rfloor>) - (ln x - ln (nat \<lfloor>x\<rfloor>))\<bar>"
    by simp
  also have "\<dots> \<le> \<bar>(\<Sum>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. ln p / p) - ln (nat \<lfloor>x\<rfloor>)\<bar> + \<bar>ln x - ln (nat \<lfloor>x\<rfloor>)\<bar>"
    by (rule abs_triangle_ineq4)
  also have "\<bar>(\<Sum>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. ln p / p) - ln (nat \<lfloor>x\<rfloor>)\<bar> \<le> 7"
    using 1 by (intro Mertens) auto
  also have "\<bar>ln x - ln (nat \<lfloor>x\<rfloor>)\<bar> = ln x - ln (nat \<lfloor>x\<rfloor>)"
    using 1 by (intro abs_of_nonneg) auto
  also from 1 have "\<dots> \<le> (x - nat \<lfloor>x\<rfloor>) / nat \<lfloor>x\<rfloor>" by (intro ln_diff_le) auto
  also have "\<dots> \<le> (x - nat \<lfloor>x\<rfloor>) / 1" using 1 by (intro divide_left_mono) auto
  also have "\<dots> = x - nat \<lfloor>x\<rfloor>" by simp
  also have "\<dots> \<le> 1" using 1 by linarith
  also have "(\<Sum>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. ln p / p) = (\<Sum>p | prime p \<and> real p \<le> x. ln p / p)"
    using 1 by (intro sum.cong refl) (auto simp: le_nat_iff le_floor_iff)
  finally show ?case by simp
qed


subsection \<open>The contribution of the non-principal characters\<close>

text \<open>
  The estimates in the next two sections are partially inspired by John Harrison's
  proof of Dirichlet's Theorem~\cite{harrison-dirichlet}.

  We first estimate the growth of the partial sums of
    \[-L'(1, \chi)/L(1, \chi) = \sum_{k=1}^\infty \chi(k) \frac{\Lambda(k)}{k}\]
  for a non-principal character $\chi$ and show that they are, in fact, bounded, which is 
  ultimately a consequence of the non-vanishing of $L(1, \chi)$ for non-principal $\chi$.
\<close>

context dcharacter
begin

context
  includes no_vec_lambda_notation dcharacter_syntax
  fixes L
  assumes nonprincipal: "\<chi> \<noteq> \<chi>\<^sub>0"
  defines "L \<equiv> Dirichlet_L n \<chi> 1"
begin

lemma Dirichlet_L_nonprincipal_mangoldt_bound_aux_strong:
  assumes x: "x > 0"
  shows   "norm (L * sum_upto (\<lambda>k. \<chi> k * mangoldt k / k) x - sum_upto (\<lambda>k. \<chi> k * ln k / k) x)
             \<le> 9 / 2 * real (totient n)"
proof -
  define B where "B = 3 * real (totient n)"
  have "sum_upto (\<lambda>k. \<chi> k * ln k / k) x = sum_upto (\<lambda>k. \<chi> k * (\<Sum>d | d dvd k. mangoldt d) / k) x"
    by (intro sum_upto_cong) (simp_all add: mangoldt_sum)
  also have "\<dots> = sum_upto (\<lambda>k. \<Sum>d | d dvd k. \<chi> k * mangoldt d / k) x"
    by (simp add: sum_distrib_left sum_distrib_right sum_divide_distrib)
  also have "\<dots> = sum_upto (\<lambda>k. sum_upto (\<lambda>d. \<chi> (d * k) * mangoldt k / (d * k)) (x / real k)) x"
    by (rule sum_upto_sum_divisors)
  also have "\<dots> = sum_upto (\<lambda>k. \<chi> k * mangoldt k / k * sum_upto (\<lambda>d. \<chi> d / d) (x / real k)) x"
    by (simp add: sum_upto_def sum_distrib_left mult_ac)
  also have "L * sum_upto (\<lambda>k. \<chi> k * mangoldt k / k) x - \<dots> =
              sum_upto (\<lambda>k. (L - sum_upto (\<lambda>d. \<chi> d / d) (x / real k)) * (\<chi> k * mangoldt k / k)) x"
    unfolding ring_distribs by (simp add: sum_upto_def sum_subtractf sum_distrib_left mult_ac)
  also have "norm \<dots> \<le> sum_upto (\<lambda>k. B / x * mangoldt k) x" unfolding sum_upto_def
  proof (rule sum_norm_le, goal_cases)
    case (1 k)
    have "norm ((L - sum_upto (\<lambda>d. \<chi> d / of_nat d) (x / k)) * \<chi> k * (mangoldt k / of_nat k)) \<le>
            (B * real k / x) * 1 * (mangoldt k / real k)" unfolding norm_mult norm_divide
    proof (intro mult_mono divide_left_mono)
      show "norm (L - sum_upto (\<lambda>d. \<chi> d / d) (x / k)) \<le> B * real k / x"
        using Dirichlet_L_minus_partial_sum_bound[OF nonprincipal, of 1 "x / k"] 1 x
        by (simp add: powr_minus B_def L_def divide_simps norm_minus_commute)
    qed (insert 1, auto intro!: divide_nonneg_pos mangoldt_nonneg norm_le_1 simp: B_def)
    also have "\<dots> =  B / x * mangoldt k" using 1 by simp
    finally show ?case by (simp add: sum_upto_def mult_ac)
  qed
  also have "\<dots> = B / x * sum_upto mangoldt x"
    unfolding sum_upto_def sum_distrib_left by simp
  also have "\<dots> \<le> B / x * (3 / 2 * x)" using x
    by (intro mult_left_mono sum_upto_mangoldt_le) (auto simp: B_def)
  also have "\<dots> = 9 / 2 * real (totient n)" using x by (simp add: B_def)
  finally show ?thesis by (simp add: B_def)
qed

lemma Dirichlet_L_nonprincipal_mangoldt_aux_bound:
  "(\<lambda>x. L * sum_upto (\<lambda>k. \<chi> k * mangoldt k / k) x - sum_upto (\<lambda>k. \<chi> k * ln k / k) x) \<in> O(\<lambda>_. 1)"
  by (intro bigoI[of _ "9 / 2 * real (totient n)"] eventually_mono[OF eventually_gt_at_top[of 0]])
     (use Dirichlet_L_nonprincipal_mangoldt_bound_aux_strong in simp_all)

lemma nonprincipal_mangoldt_bound:
  "(\<lambda>x. sum_upto (\<lambda>k. \<chi> k * mangoldt k / k) x) \<in> O(\<lambda>_. 1)" (is "?lhs \<in> _")
proof -
  have [simp]: "L \<noteq> 0"
    using nonprincipal unfolding L_def by (intro Dirichlet_L_Re_ge_1_nonzero_nonprincipal) auto
  have "fds_converges (fds_deriv (fds \<chi>)) 1" using conv_abscissa_le_0[OF nonprincipal] 
    by (intro fds_converges_deriv) (auto intro: le_less_trans)
  hence "summable (\<lambda>n. -(\<chi> n * ln n / n))" 
    by (auto simp: fds_converges_def fds_deriv_def scaleR_conv_of_real fds_nth_fds' algebra_simps)
  hence "summable (\<lambda>n. \<chi> n * ln n / n)" by (simp only: summable_minus_iff)
  from summable_imp_convergent_sum_upto [OF this] obtain c where
    "(sum_upto (\<lambda>n. \<chi> n * ln n / n) \<longlongrightarrow> c) at_top" by blast
  hence *: "sum_upto (\<lambda>k. \<chi> k * ln k / k) \<in> O(\<lambda>_. 1)" unfolding sum_upto_def
    by (intro bigoI_tendsto[of _ _ c]) auto
  from sum_in_bigo[OF Dirichlet_L_nonprincipal_mangoldt_aux_bound *]
    have "(\<lambda>x. L * sum_upto (\<lambda>k. \<chi> k * mangoldt k / k) x) \<in> O(\<lambda>_. 1)" by (simp add: L_def)
  thus ?thesis by simp
qed

end
end


subsection \<open>The contribution of the principal character\<close>

text \<open>
  Next, we turn to the analogous partial sum for the principal character and show that
  it grows logarithmically and therefore is the dominant contribution.
\<close>

context residues_nat
begin
context
  includes no_vec_lambda_notation dcharacter_syntax
begin

lemma principal_dchar_sum_bound:
  "(\<lambda>x. (\<Sum>p | prime p \<and> real p \<le> x. \<chi>\<^sub>0 p * (ln p / p)) - ln x) \<in> O(\<lambda>_. 1)"
proof -
  have fin [simp]: "finite {p. prime p \<and> real p \<le> x \<and> Q p}" for Q x
    by (rule finite_subset[of _ "{..nat \<lfloor>x\<rfloor>}"]) (auto simp: le_nat_iff le_floor_iff)
  from fin[of _ "\<lambda>_. True"] have [simp]: "finite {p. prime p \<and> real p \<le> x}" for x
    by (simp del: fin)
  define P :: complex where "P = (\<Sum>p | prime p \<and> p dvd n. of_real (ln p / p))"

  have "(\<lambda>x. (\<Sum>p | prime p \<and> real p \<le> x. \<chi>\<^sub>0 p * (ln p / p)) - ln x) \<in>
          \<Theta>(\<lambda>x. of_real ((\<Sum>p | prime p \<and> real p \<le> x. ln p / p) - ln x) - P)" (is "_ \<in> \<Theta>(?f)")
  proof (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of "real n"]], goal_cases)
    case (1 x)
    have *: "{p. prime p \<and> real p \<le> x} = 
               {p. prime p \<and> real p \<le> x \<and> p dvd n} \<union> {p. prime p \<and> real p \<le> x \<and> \<not>p dvd n}"
      (is "_ = ?A \<union> ?B") by auto
    have "(\<Sum>p | prime p \<and> real p \<le> x. of_real (ln p / p)) = 
            (\<Sum>p\<in>?A. of_real (ln p / p)) + (\<Sum>p\<in>?B. complex_of_real (ln p / p))"
      by (subst *, subst sum.union_disjoint) auto
    also from 1 have "?A = {p. prime p \<and> p dvd n}" using n by (auto dest: dvd_imp_le)
    also have "(\<Sum>p\<in>\<dots>. of_real (ln p / p)) = P" by (simp add: P_def)
    also have "(\<Sum>p\<in>?B. of_real (ln p / p)) = 
                 (\<Sum>p | prime p \<and> real p \<le> x. \<chi>\<^sub>0 p * (ln p / p))"
      by (intro sum.mono_neutral_cong_left)
         (auto simp: principal_dchar_def prime_gt_0_nat coprime_absorb_left prime_imp_coprime)
    finally show ?case using 1 by (simp add: Ln_of_real)
  qed
  also have "?f \<in> O(\<lambda>_. of_real 1)"
    by (rule sum_in_bigo, subst landau_o.big.of_real_iff, rule Mertens_bigo) auto
  finally show ?thesis by simp
qed

lemma principal_dchar_sum_bound':
  "(\<lambda>x. sum_upto (\<lambda>k. \<chi>\<^sub>0 k * mangoldt k / k) x - Ln x) \<in> O(\<lambda>_. 1)"
proof -
  have "(\<lambda>x. sum_upto (\<lambda>k. \<chi>\<^sub>0 k * mangoldt k / k) x -
               (\<Sum>p | prime p \<and> real p \<le> x. \<chi>\<^sub>0 p * (ln p / p))) \<in> O(\<lambda>_. 1)"
  proof (intro bigoI[of _ 3] eventually_mono[OF eventually_gt_at_top[of 0]], goal_cases)
    case (1 x)
    have "norm (complex_of_real (\<Sum>k | real k \<le> x \<and> coprime k n. mangoldt k / k) - 
                of_real (\<Sum>p | prime p \<and> p \<in> {k. real k \<le> x \<and> coprime k n}. ln p / p)) \<le> 3"
      unfolding of_real_diff [symmetric] norm_of_real
      by (rule Mertens_mangoldt_versus_ln[where n = "nat \<lfloor>x\<rfloor>"])
         (insert n, auto simp: Suc_le_eq le_nat_iff le_floor_iff intro!: Nat.gr0I)
    also have "complex_of_real (\<Sum>k | real k \<le> x \<and> coprime k n. mangoldt k / k) =
                 sum_upto (\<lambda>k. \<chi>\<^sub>0 k * mangoldt k / k) x"
      unfolding sum_upto_def of_real_sum using n
      by (intro sum.mono_neutral_cong_left) (auto simp: principal_dchar_def intro!: Nat.gr0I)
    also have "complex_of_real (\<Sum>p | prime p \<and> p \<in> {k. real k \<le> x \<and> coprime k n}. ln p / p) =
                 (\<Sum>p | prime p \<and> real p \<le> x. \<chi>\<^sub>0 p * (ln p / p))"
      unfolding of_real_sum
      by (intro sum.mono_neutral_cong_left)
         (auto simp: principal_dchar_def le_nat_iff le_floor_iff prime_gt_0_nat
               intro!: finite_subset[of _ "{..nat \<lfloor>x\<rfloor>}"])
    finally show ?case by simp
  qed
  from sum_in_bigo(1)[OF principal_dchar_sum_bound this] show ?thesis
    by simp
qed


subsection \<open>The main result\<close>

text \<open>
  We can now show the main result by extracting the primes we want using the orthogonality
  relation on characters, separating the principal part of the sum from the non-principal ones
  and then applying the above estimates.
\<close>
lemma Dirichlet_strong:
  assumes "coprime h n"
  shows   "(\<lambda>x. (\<Sum>p | prime p \<and> [p = h] (mod n) \<and> real p \<le> x. ln p / p) - ln x / totient n)
             \<in> O(\<lambda>_. 1)" (is "(\<lambda>x. sum _ (?A x) - _) \<in> _")
proof -
  from assms obtain h' where h': "[h * h' = Suc 0] (mod n)"
    by (subst (asm) coprime_iff_invertible_nat) blast
  let ?A' = "\<lambda>x. {p. p > 0 \<and> real p \<le> x \<and> [p = h] (mod n)}"
  let ?B = "dcharacters n - {\<chi>\<^sub>0}"
  have [simp]: "\<chi>\<^sub>0 \<in> dcharacters n"
    by (auto simp: dcharacters_def principal.dcharacter_axioms)

  have "(\<lambda>x. of_nat (totient n) * (\<Sum>p\<in>?A' x. mangoldt p / p) - ln x) \<in>
             \<Theta>(\<lambda>x. sum_upto (\<lambda>k. \<chi>\<^sub>0 k * mangoldt k / k) x - ln x +
                  (\<Sum>\<chi>\<in>?B. \<chi> h' * sum_upto (\<lambda>k. \<chi> k * mangoldt k / k) x))"
    (is "_ \<in> \<Theta>(?f)")
  proof (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 0]], goal_cases)
    case (1 x)
    have "of_nat (totient n) * (\<Sum>p\<in>?A' x. of_real (mangoldt p / p) :: complex) = 
            (\<Sum>p\<in>?A' x. of_nat (totient n) * of_real (mangoldt p / p))"
      by (subst sum_distrib_left) simp_all
    also have "\<dots> = sum_upto (\<lambda>k. \<Sum>\<chi>\<in>dcharacters n. \<chi> (h' * k) * (mangoldt k / k)) x"
      unfolding sum_upto_def
    proof (intro sum.mono_neutral_cong_left ballI, goal_cases)
      case (3 p)
      have "[h' * p \<noteq> 1] (mod n)"
      proof
        assume "[h' * p = 1] (mod n)"
        hence "[h * (h' * p) = h * 1] (mod n)" by (rule cong_scalar_left)
        hence "[h = h * h' * p] (mod n)" by (simp add: mult_ac cong_sym)
        also have "[h * h' * p = 1 * p] (mod n)"
          using h' by (intro cong_scalar_right) auto
        finally have "[p = h] (mod n)" by (simp add: cong_sym)
        with 3 show False by auto
      qed
      thus ?case
        by (auto simp: sum_dcharacters sum_divide_distrib [symmetric] sum_distrib_right [symmetric])
    next
      case (4 p)
      hence "[p * h' = h * h'] (mod n)" by (intro cong_scalar_right) auto
      also have "[h * h' = 1] (mod n)" using h' by simp
      finally have "[h' * p = 1] (mod n)" by (simp add: mult_ac)
      thus ?case using h' 4
        by (auto simp: sum_dcharacters sum_divide_distrib [symmetric] sum_distrib_right [symmetric])
    qed auto
    also have "\<dots> = (\<Sum>\<chi>\<in>dcharacters n. sum_upto (\<lambda>k. \<chi> (h' * k) * (mangoldt k / k)) x)"
      unfolding sum_upto_def by (rule sum.swap)
    also have "\<dots> = (\<Sum>\<chi>\<in>dcharacters n. \<chi> h' * sum_upto (\<lambda>k. \<chi> k * (mangoldt k / k)) x)"
      unfolding sum_upto_def
      by (intro sum.cong refl) (auto simp: dcharacters_def dcharacter.mult sum_distrib_left mult_ac)
    also have "\<dots> = \<chi>\<^sub>0 h' * sum_upto (\<lambda>k. \<chi>\<^sub>0 k * (mangoldt k / k)) x + 
                    (\<Sum>\<chi>\<in>?B. \<chi> h' * sum_upto (\<lambda>k. \<chi> k * (mangoldt k / k)) x)"
      by (subst sum.remove [symmetric]) (auto simp: sum_distrib_left)
    also have "coprime h' n"
      using h' by (subst coprime_iff_invertible_nat, subst (asm) mult.commute) auto
    hence "\<chi>\<^sub>0 h' = 1"
      by (simp add: principal_dchar_def)
    finally show ?case using n 1 by (simp add: Ln_of_real)
  qed
  also have "?f \<in> O(\<lambda>_. complex_of_real 1)"
  proof (rule sum_in_bigo[OF _ big_sum_in_bigo], goal_cases)
    case 1
    from principal_dchar_sum_bound' show ?case by simp
  next
    case (2 \<chi>)
    then interpret dcharacter n G \<chi> by (simp_all add: G_def dcharacters_def)
    from 2 have "\<chi> \<noteq> \<chi>\<^sub>0" by auto
    thus ?case unfolding of_real_1
      by (intro landau_o.big.mult_in_1 nonprincipal_mangoldt_bound) auto
  qed
  finally have *: "(\<lambda>x. real (totient n) * (\<Sum>p\<in>?A' x. mangoldt p / p) - ln x) \<in> O(\<lambda>_. 1)" 
    by (subst (asm) landau_o.big.of_real_iff)

  have "(\<lambda>x. real (totient n) * ((\<Sum>p\<in>?A x. ln p / p) - (\<Sum>p\<in>?A' x. mangoldt p / p))) \<in> O(\<lambda>_. 1)"
  proof (intro landau_o.big.mult_in_1)
    show "(\<lambda>x. (\<Sum>p\<in>?A x. ln p / p) - (\<Sum>p\<in>?A' x. mangoldt p / p)) \<in> O(\<lambda>_. 1)"
      unfolding landau_o.big.of_real_iff
    proof (intro bigoI[of _ 3] eventually_mono[OF eventually_gt_at_top[of 0]], goal_cases)
      case (1 x)
      have "\<bar>(\<Sum>p\<in>?A' x. mangoldt p / p) - (\<Sum>p | prime p \<and> p \<in> ?A' x. ln p / p)\<bar> \<le> 3"
        by (rule Mertens_mangoldt_versus_ln[where n = "nat \<lfloor>x\<rfloor>"])
           (auto simp: le_nat_iff le_floor_iff)
      also have "{p. prime p \<and> p \<in> ?A' x} = ?A x" by (auto simp: prime_gt_0_nat)
      finally show ?case by (simp add: abs_minus_commute)
    qed
  qed auto
  from sum_in_bigo(1)[OF * this] 
    have "(\<lambda>x. totient n * (\<Sum>p\<in>?A x. ln p / p) - ln x) \<in> O(\<lambda>_. 1)"
    by (simp add: field_simps)
  also have "(\<lambda>x. totient n * (\<Sum>p\<in>?A x. ln p / p) - ln x) =
               (\<lambda>x. totient n * ((\<Sum>p\<in>?A x. ln p / p) - ln x / totient n))"
    using n by (intro ext) (auto simp: field_simps)
  also have "\<dots> \<in> O(\<lambda>_. 1) \<longleftrightarrow> ?thesis" using n
    by (intro landau_o.big.cmult_in_iff) auto
  finally show ?thesis .
qed

text \<open>
  It is now obvious that the set of primes we are interested in is, in fact, infinite.
\<close>
theorem Dirichlet:
  assumes "coprime h n"
  shows   "infinite {p. prime p \<and> [p = h] (mod n)}"
proof
  assume "finite {p. prime p \<and> [p = h] (mod n)}"
  then obtain K where K: "{p. prime p \<and> [p = h] (mod n)} \<subseteq> {..<K}"
    by (auto simp: finite_nat_iff_bounded)
  have "eventually (\<lambda>x. (\<Sum>p | prime p \<and> [p = h] (mod n) \<and> real p \<le> x. ln p / p) =
                        (\<Sum>p | prime p \<and> [p = h] (mod n). ln p / p)) at_top"
    using eventually_ge_at_top[of "real K"] by eventually_elim (intro sum.cong, use K in auto)
  hence "(\<lambda>x. (\<Sum>p | prime p \<and> [p = h] (mod n) \<and> real p \<le> x. ln p / p)) \<in> 
            \<Theta>(\<lambda>_. (\<Sum>p | prime p \<and> [p = h] (mod n). ln p / p))" by (intro bigthetaI_cong) auto
  also have "(\<lambda>_. (\<Sum>p | prime p \<and> [p = h] (mod n). ln p / p)) \<in> O(\<lambda>_. 1)" by simp
  finally have "(\<lambda>x. (\<Sum>p | prime p \<and> [p = h] (mod n) \<and> real p \<le> x. ln p / p)) \<in> O(\<lambda>_. 1)" .
  from sum_in_bigo(2)[OF this Dirichlet_strong[OF assms]] and n show False by simp
qed

text \<open>
  In the future, one could extend this result to more precise estimates of the distribution
  of primes in arithmetic progressions in a similar way to the Prime Number Theorem.
\<close>

end
end
end
