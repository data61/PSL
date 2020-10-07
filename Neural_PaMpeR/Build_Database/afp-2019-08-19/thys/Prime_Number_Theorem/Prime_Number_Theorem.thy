(*
  File:       Prime Number Theorem.thy
  Authors:    Manuel Eberl (TU München), Larry Paulson (University of Cambridge)

  A proof of the Prime Number Theorem and some related properties
*)
section \<open>The Prime Number Theorem\<close>
theory Prime_Number_Theorem
imports 
  Newman_Ingham_Tauberian
  Prime_Counting_Functions
begin

(*<*)
unbundle prime_counting_notation
(*>*)

subsection \<open>Constructing Newman's function\<close>

text \<open>
  Starting from Mertens' first theorem, i.\,e.\ $\mathfrak M(x) = \ln x + O(1)$, we now 
  want to derive that $\mathfrak M(x) = \ln x + c + o(1)$. This result is considerably stronger
  and it implies the Prime Number Theorem quite directly.

  In order to do this, we define the Dirichlet series
  \[f(s) = \sum_{n=1}^\infty \frac{\mathfrak{M}(n)}{n^s}\ .\]
  We will prove that this series extends meromorphically to $\mathfrak{R}(s)\geq 1$ and
  apply Ingham's theorem to it (after we subtracted its pole at $s = 1$).
\<close>
definition fds_newman where
  "fds_newman = fds (\<lambda>n. complex_of_real (\<MM> n))"

lemma fds_nth_newman:
  "fds_nth fds_newman n = of_real (\<MM> n)"
  by (simp add: fds_newman_def fds_nth_fds)

lemma norm_fds_nth_newman:
  "norm (fds_nth fds_newman n) = \<MM> n"
  unfolding fds_nth_newman norm_of_real
  by (intro abs_of_nonneg sum_nonneg divide_nonneg_pos) (auto dest: prime_ge_1_nat)

text \<open>
  The Dirichlet series $f(s) + \zeta'(s)$ has the coefficients $\mathfrak{M}(n) - \ln n$,
  so by Mertens' first theorem, $f(s) + \zeta'(s)$ has bounded coefficients.
\<close>
lemma bounded_coeffs_newman_minus_deriv_zeta:
  defines "f \<equiv> fds_newman + fds_deriv fds_zeta"
  shows   "Bseq (\<lambda>n. fds_nth f n)"
proof -
  have "(\<lambda>n. \<MM> (real n) - ln (real n)) \<in> O(\<lambda>_. 1)"
    using mertens_bounded by (rule landau_o.big.compose) real_asymp
  from natfun_bigo_1E[OF this, of 1]
    obtain c where c: "c \<ge> 1" "\<And>n. \<bar>\<MM> (real n) - ln (real n)\<bar> \<le> c" by auto

  show ?thesis
  proof (intro BseqI[of c] allI)
    fix n :: nat
    show "norm (fds_nth f n) \<le> c"
    proof (cases "n = 0")
      case False
      hence "fds_nth f n = of_real (\<MM> n - ln n)"
        by (simp add: f_def fds_nth_newman fds_nth_deriv fds_nth_zeta scaleR_conv_of_real)
      also from \<open>n \<noteq> 0\<close> have "norm \<dots> \<le> c"
        using c(2)[of n] by (simp add: in_Reals_norm)
      finally show ?thesis .
    qed (insert c, auto)
  qed (insert c, auto)
qed

text \<open>
  A Dirichlet series with bounded coefficients converges for all $s$ with
  $\mathfrak{R}(s)>1$ and so does $\zeta'(s)$, so we can conclude that $f(s)$ does as well.
\<close>
lemma abs_conv_abscissa_newman: "abs_conv_abscissa fds_newman \<le> 1"
  and conv_abscissa_newman:     "conv_abscissa fds_newman \<le> 1"
proof -
  define f where "f = fds_newman + fds_deriv fds_zeta"
  have "abs_conv_abscissa f \<le> 1"
    using bounded_coeffs_newman_minus_deriv_zeta unfolding f_def
    by (rule bounded_coeffs_imp_abs_conv_abscissa_le_1)
  hence "abs_conv_abscissa (f - fds_deriv fds_zeta) \<le> 1"
    by (intro abs_conv_abscissa_diff_leI) (auto simp: abs_conv_abscissa_deriv)
  also have "f - fds_deriv fds_zeta = fds_newman" by (simp add: f_def)
  finally show "abs_conv_abscissa fds_newman \<le> 1" .
  from conv_le_abs_conv_abscissa and this show "conv_abscissa fds_newman \<le> 1"
    by (rule order.trans)
qed

text \<open>
  We now change the order of summation to obtain an alternative form of $f(s)$ in terms of a 
  sum of Hurwitz $\zeta$ functions.
\<close>
lemma eval_fds_newman_conv_infsetsum:
  assumes s: "Re s > 1"
  shows   "eval_fds fds_newman s = (\<Sum>\<^sub>ap | prime p. (ln (real p) / real p) * hurwitz_zeta p s)"
          "(\<lambda>p. ln (real p) / real p * hurwitz_zeta p s) abs_summable_on {p. prime p}"
proof -
  from s have conv: "fds_abs_converges fds_newman s"
    by (intro fds_abs_converges le_less_trans[OF abs_conv_abscissa_newman]) auto
  define f where "f = (\<lambda>n p. ln (real p) / real p / of_nat n powr s)"

  have eq: "(\<Sum>\<^sub>an\<in>{p..}. f n p) = ln (real p) / real p * hurwitz_zeta p s" if "prime p" for p
  proof -
    have "(\<Sum>\<^sub>an\<in>{p..}. f n p) = (\<Sum>\<^sub>ax\<in>{p..}. (ln (real p) / of_nat p) * (1 / of_nat x powr s))"
      by (simp add: f_def)
    also have "\<dots> = (ln (real p) / of_nat p) * (\<Sum>\<^sub>ax\<in>{p..}. 1 / of_nat x powr s)"
      using abs_summable_hurwitz_zeta[of s 0 p] that s
      by (intro infsetsum_cmult_right) (auto dest: prime_gt_0_nat)
    also have "(\<Sum>\<^sub>ax\<in>{p..}. 1 / of_nat x powr s) = hurwitz_zeta p s"
      using s that by (subst hurwitz_zeta_nat_conv_infsetsum(2))
                      (auto dest: prime_gt_0_nat simp: field_simps powr_minus)
    finally show ?thesis .
  qed

  have norm_f: "norm (f n p) = ln p / p / n powr Re s" if "prime p" for n p :: nat
    by (auto simp: f_def norm_divide norm_mult norm_powr_real_powr)
  from conv have "(\<lambda>n. norm (fds_nth fds_newman n / n powr s)) abs_summable_on UNIV"
    by (intro abs_summable_on_normI) (simp add: fds_abs_converges_altdef')
  also have "(\<lambda>n. norm (fds_nth fds_newman n / n powr s)) =
               (\<lambda>n. \<Sum>p | prime p \<and> p \<le> n. norm (f n p))"
    by (auto simp: norm_divide norm_fds_nth_newman sum_divide_distrib primes_M_def
                   prime_sum_upto_def norm_mult norm_f norm_powr_real_powr intro!: sum.cong)
  finally have summable1: "(\<lambda>(n,p). f n p) abs_summable_on (SIGMA n:UNIV. {p. prime p \<and> p \<le> n})"
    using conv by (subst abs_summable_on_Sigma_iff) auto
  also have "?this \<longleftrightarrow> (\<lambda>(p,n). f n p) abs_summable_on
                         (\<lambda>(n,p). (p,n)) ` (SIGMA n:UNIV. {p. prime p \<and> p \<le> n})"
    by (subst abs_summable_on_reindex_iff [symmetric]) (auto simp: case_prod_unfold inj_on_def)
  also have "(\<lambda>(n,p). (p,n)) ` (SIGMA n:UNIV. {p. prime p \<and> p \<le> n}) =
               (SIGMA p:{p. prime p}. {p..})" by auto
  finally have summable2: "(\<lambda>(p,n). f n p) abs_summable_on \<dots>" .
  from abs_summable_on_Sigma_project1'[OF this]
    have "(\<lambda>p. \<Sum>\<^sub>an\<in>{p..}. f n p) abs_summable_on {p. prime p}" by auto
  also have "?this \<longleftrightarrow> (\<lambda>p. ln (real p) / real p * hurwitz_zeta p s) abs_summable_on {p. prime p}"
    by (intro abs_summable_on_cong eq) auto
  finally show \<dots> .

  have "eval_fds fds_newman s =
          (\<Sum>\<^sub>an. \<Sum>p | prime p \<and> p \<le> n. ln (real p) / real p / of_nat n powr s)"
    using conv by (simp add: eval_fds_altdef fds_nth_newman sum_divide_distrib
                             primes_M_def prime_sum_upto_def)
  also have "\<dots> = (\<Sum>\<^sub>an. \<Sum>\<^sub>ap | prime p \<and> p \<le> n. f n p)"
    unfolding f_def by (subst infsetsum_finite) auto
  also have "\<dots> = (\<Sum>\<^sub>a(n, p) \<in> (SIGMA n:UNIV. {p. prime p \<and> p \<le> n}). f n p)"
    using summable1 by (subst infsetsum_Sigma) auto
  also have "\<dots> = (\<Sum>\<^sub>a(p, n) \<in> (\<lambda>(n,p). (p, n)) ` (SIGMA n:UNIV. {p. prime p \<and> p \<le> n}). f n p)"
    by (subst infsetsum_reindex) (auto simp: case_prod_unfold inj_on_def)
  also have "(\<lambda>(n,p). (p, n)) ` (SIGMA n:UNIV. {p. prime p \<and> p \<le> n}) =
               (SIGMA p:{p. prime p}. {p..})" by auto
  also have "(\<Sum>\<^sub>a(p,n)\<in>\<dots>. f n p) = (\<Sum>\<^sub>ap | prime p. \<Sum>\<^sub>an\<in>{p..}. f n p)"
    using summable2 by (subst infsetsum_Sigma) auto
  also have "(\<Sum>\<^sub>ap | prime p. \<Sum>\<^sub>an\<in>{p..}. f n p) =
               (\<Sum>\<^sub>ap | prime p. ln (real p) / real p * hurwitz_zeta p s)"
    by (intro infsetsum_cong eq) auto
  finally show "eval_fds fds_newman s =
                  (\<Sum>\<^sub>ap | prime p. (ln (real p) / real p) * hurwitz_zeta p s)" .
qed


text \<open>
  We now define a meromorphic continuation of $f(s)$ on $\mathfrak{R}(s) > \frac{1}{2}$.

  To construct $f(s)$, we express it as
  \[f(s) = \frac{1}{z-1}\left(\bar f(s) - \frac{\zeta'(s)}{\zeta(s)}\right)\ ,\]
  where $\bar f(s)$ (which we shall call \<open>pre_newman\<close>) is a function that is analytic on
  $\Re(s) > \frac{1}{2}$, which can be shown fairly easily using the Weierstraß M test.
  
  $\zeta'(s)/\zeta(s)$ is meromorphic except for a single pole at $s = 1$ and one $k$-th order
  pole for any $k$-th order zero of $\zeta$, but for the Prime Number Theorem, we are only
  concerned with the area $\mathfrak{R}(s) \geq 1$, where $\zeta$ does not have any zeros.

  Taken together, this means that $f(s)$ is analytic for $\mathfrak{R}(s)\geq 1$ except for a
  double pole at $s = 1$, which we will take care of later.
\<close>

context
  fixes A :: "nat \<Rightarrow> complex \<Rightarrow> complex" and B :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  defines "A \<equiv> (\<lambda>p s. (s - 1) * pre_zeta (real p) s - 
                         of_nat p / (of_nat p powr s * (of_nat p powr s - 1)))"
  defines "B \<equiv> (\<lambda>p s. of_real (ln (real p)) / of_nat p * A p s)"
begin

definition pre_newman :: "complex \<Rightarrow> complex" where
  "pre_newman s = (\<Sum>p. if prime p then B p s else 0)"

definition newman where "newman s = 1 / (s - 1) * (pre_newman s - deriv zeta s / zeta s)"

text \<open>
  The sum used in the definition of \<open>pre_newman\<close> converges uniformly on any disc within the
  half-space with $\mathfrak{R}(s) > \frac{1}{2}$ by the Weierstraß M test.
\<close>
lemma uniform_limit_pre_newman:
  assumes r: "r \<ge> 0" "Re s - r > 1 / 2"
  shows "uniform_limit (cball s r)
           (\<lambda>n s. \<Sum>p<n. if prime p then B p s else 0) pre_newman at_top"
proof -
  from r have Re: "Re z > 1 / 2" if "dist s z \<le> r" for z
    using abs_Re_le_cmod[of "s - z"] r that
    by (auto simp: dist_norm abs_if split: if_splits)

  define x where "x = Re s - r" \<comment> \<open>The lower bound for the real part in the disc\<close>
  from r Re have "x > 1 / 2" by (auto simp: x_def)

  \<comment> \<open>The following sequence \<open>M\<close> bounds the summand, and it is obviously $O(n^{-1-\epsilon})$
      and therefore summable\<close>
  define C where "C = (norm s + r + 1) * (norm s + r) / x"
  define M where "M = (\<lambda>p::nat. ln p * (C / p powr (x + 1) + 1 / (p powr x * (p powr x - 1))))"

  show ?thesis unfolding pre_newman_def
  proof (intro Weierstrass_m_test_ev[OF eventually_mono[OF eventually_gt_at_top[of 1]]] ballI)
    show "summable M"
    proof (rule summable_comparison_test_bigo)
      define \<epsilon> where "\<epsilon> = min (2 * x - 1) x / 2"
      from \<open>x > 1 / 2\<close> have \<epsilon>: "\<epsilon> > 0" "1 + \<epsilon> < 2 * x" "1 + \<epsilon> < x + 1"
        by (auto simp: \<epsilon>_def min_def field_simps)
      show "M \<in> O(\<lambda>n. n powr (- 1 - \<epsilon>))" unfolding M_def distrib_left
        by (intro sum_in_bigo) (use \<epsilon> in real_asymp)+
      from \<epsilon> show "summable (\<lambda>n. norm (n powr (- 1 - \<epsilon>)))"
        by (simp add: summable_real_powr_iff)
    qed
  next
    fix p :: nat and z assume p: "p > 1" and z: "z \<in> cball s r"
    from z r Re[of z] have x: "Re z \<ge> x" "x > 1 / 2" and "Re z > 1 / 2"
      using abs_Re_le_cmod[of "s - z"] by (auto simp: x_def algebra_simps dist_norm)
    have norm_z: "norm z \<le> norm s + r"
      using z norm_triangle_ineq2[of z s] r by (auto simp: dist_norm norm_minus_commute)
    from \<open>p > 1\<close> and x and r have "M p \<ge> 0"
      by (auto simp: C_def M_def intro!: mult_nonneg_nonneg add_nonneg_nonneg divide_nonneg_pos)

    have bound: "norm ((z - 1) * pre_zeta p z) \<le> 
                   norm (z - 1) * (norm z / (Re z * p powr Re z))"
      using pre_zeta_bound'[of z p] p \<open>Re z > 1 / 2\<close>
      unfolding norm_mult by (intro mult_mono pre_zeta_bound) auto

    have "norm (B p z) = ln p / p * norm (A p z)"
      unfolding B_def using \<open>p > 1\<close> by (simp add: B_def norm_mult norm_divide)
    also have "\<dots> \<le> ln p / p * (norm (z - 1) * norm z / Re z / p powr Re z + 
                                 p / (p powr Re z * (p powr Re z - 1)))"
      unfolding A_def using \<open>p > 1\<close> and \<open>Re z > 1 / 2\<close> and bound
      by (intro mult_left_mono order.trans[OF norm_triangle_ineq4 add_mono] mult_left_mono)
         (auto simp: norm_divide norm_mult norm_powr_real_powr
               intro!: divide_left_mono order.trans[OF _ norm_triangle_ineq2])
    also have "\<dots> = ln p * (norm (z - 1) * norm z / Re z / p powr (Re z + 1) + 
                            1 / (p powr Re z * (p powr Re z - 1)))"
      using \<open>p > 1\<close> by (simp add: field_simps powr_add powr_minus)
    also have "norm (z - 1) * norm z / Re z / p powr (Re z + 1) \<le> C / p powr (x + 1)"
      unfolding C_def using r \<open>Re z > 1 / 2\<close> norm_z p x
      by (intro mult_mono frac_le powr_mono order.trans[OF norm_triangle_ineq4]) auto
    also have "1 / (p powr Re z * (p powr Re z - 1)) \<le>
                 1 / (p powr x * (p powr x - 1))" using \<open>p > 1\<close> x
      by (intro divide_left_mono mult_mono powr_mono diff_right_mono mult_pos_pos)
         (auto simp: ge_one_powr_ge_zero)
    finally have "norm (B p z) \<le> M p"
      using \<open>p > 1\<close> by (simp add: mult_left_mono M_def)
    with \<open>M p \<ge> 0\<close> show "norm (if prime p then B p z else 0) \<le> M p" by simp
  qed
qed

lemma sums_pre_newman: "Re s > 1 / 2 \<Longrightarrow> (\<lambda>p. if prime p then B p s else 0) sums pre_newman s"
  using tendsto_uniform_limitI[OF uniform_limit_pre_newman[of 0 s]] by (auto simp: sums_def)

lemma analytic_pre_newman [THEN analytic_on_subset, analytic_intros]:
  "pre_newman analytic_on {s. Re s > 1 / 2}"
proof -
  have holo: "(\<lambda>s::complex. if prime p then B p s else 0) holomorphic_on X"
    if "X \<subseteq> {s. Re s > 1 / 2}" for X and p :: nat using that
    by (cases "prime p")
       (auto intro!: holomorphic_intros simp: B_def A_def dest!: prime_gt_1_nat)
  have holo': "pre_newman holomorphic_on ball s r" if r: "r \<ge> 0" "Re s - r > 1 / 2" for s r
  proof -
    from r have Re: "Re z > 1 / 2" if "dist s z \<le> r" for z
      using abs_Re_le_cmod[of "s - z"] r that by (auto simp: dist_norm abs_if split: if_splits)
    show ?thesis
      by (rule holomorphic_uniform_limit[OF _ uniform_limit_pre_newman[of r s]])
         (insert that Re, auto intro!: always_eventually holomorphic_on_imp_continuous_on
                                       holomorphic_intros holo)
  qed
  show ?thesis unfolding analytic_on_def
  proof safe
    fix s assume "Re s > 1 / 2"
    thus "\<exists>r>0. pre_newman holomorphic_on ball s r"
      by (intro exI[of _ "(Re s - 1 / 2) / 2"] conjI holo') (auto simp: field_simps)
  qed
qed

lemma holomorphic_pre_newman [holomorphic_intros]:
  "X \<subseteq> {s. Re s > 1 / 2} \<Longrightarrow> pre_newman holomorphic_on X"
  using analytic_pre_newman by (rule analytic_imp_holomorphic)

lemma eval_fds_newman:
  assumes s: "Re s > 1"
  shows   "eval_fds fds_newman s = newman s"
proof -
  have eq: "(ln (real p) / real p) * hurwitz_zeta p s =
              1 / (s - 1) * (ln (real p) / (p powr s - 1) + B p s)"
    if p: "prime p" for p
  proof -
    have "(ln (real p) / real p) * hurwitz_zeta p s =
            ln (real p) / real p * (p powr (1 - s) / (s - 1) + pre_zeta p s)"
      using s by (auto simp add: hurwitz_zeta_def)
    also have "\<dots> = 1 / (s - 1) * (ln (real p) / (p powr s - 1) + B p s)"
      using p s by (simp add: divide_simps powr_diff B_def)
                   (auto simp: A_def field_simps dest: prime_gt_1_nat)?
    finally show ?thesis .
  qed

  have "(\<lambda>p. (ln (real p) / real p) * hurwitz_zeta p s) abs_summable_on {p. prime p}"
    using s by (intro eval_fds_newman_conv_infsetsum)
  hence "(\<lambda>p. 1 / (s - 1) * (ln (real p) / (p powr s - 1) + B p s))
            abs_summable_on {p. prime p}"
    by (subst (asm) abs_summable_on_cong[OF eq refl]) auto
  hence summable:
    "(\<lambda>p. ln (real p) / (p powr s - 1) + B p s) abs_summable_on {p. prime p}"
    using s by (subst (asm) abs_summable_on_cmult_right_iff) auto

  from s have [simp]: "s \<noteq> 1" by auto
  have "eval_fds fds_newman s =
          (\<Sum>\<^sub>ap | prime p. (ln (real p) / real p) * hurwitz_zeta p s)"
    using s by (rule eval_fds_newman_conv_infsetsum)
  also have "\<dots> = (\<Sum>\<^sub>ap | prime p. 1 / (s - 1) * (ln (real p) / (p powr s - 1) + B p s))"
    by (intro infsetsum_cong eq) auto
  also have "\<dots> = 1 / (s - 1) * (\<Sum>\<^sub>ap | prime p. ln (real p) / (p powr s - 1) + B p s)"
    (is "_ = _ * ?S") by (rule infsetsum_cmult_right[OF summable])
  also have "?S = (\<Sum>p. if prime p then 
                      ln (real p) / (p powr s - 1) + B p s else 0)"
    by (subst infsetsum_nat[OF summable]) auto
  also have "\<dots> = (\<Sum>p. (if prime p then ln (real p) / (p powr s - 1) else 0) + 
                        (if prime p then B p s else 0))"
    by (intro suminf_cong) auto
  also have "\<dots> = pre_newman s - deriv zeta s / zeta s"
    using sums_pre_newman[of s] sums_logderiv_zeta[of s] s
    by (subst suminf_add [symmetric]) (auto simp: sums_iff)
  finally show ?thesis by (simp add: newman_def)
qed

end

text \<open>
  Next, we shall attempt to get rid of the pole by subtracting suitable multiples of $\zeta(s)$
  and $\zeta'(s)$. To this end, we shall first prove the following alternative definition of 
  $\zeta'(s)$:
\<close>
lemma deriv_zeta_eq':
  assumes "0 < Re s" "s \<noteq> 1"
  shows "deriv zeta s = deriv (\<lambda>z. pre_zeta 1 z * (z - 1)) s / (s - 1) -
                          (pre_zeta 1 s * (s - 1) + 1) / (s - 1)\<^sup>2"
    (is "_ = ?rhs")
proof (rule DERIV_imp_deriv)
  have [derivative_intros]: "(pre_zeta 1 has_field_derivative deriv (pre_zeta 1) s) (at s)"
    by (intro holomorphic_derivI[of _ UNIV] holomorphic_intros) auto
  have *: "deriv (\<lambda>z. pre_zeta 1 z * (z - 1)) s = deriv (pre_zeta 1) s * (s - 1) + pre_zeta 1 s"
    by (subst deriv_mult)
       (auto intro!: holomorphic_on_imp_differentiable_at[of _ UNIV] holomorphic_intros)
  hence "((\<lambda>s. pre_zeta 1 s + 1 / (s - 1)) has_field_derivative
           deriv (pre_zeta 1) s - 1 / ((s - 1) * (s - 1))) (at s)"
    using assms by (auto intro!: derivative_eq_intros)
  also have "deriv (pre_zeta 1) s - 1 / ((s - 1) * (s - 1)) = ?rhs"
    using * assms by (simp add: divide_simps power2_eq_square, simp add: field_simps)
  also have "((\<lambda>s. pre_zeta 1 s + 1 / (s - 1)) has_field_derivative ?rhs) (at s) \<longleftrightarrow>
               (zeta has_field_derivative ?rhs) (at s)"
    using assms
    by (intro has_field_derivative_cong_ev eventually_mono[OF t1_space_nhds[of _ 1]])
       (auto simp: zeta_def hurwitz_zeta_def)
  finally show \<dots> .
qed

text \<open>
  From this, it follows that $(s - 1) \zeta'(s) - \zeta'(s) / \zeta(s)$ is analytic 
  for $\mathfrak{R}(s) \geq 1$:
\<close>
lemma analytic_zeta_derivdiff:
  obtains a where
    "(\<lambda>z. if z = 1 then a else (z - 1) * deriv zeta z - deriv zeta z / zeta z)
          analytic_on {s. Re s \<ge> 1}" 
proof 
  have neq: "pre_zeta 1 z * (z - 1) + 1 \<noteq> 0" if "Re z \<ge> 1" for z
    using zeta_Re_ge_1_nonzero[of z] that
    by (cases "z = 1") (auto simp: zeta_def hurwitz_zeta_def divide_simps)
  let ?g = "\<lambda>z. (1 - inverse (pre_zeta 1 z * (z - 1) + 1)) * ((z - 1) *
                deriv ((\<lambda>u. pre_zeta 1 u * (u - 1))) z - (pre_zeta 1 z * (z - 1) + 1))"
  show "(\<lambda>z. if z = 1 then deriv ?g 1 else (z - 1) * deriv zeta z - deriv zeta z / zeta z)
          analytic_on {s. Re s \<ge> 1}" (is "?f analytic_on _")
  proof (rule pole_theorem_analytic_0)
    show "?g analytic_on {s. 1 \<le> Re s}" using neq
      by (auto intro!: analytic_intros)
  next
    show "\<exists>d>0. \<forall>w\<in>ball z d - {1}. ?g w = (w - 1) * ?f w"
      if z: "z \<in> {s. 1 \<le> Re s}" for z
    proof -
      have *: "isCont (\<lambda>z. pre_zeta 1 z * (z - 1) + 1) z"
        by (auto intro!: continuous_intros)
       obtain e where "e > 0" and e: "\<And>y. dist z y < e \<Longrightarrow> pre_zeta (Suc 0) y * (y-1) + 1 \<noteq> 0"
         using continuous_at_avoid [OF * neq[of z]] z by auto
      show ?thesis
      proof (intro exI ballI conjI)
        fix w
        assume w: "w \<in> ball z (min e 1) - {1}"
        then have "Re w > 0"
          using complex_Re_le_cmod [of "z-w"] z by (simp add: dist_norm)
        with w show "?g w = (w - 1) * (if w = 1 then deriv ?g 1 else
                        (w - 1) * deriv zeta w - deriv zeta w / zeta w)"
          by (subst (1 2) deriv_zeta_eq', 
              simp_all add: zeta_def hurwitz_zeta_def divide_simps e power2_eq_square)
             (simp_all add: algebra_simps)?
      qed (use \<open>e > 0\<close> in auto)
    qed
  qed auto
qed

text \<open>
  Finally, $f(s) + \zeta'(s) + c\zeta(s)$ is analytic.
\<close>
lemma analytic_newman_variant:
  obtains c a where
     "(\<lambda>z. if z = 1 then a else newman z + deriv zeta z + c * zeta z) analytic_on {s. Re s \<ge> 1}"
proof -
  obtain c where (* -euler_mascheroni *)
    c: "(\<lambda>z. if z = 1 then c else (z - 1) * deriv zeta z - deriv zeta z / zeta z)
        analytic_on {s. Re s \<ge> 1}"
    using analytic_zeta_derivdiff by blast
  let ?g = "\<lambda>z. pre_newman z +
          (if z = 1 then c
           else (z - 1) * deriv zeta z -
                deriv zeta z / zeta z) - (c + pre_newman 1) * (pre_zeta 1 z * (z - 1) + 1)"
  have "(\<lambda>z. if z = 1 then deriv ?g 1 else newman z + deriv zeta z + (-(c + pre_newman 1)) * zeta z)
        analytic_on {s. Re s \<ge> 1}"  (is "?f analytic_on _")
  proof (rule pole_theorem_analytic_0)
    show "?g analytic_on {s. 1 \<le> Re s}"
      by (intro c analytic_intros) auto
  next
    show "\<exists>d>0. \<forall>w\<in>ball z d - {1}. ?g w = (w - 1) * ?f w"
      if "z \<in> {s. 1 \<le> Re s}" for z using that
      by (intro exI[of _ 1], simp_all add: newman_def divide_simps zeta_def hurwitz_zeta_def)
         (auto simp: field_simps)?
  qed auto
  with that show ?thesis by blast
qed


subsection \<open>The asymptotic expansion of \<open>\<MM>\<close>\<close>

text \<open>
  Our next goal is to show the key result that $\mathfrak{M}(x) = \ln n + c + o(1)$.

  As a first step, we invoke Ingham's Tauberian theorem on the function we have
  just defined and obtain that the sum
  \[\sum\limits_{n=1}^\infty \frac{\mathfrak{M}(n) - \ln n + c}{n}\]
  exists.
\<close>
lemma mertens_summable:
  obtains c :: real where "summable (\<lambda>n. (\<MM> n - ln n + c) / n)"
proof -
  (* c = euler_mascheroni - pre_newman 1 *)
  from analytic_newman_variant obtain c a where
    analytic: "(\<lambda>z. if z = 1 then a else newman z + deriv zeta z + c * zeta z)
                 analytic_on {s. Re s \<ge> 1}" .
  define f where "f = (\<lambda>z. if z = 1 then a else newman z + deriv zeta z + c * zeta z)"
  have analytic: "f analytic_on {s. Re s \<ge> 1}" using analytic by (simp add: f_def)
  define F where "F = fds_newman + fds_deriv fds_zeta + fds_const c * fds_zeta"

  note le = conv_abscissa_add_leI conv_abscissa_deriv_le conv_abscissa_newman conv_abscissa_mult_const_left
  note intros = le le[THEN le_less_trans] le[THEN order.trans] fds_converges
  have eval_F: "eval_fds F s = f s" if s: "Re s > 1" for s
  proof -
    have "eval_fds F s = eval_fds (fds_newman + fds_deriv fds_zeta) s +
                           eval_fds (fds_const c * fds_zeta) s"
      unfolding F_def using s by (subst eval_fds_add) (auto intro!: intros)
    also have "\<dots> = f s" using s unfolding f_def
      by (subst eval_fds_add)
         (auto intro!: intros simp: eval_fds_newman eval_fds_deriv_zeta eval_fds_mult eval_fds_zeta)
    finally show ?thesis .
  qed

  have conv: "fds_converges F s" if "Re s \<ge> 1" for s
  proof (rule Newman_Ingham_1)
    have "(\<lambda>n. \<MM> (real n) - ln (real n)) \<in> O(\<lambda>_. 1)"
      using mertens_bounded by (rule landau_o.big.compose) real_asymp
    from natfun_bigo_1E[OF this, of 1]
      obtain c' where c': "c' \<ge> 1" "\<And>n. \<bar>\<MM> (real n) - ln (real n)\<bar> \<le> c'" by auto
    have "Bseq (fds_nth F)"
    proof (intro BseqI allI)
      fix n :: nat
      show "norm (fds_nth F n) \<le> (c' + norm c)" unfolding F_def using c'
        by (auto simp: fds_nth_zeta fds_nth_deriv fds_nth_newman scaleR_conv_of_real in_Reals_norm
                 intro!: order.trans[OF norm_triangle_ineq] add_mono)
    qed (insert c', auto intro: add_pos_nonneg)
    thus "fds_nth F \<in> O(\<lambda>_. 1)" by (simp add: natfun_bigo_iff_Bseq)
  next
    show "f analytic_on {s. Re s \<ge> 1}" by fact
  next
    show "eval_fds F s = f s" if "Re s > 1" for s using that by (rule eval_F)
  qed (insert that, auto simp: F_def intro!: intros)
  from conv[of 1] have "summable (\<lambda>n. fds_nth F n / of_nat n)"
    unfolding fds_converges_def by auto
  also have "?this \<longleftrightarrow> summable (\<lambda>n. (\<MM> n - Ln n + c) / n)"
    by (intro summable_cong eventually_mono[OF eventually_gt_at_top[of 0]])
       (auto simp: F_def fds_nth_newman fds_nth_deriv fds_nth_zeta scaleR_conv_of_real
             intro!: sum.cong dest: prime_gt_0_nat)
  finally have "summable (\<lambda>n. (\<MM> n - Re (Ln (of_nat n)) + Re c) / n)"
    by (auto dest: summable_Re)
  also have "?this \<longleftrightarrow> summable (\<lambda>n. (\<MM> n - ln n + Re c) / n)"
    by (intro summable_cong eventually_mono[OF eventually_gt_at_top[of 0]]) (auto intro!: sum.cong)
  finally show ?thesis using that[of "Re c"] by blast
qed

text \<open>
  Next, we prove a lemma given by Newman stating that if the sum $\sum a_n / n$ exists and
  $a_n + \ln n$ is nondecreasing, then $a_n$ must tend to 0. Unfortunately, the proof is
  rather tedious, but so is the paper version by Newman.
\<close>
lemma sum_goestozero_lemma:
  fixes d::real
  assumes d: "\<bar>\<Sum>i = M..N. a i / i\<bar> < d" and le: "\<And>n. a n + ln n \<le> a (Suc n) + ln (Suc n)"
      and "0 < M" "M < N"
    shows "a M \<le> d * N / (real N - real M) + (real N - real M) / M \<and>
          -a N \<le> d * N / (real N - real M) + (real N - real M) / M"
proof -
  have "0 \<le> d"
    using assms by linarith+
  then have "0 \<le> d * N / (N - M + 1)" by simp
  then have le_dN: "\<lbrakk>0 \<le> x \<Longrightarrow> x \<le> d * N / (N - M + 1)\<rbrakk> \<Longrightarrow> x \<le> d * N / (N - M + 1)" for x::real
    by linarith
  have le_a_ln: "a m + ln m \<le> a n + ln n" if "n \<ge> m" for n m
    by (rule transitive_stepwise_le) (use le that in auto)
  have *: "x \<le> b \<and> y \<le> b" if "a \<le> b" "x \<le> a" "y \<le> a" for a b x y::real
    using that by linarith
  show ?thesis
  proof (rule *)
    show "d * N / (N - M) + ln (N / M) \<le> d * N / (real N - real M) + (real N - real M) / M"
      using \<open>0 < M\<close> \<open>M < N\<close> ln_le_minus_one [of "N / M"]
      by (simp add: of_nat_diff) (simp add: divide_simps)
  next
    have "a M - ln (N / M) \<le> (d * N) / (N - M + 1)"
    proof (rule le_dN)
      assume 0: "0 \<le> a M - ln (N / M)"
      have "(Suc N - M) * (a M - ln (N / M)) / N = (\<Sum>i = M..N. (a M - ln (N / M)) / N)"
        by simp
      also have "\<dots> \<le> (\<Sum>i = M..N. a i / i)"
      proof (rule sum_mono)
        fix i
        assume i: "i \<in> {M..N}"
        with \<open>0 < M\<close> have "0 < i" by auto
        have "(a M - ln (N / M)) / N \<le> (a M - ln (N / M)) / i"
          using 0 using i \<open>0 < M\<close> by (simp add: frac_le_eq divide_simps mult_left_mono)
        also have "a M + ln (real M) \<le> a i + ln (real N)"
          by (rule order.trans[OF le_a_ln[of M i]]) (use i assms in auto)
        hence "(a M - ln (N / M)) / i \<le> a i / real i"
          using assms i by (intro divide_right_mono) (auto simp: ln_div field_simps)
        finally show "(a M - ln (N / M)) / real N \<le> a i / real i" .
      qed
      finally have "((Suc N) - M) * (a M - ln (N / M)) / N \<le> \<bar>\<Sum>i = M..N. a i / i\<bar>"
        by simp
      also have "\<dots> \<le> d" using d by simp
      finally have "((Suc N) - M) * (a M - ln (N / M)) / N \<le> d" .
      then show ?thesis
        using \<open>M < N\<close>  by (simp add: of_nat_diff field_simps)
    qed
    also have "\<dots> \<le> d * N / (N - M)"
      using assms(1,4) by (simp add: field_simps)
    finally show "a M \<le> d * N / (N - M) + ln (N / M)" by simp
  next
    have "- a N - ln (N / M) \<le> (d * N) / (N - M + 1)"
    proof (rule le_dN)
      assume 0: "0 \<le> - a N - ln (N / M)"
      have "(\<Sum>i = M..N. a i / i) \<le> (\<Sum>i = M..N. (a N + ln (N / M)) / N)"
      proof (rule sum_mono)
        fix i
        assume i: "i \<in> {M..N}"
        with \<open>0 < M\<close> have "0 < i" by auto
        have "a i + ln (real M) \<le> a N + ln (real N)"
          by (rule order.trans[OF _ le_a_ln[of i N]]) (use i assms in auto)
        hence "a i / i \<le> (a N + ln (N / M)) / i"
          using assms(3,4) by (intro divide_right_mono) (auto simp: field_simps ln_div)
        also have "\<dots> \<le> (a N + ln (N / M)) / N"
          using i \<open>i > 0\<close> 0 by (intro divide_left_mono_neg) auto
        finally show "a i / i \<le> (a N + ln (N / M)) / N" .
      qed
      also have "\<dots> = ((Suc N) - M) * (a N + ln (N / M)) / N"
        by simp
      finally have "(\<Sum>i = M..N. a i / i) \<le> (real (Suc N) - real M) * (a N + ln (N / M)) / N"
        using \<open>M < N\<close> by (simp add: of_nat_diff)
      then have "-((real (Suc N) - real M) * (a N + ln (N / M)) / N) \<le> \<bar>\<Sum>i = M..N. a i / i\<bar>"
        by linarith
      also have "\<dots> \<le> d" using d by simp
      finally have "- ((real (Suc N) - real M) * (a N + ln (N / M)) / N) \<le> d" .
      then show ?thesis
        using \<open>M < N\<close>  by (simp add: of_nat_diff field_simps)
    qed
    also have "\<dots> \<le> d * N / real (N - M)"
      using \<open>0 < M\<close> \<open>M < N\<close> \<open>0 \<le> d\<close> by (simp add: field_simps)
    finally show "-a N \<le> d * N / real (N - M) + ln (N / M)" by simp
  qed
qed

proposition sum_goestozero_theorem:
  assumes summ: "summable (\<lambda>i. a i / i)"
      and le:   "\<And>n. a n + ln n \<le> a (Suc n) + ln (Suc n)"
    shows "a \<longlonglongrightarrow> 0"
proof (clarsimp simp: lim_sequentially)
  fix r::real
  assume "r > 0"
  have *: "\<exists>n0. \<forall>n\<ge>n0. \<bar>a n\<bar> < \<epsilon>" if \<epsilon>: "0 < \<epsilon>" "\<epsilon> < 1" for \<epsilon>
  proof -
    have "0 < (\<epsilon> / 8)\<^sup>2" using \<open>0 < \<epsilon>\<close>  by simp
    then obtain N0 where N0: "\<And>m n. m \<ge> N0 \<Longrightarrow> norm (\<Sum>k=m..n. (\<lambda>i. a i / i) k) < (\<epsilon> / 8)\<^sup>2"
      by (metis summable_partial_sum_bound summ)
    obtain N1 where "real N1 > 4 / \<epsilon>"
      using reals_Archimedean2[of "4 / \<epsilon>"] \<epsilon> by auto
    hence "N1 \<noteq> 0" and N1: "1 / real N1 < \<epsilon> / 4" using \<epsilon>
      by (auto simp: divide_simps mult_ac intro: Nat.gr0I)

    have "\<bar>a n\<bar> < \<epsilon>" if n: "n \<ge> 2 * N0 + N1 + 7" for n
    proof -
      define k where "k = \<lfloor>n * \<epsilon>/4\<rfloor>"
      have "n * \<epsilon> / 4 > 1" and "n * \<epsilon> / 4 \<le> n / 4" and "n / 4 < n"
        using less_le_trans[OF N1, of "n / N1 * \<epsilon> / 4"] \<open>N1 \<noteq> 0\<close> \<epsilon> n by (auto simp: field_simps)
      hence k: "k > 0" "4 * k \<le> n" "nat k < n" "(n * \<epsilon> / 4) - 1 < k" "k \<le> (n * \<epsilon> / 4)"
        unfolding k_def by linarith+

      have "-a n < \<epsilon>"
      proof -
        have "N0 \<le> n - nat k"
          using n k by linarith
        then have *: "\<bar>\<Sum>k = n - nat k .. n. a k / k\<bar> < (\<epsilon> / 8)\<^sup>2"
          using N0 [of "n - nat k" n] by simp
        have "-a n \<le> (\<epsilon> / 8)\<^sup>2 * n / \<lfloor>n * \<epsilon> / 4\<rfloor> + \<lfloor>n * \<epsilon> / 4\<rfloor> / (n - k)"
          using sum_goestozero_lemma [OF * le, THEN conjunct2] k by (simp add: of_nat_diff k_def)
        also have "\<dots>< \<epsilon>"
        proof -
          have "\<epsilon> / 16 * n / k < 2"
            using k by (auto simp: field_simps)
          then have "\<epsilon> * (\<epsilon> / 16 * n / k) < \<epsilon> * 2"
            using \<epsilon> mult_less_cancel_left_pos by blast
          then have "(\<epsilon> / 8)\<^sup>2 * n / k < \<epsilon> / 2"
            by (simp add: field_simps power2_eq_square)
          moreover have "k / (n - k) < \<epsilon> / 2"
          proof -
            have "(\<epsilon> + 2) * k < 4 * k" using k \<epsilon> by simp
            also have "\<dots> \<le> \<epsilon> * real n" using k by (auto simp: field_simps)
            finally show ?thesis using k by (auto simp: field_simps)
          qed
          ultimately show ?thesis unfolding k_def by linarith
        qed
        finally show ?thesis .
      qed
      moreover have "a n < \<epsilon>"
      proof -
        have "N0 \<le> n" using n k by linarith
        then have *: "\<bar>\<Sum>k = n .. n + nat k. a k / k\<bar> < (\<epsilon>/8)\<^sup>2"
          using N0 [of n "n + nat k"] by simp
        have "a n \<le> (\<epsilon>/8)\<^sup>2 * (n + nat k) / k + k / n"
          using sum_goestozero_lemma [OF * le, THEN conjunct1] k by (simp add: of_nat_diff)
        also have "\<dots>< \<epsilon>"
        proof -
          have "4 \<le> 28 * real_of_int k" using k by linarith
          then have "\<epsilon>/16 * n / k < 2" using k by (auto simp: field_simps)
          have "\<epsilon> * (real n + k) < 32 * k"
          proof -
            have "\<epsilon> * n / 4 < k + 1" by (simp add: mult.commute k_def)
            then have "\<epsilon> * n < 4 * k + 4" by (simp add: divide_simps)
            also have "\<dots> \<le> 8 * k" using k by auto
            finally have 1: "\<epsilon> * real n < 8 * k" .
            have 2: "\<epsilon> * k < k" using k \<epsilon> by simp
            show ?thesis using k add_strict_mono [OF 1 2] by (simp add: algebra_simps)
        qed
          then have "(\<epsilon> / 8)\<^sup>2 * real (n + nat k) / k < \<epsilon> / 2"
            using \<epsilon> k by (simp add: divide_simps mult_less_0_iff power2_eq_square)
          moreover have "k / n < \<epsilon> / 2"
            using k \<epsilon> by (auto simp: k_def field_simps)
          ultimately show ?thesis by linarith
        qed
        finally show ?thesis .
      qed
      ultimately show ?thesis by force
    qed
    then show ?thesis by blast
  qed
  show "\<exists>n0. \<forall>n\<ge>n0. \<bar>a n\<bar> < r"
    using * [of "min r (1/5)"] \<open>0 < r\<close> by force
qed


text \<open>
  This leads us to the main intermediate result:
\<close>
lemma Mertens_convergent: "convergent (\<lambda>n::nat. \<MM> n - ln n)"
proof -
  obtain c where c: "summable (\<lambda>n. (\<MM> n - ln n + c) / n)"
    by (blast intro: mertens_summable)
  then obtain l where l: "(\<lambda>n. (\<MM> n - ln n + c) / n) sums l"
    by (auto simp: summable_def)
  have *: "(\<lambda>n. \<MM> n - ln n + c) \<longlonglongrightarrow> 0"
    by (rule sum_goestozero_theorem[OF c]) auto
  hence "(\<lambda>n. \<MM> n - ln n) \<longlonglongrightarrow> -c"
    by (simp add: tendsto_iff dist_norm)
  thus ?thesis by (rule convergentI)
qed

corollary \<MM>_minus_ln_limit:
  obtains c where "((\<lambda>x::real. \<MM> x - ln x) \<longlongrightarrow> c) at_top"
proof -
  from Mertens_convergent obtain c where "(\<lambda>n. \<MM> n - ln n) \<longlonglongrightarrow> c"
    by (auto simp: convergent_def)
  hence 1: "((\<lambda>x::real. \<MM> (nat \<lfloor>x\<rfloor>) - ln (nat \<lfloor>x\<rfloor>)) \<longlongrightarrow> c) at_top" 
    by (rule filterlim_compose) real_asymp
  have 2: "((\<lambda>x::real. ln (nat \<lfloor>x\<rfloor>) - ln x) \<longlongrightarrow> 0) at_top"
    by real_asymp
  have 3: "((\<lambda>x. \<MM> x - ln x) \<longlongrightarrow> c) at_top"
    using tendsto_add[OF 1 2] by simp
  with that show ?thesis by blast
qed


subsection \<open>The asymptotics of the prime-counting functions\<close>

text \<open>
  We will now use the above result to prove the asymptotics of the prime-counting functions
  $\vartheta(x) \sim x$, $\psi(x) \sim x$, and $\pi(x) \sim x / \ln x$. The last of these is 
  typically called the Prime Number Theorem, but since these functions can be expressed in terms 
  of one another quite easily, knowing the asymptotics of any of them immediately gives the 
  asymptotics of the other ones.

  In this sense, all of the above are equivalent formulations of the Prime Number Theorem.
  The one we shall tackle first, due to its strong connection to the $\mathfrak{M}$ function, is
  $\vartheta(x) \sim x$.

  We know that $\mathfrak{M}(x)$ has the asymptotic expansion
  $\mathfrak{M}(x) = \ln x + c + o(1)$. We also know that
  \[\vartheta(x) = x\mathfrak{M}(x) - \int\nolimits_2^x \mathfrak{M}(t) \,\mathrm{d}t\ .\]
  Substituting in the above asymptotic equation, we obtain:
  \begin{align*}
  \vartheta(x) &= x\ln x + cx + o(x) - \int\nolimits_2^x \ln t + c + o(1) \,\mathrm{d}t\\
            &= x\ln x + cx + o(x) - (x\ln x - x + cx + o(x))\\
            &= x + o(x)
  \end{align*}
  In conclusion, $\vartheta(x) \sim x$.
\<close>
theorem \<theta>_asymptotics: "\<theta> \<sim>[at_top] (\<lambda>x. x)"
proof -
  from \<MM>_minus_ln_limit obtain c where c: "((\<lambda>x. \<MM> x - ln x) \<longlongrightarrow> c) at_top"
    by auto
  define r where "r = (\<lambda>x. \<MM> x - ln x - c)"
  have \<MM>_expand: "\<MM> = (\<lambda>x. ln x + c + r x)"
    by (simp add: r_def)
  have r: "r \<in> o(\<lambda>_. 1)" unfolding r_def
    using tendsto_add[OF c tendsto_const[of "-c"]] by (intro smalloI_tendsto) auto

  define r' where "r' = (\<lambda>x. integral {2..x} r)"
  have integrable_r: "r integrable_on {x..y}"
    if "2 \<le> x" for x y :: real using that unfolding r_def
    by (intro integrable_diff integrable_primes_M)
       (auto intro!: integrable_continuous_real continuous_intros)
  hence integral: "(r has_integral r' x) {2..x}" if "x \<ge> 2" for x
    by (auto simp: has_integral_iff r'_def)
  have r': "r' \<in> o(\<lambda>x. x)" using integrable_r unfolding r'_def
    by (intro integral_smallo[OF r]) (auto simp: filterlim_ident)

  define C where "C = 2 * (c + ln 2 - 1)"
  have "\<theta> \<sim>[at_top] (\<lambda>x. x + (r x * x + C - r' x))"
  proof (intro asymp_equiv_refl_ev eventually_mono[OF eventually_gt_at_top])
    fix x :: real assume x: "x > 2"
    have "(\<MM> has_integral ((x * ln x - x + c * x) - (2 * ln 2 - 2 + c * 2) + r' x)) {2..x}"
      unfolding \<MM>_expand using x
      by (intro has_integral_add[OF fundamental_theorem_of_calculus integral])
         (auto simp flip: has_field_derivative_iff_has_vector_derivative
               intro!: derivative_eq_intros continuous_intros)
    from has_integral_unique[OF \<theta>_conv_\<MM>_integral this]
      show "\<theta> x = x + (r x * x + C - r' x)" using x
      by (simp add: field_simps \<MM>_expand C_def)
  qed
  also have "(\<lambda>x. r x * x + C - r' x) \<in> o(\<lambda>x. x)"
  proof (intro sum_in_smallo r)
    show "(\<lambda>_. C) \<in> o(\<lambda>x. x)" by real_asymp
  qed (insert landau_o.small_big_mult[OF r, of "\<lambda>x. x"] r', simp_all)
  hence "(\<lambda>x. x + (r x * x + C - r' x)) \<sim>[at_top] (\<lambda>x. x)"
    by (subst asymp_equiv_add_right) auto
  finally show ?thesis by auto
qed

text \<open>
  The various other forms of the Prime Number Theorem follow as simple corollaries.
\<close>
corollary \<psi>_asymptotics: "\<psi> \<sim>[at_top] (\<lambda>x. x)"
  using \<theta>_asymptotics PNT4_imp_PNT5 by simp
  
corollary prime_number_theorem: "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)"
  using \<theta>_asymptotics PNT4_imp_PNT1 by simp

corollary ln_\<pi>_asymptotics: "(\<lambda>x. ln (\<pi> x)) \<sim>[at_top] ln"
  using prime_number_theorem PNT1_imp_PNT1' by simp

corollary \<pi>_ln_\<pi>_asymptotics: "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x)"
  using prime_number_theorem PNT1_imp_PNT2 by simp

corollary nth_prime_asymptotics: "(\<lambda>n. real (nth_prime n)) \<sim>[at_top] (\<lambda>n. real n * ln (real n))"
  using \<pi>_ln_\<pi>_asymptotics PNT2_imp_PNT3 by simp


text \<open>
  The following versions use a little less notation.
\<close>
corollary prime_number_theorem': "((\<lambda>x. \<pi> x / (x / ln x)) \<longlongrightarrow> 1) at_top"
  using prime_number_theorem
  by (rule asymp_equivD_strong[OF _ eventually_mono[OF eventually_gt_at_top[of 1]]]) auto

corollary prime_number_theorem'':
  "(\<lambda>x. card {p. prime p \<and> real p \<le> x}) \<sim>[at_top] (\<lambda>x. x / ln x)"
proof -
  have "\<pi> = (\<lambda>x. card {p. prime p \<and> real p \<le> x})"
    by (intro ext) (simp add: \<pi>_def prime_sum_upto_def)
  with prime_number_theorem show ?thesis by simp
qed

corollary prime_number_theorem''':
  "(\<lambda>n. card {p. prime p \<and> p \<le> n}) \<sim>[at_top] (\<lambda>n. real n / ln (real n))"
proof -
  have "(\<lambda>n. card {p. prime p \<and> real p \<le> real n}) \<sim>[at_top] (\<lambda>n. real n / ln (real n))"
    using prime_number_theorem''
    by (rule asymp_equiv_compose') (simp add: filterlim_real_sequentially)
  thus ?thesis by simp
qed

(*<*)
unbundle no_prime_counting_notation
(*>*)

end