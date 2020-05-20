(*
    File:      Dirichlet_L_Functions.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Dirichlet $L$-functions\<close>
theory Dirichlet_L_Functions
imports 
  Dirichlet_Characters
  "HOL-Library.Landau_Symbols"
  "Zeta_Function.Zeta_Function"
begin

text \<open>
  We can now define the Dirichlet $L$-functions. These are essentially the functions in the complex
  plane that the Dirichlet series $\sum_{k=1}^\infty \chi(k) k^{-s}$ converge to, for some fixed 
  Dirichlet character $\chi$.

  First of all, we need to take care of a syntactical problem: The notation for vectors uses 
  $\chi$ as syntax, which causes some annoyance to us, so we disable it locally.
\<close>

(*<*)
bundle vec_lambda_notation
begin
notation vec_lambda (binder "\<chi>" 10)
end

bundle no_vec_lambda_notation
begin
no_notation vec_lambda (binder "\<chi>" 10)
end
(*>*)


subsection \<open>Definition and basic properties\<close>

(*<*)
context
  includes no_vec_lambda_notation
begin
(*>*)

text \<open>
  We now define Dirichlet $L$ functions as a finite linear combination of Hurwitz $\zeta$ functions.
  This has the advantage that we directly get the analytic continuation over the full domain
  and only need to prove that the series really converges to this definition whenever it
  does converge, which is not hard to do.
\<close>
definition Dirichlet_L :: "nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex" where
  "Dirichlet_L m \<chi> s = 
     (if s = 1 then 
        if \<chi> = principal_dchar m then 0 else eval_fds (fds \<chi>) 1
      else 
        of_nat m powr - s * (\<Sum>k = 1..m. \<chi> k * hurwitz_zeta (real k / real m) s))"

lemma Dirichlet_L_conv_hurwitz_zeta_nonprincipal:
  assumes "s \<noteq> 1"
  shows   "Dirichlet_L n \<chi> s =
             of_nat n powr -s * (\<Sum>k = 1..n. \<chi> k * hurwitz_zeta (real k / real n) s)"
  using assms by (simp add: Dirichlet_L_def)

text \<open>
  Analyticity everywhere except $1$ is trivial by the above definition, since the
  Hurwitz $\zeta$ function is analytic everywhere except $1$. For $L$ functions of non
  principal characters, we will have to show the analyticity at $1$ separately later.
\<close>
lemma holomorphic_Dirichlet_L_weak:
  assumes "m > 0" "1 \<notin> A"
  shows   "Dirichlet_L m \<chi> holomorphic_on A"
proof -
  have "(\<lambda>s. of_nat m powr - s * (\<Sum>k = 1..m. \<chi> k * hurwitz_zeta (real k / real m) s))
           holomorphic_on A"
    using assms unfolding Dirichlet_L_def by (intro holomorphic_intros) auto
  also have "?this \<longleftrightarrow> ?thesis"
    using assms by (intro holomorphic_cong refl) (auto simp: Dirichlet_L_def)
  finally show ?thesis .
qed

(*<*)
end
(*>*)


context dcharacter
begin
(*<*)
context
  includes no_vec_lambda_notation dcharacter_syntax
begin
(*>*)

text \<open>
  For a real value greater than 1, the formal Dirichlet series of an $L$ function
  for some character $\chi$ converges to the L function.
\<close>
lemma
  fixes s :: complex
  assumes s: "Re s > 1"
  shows   abs_summable_Dirichlet_L:  "summable (\<lambda>n. norm (\<chi> n * of_nat n powr -s))"
    and   summable_Dirichlet_L:      "summable (\<lambda>n. \<chi> n * of_nat n powr -s)"
    and   sums_Dirichlet_L:          "(\<lambda>n. \<chi> n * n powr -s) sums Dirichlet_L n \<chi> s"
    and   Dirichlet_L_conv_eval_fds_weak: "Dirichlet_L n \<chi> s = eval_fds (fds \<chi>) s"
proof -
  define L where "L = (\<Sum>n. \<chi> n * of_nat n powr -s)"
  show "summable (\<lambda>n. norm (\<chi> n * of_nat n powr -s))"
    by (subst summable_Suc_iff [symmetric], 
        rule summable_comparison_test [OF _ summable_zeta_real[of "Re s"]])
        (insert s norm, auto intro!: exI[of _ 0] simp: norm_mult norm_powr_real_powr)
  thus summable: "summable (\<lambda>n. \<chi> n * of_nat n powr -s)"
    by (rule summable_norm_cancel)

  hence "(\<lambda>n. \<chi> n * of_nat n powr -s) sums L" by (simp add: L_def sums_iff)
  from this have "(\<lambda>m. \<Sum>k = m * n..<m * n + n. \<chi> k * of_nat k powr - s) sums L"
    by (rule sums_group) (use n in auto)
  also have "(\<lambda>m. \<Sum>k = m * n..<m * n + n. \<chi> k * of_nat k powr - s) = 
               (\<lambda>m. of_nat n powr -s * (\<Sum>k = 1..n. \<chi> k * (of_nat m + of_nat k / of_nat n) powr - s))"
  proof (rule ext, goal_cases)
    case (1 m)
    have "(\<Sum>k = m * n..<m * n + n. \<chi> k * of_nat k powr - s) = 
            (\<Sum>k=0..<n. \<chi> (k + m * n) * of_nat (m * n + k) powr - s)"
      by (intro sum.reindex_bij_witness[of _ "\<lambda>k. k + m * n" "\<lambda>k. k - m * n"]) auto
    also have "\<dots> = (\<Sum>k=0..<n. \<chi> k * of_nat (m * n + k) powr - s)"
      by (simp add: periodic_mult)
    also have "\<dots> = (\<Sum>k=0..<n. \<chi> k * (of_nat m + of_nat k / of_nat n) powr - s * of_nat n powr -s)"
    proof (intro sum.cong refl, goal_cases)
      case (1 k)
      have "of_nat (m * n + k) = (of_nat m + of_nat k / of_nat n :: complex) * of_nat n"
        using n by (simp add: divide_simps del: div_mult_self1 div_mult_self2 div_mult_self3 div_mult_self4)
      also have "\<dots> powr -s = (of_nat m + of_nat k / of_nat n) powr -s * of_nat n powr -s"
        by (rule powr_times_real) auto
      finally show ?case by simp
    qed
    also have "\<dots> = of_nat n powr -s * (\<Sum>k=0..<n. \<chi> k * (of_nat m + of_nat k / of_nat n) powr - s)"
      by (subst sum_distrib_left) (simp_all add: mult_ac)
    also have "(\<Sum>k = 0..<n. \<chi> k * (of_nat m + of_nat k / of_nat n) powr - s) =
                 (\<Sum>k = 1..<n. \<chi> k * (of_nat m + of_nat k / of_nat n) powr - s)"
      by (intro sum.mono_neutral_right) (auto simp: Suc_le_eq)
    also have "\<dots> = (\<Sum>k = 1..n. \<chi> k * (of_nat m + of_nat k / of_nat n) powr - s)"
      using periodic_mult[of 0 1] by (intro sum.mono_neutral_left) auto
    finally show ?case .
  qed
  finally have "\<dots> sums L" .
  moreover have "(\<lambda>m. of_nat n powr - s * (\<Sum>k=1..n. \<chi> k * (of_nat m + of_real (of_nat k / of_nat n)) powr - s)) sums
                   (of_nat n powr - s * (\<Sum>k=1..n. \<chi> k * hurwitz_zeta (of_nat k / of_nat n) s))"
    using s by (intro sums_sum sums_mult sums_hurwitz_zeta) auto
  ultimately have "L = \<dots>"
    by (simp add: sums_iff)
  also have "\<dots> = Dirichlet_L n \<chi> s" using assms by (auto simp: Dirichlet_L_def)
  finally have "Dirichlet_L n \<chi> s = (\<Sum>n. \<chi> n * of_nat n powr -s)"
    by (simp add: L_def)
  with summable show "(\<lambda>n. \<chi> n * n powr -s) sums Dirichlet_L n \<chi> s"
    by (simp add: sums_iff L_def)
  thus "Dirichlet_L n \<chi> s = eval_fds (fds \<chi>) s"
    by (simp add: eval_fds_def sums_iff powr_minus field_simps fds_nth_fds')
qed

lemma fds_abs_converges_weak: "Re s > 1 \<Longrightarrow> fds_abs_converges (fds \<chi>) s"
  using abs_summable_Dirichlet_L[of s]
  by (simp add: fds_abs_converges_def powr_minus divide_simps fds_nth_fds')

lemma abs_conv_abscissa_weak: "abs_conv_abscissa (fds \<chi>) \<le> 1"
proof (rule abs_conv_abscissa_leI, goal_cases)
  case (1 c)
  thus ?case
    by (intro exI[of _ "of_real c"] conjI fds_abs_converges_weak) auto
qed


text \<open>
  Dirichlet $L$ functions have the Euler product expansion
  \[L(\chi, s) = \prod_p \left(1 - \frac{\chi(p)}{p^{-s}}\right)\]
  for all $s$ with $\mathfrak{R}(s) > 1$.
\<close>
lemma
  fixes s :: complex assumes s: "Re s > 1"
  shows   Dirichlet_L_euler_product_LIMSEQ:
            "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - \<chi> p / nat_power p s) else 1)
                \<longlonglongrightarrow> Dirichlet_L n \<chi> s" (is ?th1)
    and   Dirichlet_L_abs_convergent_euler_product:
            "abs_convergent_prod (\<lambda>p. if prime p  then inverse (1 - \<chi> p / p powr s) else 1)" 
            (is ?th2)
proof -
  have mult: "completely_multiplicative_function (fds_nth (fds \<chi>))"
    using mult.completely_multiplicative_function_axioms by (simp add: fds_nth_fds')
  have conv: "fds_abs_converges (fds \<chi>) s"
    using abs_summable_Dirichlet_L[OF s]
    by (simp add: fds_abs_converges_def fds_nth_fds' powr_minus divide_simps)
  have "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - \<chi> p / nat_power p s) else 1)
          \<longlonglongrightarrow> eval_fds (fds \<chi>) s"
    using fds_euler_product_LIMSEQ' [OF mult conv] by (simp add: fds_nth_fds' cong: if_cong)
  also have "eval_fds (fds \<chi>) s = Dirichlet_L n \<chi> s"
    using sums_Dirichlet_L[OF s] unfolding eval_fds_def
    by (simp add: sums_iff fds_nth_fds' powr_minus divide_simps)
  finally show ?th1 .
  from fds_abs_convergent_euler_product' [OF mult conv] show ?th2
      by (simp add: fds_nth_fds cong: if_cong)
  qed
  
lemma Dirichlet_L_Re_gt_1_nonzero:
  assumes "Re s > 1"
  shows   "Dirichlet_L n \<chi> s \<noteq> 0"
proof -
  have "completely_multiplicative_function (fds_nth (fds \<chi>))"
    by (simp add: fds_nth_fds' mult.completely_multiplicative_function_axioms)
  moreover have "fds_abs_converges (fds \<chi>) s"
    using abs_summable_Dirichlet_L[OF assms] 
    by (simp add: fds_abs_converges_def fds_nth_fds' powr_minus divide_simps)
  ultimately have "(eval_fds (fds \<chi>) s = 0) \<longleftrightarrow> (\<exists>p. prime p \<and> fds_nth (fds \<chi>) p = nat_power p s)"
    by (rule fds_abs_convergent_zero_iff)
  also have "eval_fds (fds \<chi>) s = Dirichlet_L n \<chi> s"
    using Dirichlet_L_conv_eval_fds_weak[OF assms] by simp
  also have "\<not>(\<exists>p. prime p \<and> fds_nth (fds \<chi>) p = nat_power p s)"
  proof safe
    fix p :: nat assume p: "prime p" "fds_nth (fds \<chi>) p = nat_power p s"
    from p have "real 1 < real p" by (subst of_nat_less_iff) (auto simp: prime_gt_Suc_0_nat)
    also have "\<dots> = real p powr 1" by simp
    also from p and assms have "real p powr 1 \<le> real p powr Re s" 
      by (intro powr_mono) (auto simp: real_of_nat_ge_one_iff prime_ge_Suc_0_nat)
    also have "\<dots> = norm (nat_power p s)" by (simp add: norm_nat_power norm_powr_real_powr)
    also have "nat_power p s = fds_nth (fds \<chi>) p" using p by simp
    also have "norm \<dots> \<le> 1" by (auto simp: fds_nth_fds' norm)
    finally show False by simp
  qed
  finally show ?thesis .
qed

lemma sum_dcharacter_antimono_bound:
  fixes x0 a b :: real and f f' :: "real \<Rightarrow> real"
  assumes nonprincipal: "\<chi> \<noteq> \<chi>\<^sub>0"
  assumes x0: "x0 \<ge> 0" and ab: "x0 \<le> a" "a < b"
  assumes f': "\<And>x. x \<ge> x0 \<Longrightarrow> (f has_field_derivative f' x) (at x)"
  assumes f_nonneg: "\<And>x. x \<ge> x0 \<Longrightarrow> f x \<ge> 0"
  assumes f'_nonpos: "\<And>x. x \<ge> x0 \<Longrightarrow> f' x \<le> 0"
  shows   "norm (\<Sum>n\<in>real -` {a<..b}. \<chi> n * (f (real n))) \<le> 2 * real (totient n) * f a"
proof -
  note deriv = has_field_derivative_at_within [OF f']
  let ?A = "sum_upto \<chi>"
  have cont: "continuous_on {a..b} f"
    by (rule DERIV_continuous_on[OF deriv]) (use ab in auto)
  have I': "(f' has_integral (f b - f a)) {a..b}"
    using ab deriv by (intro fundamental_theorem_of_calculus)
                      (auto simp: has_field_derivative_iff_has_vector_derivative [symmetric])

  define I where "I = integral {a..b} (\<lambda>t. ?A t * of_real (f' t))"
  define C where "C = real (totient n)"
  have C_nonneg: "C \<ge> 0" by (simp add: C_def)
  have C: "norm (?A x) \<le> C" for x
  proof -
    have "?A x = (\<Sum>k\<le>nat \<lfloor>x\<rfloor>. \<chi> k)" unfolding sum_upto_altdef
      by (intro sum.mono_neutral_left) auto
    also have "norm \<dots> \<le> C" unfolding C_def using nonprincipal
      by (rule sum_dcharacter_atMost_le)
    finally show ?thesis .
  qed
    
  have I: "((\<lambda>t. ?A t * f' t) has_integral ?A b * f b - ?A a * f a - 
             (\<Sum>n\<in>real -` {a<..b}. \<chi> n * f (real n))) {a..b}" using ab x0 cont f'
    by (intro partial_summation_strong[of "{}"] has_vector_derivative_of_real) auto
  hence "(\<Sum>n\<in>real -` {a<..b}. \<chi> n * f (real n)) = ?A b * f b - ?A a * f a - I"
    by (simp add: has_integral_iff I_def)
  also have "norm \<dots> \<le> norm (?A b) * norm (f b) + norm (?A a) * norm (f a) + norm I"
    by (rule order.trans[OF norm_triangle_ineq4] add_mono)+ (simp_all add: norm_mult)
  also have "norm I \<le> integral {a..b} (\<lambda>t. of_real (-C) * of_real (f' t))" 
    unfolding I_def using I I' f'_nonpos ab C
    by (intro integral_norm_bound_integral integrable_on_cmult_left)
       (simp_all add: has_integral_iff norm_mult mult_right_mono_neg)
  also have "\<dots> = - (C * (f b - f a))"
    using integral_linear[OF _ bounded_linear_of_real, of f' "{a..b}"] I'
    by (simp add: has_integral_iff o_def )
  also have "\<dots> = C * (f a - f b)" by (simp add: algebra_simps)
  also have "norm (sum_upto \<chi> b) \<le> C" by (rule C)
  also have "norm (sum_upto \<chi> a) \<le> C" by (rule C)
  also have "C * norm (f b) + C * norm (f a) + C * (f a - f b) = 2 * C * f a"
    using f_nonneg[of a] f_nonneg[of b] ab by (simp add: algebra_simps)
  finally show ?thesis by (simp add: mult_right_mono C_def)
qed

lemma summable_dcharacter_antimono:
  fixes x0 a b :: real and f f' :: "real \<Rightarrow> real"
  assumes nonprincipal: "\<chi> \<noteq> \<chi>\<^sub>0"
  assumes f': "\<And>x. x \<ge> x0 \<Longrightarrow> (f has_field_derivative f' x) (at x)"
  assumes f_nonneg: "\<And>x. x \<ge> x0 \<Longrightarrow> f x \<ge> 0"
  assumes f'_nonpos: "\<And>x. x \<ge> x0 \<Longrightarrow> f' x \<le> 0"
  assumes lim: "(f \<longlongrightarrow> 0) at_top"
  shows   "summable (\<lambda>n. \<chi> n * f n)"
proof (rule summable_bounded_partials [where ?g = "\<lambda>x. 2 * real (totient n) * f x"], goal_cases)
  case 1
  from eventually_ge_at_top[of "nat \<lceil>x0\<rceil>"] show ?case
  proof eventually_elim
    case (elim x)
    show ?case
    proof (safe, goal_cases)
      case (1 a b)
      with elim have *: "max 0 x0 \<ge> 0" "max 0 x0 \<le> a" "real a < real b" 
        by (simp_all add: nat_le_iff ceiling_le_iff)
      have "(\<Sum>n\<in>{a<..b}. \<chi> n * complex_of_real (f (real n))) =
              (\<Sum>n\<in>real -` {real a<..real b}. \<chi> n * complex_of_real (f (real n)))"
        by (intro sum.cong refl) auto
      also have "norm \<dots> \<le> 2 * real (totient n) * f a"
        using nonprincipal * f' f_nonneg f'_nonpos by (rule sum_dcharacter_antimono_bound) simp_all
      finally show ?case .
    qed
  qed
qed (auto intro!: tendsto_mult_right_zero filterlim_compose[OF lim] filterlim_real_sequentially)

lemma conv_abscissa_le_0:
  fixes s :: real
  assumes nonprincipal: "\<chi> \<noteq> \<chi>\<^sub>0"
  shows  "conv_abscissa (fds \<chi>) \<le> 0"
proof (rule conv_abscissa_leI)
  fix s assume s: "0 < ereal s"
  have "summable (\<lambda>n. \<chi> n * of_real (n powr -s))"
  proof (rule summable_dcharacter_antimono[of 1])
    fix x :: real assume "x \<ge> 1"
    thus "((\<lambda>x. x powr -s) has_field_derivative (-s * x powr (-s-1))) (at x)"
      by (auto intro!: derivative_eq_intros)
  qed (insert s assms, auto intro!: tendsto_neg_powr filterlim_ident)
  thus "\<exists>s'::complex. s' \<bullet> 1 = s \<and> fds_converges (fds \<chi>) s'" using s
    by (intro exI[of _ "of_real s"]) 
       (auto simp: fds_converges_def powr_minus divide_simps powr_of_real [symmetric] fds_nth_fds')
qed

lemma summable_Dirichlet_L':
  assumes nonprincipal: "\<chi> \<noteq> \<chi>\<^sub>0"
  assumes s: "Re s > 0"
  shows  "summable (\<lambda>n. \<chi> n * of_nat n powr -s)"
proof -
  from assms have "fds_converges (fds \<chi>) s"
    by (intro fds_converges le_less_trans[OF conv_abscissa_le_0]) auto
  thus ?thesis by (simp add: fds_converges_def powr_minus divide_simps fds_nth_fds')
qed

lemma 
  assumes "\<chi> \<noteq> \<chi>\<^sub>0"
  shows   Dirichlet_L_conv_eval_fds: "\<And>s. Re s > 0 \<Longrightarrow> Dirichlet_L n \<chi> s = eval_fds (fds \<chi>) s"
    and   holomorphic_Dirichlet_L:   "Dirichlet_L n \<chi> holomorphic_on A"
proof -
  show eq: "Dirichlet_L n \<chi> s = eval_fds (fds \<chi>) s" (is "?f s = ?g s") if "Re s > 0" for s
  proof (cases "s = 1")
    case False
    show ?thesis
    proof (rule analytic_continuation_open[where ?f = ?f and ?g = ?g])
      show "{s. Re s > 1} \<subseteq> {s. Re s > 0} - {1}" by auto
      show "connected ({s. 0 < Re s} - {1})"
        using aff_dim_halfspace_gt[of 0 "1::complex"]
        by (intro connected_punctured_convex convex_halfspace_Re_gt) auto
    qed (insert that n assms False, 
         auto intro!: convex_halfspace_Re_gt open_halfspace_Re_gt exI[of _ 2] 
                      holomorphic_intros holomorphic_Dirichlet_L_weak
                      Dirichlet_L_conv_eval_fds_weak le_less_trans[OF conv_abscissa_le_0])
  qed (insert assms, simp_all add: Dirichlet_L_def)

  have "Dirichlet_L n \<chi> holomorphic_on UNIV"
  proof (rule no_isolated_singularity')
    from n show "Dirichlet_L n \<chi> holomorphic_on (UNIV - {1})"
      by (intro holomorphic_Dirichlet_L_weak) auto
  next
    fix s :: complex assume s: "s \<in> {1}"
    show "Dirichlet_L n \<chi> \<midarrow>s\<rightarrow> Dirichlet_L n \<chi> s"
    proof (rule Lim_transform_eventually)
      from assms have "continuous_on {s. Re s > 0} (eval_fds (fds \<chi>))"
        by (intro holomorphic_fds_eval holomorphic_on_imp_continuous_on)
          (auto intro: le_less_trans[OF conv_abscissa_le_0])
      hence "eval_fds (fds \<chi>) \<midarrow>s\<rightarrow> eval_fds (fds \<chi>) s" using s
        by (subst (asm) continuous_on_eq_continuous_at) (auto simp: open_halfspace_Re_gt isCont_def)
      also have "eval_fds (fds \<chi>) s = Dirichlet_L n \<chi> s"
        using assms s by (simp add: Dirichlet_L_def)
      finally show "eval_fds (fds \<chi>) \<midarrow>s\<rightarrow> Dirichlet_L n \<chi> s" .
    next
      have "eventually (\<lambda>z. z \<in> {z. Re z > 0}) (nhds s)" using s
        by (intro eventually_nhds_in_open) (auto simp: open_halfspace_Re_gt)
      hence "eventually (\<lambda>z. z \<in> {z. Re z > 0}) (at s)"
        unfolding eventually_at_filter by eventually_elim auto
      then show "eventually (\<lambda>z. eval_fds (fds \<chi>) z = Dirichlet_L n \<chi> z) (at s)"
        by eventually_elim (auto intro!: eq [symmetric])
    qed
  qed auto
  thus "Dirichlet_L n \<chi> holomorphic_on A" by (rule holomorphic_on_subset) auto
qed

lemma cnj_Dirichlet_L: 
  "cnj (Dirichlet_L n \<chi> s) = Dirichlet_L n (inv_character \<chi>) (cnj s)"
proof -
  {
    assume *: "\<chi> \<noteq> \<chi>\<^sub>0" "s = 1"
    with summable_Dirichlet_L'[of 1] have "(\<lambda>n. \<chi> n / n) sums eval_fds (fds \<chi>) 1"
      by (simp add: eval_fds_def fds_nth_fds' powr_minus sums_iff divide_simps)
    hence "(\<lambda>n. inv_character \<chi> n / n) sums cnj (eval_fds (fds \<chi>) 1)"
      by (subst (asm) sums_cnj [symmetric]) (simp add: inv_character_def)
    hence "eval_fds (fds (inv_character \<chi>)) 1 = cnj (eval_fds (fds \<chi>) 1)"
      by (simp add: eval_fds_def fds_nth_fds' inv_character_def sums_iff)
  }
  thus ?thesis by (auto simp add: Dirichlet_L_def cnj_powr eval_inv_character)
qed

(*<*)
end
(*>*)
end

(*<*)
context
  includes no_vec_lambda_notation
begin
(*>*)

lemma holomorphic_Dirichlet_L [holomorphic_intros]:
  assumes "n > 1" "\<chi> \<noteq> principal_dchar n \<and> dcharacter n \<chi> \<or> \<chi> = principal_dchar n \<and> 1 \<notin> A"
  shows   "Dirichlet_L n \<chi> holomorphic_on A"
  using assms(2)
proof
  assume "\<chi> = principal_dchar n \<and> 1 \<notin> A"
  with holomorphic_Dirichlet_L_weak[of n A "principal_dchar n"] assms(1) show ?thesis by auto
qed (insert dcharacter.holomorphic_Dirichlet_L[of n \<chi> A], auto)

lemma holomorphic_Dirichlet_L' [holomorphic_intros]:
  assumes "n > 1" "f holomorphic_on A" 
          "\<chi> \<noteq> principal_dchar n \<and> dcharacter n \<chi> \<or> \<chi> = principal_dchar n \<and> (\<forall>x\<in>A. f x \<noteq> 1)"
  shows   "(\<lambda>s. Dirichlet_L n \<chi> (f s)) holomorphic_on A"
  using holomorphic_on_compose[OF assms(2) holomorphic_Dirichlet_L[OF assms(1), of \<chi>]] assms
  by (auto simp: o_def image_iff)

lemma continuous_on_Dirichlet_L:
  assumes "n > 1" "\<chi> \<noteq> principal_dchar n \<and> dcharacter n \<chi> \<or> \<chi> = principal_dchar n \<and> 1 \<notin> A"
  shows   "continuous_on A (Dirichlet_L n \<chi>)"
  using assms by (intro holomorphic_on_imp_continuous_on holomorphic_intros)

lemma continuous_on_Dirichlet_L' [continuous_intros]:
  assumes "continuous_on A f" "n > 1" 
      and "\<chi> \<noteq> principal_dchar n \<and> dcharacter n \<chi> \<or> \<chi> = principal_dchar n \<and> (\<forall>x\<in>A. f x \<noteq> 1)"
  shows   "continuous_on A (\<lambda>x. Dirichlet_L n \<chi> (f x))"
  using continuous_on_compose2[OF continuous_on_Dirichlet_L[of n \<chi> "f ` A"] assms(1)] assms
  by (auto simp: image_iff)

corollary continuous_Dirichlet_L [continuous_intros]:
  "n > 1 \<Longrightarrow> \<chi> \<noteq> principal_dchar n \<and> dcharacter n \<chi> \<or> \<chi> = principal_dchar n \<and> s \<noteq> 1 \<Longrightarrow> 
     continuous (at s within A) (Dirichlet_L n \<chi>)"
  by (rule continuous_within_subset[of _ UNIV])
     (insert continuous_on_Dirichlet_L[of n \<chi> "(if \<chi> = principal_dchar n then -{1} else UNIV)"],
      auto simp: continuous_on_eq_continuous_at open_Compl)

corollary continuous_Dirichlet_L' [continuous_intros]:
  "n > 1 \<Longrightarrow> continuous (at s within A) f \<Longrightarrow>
     \<chi> \<noteq> principal_dchar n \<and> dcharacter n \<chi> \<or> \<chi> = principal_dchar n \<and> f s \<noteq> 1 \<Longrightarrow> 
     continuous (at s within A) (\<lambda>x. Dirichlet_L n \<chi> (f x))"
  by (rule continuous_within_compose3[OF continuous_Dirichlet_L]) auto

(*<*)
end
(*>*)


context residues_nat
begin
(*<*)
context
includes no_vec_lambda_notation dcharacter_syntax
begin
(*>*)

text \<open>
  Applying the above to the $L(\chi_0,s)$, the $L$ function of the principal character, we find 
  that it differs from the Riemann $\zeta$ function only by multiplication with a constant that 
  depends only on the modulus $n$. They therefore have the same analytic properties as the $\zeta$
  function itself.
\<close>
lemma Dirichlet_L_principal:
  fixes s :: complex
  shows   "Dirichlet_L n \<chi>\<^sub>0 s = (\<Prod>p | prime p \<and> p dvd n. (1 - 1 / p powr s)) * zeta s"
            (is "?f s = ?g s")
proof (cases "s = 1")
  case False
  show ?thesis
  proof (rule analytic_continuation_open[where ?f = ?f and ?g = ?g])
    show "{s. Re s > 1} \<subseteq> - {1}" by auto
    show "?f s = ?g s" if "s \<in> {s. Re s > 1}" for s
    proof -
      from that have s: "Re s > 1" by simp
      let ?P = "(\<Prod>p | prime p \<and> p dvd n. (1 - 1 / p powr s))"
      have "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - \<chi>\<^sub>0 p / nat_power p s) else 1)
                    \<longlonglongrightarrow> Dirichlet_L n \<chi>\<^sub>0 s"
        using s by (rule principal.Dirichlet_L_euler_product_LIMSEQ)
      also have "?this \<longleftrightarrow> (\<lambda>n. ?P * (\<Prod>p\<le>n. if prime p then inverse (1 - 1 / of_nat p powr s) else 1)) 
                             \<longlonglongrightarrow> Dirichlet_L n \<chi>\<^sub>0 s" (is "_ = filterlim ?g _ _")
      proof (intro tendsto_cong eventually_mono [OF eventually_ge_at_top, of n], goal_cases)
        case (1 m)
        let ?f = "\<lambda>p. inverse (1 - 1 / p powr s)"
        have "(\<Prod>p\<le>m. if prime p then inverse (1 - \<chi>\<^sub>0 p / nat_power p s) else 1) =
                (\<Prod>p | p \<le> m \<and> prime p \<and> coprime p n. ?f p)" (is "_ = prod _ ?A")
          by (intro prod.mono_neutral_cong_right) (auto simp: principal_dchar_def)
        also have "?A = {p. p \<le> m \<and> prime p} - {p. prime p \<and> p dvd n}"
          (is "_ = ?B - ?C") using n by (auto dest: prime_imp_coprime simp: coprime_absorb_left)
        also {
          have *: "(\<Prod>p\<in>?B. ?f p) = (\<Prod>p\<in>?B - ?C. ?f p) * (\<Prod>p\<in>?C. ?f p)"
            using 1 n by (intro prod.subset_diff) (auto dest: dvd_imp_le)
          have "(\<Prod>p\<in>?B. ?f p) * ?P = (\<Prod>p\<in>?B - ?C. ?f p) * ((\<Prod>p\<in>?C. ?f p) * ?P)"
            by (subst *) (simp add: mult_ac)
          also have "(\<Prod>p\<in>?C. ?f p) * ?P = (\<Prod>p\<in>?C. 1)"
            by (subst prod.distrib [symmetric], rule prod.cong)
               (insert s, auto simp: divide_simps powr_def exp_eq_1)
          also have "\<dots> = 1" by simp 
          finally have "(\<Prod>p\<in>?B - ?C. ?f p) = (\<Prod>p\<in>?B. ?f p) * ?P" by simp
        }
        also have "(\<Prod>p\<in>?B. ?f p) = (\<Prod>p\<le>m. if prime p then ?f p else 1)"
          by (intro prod.mono_neutral_cong_left) auto
        finally show ?case by (simp only: mult_ac)
      qed
      finally have "?g \<longlonglongrightarrow> Dirichlet_L n \<chi>\<^sub>0 s" .
      moreover have "?g \<longlonglongrightarrow> ?P * zeta s"
        by (intro tendsto_mult tendsto_const euler_product_zeta s)
      ultimately show "Dirichlet_L n \<chi>\<^sub>0 s = ?P * zeta s"
        by (rule LIMSEQ_unique)
    qed
  qed (insert \<open>s \<noteq> 1\<close> n, auto intro!: holomorphic_intros holomorphic_Dirichlet_L_weak 
         open_halfspace_Re_gt exI[of _ 2] connected_punctured_universe)
qed (simp_all add: Dirichlet_L_def zeta_1)

(*<*)
end
(*>*)
end



subsection \<open>The non-vanishing for $\mathfrak{R}(s)\geq 1$\<close>

lemma coprime_prime_exists:
  assumes "n > (0 :: nat)"
  obtains p where "prime p" "coprime p n"
proof -
  from bigger_prime[of n] obtain p where p: "prime p" "p > n" by auto
  with assms have "\<not>p dvd n" by (auto dest: dvd_imp_le)
  with p have "coprime p n" by (intro prime_imp_coprime)
  with that[of p] and p show ?thesis by auto
qed

text \<open>
  The case of the principal character is trivial, since it differs from the Riemann $\zeta(s)$
  only in a multiplicative factor that is clearly non-zero for $\mathfrak{R}(s) \geq 1$.
\<close>
theorem (in residues_nat) Dirichlet_L_Re_ge_1_nonzero_principal:
  assumes "Re s \<ge> 1" "s \<noteq> 1"
  shows   "Dirichlet_L n (principal_dchar n) s \<noteq> 0"
proof -
  have "(\<Prod>p | prime p \<and> p dvd n. 1 - 1 / p powr s) \<noteq> (0 :: complex)"
  proof (subst prod_zero_iff)
    from n show "finite {p. prime p \<and> p dvd n}" by (intro finite_prime_divisors) auto
    show "\<not>(\<exists>p\<in>{p. prime p \<and> p dvd n}. 1 - 1 / p powr s = 0)"
    proof safe
      fix p assume p: "prime p" "p dvd n" and "1 - 1 / p powr s = 0"
      hence "norm (p powr s) = 1" by simp
      also have "norm (p powr s) = real p powr Re s" by (simp add: norm_powr_real_powr)
      finally show False using p assms by (simp add: powr_def prime_gt_0_nat)
    qed
  qed
  with zeta_Re_ge_1_nonzero[OF assms] show ?thesis by (simp add: Dirichlet_L_principal)
qed

text \<open>
  The proof for non-principal character is quite involved and is typically very complicated
  and technical in most textbooks. For instance, Apostol~\cite{apostol1976analytic} proves the
  result separately for real and non-real characters, where the non-real case is relatively short
  and nice, but the real case involves a number of complicated asymptotic estimates.

  The following proof, on the other hand -- like our proof of the analogous result for the 
  Riemann $\zeta$ function -- is based on Newman's book~\cite{newman1998analytic}. Newman gives 
  a very short, concise, and high-level sketch that we aim to reproduce faithfully here.
\<close>
context dcharacter
begin
(*<*)
context
  includes no_vec_lambda_notation dcharacter_syntax
begin
(*>*)

theorem Dirichlet_L_Re_ge_1_nonzero_nonprincipal:
  assumes "\<chi> \<noteq> \<chi>\<^sub>0" and "Re u \<ge> 1"
  shows   "Dirichlet_L n \<chi> u \<noteq> 0"
proof (cases "Re u > 1")
  include dcharacter_syntax
  case False
  define a where "a = -Im u"
  from False and assms have "Re u = 1" by simp
  hence [simp]: "u = 1 - \<i> * a" by (simp add: a_def complex_eq_iff)

  show ?thesis
  proof
    assume "Dirichlet_L n \<chi> u = 0"
    hence zero: "Dirichlet_L n \<chi> (1 - \<i> * a) = 0" by simp
    define \<chi>' where [simp]: "\<chi>' = inv_character \<chi>"

    \<comment> \<open>We define the function $Z(s)$, which is the product of all the Dirichlet $L$ functions,
        and its Dirichlet series. Then, similarly to the proof of the non-vanishing of the
        Riemann $\zeta$ function for $\mathfrak{R}(s) \geq 1$, we define
        $Q(s) = Z(s) Z(s + ia) Z(s - ia)$. Our objective is to show that the Dirichlet series
        of this function $Q$ converges everywhere.\<close>
    define Z where "Z = (\<lambda>s. \<Prod>\<chi>\<in>dcharacters n. Dirichlet_L n \<chi> s)"
    define Z_fds where "Z_fds = (\<Prod>\<chi>\<in>dcharacters n. fds \<chi>)"
    define Q where "Q = (\<lambda>s. Z s ^ 2 * Z (s + \<i> * a) * Z (s - \<i> * a))"
    define Q_fds where "Q_fds = Z_fds ^ 2 * fds_shift (\<i> * a) Z_fds * fds_shift (-\<i> * a) Z_fds"  
    let ?sings = "{1, 1 + \<i> * a, 1 - \<i> * a}"
  
    \<comment> \<open>Some preliminary auxiliary facts\<close>
    define P where "P = (\<lambda>s. (\<Prod>x\<in>{p. prime p \<and> p dvd n}. 1 - 1 / of_nat x powr s :: complex))"
    have \<chi>\<^sub>0: "\<chi>\<^sub>0 \<in> dcharacters n" by (auto simp: principal.dcharacter_axioms dcharacters_def)
    have [continuous_intros]: "continuous_on A P" for A unfolding P_def
      by (intro continuous_intros) (auto simp: prime_gt_0_nat)
    from this[of UNIV] have [continuous_intros]: "isCont P s" for s
      by (auto simp: continuous_on_eq_continuous_at)
    have \<chi>: "\<chi> \<in> dcharacters n" "\<chi>' \<in> dcharacters n" using dcharacter_axioms
      by (auto simp add: dcharacters_def dcharacter.dcharacter_inv_character)
    from zero dcharacter.cnj_Dirichlet_L[of n \<chi> "1 - \<i> * a"] dcharacter_axioms
      have zero': "Dirichlet_L n \<chi>' (1 + \<i> * a) = 0" by simp
  
    have "Z = (\<lambda>s. Dirichlet_L n \<chi>\<^sub>0 s * (\<Prod>\<chi>\<in>dcharacters n - {\<chi>\<^sub>0}. Dirichlet_L n \<chi> s))"
      unfolding Z_def using \<chi>\<^sub>0 by (intro ext prod.remove) auto
    also have "\<dots> = (\<lambda>s. P s * zeta s * (\<Prod>\<chi>\<in>dcharacters n - {\<chi>\<^sub>0}. Dirichlet_L n \<chi> s))"
      by (simp add: Dirichlet_L_principal P_def)
    finally have Z_eq: "Z = (\<lambda>s. P s * zeta s * (\<Prod>\<chi>\<in>dcharacters n - {\<chi>\<^sub>0}. Dirichlet_L n \<chi> s))" .
  
    have Z_eq': "Z = (\<lambda>s. P s * zeta s * Dirichlet_L n \<chi> s *
                       (\<Prod>\<chi>\<in>dcharacters n - {\<chi>\<^sub>0} - {\<chi>}. Dirichlet_L n \<chi> s))"
      if "\<chi> \<in> dcharacters n" "\<chi> \<noteq> \<chi>\<^sub>0" for \<chi>
    proof (rule ext, goal_cases)
      case (1 s)
      from that have \<chi>: "\<chi> \<in> dcharacters n" by (simp add: dcharacters_def)
      have "Z s = P s * zeta s * 
              (\<Prod>\<chi>\<in>dcharacters n - {\<chi>\<^sub>0}. Dirichlet_L n \<chi> s)" by (simp add: Z_eq)
      also have "(\<Prod>\<chi>\<in>dcharacters n - {\<chi>\<^sub>0}. Dirichlet_L n \<chi> s) = Dirichlet_L n \<chi> s * 
                   (\<Prod>\<chi>\<in>dcharacters n - {\<chi>\<^sub>0} - {\<chi>}. Dirichlet_L n \<chi>  s)"
        using assms \<chi> that by (intro prod.remove) auto
      finally show ?case by (simp add: mult_ac)
    qed
  
    \<comment> \<open>We again show that @{term Q} is locally bounded everywhere by showing that every
        singularity is cancelled by some zero. Since now, @{term a} can be zero, we do a
        case distinction here to make things a bit easier.\<close>
    have Q_bigo_1: "Q \<in> O[at s](\<lambda>_. 1)" for s
    proof (cases "a = 0")
      case True
      have "(\<lambda>s. Dirichlet_L n \<chi> s - Dirichlet_L n \<chi> 1) \<in> O[at 1](\<lambda>s. s - 1)" using \<chi> assms n
         by (intro taylor_bigo_linear holomorphic_on_imp_differentiable_at[of _ UNIV]
                             holomorphic_intros) (auto simp: dcharacters_def)
      hence *: "Dirichlet_L n \<chi> \<in> O[at 1](\<lambda>s. s - 1)" using zero True by simp
      have "Z = (\<lambda>s. P s * zeta s * Dirichlet_L n \<chi> s *
                  (\<Prod>\<chi>\<in>dcharacters n - {\<chi>\<^sub>0} - {\<chi>}. Dirichlet_L n \<chi> s))"
        using \<chi> assms by (intro Z_eq') auto
      also have "\<dots> \<in> O[at 1](\<lambda>s. 1 * (1 / (s - 1)) * (s - 1) * 1)" using n \<chi>
        by (intro landau_o.big.mult continuous_imp_bigo_1 zeta_bigo_at_1 continuous_intros *)
           (auto simp: dcharacters_def)
      also have "(\<lambda>s::complex. 1 * (1 / (s - 1)) * (s - 1) * 1) \<in> \<Theta>[at 1](\<lambda>_. 1)"
        by (intro bigthetaI_cong) (auto simp: eventually_at_filter)
      finally have Z_at_1: "Z \<in> O[at 1](\<lambda>_. 1)" .
  
      have "Z \<in> O[at s](\<lambda>_. 1)"
      proof (cases "s = 1")
        case False
        thus ?thesis unfolding Z_def using n \<chi>
          by (intro continuous_imp_bigo_1 continuous_intros) (auto simp: dcharacters_def)
      qed (insert Z_at_1, auto)
  
      from \<open>a = 0\<close> have "Q = (\<lambda>s. Z s * Z s * Z s * Z s)"
        by (simp add: Q_def power2_eq_square)
      also have "\<dots> \<in> O[at s](\<lambda>_. 1 * 1 * 1 * 1)"
        by (intro landau_o.big.mult) fact+
      finally show ?thesis by simp
    next
      case False
      have bigo1: "(\<lambda>s. Z s * Z (s - \<i> * a)) \<in> O[at 1](\<lambda>_. 1)"
        if "Dirichlet_L n \<chi> (1 - \<i> * a) = 0" "a \<noteq> 0" "\<chi> \<in> dcharacters n" "\<chi> \<noteq> \<chi>\<^sub>0" 
        for a :: real and \<chi>
      proof -
        have "(\<lambda>s. Dirichlet_L n \<chi> (s - \<i> * a) - Dirichlet_L n \<chi> (1 - \<i> * a)) \<in> O[at 1](\<lambda>s. s - 1)"
          using assms n that
          by (intro taylor_bigo_linear holomorphic_on_imp_differentiable_at[of _ UNIV]
                    holomorphic_intros) (auto simp: dcharacters_def)
        hence *: "(\<lambda>s. Dirichlet_L n \<chi> (s - \<i> * a)) \<in> O[at 1](\<lambda>s. s - 1)" using that by simp
  
        have "(\<lambda>s. Z (s - \<i>*a)) = (\<lambda>s. P (s - \<i>*a) * zeta (s - \<i>*a) * Dirichlet_L n \<chi> (s - \<i>*a)
                     * (\<Prod>\<chi>\<in>dcharacters n - {\<chi>\<^sub>0} - {\<chi>}. Dirichlet_L n \<chi>  (s - \<i>*a)))"
          using that by (subst Z_eq'[of \<chi>]) auto
        also have "\<dots> \<in> O[at 1](\<lambda>s. 1 * 1 * (s - 1) * 1)" unfolding P_def using that n
          by (intro landau_o.big.mult continuous_imp_bigo_1 continuous_intros *)
             (auto simp: prime_gt_0_nat dcharacters_def)
        finally have "(\<lambda>s. Z (s - \<i> * a)) \<in> O[at 1](\<lambda>s. s - 1)" by simp
        moreover have "Z \<in> O[at 1](\<lambda>s. 1 * (1 / (s - 1)) * 1)" unfolding Z_eq using n that
          by (intro landau_o.big.mult zeta_bigo_at_1 continuous_imp_bigo_1 continuous_intros)
             (auto simp: dcharacters_def)
        hence "Z \<in> O[at 1](\<lambda>s. 1 / (s - 1))" by simp
        ultimately have "(\<lambda>s. Z s * Z (s - \<i> * a)) \<in> O[at 1](\<lambda>s. 1 / (s - 1) * (s - 1))"
          by (intro landau_o.big.mult)
        also have "(\<lambda>s. 1 / (s - 1) * (s - 1)) \<in> \<Theta>[at 1](\<lambda>_. 1)"
          by (intro bigthetaI_cong) (auto simp add: eventually_at_filter)
        finally show ?thesis .
      qed
  
      have bigo1': "(\<lambda>s. Z s * Z (s + \<i> * a)) \<in> O[at 1](\<lambda>_. 1)"
        if "Dirichlet_L n \<chi> (1 - \<i> * a) = 0" "a \<noteq> 0" "\<chi> \<in> dcharacters n" "\<chi> \<noteq> \<chi>\<^sub>0" 
        for a :: real and \<chi>
      proof -
        from that interpret dcharacter n G \<chi> by (simp_all add: dcharacters_def G_def)
        from bigo1[of "inv_character \<chi>" "-a"] that cnj_Dirichlet_L[of "1 - \<i> * a"] show ?thesis
          by (simp add: dcharacters_def dcharacter_inv_character)
      qed
  
      have bigo2: "(\<lambda>s. Z s * Z (s - \<i> * a)) \<in> O[at (1 + \<i> * a)](\<lambda>_. 1)"
        if "Dirichlet_L n \<chi> (1 - \<i> * a) = 0" "a \<noteq> 0" "\<chi> \<in> dcharacters n" "\<chi> \<noteq> \<chi>\<^sub>0" 
        for a :: real and \<chi>
      proof -
        have "(\<lambda>s. Z s * Z (s - \<i> * a)) \<in> O[filtermap (\<lambda>s. s + \<i> * a) (at 1)](\<lambda>_. 1)"
          using bigo1'[of \<chi> a] that by (simp add: mult.commute landau_o.big.in_filtermap_iff)
        also have "filtermap (\<lambda>s. s + \<i> * a) (at 1) = at (1 + \<i> * a)"
          using filtermap_at_shift[of "-\<i> * a" 1] by simp
        finally show ?thesis .
      qed
  
      have bigo2': "(\<lambda>s. Z s * Z (s + \<i> * a)) \<in> O[at (1 - \<i> * a)](\<lambda>_. 1)"
        if "Dirichlet_L n \<chi> (1 - \<i> * a) = 0" "a \<noteq> 0" "\<chi> \<in> dcharacters n" "\<chi> \<noteq> \<chi>\<^sub>0" 
        for a :: real and \<chi>
      proof -
        from that interpret dcharacter n G \<chi> by (simp_all add: dcharacters_def G_def)
        from bigo2[of "inv_character \<chi>" "-a"] that cnj_Dirichlet_L[of "1 - \<i> * a"] show ?thesis
          by (simp add: dcharacters_def dcharacter_inv_character)
      qed
  
      have Q_eq: "Q = (\<lambda>s. (Z s * Z (s + \<i> * a)) * (Z s * Z (s - \<i> * a)))"
        by (simp add: Q_def power2_eq_square mult_ac)
  
      consider "s = 1" | "s = 1 + \<i> * a" | "s = 1 - \<i> * a" | "s \<notin> ?sings" by blast
      thus ?thesis
      proof cases
        case 1
        have "Q \<in> O[at 1](\<lambda>_. 1 * 1)"
          unfolding Q_eq using assms zero zero' False \<chi>
          by (intro landau_o.big.mult bigo1[of \<chi> a] bigo1'[of \<chi> a]; simp)+
        with 1 show ?thesis by simp
      next
        case 2
        have "Q \<in> O[at (1 + \<i> * a)](\<lambda>_. 1 * 1)" unfolding Q_eq
          using assms zero zero' False \<chi> n
          by (intro landau_o.big.mult bigo2[of \<chi> a] continuous_imp_bigo_1)
             (auto simp: Z_def dcharacters_def intro!: continuous_intros)
        with 2 show ?thesis by simp
      next
        case 3
        have "Q \<in> O[at (1 - \<i> * a)](\<lambda>_. 1 * 1)" unfolding Q_eq
          using assms zero zero' False \<chi> n
          by (intro landau_o.big.mult bigo2'[of \<chi> a] continuous_imp_bigo_1)
             (auto simp: Z_def dcharacters_def intro!: continuous_intros)
        with 3 show ?thesis by simp
      next
        case 4
        thus ?thesis unfolding Q_def Z_def using n 
          by (intro continuous_imp_bigo_1 continuous_intros)
             (auto simp: dcharacters_def complex_eq_iff)
      qed
    qed
  
    \<comment> \<open>Again, we can remove the singularities from @{term Q} and extend it to an entire function.\<close>
    have "\<exists>Q'. Q' holomorphic_on UNIV \<and> (\<forall>z\<in>UNIV - ?sings. Q' z = Q z)"
      using n by (intro removable_singularities Q_bigo_1)
                 (auto simp: Q_def Z_def dcharacters_def complex_eq_iff intro!: holomorphic_intros)
    then obtain Q' where Q': "Q' holomorphic_on UNIV" "\<And>z. z \<notin> ?sings \<Longrightarrow> Q' z = Q z" by blast
  
    \<comment> \<open>@{term Q'} constitutes an analytic continuation of the Dirichlet series of @{term Q}.\<close>
    have eval_Q_fds: "eval_fds Q_fds s = Q' s" if "Re s > 1" for s
    proof -
      have [simp]: "dcharacter n \<chi>" if "\<chi> \<in> dcharacters n" for \<chi>
        using that by (simp add: dcharacters_def)
      from that have "abs_conv_abscissa (fds \<chi>) < ereal (Re s)" if "\<chi> \<in> dcharacters n" for \<chi>
        using that by (intro le_less_trans[OF dcharacter.abs_conv_abscissa_weak[of n \<chi>]]) auto
      hence "eval_fds Q_fds s = Q s" using that
        by (simp add: Q_fds_def Q_def eval_fds_mult eval_fds_power fds_abs_converges_mult 
              eval_fds_prod fds_abs_converges_prod dcharacter.Dirichlet_L_conv_eval_fds_weak
              fds_abs_converges_power eval_fds_zeta Z_fds_def Z_def fds_abs_converges)
      also from that have "\<dots> = Q' s" by (subst Q') auto
      finally show ?thesis .
    qed
  
    \<comment> \<open>Since the characters are completely multiplicative, the series for this logarithm can
        be rewritten like this:\<close>
    define I where "I = (\<lambda>k. if [k = 1] (mod n) then totient n else 0 :: real)"
    have ln_Q_fds_eq:
      "fds_ln 0 Q_fds = fds (\<lambda>k. of_real (2 * I k * mangoldt k / ln k * (1 + cos (a * ln k))))"
    proof -
      have nz: "\<chi> (Suc 0) = 1" if "\<chi> \<in> dcharacters n" for \<chi>
        using dcharacter.Suc_0[of n \<chi>] that by (simp add: dcharacters_def)
      note simps = fds_ln_mult[where l' = 0 and l'' = 0] fds_ln_power[where l' = 0]
                   fds_ln_prod[where l' = "\<lambda>_. 0"]
      have "fds_ln 0 Q_fds = (\<Sum>\<chi>\<in>dcharacters n. 2 * fds_ln 0 (fds \<chi>) + 
              fds_shift (\<i> * a) (fds_ln 0 (fds \<chi>)) + fds_shift (-\<i> * a) (fds_ln 0 (fds \<chi>)))"
        by (auto simp: Q_fds_def Z_fds_def simps nz sum.distrib sum_distrib_left)
      also have "\<dots> = (\<Sum>\<chi>\<in>dcharacters n. 
                         fds (\<lambda>k. \<chi> k * of_real (2 * mangoldt k / ln k * (1 + cos (a * ln k)))))"
        (is "(\<Sum>\<chi>\<in>_. ?l \<chi>) = _")
      proof (intro sum.cong refl, goal_cases)
        case (1 \<chi>)
        then interpret dcharacter n G \<chi> by (simp_all add: dcharacters_def G_def)
        have mult: "completely_multiplicative_function (fds_nth (fds \<chi>))"
          by (simp add: fds_nth_fds' mult.completely_multiplicative_function_axioms)
        have *: "fds_ln 0 (fds \<chi>) = fds (\<lambda>n. \<chi> n * mangoldt n /\<^sub>R ln (real n))"
          by (simp add: fds_ln_completely_multiplicative[OF mult] fds_nth_fds' fds_eq_iff)
        have "?l \<chi> = fds (\<lambda>k. \<chi> k * mangoldt k /\<^sub>R ln k * (2 + k powr (\<i> * a) + k powr (-\<i> * a)))"
          by (unfold *, rule fds_eqI) (simp add: algebra_simps scaleR_conv_of_real numeral_fds)
        also have "\<dots> = fds (\<lambda>k. \<chi> k * 2 * mangoldt k /\<^sub>R ln k * (1 + cos (of_real(a * ln k))))"
          unfolding cos_exp_eq by (intro fds_eqI) (simp add: powr_def algebra_simps)
        also have "\<dots> = fds (\<lambda>k. \<chi> k * of_real (2 * mangoldt k / ln k * (1 + cos (a * ln k))))"
          unfolding cos_of_real by (simp add: field_simps scaleR_conv_of_real)
        finally show ?case .
      qed
      also have "\<dots> = fds (\<lambda>k. (\<Sum>\<chi>\<in>dcharacters n. \<chi> k) * of_real (2 * mangoldt k / ln k * 
                                 (1 + cos (a * ln k))))"
        by (simp add: sum_distrib_right sum_divide_distrib scaleR_conv_of_real sum_distrib_left)
      also have "\<dots> = fds (\<lambda>k. of_real (2 * I k * mangoldt k / ln k * (1 + cos (a * ln k))))"
        by (intro fds_eqI, subst sum_dcharacters) (simp_all add: I_def algebra_simps)
      finally show ?thesis .
    qed
    \<comment> \<open>The coefficients of that logarithm series are clearly nonnegative:\<close>
    have "nonneg_dirichlet_series (fds_ln 0 Q_fds)"
    proof
      show "fds_nth (fds_ln 0 Q_fds) k \<in> \<real>\<^sub>\<ge>\<^sub>0" for k
      proof (cases "k < 2")
        case False
        have cos: "1 + cos x \<ge> 0" for x :: real 
          using cos_ge_minus_one[of x] by linarith
        have "fds_nth (fds_ln 0 Q_fds) k =
                of_real (2 * I k * mangoldt k / ln k * (1 + cos (a * ln k)))"
          by (auto simp: fds_nth_fds' ln_Q_fds_eq)
        also have "\<dots> \<in> \<real>\<^sub>\<ge>\<^sub>0" using False unfolding I_def
          by (subst nonneg_Reals_of_real_iff) 
             (intro mult_nonneg_nonneg divide_nonneg_pos cos mangoldt_nonneg, auto)
        finally show ?thesis .
      qed (cases k; auto simp: ln_Q_fds_eq)
    qed
    \<comment> \<open>Therefore @{term Q_fds} also has non-negative coefficients.\<close>
    hence nonneg: "nonneg_dirichlet_series Q_fds"
    proof (rule nonneg_dirichlet_series_lnD)
      have "(\<Prod>x\<in>dcharacters n. x (Suc 0)) = 1"
        by (intro prod.neutral) (auto simp: dcharacters_def dcharacter.Suc_0)
      thus "exp 0 = fds_nth Q_fds (Suc 0)" by (simp add: Q_fds_def Z_fds_def)
    qed

    \<comment> \<open>And by Pringsheim--Landau, we get that the Dirichlet series of @{term Q} converges
        everywhere.\<close>
    have "abs_conv_abscissa Q_fds \<le> 1" unfolding Q_fds_def Z_fds_def fds_shift_prod
      by (intro abs_conv_abscissa_power_leI abs_conv_abscissa_mult_leI abs_conv_abscissa_prod_le)
         (auto simp: dcharacters_def dcharacter.abs_conv_abscissa_weak)
    with nonneg and eval_Q_fds and \<open>Q' holomorphic_on UNIV\<close>
      have abscissa: "abs_conv_abscissa Q_fds = -\<infinity>"
        by (intro entire_continuation_imp_abs_conv_abscissa_MInfty[where g = Q' and c = 1])
           (auto simp: one_ereal_def)
  
    \<comment> \<open>Again, similarly to the proof for $\zeta$, we select a subseries of @{term Q}. This time
        we cannot simply pick powers of 2, since 2 might not be coprime to @{term n}, in which 
        case the subseries would simply be 1 everywhere, which is not helpful. However, it is
        clear that there \emph{is} always some prime $p$ that is coprime to @{term n}, so we
        just use the subseries @{term Q} that corresponds to powers of $p$.\<close>
    from n obtain p where p: "prime p" "coprime p n"
      using coprime_prime_exists[of n] by auto
    define R_fds where "R_fds = fds_primepow_subseries p Q_fds"
    have "conv_abscissa R_fds \<le> abs_conv_abscissa R_fds" by (rule conv_le_abs_conv_abscissa)
    also have "abs_conv_abscissa R_fds \<le> abs_conv_abscissa Q_fds"
      unfolding R_fds_def by (rule abs_conv_abscissa_restrict)
    also have "\<dots> = -\<infinity>" by (simp add: abscissa)
    finally have abscissa': "conv_abscissa R_fds = -\<infinity>" by simp
  
    \<comment> \<open>The following function $g(a,s)$ is the denominator in the Euler product expansion of 
        the subseries of $Z(s + ia)$. It is clear that it is entire and non-zero for 
        $\mathfrak{R}(s) > 0$ and all real $a$.\<close>
    define g :: "real \<Rightarrow> complex \<Rightarrow> complex"
      where "g = (\<lambda>a s. (\<Prod>\<chi>\<in>dcharacters n. (1 - \<chi> p * p powr (-s + \<i> * of_real a))))"
    have g_nz: "g a s \<noteq> 0" if "Re s > 0" for s a unfolding g_def
    proof (subst prod_zero_iff[OF finite_dcharacters], safe)
      fix \<chi> assume "\<chi> \<in> dcharacters n" and *: "1 - \<chi> p * p powr (-s + \<i>*a) = 0"
      then interpret dcharacter n G \<chi> by (simp_all add: dcharacters_def G_def)
      from p have "real p > real 1" by (subst of_nat_less_iff) (auto simp: prime_gt_Suc_0_nat)
      hence "real p powr - Re s < real p powr 0"
        using p that by (intro powr_less_mono) (auto simp: )
      hence "0 < norm (1 :: complex) - norm (\<chi> p * p powr (-s + \<i>*a))"
        using p by (simp add: norm_mult norm norm_powr_real_powr)
      also have "\<dots> \<le> norm (1 - \<chi> p * p powr (-s + \<i>*a))"
        by (rule norm_triangle_ineq2)
      finally show False by (subst (asm) *) simp_all
    qed
    have [holomorphic_intros]: "g a holomorphic_on A" for a A unfolding g_def
      using p by (intro holomorphic_intros)

    \<comment> \<open>By taking Euler product expansions of every factor, we get
          \[R(s) = \frac{1}{g(0,s)^2 g(a,s) g(-a,s)} = 
              (1 - 2^{-s})^{-2} (1 - 2^{-s+ia})^{-1} (1 - 2^{-s-ia})^{-1}\]
        for every $s$ with $\mathfrak{R}(s) > 1$, and by analytic continuation also for
        $\mathfrak{R}(s) > 0$.\<close>

    have eval_R: "eval_fds R_fds s = 1 / (g 0 s ^ 2 * g a s * g (-a) s)"
      (is "_ = ?f s") if "Re s > 0" for s :: complex
    proof -
      show ?thesis
      proof (rule analytic_continuation_open[where f = "eval_fds R_fds"])
        show "?f holomorphic_on {s. Re s > 0}" using p g_nz[of 0] g_nz[of a] g_nz[of "-a"]
          by (intro holomorphic_intros) (auto simp: g_nz) 
      next
        fix z assume z: "z \<in> {s. Re s > 1}"
        have [simp]: "completely_multiplicative_function \<chi>" "fds_nth (fds \<chi>) = \<chi>"
          if "\<chi> \<in> dcharacters n" for \<chi>
        proof -
          from that interpret dcharacter n G \<chi> by (simp_all add: G_def dcharacters_def)
          show "completely_multiplicative_function \<chi>" "fds_nth (fds \<chi>) = \<chi>"
            by (simp_all add: fds_nth_fds' mult.completely_multiplicative_function_axioms)
        qed
        have [simp]: "dcharacter n \<chi>" if "\<chi> \<in> dcharacters n" for \<chi>
          using that by (simp add: dcharacters_def)
        from that have "abs_conv_abscissa (fds \<chi>) < ereal (Re z)" if "\<chi> \<in> dcharacters n" for \<chi>
          using that z by (intro le_less_trans[OF dcharacter.abs_conv_abscissa_weak[of n \<chi>]]) auto
        thus "eval_fds R_fds z = ?f z" using z p
          by (simp add: R_fds_def Q_fds_def Z_fds_def eval_fds_mult eval_fds_prod eval_fds_power 
               fds_abs_converges_mult fds_abs_converges_power fds_abs_converges_prod g_def mult_ac
               fds_primepow_subseries_euler_product_cm powr_minus powr_diff powr_add  prod_dividef
               fds_abs_summable_zeta g_nz fds_abs_converges power_one_over divide_inverse [symmetric])
      qed (insert that abscissa', auto intro!: exI[of _ 2] convex_connected open_halfspace_Re_gt
                                               convex_halfspace_Re_gt holomorphic_intros)
    qed
  
    \<comment> \<open>We again have our contradiction: $R(s)$ is entire, but the right-hand side has a pole at 0
        since $g(0,0) = 0$.\<close>
    show False
    proof (rule not_tendsto_and_filterlim_at_infinity)
      have g_limit: "(g a \<longlongrightarrow> g a 0) (at 0 within {s. Re s > 0})" for a
      proof -
        have "continuous_on UNIV (g a)" by (intro holomorphic_on_imp_continuous_on holomorphic_intros)
        hence "isCont (g a) 0" by (rule continuous_on_interior) auto
        hence "continuous (at 0 within {s. Re s > 0}) (g a)" by (rule continuous_within_subset) auto
        thus ?thesis by (auto simp: continuous_within)
      qed
      have "((\<lambda>s. g 0 s ^ 2 * g a s * g (-a) s) \<longlongrightarrow> g 0 0 ^ 2 * g a 0 * g (-a) 0) 
              (at 0 within {s. Re s > 0})" by (intro tendsto_intros g_limit)
      also have "g 0 0 = 0" unfolding g_def
      proof (rule prod_zero)
        from p and \<chi>\<^sub>0 show "\<exists>\<chi>\<in>dcharacters n. 1 - \<chi> p * of_nat p powr (- 0 + \<i> * of_real 0) = 0"
          by (intro bexI[of _ \<chi>\<^sub>0]) (auto simp: principal_dchar_def)
      qed auto
      moreover have "eventually (\<lambda>s. s \<in> {s. Re s > 0}) (at 0 within {s. Re s > 0})"
        by (auto simp: eventually_at_filter)
      hence "eventually (\<lambda>s. g 0 s ^ 2 * g a s * g (-a) s \<noteq> 0) (at 0 within {s. Re s > 0})"
        by eventually_elim (auto simp: g_nz)
      ultimately have "filterlim (\<lambda>s. g 0 s ^ 2 * g a s * g (-a) s) (at 0) 
                         (at 0 within {s. Re s > 0})" by (simp add: filterlim_at)
      hence "filterlim ?f at_infinity (at 0 within {s. Re s > 0})" (is ?lim)
        by (intro filterlim_divide_at_infinity[OF tendsto_const]
                     tendsto_mult_filterlim_at_infinity) auto
      also have ev: "eventually (\<lambda>s. Re s > 0) (at 0 within {s. Re s > 0})"
        by (auto simp: eventually_at intro!: exI[of _ 1])
      have "?lim \<longleftrightarrow> filterlim (eval_fds R_fds) at_infinity (at 0 within {s. Re s > 0})"
        by (intro filterlim_cong refl eventually_mono[OF ev]) (auto simp: eval_R)
      finally show \<dots> .
    next
      have "continuous (at 0 within {s. Re s > 0}) (eval_fds R_fds)"
        by (intro continuous_intros) (auto simp: abscissa')
      thus "((eval_fds R_fds \<longlongrightarrow> eval_fds R_fds 0)) (at 0 within {s. Re s > 0})"
        by (auto simp: continuous_within)
    next
      have "0 \<in> {s. Re s \<ge> 0}" by simp
      also have "{s. Re s \<ge> 0} = closure {s. Re s > 0}"
        using closure_halfspace_gt[of "1::complex" 0] by (simp add: inner_commute)
      finally have "0 \<in> \<dots>" .
      thus "at 0 within {s. Re s > 0} \<noteq> bot"
        by (subst at_within_eq_bot_iff) auto
    qed
  qed
qed (fact Dirichlet_L_Re_gt_1_nonzero)


subsection \<open>Asymptotic bounds on partial sums of Dirichlet $L$ functions\<close>

text \<open>
  The following are some bounds on partial sums of the $L$-function of a character that are
  useful for asymptotic reasoning, particularly for Dirichlet's Theorem.
\<close>
lemma sum_upto_dcharacter_le:
  assumes "\<chi> \<noteq> \<chi>\<^sub>0"
  shows   "norm (sum_upto \<chi> x) \<le> totient n"
proof -
  have "sum_upto \<chi> x = (\<Sum>k\<le>nat \<lfloor>x\<rfloor>. \<chi> k)" unfolding sum_upto_altdef
    by (intro sum.mono_neutral_left) auto
  also have "norm \<dots> \<le> totient n"
    by (rule sum_dcharacter_atMost_le) fact
  finally show ?thesis .
qed

lemma Dirichlet_L_minus_partial_sum_bound:
  fixes s :: complex and x :: real
  assumes "\<chi> \<noteq> \<chi>\<^sub>0" and "Re s > 0" and "x > 0"
  defines "\<sigma> \<equiv> Re s"
  shows   "norm (sum_upto (\<lambda>n. \<chi> n * n powr -s) x - Dirichlet_L n \<chi> s) \<le> 
             real (totient n) * (2 + cmod s / \<sigma>) / x powr \<sigma>"
proof (rule Lim_norm_ubound)
  from assms have "summable (\<lambda>n. \<chi> n * of_nat n powr -s)"
    by (intro summable_Dirichlet_L')
  with assms have "(\<lambda>n. \<chi> n * of_nat n powr -s) sums Dirichlet_L n \<chi> s"
    using Dirichlet_L_conv_eval_fds[OF assms(1,2)]
    by (simp add: sums_iff eval_fds_def powr_minus divide_simps fds_nth_fds')
  hence "(\<lambda>m. \<Sum>k\<le>m. \<chi> k * of_nat k powr -s) \<longlonglongrightarrow> Dirichlet_L n \<chi> s"
    by (simp add: sums_def' atLeast0AtMost)
  thus "(\<lambda>m. sum_upto (\<lambda>k. \<chi> k * of_nat k powr -s) x - (\<Sum>k\<le>m. \<chi> k * of_nat k powr -s))
           \<longlonglongrightarrow> sum_upto (\<lambda>k. \<chi> k * of_nat k powr -s) x - Dirichlet_L n \<chi> s"
    by (intro tendsto_intros)
next
  define M where "M = sum_upto \<chi>"
  have le: "norm (\<Sum>n\<in>real-`{x<..y}. \<chi> n * of_nat n powr - s)
              \<le> real (totient n) * (2 + cmod s / \<sigma>) / x powr \<sigma>" if xy: "0 < x" "x < y" for x y
  proof -
    from xy have  I: "((\<lambda>t. M t * (-s * t powr (-s-1))) has_integral
                        M y * of_real y powr - s - M x * of_real x powr - s -
                       (\<Sum>n\<in>real-`{x<..y}. \<chi> n * of_real (real n) powr -s)) {x..y}" unfolding M_def
      by (intro partial_summation_strong [of "{}"])
         (auto intro!: has_vector_derivative_real_field derivative_eq_intros continuous_intros)
    hence "(\<Sum>n\<in>real-`{x<..y}. \<chi> n * real n powr -s) = 
             M y * of_real y powr - s - M x * of_real x powr - s -
             integral {x..y} (\<lambda>t. M t * (-s * t powr (-s-1)))"
      by (simp add: has_integral_iff)
    also have "norm \<dots> \<le> norm (M y * of_real y powr -s) + norm (M x * of_real x powr -s) +
                 norm (integral {x..y} (\<lambda>t. M t * (-s * t powr (-s-1))))"
      by (intro order.trans[OF norm_triangle_ineq4] add_mono order.refl)
    also have "norm (M y * of_real y powr -s) \<le> totient n * y powr -\<sigma>"
      using xy assms unfolding norm_mult M_def \<sigma>_def
      by (intro mult_mono sum_upto_dcharacter_le) (auto simp: norm_powr_real_powr)
    also have "\<dots> \<le> totient n * x powr -\<sigma>"
      using assms xy by (intro mult_left_mono powr_mono2') (auto simp: \<sigma>_def)
    also have "norm (M x * of_real x powr -s) \<le> totient n * x powr -\<sigma>"
      using xy assms unfolding norm_mult M_def \<sigma>_def
      by (intro mult_mono sum_upto_dcharacter_le) (auto simp: norm_powr_real_powr)
    also have "norm (integral {x..y} (\<lambda>t. M t * (- s * of_real t powr (-s-1)))) \<le>
                 integral {x..y} (\<lambda>t. real (totient n) * norm s * t powr (-\<sigma>-1))"
    proof (rule integral_norm_bound_integral integrable_on_cmult_left)
      show "(\<lambda>t. real (totient n) * norm s * t powr (- \<sigma> - 1)) integrable_on {x..y}"
        using xy by (intro integrable_continuous_real continuous_intros) auto
    next
      fix t assume t: "t \<in> {x..y}"
      have "norm (M t * (-s * of_real t powr (-s-1))) \<le> 
              real (totient n) * (norm s * t powr (-\<sigma>-1))" 
        unfolding norm_mult M_def \<sigma>_def using xy t assms 
        by (intro mult_mono sum_upto_dcharacter_le) (auto simp: norm_mult norm_powr_real_powr)
      thus "norm (M t * (-s * of_real t powr (-s-1))) \<le> real (totient n) * norm s * t powr (-\<sigma>-1)"
        by (simp add: algebra_simps)
    qed (insert I, auto simp: has_integral_iff)
    also have "\<dots> = real (totient n) * norm s * integral {x..y} (\<lambda>t. t powr (-\<sigma>-1))"
      by simp
    also have "((\<lambda>t. t powr (-\<sigma>-1)) has_integral (y powr -\<sigma> / (-\<sigma>) - x powr -\<sigma> / (-\<sigma>))) {x..y}"
      using xy assms 
      by (intro fundamental_theorem_of_calculus) 
         (auto intro!: derivative_eq_intros 
               simp: has_field_derivative_iff_has_vector_derivative [symmetric] \<sigma>_def)
    hence "integral {x..y} (\<lambda>t. t powr (-\<sigma>-1)) = y powr -\<sigma> / (-\<sigma>) - x powr -\<sigma> / (-\<sigma>)"
      by (simp add: has_integral_iff)
    also from assms have "\<dots> \<le> x powr -\<sigma> / \<sigma>" by (simp add: \<sigma>_def)
    also have "real (totient n) * x powr -\<sigma> + real (totient n) * x powr -\<sigma> +
                 real (totient n) * norm s * (x powr -\<sigma> / \<sigma>) =
               real (totient n) * (2 + norm s / \<sigma>) / x powr \<sigma>"
      using xy by (simp add: field_simps powr_minus)
    finally show ?thesis by (simp add: mult_left_mono)
  qed

  show "eventually (\<lambda>m. norm (sum_upto (\<lambda>k. \<chi> k * of_nat k powr - s) x - 
                          (\<Sum>k\<le>m. \<chi> k * of_nat k powr - s))
          \<le> real (totient n) * (2 + cmod s / \<sigma>) / x powr \<sigma>) at_top"
    using eventually_gt_at_top[of "nat \<lfloor>x\<rfloor>"]
  proof eventually_elim
    case (elim m)
    have "(\<Sum>k\<le>m. \<chi> k * of_nat k powr - s) - sum_upto (\<lambda>k. \<chi> k * of_nat k powr - s) x =
            (\<Sum>k\<in>{..m} - {k. 0 < k \<and> real k \<le> x}. \<chi> k * of_nat k powr -s)" unfolding sum_upto_def
      using elim \<open>x > 0\<close> by (intro Groups_Big.sum_diff [symmetric])
                            (auto simp: nat_less_iff floor_less_iff)
    also have "\<dots> = (\<Sum>k\<in>{..m} - {k. real k \<le> x}. \<chi> k * of_nat k powr -s)"
      by (intro sum.mono_neutral_right) auto
    also have "{..m} - {k. real k \<le> x} = real -` {x<..real m}"
      using elim \<open>x > 0\<close> by (auto simp: nat_less_iff floor_less_iff not_less)
    also have "norm (\<Sum>k\<in>\<dots>. \<chi> k * of_nat k powr -s) \<le> 
                 real (totient n) * (2 + cmod s / \<sigma>) / x powr \<sigma>"
      using elim \<open>x > 0\<close> by (intro le) (auto simp: nat_less_iff floor_less_iff)
    finally show ?case by (simp add: norm_minus_commute)
  qed
qed auto

lemma partial_Dirichlet_L_sum_bigo:
  fixes s :: complex and x :: real
  assumes "\<chi> \<noteq> \<chi>\<^sub>0" "Re s > 0"
  shows   "(\<lambda>x. sum_upto (\<lambda>n. \<chi> n * n powr -s) x - Dirichlet_L n \<chi> s) \<in> O(\<lambda>x. x powr -s)"
proof (rule bigoI)
  show "eventually (\<lambda>x. norm (sum_upto (\<lambda>n. \<chi> n * of_nat n powr -s) x - Dirichlet_L n \<chi> s)
          \<le> real (totient n) * (2 + norm s / Re s) * norm (of_real x powr - s)) at_top"
    using eventually_gt_at_top[of 0]
  proof eventually_elim
    case (elim x)
    have "norm (sum_upto (\<lambda>n. \<chi> n * of_nat n powr -s) x - Dirichlet_L n \<chi> s)
            \<le> real (totient n) * (2 + norm s / Re s) / x powr Re s"
      using elim assms by (intro Dirichlet_L_minus_partial_sum_bound) auto
    thus ?case using elim assms 
      by (simp add: norm_powr_real_powr powr_minus divide_simps norm_divide
               del: div_mult_self1 div_mult_self2 div_mult_self3 div_mult_self4)
  qed
qed

(*<*)
end
(*>*)
end


subsection \<open>Evaluation of $L(\chi, 0)$\<close>

context residues_nat
begin
(*<*)
context
  includes no_vec_lambda_notation dcharacter_syntax
begin
(*>*)

lemma Dirichlet_L_0_principal [simp]: "Dirichlet_L n \<chi>\<^sub>0 0 = 0"
proof -
  have "Dirichlet_L n \<chi>\<^sub>0 0 = -1/2 * (\<Prod>p | prime p \<and> p dvd n. 1 - 1 / p powr 0)"
    by (simp add: Dirichlet_L_principal prime_gt_0_nat)
  also have "(\<Prod>p | prime p \<and> p dvd n. 1 - 1 / p powr 0) = (\<Prod>p | prime p \<and> p dvd n. 0 :: complex)"
    by (intro prod.cong) (auto simp: prime_gt_0_nat)
  also have "(\<Prod>p | prime p \<and> p dvd n. 0 :: complex) = 0"
    using prime_divisor_exists[of n] n by (auto simp: card_gt_0_iff)
  finally show ?thesis by simp
qed

end
(*<*)
end
(*>*)

context dcharacter
begin
(*<*)
context
  includes no_vec_lambda_notation dcharacter_syntax
begin
(*>*)

lemma Dirichlet_L_0_nonprincipal:
  assumes nonprincipal: "\<chi> \<noteq> \<chi>\<^sub>0"
  shows   "Dirichlet_L n \<chi> 0 = -(\<Sum>k=1..<n. of_nat k * \<chi> k) / of_nat n"
proof -
  have "Dirichlet_L n \<chi> 0 = (\<Sum>k=1..n. \<chi> k * (1 / 2 - of_nat k / of_nat n))"
    using assms n by (simp add: Dirichlet_L_conv_hurwitz_zeta_nonprincipal)
  also have "\<dots> = -1/n * (\<Sum>k=1..n. of_nat k * \<chi> k)"
    using assms by (simp add: algebra_simps sum_subtractf sum_dcharacter_block'
                              sum_divide_distrib [symmetric])
  also have "(\<Sum>k=1..n. of_nat k * \<chi> k) = (\<Sum>k=1..<n. of_nat k * \<chi> k)"
    using n by (intro sum.mono_neutral_right) (auto simp: eq_zero_iff)
  finally show eq: "Dirichlet_L n \<chi> 0 = -(\<Sum>k=1..<n. of_nat k * \<chi> k) / of_nat n"
    by simp
qed

lemma Dirichlet_L_0_even [simp]:
  assumes "\<chi> (n - 1) = 1"
  shows   "Dirichlet_L n \<chi> 0 = 0"
proof (cases "\<chi> = \<chi>\<^sub>0")
  case False
  hence "Dirichlet_L n \<chi> 0 = -(\<Sum>k=Suc 0..<n. of_nat k * \<chi> k) / of_nat n"
    by (simp add: Dirichlet_L_0_nonprincipal)
  also have "\<dots> = 0"
    using assms False by (subst even_dcharacter_linear_sum_eq_0) auto
  finally show "Dirichlet_L n \<chi> 0 = 0" .
qed auto

lemma Dirichlet_L_0:
  "Dirichlet_L n \<chi> 0 = (if \<chi> (n - 1) = 1 then 0 else -(\<Sum>k=1..<n. of_nat k * \<chi> k) / of_nat n)"
  by (cases "\<chi> = \<chi>\<^sub>0") (auto simp: Dirichlet_L_0_nonprincipal)

(*<*)
end
(*>*)
end


subsection \<open>Properties of $L(\chi, s)$ for real $\chi$\<close>

(*<*)
unbundle no_vec_lambda_notation
(*>*)

locale real_dcharacter = dcharacter +
  assumes real: "\<chi> k \<in> \<real>"
begin

lemma Im_eq_0 [simp]: "Im (\<chi> k) = 0"
  using real[of k] by (auto elim!: Reals_cases)

lemma of_real_Re [simp]: "of_real (Re (\<chi> k)) = \<chi> k"
  by (simp add: complex_eq_iff)

lemma char_cases: "\<chi> k \<in> {-1, 0, 1}"
proof -
  from norm[of k] have "Re (\<chi> k) \<in> {-1,0,1}" 
    by (auto simp: cmod_def split: if_splits)
  hence "of_real (Re (\<chi> k)) \<in> {-1, 0, 1}" by auto
  also have "of_real (Re (\<chi> k)) = \<chi> k" by (simp add: complex_eq_iff)
  finally show ?thesis .
qed

lemma cnj [simp]: "cnj (\<chi> k) = \<chi> k"
  by (simp add: complex_eq_iff)

lemma inv_character_id [simp]: "inv_character \<chi> = \<chi>"
  by (simp add: inv_character_def fun_eq_iff)

lemma Dirichlet_L_in_Reals:
  assumes "s \<in> \<real>"
  shows   "Dirichlet_L n \<chi> s \<in> \<real>"
proof -
  have "cnj (Dirichlet_L n \<chi> s) = Dirichlet_L n \<chi> s"
    using assms by (subst cnj_Dirichlet_L) (auto elim!: Reals_cases)
  thus ?thesis using Reals_cnj_iff by blast
qed

text \<open>
  The following property of real characters is used by Apostol to show the non-vanishing of
  $L(\chi, 1)$. We have already shown this in a much easier way, but this particular result is
  still of general interest.
\<close>
lemma
  assumes k: "k > 0"
  shows sum_char_divisors_ge: "Re (\<Sum>d | d dvd k. \<chi> d) \<ge> 0" (is "Re (?A k) \<ge> 0")
  and   sum_char_divisors_square_ge: "is_square k \<Longrightarrow> Re (\<Sum>d | d dvd k. \<chi> d) \<ge> 1"
proof -
  interpret sum: multiplicative_function ?A
    by (fact mult.multiplicative_sum_divisors)

  have A: "?A k \<in> \<real>" for k by (intro sum_in_Reals real)
  hence [simp]: "Im (?A k) = 0" for k by (auto elim!: Reals_cases)
  have *: "Re (?A (p ^ m)) \<ge> (if even m then 1 else 0)" if p: "prime p" for p m
  proof -
    have sum_neg1: "(\<Sum>i\<le>m. (-1) ^ i) = (if even m then 1 else (0::real))"
      by (induction m) auto
    from p have "?A (p ^ m) = (\<Sum>k\<le>m. \<chi> (p ^ k))"
      by (intro sum.reindex_bij_betw [symmetric] bij_betw_prime_power_divisors)
    also have "Re \<dots> = (\<Sum>k\<le>m. Re (\<chi> p) ^ k)" by (simp add: mult.power)
    also have "\<dots> \<ge> (if even m then 1 else 0)"
      using sum_neg1 char_cases[of p] by (auto simp: power_0_left)
    finally show ?thesis .
  qed
  have *: "Re (?A (p ^ m)) \<ge> 0" "even m \<Longrightarrow> Re (?A (p ^ m)) \<ge> 1" if "prime p" for p m
    using *[of p m] that by (auto split: if_splits)

  have eq: "Re (?A k) = (\<Prod>p\<in>prime_factors k. Re (?A (p ^ multiplicity p k)))"
    using k A by (subst sum.prod_prime_factors) (auto simp: Re_prod_Reals)
  show "Re (\<Sum>d | d dvd k. \<chi> d) \<ge> 0"  by (subst eq, intro prod_nonneg ballI *) auto

  assume "is_square k"
  then obtain m where m: "k = m ^ 2" by (auto elim!: is_nth_powerE)
  have "even (multiplicity p k)" if "prime p" for p using k that unfolding m
    by (subst prime_elem_multiplicity_power_distrib) (auto intro!: Nat.gr0I)
  thus "Re (\<Sum>d | d dvd k. \<chi> d) \<ge> 1"
    by (subst eq, intro prod_ge_1 ballI *) auto
qed

end

(*<*)
unbundle vec_lambda_notation
(*>*)

end
