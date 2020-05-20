(*
  File:    Ln_Gamma_Asymptotics.thy
  Author:  Manuel Eberl

  The complete asymptotics of the logarithmic Gamma function and the Polygamma functions.
*)
section \<open>Complete asymptotics of the logarithmic Gamma function\<close>
theory Ln_Gamma_Asymptotics
imports 
  "HOL-Complex_Analysis.Complex_Analysis"
  Bernoulli.Bernoulli_FPS 
  Bernoulli.Periodic_Bernpoly 
  Stirling_Formula
begin
  
subsection \<open>Auxiliary Facts\<close>
  
(* TODO Move *)
lemma filterlim_at_infinity_conv_norm_at_top:
  "filterlim f at_infinity G \<longleftrightarrow> filterlim (\<lambda>x. norm (f x)) at_top G"
  by (auto simp: filterlim_at_infinity[OF order.refl] filterlim_at_top_gt[of _ _ 0])

corollary Ln_times_of_nat:
    "\<lbrakk>r > 0; z \<noteq> 0\<rbrakk> \<Longrightarrow> Ln(of_nat r * z :: complex) = ln (of_nat r) + Ln(z)"
  using Ln_times_of_real[of "of_nat r" z] by simp

lemma tendsto_of_real_0_I: 
  "(f \<longlongrightarrow> 0) G \<Longrightarrow> ((\<lambda>x. (of_real (f x))) \<longlongrightarrow> (0 ::'a::real_normed_div_algebra)) G"
  by (subst (asm) tendsto_of_real_iff [symmetric]) simp  

lemma negligible_atLeastAtMostI: "b \<le> a \<Longrightarrow> negligible {a..(b::real)}"
  by (cases "b < a") auto
    
lemma integrable_on_negligible: 
 "negligible A \<Longrightarrow> (f :: 'n :: euclidean_space \<Rightarrow> 'a :: banach) integrable_on A"
  by (subst integrable_spike_set_eq[of _ "{}"]) (simp_all add: integrable_on_empty)  

lemma vector_derivative_cong_eq:
  assumes "eventually (\<lambda>x. x \<in> A \<longrightarrow> f x = g x) (nhds x)" "x = y" "A = B" "x \<in> A"
  shows   "vector_derivative f (at x within A) = vector_derivative g (at y within B)"
proof -
  from eventually_nhds_x_imp_x[OF assms(1)] assms(4) have "f x = g x" by blast
  hence "(\<lambda>D. (f has_vector_derivative D) (at x within A)) = 
           (\<lambda>D. (g has_vector_derivative D) (at x within A))" using assms
    by (intro ext has_vector_derivative_cong_ev refl assms) simp_all
  thus ?thesis by (simp add: vector_derivative_def assms)
qed

lemma differentiable_of_real [simp]: "of_real differentiable at x within A"
proof -
  have "(of_real has_vector_derivative 1) (at x within A)"
    by (auto intro!: derivative_eq_intros)
  thus ?thesis by (rule differentiableI_vector)
qed
  
lemma higher_deriv_cong_ev:
  assumes "eventually (\<lambda>x. f x = g x) (nhds x)" "x = y"
  shows   "(deriv ^^ n) f x = (deriv ^^ n) g y"
proof -
  from assms(1) have "eventually (\<lambda>x. (deriv ^^ n) f x = (deriv ^^ n) g x) (nhds x)"
  proof (induction n arbitrary: f g)
    case (Suc n)
    from Suc.prems have "eventually (\<lambda>y. eventually (\<lambda>z. f z = g z) (nhds y)) (nhds x)"
      by (simp add: eventually_eventually)
    hence "eventually (\<lambda>x. deriv f x = deriv g x) (nhds x)"
      by eventually_elim (rule deriv_cong_ev, simp_all)
    thus ?case by (auto intro!: deriv_cong_ev Suc simp: funpow_Suc_right simp del: funpow.simps)
  qed auto
  from eventually_nhds_x_imp_x[OF this] assms(2) show ?thesis by simp
qed

lemma deriv_of_real [simp]: 
  "at x within A \<noteq> bot \<Longrightarrow> vector_derivative of_real (at x within A) = 1"
  by (auto intro!: vector_derivative_within derivative_eq_intros)

lemma deriv_Re [simp]: "deriv Re = (\<lambda>_. 1)"
  by (auto intro!: DERIV_imp_deriv simp: fun_eq_iff)
    
lemma vector_derivative_of_real_left:
  assumes "f differentiable at x"
  shows   "vector_derivative (\<lambda>x. of_real (f x)) (at x) = of_real (deriv f x)"
proof -
  have "vector_derivative (of_real \<circ> f) (at x) = (of_real (deriv f x))"
    by (subst vector_derivative_chain_at)
       (simp_all add: scaleR_conv_of_real field_derivative_eq_vector_derivative assms)
  thus ?thesis by (simp add: o_def)
qed
  
lemma vector_derivative_of_real_right:
  assumes "f field_differentiable at (of_real x)"
  shows   "vector_derivative (\<lambda>x. f (of_real x)) (at x) = deriv f (of_real x)"
proof -
  have "vector_derivative (f \<circ> of_real) (at x) = deriv f (of_real x)"
    using assms by (subst vector_derivative_chain_at_general) simp_all
  thus ?thesis by (simp add: o_def)
qed
  
lemma Ln_holomorphic [holomorphic_intros]:
  assumes "A \<inter> \<real>\<^sub>\<le>\<^sub>0 = {}"
  shows   "Ln holomorphic_on (A :: complex set)"
proof (intro holomorphic_onI)
  fix z assume "z \<in> A"
  with assms have "(Ln has_field_derivative inverse z) (at z within A)"
    by (auto intro!: derivative_eq_intros)
  thus "Ln field_differentiable at z within A" by (auto simp: field_differentiable_def)
qed

lemma ln_Gamma_holomorphic [holomorphic_intros]: 
  assumes "A \<inter> \<real>\<^sub>\<le>\<^sub>0 = {}"
  shows   "ln_Gamma holomorphic_on (A :: complex set)"
proof (intro holomorphic_onI)
  fix z assume "z \<in> A"
  with assms have "(ln_Gamma has_field_derivative Digamma z) (at z within A)"
    by (auto intro!: derivative_eq_intros)
  thus "ln_Gamma field_differentiable at z within A" by (auto simp: field_differentiable_def)
qed
  
lemma higher_deriv_Polygamma:
  assumes "z \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "(deriv ^^ n) (Polygamma m) z = 
             Polygamma (m + n) (z :: 'a :: {real_normed_field,euclidean_space})"
proof -
  have "eventually (\<lambda>u. (deriv ^^ n) (Polygamma m) u = Polygamma (m + n) u) (nhds z)"
  proof (induction n)
    case (Suc n)
    from Suc.IH have "eventually (\<lambda>z. eventually (\<lambda>u. (deriv ^^ n) (Polygamma m) u = Polygamma (m + n) u) (nhds z)) (nhds z)"
      by (simp add: eventually_eventually)
    hence "eventually (\<lambda>z. deriv ((deriv ^^ n) (Polygamma m)) z = 
             deriv (Polygamma (m + n)) z) (nhds z)"
      by eventually_elim (intro deriv_cong_ev refl)
    moreover have "eventually (\<lambda>z. z \<in> UNIV - \<int>\<^sub>\<le>\<^sub>0) (nhds z)" using assms
      by (intro eventually_nhds_in_open open_Diff open_UNIV) auto
    ultimately show ?case by eventually_elim (simp_all add: deriv_Polygamma)
  qed simp_all
  thus ?thesis by (rule eventually_nhds_x_imp_x)
qed
  
lemma higher_deriv_cmult:
  assumes "f holomorphic_on A" "x \<in> A" "open A"
  shows   "(deriv ^^ j) (\<lambda>x. c * f x) x = c * (deriv ^^ j) f x"
  using assms
proof (induction j arbitrary: f x)
  case (Suc j f x)
  have "deriv ((deriv ^^ j) (\<lambda>x. c * f x)) x = deriv (\<lambda>x. c * (deriv ^^ j) f x) x"
    using eventually_nhds_in_open[of A x] assms(2,3) Suc.prems
    by (intro deriv_cong_ev refl) (auto elim!: eventually_mono simp: Suc.IH)
  also have "\<dots> = c * deriv ((deriv ^^ j) f) x" using Suc.prems assms(2,3)
    by (intro deriv_cmult holomorphic_on_imp_differentiable_at holomorphic_higher_deriv) auto
  finally show ?case by simp
qed simp_all

lemma higher_deriv_ln_Gamma_complex:
  assumes "(x::complex) \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(deriv ^^ j) ln_Gamma x = (if j = 0 then ln_Gamma x else Polygamma (j - 1) x)"
proof (cases j)
  case (Suc j')
  have "(deriv ^^ j') (deriv ln_Gamma) x = (deriv ^^ j') Digamma x"
    using eventually_nhds_in_open[of "UNIV - \<real>\<^sub>\<le>\<^sub>0" x] assms
    by (intro higher_deriv_cong_ev refl)
       (auto elim!: eventually_mono simp: open_Diff deriv_ln_Gamma_complex)
  also have "\<dots> = Polygamma j' x" using assms
    by (subst higher_deriv_Polygamma)
       (auto elim!: nonpos_Ints_cases simp: complex_nonpos_Reals_iff)
  finally show ?thesis using Suc by (simp del: funpow.simps add: funpow_Suc_right)
qed simp_all

lemma higher_deriv_ln_Gamma_real:
  assumes "(x::real) > 0"
  shows   "(deriv ^^ j) ln_Gamma x = (if j = 0 then ln_Gamma x else Polygamma (j - 1) x)"
proof (cases j)
  case (Suc j')
  have "(deriv ^^ j') (deriv ln_Gamma) x = (deriv ^^ j') Digamma x"
    using eventually_nhds_in_open[of "{0<..}" x] assms
    by (intro higher_deriv_cong_ev refl)
       (auto elim!: eventually_mono simp: open_Diff deriv_ln_Gamma_real)
  also have "\<dots> = Polygamma j' x" using assms
    by (subst higher_deriv_Polygamma)
       (auto elim!: nonpos_Ints_cases simp: complex_nonpos_Reals_iff)
  finally show ?thesis using Suc by (simp del: funpow.simps add: funpow_Suc_right)
qed simp_all
  
lemma higher_deriv_ln_Gamma_complex_of_real:
  assumes "(x :: real) > 0"
  shows   "(deriv ^^ j) ln_Gamma (complex_of_real x) = of_real ((deriv ^^ j) ln_Gamma x)"
    using assms
    by (auto simp: higher_deriv_ln_Gamma_real higher_deriv_ln_Gamma_complex
                   ln_Gamma_complex_of_real Polygamma_of_real)
(* END TODO *)

lemma stirling_limit_aux1: 
  "((\<lambda>y. Ln (1 + z * of_real y) / of_real y) \<longlongrightarrow> z) (at_right 0)" for z :: complex
proof (cases "z = 0")
  case True
  then show ?thesis by simp
next
  case False
  have "((\<lambda>y. ln (1 + z * of_real y)) has_vector_derivative 1 * z) (at 0)"
    by (rule has_vector_derivative_real_field) (auto intro!: derivative_eq_intros)
  then have "(\<lambda>y. (Ln (1 + z * of_real y) - of_real y * z) / of_real \<bar>y\<bar>) \<midarrow>0\<rightarrow> 0"
    by (auto simp add: has_vector_derivative_def has_derivative_def netlimit_at 
          scaleR_conv_of_real field_simps)
  then have "((\<lambda>y. (Ln (1 + z * of_real y) - of_real y * z) / of_real \<bar>y\<bar>) \<longlongrightarrow> 0) (at_right 0)"
    by (rule filterlim_mono[OF _ _ at_le]) simp_all
  also have "?this \<longleftrightarrow> ((\<lambda>y. Ln (1 + z * of_real y) / (of_real y) - z) \<longlongrightarrow> 0) (at_right 0)"
    using eventually_at_right_less[of "0::real"]
    by (intro filterlim_cong refl) (auto elim!: eventually_mono simp: field_simps)
  finally show ?thesis by (simp only: LIM_zero_iff)
qed
  
lemma stirling_limit_aux2: 
  "((\<lambda>y. y * Ln (1 + z / of_real y)) \<longlongrightarrow> z) at_top" for z :: complex
  using stirling_limit_aux1[of z] by (subst filterlim_at_top_to_right) (simp add: field_simps)

lemma Union_atLeastAtMost: 
  assumes "N > 0" 
  shows   "(\<Union>n\<in>{0..<N}. {real n..real (n + 1)}) = {0..real N}"
proof (intro equalityI subsetI)
  fix x assume x: "x \<in> {0..real N}"
  thus "x \<in> (\<Union>n\<in>{0..<N}. {real n..real (n + 1)})"
  proof (cases "x = real N")
    case True
    with assms show ?thesis by (auto intro!: bexI[of _ "N - 1"])
  next
    case False
    with x have x: "x \<ge> 0" "x < real N" by simp_all
    hence "x \<ge> real (nat \<lfloor>x\<rfloor>)" "x \<le> real (nat \<lfloor>x\<rfloor> + 1)" by linarith+
    moreover from x have "nat \<lfloor>x\<rfloor> < N" by linarith
    ultimately have "\<exists>n\<in>{0..<N}. x \<in> {real n..real (n + 1)}"
      by (intro bexI[of _ "nat \<lfloor>x\<rfloor>"]) simp_all
    thus ?thesis by blast
  qed
qed auto


subsection \<open>Asymptotics of @{term ln_Gamma}\<close>

text \<open>
  This is the error term that occurs in the expansion of @{term ln_Gamma}. It can be shown to 
  be of order $O(s^{-n})$.
\<close>
definition stirling_integral :: "nat \<Rightarrow> 'a :: {real_normed_div_algebra, banach} \<Rightarrow> 'a" where
  "stirling_integral n s = 
     lim (\<lambda>N. integral {0..N} (\<lambda>x. of_real (pbernpoly n x) / (of_real x + s) ^ n))"

text \<open>
  
\<close>

context
  fixes s :: complex assumes s: "Re s > 0"
  fixes approx :: "nat \<Rightarrow> complex"
  defines "approx \<equiv> (\<lambda>N. 
    (\<Sum>n = 1..<N. s / of_nat n - ln (1 + s / of_nat n)) - (euler_mascheroni * s + ln s) - \<comment> \<open>\<open>\<longrightarrow> ln_Gamma s\<close>\<close>
    (ln_Gamma (of_nat N) - ln (2 * pi / of_nat N) / 2 - of_nat N * ln (of_nat N) + of_nat N) - \<comment> \<open>\<open>\<longrightarrow> 0\<close>\<close>
    s * (harm (N - 1) - ln (of_nat (N - 1)) - euler_mascheroni) + \<comment> \<open>\<open>\<longrightarrow> 0\<close>\<close>
    s * (ln (of_nat N + s) - ln (of_nat (N - 1))) - \<comment> \<open>\<open>\<longrightarrow> 0\<close>\<close>
    (1/2) * (ln (of_nat N + s) - ln (of_nat N)) +       \<comment> \<open>\<open>\<longrightarrow> 0\<close>\<close>
    of_nat N * (ln (of_nat N + s) - ln (of_nat N)) -  \<comment> \<open>\<open>\<longrightarrow> s\<close>\<close>
    (s - 1/2) * ln s - ln (2 * pi) / 2)"
begin       
  
qualified lemma
  assumes N: "N > 0"
  shows   integrable_pbernpoly_1:
            "(\<lambda>x. of_real (-pbernpoly 1 x) / (of_real x + s)) integrable_on {0..real N}"
  and     integral_pbernpoly_1_aux:
            "integral {0..real N} (\<lambda>x. -of_real (pbernpoly 1 x) / (of_real x + s)) = approx N"
  and     has_integral_pbernpoly_1:
            "((\<lambda>x. pbernpoly 1 x /(x + s)) has_integral 
              (\<Sum>m<N. (of_nat m + 1 / 2 + s) * (ln (of_nat m + s) - 
                        ln (of_nat m + 1 + s)) + 1)) {0..real N}"
proof -
  let ?A = "(\<lambda>n. {of_nat n..of_nat (n+1)}) ` {0..<N}"
  have has_integral: 
    "((\<lambda>x. -pbernpoly 1 x / (x + s)) has_integral 
             (of_nat n + 1/2 + s) * (ln (of_nat (n + 1) + s) - ln (of_nat n + s)) - 1) 
           {of_nat n..of_nat (n + 1)}" for n
  proof (rule has_integral_spike)      
    have "((\<lambda>x. (of_nat n + 1/2 + s) * (1 / (x + s)) - 1) has_integral 
              (of_nat n + 1/2 + s) * (ln (of_real (real (n + 1)) + s) - ln (of_real (real n) + s)) - 1) 
            {of_nat n..of_nat (n + 1)}" 
      using s has_integral_const_real[of 1 "of_nat n" "of_nat (n + 1)"]
      by (intro has_integral_diff has_integral_mult_right fundamental_theorem_of_calculus)
         (auto intro!: derivative_eq_intros has_vector_derivative_real_field
               simp: has_field_derivative_iff_has_vector_derivative [symmetric] field_simps
                     complex_nonpos_Reals_iff)
    thus "((\<lambda>x. (of_nat n + 1/2 + s) * (1 / (x + s)) - 1) has_integral 
              (of_nat n + 1/2 + s) * (ln (of_nat (n + 1) + s) - ln (of_nat n + s)) - 1) 
            {of_nat n..of_nat (n + 1)}" by simp
             
    show "-pbernpoly 1 x / (x + s) = (of_nat n + 1/2 + s) * (1 / (x + s)) - 1"
         if "x \<in> {of_nat n..of_nat (n + 1)} - {of_nat (n + 1)}" for x
    proof -
      have x: "x \<ge> real n" "x < real (n + 1)" using that by simp_all
      hence "floor x = int n" by linarith
      moreover from s x have "complex_of_real x \<noteq> -s" 
        by (auto simp add: complex_eq_iff simp del: of_nat_Suc)
      ultimately show "-pbernpoly 1 x / (x + s) = (of_nat n + 1/2 + s) * (1 / (x + s)) - 1"
        by (auto simp: pbernpoly_def bernpoly_def frac_def divide_simps add_eq_0_iff2)
    qed
  qed simp_all
  hence *: "\<And>I. I\<in>?A \<Longrightarrow> ((\<lambda>x. -pbernpoly 1 x / (x + s)) has_integral 
              (Inf I + 1/2 + s) * (ln (Inf I + 1 + s) - ln (Inf I + s)) - 1) I"
    by (auto simp: add_ac)
  have "((\<lambda>x. - pbernpoly 1 x / (x + s)) has_integral
          (\<Sum>I\<in>?A. (Inf I + 1 / 2 + s) * (ln (Inf I + 1 + s) - ln (Inf I + s)) - 1))
          (\<Union>n\<in>{0..<N}. {real n..real (n + 1)})" (is "(_ has_integral ?i) _")
    apply (intro has_integral_Union * finite_imageI)
      apply (force intro!: negligible_atLeastAtMostI pairwiseI)+
    done
  hence has_integral: "((\<lambda>x. - pbernpoly 1 x / (x + s)) has_integral ?i) {0..real N}"
    by (subst has_integral_spike_set_eq)
       (use Union_atLeastAtMost assms in \<open>auto simp: intro!: empty_imp_negligible\<close>)
  hence "(\<lambda>x. - pbernpoly 1 x / (x + s)) integrable_on {0..real N}"
    and integral:   "integral {0..real N} (\<lambda>x. - pbernpoly 1 x / (x + s)) = ?i"
    by (simp_all add: has_integral_iff)
  show "(\<lambda>x. - pbernpoly 1 x / (x + s)) integrable_on {0..real N}" by fact

  note has_integral_neg[OF has_integral]
  also have "-?i = (\<Sum>x<N. (of_nat x + 1 / 2 + s) * (ln (of_nat x + s) - ln (of_nat x + 1 + s)) + 1)" 
    by (subst sum.reindex) 
       (simp_all add: inj_on_def atLeast0LessThan algebra_simps sum_negf [symmetric])
  finally show has_integral: 
    "((\<lambda>x. of_real (pbernpoly 1 x) / (of_real x + s)) has_integral \<dots>) {0..real N}" by simp
      
  note integral
  also have "?i = (\<Sum>n<N. (of_nat n + 1 / 2 + s) * 
                    (ln (of_nat n + 1 + s) - ln (of_nat n + s))) - N" (is "_ = ?S - _")
    by (subst sum.reindex) (simp_all add: inj_on_def sum_subtractf atLeast0LessThan)
  also have "?S = (\<Sum>n<N. of_nat n * (ln (of_nat n + 1 + s) - ln (of_nat n + s))) +
                    (s + 1 / 2) * (\<Sum>n<N. ln (of_nat (Suc n) + s) - ln (of_nat n + s))" 
    (is "_ = ?S1 + _ * ?S2") by (simp add: algebra_simps sum.distrib sum_subtractf sum_distrib_left)
  also have "?S2 = ln (of_nat N + s) - ln s" by (subst sum_lessThan_telescope) simp
  also have "?S1 = (\<Sum>n=1..<N. of_nat n * (ln (of_nat n + 1 + s) - ln (of_nat n + s)))"
    by (intro sum.mono_neutral_right) auto
  also have "\<dots> = (\<Sum>n=1..<N. of_nat n * ln (of_nat n + 1 + s)) - (\<Sum>n=1..<N. of_nat n * ln (of_nat n + s))"
    by (simp add: algebra_simps sum_subtractf)
  also have "(\<Sum>n=1..<N. of_nat n * ln (of_nat n + 1 + s)) = 
               (\<Sum>n=1..<N. (of_nat n - 1) * ln (of_nat n + s)) + (N - 1) * ln (of_nat N + s)"
    by (induction N) (simp_all add: add_ac of_nat_diff)
  also have "\<dots> - (\<Sum>n = 1..<N. of_nat n * ln (of_nat n + s)) =
               -(\<Sum>n=1..<N. ln (of_nat n + s)) + (N - 1) * ln (of_nat N + s)"
    by (induction N) (simp_all add: algebra_simps)
  also from s have neq: "s + of_nat x \<noteq> 0" for x by (auto simp: complex_eq_iff)
  hence "(\<Sum>n=1..<N. ln (of_nat n + s)) = (\<Sum>n=1..<N. ln (of_nat n) + ln (1 + s/n))"
    by (intro sum.cong refl, subst Ln_times_of_nat [symmetric]) (auto simp: divide_simps add_ac)
  also have "\<dots> = ln (fact (N - 1)) + (\<Sum>n=1..<N. ln (1 + s/n))"
    by (induction N) (simp_all add: Ln_times_of_nat fact_reduce add_ac)
  also have "(\<Sum>n=1..<N. ln (1 + s/n)) = -(\<Sum>n=1..<N. s / n - ln (1 + s/n)) + s * (\<Sum>n=1..<N. 1 / of_nat n)"
    by (simp add: sum_distrib_left sum_subtractf) 
  also from N have "ln (fact (N - 1)) = ln_Gamma (of_nat N :: complex)" 
    by (simp add: ln_Gamma_complex_conv_fact)
  also have "{1..<N} = {1..N - 1}" by auto
  hence "(\<Sum>n = 1..<N. 1 / of_nat n) = (harm (N - 1) :: complex)" 
    by (simp add: harm_def divide_simps)
  also have "- (ln_Gamma (of_nat N) + (- (\<Sum>n = 1..<N. s / of_nat n - ln (1 + s / of_nat n)) +
                 s * harm (N - 1))) + of_nat (N - 1) * ln (of_nat N + s) +
                (s + 1 / 2) * (ln (of_nat N + s) - ln s) - of_nat N = approx N"
    using N by (simp add: field_simps of_nat_diff ln_div approx_def Ln_of_nat 
                          ln_Gamma_complex_of_real [symmetric])
  finally show "integral {0..of_nat N} (\<lambda>x. -of_real (pbernpoly 1 x) / (of_real x + s)) = \<dots>" 
    by simp
qed
  
lemma integrable_ln_Gamma_aux:
  shows   "(\<lambda>x. of_real (pbernpoly n x) / (of_real x + s) ^ n) integrable_on {0..real N}"
proof (cases "n = 1")
  case True
  with s show ?thesis using integrable_neg[OF integrable_pbernpoly_1[of N]] 
    by (cases "N = 0") (simp_all add: integrable_on_negligible)
next
  case False
  from s have "of_real x + s \<noteq> 0" if "x \<ge> 0" for x using that 
    by (auto simp: complex_eq_iff add_eq_0_iff2)
  with False s show ?thesis
    by (auto intro!: integrable_continuous_real continuous_intros)
qed
  
text \<open>
  This following proof is based on ``Rudiments of the theory of the gamma function'' 
  by Bruce Berndt~\cite{berndt}.
\<close>
qualified lemma integral_pbernpoly_1: 
  "(\<lambda>N. integral {0..real N} (\<lambda>x. pbernpoly 1 x / (x + s)))
     \<longlonglongrightarrow> -ln_Gamma s - s + (s - 1 / 2) * ln s + ln (2 * pi) / 2"
proof -  
  have neq: "s + of_real x \<noteq> 0" if "x \<ge> 0" for x :: real
    using that s by (auto simp: complex_eq_iff)
  have "(approx \<longlongrightarrow> ln_Gamma s - 0 - 0 + 0 - 0 + s - (s - 1/2) * ln s - ln (2 * pi) / 2) at_top"
    unfolding approx_def
  proof (intro tendsto_add tendsto_diff)
    from s have s': "s \<notin> \<int>\<^sub>\<le>\<^sub>0" by (auto elim!: nonpos_Ints_cases)
    have "(\<lambda>n. \<Sum>i=1..<n. s / of_nat i - ln (1 + s / of_nat i)) \<longlonglongrightarrow> 
             ln_Gamma s + euler_mascheroni * s + ln s" (is "?f \<longlonglongrightarrow> _")
      using ln_Gamma_series'_aux[OF s'] unfolding sums_def 
      by (subst LIMSEQ_Suc_iff [symmetric], subst (asm) sum.atLeast1_atMost_eq [symmetric]) 
         (simp add: atLeastLessThanSuc_atLeastAtMost)
    thus "((\<lambda>n. ?f n - (euler_mascheroni * s + ln s)) \<longlongrightarrow> ln_Gamma s) at_top"
      by (auto intro: tendsto_eq_intros)
  next
    show "(\<lambda>x. complex_of_real (ln_Gamma (real x) - ln (2 * pi / real x) / 2 - 
                 real x * ln (real x) + real x)) \<longlonglongrightarrow> 0"
    proof (intro tendsto_of_real_0_I 
             filterlim_compose[OF tendsto_sandwich filterlim_real_sequentially])
      show "eventually (\<lambda>x::real. ln_Gamma x - ln (2 * pi / x) / 2 - x * ln x + x \<ge> 0) at_top"
        using eventually_ge_at_top[of "1::real"] 
        by eventually_elim (insert ln_Gamma_bounds(1), simp add: algebra_simps)
      show "eventually (\<lambda>x::real. ln_Gamma x - ln (2 * pi / x) / 2 - x * ln x + x \<le> 
              1 / 12 * inverse x) at_top"
        using eventually_ge_at_top[of "1::real"] 
        by eventually_elim (insert ln_Gamma_bounds(2), simp add: field_simps)
      show "((\<lambda>x::real. 1 / 12 * inverse x) \<longlongrightarrow> 0) at_top"
        by (intro tendsto_mult_right_zero tendsto_inverse_0_at_top filterlim_ident)
    qed simp_all
  next
    have "(\<lambda>x. s * of_real (harm (x - 1) - ln (real (x - 1)) - euler_mascheroni)) \<longlonglongrightarrow> 
            s * of_real (euler_mascheroni - euler_mascheroni)"
      by (subst LIMSEQ_Suc_iff [symmetric], intro tendsto_intros) 
         (insert euler_mascheroni_LIMSEQ, simp_all)
    also have "?this \<longleftrightarrow> (\<lambda>x. s * (harm (x - 1) - ln (of_nat (x - 1)) - euler_mascheroni)) \<longlonglongrightarrow> 0"
      by (intro filterlim_cong refl eventually_mono[OF eventually_gt_at_top[of "1::nat"]]) 
         (auto simp: Ln_of_nat of_real_harm)
    finally show "(\<lambda>x. s * (harm (x - 1) - ln (of_nat (x - 1)) - euler_mascheroni)) \<longlonglongrightarrow> 0"  .
  next
    have "((\<lambda>x. ln (1 + (s + 1) / of_real x)) \<longlongrightarrow> ln (1 + 0)) at_top" (is ?P)
      by (intro tendsto_intros tendsto_divide_0[OF tendsto_const]) 
         (simp_all add: filterlim_ident filterlim_at_infinity_conv_norm_at_top filterlim_abs_real)
    also have "ln (of_real (x + 1) + s) - ln (complex_of_real x) = ln (1 + (s + 1) / of_real x)" 
      if "x > 1" for x using that s
      using Ln_divide_of_real[of x "of_real (x + 1) + s", symmetric] neq[of "x+1"]
      by (simp add: field_simps Ln_of_real)
    hence "?P \<longleftrightarrow> ((\<lambda>x. ln (of_real (x + 1) + s) - ln (of_real x)) \<longlongrightarrow> 0) at_top"
      by (intro filterlim_cong refl) 
         (auto intro: eventually_mono[OF eventually_gt_at_top[of "1::real"]])
    finally have "((\<lambda>n. ln (of_real (real n + 1) + s) - ln (of_real (real n))) \<longlongrightarrow> 0) at_top"
      by (rule filterlim_compose[OF _ filterlim_real_sequentially])
    hence "((\<lambda>n. ln (of_nat n + s) - ln (of_nat (n - 1))) \<longlongrightarrow> 0) at_top"
      by (subst LIMSEQ_Suc_iff [symmetric]) (simp add: add_ac)
    thus "(\<lambda>x. s * (ln (of_nat x + s) - ln (of_nat (x - 1)))) \<longlonglongrightarrow> 0"
      by (rule tendsto_mult_right_zero)
  next
    have "((\<lambda>x. ln (1 + s / of_real x)) \<longlongrightarrow> ln (1 + 0)) at_top" (is ?P)
      by (intro tendsto_intros tendsto_divide_0[OF tendsto_const]) 
         (simp_all add: filterlim_ident  filterlim_at_infinity_conv_norm_at_top filterlim_abs_real)
    also have "ln (of_real x + s) - ln (of_real x) = ln (1 + s / of_real x)" if "x > 0" for x
      using Ln_divide_of_real[of x "of_real x + s"] neq[of x] that
      by (auto simp: field_simps Ln_of_real)
    hence "?P \<longleftrightarrow> ((\<lambda>x. ln (of_real x + s) - ln (of_real x)) \<longlongrightarrow> 0) at_top"
      using s by (intro filterlim_cong refl) 
                 (auto intro: eventually_mono [OF eventually_gt_at_top[of "1::real"]])
    finally have "(\<lambda>x. (1/2) * (ln (of_real (real x) + s) - ln (of_real (real x)))) \<longlonglongrightarrow> 0"        
      by (rule tendsto_mult_right_zero[OF filterlim_compose[OF _ filterlim_real_sequentially]])
    thus "(\<lambda>x. (1/2) * (ln (of_nat x + s) - ln (of_nat x))) \<longlonglongrightarrow> 0" by simp
  next
    have "((\<lambda>x. x * (ln (1 + s / of_real x))) \<longlongrightarrow> s) at_top" (is ?P) 
      by (rule stirling_limit_aux2)
    also have "ln (1 + s / of_real x) = ln (of_real x + s) - ln (of_real x)" if "x > 1" for x 
      using that s Ln_divide_of_real [of x "of_real x + s", symmetric] neq[of x]
      by (auto simp: Ln_of_real field_simps)
    hence "?P \<longleftrightarrow> ((\<lambda>x. of_real x * (ln (of_real x + s) - ln (of_real x))) \<longlongrightarrow> s) at_top"
      by (intro filterlim_cong refl) 
         (auto intro: eventually_mono[OF eventually_gt_at_top[of "1::real"]])
    finally have "(\<lambda>n. of_real (real n) * (ln (of_real (real n) + s) - ln (of_real (real n)))) \<longlonglongrightarrow> s"
      by (rule filterlim_compose[OF _ filterlim_real_sequentially])
    thus "(\<lambda>n. of_nat n * (ln (of_nat n + s) - ln (of_nat n))) \<longlonglongrightarrow> s" by simp
  qed simp_all
  also have "?this \<longleftrightarrow> ((\<lambda>N. integral {0..real N} (\<lambda>x. -pbernpoly 1 x / (x + s))) \<longlongrightarrow>
                         ln_Gamma s + s - (s - 1/2) * ln s - ln (2 * pi) / 2) at_top"
    using integral_pbernpoly_1_aux
    by (intro filterlim_cong refl) 
       (auto intro: eventually_mono[OF eventually_gt_at_top[of "0::nat"]])
  also have "(\<lambda>N. integral {0..real N} (\<lambda>x. -pbernpoly 1 x / (x + s))) =
               (\<lambda>N. -integral {0..real N} (\<lambda>x. pbernpoly 1 x / (x + s)))"
    by (simp add: fun_eq_iff)
  finally show ?thesis by (simp add: tendsto_minus_cancel_left [symmetric] algebra_simps)
qed


qualified lemma pbernpoly_integral_conv_pbernpoly_integral_Suc:
  assumes "n \<ge> 1"
  shows   "integral {0..real N} (\<lambda>x. pbernpoly n x / (x + s) ^ n) =
             of_real (pbernpoly (Suc n) (real N)) / (of_nat (Suc n) * (s + of_nat N) ^ n) -
             of_real (bernoulli (Suc n)) / (of_nat (Suc n) * s ^ n) + of_nat n / of_nat (Suc n) * 
               integral {0..real N} (\<lambda>x. of_real (pbernpoly (Suc n) x) / (of_real x + s) ^ Suc n)"
proof - 
  note [derivative_intros] = has_field_derivative_pbernpoly_Suc'
  define I where "I = -of_real (pbernpoly (Suc n) (of_nat N)) / (of_nat (Suc n) * (of_nat N + s) ^ n) +
            of_real (bernoulli (Suc n) / real (Suc n)) / s ^ n +
            integral {0..real N} (\<lambda>x. of_real (pbernpoly n x) / (of_real x + s) ^ n)"
  have "((\<lambda>x. (-of_nat n * inverse (of_real x + s) ^ Suc n) * 
          (of_real (pbernpoly (Suc n) x) / (of_nat (Suc n))))
          has_integral -I) {0..real N}"
  proof (rule integration_by_parts_interior_strong[OF bounded_bilinear_mult])
    fix x :: real assume x: "x \<in> {0<..<real N} - real ` {0..N}"
    have "x \<notin> \<int>"
    proof
      assume "x \<in> \<int>"
      then obtain n where "x = of_int n" by (auto elim!: Ints_cases)
      with x have x': "x = of_nat (nat n)" by simp
      from x show False by (auto simp: x')
    qed
    hence "((\<lambda>x. of_real (pbernpoly (Suc n) x / of_nat (Suc n))) has_vector_derivative
        complex_of_real (pbernpoly n x)) (at x)"
      by (intro has_vector_derivative_of_real) (auto intro!: derivative_eq_intros)
    thus "((\<lambda>x. of_real (pbernpoly (Suc n) x) / of_nat (Suc n)) has_vector_derivative
            complex_of_real (pbernpoly n x)) (at x)" by simp
    from x s have "complex_of_real x + s \<noteq> 0" by (auto simp: complex_eq_iff)
    thus "((\<lambda>x. inverse (of_real x + s) ^ n) has_vector_derivative 
             - of_nat n * inverse (of_real x + s) ^ Suc n) (at x)" using x s assms
      by (auto intro!: derivative_eq_intros has_vector_derivative_real_field simp: divide_simps power_add [symmetric]
               simp del: power_Suc)
  next
    have "complex_of_real x + s \<noteq> 0" if "x \<ge> 0" for x 
      using that s by (auto simp: complex_eq_iff)
    thus "continuous_on {0..real N} (\<lambda>x. inverse (of_real x + s) ^ n)" 
         "continuous_on {0..real N} (\<lambda>x. complex_of_real (pbernpoly (Suc n) x) / of_nat (Suc n))"
      using assms s by (auto intro!: continuous_intros simp del: of_nat_Suc)
  next
    have "((\<lambda>x. inverse (of_real x + s) ^ n * of_real (pbernpoly n x)) has_integral
            pbernpoly (Suc n) (of_nat N) / (of_nat (Suc n) * (of_nat N + s) ^ n) -
            of_real (bernoulli (Suc n) / real (Suc n)) / s ^ n - -I) {0..real N}" 
      using integrable_ln_Gamma_aux[of n N] assms
      by (auto simp: I_def has_integral_integral divide_simps)
    thus "((\<lambda>x. inverse (of_real x + s) ^ n * of_real (pbernpoly n x)) has_integral
              inverse (of_real (real N) + s) ^ n * (of_real (pbernpoly (Suc n) (real N)) / 
                  of_nat (Suc n)) -
              inverse (of_real 0 + s) ^ n * (of_real (pbernpoly (Suc n) 0) / of_nat (Suc n)) - - I)
            {0..real N}" by (simp_all add: field_simps)
  qed simp_all
  also have "(\<lambda>x. - of_nat n * inverse (of_real x + s) ^ Suc n * (of_real (pbernpoly (Suc n) x) /
                         of_nat (Suc n))) =
             (\<lambda>x. - (of_nat n / of_nat (Suc n) * of_real (pbernpoly (Suc n) x) / 
                         (of_real x + s) ^ Suc n))"
    by (simp add: divide_simps fun_eq_iff)
  finally have "((\<lambda>x. - (of_nat n / of_nat (Suc n) * of_real (pbernpoly (Suc n) x) /
                            (of_real x + s) ^ Suc n)) has_integral - I) {0..real N}" .
  from has_integral_neg[OF this] show ?thesis
    by (auto simp add: I_def has_integral_iff algebra_simps integral_mult_right [symmetric] 
             simp del: power_Suc of_nat_Suc )
qed

lemma pbernpoly_over_power_tendsto_0: 
  assumes "n > 0"
  shows   "(\<lambda>x. of_real (pbernpoly (Suc n) (real x)) / (of_nat (Suc n) * (s + of_nat x) ^ n)) \<longlonglongrightarrow> 0"
proof -
  from s have neq: "s + of_nat n \<noteq> 0" for n by (auto simp: complex_eq_iff)
  from bounded_pbernpoly[of "Suc n"] guess c . note c = this
  have "eventually (\<lambda>x. norm (of_real (pbernpoly (Suc n) (real x)) / 
                                    (of_nat (Suc n) * (s + of_nat x) ^ n)) \<le>
                          (c / real (Suc n)) / real x ^ n) at_top"
    using eventually_gt_at_top[of "0::nat"]
  proof eventually_elim
    case (elim x)
    have "norm (of_real (pbernpoly (Suc n) (real x)) / 
                                    (of_nat (Suc n) * (s + of_nat x) ^ n)) \<le>
            (c / real (Suc n)) / norm (s + of_nat x) ^ n" (is "_ \<le> ?rhs") using c[of x]
      by (auto simp: norm_divide norm_mult norm_power neq field_simps simp del: of_nat_Suc)
    also have "real x \<le> cmod (s + of_nat x)"
      using complex_Re_le_cmod[of "s + of_nat x"] s by simp
    hence "?rhs \<le> (c / real (Suc n)) / real x ^ n" using s elim c[of 0] neq[of x]
      by (intro divide_left_mono power_mono mult_pos_pos divide_nonneg_pos zero_less_power) auto
    finally show ?case .
  qed 
  moreover have "(\<lambda>x. (c / real (Suc n)) / real x ^ n) \<longlonglongrightarrow> 0"
    by (intro real_tendsto_divide_at_top[OF tendsto_const] filterlim_pow_at_top assms
              filterlim_real_sequentially)
  ultimately show ?thesis by (rule Lim_null_comparison)
qed

lemma convergent_stirling_integral:
  assumes "n > 0"
  shows   "convergent (\<lambda>N. integral {0..real N} 
             (\<lambda>x. of_real (pbernpoly n x) / (of_real x + s) ^ n))" (is "convergent (?f n)")
proof -
  have "convergent (?f (Suc n))" for n
  proof (induction n)
    case 0
    thus ?case using integral_pbernpoly_1 by (auto intro!: convergentI)
  next
    case (Suc n)
    have "convergent (\<lambda>N. ?f (Suc n) N -
            of_real (pbernpoly (Suc (Suc n)) (real N)) / 
                (of_nat (Suc (Suc n)) * (s + of_nat N) ^ Suc n) +
            of_real (bernoulli (Suc (Suc n)) / (real (Suc (Suc n)))) / s ^ Suc n)" 
      (is "convergent ?g")
      by (intro convergent_add convergent_diff Suc 
            convergent_const convergentI[OF pbernpoly_over_power_tendsto_0]) simp_all
    also have "?g = (\<lambda>N. of_nat (Suc n) / of_nat (Suc (Suc n)) * ?f (Suc (Suc n)) N)" using s
      by (subst pbernpoly_integral_conv_pbernpoly_integral_Suc) 
         (auto simp: fun_eq_iff field_simps simp del: of_nat_Suc power_Suc)
    also have "convergent \<dots> \<longleftrightarrow> convergent (?f (Suc (Suc n)))"
      by (intro convergent_mult_const_iff) (simp_all del: of_nat_Suc)
    finally show ?case .
  qed
  from this[of "n - 1"] assms show ?thesis by simp
qed

lemma stirling_integral_conv_stirling_integral_Suc:
  assumes "n > 0"
  shows   "stirling_integral n s =
             of_nat n / of_nat (Suc n) * stirling_integral (Suc n) s -
             of_real (bernoulli (Suc n)) / (of_nat (Suc n) * s ^ n)"
proof -
  have "(\<lambda>N. of_real (pbernpoly (Suc n) (real N)) / (of_nat (Suc n) * (s + of_nat N) ^ n) -
             of_real (bernoulli (Suc n)) / (real (Suc n) * s ^ n) +
             integral {0..real N} (\<lambda>x. of_nat n / of_nat (Suc n) * 
                (of_real (pbernpoly (Suc n) x) / (of_real x + s) ^ Suc n)))
           \<longlonglongrightarrow> 0 - of_real (bernoulli (Suc n)) / (of_nat (Suc n) * s ^ n) +
                   of_nat n / of_nat (Suc n) * stirling_integral (Suc n) s" (is "?f \<longlonglongrightarrow> _")
    unfolding stirling_integral_def integral_mult_right
    using convergent_stirling_integral[of "Suc n"] assms s
    by (intro tendsto_intros pbernpoly_over_power_tendsto_0)
       (auto simp: convergent_LIMSEQ_iff simp del: of_nat_Suc)
  also have "?this \<longleftrightarrow> (\<lambda>N. integral {0..real N} 
               (\<lambda>x. of_real (pbernpoly n x) / (of_real x + s) ^ n)) \<longlonglongrightarrow>
               of_nat n / of_nat (Suc n) * stirling_integral (Suc n) s -
                 of_real (bernoulli (Suc n)) / (of_nat (Suc n) * s ^ n)" 
    using eventually_gt_at_top[of "0::nat"] pbernpoly_integral_conv_pbernpoly_integral_Suc[of n] 
          assms unfolding integral_mult_right
    by (intro filterlim_cong refl) (auto elim!: eventually_mono simp del: power_Suc)
  finally show ?thesis unfolding stirling_integral_def[of n] by (rule limI)
qed

lemma stirling_integral_1_unfold:
  assumes "m > 0"
  shows   "stirling_integral 1 s = stirling_integral m s / of_nat m - 
             (\<Sum>k=1..<m. of_real (bernoulli (Suc k)) / (of_nat k * of_nat (Suc k) * s ^ k))"
proof -
  have "stirling_integral 1 s = stirling_integral (Suc m) s / of_nat (Suc m) -
          (\<Sum>k=1..<Suc m. of_real (bernoulli (Suc k)) / (of_nat k * of_nat (Suc k) * s ^ k))" for m
  proof (induction m)
    case (Suc m)
    let ?C = "(\<Sum>k = 1..<Suc m. of_real (bernoulli (Suc k)) / (of_nat k * of_nat (Suc k) * s ^ k))"
    note Suc.IH
    also have "stirling_integral (Suc m) s / of_nat (Suc m) = 
                 stirling_integral (Suc (Suc m)) s / of_nat (Suc (Suc m)) -
                 of_real (bernoulli (Suc (Suc m))) / 
                   (of_nat (Suc m) * of_nat (Suc (Suc m)) * s ^ Suc m)"
      (is "_ = ?A - ?B") by (subst stirling_integral_conv_stirling_integral_Suc)
                            (simp_all del: of_nat_Suc power_Suc add: divide_simps)
    also have "?A - ?B - ?C = ?A - (?B + ?C)" by (rule diff_diff_eq)
    also have "?B + ?C = (\<Sum>k = 1..<Suc (Suc m). of_real (bernoulli (Suc k)) /
                             (of_nat k * of_nat (Suc k) * s ^ k))" 
      using s by (simp add: divide_simps)
    finally show ?case .
  qed simp_all
  note this[of "m - 1"]
  also from assms have "Suc (m - 1) = m" by simp
  finally show ?thesis .
qed
  
lemma ln_Gamma_stirling_complex:
  assumes "m > 0"
  shows   "ln_Gamma s = (s - 1 / 2) * ln s - s + ln (2 * pi) / 2 +
             (\<Sum>k=1..<m. of_real (bernoulli (Suc k)) / (of_nat k * of_nat (Suc k) * s ^ k)) - 
             stirling_integral m s / of_nat m"
proof -
  have "ln_Gamma s = (s - 1 / 2) * ln s - s + ln (2 * pi) / 2 - stirling_integral 1 s"
    using limI[OF integral_pbernpoly_1] by (simp add: stirling_integral_def algebra_simps)
  also have "stirling_integral 1 s = stirling_integral m s / of_nat m -
               (\<Sum>k = 1..<m. of_real (bernoulli (Suc k)) / (of_nat k * of_nat (Suc k) * s ^ k))"
    using assms by (rule stirling_integral_1_unfold)
  finally show ?thesis by simp
qed

lemma LIMSEQ_stirling_integral:
  "n > 0 \<Longrightarrow> (\<lambda>x. integral {0..real x} (\<lambda>x. of_real (pbernpoly n x) / (of_real x + s) ^ n))
     \<longlonglongrightarrow> stirling_integral n s" unfolding stirling_integral_def 
  using convergent_stirling_integral[of n] by (simp only: convergent_LIMSEQ_iff)

end

lemmas has_integral_of_real = has_integral_linear[OF _ bounded_linear_of_real, unfolded o_def]
lemmas integral_of_real = integral_linear[OF _ bounded_linear_of_real, unfolded o_def]

lemma integrable_ln_Gamma_aux_real:
  assumes "0 < s"
  shows   "(\<lambda>x. pbernpoly n x / (x + s) ^ n) integrable_on {0..real N}"
proof -
  have "(\<lambda>x. complex_of_real (pbernpoly n x / (x + s) ^ n)) integrable_on {0..real N}"
    using integrable_ln_Gamma_aux[of "of_real s" n N] assms by simp
  from integrable_linear[OF this bounded_linear_Re] show ?thesis 
    by (simp only: o_def Re_complex_of_real) 
qed
  
lemma  
  assumes "x > 0" "n > 0"
  shows   stirling_integral_complex_of_real:
            "stirling_integral n (complex_of_real x) = of_real (stirling_integral n x)"
    and   LIMSEQ_stirling_integral_real:
            "(\<lambda>N. integral {0..real N} (\<lambda>t. pbernpoly n t / (t + x) ^ n))
            \<longlonglongrightarrow> stirling_integral n x"
    and   stirling_integral_real_convergent:
            "convergent (\<lambda>N. integral {0..real N} (\<lambda>t. pbernpoly n t / (t + x) ^ n))"
proof -
  have "(\<lambda>N. integral {0..real N} (\<lambda>t. of_real (pbernpoly n t / (t + x) ^ n)))
           \<longlonglongrightarrow> stirling_integral n (complex_of_real x)"
    using LIMSEQ_stirling_integral[of "complex_of_real x" n] assms by simp
  hence "(\<lambda>N. of_real (integral {0..real N} (\<lambda>t. pbernpoly n t / (t + x) ^ n)))
           \<longlonglongrightarrow> stirling_integral n (complex_of_real x)"
    using integrable_ln_Gamma_aux_real[OF assms(1), of n] 
    by (subst (asm) integral_of_real) simp
  from tendsto_Re[OF this] 
    have "(\<lambda>N. integral {0..real N} (\<lambda>t. pbernpoly n t / (t + x) ^ n))
           \<longlonglongrightarrow> Re (stirling_integral n (complex_of_real x))" by simp
  thus "convergent (\<lambda>N. integral {0..real N} (\<lambda>t. pbernpoly n t / (t + x) ^ n))"
    by (rule convergentI)
  thus "(\<lambda>N. integral {0..real N} (\<lambda>t. pbernpoly n t / (t + x) ^ n))
          \<longlonglongrightarrow> stirling_integral n x" unfolding stirling_integral_def
    by (simp add: convergent_LIMSEQ_iff)
  from tendsto_of_real[OF this, where 'a = complex] 
       integrable_ln_Gamma_aux_real[OF assms(1), of n]
    have "(\<lambda>xa. integral {0..real xa} 
                    (\<lambda>xa. complex_of_real (pbernpoly n xa) / (complex_of_real xa + x) ^ n))
             \<longlonglongrightarrow> complex_of_real (stirling_integral n x)"
    by (subst (asm) integral_of_real [symmetric]) simp_all
  from LIMSEQ_unique[OF this LIMSEQ_stirling_integral[of "complex_of_real x" n]] assms
    show "stirling_integral n (complex_of_real x) = of_real (stirling_integral n x)" by simp
qed

lemma ln_Gamma_stirling_real:
  assumes "x > (0 :: real)" "m > (0::nat)"
  shows   "ln_Gamma x = (x - 1 / 2) * ln x - x + ln (2 * pi) / 2 +
              (\<Sum>k = 1..<m. bernoulli (Suc k) / (of_nat k * of_nat (Suc k) * x ^ k)) -
              stirling_integral m x / of_nat m"
proof -
  from assms have "complex_of_real (ln_Gamma x) = ln_Gamma (complex_of_real x)"
    by (simp add: ln_Gamma_complex_of_real)
  also have "ln_Gamma (complex_of_real x) = complex_of_real (
                (x - 1 / 2) * ln x - x + ln (2 * pi) / 2 +
                (\<Sum>k = 1..<m. bernoulli (Suc k) / (of_nat k * of_nat (Suc k) * x ^ k)) -
                stirling_integral m x / of_nat m)" using assms
    by (subst ln_Gamma_stirling_complex[of _ m])
       (simp_all add: Ln_of_real stirling_integral_complex_of_real)
  finally show ?thesis by (subst (asm) of_real_eq_iff)
qed


context
begin

private lemma stirling_integral_bound_aux:
  assumes n: "n > (1::nat)"
  obtains c where "\<And>s. Re s > 0 \<Longrightarrow> norm (stirling_integral n s) \<le>  c / Re s ^ (n - 1)"
proof -
  obtain c where c: "norm (pbernpoly n x) \<le> c" for x by (rule bounded_pbernpoly[of n]) blast
  have c': "pbernpoly n x \<le> c" for x using c[of x] by (simp add: abs_real_def split: if_splits)
  from c[of 0] have c_nonneg: "c \<ge> 0" by simp
  have "norm (stirling_integral n s) \<le> c / (real n - 1) / Re s ^ (n - 1)" if s: "Re s > 0" for s
  proof (rule Lim_norm_ubound[OF _ LIMSEQ_stirling_integral])
    have pos: "x + norm s > 0" if "x \<ge> 0" for x using s that by (intro add_nonneg_pos) auto
    have nz: "of_real x + s \<noteq> 0" if "x \<ge> 0" for x using s that by (auto simp: complex_eq_iff)
    let ?bound = "\<lambda>N. c / (Re s ^ (n - 1) * (real n - 1)) - 
                        c / ((real N + Re s) ^ (n - 1) * (real n - 1))"
    show "eventually (\<lambda>N. norm (integral {0..real N} 
              (\<lambda>x. of_real (pbernpoly n x) / (of_real x + s) ^ n)) \<le> 
            c / (real n - 1) / Re s ^ (n - 1)) at_top"
      using eventually_gt_at_top[of "0::nat"]
    proof eventually_elim
      case (elim N)
      let ?F = "\<lambda>x. -c / ((x + Re s) ^ (n - 1) * (real n - 1))"
      from n s have "((\<lambda>x. c / (x + Re s) ^ n) has_integral (?F (real N) - ?F 0)) {0..real N}"
        by (intro fundamental_theorem_of_calculus)
           (auto intro!: derivative_eq_intros simp: divide_simps power_diff add_eq_0_iff2
                   has_field_derivative_iff_has_vector_derivative [symmetric])      
      also have "?F (real N) - ?F 0 = ?bound N" by simp
      finally have *: "((\<lambda>x. c / (x + Re s) ^ n) has_integral ?bound N) {0..real N}" .
      have "norm (integral {0..real N} (\<lambda>x. of_real (pbernpoly n x) / (of_real x + s) ^ n)) \<le>
              integral {0..real N} (\<lambda>x. c / (x + Re s) ^ n)"
      proof (intro integral_norm_bound_integral integrable_ln_Gamma_aux s ballI)
        fix x assume x: "x \<in> {0..real N}"
        have "norm (of_real (pbernpoly n x) / (of_real x + s) ^ n) \<le> c / norm (of_real x + s) ^ n"
          unfolding norm_divide norm_power using c by (intro divide_right_mono) simp_all
        also have "\<dots> \<le> c / (x + Re s) ^ n" 
          using x c c_nonneg s nz[of x] complex_Re_le_cmod[of "of_real x + s"]
          by (intro divide_left_mono power_mono mult_pos_pos zero_less_power add_nonneg_pos) auto
        finally show "norm (of_real (pbernpoly n x) / (of_real x + s) ^ n) \<le> \<dots>" .
      qed (insert n s * pos nz c, auto)
      also have "\<dots> = ?bound N" using * by (simp add: has_integral_iff)
      also have "\<dots> \<le> c / (Re s ^ (n - 1) * (real n - 1))" using c_nonneg elim s n by simp
      also have "\<dots> = c / (real n - 1) / (Re s ^ (n - 1))" by simp
      finally show "norm (integral {0..real N} (\<lambda>x. of_real (pbernpoly n x) /
                      (of_real x + s) ^ n)) \<le> c / (real n - 1) / Re s ^ (n - 1)" .
    qed
  qed (insert s n, simp_all)
  thus ?thesis by (rule that)
qed

lemma stirling_integral_bound:
  assumes "n > 0"
  obtains c where 
    "\<And>s. Re s > 0 \<Longrightarrow> norm (stirling_integral n s) \<le> c / Re s ^ n"
proof -
  let ?f = "\<lambda>s. of_nat n / of_nat (Suc n) * stirling_integral (Suc n) s -
                  of_real (bernoulli (Suc n)) / (of_nat (Suc n) * s ^ n)"
  from stirling_integral_bound_aux[of "Suc n"] assms obtain c where 
    c: "\<And>s. Re s > 0 \<Longrightarrow> norm (stirling_integral (Suc n) s) \<le> c / Re s ^ n" by auto
  define c1 where "c1 = real n / real (Suc n) * c"
  define c2 where "c2 = \<bar>bernoulli (Suc n)\<bar> / real (Suc n)"
  have c2_nonneg: "c2 \<ge> 0" by (simp add: c2_def)
  show ?thesis
  proof (rule that)
    fix s :: complex assume s: "Re s > 0"
    have "stirling_integral n s = ?f s" using s assms 
      by (rule stirling_integral_conv_stirling_integral_Suc)
    also have "norm \<dots> \<le> norm (of_nat n / of_nat (Suc n) * stirling_integral (Suc n) s) +
                           norm (of_real (bernoulli (Suc n)) / (of_nat (Suc n) * s ^ n))"
      by (rule norm_triangle_ineq4)
    also have "\<dots> = real n / real (Suc n) * norm (stirling_integral (Suc n) s) +
                      c2 / norm s ^ n" (is "_ = ?A + ?B")
      by (simp add: norm_divide norm_mult norm_power c2_def field_simps del: of_nat_Suc)
    also have "?A \<le> real n / real (Suc n) * (c / Re s ^ n)"
      by (intro mult_left_mono c s) simp_all
    also have "\<dots> = c1 / Re s ^ n" by (simp add: c1_def)
    also have "c2 / norm s ^ n \<le> c2 / Re s ^ n" using s c2_nonneg
      by (intro divide_left_mono power_mono complex_Re_le_cmod mult_pos_pos zero_less_power) auto
    also have "c1 / Re s ^ n + c2 / Re s ^ n = (c1 + c2) / Re s ^ n" 
      using s by (simp add: field_simps)
    finally show "norm (stirling_integral n s) \<le> (c1 + c2) / Re s ^ n" by - simp_all
  qed
qed

end


lemma stirling_integral_holomorphic [holomorphic_intros]:
  assumes m: "m > 0" and "\<forall>s\<in>A. Re s > 0"
  shows   "stirling_integral m holomorphic_on A"  
proof -
  let ?f = "\<lambda>s::complex. of_nat m * ((s - 1 / 2) * Ln s - s + of_real (ln (2 * pi) / 2) +
          (\<Sum>k=1..<m. of_real (bernoulli (Suc k)) / (of_nat k * of_nat (Suc k) * s ^ k)) - 
          ln_Gamma s)"
  have "?f holomorphic_on A" using assms
    by (auto intro!: holomorphic_intros simp del: of_nat_Suc elim!: nonpos_Reals_cases)
  also have "?this \<longleftrightarrow> stirling_integral m holomorphic_on A" 
    using assms by (intro holomorphic_cong refl) 
                   (simp_all add: field_simps ln_Gamma_stirling_complex)
  finally show "stirling_integral m holomorphic_on A" .
qed

lemma stirling_integral_continuous_on [continuous_intros]:
  assumes m: "m > 0" and "\<forall>s\<in>A. Re s > 0"
  shows   "continuous_on A (stirling_integral m)"
  by (intro holomorphic_on_imp_continuous_on stirling_integral_holomorphic assms)
    
lemma has_field_derivative_stirling_integral:
  assumes "Re x > 0" "n > 0"
  shows   "(stirling_integral n has_field_derivative deriv (stirling_integral n) x) (at x)"
  using assms 
  by (intro holomorphic_derivI[OF stirling_integral_holomorphic, of n  "{s. Re s > 0}"] 
        open_halfspace_Re_gt) auto


 
lemma
  assumes n: "n > 0" and "x > 0"
  shows   deriv_stirling_integral_complex_of_real:
            "(deriv ^^ j) (stirling_integral n) (complex_of_real x) =
               complex_of_real ((deriv ^^ j) (stirling_integral n) x)" (is "?lhs x = ?rhs x")
  and     differentiable_stirling_integral_real:
            "(deriv ^^ j) (stirling_integral n) field_differentiable at x" (is ?thesis2)
proof -
  let ?A = "{s. Re s > 0}"
  let ?f = "\<lambda>j x. (deriv ^^ j) (stirling_integral n) (complex_of_real x)"
  let ?f' = "\<lambda>j x. complex_of_real ((deriv ^^ j) (stirling_integral n) x)"
    
  have [simp]: "open ?A" by (simp add: open_halfspace_Re_gt)      

  have "?lhs x = ?rhs x \<and> (deriv ^^ j) (stirling_integral n) field_differentiable at x" 
    if "x > 0" for x using that
  proof (induction j arbitrary: x)
    case 0
    have "((\<lambda>x. Re (stirling_integral n (of_real x))) has_field_derivative 
                  Re (deriv (\<lambda>x. stirling_integral n x) (of_real x))) (at x)" using 0 n
      by (auto intro!: derivative_intros has_vector_derivative_real_field
                 field_differentiable_derivI holomorphic_on_imp_differentiable_at[of _ ?A]
                 stirling_integral_holomorphic)
    also have "?this \<longleftrightarrow> (stirling_integral n has_field_derivative 
             Re (deriv (\<lambda>x. stirling_integral n x) (of_real x))) (at x)"
      using eventually_nhds_in_open[of "{0<..}" x] 0 n
      by (intro has_field_derivative_cong_ev refl) 
         (auto elim!: eventually_mono simp: stirling_integral_complex_of_real)
    finally have "stirling_integral n field_differentiable at x"
      by (auto simp: field_differentiable_def)
    with 0 n show ?case by (auto simp: stirling_integral_complex_of_real)
  next
    case (Suc j x)
    note IH = conjunct1[OF Suc.IH] conjunct2[OF Suc.IH]
    have *: "(deriv ^^ Suc j) (stirling_integral n) (complex_of_real x) =
                 of_real ((deriv ^^ Suc j) (stirling_integral n) x)" if x: "x > 0" for x
    proof -
      have "deriv ((deriv ^^ j) (stirling_integral n)) (complex_of_real x) =
              vector_derivative (\<lambda>x. (deriv ^^ j) (stirling_integral n) (of_real x)) (at x)"
        using n x
        by (intro vector_derivative_of_real_right [symmetric] 
                   holomorphic_on_imp_differentiable_at[of _ ?A] holomorphic_higher_deriv
                   stirling_integral_holomorphic) auto
      also have "\<dots> = vector_derivative (\<lambda>x. of_real ((deriv ^^ j) (stirling_integral n) x)) (at x)"
        using eventually_nhds_in_open[of "{0<..}" x] x
        by (intro vector_derivative_cong_eq) (auto elim!: eventually_mono simp: IH(1))
      also have "\<dots> = of_real (deriv ((deriv ^^ j) (stirling_integral n)) x)"
        by (intro vector_derivative_of_real_left holomorphic_on_imp_differentiable_at[of _ ?A]
              field_differentiable_imp_differentiable IH(2) x)
      finally show ?thesis by simp
    qed
    have "((\<lambda>x. Re ((deriv ^^ Suc j) (stirling_integral n) (of_real x))) has_field_derivative 
             Re (deriv ((deriv ^^ Suc j) (stirling_integral n)) (of_real x))) (at x)"
      using Suc.prems n
      by (intro derivative_intros has_vector_derivative_real_field field_differentiable_derivI
                holomorphic_on_imp_differentiable_at[of _ ?A] stirling_integral_holomorphic
                holomorphic_higher_deriv) auto
    also have "?this \<longleftrightarrow> ((deriv ^^ Suc j) (stirling_integral n) has_field_derivative 
                  Re (deriv ((deriv ^^ Suc j) (stirling_integral n)) (of_real x))) (at x)"  
      using eventually_nhds_in_open[of "{0<..}" x] Suc.prems *
      by (intro has_field_derivative_cong_ev refl) (auto elim!: eventually_mono)
    finally have "(deriv ^^ Suc j) (stirling_integral n) field_differentiable at x"
      by (auto simp: field_differentiable_def)
    with *[OF Suc.prems] show ?case by blast
  qed
  from this[OF assms(2)] show "?lhs x = ?rhs x" ?thesis2 by blast+
qed

text \<open>
  Unfortunately, asymptotic power series cannot, in general, be differentiated. However, since 
  @{term ln_Gamma} is holomorphic on the entire positive real half-space, we can differentiate 
  its asymptotic expansion after all.

  To do this, we use an ad-hoc version of the more general approach outlined in Erdelyi's
  ``Asymptotic Expansions'' for holomorphic functions: We bound the value of the $j$-th derivative 
  of the remainder term at some value $x$ by applying Cauchy's integral formula along a circle 
  centred at $x$ with radius $\frac{1}{2} x$.
\<close>
lemma deriv_stirling_integral_real_bound:
  assumes m: "m > 0"
  shows   "(deriv ^^ j) (stirling_integral m) \<in> O(\<lambda>x::real. 1 / x ^ (m + j))"
proof -
  from stirling_integral_bound[OF m] guess c . note c = this
  have "0 \<le> cmod (stirling_integral m 1)" by simp
  also have "\<dots> \<le> c" using c[of 1] by simp
  finally have c_nonneg: "c \<ge> 0" .
  define B where "B = c * 2 ^ (m + Suc j)"
  define B' where "B' = B * fact j / 2"

  have "eventually (\<lambda>x::real. norm ((deriv ^^ j) (stirling_integral m) x) \<le> 
          B' * norm (1 / x ^ (m+ j))) at_top"
    using eventually_gt_at_top[of "0::real"]
  proof eventually_elim
    case (elim x)
    have "Re s > 0" if "s \<in> cball (of_real x) (x/2)" for s :: complex
    proof -
      have "x - Re s \<le> norm (of_real x - s)" using complex_Re_le_cmod[of "of_real x - s"] by simp
      also from that have "\<dots> \<le> x/2" by (simp add: dist_complex_def)
      finally show ?thesis using elim by simp
    qed
    hence "((\<lambda>u. stirling_integral m u / (u - of_real x) ^ Suc j) has_contour_integral
            complex_of_real (2 * pi) * \<i> / fact j * 
              (deriv ^^ j) (stirling_integral m) (of_real x)) (circlepath (of_real x) (x/2))"
      using m elim
      by (intro Cauchy_has_contour_integral_higher_derivative_circlepath 
                stirling_integral_continuous_on stirling_integral_holomorphic) auto
    hence "norm (of_real (2 * pi) * \<i> / fact j * (deriv ^^ j) (stirling_integral m) (of_real x)) \<le>
            B / x ^ (m + Suc j) * (2 * pi * (x / 2))"
    proof (rule has_contour_integral_bound_circlepath)
      fix u :: complex assume dist: "norm (u - of_real x) = x / 2"
      have "Re (of_real x - u) \<le> norm (of_real x - u)" by (rule complex_Re_le_cmod)
      also have "\<dots> = x / 2" using dist by (simp add: norm_minus_commute)
      finally have Re_u: "Re u \<ge> x/2" using elim by simp
      have "norm (stirling_integral m u / (u - of_real x) ^ Suc j) \<le> 
              c / Re u ^ m / (x / 2) ^ Suc j" using Re_u elim
        unfolding norm_divide norm_power dist
        by (intro divide_right_mono zero_le_power c) simp_all
      also have "\<dots> \<le> c / (x/2) ^ m / (x / 2) ^ Suc j" using c_nonneg elim Re_u
        by (intro divide_right_mono divide_left_mono power_mono) simp_all
      also have "\<dots> = B / x ^ (m + Suc j)" using elim by (simp add: B_def field_simps power_add)
      finally show "norm (stirling_integral m u / (u - of_real x) ^ Suc j) \<le> B / x ^ (m + Suc j)" .
    qed (insert elim c_nonneg, auto simp: B_def simp del: power_Suc)
    hence "cmod ((deriv ^^ j) (stirling_integral m) (of_real x)) \<le> B' / x ^ (j + m)"
      using elim by (simp add: field_simps norm_divide norm_mult norm_power B'_def)
    with elim m show ?case by (simp_all add: add_ac deriv_stirling_integral_complex_of_real)
  qed
  thus ?thesis by (rule bigoI)
qed

definition stirling_sum where
  "stirling_sum j m x = 
     (-1) ^ j * (\<Sum>k = 1..<m. (of_real (bernoulli (Suc k)) * pochhammer (of_nat k) j / (of_nat k *
                                 of_nat (Suc k))) * inverse x ^ (k + j))"
  
definition stirling_sum' where
  "stirling_sum' j m x = 
     (-1) ^ (Suc j) * (\<Sum>k\<le>m. (of_real (bernoulli' k) * 
       pochhammer (of_nat (Suc k)) (j - 1) * inverse x ^ (k + j)))"

lemma stirling_sum_complex_of_real:
  "stirling_sum j m (complex_of_real x) = complex_of_real (stirling_sum j m x)"
  by (simp add: stirling_sum_def pochhammer_of_real [symmetric] del: of_nat_Suc)

lemma stirling_sum'_complex_of_real:
  "stirling_sum' j m (complex_of_real x) = complex_of_real (stirling_sum' j m x)"
  by (simp add: stirling_sum'_def pochhammer_of_real [symmetric] del: of_nat_Suc)

lemma has_field_derivative_stirling_sum_complex [derivative_intros]:
  "Re x > 0 \<Longrightarrow> (stirling_sum j m has_field_derivative stirling_sum (Suc j) m x) (at x)"
    unfolding stirling_sum_def [abs_def] sum_distrib_left
    by (rule DERIV_sum) (auto intro!: derivative_eq_intros simp del: of_nat_Suc 
                              simp: pochhammer_Suc power_diff)

lemma has_field_derivative_stirling_sum_real [derivative_intros]:
  "x > (0::real) \<Longrightarrow> (stirling_sum j m has_field_derivative stirling_sum (Suc j) m x) (at x)"
    unfolding stirling_sum_def [abs_def] sum_distrib_left
    by (rule DERIV_sum) (auto intro!: derivative_eq_intros simp del: of_nat_Suc 
                              simp: pochhammer_Suc power_diff)

lemma has_field_derivative_stirling_sum'_complex [derivative_intros]:
  assumes "j > 0" "Re x > 0"
  shows   "(stirling_sum' j m has_field_derivative stirling_sum' (Suc j) m x) (at x)"
proof (cases j)
  case (Suc j')
  from assms have [simp]: "x \<noteq> 0" by auto
  define c where "c = (\<lambda>n. (-1) ^ Suc j * complex_of_real (bernoulli' n) * 
                          pochhammer (of_nat (Suc n)) j')"
  define T where "T = (\<lambda>n x. c n * inverse x ^ (j + n))"
  define T' where "T' = (\<lambda>n x. - (of_nat (j + n)) * c n * inverse x ^ (Suc (j + n)))"
  have "((\<lambda>x. \<Sum>k\<le>m. T k x) has_field_derivative (\<Sum>k\<le>m. T' k x)) (at x)" using assms Suc
    by (intro DERIV_sum)
       (auto simp: T_def T'_def intro!: derivative_eq_intros 
             simp: field_simps power_add [symmetric]  simp del: of_nat_Suc power_Suc of_nat_add)
  also have "(\<lambda>x. (\<Sum>k\<le>m. T k x)) = stirling_sum' j m"
    by (simp add: Suc T_def c_def stirling_sum'_def fun_eq_iff add_ac mult.assoc sum_distrib_left)
  also have "(\<Sum>k\<le>m. T' k x) = stirling_sum' (Suc j) m x"
    by (simp add: T'_def c_def Suc stirling_sum'_def sum_distrib_left 
          sum_distrib_right algebra_simps pochhammer_Suc)
  finally show ?thesis .
qed (insert assms, simp_all)
  
lemma has_field_derivative_stirling_sum'_real [derivative_intros]:
  assumes "j > 0" "x > (0::real)"
  shows   "(stirling_sum' j m has_field_derivative stirling_sum' (Suc j) m x) (at x)"
proof (cases j)
  case (Suc j')
  from assms have [simp]: "x \<noteq> 0" by auto
  define c where "c = (\<lambda>n. (-1) ^ Suc j * (bernoulli' n) * pochhammer (of_nat (Suc n)) j')"
  define T where "T = (\<lambda>n x. c n * inverse x ^ (j + n))"
  define T' where "T' = (\<lambda>n x. - (of_nat (j + n)) * c n * inverse x ^ (Suc (j + n)))"
  have "((\<lambda>x. \<Sum>k\<le>m. T k x) has_field_derivative (\<Sum>k\<le>m. T' k x)) (at x)" using assms Suc
    by (intro DERIV_sum)
       (auto simp: T_def T'_def intro!: derivative_eq_intros 
             simp: field_simps power_add [symmetric]  simp del: of_nat_Suc power_Suc of_nat_add)
  also have "(\<lambda>x. (\<Sum>k\<le>m. T k x)) = stirling_sum' j m"
    by (simp add: Suc T_def c_def stirling_sum'_def fun_eq_iff add_ac mult.assoc sum_distrib_left)
  also have "(\<Sum>k\<le>m. T' k x) = stirling_sum' (Suc j) m x"
    by (simp add: T'_def c_def Suc stirling_sum'_def sum_distrib_left 
          sum_distrib_right algebra_simps pochhammer_Suc)
  finally show ?thesis .
qed (insert assms, simp_all)

lemma higher_deriv_stirling_sum_complex:
  "Re x > 0 \<Longrightarrow> (deriv ^^ i) (stirling_sum j m) x = stirling_sum (i + j) m x"
proof (induction i arbitrary: x)
  case (Suc i)
  have "deriv ((deriv ^^ i) (stirling_sum j m)) x = deriv (stirling_sum (i + j) m) x"
    using eventually_nhds_in_open[of "{x. Re x > 0}" x] Suc.prems
    by (intro deriv_cong_ev refl) (auto elim!: eventually_mono simp: open_halfspace_Re_gt Suc.IH)
  also from Suc.prems have "\<dots> = stirling_sum (Suc (i + j)) m x"
    by (intro DERIV_imp_deriv has_field_derivative_stirling_sum_complex)
  finally show ?case by simp
qed simp_all
  

definition Polygamma_approx :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a :: {real_normed_field, ln}" where
  "Polygamma_approx j m = 
     (deriv ^^ j) (\<lambda>x. (x - 1 / 2) * ln x - x + of_real (ln (2 * pi)) / 2 + stirling_sum 0 m x)"
  
lemma Polygamma_approx_Suc: "Polygamma_approx (Suc j) m = deriv (Polygamma_approx j m)"
  by (simp add: Polygamma_approx_def)  

lemma Polygamma_approx_0: 
  "Polygamma_approx 0 m x = (x - 1/2) * ln x - x + of_real (ln (2*pi)) / 2 + stirling_sum 0 m x"
  by (simp add: Polygamma_approx_def)
    
lemma Polygamma_approx_1_complex: 
  "Re x > 0 \<Longrightarrow> 
     Polygamma_approx (Suc 0) m x = ln x - 1 / (2*x) + stirling_sum (Suc 0) m x"
  unfolding Polygamma_approx_Suc Polygamma_approx_0
  by (intro DERIV_imp_deriv) 
     (auto intro!: derivative_eq_intros elim!: nonpos_Reals_cases simp: field_simps)
     
lemma Polygamma_approx_1_real: 
  "x > (0 :: real) \<Longrightarrow> 
     Polygamma_approx (Suc 0) m x = ln x - 1 / (2*x) + stirling_sum (Suc 0) m x"
  unfolding Polygamma_approx_Suc Polygamma_approx_0
  by (intro DERIV_imp_deriv) 
     (auto intro!: derivative_eq_intros elim!: nonpos_Reals_cases simp: field_simps)
 
lemma stirling_sum_2_conv_stirling_sum'_1:
  fixes x :: "'a :: {real_div_algebra, field_char_0}"
  assumes "m > 0" "x \<noteq> 0"
  shows   "stirling_sum' 1 m x = 1 / x + 1 / (2 * x^2) + stirling_sum 2 m x"
proof -
  have pochhammer_2: "pochhammer (of_nat k) 2 = of_nat k * of_nat (Suc k)" for k 
    by (simp add: pochhammer_Suc eval_nat_numeral add_ac)
  have "stirling_sum 2 m x = 
          (\<Sum>k = Suc 0..<m. of_real (bernoulli' (Suc k)) * inverse x ^ Suc (Suc k))"
    unfolding stirling_sum_def pochhammer_2 power2_minus power_one mult_1_left
    by (intro sum.cong refl)
       (simp_all add: stirling_sum_def pochhammer_2 power2_eq_square divide_simps bernoulli'_def
                 del: of_nat_Suc power_Suc)
  also have "1 / (2 * x^2) + \<dots> = 
               (\<Sum>k=0..<m. of_real (bernoulli' (Suc k)) * inverse x ^ Suc (Suc k))" using assms
    by (subst (2) sum.atLeast_Suc_lessThan) (simp_all add: power2_eq_square field_simps)
  also have "1 / x + \<dots> = (\<Sum>k=0..<Suc m. of_real (bernoulli' k) * inverse x ^ Suc k)"
    by (subst sum.atLeast0_lessThan_Suc_shift) (simp_all add: bernoulli'_def divide_simps)
  also have "\<dots> = (\<Sum>k\<le>m. of_real (bernoulli' k) * inverse x ^ Suc k)"
    by (intro sum.cong) auto
  also have "\<dots> = stirling_sum' 1 m x" by (simp add: stirling_sum'_def)
  finally show ?thesis by (simp add: add_ac)
qed

lemma Polygamma_approx_2_real: 
  assumes "x > (0::real)" "m > 0"
  shows   "Polygamma_approx (Suc (Suc 0)) m x = stirling_sum' 1 m x"
proof -
  have "Polygamma_approx (Suc (Suc 0)) m x = deriv (Polygamma_approx (Suc 0) m) x" 
    by (simp add: Polygamma_approx_Suc)
  also have "\<dots> = deriv (\<lambda>x. ln x - 1 / (2*x) + stirling_sum (Suc 0) m x) x"
    using eventually_nhds_in_open[of "{0<..}" x] assms
    by (intro deriv_cong_ev) (auto elim!: eventually_mono simp: Polygamma_approx_1_real)
  also have "\<dots> = 1 / x + 1 / (2*x^2) + stirling_sum (Suc (Suc 0)) m x" using assms
    by (intro DERIV_imp_deriv) (auto intro!: derivative_eq_intros 
           elim!: nonpos_Reals_cases simp: field_simps power2_eq_square)
  also have "\<dots> = stirling_sum' 1 m x" using stirling_sum_2_conv_stirling_sum'_1[of m x] assms
    by (simp add: eval_nat_numeral)
  finally show ?thesis .
qed
  
lemma Polygamma_approx_2_complex: 
  assumes "Re x > 0" "m > 0"
  shows   "Polygamma_approx (Suc (Suc 0)) m x = stirling_sum' 1 m x"
proof -
  have "Polygamma_approx (Suc (Suc 0)) m x = deriv (Polygamma_approx (Suc 0) m) x" 
    by (simp add: Polygamma_approx_Suc)
  also have "\<dots> = deriv (\<lambda>x. ln x - 1 / (2*x) + stirling_sum (Suc 0) m x) x"
    using eventually_nhds_in_open[of "{s. Re s > 0}" x] assms
    by (intro deriv_cong_ev)
       (auto simp: open_halfspace_Re_gt elim!: eventually_mono simp: Polygamma_approx_1_complex)
  also have "\<dots> = 1 / x + 1 / (2*x^2) + stirling_sum (Suc (Suc 0)) m x" using assms
    by (intro DERIV_imp_deriv) (auto intro!: derivative_eq_intros 
           elim!: nonpos_Reals_cases simp: field_simps power2_eq_square)
  also have "\<dots> = stirling_sum' 1 m x" using stirling_sum_2_conv_stirling_sum'_1[of m x] assms
      by (subst stirling_sum_2_conv_stirling_sum'_1) (auto simp: eval_nat_numeral)
  finally show ?thesis .
qed
  
lemma Polygamma_approx_ge_2_real: 
  assumes "x > (0::real)" "m > 0"
  shows   "Polygamma_approx (Suc (Suc j)) m x = stirling_sum' (Suc j) m x"
using assms(1)
proof (induction j arbitrary: x)
  case (0 x)
  with assms show ?case by (simp add: Polygamma_approx_2_real)
next
  case (Suc j x)
  have "Polygamma_approx (Suc (Suc (Suc j))) m x = deriv (Polygamma_approx (Suc (Suc j)) m) x"
    by (simp add: Polygamma_approx_Suc)
  also have "\<dots> = deriv (stirling_sum' (Suc j) m) x"
    using eventually_nhds_in_open[of "{0<..}" x] Suc.prems
    by (intro deriv_cong_ev refl) (auto elim!: eventually_mono simp: Suc.IH)
  also have "\<dots> = stirling_sum' (Suc (Suc j)) m x" using Suc.prems
    by (intro DERIV_imp_deriv derivative_intros) simp_all
  finally show ?case .
qed
  
lemma Polygamma_approx_ge_2_complex:
  assumes "Re x > 0" "m > 0"
  shows   "Polygamma_approx (Suc (Suc j)) m x = stirling_sum' (Suc j) m x"
using assms(1)
proof (induction j arbitrary: x)
  case (0 x)
  with assms show ?case by (simp add: Polygamma_approx_2_complex)
next
  case (Suc j x)
  have "Polygamma_approx (Suc (Suc (Suc j))) m x = deriv (Polygamma_approx (Suc (Suc j)) m) x"
    by (simp add: Polygamma_approx_Suc)
  also have "\<dots> = deriv (stirling_sum' (Suc j) m) x"
    using eventually_nhds_in_open[of "{x. Re x > 0}" x] Suc.prems
    by (intro deriv_cong_ev refl) (auto elim!: eventually_mono simp: Suc.IH open_halfspace_Re_gt)
  also have "\<dots> = stirling_sum' (Suc (Suc j)) m x" using Suc.prems
    by (intro DERIV_imp_deriv derivative_intros) simp_all
  finally show ?case .
qed

lemma Polygamma_approx_complex_of_real:
  assumes "x > 0" "m > 0"
  shows   "Polygamma_approx j m (complex_of_real x) = of_real (Polygamma_approx j m x)"
proof (cases j)
  case 0
  with assms show ?thesis by (simp add: Polygamma_approx_0 Ln_of_real stirling_sum_complex_of_real)
next
  case [simp]: (Suc j')
  thus ?thesis
  proof (cases j')
    case 0
    with assms show ?thesis 
      by (simp add: Polygamma_approx_1_complex 
                    Polygamma_approx_1_real stirling_sum_complex_of_real Ln_of_real)
  next
    case (Suc j'')
    with assms show ?thesis
      by (simp add: Polygamma_approx_ge_2_complex Polygamma_approx_ge_2_real 
                    stirling_sum'_complex_of_real)
  qed
qed
  
lemma higher_deriv_Polygamma_approx [simp]: 
  "(deriv ^^ j) (Polygamma_approx i m) = Polygamma_approx (j + i) m"
  by (simp add: Polygamma_approx_def funpow_add)
  
lemma stirling_sum_holomorphic [holomorphic_intros]:
  "0 \<notin> A \<Longrightarrow> stirling_sum j m holomorphic_on A"
  unfolding stirling_sum_def by (intro holomorphic_intros) auto
  
lemma Polygamma_approx_holomorphic [holomorphic_intros]:
  "Polygamma_approx j m holomorphic_on {s. Re s > 0}"
  unfolding Polygamma_approx_def
  by (intro holomorphic_intros) (auto simp: open_halfspace_Re_gt elim!: nonpos_Reals_cases)
  
lemma higher_deriv_lnGamma_stirling:
  assumes m: "m > 0"
  shows   "(\<lambda>x::real. (deriv ^^ j) ln_Gamma x - Polygamma_approx j m x) \<in> O(\<lambda>x. 1 / x ^ (m + j))"
proof -
  have "eventually (\<lambda>x. \<bar>(deriv ^^ j) ln_Gamma x - Polygamma_approx j m x\<bar> =
                          inverse (real m) * \<bar>(deriv ^^ j) (stirling_integral m) x\<bar>) at_top"
    using eventually_gt_at_top[of "0::real"]
  proof eventually_elim
    case (elim x)
    note x = this
    have "(deriv ^^ j) (\<lambda>x. ln_Gamma x - Polygamma_approx 0 m x) (complex_of_real x) =
            (deriv ^^ j) (\<lambda>x. (-inverse (of_nat m)) * stirling_integral m x) (complex_of_real x)"
      using eventually_nhds_in_open[of "{s. Re s > 0}" x] x m
      by (intro higher_deriv_cong_ev refl)
         (auto elim!: eventually_mono simp: ln_Gamma_stirling_complex Polygamma_approx_def 
            field_simps open_halfspace_Re_gt stirling_sum_def)
    also have "\<dots> = - inverse (of_nat m) * (deriv ^^ j) (stirling_integral m) (of_real x)" using x m
      by (intro higher_deriv_cmult[of _ "{s. Re s > 0}"] stirling_integral_holomorphic)
         (auto simp: open_halfspace_Re_gt)
    also have "(deriv ^^ j) (\<lambda>x. ln_Gamma x - Polygamma_approx 0 m x) (complex_of_real x) = 
                 (deriv ^^ j) ln_Gamma (of_real x) - (deriv ^^ j) (Polygamma_approx 0 m) (of_real x)"
      using x 
      by (intro higher_deriv_diff[of _ "{s. Re s > 0}"])
         (auto intro!: holomorphic_intros elim!: nonpos_Reals_cases simp: open_halfspace_Re_gt)
    also have "(deriv ^^ j) (Polygamma_approx 0 m) (complex_of_real x) =
                 of_real (Polygamma_approx j m x)" using x m
      by (simp add: Polygamma_approx_complex_of_real)
    also have "norm (- inverse (of_nat m) * (deriv ^^ j) (stirling_integral m) (complex_of_real x)) = 
                 inverse (real m) * \<bar>(deriv ^^ j) (stirling_integral m) x\<bar>"
      using x m by (simp add: norm_mult norm_inverse deriv_stirling_integral_complex_of_real)
    also have "(deriv ^^ j) ln_Gamma (complex_of_real x) = of_real ((deriv ^^ j) ln_Gamma x)" using x
      by (simp add: higher_deriv_ln_Gamma_complex_of_real)
    also have "norm (\<dots> - of_real (Polygamma_approx j m x)) = 
                 \<bar>(deriv ^^ j) ln_Gamma x - Polygamma_approx j m x\<bar>"
      by (simp only: of_real_diff [symmetric] norm_of_real)
    finally show ?case .
  qed
  from bigthetaI_cong[OF this] m
    have "(\<lambda>x::real. (deriv ^^ j) ln_Gamma x - Polygamma_approx j m x) \<in> 
             \<Theta>(\<lambda>x. (deriv ^^ j) (stirling_integral m) x)" by simp
  also have "(\<lambda>x::real. (deriv ^^ j) (stirling_integral m) x) \<in> O(\<lambda>x. 1 / x ^ (m + j))" using m
      by (rule deriv_stirling_integral_real_bound)
  finally show ?thesis .
qed

lemma Polygamma_approx_1_real':
  assumes x: "(x::real) > 0" and m: "m > 0"
  shows   "Polygamma_approx 1 m x = ln x - (\<Sum>k = Suc 0..m. bernoulli' k * inverse x ^ k / real k)"
proof -
  have "Polygamma_approx 1 m x = ln x - (1 / (2 * x) + 
          (\<Sum>k=Suc 0..<m. bernoulli (Suc k) * inverse x ^ Suc k / real (Suc k)))"
    (is "_ = _ - (_ + ?S)") using x by (simp add: Polygamma_approx_1_real stirling_sum_def)
  also have "?S = (\<Sum>k=Suc 0..<m. bernoulli' (Suc k) * inverse x ^ Suc k / real (Suc k))"
    by (intro sum.cong refl) (simp_all add: bernoulli'_def)
  also have "1 / (2 * x) + \<dots> = 
               (\<Sum>k=0..<m. bernoulli' (Suc k) * inverse x ^ Suc k / real (Suc k))" using m
    by (subst (2) sum.atLeast_Suc_lessThan) (simp_all add: field_simps)
  also have "\<dots> = (\<Sum>k = Suc 0..m. bernoulli' k * inverse x ^ k / real k)" using assms
    by (subst sum.shift_bounds_Suc_ivl [symmetric]) (simp add: atLeastLessThanSuc_atLeastAtMost)
  finally show ?thesis .
qed

theorem
  assumes m: "m > 0"
  shows   ln_Gamma_real_asymptotics:
            "(\<lambda>x. ln_Gamma x - ((x - 1 / 2) * ln x - x + ln (2 * pi) / 2 +
                     (\<Sum>k = 1..<m. bernoulli (Suc k) / (real k * real (Suc k)) / x^k)))
                \<in> O(\<lambda>x. 1 / x ^ m)" (is ?th1)
    and   Digamma_real_asymptotics:
            "(\<lambda>x. Digamma x - (ln x - (\<Sum>k=1..m. bernoulli' k / real k / x ^ k)))
                \<in> O(\<lambda>x. 1 / (x ^ Suc m))" (is ?th2)
    and   Polygamma_real_asymptotics: "j > 0 \<Longrightarrow> 
             (\<lambda>x. Polygamma j x - (- 1) ^ Suc j * (\<Sum>k\<le>m. bernoulli' k *
                     pochhammer (real (Suc k)) (j - 1) / x ^ (k + j))) 
                \<in> O(\<lambda>x. 1 / x ^ (m+j+1))" (is "_ \<Longrightarrow> ?th3")
proof -
  define G :: "nat \<Rightarrow> real \<Rightarrow> real" where 
    "G = (\<lambda>m. if m = 0 then ln_Gamma else Polygamma (m - 1))"
  have *: "(\<lambda>x. G j x - h x) \<in> O(\<lambda>x. 1 / x ^ (m + j))"
    if "\<And>x::real. x > 0 \<Longrightarrow> Polygamma_approx j m x = h x" for j h
  proof -
    have "(\<lambda>x. G j x - h x) \<in> 
            \<Theta>(\<lambda>x. (deriv ^^ j) ln_Gamma x - Polygamma_approx j m x)" (is "_ \<in> \<Theta>(?f)")
      using that
      by (intro bigthetaI_cong) (auto intro: eventually_mono[OF eventually_gt_at_top[of "0::real"]]
            simp del: funpow.simps simp: higher_deriv_ln_Gamma_real G_def)
    also have "?f \<in> O(\<lambda>x::real. 1 / x ^ (m + j))" using m
      by (rule higher_deriv_lnGamma_stirling)
    finally show ?thesis .
  qed  
    
  note [[simproc del: simplify_landau_sum]]
  from *[OF Polygamma_approx_0] assms show ?th1 
    by (simp add: G_def Polygamma_approx_0 stirling_sum_def field_simps)
  from *[OF Polygamma_approx_1_real'] assms show ?th2 by (simp add: G_def field_simps)
      
  assume j: "j > 0"
  from *[OF Polygamma_approx_ge_2_real, of "j - 1"] assms j show ?th3
    by (simp add: G_def stirling_sum'_def power_add power_diff field_simps)
qed

end
