(*
    File:      Zeta_Function.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>The Hurwitz and Riemann $\zeta$ functions\<close>
theory Zeta_Function
imports
  "Euler_MacLaurin.Euler_MacLaurin"
  "Bernoulli.Bernoulli_Zeta"
  "Dirichlet_Series.Dirichlet_Series_Analysis"
  "Winding_Number_Eval.Winding_Number_Eval"
  "HOL-Real_Asymp.Real_Asymp"
  Zeta_Library
begin

subsection \<open>Preliminary facts\<close>

(* TODO Move once Landau symbols are in the distribution *)
lemma holomorphic_on_extend:
  assumes "f holomorphic_on S - {\<xi>}" "\<xi> \<in> interior S" "f \<in> O[at \<xi>](\<lambda>_. 1)"
  shows   "(\<exists>g. g holomorphic_on S \<and> (\<forall>z\<in>S - {\<xi>}. g z = f z))"
  by (subst holomorphic_on_extend_bounded) (insert assms, auto elim!: landau_o.bigE)

lemma removable_singularities:
  assumes "finite X" "X \<subseteq> interior S" "f holomorphic_on (S - X)"
  assumes "\<And>z. z \<in> X \<Longrightarrow> f \<in> O[at z](\<lambda>_. 1)"
  shows   "\<exists>g. g holomorphic_on S \<and> (\<forall>z\<in>S-X. g z = f z)"
  using assms
proof (induction arbitrary: f rule: finite_induct)
  case empty
  thus ?case by auto
next
  case (insert z0 X f)
  from insert.prems and insert.hyps have z0: "z0 \<in> interior (S - X)"
    by (auto simp: interior_diff finite_imp_closed)
  hence "\<exists>g. g holomorphic_on (S - X) \<and> (\<forall>z\<in>S - X - {z0}. g z = f z)"
    using insert.prems insert.hyps by (intro holomorphic_on_extend) auto
  then obtain g where g: "g holomorphic_on (S - X)" "\<forall>z\<in>S - X - {z0}. g z = f z" by blast
  have "\<exists>h. h holomorphic_on S \<and> (\<forall>z\<in>S - X. h z = g z)"
  proof (rule insert.IH)
    fix z0' assume z0': "z0' \<in> X"
    hence "eventually (\<lambda>z. z \<in> interior S - (X - {z0'}) - {z0}) (nhds z0')"
      using insert.prems insert.hyps
      by (intro eventually_nhds_in_open open_Diff finite_imp_closed) auto
    hence ev: "eventually (\<lambda>z. z \<in> S - X - {z0}) (at z0')"
      unfolding eventually_at_filter 
      by eventually_elim (insert z0' insert.hyps interior_subset[of S], auto)
    have "g \<in> \<Theta>[at z0'](f)"
      by (intro bigthetaI_cong eventually_mono[OF ev]) (insert g, auto)
    also have "f \<in> O[at z0'](\<lambda>_. 1)"
      using z0' by (intro insert.prems) auto
    finally show "g \<in> \<dots>" .
  qed (insert insert.prems g, auto)
  then obtain h where "h holomorphic_on S" "\<forall>z\<in>S - X. h z = g z" by blast
  with g have "h holomorphic_on S" "\<forall>z\<in>S - insert z0 X. h z = f z" by auto
  thus ?case by blast
qed

lemma continuous_imp_bigo_1:
  assumes "continuous (at x within A) f"
  shows   "f \<in> O[at x within A](\<lambda>_. 1)"
proof (rule bigoI_tendsto)
  from assms show "((\<lambda>x. f x / 1) \<longlongrightarrow> f x) (at x within A)"
    by (auto simp: continuous_within)
qed auto

lemma taylor_bigo_linear:
  assumes "f field_differentiable at x0 within A"
  shows   "(\<lambda>x. f x - f x0) \<in> O[at x0 within A](\<lambda>x. x - x0)"
proof -
  from assms obtain f' where "(f has_field_derivative f') (at x0 within A)"
    by (auto simp: field_differentiable_def)
  hence "((\<lambda>x. (f x - f x0) / (x - x0)) \<longlongrightarrow> f') (at x0 within A)"
    by (auto simp: has_field_derivative_iff)
  thus ?thesis by (intro bigoI_tendsto[where c = f']) (auto simp: eventually_at_filter)
qed
(* END TODO *)

(* TODO Move? *)
lemma powr_add_minus_powr_asymptotics:
  fixes a z :: complex 
  shows "((\<lambda>z. ((1 + z) powr a - 1) / z) \<longlongrightarrow> a) (at 0)"
proof (rule Lim_transform_eventually)
  have "eventually (\<lambda>z::complex. z \<in> ball 0 1 - {0}) (at 0)"
    using eventually_at_ball'[of 1 "0::complex" UNIV] by (simp add: dist_norm)
  thus "eventually (\<lambda>z. (\<Sum>n. (a gchoose (Suc n)) * z ^ n) = ((1 + z) powr a - 1) / z) (at 0)"
  proof eventually_elim
    case (elim z)
    hence "(\<lambda>n. (a gchoose n) * z ^ n) sums (1 + z) powr a"
      by (intro gen_binomial_complex) auto
    hence "(\<lambda>n. (a gchoose (Suc n)) * z ^ (Suc n)) sums ((1 + z) powr a - 1)"
      by (subst sums_Suc_iff) simp_all
    also have "(\<lambda>n. (a gchoose (Suc n)) * z ^ (Suc n)) = (\<lambda>n. z * ((a gchoose (Suc n)) * z ^ n))"
      by (simp add: algebra_simps)
    finally have "(\<lambda>n. (a gchoose (Suc n)) * z ^ n) sums (((1 + z) powr a - 1) / z)"
      by (rule sums_mult_D) (use elim in auto)
    thus ?case by (simp add: sums_iff)
  qed
next
  have "conv_radius (\<lambda>n. a gchoose (n + 1)) = conv_radius (\<lambda>n. a gchoose n)"
    using conv_radius_shift[of "\<lambda>n. a gchoose n" 1] by simp
  hence "continuous_on (cball 0 (1/2)) (\<lambda>z. \<Sum>n. (a gchoose (Suc n)) * (z - 0) ^ n)"
    using conv_radius_gchoose[of a] by (intro powser_continuous_suminf) (simp_all)
  hence "isCont (\<lambda>z. \<Sum>n. (a gchoose (Suc n)) * z ^ n) 0"
    by (auto intro: continuous_on_interior)
  thus "(\<lambda>z. \<Sum>n. (a gchoose Suc n) * z ^ n) \<midarrow>0\<rightarrow> a"
    by (auto simp: isCont_def)
qed

lemma complex_powr_add_minus_powr_asymptotics:
  fixes s :: complex
  assumes a: "a > 0" and s: "Re s < 1"
  shows "filterlim (\<lambda>x. of_real (x + a) powr s - of_real x powr s) (nhds 0) at_top"
proof (rule Lim_transform_eventually)
  show "eventually (\<lambda>x. ((1 + of_real (a / x)) powr s - 1) / of_real (a / x) * 
                            of_real x powr (s - 1) * a = 
                          of_real (x + a) powr s - of_real x powr s) at_top"
    (is "eventually (\<lambda>x. ?f x / ?g x * ?h x * _ = _) _") using eventually_gt_at_top[of a]
  proof eventually_elim
    case (elim x)
    have "?f x / ?g x * ?h x * a = ?f x * (a * ?h x / ?g x)" by simp
    also have "a * ?h x / ?g x = of_real x powr s"
      using elim a by (simp add: powr_diff)
    also have "?f x * \<dots> = of_real (x + a) powr s - of_real x powr s"
      using a elim by (simp add: algebra_simps powr_times_real [symmetric])
    finally show ?case .
  qed

  have "filterlim (\<lambda>x. complex_of_real (a / x)) (nhds (complex_of_real 0)) at_top"
    by (intro tendsto_of_real real_tendsto_divide_at_top[OF tendsto_const] filterlim_ident)
  hence "filterlim (\<lambda>x. complex_of_real (a / x)) (at 0) at_top"
    using a by (intro filterlim_atI) auto
  hence "((\<lambda>x. ?f x / ?g x * ?h x * a) \<longlongrightarrow> s * 0 * a) at_top" using s
    by (intro tendsto_mult filterlim_compose[OF powr_add_minus_powr_asymptotics]
              tendsto_const tendsto_neg_powr_complex_of_real filterlim_ident) auto
  thus "((\<lambda>x. ?f x / ?g x * ?h x * a) \<longlongrightarrow> 0) at_top" by simp
qed
(* END TODO *)

lemma summable_zeta:
  assumes "Re s > 1"
  shows   "summable (\<lambda>n. of_nat (Suc n) powr -s)"
proof -
  have "summable (\<lambda>n. exp (complex_of_real (ln (real (Suc n))) * - s))" (is "summable ?f")
    by (subst summable_Suc_iff, rule summable_complex_powr_iff) (use assms in auto)
  also have "?f = (\<lambda>n. of_nat (Suc n) powr -s)"
    by (simp add: powr_def algebra_simps del: of_nat_Suc)
  finally show ?thesis .
qed

lemma summable_zeta_real:
  assumes "x > 1"
  shows   "summable (\<lambda>n. real (Suc n) powr -x)"
proof -
  have "summable (\<lambda>n. of_nat (Suc n) powr -complex_of_real x)"
    using assms by (intro summable_zeta) simp_all
  also have "(\<lambda>n. of_nat (Suc n) powr -complex_of_real x) = (\<lambda>n. of_real (real (Suc n) powr -x))"
    by (subst powr_Reals_eq) simp_all
  finally show ?thesis
    by (subst (asm) summable_complex_of_real)
qed

lemma summable_hurwitz_zeta:
  assumes "Re s > 1" "a > 0"
  shows   "summable (\<lambda>n. (of_nat n + of_real a) powr -s)"
proof -
  have "summable (\<lambda>n. (of_nat (Suc n) + of_real a) powr -s)"
  proof (rule summable_comparison_test' [OF summable_zeta_real [OF assms(1)]] )
    fix n :: nat
    have "norm ((of_nat (Suc n) + of_real a) powr -s) = (real (Suc n) + a) powr - Re s"
      (is "?N = _") using assms by (simp add: norm_powr_real_powr)
    also have "\<dots> \<le> real (Suc n) powr -Re s"
      using assms by (intro powr_mono2') auto
    finally show "?N \<le> \<dots>" .
  qed
  thus ?thesis by (subst (asm) summable_Suc_iff)
qed

lemma summable_hurwitz_zeta_real:
  assumes "x > 1" "a > 0"
  shows   "summable (\<lambda>n. (real n + a) powr -x)"
proof -
  have "summable (\<lambda>n. (of_nat n + of_real a) powr -complex_of_real x)"
    using assms by (intro summable_hurwitz_zeta) simp_all
  also have "(\<lambda>n. (of_nat n + of_real a) powr -complex_of_real x) = 
               (\<lambda>n. of_real ((real n + a) powr -x))"
    using assms by (subst powr_Reals_eq) simp_all
  finally show ?thesis
    by (subst (asm) summable_complex_of_real)
qed



subsection \<open>Definitions\<close>

text \<open>
  We use the Euler--MacLaurin summation formula to express $\zeta(s,a) - \frac{a^{1-s}}{s-1}$ as
  a polynomial plus some remainder term, which is an integral over a function of 
  order $O(-1-2n-\mathfrak{R}(s))$. It is then clear that this integral converges uniformly
  to an analytic function in $s$ for all $s$ with $\mathfrak{R}(s) > -2n$.
\<close>
definition pre_zeta_aux :: "nat \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> complex" where
  "pre_zeta_aux N a s = a powr - s / 2 +
    (\<Sum>i=1..N. (bernoulli (2 * i) / fact (2 * i)) *\<^sub>R (pochhammer s (2*i - 1) * 
                 of_real a powr (- s - of_nat (2*i - 1)))) +
    EM_remainder (Suc (2*N)) 
      (\<lambda>x. -(pochhammer s (Suc (2*N)) * of_real (x + a) powr (- 1 - 2*N - s))) 0"

text \<open>
  By iterating the above construction long enough, we can extend this to the entire
  complex plane.
\<close>
definition pre_zeta :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  "pre_zeta a s = pre_zeta_aux (nat (1 - \<lceil>Re s / 2\<rceil>)) a s"

text \<open>
  We can then obtain the Hurwitz $\zeta$ function by adding back the pole at 1.
  Note that it is not necessary to trust that this somewhat complicated definition is,
  in fact, the correct one, since we will later show that this Hurwitz zeta function
  fulfils
  \[\zeta(s,a) = \sum_{n=0}^\infty \frac{1}{(n + a)^s}\]
  and is analytic on $\mathbb{C}\setminus \{1\}$, which uniquely defines the function
  due to analytic continuation. It is therefore obvious that any alternative definition
  that is analytic on $\mathbb{C}\setminus \{1\}$ and satisfies the above equation 
  must be equal to our Hurwitz $\zeta$ function.
\<close>
definition hurwitz_zeta :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  "hurwitz_zeta a s = (if s = 1 then 0 else pre_zeta a s + of_real a powr (1 - s) / (s - 1))"

text \<open>
  The Riemann $\zeta$ function is simply the Hurwitz $\zeta$ function with $a = 1$.
\<close>
definition zeta :: "complex \<Rightarrow> complex" where
  "zeta = hurwitz_zeta 1"


text \<open>
  We define the $\zeta$ functions as 0 at their poles. To avoid confusion, these facts
  are not added as simplification rules by default.
\<close>
lemma hurwitz_zeta_1: "hurwitz_zeta c 1 = 0"
  by (simp add: hurwitz_zeta_def)

lemma zeta_1: "zeta 1 = 0"
  by (simp add: zeta_def hurwitz_zeta_1)

lemma zeta_minus_pole_eq: "s \<noteq> 1 \<Longrightarrow> zeta s - 1 / (s - 1) = pre_zeta 1 s"
  by (simp add: zeta_def hurwitz_zeta_def)


context
begin

private lemma holomorphic_pre_zeta_aux':
  assumes "a > 0" "bounded U" "open U" "U \<subseteq> {s. Re s > \<sigma>}" and \<sigma>: "\<sigma> > - 2 * real n"
  shows   "pre_zeta_aux n a holomorphic_on U" unfolding pre_zeta_aux_def
proof (intro holomorphic_intros)
  define C :: real where "C = max 0 (Sup ((\<lambda>s. norm (pochhammer s (Suc (2 * n)))) ` closure U))"
  have "compact (closure U)" 
    using assms by (auto simp: compact_eq_bounded_closed)
  hence "compact ((\<lambda>s. norm (pochhammer s (Suc (2 * n)))) ` closure U)"
    by (rule compact_continuous_image [rotated]) (auto intro!: continuous_intros)
  hence "bounded ((\<lambda>s. norm (pochhammer s (Suc (2 * n)))) ` closure U)"
    by (simp add: compact_eq_bounded_closed)
  hence C: "cmod (pochhammer s (Suc (2 * n))) \<le> C" if "s \<in> U" for s
    using that closure_subset[of U] unfolding C_def 
    by (intro max.coboundedI2 cSup_upper bounded_imp_bdd_above) (auto simp: image_iff)
  have C' [simp]: "C \<ge> 0" by (simp add: C_def)

  let ?g = "\<lambda>(x::real). C * (x + a) powr (- 1 - 2 * of_nat n - \<sigma>)"
  let ?G = "\<lambda>(x::real). C / (- 2 * of_nat n - \<sigma>) * (x + a) powr (- 2 * of_nat n - \<sigma>)"  
  define poch' where "poch' = deriv (\<lambda>z::complex. pochhammer z (Suc (2 * n)))"
  have [derivative_intros]:
    "((\<lambda>z. pochhammer z (Suc (2 * n))) has_field_derivative poch' z) (at z within A)" 
    for z :: complex and A unfolding poch'_def
    by (rule holomorphic_derivI [OF holomorphic_pochhammer [of _ UNIV]]) auto
  have A: "continuous_on A poch'" for A unfolding poch'_def 
    by (rule continuous_on_subset[OF _ subset_UNIV], 
        intro holomorphic_on_imp_continuous_on holomorphic_deriv)
        (auto intro: holomorphic_pochhammer) 
  note [continuous_intros] = continuous_on_compose2[OF this _ subset_UNIV]

  define f' where "f' = (\<lambda>z t. - (poch' z * complex_of_real (t + a) powr (- 1 - 2 * of_nat n - z) -
                          Ln (complex_of_real (t + a)) * complex_of_real (t + a) powr 
                            (- 1 - 2 * of_nat n - z) * pochhammer z (Suc (2 * n))))"

  show "(\<lambda>z. EM_remainder (Suc (2 * n)) (\<lambda>x. - (pochhammer z (Suc (2 * n)) *
                  complex_of_real (x + a) powr (- 1 - 2 * of_nat n - z))) 0) holomorphic_on
    U" unfolding pre_zeta_aux_def
  proof (rule holomorphic_EM_remainder[of _ ?G ?g _ _ f'], goal_cases)
    case (1 x)
    show ?case
      by (insert 1 \<sigma> \<open>a > 0\<close>, rule derivative_eq_intros refl | simp)+
         (auto simp: field_simps powr_diff powr_add powr_minus)
  next
    case (2 z t x)
    note [derivative_intros] = has_field_derivative_powr_right [THEN DERIV_chain2]
    show ?case
      by (insert 2 \<sigma> \<open>a > 0\<close>, (rule derivative_eq_intros refl | (simp add: add_eq_0_iff; fail))+)
         (simp add: f'_def)
  next
    case 3
    hence *: "complex_of_real x + complex_of_real a \<notin> \<real>\<^sub>\<le>\<^sub>0" if "x \<ge> 0" for x
      using nonpos_Reals_of_real_iff[of "x+a", unfolded of_real_add] that \<open>a > 0\<close> by auto
    show ?case using \<open>a > 0\<close> and * unfolding f'_def
      by (auto simp: case_prod_unfold add_eq_0_iff intro!: continuous_intros)
  next
    case (4 b c z e)
    have "- 2 * real n < \<sigma>" by (fact \<sigma>)
    also from 4 assms have "\<sigma> < Re z" by auto
    finally show ?case using assms 4
      by (intro integrable_continuous_real continuous_intros) (auto simp: add_eq_0_iff)
  next
    case (5 t x s)
    thus ?case using \<open>a > 0\<close>
      by (intro integrable_EM_remainder') (auto intro!: continuous_intros simp: add_eq_0_iff)
  next
    case 6
    from \<sigma> have "(\<lambda>y. C / (-2 * real n - \<sigma>) * (a + y) powr (-2 * real n - \<sigma>)) \<longlonglongrightarrow> 0"
      by (intro tendsto_mult_right_zero tendsto_neg_powr
            filterlim_real_sequentially filterlim_tendsto_add_at_top [OF tendsto_const]) auto
    thus ?case unfolding convergent_def by (auto simp: add_ac)
  next
    case 7
    show ?case 
    proof (intro eventually_mono [OF eventually_ge_at_top[of 1]] ballI)
      fix x :: real and s :: complex assume x: "x \<ge> 1" and s: "s \<in> U"
      have "norm (- (pochhammer s (Suc (2 * n)) * of_real (x + a) powr (- 1 - 2 * of_nat n - s))) =
              norm (pochhammer s (Suc (2 * n))) * (x + a) powr (-1 - 2 * of_nat n - Re s)"
        (is "?N = _") using 7 \<open>a > 0\<close> x by (simp add: norm_mult norm_powr_real_powr)
      also have "\<dots> \<le> ?g x"
        using 7 assms x s \<open>a > 0\<close> by (intro mult_mono C powr_mono) auto
      finally show "?N \<le> ?g x" .
    qed
  qed (insert assms, auto)
qed (insert assms, auto)

lemma analytic_pre_zeta_aux:
  assumes "a > 0"
  shows   "pre_zeta_aux n a analytic_on {s. Re s > - 2 * real n}"
  unfolding analytic_on_def
proof
  fix s assume s: "s \<in> {s. Re s > - 2 * real n}"
  define \<sigma> where "\<sigma> = (Re s - 2 * real n) / 2"
  with s have \<sigma>: "\<sigma> > - 2 * real n" 
    by (simp add: \<sigma>_def field_simps)
  from s have s': "s \<in> {s. Re s > \<sigma>}"
    by (auto simp: \<sigma>_def field_simps)

  have "open {s. Re s > \<sigma>}"
    by (rule open_halfspace_Re_gt)
  with s' obtain \<epsilon> where "\<epsilon> > 0" "ball s \<epsilon> \<subseteq> {s. Re s > \<sigma>}"
    unfolding open_contains_ball by blast
  with \<sigma> have "pre_zeta_aux n a holomorphic_on ball s \<epsilon>"
    by (intro holomorphic_pre_zeta_aux' [OF assms, of _ \<sigma>]) auto
  with \<open>\<epsilon> > 0\<close> show "\<exists>e>0. pre_zeta_aux n a holomorphic_on ball s e"
    by blast
qed
end

context
  fixes s :: complex and N :: nat and \<zeta> :: "complex \<Rightarrow> complex" and a :: real
  assumes s: "Re s > 1" and a: "a > 0"
  defines "\<zeta> \<equiv> (\<lambda>s. \<Sum>n. (of_nat n + of_real a) powr -s)"
begin

interpretation \<zeta>: euler_maclaurin_nat'
  "\<lambda>x. of_real (x + a) powr (1 - s) / (1 - s)" "\<lambda>x. of_real (x + a) powr -s" 
  "\<lambda>n x. (-1) ^ n * pochhammer s n * of_real (x + a) powr -(s + n)" 
  0 N "\<zeta> s" "{}"
proof (standard, goal_cases)
  case 2
  show ?case by (simp add: powr_minus field_simps)
next
  case (3 k)
  have "complex_of_real x + complex_of_real a = 0 \<longleftrightarrow> x = -a" for x
    by (simp only: of_real_add [symmetric] of_real_eq_0_iff add_eq_0_iff2)
  with a s show ?case
    by (intro continuous_intros) (auto simp: add_nonneg_nonneg)
next
  case (4 k x)
  with a have "0 < x + a" by simp
  hence *: "complex_of_real x + complex_of_real a \<notin> \<real>\<^sub>\<le>\<^sub>0"
    using nonpos_Reals_of_real_iff[of "x+a", unfolded of_real_add] by auto
  have **: "pochhammer z (Suc n) = - pochhammer z n * (-z - of_nat n :: complex)" for z n
    by (simp add: pochhammer_rec' field_simps)
  show "((\<lambda>x. (- 1) ^ k * pochhammer s k * of_real (x + a) powr - (s + of_nat k)) 
          has_vector_derivative (- 1) ^ Suc k * pochhammer s (Suc k) *
            of_real (x + a) powr - (s + of_nat (Suc k))) (at x)"
    by (insert 4 *, (rule has_vector_derivative_real_field derivative_eq_intros refl | simp)+)
       (auto simp: divide_simps powr_add powr_diff powr_minus **)
next
  case 5
  with s a show ?case 
    by (auto intro!: continuous_intros simp: minus_equation_iff add_eq_0_iff)
next
  case (6 x)
  with a have "0 < x + a" by simp
  hence *: "complex_of_real x + complex_of_real a \<notin> \<real>\<^sub>\<le>\<^sub>0"
    using nonpos_Reals_of_real_iff[of "x+a", unfolded of_real_add] by auto
  show ?case unfolding of_real_add
    by (insert 6 s *, (rule has_vector_derivative_real_field derivative_eq_intros refl | 
          force simp add: minus_equation_iff)+)
next
  case 7
  from s a have "(\<lambda>k. (of_nat k + of_real a) powr -s) sums \<zeta> s"
    unfolding \<zeta>_def by (intro summable_sums summable_hurwitz_zeta) auto
  hence 1: "(\<lambda>b. (\<Sum>k=0..b. (of_nat k + of_real a) powr -s)) \<longlonglongrightarrow> \<zeta> s"
    by (simp add: sums_def')

  {
    fix z assume "Re z < 0"
    hence "((\<lambda>b. (a + real b) powr Re z) \<longlongrightarrow> 0) at_top"
      by (intro tendsto_neg_powr filterlim_tendsto_add_at_top filterlim_real_sequentially) auto    
    also have "(\<lambda>b. (a + real b) powr Re z) = (\<lambda>b. norm ((of_nat b + a) powr z))"
      using a by (subst norm_powr_real_powr) (auto simp: add_ac)
    finally have "((\<lambda>b. (of_nat b + a) powr z) \<longlongrightarrow> 0) at_top" 
      by (subst (asm) tendsto_norm_zero_iff) simp
  } note * = this
  have "(\<lambda>b. (of_nat b + a) powr (1 - s) / (1 - s)) \<longlonglongrightarrow> 0 / (1 - s)"
    using s by (intro tendsto_divide tendsto_const *) auto
  hence 2: "(\<lambda>b. (of_nat b + a) powr (1 - s) / (1 - s)) \<longlonglongrightarrow> 0"
    by simp

  have "(\<lambda>b. (\<Sum>i<2 * N + 1. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R
             ((- 1) ^ i * pochhammer s i * (of_nat b + a) powr -(s + of_nat i))))
          \<longlonglongrightarrow> (\<Sum>i<2 * N + 1. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R 
                   ((- 1) ^ i * pochhammer s i * 0))"
    using s by (intro tendsto_intros *) auto
  hence 3: "(\<lambda>b. (\<Sum>i<2 * N + 1. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R
              ((- 1) ^ i * pochhammer s i * (of_nat b + a) powr -(s + of_nat i)))) \<longlonglongrightarrow> 0" 
    by simp

  from tendsto_diff[OF tendsto_diff[OF 1 2] 3]
  show ?case by simp
qed simp_all

text \<open>
  The pre-$\zeta$ functions agree with the infinite sum that is used to define the $\zeta$
  function for $\mathfrak{R}(s)>1$.
\<close>
lemma pre_zeta_aux_conv_zeta:
  "pre_zeta_aux N a s = \<zeta> s + a powr (1 - s) / (1 - s)"
proof -
  let ?R = "(\<Sum>i=1..N. ((bernoulli (2*i) / fact (2*i)) *\<^sub>R pochhammer s (2*i - 1) * of_real a powr (-s - (2*i-1))))"
  let ?S = "EM_remainder (Suc (2 * N)) (\<lambda>x. - (pochhammer s (Suc (2*N)) *
              of_real (x + a) powr (- 1 - 2 * of_nat N - s))) 0"
  from \<zeta>.euler_maclaurin_strong_nat'[OF le_refl, simplified]
  have "of_real a powr -s = a powr (1 - s) / (1 - s) + \<zeta> s + a powr -s / 2 + (-?R) - ?S"
    unfolding sum_negf [symmetric] by (simp add: scaleR_conv_of_real pre_zeta_aux_def mult_ac)
  thus ?thesis unfolding pre_zeta_aux_def 
    (* TODO: Field_as_Ring causes some problems with field_simps vs. div_mult_self *)
    by (simp add: field_simps del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
qed

end


text \<open>
  Since all of the partial pre-$\zeta$ functions are analytic and agree in the halfspace with 
  $\mathfrak R(s)>0$, they must agree in their entire domain.
\<close>
lemma pre_zeta_aux_eq:
  assumes "m \<le> n" "a > 0" "Re s > -2 * real m"
  shows   "pre_zeta_aux m a s = pre_zeta_aux n a s"
proof -
  have "pre_zeta_aux n a s - pre_zeta_aux m a s = 0"
  proof (rule analytic_continuation[of "\<lambda>s. pre_zeta_aux n a s - pre_zeta_aux m a s"])
    show "(\<lambda>s. pre_zeta_aux n a s - pre_zeta_aux m a s) holomorphic_on {s. Re s > -2 * real m}"
      using assms by (intro holomorphic_intros analytic_imp_holomorphic 
                        analytic_on_subset[OF analytic_pre_zeta_aux]) auto
  next
    fix s assume "s \<in> {s. Re s > 1}"
    with \<open>a > 0\<close> show "pre_zeta_aux n a s - pre_zeta_aux m a s = 0"
      by (simp add: pre_zeta_aux_conv_zeta)
  next
    have "2 \<in> {s. Re s > 1}" by simp
    also have "\<dots> = interior \<dots>"
      by (intro interior_open [symmetric] open_halfspace_Re_gt)
    finally show "2 islimpt {s. Re s > 1}"
      by (rule interior_limit_point)
  next
    show "connected {s. Re s > -2 * real m}"
      using convex_halfspace_gt[of "-2 * real m" "1::complex"]
      by (intro convex_connected) auto
  qed (insert assms, auto simp: open_halfspace_Re_gt)
  thus ?thesis by simp
qed

lemma pre_zeta_aux_eq':
  assumes "a > 0" "Re s > -2 * real m" "Re s > -2 * real n"
  shows   "pre_zeta_aux m a s = pre_zeta_aux n a s"
proof (cases m n rule: linorder_cases)
  case less
  with assms show ?thesis by (intro pre_zeta_aux_eq) auto
next
  case greater
  with assms show ?thesis by (subst eq_commute, intro pre_zeta_aux_eq) auto
qed auto

lemma pre_zeta_aux_eq_pre_zeta:
  assumes "Re s > -2 * real n" and "a > 0"
  shows   "pre_zeta_aux n a s = pre_zeta a s"
  unfolding pre_zeta_def
proof (intro pre_zeta_aux_eq')
  from assms show "- 2 * real (nat (1 - \<lceil>Re s / 2\<rceil>)) < Re s"
    by linarith
qed (insert assms, simp_all)

text \<open>
  This means that the idea of iterating that construction infinitely does yield
  a well-defined entire function.
\<close>
lemma analytic_pre_zeta: 
  assumes "a > 0"
  shows   "pre_zeta a analytic_on A"
  unfolding analytic_on_def
proof
  fix s assume "s \<in> A"
  let ?B = "{s'. Re s' > of_int \<lfloor>Re s\<rfloor> - 1}"
  have s: "s \<in> ?B" by simp linarith?
  moreover have "open ?B" by (rule open_halfspace_Re_gt)
  ultimately obtain \<epsilon> where \<epsilon>: "\<epsilon> > 0" "ball s \<epsilon> \<subseteq> ?B"
    unfolding open_contains_ball by blast
  define C where "C = ball s \<epsilon>"

  note analytic = analytic_on_subset[OF analytic_pre_zeta_aux]
  have "pre_zeta_aux (nat \<lceil>- Re s\<rceil> + 2) a holomorphic_on C"
  proof (intro analytic_imp_holomorphic analytic subsetI assms, goal_cases)
    case (1 w)
    with \<epsilon> have "w \<in> ?B" by (auto simp: C_def)
    thus ?case by (auto simp: ceiling_minus)
  qed
  also have "?this \<longleftrightarrow> pre_zeta a holomorphic_on C"
  proof (intro holomorphic_cong refl pre_zeta_aux_eq_pre_zeta assms)
    fix w assume "w \<in> C"
    with \<epsilon> have w: "w \<in> ?B" by (auto simp: C_def)
    thus " - 2 * real (nat \<lceil>- Re s\<rceil> + 2) < Re w"
      by (simp add: ceiling_minus)
  qed
  finally show "\<exists>e>0. pre_zeta a holomorphic_on ball s e"
    using \<open>\<epsilon> > 0\<close> unfolding C_def by blast
qed

lemma holomorphic_pre_zeta [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> a > 0 \<Longrightarrow> (\<lambda>z. pre_zeta a (f z)) holomorphic_on A"
  using holomorphic_on_compose [OF _ analytic_imp_holomorphic [OF analytic_pre_zeta], of f]
  by (simp add: o_def)

corollary continuous_on_pre_zeta:
  "a > 0 \<Longrightarrow> continuous_on A (pre_zeta a)"
  by (intro holomorphic_on_imp_continuous_on holomorphic_intros) auto

corollary continuous_on_pre_zeta' [continuous_intros]:
  "continuous_on A f \<Longrightarrow> a > 0 \<Longrightarrow> continuous_on A (\<lambda>x. pre_zeta a (f x))"
  using continuous_on_compose2 [OF continuous_on_pre_zeta, of a A f "f ` A"]
  by (auto simp: image_iff)

corollary continuous_pre_zeta [continuous_intros]:
  "a > 0 \<Longrightarrow> continuous (at s within A) (pre_zeta a)"
  by (rule continuous_within_subset[of _ UNIV])
     (insert continuous_on_pre_zeta[of a UNIV], 
      auto simp: continuous_on_eq_continuous_at open_Compl)

corollary continuous_pre_zeta' [continuous_intros]:
  "a > 0 \<Longrightarrow> continuous (at s within A) f \<Longrightarrow>
     continuous (at s within A) (\<lambda>s. pre_zeta a (f s))"
  using continuous_within_compose3[OF continuous_pre_zeta, of a s A f] by auto


text \<open>
  It is now obvious that $\zeta$ is holomorphic everywhere except 1, where it has a 
  simple pole with residue 1, which we can simply read off.
\<close>
theorem holomorphic_hurwitz_zeta: 
  assumes "a > 0" "1 \<notin> A"
  shows   "hurwitz_zeta a holomorphic_on A"
proof -
  have "(\<lambda>s. pre_zeta a s + complex_of_real a powr (1 - s) / (s - 1)) holomorphic_on A"
    using assms by (auto intro!: holomorphic_intros)
  also from assms have "?this \<longleftrightarrow> ?thesis"
    by (intro holomorphic_cong) (auto simp: hurwitz_zeta_def)
  finally show ?thesis .
qed

corollary holomorphic_hurwitz_zeta' [holomorphic_intros]:
  assumes "f holomorphic_on A" and "a > 0" and "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 1"
  shows   "(\<lambda>x. hurwitz_zeta a (f x)) holomorphic_on A"
proof -
  have "hurwitz_zeta a \<circ> f holomorphic_on A" using assms
    by (intro holomorphic_on_compose_gen[of _ _ _ "f ` A"] holomorphic_hurwitz_zeta assms) auto
  thus ?thesis by (simp add: o_def)
qed

theorem holomorphic_zeta: "1 \<notin> A\<Longrightarrow> zeta holomorphic_on A"
  unfolding zeta_def by (auto intro: holomorphic_intros)

corollary holomorphic_zeta' [holomorphic_intros]:
  assumes "f holomorphic_on A" and "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 1"
  shows   "(\<lambda>x. zeta (f x)) holomorphic_on A"
  using assms unfolding zeta_def by (auto intro: holomorphic_intros)

corollary analytic_hurwitz_zeta: 
  assumes "a > 0" "1 \<notin> A"
  shows   "hurwitz_zeta a analytic_on A"
proof -
  from assms(1) have "hurwitz_zeta a holomorphic_on -{1}"
    by (rule holomorphic_hurwitz_zeta) auto
  also have "?this \<longleftrightarrow> hurwitz_zeta a analytic_on -{1}"
    by (intro analytic_on_open [symmetric]) auto
  finally show ?thesis by (rule analytic_on_subset) (insert assms, auto)
qed

corollary analytic_zeta: "1 \<notin> A \<Longrightarrow> zeta analytic_on A"
  unfolding zeta_def by (rule analytic_hurwitz_zeta) auto

corollary continuous_on_hurwitz_zeta:
  "a > 0 \<Longrightarrow> 1 \<notin> A \<Longrightarrow> continuous_on A (hurwitz_zeta a)"
  by (intro holomorphic_on_imp_continuous_on holomorphic_intros) auto

corollary continuous_on_hurwitz_zeta' [continuous_intros]:
  "continuous_on A f \<Longrightarrow> a > 0 \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 1) \<Longrightarrow> 
     continuous_on A (\<lambda>x. hurwitz_zeta a (f x))"
  using continuous_on_compose2 [OF continuous_on_hurwitz_zeta, of a "f ` A" A f]
  by (auto simp: image_iff)

corollary continuous_on_zeta: "1 \<notin> A \<Longrightarrow> continuous_on A zeta"
  by (intro holomorphic_on_imp_continuous_on holomorphic_intros) auto

corollary continuous_on_zeta' [continuous_intros]:
  "continuous_on A f \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 1) \<Longrightarrow> 
     continuous_on A (\<lambda>x. zeta (f x))"
  using continuous_on_compose2 [OF continuous_on_zeta, of "f ` A" A f]
  by (auto simp: image_iff)

corollary continuous_hurwitz_zeta [continuous_intros]:
  "a > 0 \<Longrightarrow> s \<noteq> 1 \<Longrightarrow> continuous (at s within A) (hurwitz_zeta a)"
  by (rule continuous_within_subset[of _ UNIV])
     (insert continuous_on_hurwitz_zeta[of a "-{1}"], 
      auto simp: continuous_on_eq_continuous_at open_Compl)

corollary continuous_hurwitz_zeta' [continuous_intros]:
  "a > 0 \<Longrightarrow> f s \<noteq> 1 \<Longrightarrow> continuous (at s within A) f \<Longrightarrow>
     continuous (at s within A) (\<lambda>s. hurwitz_zeta a (f s))"
  using continuous_within_compose3[OF continuous_hurwitz_zeta, of a f s A] by auto

corollary continuous_zeta [continuous_intros]:
  "s \<noteq> 1 \<Longrightarrow> continuous (at s within A) zeta"
  unfolding zeta_def by (intro continuous_intros) auto

corollary continuous_zeta' [continuous_intros]:
  "f s \<noteq> 1 \<Longrightarrow> continuous (at s within A) f \<Longrightarrow> continuous (at s within A) (\<lambda>s. zeta (f s))"
  unfolding zeta_def by (intro continuous_intros) auto

corollary field_differentiable_at_zeta:
  assumes "s \<noteq> 1"
  shows "zeta field_differentiable at s"
proof -
  have "zeta holomorphic_on (- {1})" using holomorphic_zeta by force
  moreover have "open (-{1} :: complex set)" by (intro open_Compl) auto
  ultimately show ?thesis using assms
    by (auto simp add: holomorphic_on_open open_halfspace_Re_gt open_Diff field_differentiable_def)
qed

theorem is_pole_hurwitz_zeta:
  assumes "a > 0"
  shows   "is_pole (hurwitz_zeta a) 1"
proof -
  from assms have "continuous_on UNIV (pre_zeta a)"
    by (intro holomorphic_on_imp_continuous_on analytic_imp_holomorphic analytic_pre_zeta)
  hence "isCont (pre_zeta a) 1"
    by (auto simp: continuous_on_eq_continuous_at)
  hence *: "pre_zeta a \<midarrow>1\<rightarrow> pre_zeta a 1"
    by (simp add: isCont_def)
  from assms have "isCont (\<lambda>s. complex_of_real a powr (1 - s)) 1"
    by (intro isCont_powr_complex) auto
  with assms have **: "(\<lambda>s. complex_of_real a powr (1 - s)) \<midarrow>1\<rightarrow> 1" 
    by (simp add: isCont_def)
  have "(\<lambda>s::complex. s - 1) \<midarrow>1\<rightarrow> 1 - 1" by (intro tendsto_intros)
  hence "filterlim (\<lambda>s::complex. s - 1) (at 0) (at 1)"
    by (auto simp: filterlim_at eventually_at_filter)
  hence ***: "filterlim (\<lambda>s :: complex. a powr (1 - s) / (s - 1)) at_infinity (at 1)"
    by (intro filterlim_divide_at_infinity [OF **]) auto
  have "is_pole (\<lambda>s. pre_zeta a s + complex_of_real a powr (1 - s) / (s - 1)) 1"
    unfolding is_pole_def hurwitz_zeta_def by (rule tendsto_add_filterlim_at_infinity * ***)+
  also have "?this \<longleftrightarrow> ?thesis" unfolding is_pole_def
    by (intro filterlim_cong refl) (auto simp: eventually_at_filter hurwitz_zeta_def)
  finally show ?thesis .
qed

corollary is_pole_zeta: "is_pole zeta 1"
  unfolding zeta_def by (rule is_pole_hurwitz_zeta) auto

theorem zorder_hurwitz_zeta: 
  assumes "a > 0"
  shows   "zorder (hurwitz_zeta a) 1 = -1"
proof (rule zorder_eqI[of UNIV])
  fix w :: complex assume "w \<in> UNIV" "w \<noteq> 1"
  thus "hurwitz_zeta a w = (pre_zeta a w * (w - 1) + a powr (1 - w)) * (w - 1) powr (of_int (-1))"
    apply (subst (1) powr_of_int)
    by (auto simp add: hurwitz_zeta_def field_simps)
qed (insert assms, auto intro!: holomorphic_intros)

corollary zorder_zeta: "zorder zeta 1 = - 1"
  unfolding zeta_def by (rule zorder_hurwitz_zeta) auto

theorem residue_hurwitz_zeta: 
  assumes "a > 0"
  shows   "residue (hurwitz_zeta a) 1 = 1"
proof -
  note holo = analytic_imp_holomorphic[OF analytic_pre_zeta]
  have "residue (hurwitz_zeta a) 1 = residue (\<lambda>z. pre_zeta a z + a powr (1 - z) / (z - 1)) 1"
    by (intro residue_cong) (auto simp: eventually_at_filter hurwitz_zeta_def)
  also have "\<dots> = residue (\<lambda>z. a powr (1 - z) / (z - 1)) 1" using assms
    by (subst residue_add [of UNIV])
       (auto intro!: holomorphic_intros holo intro: residue_holo[of UNIV, OF _ _ holo])
  also have "\<dots> = complex_of_real a powr (1 - 1)"
    using assms by (intro residue_simple [of UNIV]) (auto intro!: holomorphic_intros)
  also from assms have "\<dots> = 1" by simp
  finally show ?thesis .
qed

corollary residue_zeta: "residue zeta 1 = 1"
  unfolding zeta_def by (rule residue_hurwitz_zeta) auto

lemma zeta_bigo_at_1: "zeta \<in> O[at 1 within A](\<lambda>x. 1 / (x - 1))"
proof -
  have "zeta \<in> \<Theta>[at 1 within A](\<lambda>s. pre_zeta 1 s + 1 / (s - 1))"
    by (intro bigthetaI_cong) (auto simp: eventually_at_filter zeta_def hurwitz_zeta_def)
  also have "(\<lambda>s. pre_zeta 1 s + 1 / (s - 1)) \<in> O[at 1 within A](\<lambda>s. 1 / (s - 1))"
  proof (rule sum_in_bigo)
    have "continuous_on UNIV (pre_zeta 1)"
      by (intro holomorphic_on_imp_continuous_on holomorphic_intros) auto
    hence "isCont (pre_zeta 1) 1" by (auto simp: continuous_on_eq_continuous_at)
    hence "continuous (at 1 within A) (pre_zeta 1)"
      by (rule continuous_within_subset) auto
    hence "pre_zeta 1 \<in> O[at 1 within A](\<lambda>_. 1)"
      by (intro continuous_imp_bigo_1) auto
    also have ev: "eventually (\<lambda>s. s \<in> ball 1 1 \<and> s \<noteq> 1 \<and> s \<in> A) (at 1 within A)"
      by (intro eventually_at_ball') auto
    have "(\<lambda>_. 1) \<in> O[at 1 within A](\<lambda>s. 1 / (s - 1))"
      by (intro landau_o.bigI[of 1] eventually_mono[OF ev]) 
         (auto simp: eventually_at_filter norm_divide dist_norm norm_minus_commute field_simps)
    finally show "pre_zeta 1 \<in> O[at 1 within A](\<lambda>s. 1 / (s - 1))" .
  qed simp_all
  finally show ?thesis .
qed

theorem
  assumes "a > 0" "Re s > 1"
  shows hurwitz_zeta_conv_suminf: "hurwitz_zeta a s = (\<Sum>n. (of_nat n + of_real a) powr -s)"
  and   sums_hurwitz_zeta: "(\<lambda>n. (of_nat n + of_real a) powr -s) sums hurwitz_zeta a s"
proof -
  from assms have [simp]: "s \<noteq> 1" by auto
  from assms have "hurwitz_zeta a s = pre_zeta_aux 0 a s + of_real a powr (1 - s) / (s - 1)"
    by (simp add: hurwitz_zeta_def pre_zeta_def)
  also from assms have "pre_zeta_aux 0 a s = (\<Sum>n. (of_nat n + of_real a) powr -s) + 
                          of_real a powr (1 - s) / (1 - s)"
    by (intro pre_zeta_aux_conv_zeta)
  also have "\<dots> + a powr (1 - s) / (s - 1) = 
               (\<Sum>n. (of_nat n + of_real a) powr -s) + a powr (1 - s) * (1 / (1 - s) + 1 / (s - 1))"
    by (simp add: algebra_simps)
  also have "1 / (1 - s) + 1 / (s - 1) = 0" 
    by (simp add: divide_simps)
  finally show "hurwitz_zeta a s = (\<Sum>n. (of_nat n + of_real a) powr -s)" by simp
  moreover have "(\<lambda>n. (of_nat n + of_real a) powr -s) sums (\<Sum>n. (of_nat n + of_real a) powr -s)"
    by (intro summable_sums summable_hurwitz_zeta assms)
  ultimately show "(\<lambda>n. (of_nat n + of_real a) powr -s) sums hurwitz_zeta a s" 
    by simp
qed

corollary
  assumes "Re s > 1"
  shows zeta_conv_suminf: "zeta s = (\<Sum>n. of_nat (Suc n) powr -s)"
  and   sums_zeta: "(\<lambda>n. of_nat (Suc n) powr -s) sums zeta s"
  using hurwitz_zeta_conv_suminf[of 1 s] sums_hurwitz_zeta[of 1 s] assms 
  by (simp_all add: zeta_def add_ac)

corollary
  assumes "n > 1"
  shows zeta_nat_conv_suminf: "zeta (of_nat n) = (\<Sum>k. 1 / of_nat (Suc k) ^ n)"
  and   sums_zeta_nat: "(\<lambda>k. 1 / of_nat (Suc k) ^ n) sums zeta (of_nat n)"
proof -
  have "(\<lambda>k. of_nat (Suc k) powr -of_nat n) sums zeta (of_nat n)"
    using assms by (intro sums_zeta) auto
  also have "(\<lambda>k. of_nat (Suc k) powr -of_nat n) = (\<lambda>k. 1 / of_nat (Suc k) ^ n :: complex)"
    by (simp add: powr_minus divide_simps del: of_nat_Suc)
  finally show "(\<lambda>k. 1 / of_nat (Suc k) ^ n) sums zeta (of_nat n)" .
  thus "zeta (of_nat n) = (\<Sum>k. 1 / of_nat (Suc k) ^ n)" by (simp add: sums_iff)
qed

lemma pre_zeta_aux_cnj [simp]: 
  assumes "a > 0"
  shows   "pre_zeta_aux n a (cnj z) = cnj (pre_zeta_aux n a z)"
proof -
  have "cnj (pre_zeta_aux n a z) = 
          of_real a powr -cnj z / 2 + (\<Sum>x=1..n. (bernoulli (2 * x) / fact (2 * x)) *\<^sub>R
            a powr (-cnj z - (2*x-1)) * pochhammer (cnj z) (2*x-1)) + EM_remainder (2*n+1)
          (\<lambda>x. -(pochhammer (cnj z) (Suc (2 * n)) * 
                  cnj (of_real (x + a) powr (-1 - 2 * of_nat n - z)))) 0"
    (is "_ = _ + ?A + ?B") unfolding pre_zeta_aux_def complex_cnj_add using assms
    by (subst EM_remainder_cnj [symmetric]) 
       (auto intro!: continuous_intros simp: cnj_powr add_eq_0_iff mult_ac)
  also have "?B = EM_remainder (2*n+1)
        (\<lambda>x. -(pochhammer (cnj z) (Suc (2 * n)) * of_real (x + a) powr (-1 - 2 * of_nat n - cnj z))) 0"
    using assms by (intro EM_remainder_cong) (auto simp: cnj_powr)
  also have "of_real a powr -cnj z / 2 + ?A + \<dots> = pre_zeta_aux n a (cnj z)"
    by (simp add: pre_zeta_aux_def mult_ac)
  finally show ?thesis ..
qed

lemma pre_zeta_cnj [simp]: "a > 0 \<Longrightarrow> pre_zeta a (cnj z) = cnj (pre_zeta a z)"
  by (simp add: pre_zeta_def)

lemma hurwitz_zeta_cnj [simp]: "a > 0 \<Longrightarrow> hurwitz_zeta a (cnj z) = cnj (hurwitz_zeta a z)"
proof -
  assume "a > 0"
  moreover have "cnj z = 1 \<longleftrightarrow> z = 1" by (simp add: complex_eq_iff)
  ultimately show ?thesis by (auto simp: hurwitz_zeta_def cnj_powr)
qed

lemma zeta_cnj [simp]: "zeta (cnj z) = cnj (zeta z)"
  by (simp add: zeta_def)

corollary hurwitz_zeta_real: "a > 0 \<Longrightarrow> hurwitz_zeta a (of_real x) \<in> \<real>"
  using hurwitz_zeta_cnj [of a "of_real x"] by (simp add: Reals_cnj_iff del: zeta_cnj)

corollary zeta_real: "zeta (of_real x) \<in> \<real>"
  unfolding zeta_def by (rule hurwitz_zeta_real) auto

corollary zeta_real': "z \<in> \<real> \<Longrightarrow> zeta z \<in> \<real>"
  by (elim Reals_cases) (auto simp: zeta_real)


subsection \<open>Connection to Dirichlet series\<close>

lemma eval_fds_zeta: "Re s > 1 \<Longrightarrow> eval_fds fds_zeta s = zeta s"
  using sums_zeta [of s] by (intro eval_fds_eqI) (auto simp: powr_minus divide_simps)

theorem euler_product_zeta:
  assumes "Re s > 1"
  shows   "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - 1 / of_nat p powr s) else 1) \<longlonglongrightarrow> zeta s"
  using euler_product_fds_zeta[of s] assms unfolding nat_power_complex_def 
  by (simp add: eval_fds_zeta)

corollary euler_product_zeta':
  assumes "Re s > 1"
  shows   "(\<lambda>n. \<Prod>p | prime p \<and> p \<le> n. inverse (1 - 1 / of_nat p powr s)) \<longlonglongrightarrow> zeta s"
proof -
  note euler_product_zeta [OF assms]
  also have "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - 1 / of_nat p powr s) else 1) =
               (\<lambda>n. \<Prod>p | prime p \<and> p \<le> n. inverse (1 - 1 / of_nat p powr s))"
    by (intro ext prod.mono_neutral_cong_right refl) auto
  finally show ?thesis .
qed

theorem zeta_Re_gt_1_nonzero: "Re s > 1 \<Longrightarrow> zeta s \<noteq> 0"
  using eval_fds_zeta_nonzero[of s] by (simp add: eval_fds_zeta)

theorem tendsto_zeta_Re_going_to_at_top: "(zeta \<longlongrightarrow> 1) (Re going_to at_top)"
proof (rule Lim_transform_eventually)
  have "eventually (\<lambda>x::real. x > 1) at_top"
    by (rule eventually_gt_at_top)
  hence "eventually (\<lambda>s. Re s > 1) (Re going_to at_top)"
    by blast
  thus "eventually (\<lambda>z. eval_fds fds_zeta z = zeta z) (Re going_to at_top)"
    by eventually_elim (simp add: eval_fds_zeta)
next
  have "conv_abscissa (fds_zeta :: complex fds) \<le> 1"
  proof (rule conv_abscissa_leI)
    fix c' assume "ereal c' > 1"
    thus "\<exists>s. s \<bullet> 1 = c' \<and> fds_converges fds_zeta (s::complex)"
      by (auto intro!: exI[of _ "of_real c'"])
  qed
  hence "(eval_fds fds_zeta \<longlongrightarrow> fds_nth fds_zeta 1) (Re going_to at_top)"
    by (intro tendsto_eval_fds_Re_going_to_at_top') auto
  thus "(eval_fds fds_zeta \<longlongrightarrow> 1) (Re going_to at_top)" by simp
qed

lemma conv_abscissa_zeta [simp]: "conv_abscissa (fds_zeta :: complex fds) = 1"
  and abs_conv_abscissa_zeta [simp]: "abs_conv_abscissa (fds_zeta :: complex fds) = 1"
proof -
  let ?z = "fds_zeta :: complex fds"
  have A: "conv_abscissa ?z \<ge> 1"
  proof (intro conv_abscissa_geI)
    fix c' assume "ereal c' < 1"
    hence "\<not>summable (\<lambda>n. real n powr -c')"
      by (subst summable_real_powr_iff) auto
    hence "\<not>summable (\<lambda>n. of_real (real n powr -c') :: complex)"
      by (subst summable_of_real_iff)
    also have "summable (\<lambda>n. of_real (real n powr -c') :: complex) \<longleftrightarrow> 
                 fds_converges fds_zeta (of_real c' :: complex)"
      unfolding fds_converges_def
      by (intro summable_cong eventually_mono [OF eventually_gt_at_top[of 0]])
         (simp add: fds_nth_zeta powr_Reals_eq powr_minus divide_simps)
    finally show "\<exists>s::complex. s \<bullet> 1 = c' \<and> \<not>fds_converges fds_zeta s"
      by (intro exI[of _ "of_real c'"]) auto
  qed

  have B: "abs_conv_abscissa ?z \<le> 1"
  proof (intro abs_conv_abscissa_leI)
    fix c' assume "1 < ereal c'"
    thus "\<exists>s::complex. s \<bullet> 1 = c' \<and> fds_abs_converges fds_zeta s"
      by (intro exI[of _ "of_real c'"]) auto
  qed

  have "conv_abscissa ?z \<le> abs_conv_abscissa ?z"
    by (rule conv_le_abs_conv_abscissa)
  also note B
  finally show "conv_abscissa ?z = 1" using A by (intro antisym)

  note A
  also have "conv_abscissa ?z \<le> abs_conv_abscissa ?z"
    by (rule conv_le_abs_conv_abscissa)
  finally show "abs_conv_abscissa ?z = 1" using B by (intro antisym)
qed

theorem deriv_zeta_sums:
  assumes s: "Re s > 1"
  shows "(\<lambda>n. -of_real (ln (real (Suc n))) / of_nat (Suc n) powr s) sums deriv zeta s"
proof -
  from s have "fds_converges (fds_deriv fds_zeta) s"
    by (intro fds_converges_deriv) simp_all
  with s have "(\<lambda>n. -of_real (ln (real (Suc n))) / of_nat (Suc n) powr s) sums
                  deriv (eval_fds fds_zeta) s"
    unfolding fds_converges_altdef
    by (simp add: fds_nth_deriv scaleR_conv_of_real eval_fds_deriv eval_fds_zeta)
  also from s have "eventually (\<lambda>s. s \<in> {s. Re s > 1}) (nhds s)"
    by (intro eventually_nhds_in_open) (auto simp: open_halfspace_Re_gt)
  hence "eventually (\<lambda>s. eval_fds fds_zeta s = zeta s) (nhds s)"
    by eventually_elim (auto simp: eval_fds_zeta)
  hence "deriv (eval_fds fds_zeta) s = deriv zeta s"
    by (intro deriv_cong_ev refl)
  finally show ?thesis .
qed

theorem inverse_zeta_sums:
  assumes s: "Re s > 1"
  shows   "(\<lambda>n. moebius_mu (Suc n) / of_nat (Suc n) powr s) sums inverse (zeta s)"
proof -
  have "fds_converges (fds moebius_mu) s"
    using assms by (auto intro!: fds_abs_converges_moebius_mu)
  hence "(\<lambda>n. moebius_mu (Suc n) / of_nat (Suc n) powr s) sums eval_fds (fds moebius_mu) s"
    by (simp add: fds_converges_altdef)
  also have "fds moebius_mu = inverse (fds_zeta :: complex fds)"
    by (rule fds_moebius_inverse_zeta)
  also from s have "eval_fds \<dots> s = inverse (zeta s)"
    by (subst eval_fds_inverse)
       (auto simp: fds_moebius_inverse_zeta [symmetric] eval_fds_zeta 
             intro!: fds_abs_converges_moebius_mu)
  finally show ?thesis .
qed

text \<open>
  The following gives an extension of the $\zeta$ functions to the critical strip.
\<close>
lemma hurwitz_zeta_critical_strip:
  fixes s :: complex and a :: real
  defines "S \<equiv> (\<lambda>n. \<Sum>i<n. (of_nat i + a) powr - s)"
  defines "I' \<equiv> (\<lambda>n. of_nat n powr (1 - s) / (1 - s))"
  assumes "Re s > 0" "s \<noteq> 1" and "a > 0"
  shows   "(\<lambda>n. S n - I' n) \<longlonglongrightarrow> hurwitz_zeta a s"
proof -
  from assms have [simp]: "s \<noteq> 1" by auto
  let ?f = "\<lambda>x. of_real (x + a) powr -s"
  let ?fs = "\<lambda>n x. (-1) ^ n * pochhammer s n * of_real (x + a) powr (-s - of_nat n)"
  have minus_commute: "-a - b = -b - a" for a b :: complex by (simp add: algebra_simps)
  define I where "I = (\<lambda>n. (of_nat n + a) powr (1 - s) / (1 - s))"
  define R where "R = (\<lambda>n. EM_remainder' 1 (?fs 1) (real 0) (real n))"
  define R_lim where "R_lim = EM_remainder 1 (?fs 1) 0"
  define C where "C = - (a powr -s / 2)"
  define D where "D = (\<lambda>n. (1/2) * (of_real (a + real n) powr - s))"
  define D' where "D' = (\<lambda>n. of_real (a + real n) powr - s)"
  define C' where "C' = a powr (1 - s) / (1 - s)"
  define C'' where "C'' = of_real a powr - s"
  {
    fix n :: nat assume n: "n > 0"
    have "((\<lambda>x. of_real (x + a) powr -s) has_integral (of_real (real n + a) powr (1-s) / (1 - s) - 
            of_real (0 + a) powr (1 - s) / (1 - s))) {0..real n}" using n assms 
      by (intro fundamental_theorem_of_calculus)
         (auto intro!: continuous_intros has_vector_derivative_real_field derivative_eq_intros
               simp: complex_nonpos_Reals_iff)
    hence I: "((\<lambda>x. of_real (x + a) powr -s) has_integral (I n - C')) {0..n}"
      by (auto simp: divide_simps C'_def I_def)
    have "(\<Sum>i\<in>{0<..n}. ?f (real i)) - integral {real 0..real n} ?f =
            (\<Sum>k<1. (bernoulli' (Suc k) / fact (Suc k)) *\<^sub>R (?fs k (real n) - ?fs k (real 0))) + R n" 
      using n assms unfolding R_def
      by (intro euler_maclaurin_strong_raw_nat[where Y = "{0}"])
         (auto intro!: continuous_intros derivative_eq_intros has_vector_derivative_real_field
               simp: pochhammer_rec' algebra_simps complex_nonpos_Reals_iff add_eq_0_iff)
    also have "(\<Sum>k<1. (bernoulli' (Suc k) / fact (Suc k)) *\<^sub>R (?fs k (real n) - ?fs k (real 0))) = 
                  ((n + a) powr - s - a powr - s) / 2"
      by (simp add: lessThan_nat_numeral scaleR_conv_of_real numeral_2_eq_2 [symmetric])
    also have "\<dots> = C + D n" by (simp add: C_def D_def field_simps)
    also have "integral {real 0..real n} (\<lambda>x. complex_of_real (x + a) powr - s) = I n - C'"
      using I by (simp add: has_integral_iff)
    also have "(\<Sum>i\<in>{0<..n}. of_real (real i + a) powr - s) = 
                 (\<Sum>i=0..n. of_real (real i + a) powr - s) - of_real a powr -s"
      using assms by (subst sum.head) auto
    also have "(\<Sum>i=0..n. of_real (real i + a) powr - s) = S n + of_real (real n + a) powr -s"
      unfolding S_def by (subst sum.last_plus) (auto simp: atLeast0LessThan)
    finally have "C - C' + C'' - D' n + D n + R n + (I n - I' n) = S n - I' n"
      by (simp add: algebra_simps S_def D'_def C''_def)
  }
  hence ev: "eventually (\<lambda>n. C - C' + C'' - D' n + D n + R n + (I n - I' n) = S n - I' n) at_top"
    by (intro eventually_mono[OF eventually_gt_at_top[of 0]]) auto

  have [simp]: "-1 - s = -s - 1" by simp
  {
    let ?C = "norm (pochhammer s 1)"
    have "R \<longlonglongrightarrow> R_lim" unfolding R_def R_lim_def of_nat_0
    proof (subst of_int_0 [symmetric], rule tendsto_EM_remainder)
      show "eventually (\<lambda>x. norm (?fs 1 x) \<le> ?C * (x + a) powr (-Re s - 1)) at_top"
        using eventually_ge_at_top[of 0]
        by eventually_elim (insert assms, auto simp: norm_mult norm_powr_real_powr)
    next
      fix x assume x: "x \<ge> real_of_int 0"
      have [simp]: "-numeral n - (x :: real) = -x - numeral n" for x n by (simp add: algebra_simps)
      show "((\<lambda>x. ?C / (-Re s) * (x + a) powr (-Re s)) has_real_derivative 
              ?C * (x + a) powr (- Re s - 1)) (at x within {real_of_int 0..})"
        using assms x by (auto intro!: derivative_eq_intros)
    next
      have "(\<lambda>y. ?C / (- Re s) * (a + real y) powr (- Re s)) \<longlonglongrightarrow> 0"
        by (intro tendsto_mult_right_zero tendsto_neg_powr filterlim_real_sequentially
                  filterlim_tendsto_add_at_top[OF tendsto_const]) (use assms in auto)
      thus "convergent (\<lambda>y. ?C / (- Re s) * (real y + a) powr (- Re s))"
        by (auto simp: add_ac convergent_def)
    qed (intro integrable_EM_remainder' continuous_intros, insert assms, auto simp: add_eq_0_iff)
  }
  moreover have "(\<lambda>n. I n - I' n) \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>n. (complex_of_real (real n + a) powr (1 - s) - 
                 of_real (real n) powr (1 - s)) / (1 - s)) \<longlonglongrightarrow> 0 / (1 - s)" 
      using assms(3-5) by (intro filterlim_compose[OF _ filterlim_real_sequentially]
                             tendsto_divide complex_powr_add_minus_powr_asymptotics) auto
    thus "(\<lambda>n. I n - I' n) \<longlonglongrightarrow> 0" by (simp add: I_def I'_def divide_simps)
  qed
  ultimately have "(\<lambda>n. C - C' + C'' - D' n + D n + R n + (I n - I' n)) 
                     \<longlonglongrightarrow> C - C' + C'' - 0 + 0 + R_lim + 0"
    unfolding D_def D'_def using assms
    by (intro tendsto_add tendsto_diff tendsto_const tendsto_mult_right_zero
              tendsto_neg_powr_complex_of_real filterlim_tendsto_add_at_top 
              filterlim_real_sequentially) auto
  also have "C - C' + C'' - 0 + 0 + R_lim + 0 = 
               (a powr - s / 2) + a powr (1 - s) / (s - 1) + R_lim"
    by (simp add: C_def C'_def C''_def field_simps)
  also have "\<dots> = hurwitz_zeta a s"
    using assms by (simp add: hurwitz_zeta_def pre_zeta_def pre_zeta_aux_def
                              R_lim_def scaleR_conv_of_real)
  finally have "(\<lambda>n. C - C' + C'' - D' n + D n + R n + (I n - I' n)) \<longlonglongrightarrow> hurwitz_zeta a s" .
  with ev show ?thesis
    by (blast intro: Lim_transform_eventually)
qed

lemma zeta_critical_strip:
  fixes s :: complex and a :: real
  defines "S \<equiv> (\<lambda>n. \<Sum>i=1..n. (of_nat i) powr - s)"
  defines "I \<equiv> (\<lambda>n. of_nat n powr (1 - s) / (1 - s))"
  assumes s: "Re s > 0" "s \<noteq> 1"
  shows   "(\<lambda>n. S n - I n) \<longlonglongrightarrow> zeta s"
proof -
  from hurwitz_zeta_critical_strip[OF s zero_less_one]
    have "(\<lambda>n. (\<Sum>i<n. complex_of_real (Suc i) powr - s) -
            of_nat n powr (1 - s) / (1 - s)) \<longlonglongrightarrow> hurwitz_zeta 1 s" by (simp add: add_ac)
  also have "(\<lambda>n. (\<Sum>i<n. complex_of_real (Suc i) powr -s)) = (\<lambda>n. (\<Sum>i=1..n. of_nat i powr -s))"
    by (intro ext sum.reindex_bij_witness[of _ "\<lambda>x. x - 1" Suc]) auto
  finally show ?thesis by (simp add: zeta_def S_def I_def)
qed


subsection \<open>The non-vanishing of $\zeta$ for $\mathfrak{R}(s) \geq 1$\<close>

text \<open>
  This proof is based on a sketch by Newman~\cite{newman1998analytic}, which was previously
  formalised in HOL Light by Harrison~\cite{harrison2009pnt}, albeit in a much more concrete
  and low-level style.

  Our aim here is to reproduce Newman's proof idea cleanly and on the same high level of
  abstraction.
\<close>
theorem zeta_Re_ge_1_nonzero:
  fixes s assumes "Re s \<ge> 1" "s \<noteq> 1"
  shows "zeta s \<noteq> 0"
proof (cases "Re s > 1")
  case False
  define a where "a = -Im s"
  from False assms have s [simp]: "s = 1 - \<i> * a" and a: "a \<noteq> 0"
    by (auto simp: complex_eq_iff a_def)
  show ?thesis
  proof
    assume "zeta s = 0"
    hence zero: "zeta (1 - \<i> * a) = 0" by simp
    with zeta_cnj[of "1 - \<i> * a"] have zero': "zeta (1 + \<i> * a) = 0" by simp

    \<comment> \<open>We define the function $Q(s) = \zeta(s)^2\zeta(s+ia)\zeta(s-ia)$ and its Dirichlet series.
        The objective will be to show that this function is entire and its Dirichlet series
        converges everywhere. Of course, $Q(s)$ has singularities at $1$ and $1\pm ia$, so we 
        need to show they can be removed.\<close>
    define Q Q_fds
      where "Q = (\<lambda>s. zeta s ^ 2 * zeta (s + \<i> * a) * zeta (s - \<i> * a))"
        and "Q_fds = fds_zeta ^ 2 * fds_shift (\<i> * a) fds_zeta * fds_shift (-\<i> * a) fds_zeta"  
    let ?sings = "{1, 1 + \<i> * a, 1 - \<i> * a}"
 
    \<comment> \<open>We show that @{term Q} is locally bounded everywhere. This is the case because the
        poles of $\zeta(s)$ cancel with the zeros of $\zeta(s\pm ia)$ and vice versa.
        This boundedness is then enough to show that @{term Q} has only removable singularities.\<close>
    have Q_bigo_1: "Q \<in> O[at s](\<lambda>_. 1)" for s
    proof -
      have Q_eq: "Q = (\<lambda>s. (zeta s * zeta (s + \<i> * a)) * (zeta s * zeta (s - \<i> * a)))"
        by (simp add: Q_def power2_eq_square mult_ac)

      \<comment> \<open>The singularity of $\zeta(s)$ at 1 gets cancelled by the zero of $\zeta(s-ia)$:\<close>
      have bigo1: "(\<lambda>s. zeta s * zeta (s - \<i> * a)) \<in> O[at 1](\<lambda>_. 1)"
        if "zeta (1 - \<i> * a) = 0" "a \<noteq> 0" for a :: real
      proof -
        have "(\<lambda>s. zeta (s - \<i> * a) - zeta (1 - \<i> * a)) \<in> O[at 1](\<lambda>s. s - 1)"
          using that
          by (intro taylor_bigo_linear holomorphic_on_imp_differentiable_at[of _ "-{1 + \<i> * a}"]
                    holomorphic_intros) (auto simp: complex_eq_iff)
        hence "(\<lambda>s. zeta s * zeta (s - \<i> * a)) \<in> O[at 1](\<lambda>s. 1 / (s - 1) * (s - 1))" 
          using that by (intro landau_o.big.mult zeta_bigo_at_1) simp_all
        also have "(\<lambda>s. 1 / (s - 1) * (s - 1)) \<in> \<Theta>[at 1](\<lambda>_. 1)"
          by (intro bigthetaI_cong) (auto simp: eventually_at_filter)
        finally show ?thesis .
      qed

      \<comment> \<open>The analogous result for $\zeta(s) \zeta(s+ia)$:\<close>
      have bigo1': "(\<lambda>s. zeta s * zeta (s + \<i> * a)) \<in> O[at 1](\<lambda>_. 1)"
        if "zeta (1 - \<i> * a) = 0" "a \<noteq> 0" for a :: real
        using bigo1[of  "-a"] that zeta_cnj[of "1 - \<i> * a"] by simp

      \<comment> \<open>The singularity of $\zeta(s-ia)$ gets cancelled by the zero of $\zeta(s)$:\<close>
      have bigo2: "(\<lambda>s. zeta s * zeta (s - \<i> * a)) \<in> O[at (1 + \<i> * a)](\<lambda>_. 1)"
        if "zeta (1 - \<i> * a) = 0" "a \<noteq> 0" for a :: real
      proof -
        have "(\<lambda>s. zeta s * zeta (s - \<i> * a)) \<in> O[filtermap (\<lambda>s. s + \<i> * a) (at 1)](\<lambda>_. 1)"
          using bigo1'[of a] that by (simp add: mult.commute landau_o.big.in_filtermap_iff)
        also have "filtermap (\<lambda>s. s + \<i> * a) (at 1) = at (1 + \<i> * a)"
          using filtermap_at_shift[of "-\<i> * a" 1] by simp
        finally show ?thesis .
      qed

      \<comment> \<open>Again, the analogous result for $\zeta(s) \zeta(s+ia)$:\<close>
      have bigo2': "(\<lambda>s. zeta s * zeta (s + \<i> * a)) \<in> O[at (1 - \<i> * a)](\<lambda>_. 1)"
        if "zeta (1 - \<i> * a) = 0" "a \<noteq> 0" for a :: real
        using bigo2[of "-a"] that zeta_cnj[of "1 - \<i> * a"] by simp

      \<comment> \<open>Now the final case distinction to show $Q(s)\in O(1)$ for all $s\in\mathbb{C}$:\<close>
      consider "s = 1" | "s = 1 + \<i> * a" | "s = 1 - \<i> * a" | "s \<notin> ?sings" by blast
      thus ?thesis
      proof cases
        case 1
        thus ?thesis unfolding Q_eq using zero zero' a
          by (auto intro: bigo1 bigo1' landau_o.big.mult_in_1)
      next
        case 2
        from a have "isCont (\<lambda>s. zeta s * zeta (s + \<i> * a)) (1 + \<i> * a)"
          by (auto intro!: continuous_intros)
        with 2 show ?thesis unfolding Q_eq using zero zero' a
          by (auto intro: bigo2 landau_o.big.mult_in_1 continuous_imp_bigo_1)
      next
        case 3
        from a have "isCont (\<lambda>s. zeta s * zeta (s - \<i> * a)) (1 - \<i> * a)"
          by (auto intro!: continuous_intros)
        with 3 show ?thesis unfolding Q_eq using zero zero' a
          by (auto intro: bigo2' landau_o.big.mult_in_1 continuous_imp_bigo_1)
      qed (auto intro!: continuous_imp_bigo_1 continuous_intros simp: Q_def complex_eq_iff)
    qed
  
    \<comment> \<open>Thus, we can remove the singularities from @{term Q} and extend it to an entire function.\<close>
    have "\<exists>Q'. Q' holomorphic_on UNIV \<and> (\<forall>z\<in>UNIV - ?sings. Q' z = Q z)"
      by (intro removable_singularities Q_bigo_1)
         (auto simp: Q_def complex_eq_iff intro!: holomorphic_intros)
    then obtain Q' where Q': "Q' holomorphic_on UNIV" "\<And>z. z \<notin> ?sings \<Longrightarrow> Q' z = Q z" by blast

    \<comment> \<open>@{term Q'} constitutes an analytic continuation of the Dirichlet series of @{term Q}.\<close>
    have eval_Q_fds: "eval_fds Q_fds s = Q' s" if "Re s > 1" for s
    proof -
      have "eval_fds Q_fds s = Q s" using that
        by (simp add: Q_fds_def Q_def eval_fds_mult eval_fds_power fds_abs_converges_mult 
                      fds_abs_converges_power eval_fds_zeta)
      also from that have "\<dots> = Q' s" by (subst Q') auto
      finally show ?thesis .
    qed
  
    \<comment> \<open>Since $\zeta(s)$ and $\zeta(s\pm ia)$ are completely multiplicative Dirichlet series,
        the logarithm of their product can be rewritten into the following nice form:\<close>
    have ln_Q_fds_eq: 
      "fds_ln 0 Q_fds = fds (\<lambda>k. of_real (2 * mangoldt k / ln k * (1 + cos (a * ln k))))"
    proof -
      note simps = fds_ln_mult[where l' = 0 and l'' = 0] fds_ln_power[where l' = 0]
                   fds_ln_prod[where l' = "\<lambda>_. 0"]
      have "fds_ln 0 Q_fds = 2 * fds_ln 0 fds_zeta + fds_shift (\<i> * a) (fds_ln 0 fds_zeta) + 
                               fds_shift (-\<i> * a) (fds_ln 0 fds_zeta)"
        by (auto simp: Q_fds_def simps)
      also have "completely_multiplicative_function (fds_nth (fds_zeta :: complex fds))"
        by standard auto
      hence "fds_ln (0 :: complex) fds_zeta = fds (\<lambda>n. mangoldt n /\<^sub>R ln (real n))"
        by (subst fds_ln_completely_multiplicative) (auto simp: fds_eq_iff)
      also have "2 * \<dots> + fds_shift (\<i> * a) \<dots> + fds_shift (-\<i> * a) \<dots> = 
                   fds (\<lambda>k. of_real (2 * mangoldt k / ln k * (1 + cos (a * ln k))))"
        (is "?a = ?b")
      proof (intro fds_eqI, goal_cases)
        case (1 n)
        then consider "n = 1" | "n > 1" by force
        hence "fds_nth ?a n = mangoldt n / ln (real n) * (2 + (n powr (\<i> * a) + n powr (-\<i> * a)))"
          by cases (auto simp: field_simps scaleR_conv_of_real numeral_fds)
        also have "n powr (\<i> * a) + n powr (-\<i> * a) = 2 * cos (of_real (a * ln n))"
          using 1 by (subst cos_exp_eq) (simp_all add: powr_def algebra_simps)
        also have "mangoldt n / ln (real n) * (2 + \<dots>) = 
                     of_real (2 * mangoldt n / ln n * (1 + cos (a * ln n)))"
          by (subst cos_of_real) simp_all
        finally show ?case by (simp add: fds_nth_fds')
      qed
      finally show ?thesis .
    qed
    \<comment> \<open>It is then obvious that this logarithm series has non-negative real coefficients.\<close>
    also have "nonneg_dirichlet_series \<dots>"
    proof (standard, goal_cases)
      case (1 n)
      from cos_ge_minus_one[of "a * ln n"] have "1 + cos (a * ln (real n)) \<ge> 0" by linarith
      thus ?case using 1
        by (cases "n = 0")
           (auto simp: complex_nonneg_Reals_iff fds_nth_fds' mangoldt_nonneg
                 intro!: divide_nonneg_nonneg mult_nonneg_nonneg)
    qed
    \<comment> \<open>Therefore, the original series also has non-negative real coefficients.\<close>
    finally have nonneg: "nonneg_dirichlet_series Q_fds"
      by (rule nonneg_dirichlet_series_lnD) (auto simp: Q_fds_def)
  
    \<comment> \<open>By the Pringsheim--Landau theorem, a Dirichlet series with non-negative coefficnets that 
        can be analytically continued to the entire complex plane must converge everywhere, i.\,e.\ 
        its abscissa of (absolute) convergence is $-\infty$:\<close>
    have abscissa_Q_fds: "abs_conv_abscissa Q_fds \<le> 1"
      unfolding Q_fds_def by (auto intro!: abs_conv_abscissa_mult_leI abs_conv_abscissa_power_leI)
    with nonneg and eval_Q_fds and \<open>Q' holomorphic_on UNIV\<close>
      have abscissa: "abs_conv_abscissa Q_fds = -\<infinity>"
        by (intro entire_continuation_imp_abs_conv_abscissa_MInfty[where c = 1 and g = Q'])
           (auto simp: one_ereal_def)
  
    \<comment> \<open>This now leads to a contradiction in a very obvious way. If @{term Q_fds} is
        absolutely convergent, then the subseries corresponding to powers of 2 (\i.e.
        we delete all summands $a_n / n ^ s$ where $n$ is not a power of 2 from the sum) is
        also absolutely convergent. We denote this series with $R$.\<close>
    define R_fds where "R_fds = fds_primepow_subseries 2 Q_fds"
    have "conv_abscissa R_fds \<le> abs_conv_abscissa R_fds" by (rule conv_le_abs_conv_abscissa)
    also have "abs_conv_abscissa R_fds \<le> abs_conv_abscissa Q_fds"
      unfolding R_fds_def by (rule abs_conv_abscissa_restrict)
    also have "\<dots> = -\<infinity>" by (simp add: abscissa)
    finally have abscissa': "conv_abscissa R_fds = -\<infinity>" by simp
  
    \<comment> \<open>Since $\zeta(s)$ and $\zeta(s \pm ia)$ have an Euler product expansion for 
        $\mathfrak{R}(s) > 1$, we have
          \[R(s) = (1 - 2^{-s})^-2 (1 - 2^{-s+ia})^{-1} (1 - 2^{-s-ia})^{-1}\]
        there, and since $R$ converges everywhere and the right-hand side is holomorphic for
        $\mathfrak{R}(s) > 0$, the equation is also valid for all $s$ with $\mathfrak{R}(s) > 0$
        by analytic continuation.\<close>
    have eval_R: "eval_fds R_fds s = 
                   1 / ((1 - 2 powr -s) ^ 2 * (1 - 2 powr (-s + \<i> * a)) * (1 - 2 powr (-s - \<i> * a)))"
      (is "_ = ?f s") if "Re s > 0" for s
    proof -
      show ?thesis
      proof (rule analytic_continuation_open[where f = "eval_fds R_fds"])
        show "?f holomorphic_on {s. Re s > 0}"
          by (intro holomorphic_intros) (auto simp: powr_def exp_eq_1 Ln_Reals_eq)
      next
        fix z assume z: "z \<in> {s. Re s > 1}"
        have [simp]: "completely_multiplicative_function (fds_nth fds_zeta)" by standard auto
        thus "eval_fds R_fds z = ?f z" using z
          by (simp add: R_fds_def Q_fds_def eval_fds_mult eval_fds_power fds_abs_converges_mult 
                fds_abs_converges_power fds_primepow_subseries_euler_product_cm divide_simps
                powr_minus powr_diff powr_add fds_abs_summable_zeta)
      qed (insert that abscissa', auto intro!: exI[of _ 2] convex_connected open_halfspace_Re_gt
                                               convex_halfspace_Re_gt holomorphic_intros)
    qed
  
    \<comment> \<open>We now clearly have a contradiction: $R(s)$, being entire, is continuous everywhere,
        while the function on the right-hand side clearly has a pole at $0$.\<close>
    show False
    proof (rule not_tendsto_and_filterlim_at_infinity)
      have "((\<lambda>b. (1-2 powr - b)\<^sup>2 * (1 - 2 powr (-b+\<i>*a)) * (1 - 2 powr (-b-\<i>*a))) \<longlongrightarrow> 0) 
              (at 0 within {s. Re s > 0})"
        (is "filterlim ?f' _ _") by (intro tendsto_eq_intros) (auto)
      moreover have "eventually (\<lambda>s. s \<in> {s. Re s > 0}) (at 0 within {s. Re s > 0})"
        by (auto simp: eventually_at_filter)
      hence "eventually (\<lambda>s. ?f' s \<noteq> 0) (at 0 within {s. Re s > 0})"
        by eventually_elim (auto simp: powr_def exp_eq_1 Ln_Reals_eq)
      ultimately have "filterlim ?f' (at 0) (at 0 within {s. Re s > 0})" by (simp add: filterlim_at)
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
qed (fact zeta_Re_gt_1_nonzero)


subsection \<open>Special values of the $\zeta$ functions\<close>

theorem hurwitz_zeta_neg_of_nat: 
  assumes "a > 0"
  shows   "hurwitz_zeta a (-of_nat n) = -bernpoly (Suc n) a / of_nat (Suc n)"
proof -
  have "-of_nat n \<noteq> (1::complex)" by (simp add: complex_eq_iff)
  hence "hurwitz_zeta a (-of_nat n) = 
           pre_zeta a (-of_nat n) + a powr real (Suc n) / (-of_nat (Suc n))"
    unfolding zeta_def hurwitz_zeta_def using assms by (simp add: powr_of_real [symmetric])
  also have "a powr real (Suc n) / (-of_nat (Suc n)) = - (a powr real (Suc n) / of_nat (Suc n))"
    by (simp add: divide_simps del: of_nat_Suc)
  also have "a powr real (Suc n) = a ^ Suc n"
    using assms by (intro powr_realpow)
  also have "pre_zeta a (-of_nat n) = pre_zeta_aux (Suc n) a (- of_nat n)"
    using assms by (intro pre_zeta_aux_eq_pre_zeta [symmetric]) auto
  also have "\<dots> = of_real a powr of_nat n / 2 +
                    (\<Sum>i = 1..Suc n. (bernoulli (2 * i) / fact (2 * i)) *\<^sub>R
                       (pochhammer (- of_nat n) (2 * i - 1) *
                       of_real a powr (of_nat n - of_nat (2 * i - 1)))) +
                    EM_remainder (Suc (2 * Suc n)) (\<lambda>x. - (pochhammer (- of_nat n)
                      (2*n+3) * of_real (x + a) powr (- of_nat n - 3))) 0"
    (is "_ = ?B + sum (\<lambda>n. ?f (2 * n)) _ + _") 
    unfolding pre_zeta_aux_def by (simp add: add_ac eval_nat_numeral)
  also have "?B = of_real (a ^ n) / 2" 
    using assms by (subst powr_Reals_eq) (auto simp: powr_realpow)
  also have "pochhammer (-of_nat n :: complex) (2*n+3) = 0"
    by (subst pochhammer_eq_0_iff) auto
  finally have "hurwitz_zeta a (-of_nat n) = 
                  - (a ^ Suc n / of_nat (Suc n)) + (a ^ n / 2 + sum (\<lambda>n. ?f (2 * n)) {1..Suc n})"
    by simp

  also have "sum (\<lambda>n. ?f (2 * n)) {1..Suc n} = sum ?f ((*) 2 ` {1..Suc n})"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>i. i div 2" "\<lambda>i. 2*i"]) auto
  also have "\<dots> = (\<Sum>i=2..2*n+2. ?f i)"
  proof (intro sum.mono_neutral_left ballI, goal_cases)
    case (3 i)
    hence "odd i" "i \<noteq> 1" by (auto elim!: evenE)
    thus ?case by (simp add: bernoulli_odd_eq_0)
  qed auto
  also have "\<dots> = (\<Sum>i=2..Suc n. ?f i)"
  proof (intro sum.mono_neutral_right ballI, goal_cases)
    case (3 i)
    hence "pochhammer (-of_nat n :: complex) (i - 1) = 0"
      by (subst pochhammer_eq_0_iff) auto
    thus ?case by simp
  qed auto
  also have "\<dots> = (\<Sum>i=Suc 1..Suc n. -of_real (real (Suc n choose i) * bernoulli i * 
                     a ^ (Suc n - i)) / of_nat (Suc n))"
    (is "sum ?lhs _ = sum ?f _")
  proof (intro sum.cong, goal_cases)
    case (2 i)
    hence "of_nat n - of_nat (i - 1) = (of_nat (Suc n - i) :: complex)"
      by (auto simp: of_nat_diff)
    also have "of_real a powr \<dots> = of_real (a ^ (Suc n - i))"
      using 2 assms by (subst powr_nat) auto
    finally have A: "of_real a powr (of_nat n - of_nat (i - 1)) = \<dots>" .
    have "pochhammer (-of_nat n) (i - 1) = complex_of_real (pochhammer (-real n) (i - 1))"
      by (simp add: pochhammer_of_real [symmetric])
    also have "pochhammer (-real n) (i - 1) = pochhammer (-of_nat (Suc n)) i / (-1 - real n)"
      using 2 by (subst (2) pochhammer_rec_if) auto
    also have "-1 - real n = -real (Suc n)" by simp
    finally have B: "pochhammer (-of_nat n) (i - 1) = 
                    -complex_of_real (pochhammer (-real (Suc n)) i / real (Suc n))"
      by (simp del: of_nat_Suc)
    have "?lhs i = -complex_of_real (bernoulli i * pochhammer (-real (Suc n)) i / fact i * 
                      a ^ (Suc n - i)) / of_nat (Suc n)"
      by (simp only: A B) (simp add: scaleR_conv_of_real)
    also have "bernoulli i * pochhammer (-real (Suc n)) i / fact i =
                 (real (Suc n) gchoose i) * bernoulli i" using 2
      by (subst gbinomial_pochhammer) (auto simp: minus_one_power_iff bernoulli_odd_eq_0)
    also have "real (Suc n) gchoose i = Suc n choose i"
      by (subst binomial_gbinomial) auto
    finally show ?case by simp
  qed auto
  also have "a ^ n / 2 + sum ?f {Suc 1..Suc n} = sum ?f {1..Suc n}"
    by (subst (2) sum.atLeast_Suc_atMost) (simp_all add: scaleR_conv_of_real del: of_nat_Suc)
  also have "-(a ^ Suc n / of_nat (Suc n)) + sum ?f {1..Suc n} = sum ?f {0..Suc n}"
    by (subst (2) sum.atLeast_Suc_atMost) (simp_all add: scaleR_conv_of_real)
  also have "\<dots> = - bernpoly (Suc n) a / of_nat (Suc n)"
    unfolding sum_negf sum_divide_distrib [symmetric] by (simp add: bernpoly_def atLeast0AtMost)
  finally show ?thesis .
qed

lemma hurwitz_zeta_0 [simp]: "a > 0 \<Longrightarrow> hurwitz_zeta a 0 = 1 / 2 - a"
  using hurwitz_zeta_neg_of_nat[of a 0] by (simp add: bernpoly_def)

lemma zeta_0 [simp]: "zeta 0 = -1 / 2"
  by (simp add: zeta_def)

theorem zeta_neg_of_nat: 
  "zeta (-of_nat n) = -of_real (bernoulli' (Suc n)) / of_nat (Suc n)"
  unfolding zeta_def by (simp add: hurwitz_zeta_neg_of_nat bernpoly_1')

corollary zeta_trivial_zero:
  assumes "even n" "n \<noteq> 0"
  shows   "zeta (-of_nat n) = 0"
  using zeta_neg_of_nat[of n] assms by (simp add: bernoulli'_odd_eq_0)

theorem zeta_even_nat: 
  "zeta (2 * of_nat n) = 
     of_real ((-1) ^ Suc n * bernoulli (2 * n) * (2 * pi) ^ (2 * n) / (2 * fact (2 * n)))"
proof (cases "n = 0")
  case False
  hence "(\<lambda>k. 1 / of_nat (Suc k) ^ (2 * n)) sums zeta (of_nat (2 * n))"
    by (intro sums_zeta_nat) auto
  from sums_unique2 [OF this nat_even_power_sums_complex] False show ?thesis by simp
qed (insert zeta_neg_of_nat[of 0], simp_all)

corollary zeta_even_numeral: 
  "zeta (numeral (Num.Bit0 n)) = of_real
     ((- 1) ^ Suc (numeral n) * bernoulli (numeral (num.Bit0 n)) *
     (2 * pi) ^ numeral (num.Bit0 n) / (2 * fact (numeral (num.Bit0 n))))" (is "_ = ?rhs")
proof -
  have *: "(2 * numeral n :: nat) = numeral (Num.Bit0 n)"
    by (subst numeral.numeral_Bit0, subst mult_2, rule refl)
  have "numeral (Num.Bit0 n) = (2 * numeral n :: complex)"
    by (subst numeral.numeral_Bit0, subst mult_2, rule refl)
  also have "\<dots> = 2 * of_nat (numeral n)" by (simp only: of_nat_numeral of_nat_mult)
  also have "zeta \<dots> = ?rhs" by (subst zeta_even_nat) (simp only: *)
  finally show ?thesis .
qed

corollary zeta_neg_even_numeral [simp]: "zeta (-numeral (Num.Bit0 n)) = 0"
proof -
  have "-numeral (Num.Bit0 n) = (-of_nat (numeral (Num.Bit0 n)) :: complex)"
    by simp
  also have "zeta \<dots> = 0"
  proof (rule zeta_trivial_zero)
    have "numeral (Num.Bit0 n) = (2 * numeral n :: nat)"
      by (subst numeral.numeral_Bit0, subst mult_2, rule refl)
    also have "even \<dots>" by (rule dvd_triv_left)
    finally show "even (numeral (Num.Bit0 n) :: nat)" .
  qed auto
  finally show ?thesis .
qed

corollary zeta_neg_numeral:
  "zeta (-numeral n) = 
     -of_real (bernoulli' (numeral (Num.inc n)) / numeral (Num.inc n))"
proof -
  have "-numeral n = (- of_nat (numeral n) :: complex)" 
    by simp
  also have "zeta \<dots> = -of_real (bernoulli' (numeral (Num.inc n)) / numeral (Num.inc n))"
    by (subst zeta_neg_of_nat) (simp add: numeral_inc)
  finally show ?thesis .
qed

corollary zeta_neg1: "zeta (-1) = - 1 / 12"
  using zeta_neg_of_nat[of 1] by (simp add: eval_bernoulli)

corollary zeta_neg3: "zeta (-3) = 1 / 120"
  by (simp add: zeta_neg_numeral)

corollary zeta_neg5: "zeta (-5) = - 1 / 252"
  by (simp add: zeta_neg_numeral)

corollary zeta_2: "zeta 2 = pi ^ 2 / 6"
  by (simp add: zeta_even_numeral)

corollary zeta_4: "zeta 4 = pi ^ 4 / 90"
  by (simp add: zeta_even_numeral fact_num_eq_if)

corollary zeta_6: "zeta 6 = pi ^ 6 / 945"
  by (simp add: zeta_even_numeral fact_num_eq_if)

corollary zeta_8: "zeta 8 = pi ^ 8 / 9450"
  by (simp add: zeta_even_numeral fact_num_eq_if)


subsection \<open>Integral relation between $\Gamma$ and $\zeta$ function\<close>

lemma
  assumes z: "Re z > 0" and a: "a > 0"
  shows   Gamma_hurwitz_zeta_aux_integral: 
            "Gamma z / (of_nat n + of_real a) powr z = 
               (\<integral>s\<in>{0<..}. (s powr (z - 1) / exp ((n+a) * s)) \<partial>lebesgue)"
    and   Gamma_hurwitz_zeta_aux_integrable:
            "set_integrable lebesgue {0<..} (\<lambda>s. s powr (z - 1) / exp ((n+a) * s))"
proof -
  note integrable = absolutely_integrable_Gamma_integral' [OF z]
  let ?INT = "set_lebesgue_integral lebesgue {0<..} :: (real \<Rightarrow> complex) \<Rightarrow> complex"
  let ?INT' = "set_lebesgue_integral lebesgue {0<..} :: (real \<Rightarrow> real) \<Rightarrow> real"

  have meas1: "set_borel_measurable lebesgue {0<..} 
                 (\<lambda>x. of_real x powr (z - 1) / of_real (exp ((n+a) * x)))"
    unfolding set_borel_measurable_def
    by (intro measurable_completion, subst measurable_lborel2, 
        intro borel_measurable_continuous_on_indicator) (auto intro!: continuous_intros)
  show integrable1: "set_integrable lebesgue {0<..} 
                       (\<lambda>s. s powr (z - 1) / exp ((n+a) * s))"
    using assms by (intro absolutely_integrable_Gamma_integral) auto
  from assms have pos: "0 < real n + a" by (simp add: add_nonneg_pos)
  hence "complex_of_real 0 \<noteq> of_real (real n + a)" by (simp only: of_real_eq_iff)
  also have "complex_of_real (real n + a) = of_nat n + of_real a" by simp
  finally have nz: "\<dots> \<noteq> 0" by auto

  have "((\<lambda>t. complex_of_real t powr (z - 1) / of_real (exp t)) has_integral Gamma z) {0<..}"
    by (rule Gamma_integral_complex') fact+
  hence "Gamma z = ?INT (\<lambda>t. t powr (z - 1) / of_real (exp t))"
    using set_lebesgue_integral_eq_integral(2) [OF integrable] 
    by (simp add: has_integral_iff exp_of_real)
  also have "lebesgue = density (distr lebesgue lebesgue (\<lambda>t. (real n+a) * t)) 
                          (\<lambda>x. ennreal (real n+a))"
    using lebesgue_real_scale[of "real n + a"] pos by auto
  also have "set_lebesgue_integral \<dots> {0<..} (\<lambda>t. of_real t powr (z - 1) / of_real (exp t)) = 
               set_lebesgue_integral (distr lebesgue lebesgue (\<lambda>t. (real n + a) * t)) {0<..}
                 (\<lambda>t. (real n + a) * t powr (z - 1) / exp t)" using integrable pos
    unfolding set_lebesgue_integral_def
    by (subst integral_density) (simp_all add: exp_of_real algebra_simps scaleR_conv_of_real set_integrable_def)
  also have "\<dots> = ?INT (\<lambda>s. (n + a) * (of_real (n+a) * of_real s) powr (z - 1) / 
                    of_real (exp ((n+a) * s)))"
    unfolding set_lebesgue_integral_def
  proof (subst integral_distr)
    show "(*) (real n + a) \<in> lebesgue \<rightarrow>\<^sub>M lebesgue"
      using lebesgue_measurable_scaling[of "real n + a", where ?'a = real]
      unfolding real_scaleR_def .
  next
    have "(\<lambda>x. (n+a) * (indicator {0<..} x *\<^sub>R (of_real x powr (z - 1) / of_real (exp x)))) 
             \<in> lebesgue \<rightarrow>\<^sub>M borel" 
      using integrable unfolding set_integrable_def by (intro borel_measurable_times) simp_all
    thus "(\<lambda>x. indicator {0<..} x *\<^sub>R
           (complex_of_real (real n + a) * complex_of_real x powr (z - 1) / exp x))
    \<in> borel_measurable lebesgue" by simp
  qed (intro Bochner_Integration.integral_cong refl, insert pos, 
       auto simp: indicator_def zero_less_mult_iff)
  also have "\<dots> = ?INT (\<lambda>s. ((n+a) powr z) * (s powr (z - 1) / exp ((n+a) * s)))" using pos
    by (intro set_lebesgue_integral_cong refl allI impI, simp, subst powr_times_real)
       (auto simp: powr_diff)
  also have "\<dots> = (n + a) powr z * ?INT (\<lambda>s. s powr (z - 1) / exp ((n+a) * s))"
    unfolding set_lebesgue_integral_def
    by (subst integral_mult_right_zero [symmetric]) simp_all
  finally show "Gamma z / (of_nat n + of_real a) powr z = 
                  ?INT (\<lambda>s. s powr (z - 1) / exp ((n+a) * s))" 
    using nz by (auto simp add: field_simps)
qed

lemma
  assumes x: "x > 0" and "a > 0"
  shows   Gamma_hurwitz_zeta_aux_integral_real: 
            "Gamma x / (real n + a) powr x = 
               set_lebesgue_integral lebesgue {0<..} 
               (\<lambda>s. s powr (x - 1) / exp ((real n + a) * s))"
    and   Gamma_hurwitz_zeta_aux_integrable_real:
            "set_integrable lebesgue {0<..} (\<lambda>s. s powr (x - 1) / exp ((real n + a) * s))"
proof -
  show "set_integrable lebesgue {0<..} (\<lambda>s. s powr (x - 1) / exp ((real n + a) * s))"
    using absolutely_integrable_Gamma_integral[of "of_real x" "real n + a"]
    unfolding set_integrable_def
  proof (rule Bochner_Integration.integrable_bound, goal_cases)
    case 3
    have "set_integrable lebesgue {0<..} (\<lambda>xa. complex_of_real xa powr (of_real x - 1) / 
              of_real (exp ((n + a) * xa)))"
      using assms by (intro Gamma_hurwitz_zeta_aux_integrable) auto
    also have "?this \<longleftrightarrow> integrable lebesgue
                 (\<lambda>s. complex_of_real (indicator {0<..} s *\<^sub>R (s powr (x - 1) / (exp ((n+a) * s)))))"
      unfolding set_integrable_def
      by (intro Bochner_Integration.integrable_cong refl) (auto simp: powr_Reals_eq indicator_def)
    finally have "set_integrable lebesgue {0<..} (\<lambda>s. s powr (x - 1) / exp ((n+a) * s))"
      unfolding set_integrable_def complex_of_real_integrable_eq .
    thus ?case
      by (simp add: set_integrable_def)
  qed (insert assms, auto intro!: AE_I2 simp: indicator_def norm_divide norm_powr_real_powr)
  from Gamma_hurwitz_zeta_aux_integral[of "of_real x" a n] and assms
    have "of_real (Gamma x / (real n + a) powr x) = set_lebesgue_integral lebesgue {0<..} 
            (\<lambda>s. complex_of_real s powr (of_real x - 1) / of_real (exp ((n+a) * s)))" (is "_ = ?I")
      by (auto simp: Gamma_complex_of_real powr_Reals_eq)
  also have "?I = lebesgue_integral lebesgue
                    (\<lambda>s. of_real (indicator {0<..} s *\<^sub>R (s powr (x - 1) / exp ((n+a) * s))))"
    unfolding set_lebesgue_integral_def
    using assms by (intro Bochner_Integration.integral_cong refl) 
                   (auto simp: indicator_def powr_Reals_eq)
  also have "\<dots> = of_real (set_lebesgue_integral lebesgue {0<..} 
                    (\<lambda>s. s powr (x - 1) / exp ((n+a) * s)))"
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_complex_of_real)
  finally show "Gamma x / (real n + a) powr x = set_lebesgue_integral lebesgue {0<..} 
                  (\<lambda>s. s powr (x - 1) / exp ((real n + a) * s))"
    by (subst (asm) of_real_eq_iff)
qed

theorem
  assumes "Re z > 1" and "a > (0::real)"
  shows   Gamma_times_hurwitz_zeta_integral: "Gamma z * hurwitz_zeta a z =
            (\<integral>x\<in>{0<..}. (of_real x powr (z - 1) * of_real (exp (-a*x) / (1 - exp (-x)))) \<partial>lebesgue)"
    and   Gamma_times_hurwitz_zeta_integrable:
            "set_integrable lebesgue {0<..} 
               (\<lambda>x. of_real x powr (z - 1) * of_real (exp (-a*x) / (1 - exp (-x))))"
proof -
  from assms have z: "Re z > 0" by simp
  let ?INT = "set_lebesgue_integral lebesgue {0<..} :: (real \<Rightarrow> complex) \<Rightarrow> complex"
  let ?INT' = "set_lebesgue_integral lebesgue {0<..} :: (real \<Rightarrow> real) \<Rightarrow> real"

  have 1: "complex_set_integrable lebesgue {0<..} 
            (\<lambda>x. of_real x powr (z - 1) / of_real (exp ((real n + a) * x)))" for n
      by (rule Gamma_hurwitz_zeta_aux_integrable) (use assms in simp_all)
  have 2: "summable (\<lambda>n. norm (indicator {0<..} s *\<^sub>R (of_real s powr (z - 1) / 
             of_real (exp ((n + a) * s)))))" for s
  proof (cases "s > 0")
    case True
    hence "summable (\<lambda>n. norm (of_real s powr (z - 1)) * exp (-a * s) * exp (-s) ^ n)"
      using assms by (intro summable_mult summable_geometric) simp_all
    with True show ?thesis
      by (simp add: norm_mult norm_divide exp_add exp_diff
                    exp_minus field_simps exp_of_nat_mult [symmetric])
  qed simp_all
  have 3: "summable (\<lambda>n. \<integral>x. norm (indicator {0<..} x *\<^sub>R (complex_of_real x powr (z - 1) /
                            complex_of_real (exp ((n + a) * x)))) \<partial>lebesgue)"
  proof -
    have "summable (\<lambda>n. Gamma (Re z) * (real n + a) powr -Re z)"
      using assms by (intro summable_mult summable_hurwitz_zeta_real) simp_all
    also have "?this \<longleftrightarrow> summable (\<lambda>n. ?INT' (\<lambda>s. norm (of_real s powr (z - 1) / 
                                       of_real (exp ((n+a) * s)))))"
    proof (intro summable_cong always_eventually allI, goal_cases)
      case (1 n)
      have "Gamma (Re z) * (real n + a) powr -Re z = Gamma (Re z) / (real n + a) powr Re z"
        by (subst powr_minus) (simp_all add: field_simps)
      also from assms have "\<dots> = (\<integral>x\<in>{0<..}. (x powr (Re z-1) / exp ((n+a) * x)) \<partial>lebesgue)"
        by (subst Gamma_hurwitz_zeta_aux_integral_real) simp_all
      also have "\<dots> = (\<integral>xa\<in>{0<..}. norm (of_real xa powr (z-1) / of_real (exp ((n+a) * xa)))
                         \<partial>lebesgue)"
        unfolding set_lebesgue_integral_def
        by (intro Bochner_Integration.integral_cong refl)
          (auto simp: indicator_def norm_divide norm_powr_real_powr)
      finally show ?case .
    qed
    finally show ?thesis
      by (simp add: set_lebesgue_integral_def)
  qed

  have sum_eq: "(\<Sum>n. indicator {0<..} s *\<^sub>R (of_real s powr (z - 1) / of_real (exp ((n+a) * s)))) = 
                   indicator {0<..} s *\<^sub>R (of_real s powr (z - 1) * 
                     of_real (exp (-a * s) / (1 - exp (-s))))" for s
  proof (cases "s > 0")
    case True
    hence "(\<Sum>n. indicator {0..} s *\<^sub>R (of_real s powr (z - 1) / of_real (exp ((n+a) * s)))) =
             (\<Sum>n. of_real s powr (z - 1) * of_real (exp (-a * s)) * of_real (exp (-s)) ^ n)"
      by (intro suminf_cong) 
         (auto simp: exp_add exp_minus exp_of_nat_mult [symmetric] field_simps of_real_exp)
    also have "(\<Sum>n. of_real s powr (z - 1) * of_real (exp (-a * s)) * of_real (exp (-s)) ^ n) =
                 of_real s powr (z - 1) * of_real (exp (-a * s)) * (\<Sum>n. of_real (exp (-s)) ^ n)"
      using True by (intro suminf_mult summable_geometric) simp_all
    also have "(\<Sum>n. complex_of_real (exp (-s)) ^ n) = 1 / (1 - of_real (exp (-s)))"
      using True by (intro suminf_geometric) auto
    also have "of_real s powr (z - 1) * of_real (exp (-a * s)) * \<dots> = 
                 of_real s powr (z - 1) * of_real (exp (-a * s) / (1 - exp (-s)))" using \<open>a > 0\<close>
      by (auto simp add: divide_simps exp_minus)
    finally show ?thesis using True by simp
  qed simp_all

  show "set_integrable lebesgue {0<..} 
          (\<lambda>x. of_real x powr (z - 1) * of_real (exp (-a*x) / (1 - exp (-x))))"
    using 1 unfolding sum_eq [symmetric] set_integrable_def 
    by (intro integrable_suminf[OF _ AE_I2] 2 3)

  have "(\<lambda>n. ?INT (\<lambda>s. s powr (z - 1) / exp ((n+a) * s))) sums lebesgue_integral lebesgue
            (\<lambda>s. \<Sum>n. indicator {0<..} s *\<^sub>R (s powr (z - 1) / exp ((n+a) * s)))" (is "?A sums ?B")
    using 1 unfolding set_lebesgue_integral_def set_integrable_def
    by (rule sums_integral[OF _ AE_I2[OF 2] 3])
  also have "?A = (\<lambda>n. Gamma z * (n + a) powr -z)"
    using assms by (subst Gamma_hurwitz_zeta_aux_integral [symmetric]) 
                   (simp_all add: powr_minus divide_simps)
  also have "?B = ?INT (\<lambda>s. of_real s powr (z - 1) * of_real (exp (-a * s) / (1 - exp (-s))))"
    unfolding sum_eq set_lebesgue_integral_def ..
  finally have "(\<lambda>n. Gamma z * (of_nat n + of_real a) powr -z) sums
                  ?INT (\<lambda>x. of_real x powr (z - 1) * of_real (exp (-a * x) / (1 - exp (-x))))" 
    by simp
  moreover have "(\<lambda>n. Gamma z * (of_nat n + of_real a) powr -z) sums (Gamma z * hurwitz_zeta a z)"
    using assms by (intro sums_mult sums_hurwitz_zeta) simp_all
  ultimately show "Gamma z * hurwitz_zeta a z = 
                     (\<integral>x\<in>{0<..}. (of_real x powr (z - 1) * 
                        of_real (exp (-a * x) / (1 - exp (-x)))) \<partial>lebesgue)"
    by (rule sums_unique2 [symmetric])
qed

corollary
  assumes "Re z > 1"
  shows   Gamma_times_zeta_integral: "Gamma z * zeta z =
            (\<integral>x\<in>{0<..}. (of_real x powr (z - 1) / of_real (exp x - 1)) \<partial>lebesgue)" (is ?th1)
    and   Gamma_times_zeta_integrable:
            "set_integrable lebesgue {0<..} 
               (\<lambda>x. of_real x powr (z - 1) / of_real (exp x - 1))" (is ?th2)
proof -
  have *: "(\<lambda>x. indicator {0<..} x *\<^sub>R (of_real x powr (z - 1) * 
                of_real (exp (-x) / (1 - exp (-x))))) =
             (\<lambda>x. indicator {0<..} x *\<^sub>R (of_real x powr (z - 1) / of_real (exp x - 1)))"
    by (intro ext) (simp add: field_simps exp_minus indicator_def)
  from Gamma_times_hurwitz_zeta_integral [OF assms zero_less_one] and *
    show ?th1 by (simp add: zeta_def set_lebesgue_integral_def)
  from Gamma_times_hurwitz_zeta_integrable [OF assms zero_less_one] and *
    show ?th2 by (simp add: zeta_def set_integrable_def)
qed

corollary hurwitz_zeta_integral_Gamma_def:
  assumes "Re z > 1" "a > 0"
  shows   "hurwitz_zeta a z = 
             rGamma z * (\<integral>x\<in>{0<..}. (of_real x powr (z - 1) * 
               of_real (exp (-a * x) / (1 - exp (-x)))) \<partial>lebesgue)"
proof -
  from assms have "Gamma z \<noteq> 0" 
    by (subst Gamma_eq_zero_iff) (auto elim!: nonpos_Ints_cases)
  with Gamma_times_hurwitz_zeta_integral [OF assms] show ?thesis
    by (simp add: rGamma_inverse_Gamma field_simps)
qed

corollary zeta_integral_Gamma_def:
  assumes "Re z > 1"
  shows   "zeta z =
             rGamma z * (\<integral>x\<in>{0<..}. (of_real x powr (z - 1) / of_real (exp x - 1)) \<partial>lebesgue)"
proof -
  from assms have "Gamma z \<noteq> 0" 
    by (subst Gamma_eq_zero_iff) (auto elim!: nonpos_Ints_cases)
  with Gamma_times_zeta_integral [OF assms] show ?thesis
    by (simp add: rGamma_inverse_Gamma field_simps)
qed

lemma Gamma_times_zeta_has_integral:
  assumes "Re z > 1"
  shows   "((\<lambda>x. x powr (z - 1) / (of_real (exp x) - 1)) has_integral (Gamma z * zeta z)) {0<..}"
    (is "(?f has_integral _) _")
proof -
  have "(?f has_integral set_lebesgue_integral lebesgue {0<..} ?f) {0<..}"
    using Gamma_times_zeta_integrable[OF assms]
    by (intro has_integral_set_lebesgue) auto
  also have "set_lebesgue_integral lebesgue {0<..} ?f = Gamma z * zeta z"
    using Gamma_times_zeta_integral[OF assms] by simp
  finally show ?thesis .
qed

lemma Gamma_times_zeta_has_integral_real:
  fixes z :: real
  assumes "z > 1"
  shows   "((\<lambda>x. x powr (z - 1) / (exp x - 1)) has_integral (Gamma z * Re (zeta z))) {0<..}"
proof -
  from assms have *: "Re (of_real z) > 1" by simp
  have "((\<lambda>x. Re (complex_of_real x powr (complex_of_real z - 1)) / (exp x - 1)) has_integral
           Gamma z * Re (zeta (complex_of_real z))) {0<..}"
    using has_integral_linear[OF Gamma_times_zeta_has_integral[OF *] bounded_linear_Re] 
    by (simp add: o_def Gamma_complex_of_real)
  also have "?this \<longleftrightarrow> ?thesis"
    using assms by (intro has_integral_cong) (auto simp: powr_Reals_eq)
  finally show ?thesis .
qed

lemma Gamma_integral_real':
  assumes x: "x > (0 :: real)"
  shows   "((\<lambda>t. t powr (x - 1) / exp t) has_integral Gamma x) {0<..}"
  using Gamma_integral_real[OF assms] by (subst has_integral_closure [symmetric]) auto


subsection \<open>An analytic proof of the infinitude of primes\<close>

text \<open>
  We can now also do an analytic proof of the infinitude of primes.
\<close>
lemma primes_infinite_analytic: "infinite {p :: nat. prime p}"
proof
  \<comment> \<open>Suppose the set of primes were finite.\<close>
  define P :: "nat set" where "P = {p. prime p}"
  assume fin: "finite P"

  \<comment> \<open>Then the Euler product form of the $\zeta$ function ranges over a finite set,
      and since each factor is holomorphic in the positive real half-space, 
      the product is, too.\<close>
  define zeta' :: "complex \<Rightarrow> complex" 
    where "zeta' = (\<lambda>s. (\<Prod>p\<in>P. inverse (1 - 1 / of_nat p powr s)))"
  have holo: "zeta' holomorphic_on A" if "A \<subseteq> {s. Re s > 0}" for A
  proof -
    {
      fix p :: nat and s :: complex assume p: "p \<in> P" and s: "s \<in> A"
      from p have p': "real p > 1" 
        by (subst of_nat_1 [symmetric], subst of_nat_less_iff) (simp add: prime_gt_Suc_0_nat P_def)
      have "norm (of_nat p powr s) = real p powr Re s"
        by (simp add: norm_powr_real_powr)
      also have "\<dots> > real p powr 0" using p p' s that
        by (subst powr_less_cancel_iff) (auto simp: prime_gt_1_nat)
      finally have "of_nat p powr s \<noteq> 1" using p by (auto simp: P_def)
    }
    thus ?thesis by (auto simp: zeta'_def P_def intro!: holomorphic_intros)
  qed

  \<comment> \<open>Since the Euler product expansion of $\zeta(s)$ is valid for all $s$ with
      real value at least 1, and both $\zeta(s)$ and the Euler product must 
      be equal in the positive real half-space punctured at 1 by analytic
      continuation.\<close>
  have eq: "zeta s = zeta' s" if "Re s > 0" "s \<noteq> 1" for s
  proof (rule analytic_continuation_open[of "{s. Re s > 1}" "{s. Re s > 0} - {1}" zeta zeta'])
    fix s assume s: "s \<in> {s. Re s > 1}"
    let ?f = "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - 1 / of_nat p powr s) else 1)"
    have "eventually (\<lambda>n. ?f n = zeta' s) sequentially"
      using eventually_ge_at_top[of "Max P"]
    proof eventually_elim
      case (elim n)
      have "P \<noteq> {}" by (auto simp: P_def intro!: exI[of _ 2])
      with elim have "P \<subseteq> {..n}" using fin by auto
      thus ?case unfolding zeta'_def
        by (intro prod.mono_neutral_cong_right) (auto simp: P_def)
    qed
    moreover from s have "?f \<longlonglongrightarrow> zeta s" by (intro euler_product_zeta) auto
    ultimately have "(\<lambda>_. zeta' s) \<longlonglongrightarrow> zeta s"
      by (blast intro: Lim_transform_eventually)
    thus "zeta s = zeta' s" by (simp add: LIMSEQ_const_iff)
  qed (auto intro!: exI[of _ 2] open_halfspace_Re_gt connected_open_delete convex_halfspace_Re_gt 
         holomorphic_intros holo that intro: convex_connected)

  \<comment> \<open>However, since the Euler product is holomorphic on the entire positive real
      half-space, it cannot have a pole at 1, while $\zeta(s)$ does have a pole
      at 1. Since they are equal in the punctured neighbourhood of 1, this is
      a contradiction.\<close>
  have ev: "eventually (\<lambda>s. s \<in> {s. Re s > 0} - {1}) (at 1)"
    by (auto simp: eventually_at_filter intro!: open_halfspace_Re_gt
               eventually_mono[OF eventually_nhds_in_open[of "{s. Re s > 0}"]])
  have "\<not>is_pole zeta' 1"
    by (rule not_is_pole_holomorphic [of "{s. Re s > 0}"]) (auto intro!: holo open_halfspace_Re_gt)
  also have "is_pole zeta' 1 \<longleftrightarrow> is_pole zeta 1" unfolding is_pole_def
    by (intro filterlim_cong refl eventually_mono [OF ev] eq [symmetric]) auto
  finally show False using is_pole_zeta by contradiction
qed


subsection \<open>The periodic zeta function\<close>

text \<open>
  The periodic zeta function $F(s, q)$ (as described e.\,g.\ by Apostol~\cite{apostol1976analytic} 
  is related to the Hurwitz zeta function. It is periodic in \<open>q\<close> with period 1 and it can be 
  represented by a Dirichlet series that is absolutely convergent for $\mathfrak{R}(s) > 1$.
   If \<open>q \<notin> \<int>\<close>, it furthermore convergent for $\mathfrak{R}(s) > 0$.

  It is clear that for integer \<open>q\<close>, we have $F(s, q) = F(s, 0) = \zeta(s)$. Moreover, for
  non-integer \<open>q\<close>, $F(s, q)$ can be analytically continued to an entire function.
\<close>
definition fds_perzeta :: "real \<Rightarrow> complex fds" where
  "fds_perzeta q = fds (\<lambda>m. exp (2 * pi * \<i> * m * q))"

text \<open>
  The definition of the periodic zeta function on the full domain is a bit unwieldy.
  The precise reasoning for this definition will be given later, and, in any case, it
  is probably more instructive to look at the derived ``alternative'' definitions later.
\<close>
definition perzeta :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  "perzeta q' s =
     (if q' \<in> \<int> then zeta s
      else let q = frac q' in
        if s = 0 then \<i> / (2 * pi) * (pre_zeta q 1 - pre_zeta (1 - q) 1 + 
                                             ln (1 - q) - ln q + pi * \<i>)
        else if s \<in> \<nat> then eval_fds (fds_perzeta q) s 
        else complex_of_real (2 * pi) powr (s - 1) * \<i> * Gamma (1 - s) *
               (\<i> powr (-s) * hurwitz_zeta q (1 - s) -
                \<i> powr s * hurwitz_zeta (1 - q) (1 - s)))"

interpretation fds_perzeta: periodic_fun_simple' fds_perzeta
  by standard (simp_all add: fds_perzeta_def exp_add ring_distribs exp_eq_polar
                             cis_mult [symmetric] cis_multiple_2pi)

interpretation perzeta: periodic_fun_simple' perzeta
proof -
  have [simp]: "n + 1 \<in> \<int> \<longleftrightarrow> n \<in> \<int>" for n :: real
    by (simp flip: frac_eq_0_iff add: frac.plus_1)
  show "periodic_fun_simple' perzeta"
    by standard (auto simp: fun_eq_iff perzeta_def Let_def frac.plus_1)
qed

lemma perzeta_frac [simp]: "perzeta (frac q) = perzeta q"
  by (auto simp: perzeta_def fun_eq_iff Let_def)

lemma fds_perzeta_frac [simp]: "fds_perzeta (frac q) = fds_perzeta q"
  using fds_perzeta.plus_of_int[of "frac q" "\<lfloor>q\<rfloor>"] by (simp add: frac_def)

lemma abs_conv_abscissa_perzeta: "abs_conv_abscissa (fds_perzeta q) \<le> 1"
proof (rule abs_conv_abscissa_leI)
  fix c assume c: "ereal c > 1"
  hence "summable (\<lambda>n. n powr -c)"
    by (simp add: summable_real_powr_iff)
  also have "?this \<longleftrightarrow> fds_abs_converges (fds_perzeta q) (of_real c)" unfolding fds_abs_converges_def
    by (intro summable_cong eventually_mono[OF eventually_gt_at_top[of 0]])
       (auto simp: norm_divide norm_powr_real_powr fds_perzeta_def powr_minus field_simps)
  finally show "\<exists>s. s \<bullet> 1 = c \<and> fds_abs_converges (fds_perzeta q) s"
    by (intro exI[of _ "of_real c"]) auto
qed

lemma conv_abscissa_perzeta: "conv_abscissa (fds_perzeta q) \<le> 1"
  by (rule order.trans[OF conv_le_abs_conv_abscissa abs_conv_abscissa_perzeta])

lemma fds_perzeta__left_0 [simp]: "fds_perzeta 0 = fds_zeta"
  by (simp add: fds_perzeta_def fds_zeta_def)

lemma perzeta_0_left [simp]: "perzeta 0 s = zeta s"
  by (simp add: perzeta_def eval_fds_zeta)

lemma perzeta_int: "q \<in> \<int> \<Longrightarrow> perzeta q = zeta"
  by (simp add: perzeta_def fun_eq_iff)

lemma fds_perzeta_int: "q \<in> \<int> \<Longrightarrow> fds_perzeta q = fds_zeta"
  by (auto simp: fds_perzeta.of_int elim!: Ints_cases)

lemma sums_fds_perzeta:
  assumes "Re s > 1"
  shows   "(\<lambda>m. exp (2 * pi * \<i> * Suc m * q) / of_nat (Suc m) powr s) sums
             eval_fds (fds_perzeta q) s"
proof -
  have "conv_abscissa (fds_perzeta q) \<le> 1" by (rule conv_abscissa_perzeta)
  also have "\<dots> < ereal (Re s)"  using assms by (simp add: one_ereal_def)
  finally have "fds_converges (fds_perzeta q) s" by (intro fds_converges) auto
  hence "(\<lambda>n. fds_nth (fds_perzeta q) (Suc n) / nat_power (Suc n) s) sums
           eval_fds (fds_perzeta q) s" by (subst sums_Suc_iff) (auto simp: fds_converges_iff)
  thus ?thesis by (simp add: fds_perzeta_def)
qed

lemma sum_tendsto_fds_perzeta:
  assumes "Re s > 1"
  shows   "(\<lambda>n. \<Sum>k\<in>{0<..n}. exp (2 * real k * pi * q * \<i>) * of_nat k powr - s)
              \<longlonglongrightarrow> eval_fds (fds_perzeta q) s"
proof -
  have "(\<lambda>m. exp (2 * pi * \<i> * Suc m * q) / of_nat (Suc m) powr s) sums eval_fds (fds_perzeta q) s"
    by (intro sums_fds_perzeta assms)
  hence "(\<lambda>n. \<Sum>k<n. exp (2 * real (Suc k) * pi * q * \<i>) * of_nat (Suc k) powr -s) \<longlonglongrightarrow>
           eval_fds (fds_perzeta q) s"
    (is "filterlim ?f _ _") by (simp add: sums_def powr_minus field_simps)
  also have "?f = (\<lambda>n. \<Sum>k\<in>{0<..n}. exp (2 * real k * pi * q * \<i>) * of_nat k powr -s)"
    by (intro ext sum.reindex_bij_betw sum.reindex_bij_witness[of _ "\<lambda>n. n - 1" Suc]) auto
  finally show ?thesis by simp
qed

text \<open>
  Using the geometric series, it is easy to see that the Dirichlet series for $F(s, q)$
  has bounded partial sums for non-integer \<open>q\<close>, so it must converge for any \<open>s\<close> with
  $\mathfrak{R}(s) > 0$.
\<close>
lemma conv_abscissa_perzeta':
  assumes "q \<notin> \<int>"
  shows   "conv_abscissa (fds_perzeta q) \<le> 0"
proof (rule conv_abscissa_leI)
  fix c :: real assume c: "ereal c > 0"
  have "fds_converges (fds_perzeta q) (of_real c)"
  proof (rule bounded_partial_sums_imp_fps_converges)
    define \<omega> where "\<omega> = exp (2 * pi * \<i> * q)"
    have [simp]: "norm \<omega> = 1" by (simp add: \<omega>_def)
    define M where "M = 2 / norm (1 - \<omega>)"
    from \<open>q \<notin> \<int>\<close> have "\<omega> \<noteq> 1"
      by (auto simp: \<omega>_def exp_eq_1)
    hence "M > 0" by (simp add: M_def)
  
    show "Bseq (\<lambda>n. \<Sum>k\<le>n. fds_nth (fds_perzeta q) k / nat_power k 0)"
      unfolding Bseq_def
    proof (rule exI, safe)
      fix n :: nat
      show "norm (\<Sum>k\<le>n. fds_nth (fds_perzeta q) k / nat_power k 0) \<le> M"
      proof (cases "n = 0")
        case False
        have "(\<Sum>k\<le>n. fds_nth (fds_perzeta q) k / nat_power k 0) =
                (\<Sum>k\<in>{1..1 + (n - 1)}. \<omega> ^ k)" using False
          by (intro sum.mono_neutral_cong_right)
             (auto simp: fds_perzeta_def fds_nth_fds exp_of_nat_mult [symmetric] mult_ac \<omega>_def)
        also have "\<dots> = \<omega> * (1 - \<omega> ^ n) / (1 - \<omega>)" using \<open>\<omega> \<noteq> 1\<close> and False
          by (subst sum_gp_offset) simp
        also have "norm \<dots> \<le> 1 * (norm (1::complex) + norm (\<omega> ^ n)) / norm (1 - \<omega>)"
          unfolding norm_mult norm_divide
          by (intro mult_mono divide_right_mono norm_triangle_ineq4) auto
        also have "\<dots> = M" by (simp add: M_def norm_power)
        finally show ?thesis .
      qed (use \<open>M > 0\<close> in simp_all)
    qed fact+
  qed (insert c, auto)
  thus "\<exists>s. s \<bullet> 1 = c \<and> fds_converges (fds_perzeta q) s"
    by (intro exI[of _ "of_real c"]) auto
qed

lemma fds_perzeta_one_half: "fds_perzeta (1 / 2) = fds (\<lambda>n. (-1) ^ n)"
  using Complex.DeMoivre[of pi]
  by (intro fds_eqI) (auto simp: fds_perzeta_def exp_eq_polar mult_ac)

lemma perzeta_one_half_1 [simp]: "perzeta (1 / 2) 1 = -ln 2"
proof (rule sums_unique2)
  have *: "(1 / 2 :: real) \<notin> \<int>"
    using fraction_not_in_ints[of 2 1] by auto
  have "fds_converges (fds_perzeta (1 / 2)) 1"
    by (rule fds_converges, rule le_less_trans, rule conv_abscissa_perzeta') (use * in auto)
  hence "(\<lambda>n. (-1) ^ Suc n / Suc n) sums eval_fds (fds_perzeta (1 / 2)) 1"
    unfolding fds_converges_altdef by (simp add: fds_perzeta_one_half)
  also from * have "eval_fds (fds_perzeta (1 / 2)) 1 = perzeta (1 / 2) 1"
    by (simp add: perzeta_def)
  finally show "(\<lambda>n. -complex_of_real ((-1) ^ n / Suc n)) sums perzeta (1 / 2) 1"
    by simp
  hence "(\<lambda>n. -complex_of_real ((-1) ^ n / Suc n)) sums -of_real (ln 2)"
    by (intro sums_minus sums_of_real alternating_harmonic_series_sums)
  thus "(\<lambda>n. -complex_of_real ((-1) ^ n / Suc n)) sums -(ln 2)"
    by (simp flip: Ln_of_real)
qed


subsection \<open>Hurwitz's formula\<close>

text \<open>
  We now move on to prove Hurwitz's formula relating the Hurwitz zeta function and the
  periodic zeta function. We mostly follow Apostol's proof, although we do make some small
  changes in order to make the proof more amenable to Isabelle's complex analysis library.
 
  The big difference is that Apostol integrates along a circle with a slit, where the two
  sides of the slit lie on different branches of the integrand. This makes sense when looking
  as the integrand as a Riemann surface, but we do not have a notion of Riemann surfaces in
  Isabelle.

  It is therefore much easier to simply cut the circle into an upper and a lower half. In fact,
  the integral on the lower half can be reduced to the one on the upper half easily by
  symmetry, so we really only need to handle the integral on the upper half. The integration
  contour that we will use is therefore a semi-annulus in the upper half of the complex plane,
  centred around the origin.

  Now, first of all, we prove the existence of an important improper integral 
  that we will need later.
\<close>
(* TODO: Move *)
lemma set_integrable_bigo:
  fixes f g :: "real \<Rightarrow> 'a :: {banach, real_normed_field, second_countable_topology}"
  assumes "f \<in> O(\<lambda>x. g x)" and "set_integrable lborel {a..} g"
  assumes "\<And>b. b \<ge> a \<Longrightarrow> set_integrable lborel {a..<b} f"
  assumes [measurable]: "set_borel_measurable borel {a..} f"
  shows   "set_integrable lborel {a..} f"
proof -
  from assms(1) obtain C x0 where C: "C > 0" "\<And>x. x \<ge> x0 \<Longrightarrow> norm (f x) \<le> C * norm (g x)"
    by (fastforce elim!: landau_o.bigE simp: eventually_at_top_linorder)
  define x0' where "x0' = max a x0"

  have "set_integrable lborel {a..<x0'} f"
    by (intro assms) (auto simp: x0'_def)
  moreover have "set_integrable lborel {x0'..} f" unfolding set_integrable_def
  proof (rule Bochner_Integration.integrable_bound)
    from assms(2) have "set_integrable lborel {x0'..} g"
      by (rule set_integrable_subset) (auto simp: x0'_def)
    thus "integrable lborel (\<lambda>x. C *\<^sub>R (indicator {x0'..} x *\<^sub>R g x))" unfolding set_integrable_def
      by (intro integrable_scaleR_right) (simp add: abs_mult norm_mult)
  next
    from assms(4) have "set_borel_measurable borel {x0'..} f"
      by (rule set_borel_measurable_subset) (auto simp: x0'_def)
    thus "(\<lambda>x. indicator {x0'..} x *\<^sub>R f x) \<in> borel_measurable lborel"
      by (simp add: set_borel_measurable_def)
  next
    show "AE x in lborel. norm (indicator {x0'..} x *\<^sub>R f x)
                            \<le> norm (C *\<^sub>R (indicator {x0'..} x *\<^sub>R g x))"
      using C by (intro AE_I2) (auto simp: abs_mult indicator_def x0'_def)
  qed
  ultimately have "set_integrable lborel ({a..<x0'} \<union> {x0'..}) f"
    by (rule set_integrable_Un) auto
  also have "{a..<x0'} \<union> {x0'..} = {a..}" by (auto simp: x0'_def)
  finally show ?thesis .
qed

lemma set_integrable_Gamma_hurwitz_aux2_real:
  fixes s a :: real
  assumes "r > 0" and "a > 0"
  shows "set_integrable lborel {r..} (\<lambda>x. x powr s * (exp (-a * x)) / (1 - exp (-x)))"
    (is "set_integrable _ _ ?g")
proof (rule set_integrable_bigo)
  have "(\<lambda>x. exp (-(a/2) * x)) integrable_on {r..}" using assms
    by (intro integrable_on_exp_minus_to_infinity) auto
  hence "set_integrable lebesgue {r..} (\<lambda>x. exp (-(a/2) * x))"
    by (intro nonnegative_absolutely_integrable) simp_all
  thus "set_integrable lborel {r..} (\<lambda>x. exp (-(a/2) * x))"
    by (simp add: set_integrable_def integrable_completion)
next
  fix y :: real
  have "set_integrable lborel {r..y} ?g" using assms
    by (intro borel_integrable_atLeastAtMost') (auto intro!: continuous_intros)
  thus "set_integrable lborel {r..<y} ?g"
    by (rule set_integrable_subset) auto
next
  from assms show "?g \<in> O(\<lambda>x. exp (-(a/2) * x))"
    by real_asymp
qed (auto simp: set_borel_measurable_def)

lemma set_integrable_Gamma_hurwitz_aux2:
  fixes s :: complex and a :: real
  assumes "r > 0" and "a > 0"
  shows   "set_integrable lborel {r..} (\<lambda>x. x powr -s * (exp (- a * x)) / (1 - exp (- x)))"
             (is "set_integrable _ _ ?g")
proof -
  have "set_integrable lborel {r..} (\<lambda>x. x powr -Re s * (exp (-a * x)) / (1 - exp (-x)))" 
    (is "set_integrable _ _ ?g'")
    by (rule set_integrable_Gamma_hurwitz_aux2_real) (use assms in auto)
  also have "?this \<longleftrightarrow> integrable lborel (\<lambda>x. indicator {r..} x *\<^sub>R ?g' x)"
    by (simp add: set_integrable_def)
  also have "(\<lambda>x. indicator {r..} x *\<^sub>R ?g' x) = (\<lambda>x. norm (indicator {r..} x *\<^sub>R ?g x))" using assms
    by (auto simp: indicator_def norm_mult norm_divide norm_powr_real_powr fun_eq_iff
                   exp_of_real exp_minus norm_inverse in_Reals_norm power2_eq_square divide_simps)
  finally show ?thesis unfolding set_integrable_def
    by (subst (asm) integrable_norm_iff) auto
qed

lemma closed_neg_Im_slit: "closed {z. Re z = 0 \<and> Im z \<le> 0}"
proof -
  have "closed ({z. Re z = 0} \<inter> {z. Im z \<le> 0})"
    by (intro closed_Int closed_halfspace_Re_eq closed_halfspace_Im_le)
  also have "{z. Re z = 0} \<inter> {z. Im z \<le> 0} = {z. Re z = 0 \<and> Im z \<le> 0}" by blast
  finally show ?thesis .
qed


text \<open>
  We define tour semi-annulus path. When this path is mirrored into the lower half of the complex
  plane and subtracted from the original path and the outer radius tends to \<open>\<infinity>\<close>, this becomes a
  Hankel contour extending to \<open>-\<infinity>\<close>.
\<close>
definition hankel_semiannulus :: "real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex" where
 "hankel_semiannulus r N = (let R = (2 * N + 1) * pi in
    part_circlepath 0 R 0 pi +++                  \<comment>\<open>Big half circle\<close>
    linepath (of_real (-R)) (of_real (-r)) +++    \<comment>\<open>Line on the negative real axis\<close>
    part_circlepath 0 r pi 0 +++                  \<comment>\<open>Small half circle\<close>
    linepath (of_real r) (of_real R))             \<comment>\<open>Line on the positive real axis\<close>" 

lemma path_hankel_semiannulus [simp, intro]: "path (hankel_semiannulus r R)"
  and valid_path_hankel_semiannulus [simp, intro]: "valid_path (hankel_semiannulus r R)"
  and pathfinish_hankel_semiannulus [simp, intro]:
        "pathfinish (hankel_semiannulus r R) = pathstart (hankel_semiannulus r R)"
  by (simp_all add: hankel_semiannulus_def Let_def)


text \<open>
  We set the stage for an application of the Residue Theorem. We define a function
  \[f(s, z) = z^{-s} \frac{\exp(az)}{1-\exp(-z)}\ ,\]
  which will be the integrand. However, the principal branch of $z^{-s}$ has a branch cut
  along the non-positive real axis, which is bad because a part of our integration path also
  lies on the non-positive real axis. We therefore choose a slightly different branch of $z^{-s}$
  by moving the logarithm branch along by $90^{\circ}$ so that the branch cut lies on the
  non-positive imaginary axis instead.
\<close>
context
  fixes a :: real
  fixes f :: "complex \<Rightarrow> complex \<Rightarrow> complex"
    and g :: "complex \<Rightarrow> real \<Rightarrow> complex"
    and h :: "real \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> complex"
    and Res :: "complex \<Rightarrow> nat \<Rightarrow> complex" 
    and Ln' :: "complex \<Rightarrow> complex"
    and F :: "real \<Rightarrow> complex \<Rightarrow> complex"
  assumes a: "a \<in> {0<..1}"

  \<comment>\<open>Our custom branch of the logarithm\<close>
  defines "Ln' \<equiv> (\<lambda>z. ln (-\<i> * z) + \<i> * pi / 2)"

  \<comment>\<open>The integrand\<close>
  defines "f \<equiv> (\<lambda>s z. exp (Ln' z * (-s) + of_real a * z) / (1 - exp z))"

  \<comment>\<open>The integrand on the negative real axis\<close>
  defines "g \<equiv> (\<lambda>s x. complex_of_real x powr -s * of_real (exp (-a*x)) / of_real (1 - exp (-x)))"

  \<comment>\<open>The integrand on the circular arcs\<close>
  defines "h \<equiv> (\<lambda>r s t. r * \<i> * cis t * exp (a * (r * cis t) - (ln r + \<i> * t) * s) /
                        (1 - exp (r * cis t)))"

  \<comment>\<open>The interesting part of the residues\<close>
  defines "Res \<equiv> (\<lambda>s k. exp (of_real (2 * real k * pi * a) * \<i>) *
                            of_real (2 * real k * pi) powr (-s))"

  \<comment>\<open>The periodic zeta function (at least on $\mathfrak{R}(s) > 1$ half-plane)\<close>
  defines "F \<equiv> (\<lambda>q. eval_fds (fds_perzeta q))"
begin

text \<open>
  First, some basic properties of our custom branch of the logarithm:
\<close>
lemma Ln'_i: "Ln' \<i> = \<i> * pi / 2"
  by (simp add: Ln'_def)

lemma Ln'_of_real_pos:
  assumes "x > 0"
  shows   "Ln' (of_real x) = of_real (ln x)"
proof -
  have "Ln' (of_real x) = Ln (of_real x * (-\<i>)) + \<i> * pi / 2"
    by (simp add: Ln'_def mult_ac)
  also have "\<dots> = of_real (ln x)" using assms
    by (subst Ln_times_of_real) (auto simp: Ln_of_real)
  finally show ?thesis .
qed

lemma Ln'_of_real_neg:
  assumes "x < 0"
  shows   "Ln' (of_real x) = of_real (ln (-x)) + \<i> * pi"
proof -
  have "Ln' (of_real x) = Ln (of_real (-x) * \<i>) + \<i> * pi / 2"
    by (simp add: Ln'_def mult_ac)
  also have "\<dots> = of_real (ln (-x)) + \<i> * pi" using assms
    by (subst Ln_times_of_real) (auto simp: Ln_Reals_eq)
  finally show ?thesis .
qed

lemma Ln'_times_of_real:
  "Ln' (of_real x * z) = of_real (ln x) + Ln' z" if "x > 0" "z \<noteq> 0" for z x
proof -
  have "Ln' (of_real x * z) = Ln (of_real x * (- \<i> * z)) + \<i> * pi / 2"
    by (simp add: Ln'_def mult_ac)
  also have "\<dots> = of_real (ln x) + Ln' z"
    using that by (subst Ln_times_of_real) (auto simp: Ln'_def Ln_of_real)
  finally show ?thesis .
qed

lemma Ln'_cis:
  assumes "t \<in> {-pi / 2<..3 / 2 * pi}"
  shows   "Ln' (cis t) = \<i> * t"
proof -
  have "exp (\<i> * pi / 2) = \<i>" by (simp add: exp_eq_polar)
  hence "Ln (- (\<i> * cis t)) = \<i> * (t - pi / 2)" using assms
    by (intro Ln_unique) (auto simp: algebra_simps exp_diff cis_conv_exp)
  thus ?thesis by (simp add: Ln'_def algebra_simps)
qed

text \<open>
  Next, we show that the line and circle integrals are holomorphic using Leibniz's rule:
\<close>
lemma contour_integral_part_circlepath_h:
  assumes r: "r > 0"
  shows   "contour_integral (part_circlepath 0 r 0 pi) (f s) = integral {0..pi} (h r s)"
proof -
  have "contour_integral (part_circlepath 0 r 0 pi) (f s) = 
          integral {0..pi} (\<lambda>t. f s (r * cis t) * r * \<i> * cis t)"
    by (simp add: contour_integral_part_circlepath_eq)
  also have "integral {0..pi} (\<lambda>t. f s (r * cis t) * r * \<i> * cis t) = integral {0..pi} (h r s)"
  proof (intro integral_cong)
    fix t assume t: "t \<in> {0..pi}"
    have "-(pi / 2) < 0" by simp
    also have "0 \<le> t" using t by simp
    finally have "t \<in> {-(pi/2)<..3/2*pi}" using t by auto
    thus "f s (r * cis t) * r * \<i> * cis t = h r s t"
      using r by (simp add: f_def Ln'_times_of_real Ln'_cis h_def Ln_Reals_eq)
  qed
  finally show ?thesis .
qed

lemma integral_g_holomorphic:
  assumes "b > 0"
  shows   "(\<lambda>s. integral {b..c} (g s)) holomorphic_on A"
proof -
  define g' where "g' = (\<lambda>s t. - (of_real t powr (-s)) * complex_of_real (ln t) * 
                          of_real (exp (- (a * t))) / of_real (1 - exp (- t)))"
  have "(\<lambda>s. integral (cbox b c) (g s)) holomorphic_on UNIV"
  proof (rule leibniz_rule_holomorphic)
    fix s :: complex and t :: real assume "t \<in> cbox b c"
    thus "((\<lambda>s. g s t) has_field_derivative g' s t) (at s)" using assms
      by (auto simp: g_def g'_def powr_def Ln_Reals_eq intro!: derivative_eq_intros)
  next
    fix s show "g s integrable_on cbox b c" for s unfolding g_def using assms
      by (intro integrable_continuous continuous_intros) auto
  next
    show "continuous_on (UNIV \<times> cbox b c) (\<lambda>(s, t). g' s t)" using assms
      by (auto simp: g'_def case_prod_unfold intro!: continuous_intros)
  qed auto
  thus ?thesis by auto
qed

lemma integral_h_holomorphic:
  assumes r: "r \<in> {0<..<2}"
  shows   "(\<lambda>s. integral {b..c} (h r s)) holomorphic_on A"
proof -
  have no_sing: "exp (r * cis t) \<noteq> 1" for t
  proof
    define z where "z = r * cis t"
    assume "exp z = 1"
    then obtain n where "norm z = 2 * pi * of_int \<bar>n\<bar>"
      by (auto simp: exp_eq_1 cmod_def abs_mult)
    moreover have "norm z = r" using r by (simp add: z_def norm_mult)
    ultimately have r_eq: "r = 2 * pi * of_int \<bar>n\<bar>" by simp
    with r have "n \<noteq> 0" by auto
    moreover from r have "r < 2 * pi" using pi_gt3 by simp 
    with r_eq have "\<bar>n\<bar> < 1" by simp
    ultimately show False by simp
  qed

  define h' where "h' = (\<lambda>s t. exp (a * r * cis t - (ln r + \<i> * t) * s) *
                           (-ln r - \<i> * t) * (r * \<i> * cis t) / (1 - exp (r * cis t)))"
  have "(\<lambda>s. integral (cbox b c) (h r s)) holomorphic_on UNIV"
  proof (rule leibniz_rule_holomorphic)
    fix s t assume "t \<in> cbox b c"
    thus "((\<lambda>s. h r s t) has_field_derivative h' s t) (at s)" using no_sing r
      by (auto intro!: derivative_eq_intros simp: h_def h'_def mult_ac Ln_Reals_eq)
  next
    fix s show "h r s integrable_on cbox b c" using no_sing unfolding h_def
      by (auto intro!: integrable_continuous_real continuous_intros)
  next
    show "continuous_on (UNIV \<times> cbox b c) (\<lambda>(s, t). h' s t)" using no_sing
      by (auto simp: h'_def case_prod_unfold intro!: continuous_intros)
  qed auto
  thus ?thesis by auto
qed

text \<open>
  We now move on to the core result, which uses the Residue Theorem to relate a contour integral
  along a semi-annulus to a partial sum of the periodic zeta function.
\<close>
lemma hurwitz_formula_integral_semiannulus:
  fixes N :: nat and r :: real and s :: complex
  defines "R \<equiv> real (2 * N + 1) * pi"
  assumes "r > 0" and "r < 2"
  shows "exp (-\<i> * pi * s) * integral {r..R} (\<lambda>x. x powr (-s) * exp (-a * x) / (1 - exp (-x))) +
         integral {r..R} (\<lambda>x. x powr (-s) * exp (a * x) / (1 - exp x)) +
         contour_integral (part_circlepath 0 R 0 pi) (f s) +
         contour_integral (part_circlepath 0 r pi 0) (f s)
         = -2 * pi * \<i> * exp (- s * of_real pi * \<i> / 2) * (\<Sum>k\<in>{0<..N}. Res s k)" (is ?thesis1)
    and "f s contour_integrable_on hankel_semiannulus r N"
proof -
  have "2 < 1 * pi" using pi_gt3 by simp
  also have "\<dots> \<le> R" unfolding R_def by (intro mult_right_mono) auto
  finally have "R > 2" by (auto simp: R_def)
  note r_R = \<open>r > 0\<close> \<open>r < 2\<close> this

  \<comment>\<open>We integrate along the edge of a semi-annulus in the upper half of the complex plane.
     It consists of a big semicircle, a small semicircle, and two lines connecting the two
     circles, one on the positive real axis and one on the negative real axis.

     The integral along the big circle will vanish as the radius of the circle tends to \<open>\<infinity>\<close>,
     whereas the remaining path becomes a Hankel contour, and the integral along that Hankel
     contour is what we are interested in, since it is connected to the Hurwitz zeta function.\<close>
  define big_circle where "big_circle = part_circlepath 0 R 0 pi"
  define small_circle where "small_circle = part_circlepath 0 r pi 0"
  define neg_line where "neg_line = linepath (complex_of_real (-R)) (complex_of_real (-r))"
  define pos_line where "pos_line = linepath (complex_of_real r) (complex_of_real R)"
  define \<gamma> where "\<gamma> = hankel_semiannulus r N"
  have \<gamma>_altdef: "\<gamma> = big_circle +++ neg_line +++ small_circle +++ pos_line"
    by (simp add: \<gamma>_def R_def add_ac hankel_semiannulus_def big_circle_def
                  neg_line_def small_circle_def pos_line_def)
  have [simp]: "path \<gamma>" "valid_path \<gamma>" "pathfinish \<gamma> = pathstart \<gamma>"
    by (simp_all add: \<gamma>_def)

  \<comment>\<open>The integrand has a branch cut along the non-positive imaginary axis and additional 
     simple poles at $2n\pi i$ for any \<open>n \<in> \<nat>\<^sub>>\<^sub>0\<close>. The radius of the smaller circle will always
     be less than $2\pi$ and the radius of the bigger circle of the form $(2N+1)\pi$, so we
     always have precisely the first $N$ poles inside our path.\<close>
  define sngs where "sngs = (\<lambda>n. of_real (2 * pi * real n) * \<i>) ` {0<..}"
  define sngs' where "sngs' = (\<lambda>n. of_real (2 * pi * real n) * \<i>) ` {0<..N}"
  have sngs_subset: "sngs' \<subseteq> sngs" unfolding sngs_def sngs'_def by (intro image_mono) auto
  have closed_sngs [intro]: "closed (sngs - sngs')" unfolding sngs_def
  proof (rule discrete_imp_closed[of "2 * pi"]; safe?)
    fix m n :: nat
    assume "dist (of_real (2 * pi * real m) * \<i>) (of_real (2 * pi * real n) * \<i>) < 2 * pi"
    also have "dist (of_real (2 * pi * real m) * \<i>) (of_real (2 * pi * real n) * \<i>) =
                norm (of_real (2 * pi * real m) * \<i> - of_real (2 * pi * real n) * \<i>)"
      by (simp add: dist_norm)
    also have "of_real (2 * pi * real m) * \<i> - of_real (2 * pi * real n) * \<i> =
                 of_real (2 * pi) * \<i> * of_int (int m - int n)" by (simp add: algebra_simps)
    also have "norm \<dots> = 2 * pi * of_int \<bar>int m - int n\<bar>"
      unfolding norm_mult norm_of_int by (simp add: norm_mult)
    finally have "\<bar>real m - real n\<bar> < 1" by simp
    hence "m = n" by linarith
    thus "of_real (2 * pi * real m) * \<i> = of_real (2 * pi * real n) * \<i>" by simp
  qed auto

  \<comment>\<open>We define an area within which the integrand is holomorphic. Choosing this area as big as
     possible makes things easier later on, so we only remove the branch cut and the poles.\<close>
  define S where "S = - {z. Re z = 0 \<and> Im z \<le> 0} - (sngs - sngs')"
  define S' where "S' = - {z. Re z = 0 \<and> Im z \<le> 0}"

  have sngs: "exp z = 1 \<longleftrightarrow> z \<in> sngs" if "Re z \<noteq> 0 \<or> Im z > 0" for z
  proof
    assume "exp z = 1"
    then obtain n where n: "z = 2 * pi * of_int n * \<i>"
      unfolding exp_eq_1 by (auto simp: complex_eq_iff mult_ac)
    moreover from n and pi_gt_zero and that have "n > 0" by (auto simp: zero_less_mult_iff)
    ultimately have "z = of_real (2 * pi * nat n) * \<i>" and "nat n \<in> {0<..}"
      by auto
    thus "z \<in> sngs" unfolding sngs_def by blast
  qed (insert that, auto simp: sngs_def exp_eq_polar)

  \<comment>\<open>We show that the path stays within the well-behaved area.\<close>
  have "path_image neg_line = of_real ` {-R..-r}" using r_R
    by (auto simp: neg_line_def closed_segment_Reals closed_segment_eq_real_ivl)
  hence "path_image neg_line \<subseteq> S - sngs'" using r_R sngs_subset
    by (auto simp: S_def sngs_def complex_eq_iff)

  have "path_image pos_line = of_real ` {r..R}" using r_R
    by (auto simp: pos_line_def closed_segment_Reals closed_segment_eq_real_ivl)
  hence "path_image pos_line \<subseteq> S - sngs'" using r_R sngs_subset
    by (auto simp: S_def sngs_def complex_eq_iff)

  have part_circlepath_in_S: "z \<in> S - sngs'"
    if "z \<in> path_image (part_circlepath 0 r' 0 pi) \<or> z \<in> path_image (part_circlepath 0 r' pi 0)"
    and "r' > 0" "r' \<notin> (\<lambda>n. 2 * pi * real n) ` {0<..}" for z r'
  proof -
    have z: "norm z = r' \<and> Im z \<ge> 0" using that
      by (auto simp: path_image_def part_circlepath_def norm_mult Im_exp linepath_def
               intro!: mult_nonneg_nonneg sin_ge_zero)
    hence "Re z \<noteq> 0 \<or> Im z > 0" using that by (auto simp: cmod_def)
    moreover from z and that have "z \<notin> sngs"
      by (auto simp: sngs_def norm_mult image_iff)
    ultimately show "z \<in> S - sngs'" using sngs_subset by (auto simp: S_def)
  qed

  {
    fix n :: nat assume n: "n > 0"
    have "r < 2 * pi * 1" using pi_gt3 r_R by simp
    also have "\<dots> \<le> 2 * pi * real n" using n by (intro mult_left_mono) auto
    finally have "r < \<dots>" .
  }
  hence "r \<notin> (\<lambda>n. 2 * pi * real n) ` {0<..}" using r_R by auto
  from part_circlepath_in_S[OF _ _ this] r_R have "path_image small_circle \<subseteq> S - sngs'"
    by (auto simp: small_circle_def)

  {
    fix n :: nat assume n: "n > 0" "2 * pi * real n = real (2 * N + 1) * pi"
    hence "real (2 * n) = real (2 * N + 1)" unfolding of_nat_mult by simp
    hence False unfolding of_nat_eq_iff by presburger
  }
  hence "R \<notin> (\<lambda>n. 2 * pi * real n) ` {0<..}" unfolding R_def by force
  from part_circlepath_in_S[OF _ _ this] r_R have "path_image big_circle \<subseteq> S - sngs'"
    by (auto simp: big_circle_def)

  note path_images =
    \<open>path_image small_circle \<subseteq> S - sngs'\<close> \<open>path_image big_circle \<subseteq> S - sngs'\<close>
    \<open>path_image neg_line \<subseteq> S - sngs'\<close> \<open>path_image pos_line \<subseteq> S - sngs'\<close>
  have "path_image \<gamma> \<subseteq> S - sngs'" using path_images
    by (auto simp: \<gamma>_altdef path_image_join big_circle_def neg_line_def 
                   small_circle_def pos_line_def)

  \<comment>\<open>We need to show that the complex plane is still connected after we removed the branch cut
     and the poles. We do this by showing that the complex plane with the branch cut removed
     is starlike and therefore connected. Then we remove the (countably many) poles, which does not
     break connectedness either.\<close>
  have "open S" using closed_neg_Im_slit by (auto simp: S_def)
  have "starlike (UNIV - {z. Re z = 0 \<and> Im z \<le> 0})"
    (is "starlike ?S'") unfolding starlike_def
  proof (rule bexI ballI)+
    have "1 \<le> 1 * pi" using pi_gt3 by simp
    also have "\<dots> < (2 + 2 * real N) * pi" by (intro mult_strict_right_mono) auto
    finally show *: "\<i> \<in> ?S'" by (auto simp: S_def)
    fix z assume z: "z \<in> ?S'"
    have "closed_segment \<i> z \<inter> {z. Re z = 0 \<and> Im z \<le> 0} = {}"
    proof safe
      fix s assume s: "s \<in> closed_segment \<i> z" "Re s = 0" "Im s \<le> 0"
      then obtain t where t: "t \<in> {0..1}" "s = linepath \<i> z t"
        using linepath_image_01 by blast
      with z s t have z': "Re z = 0" "Im z > 0"
        by (auto simp: Re_linepath' S_def linepath_0')
      with s have "Im s \<in> closed_segment 1 (Im z) \<and> Im s \<le> 0"
        by (subst (asm) closed_segment_same_Re) auto
      with z' show "s \<in> {}"
        by (auto simp: closed_segment_eq_real_ivl split: if_splits)
    qed
    thus "closed_segment \<i> z \<subseteq> ?S'" by (auto simp: S_def)
  qed
  hence "connected ?S'" by (rule starlike_imp_connected)
  hence "connected S'" by (simp add: Compl_eq_Diff_UNIV S'_def)
  have "connected S" unfolding S_def
    by (rule connected_open_diff_countable)
       (insert \<open>connected S'\<close>, auto simp: sngs_def closed_neg_Im_slit S'_def)

  \<comment>\<open>The integrand is now clearly holomorphic on @{term "S - sngs'"} and we can apply the
     Residue Theorem.\<close>
  have holo: "f s holomorphic_on (S - sngs')"
    unfolding f_def Ln'_def S_def using sngs
    by (auto intro!: holomorphic_intros simp: complex_nonpos_Reals_iff)
  have "contour_integral \<gamma> (f s) =
          of_real (2 * pi) * \<i> * (\<Sum>z\<in>sngs'. winding_number \<gamma> z * residue (f s) z)"
  proof (rule Residue_theorem)
    show "\<forall>z. z \<notin> S \<longrightarrow> winding_number \<gamma> z = 0"
    proof safe
      fix z assume "z \<notin> S"
      hence "Re z = 0 \<and> Im z \<le> 0 \<or> z \<in> sngs - sngs'" by (auto simp: S_def)
      thus "winding_number \<gamma> z = 0"
      proof
        define x where "x = -Im z"
        assume "Re z = 0 \<and> Im z \<le> 0"
        hence x: "z = -of_real x * \<i>" "x \<ge> 0" unfolding complex_eq_iff by (simp_all add: x_def)
        obtain B where "\<And>z. norm z \<ge> B \<Longrightarrow> winding_number \<gamma> z = 0"
          using winding_number_zero_at_infinity[of \<gamma>] by auto
        hence "winding_number \<gamma> (-of_real (max B 0) * \<i>) = 0" by (auto simp: norm_mult)
        also have "winding_number \<gamma> (-of_real (max B 0) * \<i>) = winding_number \<gamma> z"
        proof (rule winding_number_eq)
          from x have "closed_segment (-of_real (max B 0) * \<i>) z \<subseteq> {z. Re z = 0 \<and> Im z \<le> 0}"
            by (auto simp: closed_segment_same_Re closed_segment_eq_real_ivl)
          with \<open>path_image \<gamma> \<subseteq> S - sngs'\<close>
          show "closed_segment (-of_real (max B 0) * \<i>) z \<inter> path_image \<gamma> = {}"
            by (auto simp: S_def)
        qed auto
        finally show "winding_number \<gamma> z = 0" .
      next
        assume z: "z \<in> sngs - sngs'"
        show "winding_number \<gamma> z = 0"
        proof (rule winding_number_zero_outside)
          have "path_image \<gamma> = path_image big_circle \<union> path_image neg_line \<union>
                                 path_image small_circle \<union> path_image pos_line"
            unfolding \<gamma>_altdef small_circle_def big_circle_def pos_line_def neg_line_def
            by (simp add: path_image_join Un_assoc)
          also have "\<dots> \<subseteq> cball 0 ((2 * N + 1) * pi)" using r_R
            by (auto simp: small_circle_def big_circle_def pos_line_def neg_line_def
                           path_image_join norm_mult R_def path_image_part_circlepath'
                           in_Reals_norm closed_segment_Reals closed_segment_eq_real_ivl)
          finally show "path_image \<gamma> \<subseteq> \<dots>" .
        qed (insert z, auto simp: sngs_def sngs'_def norm_mult)
      qed
    qed
  qed (insert \<open>path_image \<gamma> \<subseteq> S - sngs'\<close> \<open>connected S\<close> \<open>open S\<close> holo, auto simp: sngs'_def)

  \<comment>\<open>We can use Wenda Li's framework to compute the winding numbers at the poles and show that
     they are all 1.\<close>
  also have "winding_number \<gamma> z = 1" if "z \<in> sngs'" for z
  proof -
    have "r < 2 * pi * 1" using pi_gt3 r_R by simp
    also have "\<dots> \<le> 2 * pi * real n" if "n > 0" for n using that by (intro mult_left_mono) auto
    finally have norm_z: "norm z > r" "norm z < R" using that r_R
      by (auto simp: sngs'_def norm_mult R_def)

    have "cindex_pathE big_circle z = -1" using r_R that unfolding big_circle_def
      by (subst cindex_pathE_circlepath_upper(1)) (auto simp: sngs'_def norm_mult R_def)
    have "cindex_pathE small_circle z = -1" using r_R that norm_z unfolding small_circle_def
      by (subst cindex_pathE_reversepath', subst reversepath_part_circlepath,
          subst cindex_pathE_circlepath_upper(2)) (auto simp: sngs'_def norm_mult)
    have "cindex_pathE neg_line z = 0" "cindex_pathE pos_line z = 0" 
      unfolding neg_line_def pos_line_def using r_R that
      by (subst cindex_pathE_linepath; force simp: neg_line_def cindex_pathE_linepath
            closed_segment_Reals closed_segment_eq_real_ivl sngs'_def complex_eq_iff)+
    note indices = \<open>cindex_pathE big_circle z = -1\<close> \<open>cindex_pathE small_circle z = -1\<close>
                   \<open>cindex_pathE neg_line z = 0\<close> \<open>cindex_pathE pos_line z = 0\<close>
    show ?thesis unfolding \<gamma>_altdef big_circle_def small_circle_def pos_line_def neg_line_def
      by eval_winding (insert indices path_images that,
                       auto simp: big_circle_def small_circle_def pos_line_def neg_line_def)
  qed
  hence "(\<Sum>z\<in>sngs'. winding_number \<gamma> z * residue (f s) z) = (\<Sum>z\<in>sngs'. residue (f s) z)"
    by simp
  also have "\<dots> = (\<Sum>k\<in>{0<..N}. residue (f s) (2 * pi * of_nat k * \<i>))"
    unfolding sngs'_def by (subst sum.reindex) (auto intro!: inj_onI simp: o_def)

  \<comment>\<open>Next, we compute the residues at each pole.\<close>
  also have "residue (f s) (2 * pi * of_nat k * \<i>) = -exp (- s * of_real pi * \<i> / 2) * Res s k"
    if "k \<in> {0<..N}" for k unfolding f_def
  proof (subst residue_simple_pole_deriv)
    show "open S'" using closed_neg_Im_slit by (auto simp: S'_def)
    show "connected S'" by fact
    show "(\<lambda>z. exp (Ln' z * (-s) + of_real a * z)) holomorphic_on S'"
         "(\<lambda>z. 1 - exp z) holomorphic_on S'"
      by (auto simp: S'_def Ln'_def complex_nonpos_Reals_iff intro!: holomorphic_intros)
    have "((\<lambda>z. 1 - exp z) has_field_derivative -exp (2 * pi * k * \<i>))
            (at (of_real (2 * pi * real k) * \<i>))"
      by (auto intro!: derivative_eq_intros)
    also have "-exp (2 * pi * k * \<i>) = -1" by (simp add: exp_eq_polar)
    finally show "((\<lambda>z. 1 - exp z) has_field_derivative -1)
                    (at (of_real (2 * pi * real k) * \<i>))" .
    have "Im (of_real (2 * pi * real k) * \<i>) > 0" using pi_gt_zero that
      by auto
    thus "of_real (2 * pi * real k) * \<i> \<in> S'" by (simp add: S'_def)

    have "exp (\<i> * pi / 2) = \<i>" by (simp add: exp_eq_polar)
    hence "exp (Ln' (complex_of_real (2 * pi * real k) * \<i>) * -s +
              of_real a * (of_real (2 * pi * real k) * \<i>)) / -1 = 
            - exp (2 * k * a * pi * \<i> - s * pi * \<i> / 2 - s * ln (2 * k * pi))" (is "?R = _")
      using that by (subst Ln'_times_of_real) (simp_all add: Ln'_i algebra_simps exp_diff)
    also have "\<dots> = -exp (- s * of_real pi * \<i> / 2) * Res s k" using that 
      by (simp add: Res_def exp_diff powr_def exp_minus inverse_eq_divide Ln_Reals_eq mult_ac)
    finally show "?R = -exp (- s * of_real pi * \<i> / 2) * Res s k" .
  qed (insert that, auto simp: S'_def exp_eq_polar)
  hence "(\<Sum>k\<in>{0<..N}. residue (f s) (2 * pi * of_nat k * \<i>)) = 
           -exp (- s * of_real pi * \<i> / 2) * (\<Sum>k\<in>{0<..N}. Res s k)"
    by (simp add: sum_distrib_left)

  \<comment>\<open>This gives us the final result:\<close>
  finally have "contour_integral \<gamma> (f s) =
                  -2 * pi * \<i> * exp (- s * of_real pi * \<i> / 2) * (\<Sum>k\<in>{0<..N}. Res s k)" by simp

  \<comment>\<open>Lastly, we decompose the contour integral into its four constituent integrals because this
     makes them somewhat nicer to work with later on.\<close>
  also show "f s contour_integrable_on \<gamma>"
  proof (rule contour_integrable_holomorphic_simple)
    show "path_image \<gamma> \<subseteq> S - sngs'" by fact
    have "closed sngs'" by (intro finite_imp_closed) (auto simp: sngs'_def)
    with \<open>open S\<close> show "open (S - sngs')" by auto
  qed (insert holo, auto)
  hence eq: "contour_integral \<gamma> (f s) = 
               contour_integral big_circle (f s) + contour_integral neg_line (f s) +
               contour_integral small_circle (f s) + contour_integral pos_line (f s)"
    unfolding \<gamma>_altdef big_circle_def neg_line_def small_circle_def pos_line_def by simp
  
  also have "contour_integral neg_line (f s) = integral {-R..-r} (\<lambda>x. f s (complex_of_real x))"
    unfolding neg_line_def using r_R by (subst contour_integral_linepath_Reals_eq) auto
  also have "\<dots> = exp (- \<i> * pi * s) * 
                    integral {r..R} (\<lambda>x. exp (-ln x * s) * exp (-a * x) / (1 - exp (-x)))"
    (is "_ = _ * ?I") unfolding integral_mult_right [symmetric] using r_R
    by (subst Henstock_Kurzweil_Integration.integral_reflect_real [symmetric], intro integral_cong)
       (auto simp: f_def exp_of_real Ln'_of_real_neg exp_minus exp_Reals_eq
                   exp_diff exp_add field_simps)
  also have "?I = integral {r..R} (\<lambda>x. x powr (-s) * exp (-a * x) / (1 - exp (-x)))" using r_R
    by (intro integral_cong) (auto simp: powr_def Ln_Reals_eq exp_minus exp_diff field_simps)

  also have "contour_integral pos_line (f s) = integral {r..R} (\<lambda>x. f s (complex_of_real x))"
    unfolding pos_line_def using r_R by (subst contour_integral_linepath_Reals_eq) auto
  also have "\<dots> = integral {r..R} (\<lambda>x. x powr (-s) * exp (a * x) / (1 - exp x))"
    using r_R by (intro integral_cong) (simp add: f_def Ln'_of_real_pos exp_diff exp_minus
                                                  exp_Reals_eq field_simps powr_def Ln_Reals_eq)
  finally show ?thesis1 by (simp only: add_ac big_circle_def small_circle_def)
qed

text \<open>
  Next, we need bounds on the integrands of the two semicircles.
\<close>
lemma hurwitz_formula_bound1:
  defines "H \<equiv> \<lambda>z. exp (complex_of_real a * z) / (1 - exp z)"
  assumes "r > 0"
  obtains C where "C \<ge> 0" and "\<And>z. z \<notin> (\<Union>n::int. ball (2 * n * pi * \<i>) r) \<Longrightarrow> norm (H z) \<le> C"
proof -
  define A where "A = cbox (-1 - pi * \<i>) (1 + pi * \<i>) - ball 0 r"
  {
    fix z assume "z \<in> A"
    have "exp z \<noteq> 1"
    proof
      assume "exp z = 1"
      then obtain n :: int where [simp]: "z = 2 * n * pi * \<i>"
        by (subst (asm) exp_eq_1) (auto simp: complex_eq_iff)
      from \<open>z \<in> A\<close> have "(2 * n) * pi \<ge> (-1) * pi" and "(2 * n) * pi \<le> 1 * pi"
        by (auto simp: A_def in_cbox_complex_iff)
      hence "n = 0" by (subst (asm) (1 2) mult_le_cancel_right) auto
      with \<open>z \<in> A\<close> and \<open>r > 0\<close> show False by (simp add: A_def)
    qed
  }
  hence "continuous_on A H"
    by (auto simp: A_def H_def intro!: continuous_intros)
  moreover have "compact A" by (auto simp: A_def compact_eq_bounded_closed)
  ultimately have "compact (H ` A)" by (rule compact_continuous_image)
  hence "bounded (H ` A)" by (rule compact_imp_bounded)
  then obtain C where bound_inside: "\<And>z. z \<in> A \<Longrightarrow> norm (H z) \<le> C"
    by (auto simp: bounded_iff)

  have bound_outside: "norm (H z) \<le> exp 1 / (exp 1 - 1)" if "\<bar>Re z\<bar> > 1" for z
  proof -
    have "norm (H z) = exp (a * Re z) / norm (1 - exp z)"
      by (simp add: H_def norm_divide)
    also have "\<bar>1 - exp (Re z)\<bar> \<le> norm (1 - exp z)"
      by (rule order.trans[OF _ norm_triangle_ineq3]) simp
    hence "exp (a * Re z) / norm (1 - exp z) \<le> exp (a * Re z) / \<bar>1 - exp (Re z)\<bar>"
      using that by (intro divide_left_mono mult_pos_pos) auto
    also have "\<dots> \<le> exp 1 / (exp 1 - 1)"
    proof (cases "Re z > 1")
      case True
      hence "exp (a * Re z) / \<bar>1 - exp (Re z)\<bar> = exp (a * Re z) / (exp (Re z) - 1)"
        by simp
      also have "\<dots> \<le> exp (Re z) / (exp (Re z) - 1)"
        using a True by (intro divide_right_mono) auto
      also have "\<dots> = 1 / (1 - exp (-Re z))" by (simp add: exp_minus field_simps)
      also have "\<dots> \<le> 1 / (1 - exp (-1))" using True by (intro divide_left_mono diff_mono) auto
      also have "\<dots> = exp 1 / (exp 1 - 1)" by (simp add: exp_minus field_simps)
      finally show ?thesis .
    next
      case False
      with that have "Re z < -1" by simp
      hence "exp (a * Re z) / \<bar>1 - exp (Re z)\<bar> = exp (a * Re z) / (1 - exp (Re z))" by simp
      also have "\<dots> \<le> 1 / (1 - exp (Re z))"
        using a and \<open>Re z < -1\<close> by (intro divide_right_mono) (auto intro: mult_nonneg_nonpos)
      also have "\<dots> \<le> 1 / (1 - exp (-1))"
        using \<open>Re z < -1\<close> by (intro divide_left_mono) auto
      also have "\<dots> = exp 1 / (exp 1 - 1)" by (simp add: exp_minus field_simps)
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed

  define D where "D = max C (exp 1 / (exp 1 - 1))"
  have "D \<ge> 0" by (simp add: D_def max.coboundedI2)

  have "norm (H z) \<le> D" if "z \<notin> (\<Union>n::int. ball (2 * n * pi * \<i>) r)" for z
  proof (cases "\<bar>Re z\<bar> \<le> 1")
    case False
    with bound_outside[of z] show ?thesis by (simp add: D_def)
  next
    case True
    define n where "n = \<lfloor>Im z / (2 * pi) + 1 / 2\<rfloor>"

    have "Im (z - 2 * n * pi * \<i>) = frac (Im z / (2 * pi) + 1 / 2) * (2 * pi) - pi"
      by (simp add: n_def frac_def algebra_simps)
    also have "\<dots> \<in> {-pi..<pi}" using frac_lt_1 by simp
    finally have "norm (H (z - 2 * n * pi * \<i>)) \<le> C" using True that
      by (intro bound_inside) (auto simp: A_def in_cbox_complex_iff dist_norm n_def)
    also have "exp (2 * pi * n * \<i>) = 1" by (simp add: exp_eq_polar)
    hence "norm (H (z - 2 * n * pi * \<i>)) = norm (H z)"
      by (simp add: H_def norm_divide exp_diff mult_ac)
    also have "C \<le> D" by (simp add: D_def)
    finally show ?thesis .
  qed
  from \<open>D \<ge> 0\<close> and this show ?thesis by (rule that)
qed

lemma hurwitz_formula_bound2:
  obtains C where "C \<ge> 0" and "\<And>r z. r > 0 \<Longrightarrow> r < pi \<Longrightarrow> z \<in> sphere 0 r \<Longrightarrow>
     norm (f s z) \<le> C * r powr (-Re s - 1)"
proof -
  have "2 * pi > 0" by auto
  have nz: "1 - exp z \<noteq> 0" if "z \<in> ball 0 (2 * pi) - {0}" for z :: complex
  proof
    assume "1 - exp z = 0"
    then obtain n where "z = 2 * pi * of_int n * \<i>"
      by (auto simp: exp_eq_1 complex_eq_iff[of z])
    moreover have "\<bar>real_of_int n\<bar> < 1 \<longleftrightarrow> n = 0" by linarith
    ultimately show False using that by (auto simp: norm_mult)
  qed

  have ev: "eventually (\<lambda>z::complex. 1 - exp z \<noteq> 0) (at 0)"
    using eventually_at_ball'[OF \<open>2 * pi > 0\<close>] by eventually_elim (use nz in auto)
  have [simp]: "subdegree (1 - fps_exp (1 :: complex)) = 1"
    by (intro subdegreeI) auto
  hence "(\<lambda>z. exp (a * z) * (if z = 0 then -1 else z / (1 - exp z :: complex)))
            has_fps_expansion fps_exp a * (fps_X / (fps_const 1 - fps_exp 1))"
    by (auto intro!: fps_expansion_intros)
  hence "(\<lambda>z::complex. exp (a * z) * (if z = 0 then -1 else z / (1 - exp z))) \<in> O[at 0](\<lambda>z. 1)"
    using continuous_imp_bigo_1 has_fps_expansion_imp_continuous by blast
  also have "?this \<longleftrightarrow> (\<lambda>z::complex. exp (a * z) * (z / (1 - exp z))) \<in> O[at 0](\<lambda>z. 1)"
    by (intro landau_o.big.in_cong eventually_mono[OF ev]) auto
  finally have "\<exists>g. g holomorphic_on ball 0 (2 * pi) \<and>
                    (\<forall>z\<in>ball 0 (2 * pi) - {0}. g z = exp (of_real a * z) * (z / (1 - exp z)))" 
    using nz by (intro holomorphic_on_extend holomorphic_intros) auto
  then guess g by (elim exE conjE) note g = this
  hence "continuous_on (ball 0 (2 * pi)) g"
    by (auto dest: holomorphic_on_imp_continuous_on)
  hence "continuous_on (cball 0 pi) g"
    by (rule continuous_on_subset) (subst cball_subset_ball_iff, use pi_gt_zero in auto)
  hence "compact (g ` cball 0 pi)" by (intro compact_continuous_image) auto
  hence "bounded (g ` cball 0 pi)" by (auto simp: compact_imp_bounded)
  then obtain C where C: "\<forall>x\<in>cball 0 pi. norm (g x) \<le> C" by (auto simp: bounded_iff)

  {
    fix r :: real assume r: "r > 0" "r < pi"
    fix z :: complex assume z: "z \<in> sphere 0 r"
    define x where "x = (if Arg z \<le> -pi / 2 then Arg z + 2 * pi else Arg z)"
    have "exp (\<i> * (2 * pi)) = 1" by (simp add: exp_eq_polar)
    with z have "z = r * exp (\<i> * x)" using r pi_gt_zero Arg_eq[of z]
      by (auto simp: x_def exp_add distrib_left)
    have "x > - pi / 2" "x \<le> 3 / 2 * pi" using Arg_le_pi[of z] mpi_less_Arg[of z]
      by (auto simp: x_def)
    note x = \<open>z = r * exp (\<i> * x)\<close> this

    from x r have z': "z \<in> cball 0 pi - {0}"
      using pi_gt3 by (auto simp: norm_mult)
    also have "cball 0 pi \<subseteq> ball (0::complex) (2 * pi)"
      by (subst cball_subset_ball_iff) (use pi_gt_zero in auto)
    hence "cball 0 pi - {0} \<subseteq> ball 0 (2 * pi) - {0::complex}" by blast
    finally have z'': "z \<in> ball 0 (2 * pi) - {0}" .
    hence bound: "norm (exp (a * z) * (z / (1 - exp z))) \<le> C" using C and g and z'
      by force

    have "exp z \<noteq> 1" using nz z'' by auto
    with bound z'' have bound': "norm (exp (a * z) / (1 - exp z)) \<le> C / norm z"
      by (simp add: norm_divide field_simps norm_mult)

    have "Ln' z = of_real (ln r) + Ln' (exp (\<i> * of_real x))"
      using x r by (simp add: Ln'_times_of_real)
    also have "exp (\<i> * pi / 2) = \<i>"
      by (simp add: exp_eq_polar)
    hence "Ln' (exp (\<i> * of_real x)) = Ln (exp (\<i> * of_real (x - pi / 2))) + \<i> * pi / 2"
      by (simp add: algebra_simps Ln'_def exp_diff)
    also have "\<dots> = \<i> * x"
      using x pi_gt3 by (subst Ln_exp) (auto simp: algebra_simps)
    finally have "norm (exp (-Ln' z * s)) = exp (x * Im s - ln r * Re s)"
      by simp
    also {
      have "x * Im s \<le> \<bar>x * Im s\<bar>" by (rule abs_ge_self)
      also have "\<dots> \<le> (3/2 * pi) * \<bar>Im s\<bar>" unfolding abs_mult using x
        by (intro mult_right_mono) auto
      finally have "exp (x * Im s - ln r * Re s) \<le> exp (3 / 2 * pi * \<bar>Im s\<bar> - ln r * Re s)" by simp
    }
    finally have "norm (exp (-Ln' z * s) * (exp (a * z) / (1 - exp z))) \<le>
                    exp (3 / 2 * pi * \<bar>Im s\<bar> - ln r * Re s) * (C / norm z)"
      unfolding norm_mult[of "exp t" for t] by (intro mult_mono bound') simp_all
    also have "norm z = r" using \<open>r > 0\<close> by (simp add: x norm_mult)
    also have "exp (3 / 2 * pi * \<bar>Im s\<bar> - ln r * Re s) = exp (3 / 2 * pi * \<bar>Im s\<bar>) * r powr (-Re s)"
      using r by (simp add: exp_diff powr_def exp_minus inverse_eq_divide)
    finally have "norm (f s z) \<le> C * exp (3 / 2 * pi * \<bar>Im s\<bar>) * r powr (-Re s - 1)" using r
      by (simp add: f_def exp_diff exp_minus field_simps powr_diff)
    also have "\<dots> \<le> max 0 (C * exp (3 / 2 * pi * \<bar>Im s\<bar>)) * r powr (-Re s - 1)"
      by (intro mult_right_mono max.coboundedI2) auto
    finally have "norm (f s z) \<le> \<dots>" .
  }
  with that[of "max 0 (C * exp (3 / 2 * pi * \<bar>Im s\<bar>))"] show ?thesis by auto
qed

text \<open>
  We can now relate the integral along a partial Hankel contour that is cut off at $-\pi$ to
  $\zeta(1 - s, a) / \Gamma(s)$.
\<close>
lemma rGamma_hurwitz_zeta_eq_contour_integral:
  fixes s :: complex and r :: real
  assumes "s \<noteq> 0" and r: "r \<in> {1..<2}" and a: "a > 0"
  defines "err1 \<equiv> (\<lambda>s r. contour_integral (part_circlepath 0 r pi 0) (f s))"
  defines "err2 \<equiv> (\<lambda>s r. cnj (contour_integral (part_circlepath 0 r pi 0) (f (cnj s))))"
  shows   "2 * \<i> * pi * rGamma s * hurwitz_zeta a (1 - s) =
             err2 s r - err1 s r + 2 * \<i> * sin (pi * s) * (CLBINT x:{r..}. g s x)"
  (is "?f s = ?g s")
proof (rule analytic_continuation_open[where f = ?f])
  fix s :: complex assume s: "s \<in> {s. Re s < 0}"

  \<comment>\<open>We first show that the integrals along the Hankel contour cut off at $-\pi$ all have the
     same value, no matter what the radius of the circle is (as long as it is small enough).
     We call this value \<open>C\<close>.

     This argument could be done by a homotopy argument, but it is easier to simply re-use the
     above result about the contour integral along the annulus where we fix the radius of the 
     outer circle to $\pi$.\<close>
  define C where "C = -contour_integral (part_circlepath 0 pi 0 pi) (f s) +
                       cnj (contour_integral (part_circlepath 0 pi 0 pi) (f (cnj s)))"
  have integrable: "set_integrable lborel A (g s)"
    if "A \<in> sets lborel" "A \<subseteq> {0<..}" for A
  proof (rule set_integrable_subset)
    show "set_integrable lborel {0<..} (g s)"
      using Gamma_times_hurwitz_zeta_integrable[of "1 - s" a] s a
      by (simp add: g_def exp_of_real exp_minus integrable_completion set_integrable_def)
  qed (insert that, auto)

  {
    fix r' :: real assume r': "r' \<in> {0<..<2}"
    from hurwitz_formula_integral_semiannulus(2)[of r' s 0] and r'
    have "f s contour_integrable_on part_circlepath 0 r' pi 0"
      by (auto simp: hankel_semiannulus_def add_ac)
  } note integrable_circle = this
  {
    fix r' :: real assume r': "r' \<in> {0<..<2}"
    from hurwitz_formula_integral_semiannulus(2)[of r' "cnj s" 0] and r'
    have "f (cnj s) contour_integrable_on part_circlepath 0 r' pi 0"
      by (auto simp: hankel_semiannulus_def add_ac)
  } note integrable_circle' = this

  have eq: "-2 * \<i> * sin (pi * s) * (CLBINT x:{r..pi}. g s x) + (err1 s r - err2 s r) = C"
    if r: "r \<in> {0<..<2}" for r :: real
  proof -
    have eq1: "integral {r..pi} (\<lambda>x. cnj (x powr - cnj s) * (exp (- (a * x))) / (1 - (exp (- x)))) =
               integral {r..pi} (g s)" using r
      by (intro integral_cong) (auto simp: cnj_powr g_def exp_of_real exp_minus)
    have eq2: "integral {r..pi} (\<lambda>x. cnj (x powr - cnj s) * (exp (a * x)) / (1 - (exp x))) =
               integral {r..pi} (\<lambda>x. x powr - s * (exp (a * x)) / (1 - (exp x)))" using r
      by (intro integral_cong) (auto simp: cnj_powr)
  
    from hurwitz_formula_integral_semiannulus(1)[of r s 0] hurwitz_formula_integral_semiannulus(1)[of r "cnj s" 0]
    have "exp (-\<i>*pi * s) *
            integral {r..real (2*0+1) * pi} (g s) +
            integral {r..real (2*0+1) * pi} (\<lambda>x. x powr -s * exp (a * x) / (1 - exp x)) +
            contour_integral (part_circlepath 0 (real (2 * 0 + 1) * pi) 0 pi) (f s) +
            contour_integral (part_circlepath 0 r pi 0) (f s) - cnj (
          exp (-\<i>*pi * cnj s) *
            integral {r..real (2*0+1) * pi} (\<lambda>x. x powr - cnj s * exp (-a*x) / (1 - exp (-x))) +
            integral {r..real (2*0+1) * pi} (\<lambda>x. x powr - cnj s * exp (a*x) / (1 - exp x)) +
            contour_integral (part_circlepath 0 (real (2 * 0 + 1) * pi) 0 pi) (f (cnj s)) +
            contour_integral (part_circlepath 0 r pi 0) (f (cnj s))) = 0" (is "?lhs = _") 
      unfolding g_def using r by (subst (1 2) hurwitz_formula_integral_semiannulus) auto
    also have "?lhs = -2 * \<i> * sin (pi * s) * integral {r..pi} (g s) + err1 s r - err2 s r - C"
      using eq1 eq2
      by (auto simp: integral_cnj exp_cnj err1_def err2_def sin_exp_eq algebra_simps C_def)
    also have "integral {r..pi} (g s) = (CLBINT x:{r..pi}. g s x)" using r
      by (intro set_borel_integral_eq_integral(2) [symmetric] integrable) auto
    finally show "-2 * \<i> * sin (pi * s) * (CLBINT x:{r..pi}. g s x) + (err1 s r - err2 s r) = C"
      by (simp add: algebra_simps)
  qed

  \<comment>\<open>Next, compute the value of @{term C} by letting the radius tend to 0 so that the contribution
     of the circle vanishes.\<close>
  have "((\<lambda>r. -2 * \<i> * sin (pi * s) * (CLBINT x:{r..pi}. g s x)  + (err1 s r - err2 s r)) \<longlongrightarrow>
             -2 * \<i> * sin (pi * s) * (CLBINT x:{0<..pi}. g s x) + 0) (at_right 0)"
  proof (intro tendsto_intros tendsto_set_lebesgue_integral_at_right integrable)
    from hurwitz_formula_bound2[of s] guess C1 . note C1 = this
    from hurwitz_formula_bound2[of "cnj s"] guess C2 . note C2 = this
    have ev: "eventually (\<lambda>r::real. r \<in> {0<..<2}) (at_right 0)"
      by (intro eventually_at_right_real) auto
    show "((\<lambda>r. err1 s r - err2 s r) \<longlongrightarrow> 0) (at_right 0)"
    proof (rule Lim_null_comparison[OF eventually_mono[OF ev]])
      fix r :: real assume r: "r \<in> {0<..<2}"
      have "norm (err1 s r - err2 s r) \<le> norm (err1 s r) + norm (err2 s r)"
        by (rule norm_triangle_ineq4)
      also have "norm (err1 s r) \<le> C1 * r powr (- Re s - 1) * r * \<bar>0 - pi\<bar>"
        unfolding err1_def using C1(1) C1(2)[of r] pi_gt3 integrable_circle[of r]
          path_image_part_circlepath_subset'[of r 0 pi 0] r
        by (intro contour_integral_bound_part_circlepath) auto
      also have "\<dots> = C1 * r powr (-Re s) * pi" using r
        by (simp add: powr_diff field_simps)
      also have "norm (err2 s r) \<le> C2 * r powr (- Re s - 1) * r * \<bar>0 - pi\<bar>"
        unfolding err2_def complex_mod_cnj using C2(1) C2(2)[of r] r
          pi_gt3 integrable_circle'[of r] path_image_part_circlepath_subset'[of r 0 pi 0]
        by (intro contour_integral_bound_part_circlepath) auto
      also have "\<dots> = C2 * r powr (-Re s) * pi" using r
        by (simp add: powr_diff field_simps)
      also have "C1 * r powr (-Re s) * pi + C2 * r powr (-Re s) * pi =
                   (C1 + C2) * pi * r powr (-Re s)" by (simp add: algebra_simps)
      finally show "norm (err1 s r - err2 s r) \<le> (C1 + C2) * pi * r powr - Re s" by simp
    next
      show "((\<lambda>x. (C1 + C2) * pi * x powr - Re s) \<longlongrightarrow> 0) (at_right 0)" using s
        by (auto intro!: tendsto_eq_intros simp: eventually_at exI[of _ 1])
    qed
  qed auto
  moreover have "eventually (\<lambda>r::real. r \<in> {0<..<2}) (at_right 0)"
    by (intro eventually_at_right_real) auto
  hence "eventually (\<lambda>r. -2 * \<i> * sin (pi * s) * (CLBINT x:{r..pi}. g s x) +
           (err1 s r - err2 s r) = C) (at_right 0)" by eventually_elim (use eq in auto)
  hence "((\<lambda>r. -2 * \<i> * sin (pi * s) * (CLBINT x:{r..pi}. g s x)  + (err1 s r - err2 s r)) \<longlongrightarrow> C)
            (at_right 0)" by (rule tendsto_eventually)
  ultimately have [simp]: "C = -2 * \<i> * sin (pi * s) * (CLBINT x:{0<..pi}. g s x)"
    using tendsto_unique by force

  \<comment>\<open>We now rearrange everything and obtain the result.\<close>
  have "2 * \<i> * sin (pi * s) * ((CLBINT x:{0<..pi}. g s x) - (CLBINT x:{r..pi}. g s x)) =
          err2 s r - err1 s r"
    using eq[of r] r by (simp add: algebra_simps)
  also have "{0<..pi} = {0<..<r} \<union> {r..pi}" using r pi_gt3 by auto
  also have "(CLBINT x:\<dots>. g s x) - (CLBINT x:{r..pi}. g s x) = (CLBINT x:{0<..<r}. g s x)"
    using r pi_gt3 by (subst set_integral_Un[OF _ integrable integrable]) auto
  also have "(CLBINT x:{0<..<r}. g s x) =
               (CLBINT x:{0<..<r} \<union> {r..}. g s x) - (CLBINT x:{r..}. g s x)"
    using r pi_gt3 by (subst set_integral_Un[OF _ integrable integrable]) auto
  also have "{0<..<r} \<union> {r..} = {0<..}" using r by auto
  also have "(CLBINT x:{0<..}. g s x) = Gamma (1 - s) * hurwitz_zeta a (1 - s)"
    using Gamma_times_hurwitz_zeta_integral[of "1 - s" a] s a
    by (simp add: g_def exp_of_real exp_minus integral_completion set_lebesgue_integral_def)
  finally have "2 * \<i> * (sin (pi * s) * Gamma (1 - s)) * hurwitz_zeta a (1 - s) =
                  err2 s r - err1 s r + 2 * \<i> * sin (pi * s) * (CLBINT x:{r..}. g s x)"
    by (simp add: algebra_simps)
  also have "sin (pi * s) * Gamma (1 - s) = pi * rGamma s"
  proof (cases "s \<in> \<int>")
    case False
    with Gamma_reflection_complex[of s] show ?thesis
      by (auto simp: divide_simps sin_eq_0 Ints_def rGamma_inverse_Gamma mult_ac split: if_splits)
  next
    case True
    with s have "rGamma s = 0"
      by (auto simp: rGamma_eq_zero_iff nonpos_Ints_def Ints_def)
    moreover from True have "sin (pi * s) = 0"
      by (subst sin_eq_0) (auto elim!: Ints_cases)
    ultimately show ?thesis by simp
  qed
  finally show "2 * \<i> * pi * rGamma s * hurwitz_zeta a (1 - s) =
                  err2 s r - err1 s r + 2 * \<i> * sin (pi * s) * (CLBINT x:{r..}. g s x)"
    by (simp add: mult_ac)
next
  \<comment>\<open>By analytic continuation, we lift the result to the case of any non-zero @{term s}.\<close>
  show "(\<lambda>s. 2 * \<i> * pi * rGamma s * hurwitz_zeta a (1 - s)) holomorphic_on - {0}" using a
    by (auto intro!: holomorphic_intros)
  show "(\<lambda>s. err2 s r - err1 s r + 2 * \<i> * sin (pi * s) * (CLBINT x:{r..}. g s x))
           holomorphic_on -{0}"
  proof (intro holomorphic_intros)
    have "(\<lambda>s. err2 s r) = (\<lambda>s. - cnj (integral {0..pi} (h r (cnj s))))" using r
      by (simp add: err2_def contour_integral_part_circlepath_reverse'
                    contour_integral_part_circlepath_h)
    also have "(\<lambda>s. - cnj (integral {0..pi} (h r (cnj s)))) = 
               (\<lambda>s. (integral {0..pi} (\<lambda>x. h r s (-x))))" using r
      by (simp add: integral_cnj h_def exp_cnj cis_cnj Ln_Reals_eq)
    also have "\<dots> = (\<lambda>s. integral {-pi..0} (h r s))"
      by (subst Henstock_Kurzweil_Integration.integral_reflect_real [symmetric]) simp
    finally have "(\<lambda>s. err2 s r) = \<dots>" .
    moreover have "(\<lambda>s. integral {-pi..0} (h r s)) holomorphic_on -{0}"
      using r by (intro integral_h_holomorphic) auto
    ultimately show "(\<lambda>s. err2 s r) holomorphic_on -{0}" by simp
  next
    have "(\<lambda>s. - integral {0..pi} (h r s)) holomorphic_on -{0}" using r
      by (intro holomorphic_intros integral_h_holomorphic) auto
    also have "(\<lambda>s. - integral {0..pi} (h r s)) = (\<lambda>s. err1 s r)"
      unfolding err1_def using r
      by (simp add: contour_integral_part_circlepath_reverse' contour_integral_part_circlepath_h)
    finally show "(\<lambda>s. err1 s r) holomorphic_on -{0}" .
  next
    show "(\<lambda>s. CLBINT x:{r..}. g s x) holomorphic_on -{0}"
    proof (rule holomorphic_on_balls_imp_entire')
      fix R :: real
      have "eventually (\<lambda>b. b > r) at_top" by (rule eventually_gt_at_top)
      hence 1: "eventually (\<lambda>b. continuous_on (cball 0 R) (\<lambda>s. CLBINT x:{r..b}. g s x) \<and>
                                (\<lambda>s. CLBINT x:{r..b}. g s x) holomorphic_on ball 0 R) at_top"
      proof eventually_elim
        case (elim b)
        have integrable: "set_integrable lborel {r..b} (g s)" for s unfolding g_def using r
              by (intro borel_integrable_atLeastAtMost' continuous_intros) auto
        have "(\<lambda>s. integral {r..b} (g s)) holomorphic_on UNIV" using r
          by (intro integral_g_holomorphic) auto
        also have "(\<lambda>s. integral {r..b} (g s)) = (\<lambda>s. CLBINT x:{r..b}. g s x)"
          by (intro ext set_borel_integral_eq_integral(2)[symmetric] integrable)
        finally have "\<dots> holomorphic_on UNIV" .
        thus ?case by (auto intro!: holomorphic_on_imp_continuous_on)
      qed

      have 2: "uniform_limit (cball 0 R) (\<lambda>b s. CLBINT x:{r..b}. g s x)
                 (\<lambda>s. CLBINT x:{r..}. g s x) at_top"
      proof (rule uniform_limit_set_lebesgue_integral_at_top)
        fix s :: complex and x :: real
        assume s: "s \<in> cball 0 R" and x: "x \<ge> r"
        have "norm (g s x) = x powr -Re s * exp (-a * x) / (1 - exp (-x))" using x r
          by (simp add: g_def norm_mult norm_divide in_Reals_norm norm_powr_real_powr)
        also have "\<dots> \<le> x powr R * exp (-a * x) / (1 - exp (-x))" using r s x abs_Re_le_cmod[of s]
          by (intro mult_right_mono divide_right_mono powr_mono) auto
        finally show "norm (g s x) \<le> x powr R * exp (- a * x) / (1 - exp (- x))" .
      next
        show "set_integrable lborel {r..} (\<lambda>x. x powr R * exp (-a * x) / (1 - exp (-x)))"
          using r a by (intro set_integrable_Gamma_hurwitz_aux2_real) auto
      qed (simp_all add: set_borel_measurable_def g_def)
  
      show "(\<lambda>s. CLBINT x:{r..}. g s x) holomorphic_on ball 0 R"
        using holomorphic_uniform_limit[OF 1 2] by auto
    qed
  qed
qed (insert \<open>s \<noteq> 0\<close>, 
     auto simp: connected_punctured_universe open_halfspace_Re_lt intro: exI[of _ "-1"])
    
text \<open>
  Finally, we obtain Hurwitz's formula by letting the radius of the outer circle tend to \<open>\<infinity>\<close>.
\<close>
lemma hurwitz_zeta_formula_aux:
  fixes s :: complex
  assumes s: "Re s > 1"
  shows   "rGamma s * hurwitz_zeta a (1 - s) = (2 * pi) powr -s * 
                  (\<i> powr (-s) * F a s + \<i> powr s * F (-a) s)"
proof -
  from s have [simp]: "s \<noteq> 0" by auto
  define r where "r = (1 :: real)"
  have r: "r \<in> {0<..<2}" by (simp add: r_def)
  define R where "R = (\<lambda>n. real (2 * n + 1) * pi)"
  define bigc where "bigc = (\<lambda>n. contour_integral (part_circlepath 0 (R n) 0 pi) (f s) -
                                 cnj (contour_integral (part_circlepath 0 (R n) 0 pi) (f (cnj s))))"
  define smallc where "smallc = contour_integral (part_circlepath 0 r pi 0) (f s) - 
                                cnj (contour_integral (part_circlepath 0 r pi 0) (f (cnj s)))"
  define I where "I = (\<lambda>n. CLBINT x:{r..R n}. g s x)"

  define F1 and F2 where
    "F1 = (\<lambda>n. exp (-s * pi * \<i> / 2) * (\<Sum>k\<in>{0<..n}. exp (2 * real k * pi * a * \<i>) * k powr (-s)))"
    "F2 = (\<lambda>n. exp (s * pi * \<i> / 2) * (\<Sum>k\<in>{0<..n}. exp (2 * real k * pi * (-a) * \<i>) * k powr (-s)))"
  
  have R: "R n \<ge> pi" for n using r by (auto simp: R_def field_simps)
  have [simp]: "\<not>(pi \<le> 0)" using pi_gt_zero by linarith

  have integrable: "set_integrable lborel A (g s)"
    if "A \<in> sets lborel" "A \<subseteq> {r..}" for A
  proof -
    have "set_integrable lborel {r..} (g s)"
      using set_integrable_Gamma_hurwitz_aux2[of r a s] a r
      by (simp add: g_def exp_of_real exp_minus)
    thus ?thesis by (rule set_integrable_subset) (use that in auto)
  qed

  {
    fix n :: nat
    from hurwitz_formula_integral_semiannulus(2)[of "r" s n] and r R[of n]
    have "f s contour_integrable_on part_circlepath 0 (R n) 0 pi"
      by (auto simp: hankel_semiannulus_def R_def add_ac)
  } note integrable_circle = this
  {
    fix n :: nat
    from hurwitz_formula_integral_semiannulus(2)[of "r" "cnj s" n] and r R[of n]
    have "f (cnj s) contour_integrable_on part_circlepath 0 (R n) 0 pi"
      by (auto simp: hankel_semiannulus_def R_def add_ac)
  } note integrable_circle' = this

  {
    fix n :: nat
    have "(exp (-\<i> * pi * s) * integral {r..R n} (g s) +
            integral {r..R n} (\<lambda>x. x powr (-s) * exp (a * x) / (1 - exp x)) +
            contour_integral (part_circlepath 0 (R n) 0 pi) (f s) +
            contour_integral (part_circlepath 0 r pi 0) (f s)) - cnj (
           exp (-\<i> * pi * cnj s) * integral {r..R n} (g (cnj s)) +
            integral {r..R n} (\<lambda>x. x powr (-cnj s) * exp (a * x) / (1 - exp x)) +
            contour_integral (part_circlepath 0 (R n) 0 pi) (f (cnj s)) +
            contour_integral (part_circlepath 0 r pi 0) (f (cnj s)))
           = -2 * pi * \<i> * exp (- s * of_real pi * \<i> / 2) * (\<Sum>k\<in>{0<..n}. Res s k) -
             cnj (-2 * pi * \<i> * exp (- cnj s * of_real pi * \<i> / 2) * (\<Sum>k\<in>{0<..n}. Res (cnj s) k))"
      (is "?lhs = ?rhs") unfolding R_def g_def using r
      by (subst (1 2) hurwitz_formula_integral_semiannulus) auto
    also have "?rhs = -2 * pi * \<i> * (exp (- s * pi * \<i> / 2) * (\<Sum>k\<in>{0<..n}. Res s k) +
                                     exp (s * pi * \<i> / 2) * (\<Sum>k\<in>{0<..n}. cnj (Res (cnj s) k)))"
      by (simp add: exp_cnj sum.distrib algebra_simps sum_distrib_left sum_distrib_right sum_negf)
    also have "(\<Sum>k\<in>{0<..n}. Res s k) = 
                 (2 * pi) powr (-s) * (\<Sum>k\<in>{0<..n}. exp (2 * k * pi * a * \<i>) * k powr (-s))"
      (is "_ = ?S1") by (simp add: Res_def powr_times_real algebra_simps sum_distrib_left)
    also have "(\<Sum>k\<in>{0<..n}. cnj (Res (cnj s) k)) =
                 (2 * pi) powr (-s) * (\<Sum>k\<in>{0<..n}. exp (-2 * k * pi * a * \<i>) * k powr (-s))"
      by (simp add: Res_def cnj_powr powr_times_real algebra_simps exp_cnj sum_distrib_left)
    also have "exp (-s * pi * \<i> / 2) * ?S1 + exp (s * pi * \<i> / 2) * \<dots> =
                 (2 * pi) powr (-s) *
                   (exp (-s * pi * \<i> / 2) * (\<Sum>k\<in>{0<..n}. exp (2 * k * pi * a * \<i>) * k powr (-s)) +
                    exp (s * pi * \<i> / 2) * (\<Sum>k\<in>{0<..n}. exp (-2 * k * pi * a * \<i>) * k powr (-s)))"
      by (simp add: algebra_simps)
    also have 1: "integral {r..R n} (g s) = I n" unfolding I_def
      by (intro set_borel_integral_eq_integral(2) [symmetric] integrable) auto
    have 2: "cnj (integral {r..R n} (g (cnj s))) = integral {r..R n} (g s)" using r
      unfolding integral_cnj by (intro integral_cong) (auto simp: g_def cnj_powr)
    have 3: "integral {r..R n} (\<lambda>x. exp (x * a) * cnj (x powr - cnj s) / (1 - exp x)) =
             integral {r..R n} (\<lambda>x. exp (x * a) * of_real x powr - s / (1 - exp x))"
      unfolding I_def g_def using r R[of n] by (intro integral_cong; force simp: cnj_powr)+
    from 1 2 3 have "?lhs = (exp (-\<i> * s * pi) - exp (\<i> * s * pi)) * I n + bigc n + smallc"
      by (simp add: integral_cnj cnj_powr algebra_simps exp_cnj
                    bigc_def smallc_def g_def)
    also have "exp (-\<i> * s * pi) - exp (\<i> * s * pi) = -2 * \<i> * sin (s * pi)"
      by (simp add: sin_exp_eq' algebra_simps)
    finally have "(- 2 * \<i> * sin (s * pi) * I n + smallc) + bigc n = 
                    -2 * \<i> * pi * (2 * pi) powr (-s) * (F1 n + F2 n)"
      by (simp add: F1_F2_def algebra_simps)
  } note eq = this

  
  have "(\<lambda>n. - 2 * \<i> * sin (s * pi) * I n + smallc + bigc n) \<longlonglongrightarrow>
           (-2 * \<i> * sin (s * pi)) * (CLBINT x:{r..}. g s x) + smallc + 0"
    unfolding I_def
  proof (intro tendsto_intros filterlim_compose[OF tendsto_set_lebesgue_integral_at_top] integrable)
    show "filterlim R at_top sequentially" unfolding R_def
      by (intro filterlim_at_top_mult_tendsto_pos[OF tendsto_const] pi_gt_zero
                filterlim_compose[OF filterlim_real_sequentially] filterlim_subseq) 
         (auto simp: strict_mono_Suc_iff)

    from hurwitz_formula_bound1[OF pi_gt_zero] guess C . note C = this
    define D where "D = C * exp (3 / 2 * pi * \<bar>Im s\<bar>)"
    from \<open>C \<ge> 0\<close> have "D \<ge> 0" by (simp add: D_def)
    show "bigc \<longlonglongrightarrow> 0"
    proof (rule Lim_null_comparison[OF always_eventually[OF allI]])
      fix n :: nat
      have bound: "norm (f s' z) \<le> D * R n powr (-Re s')"
        if z: "z \<in> sphere 0 (R n)" "Re s' = Re s" "\<bar>Im s'\<bar> = \<bar>Im s\<bar>" for z s'
      proof -
        from z and r R[of n] have [simp]: "z \<noteq> 0" by auto
        have not_in_ball: "z \<notin> ball (2 * m * pi * \<i>) pi" for m :: int
        proof -
          have "dist z (2 * m * pi * \<i>) \<ge> \<bar>dist z 0 - dist 0 (2 * m * pi * \<i>)\<bar>"
            by (rule abs_dist_diff_le)
          also have "dist 0 (2 * m * pi * \<i>) = 2 * \<bar>m\<bar> * pi"
            by (simp add: norm_mult)
          also from z have "dist z 0 = R n" by simp
          also have "R n - 2 * \<bar>m\<bar> * pi = (int (2 * n + 1) - 2 * \<bar>m\<bar>) * pi"
            by (simp add: R_def algebra_simps)
          also have "\<bar>\<dots>\<bar> = \<bar>int (2 * n + 1) - 2 * \<bar>m\<bar>\<bar> * pi"
            by (subst abs_mult) simp_all
          also have "\<bar>int (2 * n + 1) - 2 * \<bar>m\<bar>\<bar> \<ge> 1" by presburger
          hence "\<dots> * pi \<ge> 1 * pi" by (intro mult_right_mono) auto
          finally show ?thesis by (simp add: dist_commute)
        qed

        have "norm (f s' z) = norm (exp (-Ln' z * s')) * norm (exp (a * z) / (1 - exp z))"
          by (simp add: f_def exp_diff norm_mult norm_divide mult_ac exp_minus norm_inverse
                        divide_simps del: norm_exp_eq_Re)
        also have "\<dots> \<le> norm (exp (-Ln' z * s')) * C" using not_in_ball
          by (intro mult_left_mono C) auto
        also have "norm (exp (-Ln' z * s')) = 
                     exp (Im s' * (Im (Ln (- (\<i> * z))) + pi / 2)) / exp (Re s' * ln (R n))"
          using z r R[of n] pi_gt_zero
          by (simp add: Ln'_def norm_mult norm_divide exp_add exp_diff exp_minus
                        norm_inverse algebra_simps inverse_eq_divide)
        also have "\<dots> \<le> exp (3/2 * pi * \<bar>Im s'\<bar>) / exp (Re s' * ln (R n))"
        proof (intro divide_right_mono, subst exp_le_cancel_iff)
          have "Im s' * (Im (Ln (- (\<i> * z))) + pi / 2) \<le> \<bar>Im s' * (Im (Ln (- (\<i> * z))) + pi / 2)\<bar>"
            by (rule abs_ge_self)
          also have "\<dots> \<le> \<bar>Im s'\<bar> * (pi + pi / 2)"
            unfolding abs_mult using mpi_less_Im_Ln[of "- (\<i> * z)"] Im_Ln_le_pi[of "- (\<i> * z)"]
            by (intro mult_left_mono order.trans[OF abs_triangle_ineq] add_mono) auto
          finally show "Im s' * (Im (Ln (- (\<i> * z))) + pi / 2) \<le> 3/2 * pi * \<bar>Im s'\<bar>"
            by (simp add: algebra_simps)
        qed auto
        also have "exp (Re s' * ln (R n)) = R n powr Re s'"
          using r R[of n] by (auto simp: powr_def)
        finally show "norm (f s' z) \<le> D * R n powr (-Re s')" using \<open>C \<ge> 0\<close>
          by (simp add:  that D_def powr_minus mult_right_mono mult_left_mono field_simps)
      qed

      have "norm (bigc n) \<le> norm (contour_integral (part_circlepath 0 (R n) 0 pi) (f s)) +
              norm (cnj (contour_integral (part_circlepath 0 (R n) 0 pi) (f (cnj s))))"
        (is "_ \<le> norm ?err1 + norm ?err2") unfolding bigc_def by (rule norm_triangle_ineq4)
      also have "norm ?err1 \<le> D * R n powr (-Re s) * R n * \<bar>pi - 0\<bar>"
        using \<open>D \<ge> 0\<close> and r R[of n] and pi_gt3 and integrable_circle and
              path_image_part_circlepath_subset[of 0 pi "R n" 0] and bound[of _ s]
        by (intro contour_integral_bound_part_circlepath) auto
      also have "\<dots> = D * pi * R n powr (1 - Re s)" using r R[of n] pi_gt3
        by (simp add: powr_diff field_simps powr_minus)
      also have "norm ?err2 \<le> D * R n powr (-Re s) * R n * \<bar>pi - 0\<bar>"
        unfolding complex_mod_cnj
        using \<open>D \<ge> 0\<close> and r R[of n] and pi_gt3 and integrable_circle'[of n] and
              path_image_part_circlepath_subset[of 0 pi "R n" 0] and bound[of _ "cnj s"]
        by (intro contour_integral_bound_part_circlepath) auto
      also have "\<dots> = D * pi * R n powr (1 - Re s)" using r R[of n] pi_gt3
        by (simp add: powr_diff field_simps powr_minus)
      finally show "norm (bigc n) \<le> 2 * D * pi * R n powr (1 - Re s)"
        by simp
    next
      have "filterlim R at_top at_top" by fact
      hence "(\<lambda>x. 2 * D * pi * R x powr (1 - Re s)) \<longlonglongrightarrow> 2 * D * pi * 0" using s unfolding R_def
        by (intro tendsto_intros tendsto_neg_powr) auto
      thus "(\<lambda>x. 2 * D * pi * R x powr (1 - Re s)) \<longlonglongrightarrow> 0" by simp
    qed
  qed auto
  also have "(\<lambda>n. - 2 * \<i> * sin (s * pi) * I n + smallc + bigc n) =
               (\<lambda>n. -2 * \<i> * pi * (2 * pi) powr -s * (F1 n + F2 n))" by (subst eq) auto
  finally have "\<dots> \<longlonglongrightarrow> (-2 * \<i> * sin (s * pi)) * (CLBINT x:{r..}. g s x) + smallc" by simp

  moreover have "(\<lambda>n. -2 * \<i> * pi * (2 * pi) powr -s * (F1 n + F2 n)) \<longlonglongrightarrow>
                   -2 * \<i> * pi * (2 * pi) powr -s * 
                   (exp (-s * pi * \<i> / 2) * F a s + exp (s * pi * \<i> / 2) * F (-a) s)"
    unfolding F1_F2_def F_def using s by (intro tendsto_intros sum_tendsto_fds_perzeta)
  ultimately have "-2 * \<i> * pi * (2 * pi) powr -s * 
                       (exp (-s * pi * \<i> / 2) * F a s + exp (s * pi * \<i> / 2) * F (-a) s) =
                     (-2 * \<i> * sin (s * pi)) * (CLBINT x:{r..}. g s x) + smallc"
    by (force intro: tendsto_unique)
  also have "\<dots> = -2 * \<i> * pi * rGamma s * hurwitz_zeta a (1 - s)" using s r a
    using rGamma_hurwitz_zeta_eq_contour_integral[of s r]
    by (simp add: r_def smallc_def algebra_simps)
  also have "exp (- s * complex_of_real pi * \<i> / 2) = \<i> powr (-s)"
    by (simp add: powr_def field_simps)
  also have "exp (s * complex_of_real pi * \<i> / 2) = \<i> powr s"
    by (simp add: powr_def field_simps)
  finally show "rGamma s * hurwitz_zeta a (1 - s) = (2 * pi) powr -s * 
                  (\<i> powr (-s) * F a s + \<i> powr s * F (-a) s)" by simp
qed

end

text \<open>
  We can now use Hurwitz's formula to prove the following nice formula that expresses the periodic 
  zeta function in terms of the Hurwitz zeta function:
  \[F(s, a) = (2\pi)^{s-1} i \Gamma(1 - s)
                \left(i^{-s} \zeta(1 - s, a) - i^{s} \zeta(1 - s, 1 - a)\right)\]
  This holds for all \<open>s\<close> with \<open>\mathfrak{R}(s) > 0\<close> as long as \<open>a \<notin> \<int>\<close>. For convenience, we
  move the \<open>\<Gamma>\<close> function to the left-hand side in order to avoid having to account for its poles.
\<close>
lemma perzeta_conv_hurwitz_zeta_aux:
  fixes a :: real and s :: complex
  assumes a: "a \<in> {0<..<1}" and s: "Re s > 0"
  shows   "rGamma (1 - s) * eval_fds (fds_perzeta a) s = (2 * pi) powr (s - 1) * \<i> *
             (\<i> powr -s * hurwitz_zeta a (1 - s) -
              \<i> powr s * hurwitz_zeta (1 - a) (1 - s))" 
  (is "?lhs s = ?rhs s")
proof (rule analytic_continuation_open[where f = ?lhs])
  show "connected {s. Re s > 0}"
    by (intro convex_connected convex_halfspace_Re_gt)
  show "{s. Re s > 1} \<noteq> {}" by (auto intro: exI[of _ 2])
  show "(\<lambda>s. rGamma (1 - s) * eval_fds (fds_perzeta a) s) holomorphic_on {s. 0 < Re s}"
    unfolding perzeta_def using a
    by (auto intro!: holomorphic_intros le_less_trans[OF conv_abscissa_perzeta'] elim!: Ints_cases)
  show "?rhs holomorphic_on {s. 0 < Re s}" using assms by (auto intro!: holomorphic_intros)
next
  fix s assume s: "s \<in> {s. Re s > 1}"
  have [simp]: "fds_perzeta (1 - a) = fds_perzeta (-a)"
    using fds_perzeta.plus_of_nat[of "-a" 1] by simp
  have [simp]: "fds_perzeta (a - 1) = fds_perzeta a"
    using fds_perzeta.minus_of_nat[of a 1] by simp
  from s have [simp]: "Gamma s \<noteq> 0" by (auto simp: Gamma_eq_zero_iff elim!: nonpos_Ints_cases)

  have "(2 * pi) powr (-s) * (\<i> * (\<i> powr (-s) * (rGamma s * hurwitz_zeta a (1 - s)) -
                              \<i> powr s * (rGamma s * hurwitz_zeta (1 - a) (1 - s)))) =
        (2 * pi) powr (-s) * ((\<i> powr (1 - s) * (rGamma s * hurwitz_zeta a (1 - s)) +
                               \<i> powr (s - 1) * (rGamma s * hurwitz_zeta (1 - a) (1 - s))))"
    by (simp add: powr_diff field_simps powr_minus)
  also have "\<dots> = ((2 * pi) powr (-s)) ^ 2 * (
          eval_fds (fds_perzeta a) s * (\<i> powr s * \<i> powr (s - 1) + \<i> powr (-s) * \<i> powr (1 - s)) +
          eval_fds (fds_perzeta (-a)) s * (\<i> powr s * \<i> powr (1 - s) + \<i> powr (-s) * \<i> powr (s - 1)))"
    using s a by (subst (1 2) hurwitz_zeta_formula_aux) (auto simp: algebra_simps power2_eq_square)
  also have "(\<i> powr s * \<i> powr (1 - s) + \<i> powr (-s) * \<i> powr (s - 1)) = 
               exp (\<i> * complex_of_real pi / 2) + exp (- (\<i> * complex_of_real pi / 2))"
    by (simp add: powr_def exp_add [symmetric] field_simps)
  also have "\<dots> = 0" by (simp add: exp_eq_polar)
  also have "\<i> powr s * \<i> powr (s - 1) = \<i> powr (2 * s - 1)"
    by (simp add: powr_def exp_add [symmetric] field_simps)
  also have "\<i> powr (-s) * \<i> powr (1 - s) = \<i> powr (1 - 2 * s)"
    by (simp add: powr_def exp_add [symmetric] field_simps)
  also have "\<i> powr (2 * s - 1) + \<i> powr (1 - 2 * s) = 2 * cos ((2 * s - 1) * pi / 2)"
    by (simp add: powr_def cos_exp_eq algebra_simps minus_divide_left cos_sin_eq)
  also have "\<dots> = 2 * sin (pi - s * pi)" by (simp add: cos_sin_eq field_simps)
  also have "\<dots> = 2 * sin (s * pi)" by (simp add: sin_diff)
  finally have "\<i> * (rGamma s * \<i> powr (-s) * hurwitz_zeta a (1 - s) -
                     rGamma s * \<i> powr s * hurwitz_zeta (1 - a) (1 - s)) =
                2 * (2 * pi) powr -s * sin (s * pi) * eval_fds (fds_perzeta a) s"
    by (simp add: power2_eq_square mult_ac)
  hence "(2 * pi) powr s / 2 * \<i> *
           (\<i> powr (-s) * hurwitz_zeta a (1 - s) -
            \<i> powr s * hurwitz_zeta (1 - a) (1 - s)) =
         Gamma s * sin (s * pi) * eval_fds (fds_perzeta a) s"
    by (subst (asm) (2) powr_minus) (simp add: field_simps rGamma_inverse_Gamma)
  also have "Gamma s * sin (s * pi) = pi * rGamma (1 - s)"
    using Gamma_reflection_complex[of s]
    by (auto simp: divide_simps rGamma_inverse_Gamma mult_ac split: if_splits)
  finally show "?lhs s = ?rhs s" by (simp add: powr_diff)
qed (insert s, auto simp: open_halfspace_Re_gt)

text \<open>
  We can now use the above equation as a defining equation to continue the periodic
  zeta function $F$ to the entire complex plane except at non-negative integer values for \<open>s\<close>.
  However, the positive integers are already covered by the original Dirichlet series definition
  of $F$, so we only need to take care of \<open>s = 0\<close>. We do this by cancelling the pole of \<open>\<Gamma>\<close> at \<open>0\<close>
  with the zero of $i^{-s} \zeta(1 - s, a) - i^s \zeta(1 - s, 1 - a)$.
\<close>
lemma
  assumes "q' \<notin> \<int>"
  shows   holomorphic_perzeta': "perzeta q' holomorphic_on A"
    and   perzeta_altdef2:   "Re s > 0 \<Longrightarrow> perzeta q' s = eval_fds (fds_perzeta q') s"
proof -
  define q where "q = frac q'"
  from assms have q: "q \<in> {0<..<1}" by (auto simp: q_def frac_lt_1)
  hence [simp]: "q \<notin> \<int>" by (auto elim!: Ints_cases)
  have [simp]: "frac q = q" by (simp add: q_def frac_def)
  define f where "f = (\<lambda>s. complex_of_real (2 * pi) powr (s - 1) * \<i> * Gamma (1 - s) *
                        (\<i> powr (-s) * hurwitz_zeta q (1 - s) -
                         \<i> powr s * hurwitz_zeta (1 - q) (1 - s)))"

  {
    fix s :: complex assume "1 - s \<in> \<int>\<^sub>\<le>\<^sub>0"
    then obtain n where "1 - s = of_int n" "n \<le> 0" by (auto elim!: nonpos_Ints_cases)
    hence "s = 1 - of_int n" by (simp add: algebra_simps)
    also have "\<dots> \<in> \<nat>" using \<open>n \<le> 0\<close> by (auto simp: Nats_altdef1 intro: exI[of _ "1 - n"])
    finally have "s \<in> \<nat>" .
  } note * = this
  hence "f holomorphic_on -\<nat>" using q
    by (auto simp: f_def Nats_altdef2 nonpos_Ints_altdef not_le intro!: holomorphic_intros)
  also have "?this \<longleftrightarrow> perzeta q holomorphic_on -\<nat>" using assms
    by (intro holomorphic_cong refl) (auto simp: perzeta_def Let_def f_def)
  finally have holo: "perzeta q holomorphic_on -\<nat>" .

  have f_altdef: "f s = eval_fds (fds_perzeta q) s" if "Re s > 0" and "s \<notin> \<nat>" for s
    using perzeta_conv_hurwitz_zeta_aux[OF q, of s] that *
    by (auto simp: rGamma_inverse_Gamma Gamma_eq_zero_iff divide_simps f_def perzeta_def
             split: if_splits)
  show "perzeta q' s = eval_fds (fds_perzeta q') s" if "Re s > 0" for s
    using f_altdef[of s] that assms by (auto simp: f_def perzeta_def Let_def q_def)

  have cont: "isCont (perzeta q) s" if "s \<in> \<nat>" for s
  proof (cases "s = 0")
    case False
    with that obtain n where [simp]: "s = of_nat n" and n: "n > 0"
      by (auto elim!: Nats_cases)
    have *: "open ({s. Re s > 0} - (\<nat> - {of_nat n}))" using Nats_subset_Ints
      by (intro open_Diff closed_subset_Ints open_halfspace_Re_gt) auto
    have "eventually (\<lambda>s. s \<in> {s. Re s > 0} - (\<nat> - {of_nat n})) (nhds (of_nat n))" using \<open>n > 0\<close>
      by (intro eventually_nhds_in_open *) auto 
    hence ev: "eventually (\<lambda>s. eval_fds (fds_perzeta q) s = perzeta q s) (nhds (of_nat n))"
    proof eventually_elim
      case (elim s)
      thus ?case using q f_altdef[of s]
        by (auto simp: perzeta_def dist_of_nat f_def elim!: Nats_cases Ints_cases)
    qed
    have "isCont (eval_fds (fds_perzeta q)) (of_nat n)" using q and \<open>n > 0\<close>
      by (intro continuous_eval_fds le_less_trans[OF conv_abscissa_perzeta'])
         (auto elim!: Ints_cases)
    also have "?this \<longleftrightarrow> isCont (perzeta q) (of_nat n)" using ev
      by (intro isCont_cong ev)
    finally show ?thesis by simp
  next
    assume [simp]: "s = 0"
    define a where "a = Complex (ln q) (-pi / 2)"
    define b where "b = Complex (ln (1 - q)) (pi / 2)"
    have "eventually (\<lambda>s::complex. s \<notin> \<nat>) (at 0)"
      unfolding eventually_at_topological using Nats_subset_Ints
      by (intro exI[of _ "-(\<nat>-{0})"] conjI open_Compl closed_subset_Ints) auto
    hence ev: "eventually (\<lambda>s. perzeta q s = (2 * pi) powr (s - 1) * Gamma (1 - s) * \<i> *
                 (\<i> powr - s * pre_zeta q (1 - s) -\<i> powr s * pre_zeta (1 - q) (1 - s) +
                 (exp (b * s) - exp (a * s)) / s)) (at (0::complex))"
      (is "eventually (\<lambda>s. _ = ?f s) _")
    proof eventually_elim
      case (elim s)
      have "perzeta q s = (2 * pi) powr (s - 1) * Gamma (1 - s) * \<i> *
              (\<i> powr (-s) * hurwitz_zeta q (1 - s) -
               \<i> powr s * hurwitz_zeta (1 - q) (1 - s))" (is "_ = _ * ?T")
        using elim by (auto simp: perzeta_def powr_diff powr_minus field_simps)
      also have "?T = \<i> powr (-s) * pre_zeta q (1 - s) - \<i> powr s * pre_zeta (1 - q) (1 - s) +
                      (\<i> powr s * (1 - q) powr s - \<i> powr (-s) * q powr s) / s" using elim
        by (auto simp: hurwitz_zeta_def field_simps)
      also have "\<i> powr s * (1 - q) powr s = exp (b * s)" using q
        by (simp add: powr_def exp_add algebra_simps Ln_Reals_eq Complex_eq b_def)
      also have "\<i> powr (-s) * q powr s = exp (a * s)" using q
        by (simp add: powr_def exp_add Ln_Reals_eq exp_diff exp_minus diff_divide_distrib 
                      ring_distribs inverse_eq_divide mult_ac Complex_eq a_def)
      finally show ?case .
    qed
  
    have [simp]: "\<not>(pi \<le> 0)" using pi_gt_zero by (simp add: not_le)
    have "(\<lambda>s::complex. if s = 0 then b - a else (exp (b * s) - exp (a * s)) / s)
                has_fps_expansion (fps_exp b - fps_exp a) / fps_X" (is "?f' has_fps_expansion _")
      by (rule fps_expansion_intros)+ (auto intro!: subdegree_geI simp: Ln_Reals_eq a_def b_def)
    hence "isCont ?f' 0" by (rule has_fps_expansion_imp_continuous)
    hence "?f' \<midarrow>0\<rightarrow> b - a" by (simp add: isCont_def)
    also have "?this \<longleftrightarrow> (\<lambda>s. (exp (b * s) - exp (a * s)) / s) \<midarrow>0\<rightarrow> b - a"
      by (intro filterlim_cong refl) (auto simp: eventually_at intro: exI[of _ 1])
    finally have "?f \<midarrow>0\<rightarrow> of_real (2 * pi) powr (0 - 1) * Gamma (1 - 0) * \<i> *
                    (\<i> powr -0 * pre_zeta q (1 - 0) -\<i> powr 0 * pre_zeta (1 - q) (1 - 0) + (b - a))"
      (is "filterlim _ (nhds ?c) _")
      using q by (intro tendsto_intros isContD)
                 (auto simp: complex_nonpos_Reals_iff intro!: continuous_intros)
    also have "?c = perzeta q 0" using q
      by (simp add: powr_minus perzeta_def Ln_Reals_eq a_def b_def
                    Complex_eq mult_ac inverse_eq_divide)
    also have "?f \<midarrow>0\<rightarrow> \<dots> \<longleftrightarrow> perzeta q \<midarrow>0\<rightarrow> \<dots>"
      by (rule sym, intro filterlim_cong refl ev)
    finally show "isCont (perzeta q) s" by (simp add: isCont_def)
  qed

  have "perzeta q field_differentiable at s" for s
  proof (cases "s \<in> \<nat>")
    case False
    with holo have "perzeta q field_differentiable at s within -\<nat>" 
      unfolding holomorphic_on_def by blast
    also have "at s within -\<nat> = at s" using False
      by (intro at_within_open) auto
    finally show ?thesis .
  next
    case True
    hence *: "perzeta q holomorphic_on (ball s 1 - {s})"
      by (intro holomorphic_on_subset[OF holo]) (auto elim!: Nats_cases simp: dist_of_nat)
    have "perzeta q holomorphic_on ball s 1" using cont True
      by (intro no_isolated_singularity'[OF _ *])
         (auto simp: at_within_open[of _ "ball s 1"] isCont_def)
    hence "perzeta q field_differentiable at s within ball s 1" 
      unfolding holomorphic_on_def by auto
    thus ?thesis by (simp add: at_within_open[of _ "ball s 1"])
  qed
  hence "perzeta q holomorphic_on UNIV"
    by (auto simp: holomorphic_on_def)
  also have "perzeta q = perzeta q'" by (simp add: q_def)
  finally show "perzeta q' holomorphic_on A" by auto
qed

lemma perzeta_altdef1: "Re s > 1 \<Longrightarrow> perzeta q' s = eval_fds (fds_perzeta q') s"
  by (cases "q' \<in> \<int>") (auto simp: perzeta_int eval_fds_zeta fds_perzeta_int perzeta_altdef2)

lemma holomorphic_perzeta: "q \<notin> \<int> \<or> 1 \<notin> A \<Longrightarrow> perzeta q holomorphic_on A"
  by (cases "q \<in> \<int>") (auto simp: perzeta_int intro: holomorphic_perzeta' holomorphic_zeta)

lemma holomorphic_perzeta'' [holomorphic_intros]:
  assumes "f holomorphic_on A" and "q \<notin> \<int> \<or> (\<forall>x\<in>A. f x \<noteq> 1)"
  shows   "(\<lambda>x. perzeta q (f x)) holomorphic_on A"
proof -
  have "perzeta q \<circ> f holomorphic_on A" using assms 
    by (intro holomorphic_on_compose holomorphic_perzeta) auto
  thus ?thesis by (simp add: o_def)
qed

text \<open>
  Using this analytic continuation of the periodic zeta function, Hurwitz's formula now
  holds (almost) on the entire complex plane.
\<close>
theorem hurwitz_zeta_formula:
  fixes a :: real and s :: complex
  assumes "a \<in> {0<..1}" and "s \<noteq> 0" and "a \<noteq> 1 \<or> s \<noteq> 1"
  shows   "rGamma s * hurwitz_zeta a (1 - s) =
             (2 * pi) powr - s * (\<i> powr - s * perzeta a s + \<i> powr s * perzeta (-a) s)"
  (is "?f s = ?g s")
proof -
  define A where "A = UNIV - (if a \<in> \<int> then {0, 1} else {0 :: complex})"
  show ?thesis
  proof (rule analytic_continuation_open[where f = ?f])
    show "?f holomorphic_on A" using assms by (auto intro!: holomorphic_intros simp: A_def)
    show "?g holomorphic_on A" using assms
      by (auto intro!: holomorphic_intros simp: A_def minus_in_Ints_iff)
  next
    fix s assume "s \<in> {s. Re s > 1}"
    thus "?f s = ?g s" using hurwitz_zeta_formula_aux[of a s] assms
      by (simp add: perzeta_altdef1)
  qed (insert assms, auto simp: open_halfspace_Re_gt A_def elim!: Ints_cases
                           intro: connected_open_delete_finite exI[of _ 2])
qed

text \<open>
  The equation expressing the periodic zeta function in terms of the Hurwitz zeta function
  can be extened similarly.
\<close>
theorem perzeta_conv_hurwitz_zeta:
  fixes a :: real and s :: complex
  assumes "a \<in> {0<..<1}" and "s \<noteq> 0"
  shows   "rGamma (1 - s) * perzeta a s =
             (2 * pi) powr (s - 1) * \<i> * (\<i> powr (-s) * hurwitz_zeta a (1 - s) -
                                         \<i> powr s * hurwitz_zeta (1 - a) (1 - s))"
  (is "?f s = ?g s")
proof (rule analytic_continuation_open[where f = ?f])
  show "?f holomorphic_on -{0}" using assms by (auto intro!: holomorphic_intros elim: Ints_cases)
  show "?g holomorphic_on -{0}" using assms by (auto intro!: holomorphic_intros)
next
  fix s assume "s \<in> {s. Re s > 1}"
  thus "?f s = ?g s" using perzeta_conv_hurwitz_zeta_aux[of a s] assms
    by (simp add: perzeta_altdef1)
qed (insert assms, auto simp: open_halfspace_Re_gt connected_punctured_universe intro: exI[of _ 2])


text \<open>
  As a simple corollary, we derive the reflection formula for the Riemann zeta function:
\<close>
corollary zeta_reflect:
  fixes s :: complex
  assumes "s \<noteq> 0" "s \<noteq> 1"
  shows   "rGamma s * zeta (1 - s) = 2 * (2 * pi) powr -s * cos (s * pi / 2) * zeta s"
  using hurwitz_zeta_formula[of 1 s] assms
  by (simp add: zeta_def cos_exp_eq powr_def perzeta_int algebra_simps)

corollary zeta_reflect':
  fixes s :: complex
  assumes "s \<noteq> 0" "s \<noteq> 1"
  shows   "rGamma (1 - s) * zeta s = 2 * (2 * pi) powr (s - 1) * sin (s * pi / 2) * zeta (1 - s)"
  using zeta_reflect[of "1 - s"] assms by (simp add: cos_sin_eq field_simps)

text \<open>
  It is now easy to see that all the non-trivial zeroes of the Riemann zeta function must lie
  the critical strip $(0;1)$, and they must be symmetric around the
  $\mathfrak{R}(z) = \frac{1}{2}$ line.
\<close>
corollary zeta_zeroD:
  assumes "zeta s = 0" "s \<noteq> 1"
  shows   "Re s \<in> {0<..<1} \<or> (\<exists>n::nat. n > 0 \<and> even n \<and> s = -real n)"
proof (cases "Re s \<le> 0")
  case False
  with zeta_Re_ge_1_nonzero[of s] assms have "Re s < 1"
    by (cases "Re s < 1") auto
  with False show ?thesis by simp
next
  case True
  {
    assume *: "\<And>n. n > 0 \<Longrightarrow> even n \<Longrightarrow> s \<noteq> -real n"
    have "s \<noteq> of_int n" for n :: int
    proof
      assume [simp]: "s = of_int n"
      show False
      proof (cases n "0::int" rule: linorder_cases)
        assume "n < 0"
        show False
        proof (cases "even n")
          case True
          hence "nat (-n) > 0" "even (nat (-n))" using \<open>n < 0\<close>
            by (auto simp: even_nat_iff)
          with * have "s \<noteq> -real (nat (-n))" .
          with \<open>n < 0\<close> and True show False by auto
        next
          case False
          with \<open>n < 0\<close> have "of_int n = (-of_nat (nat (-n)) :: complex)" by simp
          also have "zeta \<dots> = -(bernoulli' (Suc (nat (-n)))) / of_nat (Suc (nat (-n)))"
            using \<open>n < 0\<close> by (subst zeta_neg_of_nat) (auto)
          finally have "bernoulli' (Suc (nat (-n))) = 0" using assms
            by (auto simp del: of_nat_Suc)
          with False and \<open>n < 0\<close> show False
            by (auto simp: bernoulli'_zero_iff even_nat_iff)
        qed
      qed (insert assms True, auto)
    qed
    hence "rGamma s \<noteq> 0"
      by (auto simp: rGamma_eq_zero_iff nonpos_Ints_def)
    moreover from assms have [simp]: "s \<noteq> 0" by auto
    ultimately have "zeta (1 - s) = 0" using zeta_reflect[of s] and assms
      by auto
    with True zeta_Re_ge_1_nonzero[of "1 - s"] have "Re s > 0" by auto
  }
  with True show ?thesis by auto
qed

lemma zeta_zero_reflect:
  assumes "Re s \<in> {0<..<1}" and "zeta s = 0"
  shows   "zeta (1 - s) = 0"
proof -
  from assms have "rGamma s \<noteq> 0"
    by (auto simp: rGamma_eq_zero_iff elim!: nonpos_Ints_cases)
  moreover from assms have "s \<noteq> 0" and "s \<noteq> 1" by auto
  ultimately show ?thesis using zeta_reflect[of s] and assms by auto
qed

corollary zeta_zero_reflect_iff:
  assumes "Re s \<in> {0<..<1}"
  shows   "zeta (1 - s) = 0 \<longleftrightarrow> zeta s = 0"
  using zeta_zero_reflect[of s] zeta_zero_reflect[of "1 - s"] assms by auto


subsection \<open>More functional equations\<close>

lemma perzeta_conv_hurwitz_zeta_multiplication:
  fixes k :: nat and a :: int and s :: complex
  assumes "k > 0" "s \<noteq> 1"
  shows   "k powr s * perzeta (a / k) s =
             (\<Sum>n=1..k. exp (2 * pi * n * a / k * \<i>) * hurwitz_zeta (n / k) s)"
  (is "?lhs s = ?rhs s")
proof (rule analytic_continuation_open[where ?f = ?lhs and ?g = ?rhs])
  show "connected (-{1::complex})" by (rule connected_punctured_universe) auto
  show "{s. Re s > 1} \<noteq> {}" by (auto intro!: exI[of _ 2])
next
  fix s assume s: "s \<in> {s. Re s > 1}"
  let ?f = "\<lambda>n. exp (2 * pi * n * a / k * \<i>)"

  show "?lhs s = ?rhs s"
  proof (rule sums_unique2)
    have "(\<lambda>m. \<Sum>n=1..k. ?f n * (of_nat m + of_real (real n / real k)) powr -s) sums
            (\<Sum>n=1..k. ?f n * hurwitz_zeta (real n / real k) s)"
      using assms s by (intro sums_sum sums_mult sums_hurwitz_zeta) auto
    also have "(\<lambda>m. \<Sum>n=1..k. ?f n * (of_nat m + of_real (real n / real k)) powr -s) =
                 (\<lambda>m. of_nat k powr s * (\<Sum>n=1..k. ?f n * of_nat (m * k + n) powr -s))"
      unfolding sum_distrib_left
    proof (intro ext sum.cong, goal_cases)
      case (2 m n)
      hence "m * k + n > 0" by (intro add_nonneg_pos) auto
      hence "of_nat 0 \<noteq> (of_nat (m * k + n) :: complex)" by (simp only: of_nat_eq_iff)
      also have "of_nat (m * k + n) = of_nat m * of_nat k + (of_nat n :: complex)" by simp
      finally have nz: "\<dots> \<noteq> 0" by auto
      
      have "of_nat m + of_real (real n / real k) = 
              (inverse (of_nat k) * of_nat (m * k + n) :: complex)" using assms
        (* TODO: Field_as_Ring messing up things again *)
        by (simp add: field_simps del: div_mult_self1 div_mult_self2 div_mult_self3 div_mult_self4)
      also from nz have "\<dots> powr -s = of_nat k powr s * of_nat (m * k + n) powr -s"
        by (subst powr_times_real) (auto simp: add_eq_0_iff powr_def exp_minus Ln_inverse)
      finally show ?case by simp
    qed auto
    finally show "\<dots> sums (\<Sum>n=1..k. ?f n * hurwitz_zeta (real n / real k) s)" .
  next
    define g where "g = (\<lambda>m. exp (2 * pi * \<i> * m * (real_of_int a / real k)))"
    have "(\<lambda>m. g (Suc m) / (Suc m) powr s) sums eval_fds (fds_perzeta (a / k)) s"
      unfolding g_def using s by (intro sums_fds_perzeta) auto
    also have "(\<lambda>m. g (Suc m) / (Suc m) powr s) = (\<lambda>m. ?f (Suc m) * (Suc m) powr -s)"
      by (simp add: powr_minus field_simps g_def)
    also have "eval_fds (fds_perzeta (a / k)) s = perzeta (a / k) s"
      using s by (simp add: perzeta_altdef1)
    finally have "(\<lambda>m. \<Sum>n=m*k..<m*k+k. ?f (Suc n) * of_nat (Suc n) powr -s) sums perzeta (a / k) s"
      using \<open>k > 0\<close> by (rule sums_group)
    also have "(\<lambda>m. \<Sum>n=m*k..<m*k+k. ?f (Suc n) * of_nat (Suc n) powr -s) = 
                 (\<lambda>m. \<Sum>n=1..k. ?f (m * k + n) * of_nat (m * k + n) powr -s)"
    proof (rule ext, goal_cases)
      case (1 m)
      show ?case using assms
        by (intro ext sum.reindex_bij_witness[of _ "\<lambda>n. m * k + n - 1" "\<lambda>n. Suc n - m * k"]) auto
    qed
    also have "(\<lambda>m n. ?f (m * k + n)) = (\<lambda>m n. ?f n)"
    proof (intro ext)
      fix m n :: nat
      have "?f (m * k + n) / ?f n = exp (2 * pi * m * a * \<i>)"
        using \<open>k > 0\<close> by (auto simp: ring_distribs add_divide_distrib exp_add mult_ac)
      also have "\<dots> = cis (2 * pi * (m * a))"
        by (simp add: exp_eq_polar mult_ac)
      also have "\<dots> = 1"
        by (rule cis_multiple_2pi) auto
      finally show "?f (m * k + n) = ?f n"
        by simp
    qed
    finally show "(\<lambda>m. of_nat k powr s * (\<Sum>n=1..k. ?f n * of_nat (m * k + n) powr -s)) sums
                    (of_nat k powr s * perzeta (a / k) s)" by (rule sums_mult)
  qed
qed (use assms in \<open>auto intro!: holomorphic_intros simp: finite_imp_closed open_halfspace_Re_gt\<close>)

lemma perzeta_conv_hurwitz_zeta_multiplication':
  fixes k :: nat and a :: int and s :: complex
  assumes "k > 0" "s \<noteq> 1"
  shows   "perzeta (a / k) s = k powr -s *
             (\<Sum>n=1..k. exp (2 * pi * n * a / k * \<i>) * hurwitz_zeta (n / k) s)"
  using perzeta_conv_hurwitz_zeta_multiplication[of k s a] assms
  by (simp add: powr_minus field_simps)

lemma zeta_conv_hurwitz_zeta_multiplication:
  fixes k a :: nat and s :: complex
  assumes "k > 0" "s \<noteq> 1"
  shows   "k powr s * zeta s = (\<Sum>n=1..k. hurwitz_zeta (n / k) s)"
  using perzeta_conv_hurwitz_zeta_multiplication[of k s 0]
  using assms by (simp add: perzeta_int)

lemma hurwitz_zeta_one_half_left:
  assumes "s \<noteq> 1"
  shows   "hurwitz_zeta (1 / 2) s = (2 powr s - 1) * zeta s"
  using zeta_conv_hurwitz_zeta_multiplication[of 2 s] assms
  by (simp add: eval_nat_numeral zeta_def field_simps)

theorem hurwitz_zeta_functional_equation:
  fixes h k :: nat and s :: complex
  assumes hk: "k > 0" "h \<in> {0<..k}" and s: "s \<notin> {0, 1}"
  defines "a \<equiv> real h / real k"
  shows "rGamma s * hurwitz_zeta a (1 - s) =
           2 * (2 * pi * k) powr -s *
             (\<Sum>n=1..k. cos (s*pi/2 - 2*pi*n*h/k) * hurwitz_zeta (n / k) s)"
proof -
  from hk have a: "a \<in> {0<..1}" by (auto simp: a_def)

  have "rGamma s * hurwitz_zeta a (1 - s) =
          (2 * pi) powr - s * (\<i> powr - s * perzeta a s + \<i> powr s * perzeta (- a) s)"
    using s a by (intro hurwitz_zeta_formula) auto
  also have "\<dots> = (2 * pi) powr - s * (\<i> powr - s * perzeta (of_int (int h) / k) s +
                                       \<i> powr s * perzeta (of_int (-int h) / k) s)"
    by (simp add: a_def)
  also have "\<dots> = (2 * pi) powr -s * k powr -s *
     ((\<Sum>n=1..k. \<i> powr -s * cis (2 * pi * n * h / k) * hurwitz_zeta (n / k) s) +
       (\<Sum>n=1..k. \<i> powr s  * cis (-2 * pi * n * h / k) * hurwitz_zeta (n / k) s))"
    (is "_ = _ * (?S1 + ?S2)") using hk a s
    by (subst (1 2) perzeta_conv_hurwitz_zeta_multiplication')
       (auto simp: field_simps sum_distrib_left sum_distrib_right exp_eq_polar)
  also have "(2 * pi) powr -s * k powr -s = (2 * k * pi) powr -s"
    using hk pi_gt_zero
    by (simp add: powr_def Ln_times_Reals field_simps exp_add exp_diff exp_minus)
  also have "?S1 + ?S2 = (\<Sum>n=1..k. (\<i> powr -s * cis (2*pi*n*h/k) + \<i> powr s * cis (-2*pi*n*h/k)) *
                                    hurwitz_zeta (n / k) s)"
    (is "_ = (\<Sum>n\<in>_. ?c n * _)") by (simp add: algebra_simps sum.distrib)
  also have "?c = (\<lambda>n. 2 * cos (s*pi/2 - 2*pi*n*h/k))"
  proof
    fix n :: nat
    have "\<i> powr -s * cis (2*pi*n*h/k) = exp (-s*pi/2*\<i> + 2*pi*n*h/k*\<i>)"
      unfolding exp_add by (simp add: powr_def cis_conv_exp mult_ac)
    moreover have "\<i> powr s * cis (-2*pi*n*h/k) = exp (s*pi/2*\<i> + -2*pi*n*h/k*\<i>)"
      unfolding exp_add by (simp add: powr_def cis_conv_exp mult_ac)
    ultimately have "?c n = exp (\<i> * (s*pi/2 - 2*pi*n*h/k)) + exp (-(\<i> * (s*pi/2 - 2*pi*n*h/k)))"
      by (simp add: mult_ac ring_distribs)
    also have "\<dots> / 2 = cos (s*pi/2 - 2*pi*n*h/k)"
      by (rule cos_exp_eq [symmetric])
    finally show "?c n = 2 * cos (s*pi/2 - 2*pi*n*h/k)" 
      by simp
  qed
  also have "(2 * k * pi) powr -s * (\<Sum>n=1..k. \<dots> n * hurwitz_zeta (n / k) s) =
               2 * (2 * pi * k) powr -s *
               (\<Sum>n=1..k. cos (s*pi/2 - 2*pi*n*h/k) * hurwitz_zeta (n / k) s)"
    by (simp add: sum_distrib_left sum_distrib_right mult_ac)
  finally show ?thesis .
qed

lemma perzeta_one_half_left: "s \<noteq> 1 \<Longrightarrow> perzeta (1 / 2) s = (2 powr (1-s) - 1) * zeta s"
  using perzeta_conv_hurwitz_zeta_multiplication'[of 2 s 1]
  by (simp add: eval_nat_numeral hurwitz_zeta_one_half_left powr_minus
                field_simps zeta_def powr_diff)

lemma perzeta_one_half_left':
  "perzeta (1 / 2) s =
         (if s = 1 then -ln 2 else (2 powr (1 - s) - 1) / (s - 1)) * ((s - 1) * pre_zeta 1 s + 1)"
  by (cases "s = 1") (auto simp: perzeta_one_half_left field_simps zeta_def hurwitz_zeta_def)
  
end
