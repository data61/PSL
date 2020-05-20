section \<open>The Hadjicostas--Chapman formula\<close>
theory Hadjicostas_Chapman
  imports Zeta_Laurent_Expansion
begin

text \<open>
  In this section, we will derive a formula for the \<open>\<zeta>\<close> function that was conjectured by 
  Hadjicostas~\cite{hadjicostas2004} and proven shortly afterwards by Chapman~\cite{chapman2004}.
  The formula is:
    \begin{align*}
    &\int_0^1 \int_0^1 \frac{(-\ln (xy))^z (1-x)}{1-xy}\ \text{d}x\,\text{d}y\\
      &\quad = \int_0^1 \frac{(-\ln u)^z(-\ln u + u - 1)}{1-u}\ \text{d}u\\
      &\quad = \Gamma(z + 2) \left(\zeta(z + 2) - \frac{1}{z+1}\right)
    \end{align*}
  for any \<open>z\<close> with $\mathfrak{R}(z) > -2$. In particular, setting $z = 1$, we can derive
  the following formula for the Euler--Mascheroni constant \<open>\<gamma>\<close>:
    \[-\int_0^1 \int_0^1 \frac{1-x}{(1-xy) \ln (xy)}\ \text{d}x\,\text{d}y = \gamma\]
  This formula was first proven by Sondow~\cite{sondow2002}.      
\<close>

subsection \<open>The real case\<close>

text \<open>
  We first define the integral for real \<open>z > -2\<close>. This is then a non-negative integral,
  so that we can ignore the issue of integrability and use the Lebesgue integral on the
  extended non-negative reals

  We first show the equivalence of the single-integral and the double-integral form.
\<close>

definition Hadjicostas_nn_integral :: "real \<Rightarrow> ennreal" where
  "Hadjicostas_nn_integral z =
     set_nn_integral lborel {0<..<1}
       (\<lambda>u. ennreal ((-ln u) powr z / (1 - u) * (-ln u + u - 1)))"

definition Hadjicostas_integral :: "complex \<Rightarrow> complex" where
  "Hadjicostas_integral z =
     (LBINT u=0..1. of_real (-ln u) powr z / of_real (1 - u) * of_real (-ln u + u - 1))"

lemma Hadjicostas_nn_integral_altdef:
  "Hadjicostas_nn_integral z =
     (\<integral>\<^sup>+(x,y)\<in>{0<..<1}\<times>{0<..<1}. ((-ln (x*y)) powr z * (1-x) / (1-x*y)) \<partial>lborel)"
proof -
  define f where "f \<equiv> (\<lambda>u. ((-ln u) powr z / (1 - u) * (-ln u + u - 1)))"
  let ?I = "Gamma (z + 2) * (Re (zeta (z + 2)) - 1 / (z + 1))"
  let ?f = "\<lambda>u. ((-ln u) powr z / (1 - u) * (-ln u + u - 1))"
  define D :: "(real \<times> real) set" where "D = {0<..<1} \<times> {0<..<1}"
  define D1 where "D1 = (SIGMA x:{0<..<1}. {0<..<(x::real)})"
  define D2 where "D2 = (SIGMA u:{0<..<1}. {u<..<(1::real)})"
  have [measurable]: "D1 \<in> sets (lborel \<Otimes>\<^sub>M lborel)"
  proof -
    have "D1 = {x\<in>space (lborel \<Otimes>\<^sub>M lborel). snd x > 0 \<and> fst x > snd x \<and> fst x < 1}"
      by (auto simp: D1_def space_pair_measure)
    also have "\<dots> \<in> sets (lborel \<Otimes>\<^sub>M lborel)"
      by measurable
    finally show ?thesis .
  qed
  have [measurable]: "D2 \<in> sets (lborel \<Otimes>\<^sub>M lborel)"
  proof -
    have "D2 = {x\<in>space (lborel \<Otimes>\<^sub>M lborel). fst x > 0 \<and> fst x < snd x \<and> snd x < 1}"
      by (auto simp: D2_def space_pair_measure)
    also have "\<dots> \<in> sets (lborel \<Otimes>\<^sub>M lborel)"
      by measurable
    finally show ?thesis .
  qed

  have "(\<integral>\<^sup>+(x,y)\<in>D. ((-ln (x*y)) powr z * (1-x) / (1-x*y)) \<partial>lborel) =
          (\<integral>\<^sup>+x\<in>{0<..<1}. (\<integral>\<^sup>+y\<in>{0<..<1}. ((-ln (x*y)) powr z / (1-x*y) * (1-x)) \<partial>lborel) \<partial>lborel)"
    unfolding lborel_prod [symmetric] case_prod_unfold D_def
    by (subst lborel.nn_integral_fst[symmetric])
       (auto intro!: nn_integral_cong simp: indicator_def)
  also have "\<dots> = (\<integral>\<^sup>+x\<in>{0<..<1}. (\<integral>\<^sup>+u\<in>{0<..<x}. ((- ln u) powr z / (1 - u) * (1 - x) / x) \<partial>lborel) \<partial>lborel)"
  proof (rule set_nn_integral_cong)
    fix x :: real assume x: "x \<in> space lborel \<inter> {0<..<1}"
    show "(\<integral>\<^sup>+y\<in>{0<..<1}. ((-ln (x*y)) powr z / (1-x*y) * (1-x)) \<partial>lborel) =
            (\<integral>\<^sup>+u\<in>{0<..<x}. ((- ln u) powr z / (1 - u) * (1 - x) / x) \<partial>lborel)" using x
      by (subst lborel_distr_mult'[of "1/x"])
         (auto simp: nn_integral_density nn_integral_distr indicator_def field_simps
               simp flip: ennreal_mult' intro!: nn_integral_cong)
  qed auto
  also have "\<dots> = (\<integral>\<^sup>+(x,u)\<in>D1. ((- ln u) powr z / (1 - u) * (1 - x) / x) \<partial>lborel)"
    unfolding lborel_prod [symmetric] case_prod_unfold D_def
    by (subst lborel.nn_integral_fst[symmetric], measurable)
       (auto intro!: nn_integral_cong simp: indicator_def D1_def)
  also have "\<dots> = (\<integral>\<^sup>+(x,u). indicator D2 (u,x) * ((- ln u) powr z / (1 - u) * (1 - x) / x) \<partial>lborel)"
    by (intro nn_integral_cong)  (auto simp: D1_def D2_def indicator_def split: if_splits)
  also have "\<dots> = (\<integral>\<^sup>+u\<in>{0<..<1}. (\<integral>\<^sup>+x\<in>{u<..<1}. ((- ln u) powr z / (1 - u) * (1 - x) / x) \<partial>lborel) \<partial>lborel)"
    unfolding case_prod_unfold lborel_prod [symmetric]
    by (subst lborel_pair.nn_integral_snd [symmetric], measurable)
       (auto intro!: nn_integral_cong simp: D2_def indicator_def)
  also have "\<dots> = (\<integral>\<^sup>+u\<in>{0<..<1}. ((-ln u) powr z / (1 - u) * (-ln u + u - 1)) \<partial>lborel)"
  proof (intro set_nn_integral_cong refl)
    fix u :: real assume u: "u \<in> space lborel \<inter> {0<..<1}"
    let ?F = "\<lambda>x. (- ln u) powr z / (1 - u) * (ln x - x)"
    have "(\<integral>\<^sup>+x\<in>{u<..<1}. ennreal ((- ln u) powr z / (1 - u) * (1 - x) / x) \<partial>lborel) =
            (\<integral>\<^sup>+x\<in>{u..1}. ennreal ((- ln u) powr z / (1 - u) * (1 - x) / x) \<partial>lborel)"
      by (rule nn_integral_cong_AE, rule AE_I[of _ _ "{u,1}"])
         (auto simp: emeasure_lborel_countable indicator_def)
    also have "\<dots> = ennreal (?F 1 - ?F u)"
      using u by (intro nn_integral_FTC_Icc) (auto intro!: derivative_eq_intros simp: divide_simps)
    also have "?F 1 - ?F u = (-ln u) powr z / (1 - u) * (-ln u + u - 1)"
      using u by (simp add: divide_simps) (simp add: algebra_simps)?
    finally show "(\<integral>\<^sup>+x\<in>{u<..<1}. ((- ln u) powr z / (1 - u) * (1 - x) / x) \<partial>lborel) = ennreal \<dots>" .
  qed
  also have "\<dots> = Hadjicostas_nn_integral z"
    by (simp add: Hadjicostas_nn_integral_def)
  finally show ?thesis by (simp add: D_def)
qed

text \<open>
  We now solve the single integral for real \<open>z > -1\<close>.
\<close>
lemma Hadjicostas_Chapman_aux:
  fixes z :: real
  assumes z: "z > -1"
  defines "f \<equiv> (\<lambda>u. ((-ln u) powr z / (1 - u) * (-ln u + u - 1)))"
  shows   "(f has_integral (Gamma (z + 2) * (Re (zeta (z + 2)) - 1 / (z + 1)))) {0<..<1}"
proof -
  let ?I = "Gamma (z + 2) * (Re (zeta (z + 2)) - 1 / (z + 1))"
  have nonneg: "1 \<le> x + exp (- x)" if "x \<ge> 0" for x :: real
  proof -
    have "x + (1 + (-x)) \<le> x + exp (-x)"
      by (intro add_left_mono exp_ge_add_one_self)
    thus ?thesis by simp
  qed

  have eq: "((\<lambda>t::real. exp (-t)) ` {0<..}) = {0<..<1}"
  proof safe
    fix x :: real assume x: "x \<in> {0<..<1}"
    hence "x = exp (-(-ln x))" and "-ln x \<in> {0<..}"
      by auto
    thus "x \<in> (\<lambda>t. exp (-t)) ` {0<..}" by blast
  qed auto
    
  have I: "((\<lambda>x. x powr (z+1) / (exp x - 1) - x powr z / exp x) has_integral ?I) {0<..}"
  proof -
    from z have "z + 1 \<notin> \<real>\<^sub>\<le>\<^sub>0"
      by (auto simp: nonpos_Reals_def)
    hence z': "z + 1 \<notin> \<int>\<^sub>\<le>\<^sub>0" 
      using nonpos_Ints_subset_nonpos_Reals by blast
    have "((\<lambda>x. x powr (z + 2 - 1) / (exp x - 1) - x powr (z + 1 - 1) / exp x)
            has_integral (Gamma (z + 2) * Re (zeta (z + 2)) - Gamma (z + 1))) {0<..}" using z
      by (intro has_integral_diff Gamma_integral_real' Gamma_times_zeta_has_integral_real) auto
    also have "Gamma (z + 2) * Re (zeta (z + 2)) - Gamma (z + 1) =
                 Gamma (z + 2) * (Re (zeta (z + 2)) - 1 / (z + 1))"
      using Gamma_plus1[of "z+1"] z z' by (auto simp: field_simps)
    finally show ?thesis
      by (simp add: add_ac)
  qed
  also have "?this \<longleftrightarrow> ((\<lambda>x. \<bar>-exp (-x)\<bar> * f (exp (-x))) has_integral ?I) {0<..}"
    unfolding f_def
    apply (intro has_integral_cong)
    apply (auto simp: field_simps powr_add powr_def exp_add)
    apply (simp flip: exp_add)
    done
  finally have *: "((\<lambda>x. \<bar>-exp (-x)\<bar> * f (exp (-x))) has_integral ?I) {0<..}" .

  have "((\<lambda>x. \<bar>-exp (-x)\<bar> *\<^sub>R f (exp (-x))) absolutely_integrable_on {0<..}) \<and>
                  integral {0<..} (\<lambda>x. \<bar>-exp (-x)\<bar> *\<^sub>R f (exp (-x))) = ?I"
  proof (intro conjI nonnegative_absolutely_integrable_1)
    fix x :: real assume x: "x \<in> {0<..}"
    thus "\<bar>-exp (-x)\<bar> *\<^sub>R f (exp (-x)) \<ge> 0"
      unfolding f_def using nonneg
      by (intro scaleR_nonneg_nonneg mult_nonneg_nonneg divide_nonneg_nonneg) auto
  qed (use * in \<open>simp_all add: has_integral_iff\<close>)

  also have "?this \<longleftrightarrow> f absolutely_integrable_on (\<lambda>x. exp (- x)) ` {0<..} \<and>
                       integral ((\<lambda>x. exp (- x)) ` {0<..}) f = ?I"
    by (intro has_absolute_integral_change_of_variables_1')
       (auto intro!: derivative_eq_intros inj_onI)
  also have "(\<lambda>x::real. exp (- x)) ` {0<..} = {0<..<1}"
    by (fact eq)
  finally show "(f has_integral ?I) {0<..<1}"
    by (auto simp: has_integral_iff dest: set_lebesgue_integral_eq_integral)
qed

lemma real_zeta_ge_one_over_minus_one:
  fixes z :: real
  assumes z: "z > 1"
  shows "Re (zeta (complex_of_real z)) \<ge> 1 / (z - 1)"
proof -
  have ineq: "1 \<le> x - ln x" if "x \<in> {0<..<1}" for x :: real
    using ln_le_minus_one[of x] that by simp
  have *: "((\<lambda>u. (- ln u) powr (z - 2) * (u - ln u - 1) / (1 - u)) has_integral
           Gamma z * (Re (zeta (complex_of_real z)) - 1 / (z - 1))) {0<..<1}"
    using Hadjicostas_Chapman_aux[of "z - 2"] z by simp
  from ineq have "Gamma z * (Re (zeta (complex_of_real z)) - 1 / (z - 1)) \<ge> 0"
    by (intro has_integral_nonneg[OF *] z mult_nonneg_nonneg divide_nonneg_nonneg) auto
  moreover have "Gamma z > 0"
    using assms by (intro Gamma_real_pos) auto
  ultimately show "Re (zeta (complex_of_real z)) \<ge> 1 / (z - 1)"
    by (subst (asm) zero_le_mult_iff) auto
qed

text \<open>
  We now have the formula for real \<open>z > -1\<close>.
\<close>
lemma Hadjicostas_Chapman_formula_real:
  fixes z :: real
  assumes z: "z > -1"
  shows   "Hadjicostas_nn_integral z =
             ennreal (Gamma (z + 2) * (Re (zeta (z + 2)) - 1 / (z + 1)))"
proof -
  have nonneg: "1 \<le> x - ln x" if "x > 0" "x < 1" for x :: real
  proof -
    have "ln x + (1 + ln x) \<le> ln x + exp (ln x)"
      by (intro add_left_mono exp_ge_add_one_self)
    thus ?thesis using that by (simp add: exp_minus)
  qed
  show ?thesis
    unfolding Hadjicostas_nn_integral_def using nonneg Hadjicostas_Chapman_aux[OF z]
    by (intro nn_integral_has_integral_lebesgue' mult_nonneg_nonneg divide_nonneg_nonneg) auto
qed


subsection \<open>Analyticity of the integral\<close>

text \<open>
  To extend the formula to its full domain of validity (any complex \<open>z\<close> with
  $\mathfrak{R}(z)>-2$), we will use analytic continuation. To do this, we first
  have to show that the integral is an analytic function of \<open>z\<close> on that domain.
  This is unfortunately somewhat involved, since the integral is an improper one
  and we first need to show uniform convergence so that we can pull the derivative
  inside the integral sign.

  We will use the single-integral form so that we only have to deal with one integral
  and not two.
\<close>

context
  fixes f :: "complex \<Rightarrow> real \<Rightarrow> complex"
  defines "f \<equiv> (\<lambda>z u. of_real (-ln u) powr z / of_real (1 - u) * of_real (-ln u + u - 1))"
begin

context
  fixes x y :: real and g1 g2 :: "real \<Rightarrow> real"
  assumes "x > -2"
  defines "g1 \<equiv> (\<lambda>x. (- ln x) powr y * (x - ln x - 1) / (1 - x))"
  defines "g2 \<equiv> (\<lambda>u. (-ln u) powr x * (u - ln u - 1) / (1 - u))"
begin

lemma integrable_bound1:
  "interval_lebesgue_integrable lborel 0 (ereal (exp (- 1))) g1"
  unfolding zero_ereal_def
proof (rule interval_lebesgue_integrable_bigo_left)
  show "g1 \<in> O[at_right 0](\<lambda>u. u powr (-1/2))"
    unfolding g1_def by real_asymp
  show "continuous_on {0<..exp(-1)} g1"
    unfolding g1_def by (auto intro!: continuous_intros)
  have "set_integrable lborel (einterval 0 (exp (-1))) (\<lambda>u. u powr (-1/2))"
  proof (rule interval_integral_FTC_nonneg)
    fix u :: real assume u: "0 < ereal u" "ereal u < ereal (exp (-1))"
    show "((\<lambda>u. 2 * u powr (1/2)) has_field_derivative (u powr (-1/2))) (at u)"
      using u by (auto intro!: derivative_eq_intros simp: power2_eq_square)
    show "isCont (\<lambda>u. u powr (-1/2)) u"
      using u by (auto intro!: continuous_intros)
  next
    show "(((\<lambda>u. 2 * u powr (1/2)) \<circ> real_of_ereal) \<longlongrightarrow> 2 * exp (-1) powr (1/2))
            (at_left (ereal (exp (- 1))))"
      unfolding ereal_tendsto_simps by real_asymp
    show "(((\<lambda>u. 2 * u powr (1/2)) \<circ> real_of_ereal) \<longlongrightarrow> 0) (at_right 0)"
      unfolding zero_ereal_def unfolding ereal_tendsto_simps by real_asymp
  qed auto
  thus "interval_lebesgue_integrable lborel (ereal 0) (ereal (exp (- 1)))
          (\<lambda>u. u powr (-1/2))"
    by (simp add: interval_lebesgue_integrable_def zero_ereal_def)
qed (auto simp add: g1_def set_borel_measurable_def)

lemma integrable_bound2:
  "interval_lebesgue_integrable lborel (exp (-1)) 1 g2"
      unfolding one_ereal_def
proof (rule interval_lebesgue_integrable_bigo_right)
  show "g2 \<in> O[at_left 1](\<lambda>u. (1 - u) powr (x + 1))"
    unfolding g2_def by real_asymp
  have "ln x \<noteq> 0" if "x \<in> {exp (-1)..<1}" for x :: real
  proof -
    have "0 < exp (-1 :: real)" by simp
    also have "\<dots> \<le> x" using that by auto
    finally have "x > 0" .
    from that \<open>x > 0\<close> have "ln x < ln 1"
      by (subst ln_less_cancel_iff) auto
    thus "ln x \<noteq> 0" by simp
  qed
  thus "continuous_on {exp (- 1)..<1} g2"
    unfolding g2_def by (auto intro!: continuous_intros)
  let ?F = "(\<lambda>u. -1 / (x + 2) * (1 - u) powr (x + 2))"
  have "set_integrable lborel (einterval (exp (-1)) 1) (\<lambda>u. (1 - u) powr (x + 1))"
  proof (rule interval_integral_FTC_nonneg[where F = ?F])
    fix u :: real assume u: "ereal (exp (-1)) < ereal u" "ereal u < 1"
    show "(?F has_field_derivative (1 - u) powr (x + 1)) (at u)"
      using u \<open>x > -2\<close> by (auto intro!: derivative_eq_intros simp: one_ereal_def add_ac)
    show "isCont (\<lambda>u. (1 - u) powr (x + 1)) u"
      using u by (auto intro!: continuous_intros)
  next
    show "(((\<lambda>u. - 1 / (x + 2) * (1 - u) powr (x + 2)) \<circ> real_of_ereal) \<longlongrightarrow>
            - 1 / (x + 2) * (1 - exp (-1)) powr (x + 2)) (at_right (ereal (exp (- 1))))"
      unfolding ereal_tendsto_simps by real_asymp
    show "(((\<lambda>u. - 1 / (x + 2) * (1 - u) powr (x + 2)) \<circ> real_of_ereal) \<longlongrightarrow> 0) (at_left 1)"
      unfolding one_ereal_def unfolding ereal_tendsto_simps
      using \<open>x > -2\<close> by real_asymp
  qed auto
  thus "interval_lebesgue_integrable lborel (ereal (exp (- 1)))
          (ereal 1) (\<lambda>u. (1 - u) powr (x + 1))"
    by (simp add: interval_lebesgue_integrable_def one_ereal_def)
qed (auto simp add: g2_def set_borel_measurable_def)

lemma bound2:
  "norm (f z u) \<le> g2 u" if z: "Re z \<in> {x..y}" and u: "u \<in> {exp (-1)<..<1}" for z u
proof -
  have "0 < exp (-1::real)" by simp
  also have "\<dots> \<le> u" using u by (simp add: einterval_def)
  finally have "u > 0" .

  from u \<open>u > 0\<close> have ln_u: "ln u > ln (exp (-1))"
    by (subst ln_less_cancel_iff) (auto simp: einterval_def)
  from z u \<open>u > 0\<close> have "norm (f z u) = (- ln u) powr Re z * \<bar>u - ln u - 1\<bar> / (1 - u)"
    unfolding f_def norm_mult norm_divide norm_of_real
    by (simp add: norm_powr_real_powr einterval_def)
  also have "\<bar>u - ln u - 1\<bar> = u - ln u - 1"
    using u \<open>u > 0\<close> ln_add_one_self_le_self2[of "u - 1"] by (simp add: einterval_def)
  also have "(- ln u) powr Re z * (u - ln u - 1) / (1 - u) \<le>
               (- ln u) powr x * (u - ln u - 1) / (1 - u)"
    using z u \<open>u > 0\<close> ln_u ln_add_one_self_le_self2[of "u - 1"]
    by (intro mult_right_mono divide_right_mono powr_mono') (auto simp: einterval_def)
  finally show "norm (f z u) \<le> g2 u" by (simp add: g2_def)
qed

lemma integrable2_aux: "interval_lebesgue_integrable lborel (exp (-1)) 1 (f z)"
    if z: "Re z \<in> {x..y}" for z
proof -
  have "set_integrable lborel {exp (-1)<..<1} (f z)"
  proof (rule set_integrable_bound[OF _ _ AE_I2[OF impI]])
    fix u :: real assume "u \<in> {exp (-1)<..<1}"
    hence "norm (f z u) \<le> g2 u" using z by (intro bound2) auto
    also have "\<dots> \<le> norm (g2 u)" by simp
    finally show "norm (f z u) \<le> norm (g2 u)" .
  qed (use integrable_bound2 in \<open>simp_all add: interval_lebesgue_integrable_def
         one_ereal_def set_borel_measurable_def f_def\<close>)
  thus ?thesis by (simp add: interval_lebesgue_integrable_def one_ereal_def)
qed

lemma uniform_limit2:
  "uniform_limit {z. Re z \<in> {x..y}}
        (\<lambda>a z. LBINT u=exp (-1)..a. f z u)
        (\<lambda>z. LBINT u=exp (-1)..1. f z u) (at_left 1)"
  by (intro uniform_limit_interval_integral_right[of _ _ g2] AE_I2 impI)
     (use bound2 integrable_bound2 in \<open>simp_all add: einterval_def f_def set_borel_measurable_def\<close>)

lemma uniform_limit2':
    "uniform_limit {z. Re z \<in> {x..y}}
          (\<lambda>n z. LBINT u=exp (-1)..ereal (1-(1/2)^Suc n). f z u)
          (\<lambda>z. LBINT u=exp (-1)..1. f z u) sequentially"
proof (rule filterlim_compose[OF uniform_limit2])
  have "filterlim (\<lambda>n. 1 - (1/2)^Suc n :: real) (at_left 1) sequentially"
    by real_asymp
  hence "filtermap ereal (filtermap (\<lambda>n. (1 - (1 / 2) ^ Suc n)) sequentially) \<le>
        filtermap ereal (at_left 1)"
    unfolding filterlim_def by (rule filtermap_mono)
  thus "filterlim (\<lambda>n. ereal (1 - (1/2)^Suc n)) (at_left 1) sequentially"
    unfolding one_ereal_def at_left_ereal by (simp add: filterlim_def filtermap_filtermap)
qed

lemma bound1: "norm (f z u) \<le> g1 u" if z: "Re z \<in> {x..y}" and u: "u \<in> {0<..<exp (-1)}" for z u
proof -
  from u have "u \<le> exp (-1)" by (simp add: einterval_def)
  also have "exp (-1) < exp (0::real)"
    by (subst exp_less_cancel_iff) auto
  also have "exp (0::real) = 1" by simp
  finally have "u < 1" .
  from u have "ln u < ln (exp (-1))"
    by (subst ln_less_cancel_iff) (auto simp: einterval_def)
  hence ln_u: "ln u < -1" by simp
  from z u \<open>u < 1\<close> have "norm (f z u) = (- ln u) powr Re z * \<bar>u - ln u - 1\<bar> / (1 - u)"
    unfolding f_def norm_mult norm_divide norm_of_real
    by (simp add: norm_powr_real_powr einterval_def)
  also have "\<bar>u - ln u - 1\<bar> = u - ln u - 1"
    using u ln_add_one_self_le_self2[of "u - 1"] by (simp add: einterval_def)
  also have "(- ln u) powr Re z * (u - ln u - 1) / (1 - u) \<le>
               (- ln u) powr y * (u - ln u - 1) / (1 - u)"
    using z u ln_u \<open>u < 1\<close>
    by (intro mult_right_mono divide_right_mono powr_mono) (auto simp: einterval_def)
  finally show "norm (f z u) \<le> g1 u" by (simp add: g1_def)
qed

lemma integrable1_aux: "interval_lebesgue_integrable lborel 0 (exp (-1)) (f z)"
  if z: "Re z \<in> {x..y}" for z
proof -
  have "set_integrable lborel {0<..<exp (-1)} (f z)"
  proof (rule set_integrable_bound[OF _ _ AE_I2[OF impI]])
    fix u :: real assume "u \<in> {0<..<exp (-1)}"
    hence "norm (f z u) \<le> g1 u" using z by (intro bound1) auto
    also have "\<dots> \<le> norm (g1 u)" by simp
    finally show "norm (f z u) \<le> norm (g1 u)" .
  qed (use integrable_bound1 in \<open>simp_all add: interval_lebesgue_integrable_def
         zero_ereal_def set_borel_measurable_def f_def\<close>)
  thus ?thesis by (simp add: interval_lebesgue_integrable_def zero_ereal_def)
qed

lemma uniform_limit1:
  "uniform_limit {z. Re z \<in> {x..y}}
        (\<lambda>a z. LBINT u=a..exp (-1). f z u)
        (\<lambda>z. LBINT u=0..exp (-1). f z u) (at_right 0)"
  by (intro uniform_limit_interval_integral_left[of _ _ g1] AE_I2 impI)
     (use bound1 integrable_bound1 in \<open>simp_all add: einterval_def f_def set_borel_measurable_def\<close>)

lemma uniform_limit1':
    "uniform_limit {z. Re z \<in> {x..y}}
          (\<lambda>n z. LBINT u=ereal ((1/2)^Suc n)..exp (-1). f z u)
          (\<lambda>z. LBINT u=0..exp (-1). f z u) sequentially"
proof (rule filterlim_compose[OF uniform_limit1])
  have "filterlim (\<lambda>n. (1/2)^Suc n :: real) (at_right 0) sequentially"
    by real_asymp
  hence "filtermap ereal (filtermap (\<lambda>n. ((1 / 2) ^ Suc n)) sequentially) \<le>
        filtermap ereal (at_right 0)"
    unfolding filterlim_def by (rule filtermap_mono)
  thus "filterlim (\<lambda>n. ereal ((1/2)^Suc n)) (at_right 0) sequentially"
    unfolding zero_ereal_def at_right_ereal by (simp add: filterlim_def filtermap_filtermap)
qed

end

text \<open>
  With all of the above bounds, we have shown that the integral exists for any
  \<open>z\<close> with $\mathfrak{R}(z) > -2$.
\<close>
theorem Hadjicostas_integral_integrable: "interval_lebesgue_integrable lborel 0 1 (f z)"
  if z: "Re z > -2"
proof -
  from dense[OF z] obtain x where x: "x > -2" "Re z > x" by blast
  have "interval_lebesgue_integrable lborel 0 (exp(-1)) (f z)"
    by (rule integrable1_aux[of x _ "Re z + 1"]) (use x in auto)
  moreover have "interval_lebesgue_integrable lborel (exp(-1)) 1 (f z)"
    by (rule integrable2_aux[of x _ "Re z + 1"]) (use x in auto)
  ultimately show "interval_lebesgue_integrable lborel 0 1 (f z)"
    by (rule interval_lebesgue_integrable_combine) (auto simp: f_def set_borel_measurable_def)
qed

lemma integral_holo_aux:
  assumes ab: "a > 0" "a \<le> b" "b < 1"
  shows "(\<lambda>z. LBINT u=ereal a..ereal b. f z u) holomorphic_on A"
proof -
  define f' :: "complex \<Rightarrow> real \<Rightarrow> complex"
    where "f' \<equiv> (\<lambda>z u. ln (-ln u) * f z u)"
  note [derivative_intros] = has_field_derivative_complex_powr_right'

  have "(\<lambda>z. integral (cbox a b) (f z)) holomorphic_on UNIV"
  proof (rule leibniz_rule_holomorphic[of _ _ _ _ f'], goal_cases)
    case (1 z t)
    show ?case unfolding f_def
      apply (insert 1 ab)
      apply (rule derivative_eq_intros refl | simp)+
      apply (auto simp: f'_def field_simps f_def Ln_of_real)
      done
  next
    from ab show "continuous_on (UNIV \<times> cbox a b) (\<lambda>(z, t). f' z t)"
      by (auto simp: case_prod_unfold f'_def f_def Ln_of_real intro!: continuous_intros)
  next
    fix z :: complex
    show "f z integrable_on cbox a b"
      unfolding f_def f'_def using ab
      by (intro integrable_continuous continuous_intros) auto
  qed (auto simp: convex_halfspace_Re_gt)
  also have "(\<lambda>z. integral (cbox a b) (f z)) = (\<lambda>z. \<integral>u\<in>cbox a b. f z u \<partial>lborel)"
  proof (intro ext set_borel_integral_eq_integral(2) [symmetric])
    fix z :: complex
    show "complex_set_integrable lborel (cbox a b) (f z)"
      unfolding f_def using ab
      by (intro continuous_on_imp_set_integrable_cbox continuous_intros) (auto simp: Ln_of_real)
  qed
  also have "\<dots> = (\<lambda>z. LBINT u=a..b. f z u)"
    using ab by (simp add: interval_integral_Icc)
  finally show ?thesis by (rule holomorphic_on_subset) auto
qed

lemma integral_holo:
  assumes ab: "min a b > 0" "max a b < 1"
  shows "(\<lambda>z. LBINT u=ereal a..ereal b. f z u) holomorphic_on A"
proof (cases "a \<le> b")
  case True
  thus ?thesis using assms integral_holo_aux[of a b] by auto
next
  case False
  have "(\<lambda>z. -(LBINT u=ereal b..ereal a. f z u)) holomorphic_on A"
    using False assms by (intro holomorphic_intros integral_holo_aux) auto
  thus ?thesis by (subst interval_integral_endpoints_reverse)
qed 

lemma holo1: "(\<lambda>z. LBINT u=0..exp (-1). f z u) holomorphic_on {z. Re z > -2}"
proof (rule holomorphic_uniform_sequence
    [where f = "(\<lambda>n z. LBINT u=ereal ((1/2)^Suc n)..exp (-1). f z u)"], goal_cases)
  case (3 z)
  define \<epsilon> where "\<epsilon> = (Re z + 2) / 2"
  from 3 have "\<epsilon> > 0" by (auto simp: \<epsilon>_def)
  have subset: "cball z \<epsilon> \<subseteq> {s. Re s \<in> {Re z - \<epsilon>..Re z + \<epsilon>}}"
  proof safe
    fix s assume s: "s \<in> cball z \<epsilon>"
    have "\<bar>Re (s - z)\<bar> \<le> norm (s - z)" by (rule abs_Re_le_cmod)
    also have "\<dots> \<le> \<epsilon>" using s by (simp add: dist_norm norm_minus_commute)
    finally show "Re s \<in> {Re z - \<epsilon>..Re z + \<epsilon>}" by auto
  qed

  show ?case
  proof (rule exI[of _ \<epsilon>], intro conjI)
    have "cball z \<epsilon> \<subseteq> {s. Re s \<in> {Re z - \<epsilon>..Re z + \<epsilon>}}" by fact
    also have "\<dots> \<subseteq> {s. Re s > -2}"
      using 3 by (auto simp: \<epsilon>_def field_simps)
    finally show "cball z \<epsilon> \<subseteq> {s. Re s > -2}" .
  next
    from 3 have "Re z - \<epsilon> > -2" by (simp add: \<epsilon>_def field_simps)
    thus "uniform_limit (cball z \<epsilon>) (\<lambda>n z. LBINT u=ereal ((1 / 2) ^ Suc n)..ereal (exp (- 1)). f z u)
            (\<lambda>z. LBINT u=0..ereal (exp(-1)). f z u) sequentially"
      using uniform_limit_on_subset[OF uniform_limit1' subset] by simp
  qed fact+
next
  fix n :: nat
  have "(1 / 2) ^ Suc n < (1 / 2 :: real) ^ 0"
    by (subst power_strict_decreasing_iff) auto
  thus "(\<lambda>z. LBINT u=ereal ((1 / 2) ^ Suc n)..ereal (exp (- 1)). f z u) holomorphic_on {z. Re z > -2}"
    by (intro integral_holo) auto
qed (auto simp: open_halfspace_Re_gt)

lemma holo2: "(\<lambda>z. LBINT u=exp (-1)..1. f z u) holomorphic_on {z. Re z > -2}"
proof (rule holomorphic_uniform_sequence
    [where f = "(\<lambda>n z. LBINT u=exp (-1)..ereal (1-(1/2)^Suc n). f z u)"], goal_cases)
  case (3 z)
  define \<epsilon> where "\<epsilon> = (Re z + 2) / 2"
  from 3 have "\<epsilon> > 0" by (auto simp: \<epsilon>_def)
  have subset: "cball z \<epsilon> \<subseteq> {s. Re s \<in> {Re z - \<epsilon>..Re z + \<epsilon>}}"
  proof safe
    fix s assume s: "s \<in> cball z \<epsilon>"
    have "\<bar>Re (s - z)\<bar> \<le> norm (s - z)" by (rule abs_Re_le_cmod)
    also have "\<dots> \<le> \<epsilon>" using s by (simp add: dist_norm norm_minus_commute)
    finally show "Re s \<in> {Re z - \<epsilon>..Re z + \<epsilon>}" by auto
  qed

  show ?case
  proof (rule exI[of _ \<epsilon>], intro conjI)
    have "cball z \<epsilon> \<subseteq> {s. Re s \<in> {Re z - \<epsilon>..Re z + \<epsilon>}}" by fact
    also have "\<dots> \<subseteq> {s. Re s > -2}"
      using 3 by (auto simp: \<epsilon>_def field_simps)
    finally show "cball z \<epsilon> \<subseteq> {s. Re s > -2}" .
  next
    from 3 have "Re z - \<epsilon> > -2" by (simp add: \<epsilon>_def field_simps)
    thus "uniform_limit (cball z \<epsilon>) (\<lambda>n z. LBINT u=ereal (exp (- 1))..ereal (1-(1/2)^Suc n). f z u)
            (\<lambda>z. LBINT u=ereal (exp(-1))..1. f z u) sequentially"
      using uniform_limit_on_subset[OF uniform_limit2' subset] by simp
  qed fact+
next
  fix n :: nat
  have "(1 / 2) ^ Suc n < (1 / 2 :: real) ^ 0"
    by (subst power_strict_decreasing_iff) auto
  thus "(\<lambda>z. LBINT u=ereal (exp (-1))..ereal (1-(1/2)^Suc n). f z u) holomorphic_on {z. Re z > -2}"
    by (intro integral_holo) auto
qed (auto simp: open_halfspace_Re_gt)

text \<open>
  Finally, we have shown that Hadjicostas's integral is an analytic function
  of \<open>z\<close> in the domain $\mathfrak{R}(z) > -2$.
\<close>
lemma holomorphic_Hadjicostas_integral:
  "Hadjicostas_integral holomorphic_on {z. Re z > -2}"
proof -
  have "(\<lambda>z. (LBINT u=0..exp(-1). f z u) + (LBINT u=exp(-1)..1. f z u))
          holomorphic_on {z. Re z > -2}"
    by (intro holomorphic_intros holo1 holo2)
  also have "?this \<longleftrightarrow> (\<lambda>z. LBINT u=0..1. f z u) holomorphic_on {z. Re z > -2}"
    using Hadjicostas_integral_integrable
    by (intro holomorphic_cong interval_integral_sum)
       (simp_all add: zero_ereal_def one_ereal_def min_def max_def)
  also have "(\<lambda>z. LBINT u=0..1. f z u) = Hadjicostas_integral"
    by (simp add: Hadjicostas_integral_def[abs_def] f_def)
  finally show ?thesis .
qed

lemma analytic_Hadjicostas_integral:
  "Hadjicostas_integral analytic_on {z. Re z > -2}"
  by (simp add: analytic_on_open open_halfspace_Re_gt holomorphic_Hadjicostas_integral)

end


subsection \<open>Analytic continuation and main result\<close>

text \<open>
  Since we have already shown the formula for any real \<open>z > -1\<close> and e.\,g.\ 0 is a limit
  point of that set, it extends to the full domain by analytic continuation.

  As a caveat, note that $\zeta(s)$ is \<^emph>\<open>not\<close> analytic at \<open>z = 1\<close>, so that we use
  an analytic continuation of $\zeta(z) - \frac{1}{z-1}$ to state the formula. This
  continuation is @{term "pre_zeta 1"}.
\<close>
lemma Hadjicostas_Chapman_formula_aux:
  assumes z: "Re z > -2"
  shows   "Hadjicostas_integral z = Gamma (z + 2) * pre_zeta 1 (z + 2)"
    (is "_ z = ?f z")
proof (rule analytic_continuation'[of Hadjicostas_integral])
  show "Hadjicostas_integral holomorphic_on {z. Re z > -2}"
    by (rule holomorphic_Hadjicostas_integral)
  show "connected {z. Re z > -2}"
    by (intro convex_connected convex_halfspace_Re_gt)
  show "open {z. Re z > -2}"
    by (auto simp: open_halfspace_Re_gt)
  show "{z. Re z > -1 \<and> Im z = 0} \<subseteq> {z. Re z > -2}" and "0 \<in> {z. Re z > -2}"
    by auto
  have "\<forall>n. 1 / (of_nat (Suc n)) \<in> {z. Re z > -1 \<and> Im z = 0} - {0}"
    by (auto simp: field_simps simp flip: of_nat_Suc)
  moreover have "(\<lambda>n. 1 / of_nat (Suc n) :: complex) \<longlonglongrightarrow> 0"
    by (rule tendsto_divide_0[OF tendsto_const] filterlim_compose[OF tendsto_of_nat] filterlim_Suc)+
  ultimately show "0 islimpt {z. Re z > -1 \<and> Im z = 0}"
    unfolding islimpt_sequential
    by (intro exI[of _ "\<lambda>n. 1 / of_nat (Suc n) :: complex"]) simp
  show "?f holomorphic_on {z. - 2 < Re z}"
  proof (intro holomorphic_intros)
    fix z assume z: "z \<in> {z. Re z > -2}"
    hence "z + 2 \<notin> \<real>\<^sub>\<le>\<^sub>0" by (auto elim!: nonpos_Reals_cases simp: complex_eq_iff)
    thus "z + 2 \<notin> \<int>\<^sub>\<le>\<^sub>0" using nonpos_Ints_subset_nonpos_Reals by blast
  qed auto
next
  fix s assume s: "s \<in> {z. - 1 < Re z \<and> Im z = 0}"
  hence "s + 2 \<noteq> 1" by (simp add: algebra_simps complex_eq_iff)
  have ineq: "x - ln x \<ge> 1" if "x \<in> {0<..<1}" for x :: real
    using ln_le_minus_one[of x] that by (simp add: algebra_simps)
  define x where "x = Re s"
  from s have x: "x > -1" and [simp]: "s = of_real x"
    by (auto simp: x_def complex_eq_iff)
  have "Hadjicostas_integral s = (LBINT u=0..1. of_real ((-ln u) powr x / (1-u) * (-ln u + u - 1)))"
    unfolding Hadjicostas_integral_def
    by (intro interval_lebesgue_integral_cong) (auto simp: einterval_def powr_Reals_eq)
  also have "\<dots> = of_real (LBINT u=0..1. (-ln u) powr x / (1-u) * (-ln u + u - 1))"
    by (subst interval_lebesgue_integral_of_real) auto
  also have "(LBINT u=0..1. (- ln u) powr x / (1 - u) * (- ln u + u - 1)) =
             (\<integral>u. (- ln u) powr x / (1-u) * (- ln u + u - 1) * indicator {0<..<1} u \<partial>lborel)"
    by (simp add: interval_integral_Ioo zero_ereal_def one_ereal_def set_lebesgue_integral_def mult_ac)
  also have "\<dots> = enn2real (Hadjicostas_nn_integral x)"
    unfolding Hadjicostas_nn_integral_def using ineq
    by (subst integral_eq_nn_integral)
       (auto intro!: AE_I2 divide_nonneg_nonneg mult_nonneg_nonneg arg_cong[where f = enn2real]
               nn_integral_cong simp: indicator_def)
  also have "\<dots> = enn2real (ennreal (Gamma (x + 2) * (Re (zeta (x + 2)) - 1 / (x + 1))))"
    using x by (subst Hadjicostas_Chapman_formula_real) auto
  also have "\<dots> = Gamma (x + 2) * (Re (zeta (x + 2)) - 1 / (x + 1))"
    using x real_zeta_ge_one_over_minus_one[of "x + 2"]
    by (intro enn2real_ennreal mult_nonneg_nonneg Gamma_real_nonneg) (auto simp: add_ac)
  also have "complex_of_real \<dots> = Gamma (s + 2) * (zeta (s + 2) -  1 / (s + 1))"
    using x Gamma_complex_of_real[of "x + 2"] by (simp add: zeta_real')
  also have "(zeta (s + 2) -  1 / (s + 1)) = pre_zeta 1 (s + 2)"
    using \<open>s + 2 \<noteq> 1\<close> by (subst zeta_minus_pole_eq [symmetric]) (auto simp flip: of_nat_Suc)
  finally show "Hadjicostas_integral s = Gamma (s + 2) * pre_zeta 1 (s + 2)" .
qed (use assms in auto)

text \<open>
  The following form and the corollary are perhaps a bit nicer to read.
\<close>
theorem Hadjicostas_Chapman_formula:
  assumes z: "Re z > -2" "z \<noteq> -1"
  shows   "Hadjicostas_integral z = Gamma (z + 2) * (zeta (z + 2) - 1 / (z + 1))"
proof -
  from z have "z + 1 \<noteq> 0"
    by (auto simp: complex_eq_iff)
  thus ?thesis using Hadjicostas_Chapman_formula_aux[of z] assms
    by (subst (asm) zeta_minus_pole_eq [symmetric]) (auto simp: add_ac)
qed

corollary euler_mascheroni_integral_form:
  "Hadjicostas_integral (-1) = euler_mascheroni"
  using Hadjicostas_Chapman_formula_aux[of "-1"] by simp

end
