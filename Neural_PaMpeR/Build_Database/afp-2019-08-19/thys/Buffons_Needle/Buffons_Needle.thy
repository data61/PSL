(*
  File:    Buffons_Needle.thy
  Author:  Manuel Eberl <eberlm@in.tum.de>

  A formal solution of Buffon's needle problem.
*)
section \<open>Buffon's Needle Problem\<close>
theory Buffons_Needle
  imports "HOL-Probability.Probability"
begin

subsection \<open>Auxiliary material\<close>

lemma sin_le_zero': "sin x \<le> 0" if "x \<ge> -pi" "x \<le> 0" for x
  by (metis minus_le_iff neg_0_le_iff_le sin_ge_zero sin_minus that(1) that(2))

lemma emeasure_Un':
  assumes "A \<in> sets M" "B \<in> sets M" "A \<inter> B \<in> null_sets M"
  shows   "emeasure M (A \<union> B) = emeasure M A + emeasure M B"
proof -
  have "A \<union> B = A \<union> (B - A \<inter> B)" by blast
  also have "emeasure M \<dots> = emeasure M A + emeasure M (B - A \<inter> B)"
    using assms by (subst plus_emeasure) auto
  also have "emeasure M (B - A \<inter> B) = emeasure M B"
    using assms by (intro emeasure_Diff_null_set) auto
  finally show ?thesis .
qed

lemma singleton_null_set_lborel [simp,intro]: "{x} \<in> null_sets lborel"
  by (simp add: null_sets_def)

lemma continuous_on_min [continuous_intros]:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::linorder_topology"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. min (f x) (g x))"
  by (auto simp: continuous_on_def intro!: tendsto_min)
    
lemma integral_shift:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes cont: "continuous_on {a + c..b + c} f"
  shows "integral {a..b} (f \<circ> (\<lambda>x. x + c)) = integral {a + c..b + c} f"
proof (cases "a \<le> b")
  case True
  have "((\<lambda>x. 1 *\<^sub>R f (x + c)) has_integral integral {a+c..b+c} f) {a..b}"
    using True cont
    by (intro has_integral_substitution[where c = "a + c" and d = "b + c"])
       (auto intro!: derivative_eq_intros)
  thus ?thesis by (simp add: has_integral_iff o_def)
qed auto

lemma arcsin_le_iff:
  assumes "x \<ge> -1" "x \<le> 1" "y \<ge> -pi/2" "y \<le> pi/2"
  shows   "arcsin x \<le> y \<longleftrightarrow> x \<le> sin y"
proof -
  have "arcsin x \<le> y \<longleftrightarrow> sin (arcsin x) \<le> sin y"
    using arcsin_bounded[of x] assms by (subst sin_mono_le_eq) auto
  also from assms have "sin (arcsin x) = x" by simp
  finally show ?thesis .
qed

lemma le_arcsin_iff:
  assumes "x \<ge> -1" "x \<le> 1" "y \<ge> -pi/2" "y \<le> pi/2"
  shows   "arcsin x \<ge> y \<longleftrightarrow> x \<ge> sin y"
proof -
  have "arcsin x \<ge> y \<longleftrightarrow> sin (arcsin x) \<ge> sin y"
    using arcsin_bounded[of x] assms by (subst sin_mono_le_eq) auto
  also from assms have "sin (arcsin x) = x" by simp
  finally show ?thesis .
qed


subsection \<open>Problem definition\<close>

text \<open>
  Consider a needle of length $l$ whose centre has the $x$-coordinate $x$. The following then
  defines the set of all $x$-coordinates that the needle covers 
  (i.e. the projection of the needle onto the $x$-axis.)
\<close>
definition needle :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real set" where
  "needle l x \<phi> = closed_segment (x - l / 2 * sin \<phi>) (x + l / 2 * sin \<phi>)"

text \<open>
  Buffon's Needle problem is then this: Assuming the needle's $x$ position is chosen uniformly
  at random in a strip of width $d$ centred at the origin, what is the probability that the 
  needle crosses at least one of the left/right boundaries of that strip (located at 
  $x = \pm\frac{1}{2}d$)?
\<close>
definition buffon :: "real \<Rightarrow> real \<Rightarrow> bool measure" where
  "buffon l d = 
     do {
       (x, \<phi>) \<leftarrow> uniform_measure lborel ({-d/2..d/2} \<times> {-pi..pi});
       return (count_space UNIV) (needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {})
     }"


subsection \<open>Derivation of the solution\<close>

text \<open>
  The following form is a bit easier to handle.
\<close>
lemma buffon_altdef:
  "buffon l d =
     do {
       (x, \<phi>) \<leftarrow> uniform_measure lborel ({-d/2..d/2} \<times> {-pi..pi});
       return (count_space UNIV) 
         (let a = x - l / 2 * sin \<phi>; b = x + l / 2 * sin \<phi>
          in  min a b + d/2 \<le> 0 \<and> max a b + d/2 \<ge> 0 \<or> min a b - d/2 \<le> 0 \<and> max a b - d/2 \<ge> 0)
     }"
proof -
  note buffon_def[of l d]
  also {
    have "(\<lambda>(x,\<phi>). needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}) =
        (\<lambda>(x,\<phi>). let a = x - l / 2 * sin \<phi>; b = x + l / 2 * sin \<phi>
                 in  -d/2 \<ge> min a b \<and> -d/2 \<le> max a b \<or> min a b \<le> d/2 \<and> max a b \<ge> d/2)"
      by (auto simp: needle_def Let_def closed_segment_eq_real_ivl min_def max_def)
    also have "\<dots> = 
      (\<lambda>(x,\<phi>). let a = x - l / 2 * sin \<phi>; b = x + l / 2 * sin \<phi>
               in  min a b + d/2 \<le> 0 \<and> max a b + d/2 \<ge> 0 \<or> min a b - d/2 \<le> 0 \<and> max a b - d/2 \<ge> 0)"
      by (auto simp add: algebra_simps Let_def)
    finally have "(\<lambda>(x, \<phi>). return (count_space UNIV) (needle l x \<phi> \<inter> {- d/2, d/2} \<noteq> {})) =
                  (\<lambda>(x,\<phi>). return (count_space UNIV) 
                    (let a = x - l / 2 * sin \<phi>; b = x + l / 2 * sin \<phi>
                     in  min a b + d/2 \<le> 0 \<and> max a b + d/2 \<ge> 0 \<or> min a b - d/2 \<le> 0 \<and> max a b - d/2 \<ge> 0))"
      by (simp add: case_prod_unfold fun_eq_iff)
  }
  finally show ?thesis .
qed
    
text \<open>
  It is obvious that the problem boils down to determining the measure of the following set:
\<close>
definition buffon_set :: "real \<Rightarrow> real \<Rightarrow> (real \<times> real) set" where
  "buffon_set l d = {(x,\<phi>) \<in> {-d/2..d/2} \<times> {-pi..pi}. abs x \<ge> d / 2 - abs (sin \<phi>) * l / 2}"

text \<open>
  By using the symmetry inherent in the problem, we can reduce the problem to the following 
  set, which corresponds to one quadrant of the original set:
\<close>
definition buffon_set' :: "real \<Rightarrow> real \<Rightarrow> (real \<times> real) set" where
  "buffon_set' l d = {(x,\<phi>) \<in> {0..d/2} \<times> {0..pi}. x \<ge> d / 2 - sin \<phi> * l / 2}"

lemma closed_buffon_set [simp, intro, measurable]: "closed (buffon_set l d)"
proof -
  have "buffon_set l d = ({-d/2..d/2} \<times> {-pi..pi}) \<inter> 
          (\<lambda>z. abs (fst z) + abs (sin (snd z)) * l / 2 - d / 2) -` {0..}" 
    (is "_ = ?A") unfolding buffon_set_def by auto
  also have "closed \<dots>"
    by (intro closed_Int closed_vimage closed_Times) (auto intro!: continuous_intros)
  finally show ?thesis by simp
qed

lemma closed_buffon_set' [simp, intro, measurable]: "closed (buffon_set' l d)"
proof -
  have "buffon_set' l d = ({0..d/2} \<times> {0..pi}) \<inter> 
          (\<lambda>z. fst z + sin (snd z) * l / 2 - d / 2) -` {0..}" 
    (is "_ = ?A") unfolding buffon_set'_def by auto
  also have "closed \<dots>"
    by (intro closed_Int closed_vimage closed_Times) (auto intro!: continuous_intros)
  finally show ?thesis by simp
qed

lemma measurable_buffon_set [measurable]: "buffon_set l d \<in> sets borel" 
  by measurable

lemma measurable_buffon_set' [measurable]: "buffon_set' l d \<in> sets borel" 
  by measurable


context
  fixes d l :: real
  assumes d: "d > 0" and l: "l > 0"
begin

lemma buffon_altdef':
  "buffon l d = distr (uniform_measure lborel ({-d/2..d/2} \<times> {-pi..pi}))
                  (count_space UNIV) (\<lambda>z. z \<in> buffon_set l d)"
proof -
  let ?P = "\<lambda>(x,\<phi>). let a = x - l / 2 * sin \<phi>; b = x + l / 2 * sin \<phi>
                    in  min a b + d/2 \<le> 0 \<and> max a b + d/2 \<ge> 0 \<or> min a b - d/2 \<le> 0 \<and> max a b - d/2 \<ge> 0"
  have "buffon l d = 
          uniform_measure lborel ({- d / 2..d / 2} \<times> {-pi..pi}) \<bind>
          (\<lambda>z. return (count_space UNIV) (?P z))"
    unfolding buffon_altdef case_prod_unfold by simp
  also have "\<dots> = uniform_measure lborel ({- d / 2..d / 2} \<times> {-pi..pi}) \<bind>
          (\<lambda>z. return (count_space UNIV) (z \<in> buffon_set l d))"
  proof (intro bind_cong_AE AE_uniform_measureI AE_I2 impI refl return_measurable, goal_cases)
    show "(\<lambda>z. return (count_space UNIV) (?P z))
             \<in> uniform_measure lborel ({- d / 2..d / 2} \<times> {- pi..pi}) \<rightarrow>\<^sub>M
                 subprob_algebra (count_space UNIV)"
      unfolding Let_def case_prod_unfold lborel_prod [symmetric] by measurable
    show "(\<lambda>z. return (count_space UNIV) (z \<in> buffon_set l d))
            \<in> uniform_measure lborel ({- d / 2..d / 2} \<times> {- pi..pi}) \<rightarrow>\<^sub>M
                subprob_algebra (count_space UNIV)" by simp
    
    case (4 z)
    hence "?P z \<longleftrightarrow> z \<in> buffon_set l d"
    proof (cases "snd z \<ge> 0")
      case True
      with 4 have "fst z - l / 2 * sin (snd z) \<le> fst z + l / 2 * sin (snd z)" using l
        by (auto simp: sin_ge_zero)
      moreover from True and 4 have "sin (snd z) \<ge> 0" by (auto simp: sin_ge_zero)
      ultimately show ?thesis using 4 True unfolding buffon_set_def
        by (force simp: field_simps Let_def min_def max_def case_prod_unfold abs_if)
    next
      case False
      with 4 have "fst z - l / 2 * sin (snd z) \<ge> fst z + l / 2 * sin (snd z)" using l
        by (auto simp: sin_le_zero' mult_nonneg_nonpos)
      moreover from False and 4 have "sin (snd z) \<le> 0" by (auto simp: sin_le_zero')
      ultimately show ?thesis using 4 and False
        unfolding buffon_set_def using l d
        by (force simp: field_simps Let_def min_def max_def case_prod_unfold abs_if)
    qed
    thus ?case by (simp only: )
  qed (simp_all add: borel_prod [symmetric])
  also have "\<dots> = distr (uniform_measure lborel ({-d/2..d/2} \<times> {-pi..pi})) 
                    (count_space UNIV) (\<lambda>z. z \<in> buffon_set l d)"
    by (rule bind_return_distr') simp_all
  finally show ?thesis .
qed

lemma buffon_prob_aux:
  "emeasure (buffon l d) {True} = emeasure lborel (buffon_set l d) / ennreal (2 * d * pi)"
proof -
  have [measurable]: "A \<times> B \<in> sets borel" if "A \<in> sets borel" "B \<in> sets borel" 
    for A B :: "real set" using that unfolding borel_prod [symmetric] by simp
    
  have "emeasure (buffon l d) {True} = 
          emeasure (uniform_measure lborel ({- (d / 2)..d / 2} \<times> {-pi..pi}))
          ((\<lambda>z. z \<in> buffon_set l d) -` {True})" (is "_ = emeasure ?M _")
    by (simp add: buffon_altdef' emeasure_distr)
  also have "(\<lambda>z. z \<in> buffon_set l d) -` {True} = buffon_set l d" by auto
  also have "buffon_set l d \<subseteq> {-d/2..d/2} \<times> {-pi..pi}"
    using l d by (auto simp: buffon_set_def)
  hence "emeasure ?M (buffon_set l d) = 
           emeasure lborel (buffon_set l d) / emeasure lborel ({- (d / 2)..d / 2} \<times> {-pi..pi})"
    by (subst emeasure_uniform_measure) (simp_all add: Int_absorb1)
  also have "emeasure lborel ({- (d / 2)..d / 2} \<times> {-pi..pi}) = ennreal (2 * pi * d)"
    using d by (simp add: lborel_prod [symmetric] lborel.emeasure_pair_measure_Times
                          ennreal_mult algebra_simps)
  finally show ?thesis by (simp add: mult_ac)
qed

lemma emeasure_buffon_set_conv_buffon_set':
  "emeasure lborel (buffon_set l d) = 4 * emeasure lborel (buffon_set' l d)"
proof -
  have distr_lborel [simp]: "distr M lborel f = distr M borel f" for M and f :: "real \<Rightarrow> real"
    by (rule distr_cong) simp_all
    
  define A where "A = buffon_set' l d"
  define B C D where "B = (\<lambda>x. (-fst x, snd x)) -` A" and "C = (\<lambda>x. (fst x, -snd x)) -` A" and
      "D = (\<lambda>x. (-fst x, -snd x)) -` A"
  have meas [measurable]:
     "(\<lambda>x::real \<times> real. (-fst x, snd x)) \<in> borel_measurable borel"
     "(\<lambda>x::real \<times> real. (fst x, -snd x)) \<in> borel_measurable borel"
     "(\<lambda>x::real \<times> real. (-fst x, -snd x)) \<in> borel_measurable borel"
    unfolding borel_prod [symmetric] by measurable
  have meas' [measurable]: "A \<in> sets borel" "B \<in> sets borel" "C \<in> sets borel" "D \<in> sets borel"
    unfolding A_def B_def C_def D_def by (rule measurable_buffon_set' measurable_sets_borel meas)+
  
  have *: "buffon_set l d = A \<union> B \<union> C \<union> D"
  proof (intro equalityI subsetI, goal_cases)
    case (1 z)
    show ?case
    proof (cases "fst z \<ge> 0"; cases "snd z \<ge> 0")
      assume "fst z \<ge> 0" "snd z \<ge> 0"
      with 1 have "z \<in> A"
        by (auto split: prod.splits simp: buffon_set_def buffon_set'_def sin_ge_zero A_def)
      thus ?thesis by blast   
    next
      assume "\<not>(fst z \<ge> 0)" "snd z \<ge> 0"
      with 1 have "z \<in> B"
        by (auto split: prod.splits simp: buffon_set_def buffon_set'_def sin_ge_zero A_def B_def)
      thus ?thesis by blast
    next    
      assume "fst z \<ge> 0" "\<not>(snd z \<ge> 0)"
      with 1 have "z \<in> C"
        by (auto split: prod.splits simp: buffon_set_def buffon_set'_def sin_le_zero' A_def C_def)
      thus ?thesis by blast   
    next
      assume "\<not>(fst z \<ge> 0)" "\<not>(snd z \<ge> 0)"
      with 1 have "z \<in> D"
        by (auto split: prod.splits simp: buffon_set_def buffon_set'_def sin_le_zero' A_def D_def)
      thus ?thesis by blast
    qed
  qed (auto simp: buffon_set_def buffon_set'_def sin_ge_zero sin_le_zero'  A_def B_def C_def D_def)
  
  have "A \<inter> B = {0} \<times> ({0..pi} \<inter> {\<phi>. sin \<phi> * l - d \<ge> 0})"
    using d l by (auto simp: buffon_set'_def  A_def B_def C_def D_def)
  moreover have "emeasure lborel \<dots> = 0"
    unfolding lborel_prod [symmetric] by (subst lborel.emeasure_pair_measure_Times) simp_all
  ultimately have AB: "(A \<inter> B) \<in> null_sets lborel"
    unfolding lborel_prod [symmetric] by (simp add: null_sets_def)
  
  have "C \<inter> D = {0} \<times> ({-pi..0} \<inter> {\<phi>. -sin \<phi> * l - d \<ge> 0})"
    using d l by (auto simp: buffon_set'_def  A_def B_def C_def D_def)
  moreover have "emeasure lborel \<dots> = 0"
    unfolding lborel_prod [symmetric] by (subst lborel.emeasure_pair_measure_Times) simp_all
  ultimately have CD: "(C \<inter> D) \<in> null_sets lborel"
    unfolding lborel_prod [symmetric] by (simp add: null_sets_def)

  have "A \<inter> D = {}" "B \<inter> C = {}" using d l 
    by (auto simp: buffon_set'_def A_def D_def B_def C_def)
  moreover have "A \<inter> C = {(d/2, 0)}" "B \<inter> D = {(-d/2, 0)}"
    using d l by (auto simp: case_prod_unfold buffon_set'_def A_def B_def C_def D_def)
  ultimately have AD: "A \<inter> D \<in> null_sets lborel" and BC: "B \<inter> C \<in> null_sets lborel" and
    AC: "A \<inter> C \<in> null_sets lborel" and BD: "B \<inter> D \<in> null_sets lborel" by simp_all
  
  note *
  also have "emeasure lborel (A \<union> B \<union> C \<union> D) = emeasure lborel (A \<union> B \<union> C) + emeasure lborel D"
    using AB AC AD BC BD CD by (intro emeasure_Un') (auto simp: Int_Un_distrib2)
  also have "emeasure lborel (A \<union> B \<union> C) = emeasure lborel (A \<union> B) + emeasure lborel C"
    using AB AC BC using AB AC AD BC BD CD by (intro emeasure_Un') (auto simp: Int_Un_distrib2)
  also have "emeasure lborel (A \<union> B) = emeasure lborel A + emeasure lborel B"
    using AB using AB AC AD BC BD CD by (intro emeasure_Un') (auto simp: Int_Un_distrib2)
  also have "emeasure lborel B = emeasure (distr lborel lborel (\<lambda>(x,y). (-x, y))) A"
    (is "_ = emeasure ?M _") unfolding B_def 
    by (subst emeasure_distr) (simp_all add: case_prod_unfold)
  also have "?M = lborel" unfolding lborel_prod [symmetric]
    by (subst pair_measure_distr [symmetric]) (simp_all add: sigma_finite_lborel lborel_distr_uminus)
  also have "emeasure lborel C = emeasure (distr lborel lborel (\<lambda>(x,y). (x, -y))) A"
    (is "_ = emeasure ?M _") unfolding C_def 
    by (subst emeasure_distr) (simp_all add: case_prod_unfold)
  also have "?M = lborel" unfolding lborel_prod [symmetric]
    by (subst pair_measure_distr [symmetric]) (simp_all add: sigma_finite_lborel lborel_distr_uminus)
  also have "emeasure lborel D = emeasure (distr lborel lborel (\<lambda>(x,y). (-x, -y))) A"
    (is "_ = emeasure ?M _") unfolding D_def 
    by (subst emeasure_distr) (simp_all add: case_prod_unfold)
  also have "?M = lborel" unfolding lborel_prod [symmetric]
    by (subst pair_measure_distr [symmetric]) (simp_all add: sigma_finite_lborel lborel_distr_uminus)
  finally have "emeasure lborel (buffon_set l d) = 
                  of_nat (Suc (Suc (Suc (Suc 0)))) * emeasure lborel A"
    unfolding of_nat_Suc ring_distribs by simp
  also have "of_nat (Suc (Suc (Suc (Suc 0)))) = (4 :: ennreal)" by simp
  finally show ?thesis unfolding A_def .
qed 

text \<open>
  It only remains now to compute the measure of @{const buffon_set'}. We first reduce this
  problem to a relatively simple integral:
\<close>
lemma emeasure_buffon_set':
  "emeasure lborel (buffon_set' l d) = 
     ennreal (integral {0..pi} (\<lambda>x. min (d / 2) (sin x * l / 2)))"
  (is "emeasure lborel ?A = _")
proof -  
  have "emeasure lborel ?A = nn_integral lborel (\<lambda>x. indicator ?A x)"
    by (intro nn_integral_indicator [symmetric]) simp_all
  also have "(lborel :: (real \<times> real) measure) = lborel \<Otimes>\<^sub>M lborel" 
    by (simp only: lborel_prod)
  also have "nn_integral \<dots> (indicator ?A) = (\<integral>\<^sup>+\<phi>. \<integral>\<^sup>+x. indicator ?A (x, \<phi>) \<partial>lborel \<partial>lborel)"
    by (subst lborel_pair.nn_integral_snd [symmetric]) (simp_all add: lborel_prod borel_prod)
  also have "\<dots> = (\<integral>\<^sup>+\<phi>. \<integral>\<^sup>+x. indicator {0..pi} \<phi> * indicator {max 0 (d/2 - sin \<phi> * l / 2) .. d/2} x \<partial>lborel \<partial>lborel)"
    using d l by (intro nn_integral_cong) (auto simp: indicator_def field_simps buffon_set'_def)
  also have "\<dots> = \<integral>\<^sup>+ \<phi>. indicator {0..pi} \<phi> * emeasure lborel {max 0 (d / 2 - sin \<phi> * l / 2)..d / 2} \<partial>lborel"
    by (subst nn_integral_cmult) simp_all
  also have "\<dots> = \<integral>\<^sup>+ \<phi>. ennreal (indicator {0..pi} \<phi> * min (d / 2) (sin \<phi> * l / 2)) \<partial>lborel"
    (is "_ = ?I") using d l by (intro nn_integral_cong) (auto simp: indicator_def sin_ge_zero max_def min_def)
  also have "integrable lborel (\<lambda>\<phi>. (d / 2) * indicator {0..pi} \<phi>)" by simp
  hence int: "integrable lborel (\<lambda>\<phi>. indicator {0..pi} \<phi> * min (d / 2) (sin \<phi> * l / 2))"
    by (rule Bochner_Integration.integrable_bound)
       (insert l d, auto intro!: AE_I2 simp: indicator_def min_def sin_ge_zero)
  hence "?I = set_lebesgue_integral lborel {0..pi} (\<lambda>\<phi>. min (d / 2) (sin \<phi> * l / 2))"
    by (subst nn_integral_eq_integral, assumption)
       (insert d l, auto intro!: AE_I2 simp: sin_ge_zero min_def indicator_def set_lebesgue_integral_def)
  also have "\<dots> = ennreal (integral {0..pi} (\<lambda>x. min (d / 2) (sin x * l / 2)))"
    (is "_ = ennreal ?I") using int by (subst set_borel_integral_eq_integral) (simp_all add: set_integrable_def)
  finally show ?thesis by (simp add: lborel_prod)
qed

  
text \<open>
  We now have to distinguish two cases: The first and easier one is that where the length 
  of the needle, $l$, is less than or equal to the strip width, $d$:
\<close>
context
  assumes l_le_d: "l \<le> d"
begin

lemma emeasure_buffon_set'_short: "emeasure lborel (buffon_set' l d) = ennreal l"
proof -
  have "emeasure lborel (buffon_set' l d) =
          ennreal (integral {0..pi} (\<lambda>x. min (d / 2) (sin x * l / 2)))" (is "_ = ennreal ?I")
    by (rule emeasure_buffon_set')
  also have *: "sin \<phi> * l \<le> d" if "\<phi> \<ge> 0" "\<phi> \<le> pi" for \<phi>
    using mult_mono[OF l_le_d sin_le_one _ sin_ge_zero] that d by (simp add: algebra_simps)
  have "?I = integral {0..pi} (\<lambda>x. (l / 2) * sin x)"
    using l d l_le_d  
    by (intro integral_cong) (auto dest: * simp: min_def sin_ge_zero)
  also have "\<dots> = l / 2 * integral {0..pi} sin" by simp
  also have "(sin has_integral (-cos pi - (- cos 0))) {0..pi}"
    by (intro fundamental_theorem_of_calculus)
       (auto intro!: derivative_eq_intros simp: has_field_derivative_iff_has_vector_derivative [symmetric])
  hence "integral {0..pi} sin = -cos pi - (-cos 0)"
    by (simp add: has_integral_iff)
  finally show ?thesis by (simp add: lborel_prod)
qed

lemma emeasure_buffon_set_short: "emeasure lborel (buffon_set l d) = 4 * ennreal l"
  by (simp add: emeasure_buffon_set_conv_buffon_set' emeasure_buffon_set'_short l_le_d)

theorem buffon_short: "emeasure (buffon l d) {True} = ennreal (2 * l / (d * pi))"
proof -
  have "emeasure (buffon l d) {True} = ennreal (4 * l) / ennreal (2 * d * pi)"
    using d l by (subst buffon_prob_aux) (simp add: emeasure_buffon_set_short ennreal_mult)
  also have "\<dots> = ennreal (4 * l / (2 * d * pi))"
    using d l by (subst divide_ennreal) simp_all
  also have "4 * l / (2 * d * pi) = 2 * l / (d * pi)" by simp
  finally show ?thesis .
qed

end


text \<open>
  The other case where the needle is at least as long as the strip width is more complicated:
\<close>
context
  assumes l_ge_d: "l \<ge> d"
begin

lemma emeasure_buffon_set'_long: 
  "emeasure lborel (buffon_set' l d) =
     ennreal (l * (1 - sqrt (1 - (d / l)\<^sup>2)) + arccos (d / l) * d)"
proof -
  define \<phi>' where "\<phi>' = arcsin (d / l)"
  have \<phi>'_nonneg: "\<phi>' \<ge> 0" unfolding \<phi>'_def using d l l_ge_d arcsin_le_mono[of 0 "d/l"] 
    by (simp add: \<phi>'_def)
  have \<phi>'_le: "\<phi>' \<le> pi / 2" unfolding \<phi>'_def using arcsin_bounded[of "d/l"] d l l_ge_d
    by (simp add: field_simps)
  have ge_phi': "sin \<phi> \<ge> d / l" if "\<phi> \<ge> \<phi>'" "\<phi> \<le> pi / 2" for \<phi>
    using arcsin_le_iff[of "d / l" "\<phi>"] d l_ge_d that \<phi>'_nonneg by (auto simp: \<phi>'_def field_simps)
  have le_phi': "sin \<phi> \<le> d / l" if "\<phi> \<le> \<phi>'" "\<phi> \<ge> 0" for \<phi>
    using le_arcsin_iff[of "d / l" "\<phi>"] d l_ge_d that \<phi>'_le by (auto simp: \<phi>'_def field_simps)
    
  let ?f = "(\<lambda>x. min (d / 2) (sin x * l / 2))"
  have "emeasure lborel (buffon_set' l d) = ennreal (integral {0..pi} ?f)" (is "_ = ennreal ?I")
    by (rule emeasure_buffon_set')
  also have "?I = integral {0..pi/2} ?f + integral {pi/2..pi} ?f"
    by (rule integral_combine [symmetric]) (auto intro!: integrable_continuous_real continuous_intros)
  also have "integral {pi/2..pi} ?f = integral {-pi/2..0} (?f \<circ> (\<lambda>\<phi>. \<phi> + pi))"
    by (subst integral_shift) (auto intro!: continuous_intros)
  also have "\<dots> = integral {-(pi/2)..-0} (\<lambda>x. min (d / 2) (sin (-x) * l / 2))" by (simp add: o_def)
  also have "\<dots> = integral {0..pi/2} ?f" (is "_ = ?I") by (subst integral_reflect_real) simp_all
  also have "\<dots> + \<dots> = 2 * \<dots>" by simp
  also have "?I = integral {0..\<phi>'} ?f + integral {\<phi>'..pi/2} ?f"
    using l d l_ge_d \<phi>'_nonneg \<phi>'_le
    by (intro integral_combine [symmetric]) (auto intro!: integrable_continuous_real continuous_intros)
  also have "integral {0..\<phi>'} ?f = integral {0..\<phi>'} (\<lambda>x. l / 2 * sin x)"
    using l by (intro integral_cong) (auto simp: min_def field_simps dest: le_phi')
  also have "((\<lambda>x. l / 2 * sin x) has_integral (- (l / 2 * cos \<phi>') - (- (l / 2 * cos 0)))) {0..\<phi>'}"
    using \<phi>'_nonneg
    by (intro fundamental_theorem_of_calculus)
       (auto simp: has_field_derivative_iff_has_vector_derivative [symmetric] intro!: derivative_eq_intros)
  hence "integral {0..\<phi>'} (\<lambda>x. l / 2 * sin x) = (1 - cos \<phi>') * l / 2"
    by (simp add: has_integral_iff algebra_simps)
  also have "integral {\<phi>'..pi/2} ?f = integral {\<phi>'..pi/2} (\<lambda>_. d / 2)"
    using l by (intro integral_cong) (auto simp: min_def field_simps dest: ge_phi')
  also have "\<dots> = arccos (d / l) * d / 2" using \<phi>'_le d l l_ge_d 
    by (subst arccos_arcsin_eq) (auto simp: field_simps \<phi>'_def)
  also have "cos \<phi>' = sqrt (1 - (d / l)^2)"
    unfolding \<phi>'_def by (rule cos_arcsin) (insert d l l_ge_d, auto simp: field_simps)
  also have "2 * ((1 - sqrt (1 - (d / l)\<^sup>2)) * l / 2 + arccos (d / l) * d / 2) = 
               l * (1 - sqrt (1 - (d / l)\<^sup>2)) + arccos (d / l) * d"
    using d l by (simp add: field_simps)
  finally show ?thesis .
qed

lemma emeasure_buffon_set_long: "emeasure lborel (buffon_set l d) = 
        4 * ennreal (l * (1 - sqrt (1 - (d / l)\<^sup>2)) + arccos (d / l) * d)"
  by (simp add: emeasure_buffon_set_conv_buffon_set' emeasure_buffon_set'_long l_ge_d)

theorem buffon_long: 
  "emeasure (buffon l d) {True} = 
     ennreal (2 / pi * ((l / d) - sqrt ((l / d)\<^sup>2 - 1) + arccos (d / l)))"
proof -
  have *: "l * sqrt ((l\<^sup>2 - d\<^sup>2) / l\<^sup>2) + 0 \<le> l + d * arccos (d / l)"
    using d l_ge_d by (intro add_mono mult_nonneg_nonneg arccos_lbound) (auto simp: field_simps)
  have "emeasure (buffon l d) {True} = 
          ennreal (4 * (l - l * sqrt (1 - (d / l)\<^sup>2) + arccos (d / l) * d)) / ennreal (2 * d * pi)"
    using d l l_ge_d * unfolding buffon_prob_aux emeasure_buffon_set_long ennreal_numeral [symmetric]
    by (subst ennreal_mult [symmetric])
       (auto intro!: add_nonneg_nonneg mult_nonneg_nonneg simp: field_simps)
  also have "\<dots> = ennreal ((4 * (l - l * sqrt (1 - (d / l)\<^sup>2) + arccos (d / l) * d)) / (2 * d * pi))"
    using d l * by (subst divide_ennreal) (auto simp: field_simps)
  also have "(4 * (l - l * sqrt (1 - (d / l)\<^sup>2) + arccos (d / l) * d)) / (2 * d * pi) =
               2 / pi * (l / d - l / d * sqrt ((d / l)^2 * ((l / d)^2 - 1)) + arccos (d / l))"
    using d l by (simp add: field_simps)
  also have "l / d * sqrt ((d / l)^2 * ((l / d)^2 - 1)) = sqrt ((l / d) ^ 2 - 1)"
    using d l l_ge_d unfolding real_sqrt_mult real_sqrt_abs by simp
  finally show ?thesis .
qed

end
end

end
