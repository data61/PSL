(* License: LGPL *)
(* Author: Julian Parsert *)


theory PMF_Composition
  imports
    "HOL-Probability.Probability"
begin


section \<open> Composition of Probability Mass functions \<close>

definition mix_pmf :: "real \<Rightarrow> 'a pmf \<Rightarrow> 'a pmf \<Rightarrow> 'a pmf" where
  "mix_pmf \<alpha> p q = (bernoulli_pmf \<alpha>)\<bind> (\<lambda>X. if X then p else q)"

lemma pmf_mix: "a \<in> {0..1} \<Longrightarrow> pmf (mix_pmf a p q) x = a * pmf p x + (1 - a) * pmf q x"
  by (simp add: mix_pmf_def pmf_bind)

lemma pmf_mix_deeper: "a \<in> {0..1} \<Longrightarrow> pmf (mix_pmf a p q) x = a * pmf p x + pmf q x - a * pmf q x"
  by (simp add: left_diff_distrib' pmf_mix)

lemma bernoulli_pmf_0 [simp]: "bernoulli_pmf 0 = return_pmf False"
  by (intro pmf_eqI) (auto simp: bernoulli_pmf.rep_eq)

lemma bernoulli_pmf_1 [simp]: "bernoulli_pmf 1 = return_pmf True"
  by (intro pmf_eqI) (auto simp: bernoulli_pmf.rep_eq)

lemma pmf_mix_0 [simp]: "mix_pmf 0 p q = q"
  by (simp add: mix_pmf_def bind_return_pmf)

lemma pmf_mix_1 [simp]: "mix_pmf 1 p q = p"
  by (simp add: mix_pmf_def bind_return_pmf)

lemma set_pmf_mix: "a \<in> {0<..<1} \<Longrightarrow> set_pmf (mix_pmf a p q) = set_pmf p \<union> set_pmf q"
  by (auto simp add: mix_pmf_def split: if_splits)

lemma set_pmf_mix_eq: "a \<in> {0..1} \<Longrightarrow> mix_pmf a p p = p"
  by (simp add: mix_pmf_def)

lemma pmf_equiv_intro[intro]:
  assumes "\<And>e. e \<in> set_pmf p \<Longrightarrow> pmf p e = pmf q e"
  assumes "\<And>e. e \<in> set_pmf q \<Longrightarrow> pmf q e = pmf p e"
  shows "p = q"
  by (metis assms(2) less_irrefl pmf_neq_exists_less pmf_not_neg set_pmf_iff)

lemma pmf_equiv_intro1[intro]:
  assumes "\<And>e. e \<in> set_pmf p \<Longrightarrow> pmf p e = pmf q e"
  shows "p = q"
  by (standard, auto simp: assms, metis assms set_pmf_iff assms 
      linorder_not_le order_refl pmf_neq_exists_less pmf_not_neg set_pmf_iff)

lemma pmf_inverse_switch_eqals:  
  assumes "a \<in> {0..1}"
  shows "mix_pmf a p q = mix_pmf (1-a) q p"
proof -
  have fst: "\<forall>x \<in> set_pmf p. pmf (mix_pmf a p q) x = pmf (mix_pmf (1-a) q p) x"
  proof
    fix x 
    assume "x \<in> set_pmf p"
    have "pmf (mix_pmf a p q) x = a * pmf p x + (1 - a) * pmf q x"
      using pmf_mix[of a p q x] assms by blast
    also have "... = a * pmf p x +  pmf q x - a * pmf q x"
      by (simp add: left_diff_distrib)
    from pmf_mix[of "1-a" q p x] assms 
    have "pmf (mix_pmf (1 - a) q p) x = (1 - a) * pmf q x + (1 - (1 - a)) * pmf p x"
      by auto
    then show "pmf (mix_pmf a p q) x = pmf (mix_pmf (1 - a) q p) x"
      using calculation by auto
  qed
  have "\<forall>x \<in> set_pmf q. pmf (mix_pmf a p q) x =  pmf (mix_pmf (1-a) q p) x"
  proof
    fix x 
    assume "x \<in> set_pmf q"
    have "pmf (mix_pmf a p q) x = a * pmf p x + (1 - a) * pmf q x"
      using pmf_mix[of a p q x] assms by blast
    also have "... = a * pmf p x +  pmf q x - a * pmf q x"
      by (simp add: left_diff_distrib)
    from pmf_mix[of "1-a" q p x] assms
    show "pmf (mix_pmf a p q) x = pmf (mix_pmf (1 - a) q p) x"
      using calculation by auto
  qed
  then have "\<forall>x \<in> set_pmf (mix_pmf a p q). pmf (mix_pmf a p q) x =  pmf (mix_pmf (1-a) q p) x"
    by (metis (no_types) fst add_0_left assms mult_eq_0_iff pmf_mix set_pmf_iff)
  thus ?thesis
    by (simp add: pmf_equiv_intro1)
qed

lemma mix_pmf_comp_left_div:
  assumes "\<alpha> \<in> {0..(1::real)}"
    and "\<beta> \<in> {0..(1::real)}"
  assumes "\<alpha> > \<beta>"
  shows "pmf (mix_pmf (\<beta>/\<alpha>) (mix_pmf \<alpha> p q) q) e = \<beta> * pmf p e + pmf q e - \<beta> * pmf q e"
proof-
  let ?l = "(mix_pmf (\<beta>/\<alpha>) (mix_pmf \<alpha> p q) q)"
  have fst: "pmf ?l e = (\<beta>/\<alpha>) * pmf (mix_pmf \<alpha> p q) e + (1-\<beta>/\<alpha>) * pmf q e"
    by (meson assms(1) assms(2) assms(3) atLeastAtMost_iff less_divide_eq_1 
        less_eq_real_def not_less pmf_mix zero_le_divide_iff)
  then have "pmf (mix_pmf \<alpha> p q) e = \<alpha> * pmf p e + (1 - \<alpha>) * pmf q e"
    using pmf_mix[of "\<alpha>" p q] assms(2) assms(3) assms(1) by blast
  have "pmf ?l e = (\<beta>/\<alpha>) * (\<alpha> * pmf p e + (1 - \<alpha>) * pmf q e) + (1-\<beta>/\<alpha>) * pmf q e"
    using fst assms(1) pmf_mix by fastforce
  then have "pmf ?l e = ((\<beta>/\<alpha>) *\<alpha> * pmf p e + (\<beta>/\<alpha>) *(1 - \<alpha>) * pmf q e) + (1-\<beta>/\<alpha>) * pmf q e"
    using fst assms(1) by (metis  mult.assoc  ring_class.ring_distribs(1))
  then have *: "pmf ?l e = (\<beta> * pmf p e + (\<beta>/\<alpha>) *(1 - \<alpha>) * pmf q e) + (1-\<beta>/\<alpha>) * pmf q e"
    using fst assms(1) assms(2) assms(3) by auto
  then have "pmf ?l e = (\<beta> * pmf p e + ((\<beta>/\<alpha>) - (\<beta>/\<alpha>)*\<alpha>) * pmf q e) + (1-\<beta>/\<alpha>) * pmf q e"
    using fst assms(1) assms(2) assms(3) by (simp add: * diff_divide_distrib right_diff_distrib')
  then have "pmf ?l e = (\<beta> * pmf p e + ((\<beta>/\<alpha>) - \<beta>) * pmf q e) + (1-\<beta>/\<alpha>) * pmf q e"
    using fst assms(1) assms(2) assms(3) by auto
  then have "pmf ?l e = (\<beta> * pmf p e + (\<beta>/\<alpha>) * pmf q e - \<beta> * pmf q e) + 1* pmf q e-\<beta>/\<alpha>* pmf q e"
    by (simp add: left_diff_distrib)
  thus ?thesis
    by linarith
qed

lemma mix_pmf_comp_with_dif_equiv:
  assumes "\<alpha> \<in> {0..(1::real)}"
    and "\<beta> \<in> {0..(1::real)}"
  assumes "\<alpha> > \<beta>"
  shows "mix_pmf (\<beta>/\<alpha>) (mix_pmf \<alpha> p q) q = mix_pmf \<beta> p q" (is "?l = ?r")
proof (rule pmf_equiv_intro1[symmetric])
  fix e
  assume a: "e \<in> set_pmf ?r" 
  have "e \<in> set_pmf ?l"
    using a pmf_mix_deeper by (metis assms(1) assms(2) assms(3) mix_pmf_comp_left_div pmf_eq_0_set_pmf)
  then have "pmf ?l e = \<beta> * pmf p e - \<beta> * pmf q e + pmf q e"
    using pmf_mix_deeper[of "\<beta>/\<alpha>" p q e] mix_pmf_comp_left_div[of \<alpha> \<beta> p q e] assms by auto  
  then show "pmf (mix_pmf \<beta> p q) e = pmf (mix_pmf (\<beta> / \<alpha>) (mix_pmf \<alpha> p q) q) e"
    by (metis (full_types) assms(1) assms(2) assms(3) mix_pmf_comp_left_div pmf_mix_deeper)
qed

lemma product_mix_pmf_prob_distrib:
  assumes "a \<in> {0..1}"
    and "b \<in> {0..1}"
  shows "mix_pmf a (mix_pmf b p q) q = mix_pmf (a*b) p q"
proof -
  define \<gamma> where g: "\<gamma> = (a * b)"
  define l where l: "l = (mix_pmf b p q)"
  define r where r: "r =  mix_pmf (a*b) p q"
  have y: "\<gamma> \<in> {0..1}"
    using assms(2) mult_le_one assms g by auto
  have alt_: "\<forall>e \<in> set_pmf l. pmf r e = \<gamma> * pmf p e + pmf q e - \<gamma> * pmf q e"
  proof
    fix e 
    have "pmf r e = \<gamma> * pmf p e + (1-\<gamma>) * pmf q e"
      using \<open>\<gamma> \<in> {0..1}\<close> g pmf_mix r by fastforce
    moreover have "... = \<gamma> * pmf p e + 1 * pmf q e - \<gamma> * pmf q e"
      by (simp add: linordered_field_class.sign_simps(37))
    moreover have "... = pmf (mix_pmf \<gamma> p q) e"
      using calculation g r by auto
    moreover have "... = \<gamma>  * pmf p e + pmf q e - \<gamma> * pmf q e"
      using calculation by auto
    ultimately show "pmf r e = \<gamma> * pmf p e + pmf q e - \<gamma> * pmf q e" 
      by auto
  qed
  have "\<forall>e \<in> set_pmf r. pmf l e = b * pmf p e + pmf q e - b * pmf q e"
    using allI pmf_mix_deeper assms(2) l by fastforce
  have "mix_pmf a (mix_pmf b p q) q = mix_pmf (a * b) p q" 
  proof (rule ccontr)
    assume neg:"\<not>mix_pmf a (mix_pmf b p q) q = mix_pmf (a * b) p q"
    then have b: "b \<noteq> 0"
      by (metis (no_types) assms(1) mult_cancel_right2 pmf_mix_0 set_pmf_mix_eq)
    have f3: "b - (a * b) > 0 \<longrightarrow> mix_pmf a (mix_pmf b p q) q = mix_pmf (a * b) p q"  
      by (metis assms(2) diff_le_0_iff_le g mix_pmf_comp_with_dif_equiv mult_eq_0_iff 
          nonzero_mult_div_cancel_right not_le order_refl y)
    thus False
      using b neg assms(1) assms(2) by auto
  qed
  then show ?thesis by auto
qed

lemma mix_pmf_subset_of_original:
  assumes "a \<in> {0..1}"
  shows "(set_pmf (mix_pmf a p q)) \<subseteq> set_pmf p \<union> set_pmf q"
proof -
  have "a \<in> {0<..<1} \<Longrightarrow> ?thesis"
    by (simp add: set_pmf_mix)
  moreover have "a = 1 \<Longrightarrow> ?thesis"
    by simp
  moreover have "a = 0 \<Longrightarrow> ?thesis"
    by simp
  ultimately show ?thesis
    using assms less_eq_real_def by auto
qed

lemma mix_pmf_preserves_finite_support:
  assumes "a \<in> {0..1}"
  assumes "finite (set_pmf p)"
    and "finite (set_pmf q)"
  shows "finite (set_pmf (mix_pmf a p q))"
  by (meson assms(1) assms(2) assms(3) finite_Un finite_subset mix_pmf_subset_of_original)

lemma ex_certain_iff_singleton_support:
  shows "(\<exists>x. pmf p x = 1) \<longleftrightarrow> card (set_pmf p) = 1"
proof (rule iffI, goal_cases)
  case 1
  show ?case 
  proof (rule ccontr)
    assume neg: "\<not> card (set_pmf p) = 1"
    then have "card (set_pmf p) \<noteq> 1"
      by blast
    have "finite (set_pmf p)"  
      by (metis "1" empty_iff finite.emptyI finite_insert insert_iff 
          not_le pmf_le_1 pmf_neq_exists_less pmf_nonneg set_pmf_iff set_return_pmf)
    then have sumeq_1: "(\<Sum>i \<in> set_pmf p. pmf p i) = 1"
      using sum_pmf_eq_1[of "set_pmf p" p] by auto
    have set_pmf_nemtpy: "set_pmf p \<noteq> {}"
      by (simp add: set_pmf_not_empty)
    then have g1: "card (set_pmf p) > 1"
      by (metis card_0_eq less_one nat_neq_iff neg sum.infinite sumeq_1 zero_neq_one)
    have "card (set_pmf p) > 1 \<longrightarrow> (\<Sum>i \<in> set_pmf p. pmf p i) > 1"
    proof
      assume "card (set_pmf p) > 1"     
      have "\<exists>x y. pmf p x = 1 \<and> y \<noteq> x \<and> y \<in> set_pmf p"
        using  set_pmf_nemtpy is_singletonI' is_singleton_altdef
        by (metis "1" neg)
      then show "(\<Sum>i \<in> set_pmf p. pmf p i) > 1"
        by (metis AE_measure_pmf_iff UNIV_I empty_iff insert_iff
            measure_pmf.prob_eq_1 pmf.rep_eq sets_measure_pmf)
    qed
    then have "card (set_pmf p) < 1"
      using sumeq_1 neg by linarith
    then show False
      using g1 by linarith
  qed
qed (metis card_1_singletonE less_numeral_extra(1) pmf.rep_eq subset_eq
    sum_pmf_eq_1[of "set_pmf p" p]  card_gt_0_iff[of "set_pmf p"] 
    measure_measure_pmf_finite[of "set_pmf p"])


text \<open> We thank Manuel Eberl for suggesting the following two lemmas. \<close>

lemma mix_pmf_partition:
  fixes p :: "'a pmf"
  assumes "y \<in> set_pmf p" "set_pmf p - {y} \<noteq> {}"
  obtains a q where "a \<in> {0<..<1}" "set_pmf q = set_pmf p - {y}" 
    "p = mix_pmf a q (return_pmf y)"
proof -
  from assms obtain x where x: "x \<in> set_pmf p - {y}" by auto
  define a where "a = 1 - pmf p y"
  have a_n1:"a \<noteq> 1"
    by (simp add: a_def assms(1) pmf_eq_0_set_pmf)
  have "pmf p y \<noteq> 1"
    using ex_certain_iff_singleton_support by (metis (full_types) 
        Diff_cancel assms(1) assms(2) card_1_singletonE singletonD)
  hence y: "pmf p y < 1" using pmf_le_1[of p y] unfolding a_def by linarith
  hence a: "a > 0" by (simp add: a_def)
  define q where "q = embed_pmf (\<lambda>z. if z = y then 0 else pmf p z / a)"
  have q: "pmf q z = (if z = y then 0 else pmf p z / a)" for z
    unfolding q_def
  proof (rule pmf_embed_pmf)
    have "1 = (\<integral>\<^sup>+ x. ennreal (pmf p x) \<partial>count_space UNIV)"
      by (rule nn_integral_pmf_eq_1 [symmetric])
    also have "\<dots> = (\<integral>\<^sup>+ x. ennreal (pmf p x) * indicator {y} x + 
                      ennreal (pmf p x) * indicator (-{y}) x \<partial>count_space UNIV)"
      by (intro nn_integral_cong) (auto simp: indicator_def)
    also have "\<dots> = (\<integral>\<^sup>+ x. ennreal (pmf p x) * indicator {y} x \<partial>count_space UNIV) + 
                    (\<integral>\<^sup>+ x. ennreal (pmf p x) * indicator (-{y}) x \<partial>count_space UNIV)"
      by (subst nn_integral_add) auto
    also have "(\<integral>\<^sup>+ x. ennreal (pmf p x) * indicator {y} x \<partial>count_space UNIV) = pmf p y"
      by (subst nn_integral_indicator_finite) auto
    also have "ennreal (pmf p y) + (\<integral>\<^sup>+ x. ennreal (pmf p x) * indicator (-{y}) x \<partial>count_space UNIV)
                 - ennreal (pmf p y) = (\<integral>\<^sup>+ x. ennreal (pmf p x) * indicator (-{y}) x \<partial>count_space UNIV)"
      by simp
    also have "1 - ennreal (pmf p y) = ennreal (1 - pmf p y)"
      by (subst ennreal_1 [symmetric], subst ennreal_minus) auto
    finally have eq: "(\<integral>\<^sup>+x\<in>-{y}. ennreal (pmf p x)\<partial>count_space UNIV) = 1 - pmf p y" ..
    have "(\<integral>\<^sup>+ x. ennreal (if x = y then 0 else pmf p x / a) \<partial>count_space UNIV) =
            (\<integral>\<^sup>+ x. inverse a * (ennreal (pmf p x) * indicator (-{y}) x) \<partial>count_space UNIV)"
      using a by (intro nn_integral_cong) (auto simp: divide_simps ennreal_mult' [symmetric])
    also have "\<dots> = inverse a * (\<integral>\<^sup>+ x\<in>-{y}. ennreal (pmf p x) \<partial>count_space UNIV)"
      using a by (subst nn_integral_cmult [symmetric]) (auto simp: ennreal_mult')
    also note eq
    also have "ennreal (inverse a) * ennreal (1 - pmf p y) = ennreal ((1 - pmf p y) / a)"
      using a by (subst ennreal_mult' [symmetric]) (auto simp: field_simps)
    also have "(1 - pmf p y) / a = 1" using y by (simp add: a_def)
    finally show "(\<integral>\<^sup>+ x. ennreal (if x = y then 0 else pmf p x / a) \<partial>count_space UNIV) = 1"
      by simp
  qed (insert a, auto)
  have "mix_pmf (1 - pmf p y) q (return_pmf y) = p"
    using y by (intro pmf_eqI) (auto simp: q pmf_mix pmf_le_1 a_def)
  moreover have "set_pmf q = set_pmf p - {y}"
    using y by (auto simp: q set_pmf_eq a_def)
  ultimately show ?thesis using that[of "1 - pmf p y" q] y assms by (auto simp: set_pmf_eq)
qed

lemma pmf_mix_induct [consumes 2, case_names degenerate mix]:
  assumes "finite A" "set_pmf p \<subseteq> A"
  assumes degenerate: "\<And>x. x \<in> A \<Longrightarrow> P (return_pmf x)"
  assumes mix:        "\<And>p a y. set_pmf p \<subseteq> A \<Longrightarrow> a \<in> {0<..<1} \<Longrightarrow> y \<in> A \<Longrightarrow> 
                         P p \<Longrightarrow> P (mix_pmf a p (return_pmf y))"
  shows "P p"
proof -
  have "finite (set_pmf p)" "set_pmf p \<noteq> {}" "set_pmf p \<subseteq> A"
    using assms(1,2) by (auto simp: set_pmf_not_empty dest: finite_subset)
  thus ?thesis
  proof (induction "set_pmf p" arbitrary: p rule: finite_ne_induct)
    case (singleton x p)
    hence "p = return_pmf x" using set_pmf_subset_singleton[of p x] by auto
    thus ?case using singleton by (auto intro: degenerate)
  next
    case (insert x B p)
    from insert.hyps have "x \<in> set_pmf p" "set_pmf p - {x} \<noteq> {}" by auto
    from mix_pmf_partition[OF this] obtain a q
      where decomp: "a \<in> {0<..<1}" "set_pmf q = set_pmf p - {x}" 
        "p = mix_pmf a q (return_pmf x)" by blast
    have "P (mix_pmf a q (return_pmf x))"
      using insert.prems decomp(1) insert.hyps
      by (intro mix insert) (auto simp: decomp(2))
    with decomp(3) show ?case by simp
  qed
qed

lemma pmf_mix_induct' [consumes 2, case_names degenerate mix]:
  assumes "finite A" "set_pmf p \<subseteq> A"
  assumes degenerate: "\<And>x. x \<in> A \<Longrightarrow> P (return_pmf x)"
  assumes mix:        "\<And>p q a. set_pmf p \<subseteq> A \<Longrightarrow> set_pmf q \<subseteq> A \<Longrightarrow> a \<in> {0<..<1} \<Longrightarrow> 
                         P p \<Longrightarrow> P q \<Longrightarrow> P (mix_pmf a p q)"
  shows "P p"
  using assms by (induct p rule: pmf_mix_induct)(auto)+

lemma finite_sum_distribute_mix_pmf:
  assumes "finite (set_pmf (mix_pmf a p q))"
  assumes "finite (set_pmf p)"
  assumes "finite (set_pmf q)"
  shows "(\<Sum>i \<in> set_pmf (mix_pmf a p q). pmf (mix_pmf a p q) i) = (\<Sum>i\<in>set_pmf p.  a * pmf p i) + (\<Sum>i\<in>set_pmf q. (1-a) * pmf q i)"
proof -
  have fst: "(\<Sum>i \<in> set_pmf (mix_pmf a p q). pmf (mix_pmf a p q) i) = 1"
    using sum_pmf_eq_1 assms by auto
  have "(\<Sum>i\<in>set_pmf p.  a * pmf p i) = a * (\<Sum>i\<in>set_pmf p. pmf p i)"
    by (simp add: sum_distrib_left)
  also have "... = a * 1"
    using assms sum_pmf_eq_1 by (simp add: sum_pmf_eq_1)
  then show ?thesis 
    by (metis fst add.assoc add_diff_cancel_left' add_uminus_conv_diff assms(3) 
        mult.right_neutral order_refl sum_distrib_left sum_pmf_eq_1)
qed

lemma distribute_alpha_over_sum:
  shows "(\<Sum>i\<in>set_pmf T. a * pmf p i * f i) = a * (\<Sum>i\<in>set_pmf T. pmf p i * f i)"
  by (metis (mono_tags, lifting) semiring_normalization_rules(18) sum.cong sum_distrib_left)

lemma sum_over_subset_pmf_support:
  assumes "finite T"
  assumes "set_pmf p \<subseteq> T"
  shows "(\<Sum>i\<in>T. a * pmf p i * f i) = (\<Sum>i\<in>set_pmf p. a * pmf p i * f i)"
proof -
  consider (eq) "set_pmf p = T" | (sub) "set_pmf p \<subset> T"
    using assms by blast
  then show ?thesis
  proof (cases)
  next
    case sub
    define A where "A = T - (set_pmf p)"
    have "finite (set_pmf p)" 
      using assms(1) assms(2) finite_subset by auto
    moreover have "finite A"
      using A_def assms(1) by blast
    moreover have "A \<inter> set_pmf p = {}"
      using A_def assms(1) by blast
    ultimately have *: "(\<Sum>i\<in>T. a * pmf p i * f i) = (\<Sum>i\<in>set_pmf p. a * pmf p i * f i) + (\<Sum>i\<in>A. a * pmf p i * f i)"
      using sum.union_disjoint by (metis (no_types) A_def Un_Diff_cancel2 
          Un_absorb2 assms(2) inf.commute inf_sup_aci(5) sum.union_disjoint)
    have "\<forall>e \<in> A. pmf p e = 0"
      by (simp add: A_def pmf_eq_0_set_pmf)
    hence "(\<Sum>i\<in>A. a * pmf p i * f i) = 0"
      by simp
    then show ?thesis
      by (simp add: "*")
  qed (auto)
qed

lemma expected_value_mix_pmf_distrib:
  assumes "finite (set_pmf p)"
    and "finite (set_pmf q)"
  assumes "a \<in> {0<..<1}"
  shows "measure_pmf.expectation (mix_pmf a p q) f = a * measure_pmf.expectation p f + (1-a) * measure_pmf.expectation q f"
proof -
  have fn: "finite (set_pmf (mix_pmf a p q))"
    using mix_pmf_preserves_finite_support assms less_eq_real_def  by auto
  have subsets: "set_pmf p \<subseteq> set_pmf (mix_pmf a p q)" "set_pmf q \<subseteq> set_pmf (mix_pmf a p q)" 
    using assms assms set_pmf_mix by(fastforce)+
  have *: "(\<Sum>i \<in> set_pmf (mix_pmf a p q). a * pmf p i * f i) = a * (\<Sum>i \<in> set_pmf (mix_pmf a p q). pmf p i * f i)"
    by (metis (mono_tags, lifting) mult.assoc sum.cong sum_distrib_left)
  have **: "(\<Sum>i \<in> set_pmf (mix_pmf a p q). (1-a) * pmf q i * f i) = (1-a) * (\<Sum>i \<in> set_pmf (mix_pmf a p q). pmf q i * f i)"
    using distribute_alpha_over_sum[of "(1 - a)" q f "(mix_pmf a p q)"] by auto
  have ***: "measure_pmf.expectation (mix_pmf a p q) f = (\<Sum>i \<in> set_pmf (mix_pmf a p q). pmf (mix_pmf a p q) i * f i)"
    by (metis fn pmf_integral_code_unfold pmf_integral_pmf_set_integral
        pmf_set_integral_code_alt_finite)
  also have g: "... = (\<Sum>i \<in> set_pmf (mix_pmf a p q). (a * pmf p i + (1-a) * pmf q i) * f i)"
    using pmf_mix[of a p q] assms(3) by auto
  also have ****: "... =  (\<Sum>i \<in> set_pmf (mix_pmf a p q). a * pmf p i * f i + (1-a) * pmf q i * f i)"
    by (simp add: mult.commute ring_class.ring_distribs(1))
  also have f: "... = (\<Sum>i \<in> set_pmf (mix_pmf a p q). a * pmf p i * f i) + (\<Sum>i \<in> set_pmf (mix_pmf a p q). (1-a) * pmf q i * f i)"
    by (simp add: sum.distrib)
  also have "... = a * (\<Sum>i \<in> set_pmf (mix_pmf a p q). pmf p i * f i) + (1-a) * (\<Sum>i \<in> set_pmf (mix_pmf a p q). pmf q i * f i)"
    using * ** by simp
  also have h: "... =  a * (\<Sum>i \<in> set_pmf p. pmf p i * f i) + (1-a) * (\<Sum>i \<in> set_pmf q. pmf q i * f i)"
  proof -
    have "(\<Sum>i \<in> set_pmf (mix_pmf a p q). pmf p i * f i) = (\<Sum>i \<in> set_pmf p. pmf p i * f i)"
      using subsets sum_over_subset_pmf_support[of "(mix_pmf a p q)" p 1 f] fn by auto
    moreover have "(\<Sum>i \<in> set_pmf (mix_pmf a p q). pmf q i * f i) = (\<Sum>i \<in> set_pmf q. pmf q i * f i)"
      using subsets sum_over_subset_pmf_support[of "(mix_pmf a p q)" q 1 f] fn by auto
    ultimately show ?thesis
      by (simp)
  qed
  finally show ?thesis 
  proof -
    have "(\<Sum>i\<in>set_pmf q. pmf q i * f i) = measure_pmf.expectation q f"
      by (metis (full_types) assms(2) pmf_integral_code_unfold pmf_integral_pmf_set_integral pmf_set_integral_code_alt_finite)
    moreover have "(\<Sum>i\<in>set_pmf p. pmf p i * f i) = measure_pmf.expectation p f"
      by (metis (full_types) assms(1) pmf_integral_code_unfold pmf_integral_pmf_set_integral pmf_set_integral_code_alt_finite)
    ultimately show ?thesis
      by (simp add: "*" "**" "***" "****" f g h)
  qed
qed

lemma expected_value_mix_pmf:
  assumes "finite (set_pmf p)"
    and "finite (set_pmf q)"
  assumes "a \<in> {0..1}"
  shows "measure_pmf.expectation (mix_pmf a p q) f = a * measure_pmf.expectation p f + (1-a) * measure_pmf.expectation q f"
proof -
  consider (0) "a = 0" | (b) "a \<in> {0<..<1}" | (1) "a = 1"
    using assms(3) less_eq_real_def by auto
  then show ?thesis
  proof (cases)
    case 0
    have "(mix_pmf a p q) = q"
      using 0 pmf_mix_0 by blast
    have "measure_pmf.expectation q f = (1-a) * measure_pmf.expectation q f"
      by (simp add: 0)
    show ?thesis
      using 0 by auto
  next
    case b
    show ?thesis
      using assms(1) assms(2) b expected_value_mix_pmf_distrib by blast
  next
    case 1
    have "(mix_pmf a p q) = p"
      using 1 pmf_mix_0 by simp
    then show ?thesis
      by (simp add: "1")
  qed
qed

end
