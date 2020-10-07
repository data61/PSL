(* Author: Alexander Maletzky *)

section \<open>Cone Decompositions\<close>

theory Cone_Decomposition
  imports Groebner_Bases.Groebner_PM Monomial_Module Hilbert_Function
begin

subsection \<open>More Properties of Reduced Gr\"obner Bases\<close>

context pm_powerprod
begin

lemmas reduced_GB_subset_monic_Polys =
  punit.reduced_GB_subset_monic_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]
lemmas reduced_GB_is_monomial_set_Polys =
  punit.reduced_GB_is_monomial_set_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]
lemmas is_red_reduced_GB_monomial_lt_GB_Polys =
  punit.is_red_reduced_GB_monomial_lt_GB_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]
lemmas reduced_GB_monomial_lt_reduced_GB_Polys =
  punit.reduced_GB_monomial_lt_reduced_GB_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]

end

subsection \<open>Quotient Ideals\<close>

definition quot_set :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a::semigroup_mult set" (infixl "\<div>" 55)
  where "quot_set A x = (*) x -` A"

lemma quot_set_iff: "a \<in> A \<div> x \<longleftrightarrow> x * a \<in> A"
  by (simp add: quot_set_def)

lemma quot_setI: "x * a \<in> A \<Longrightarrow> a \<in> A \<div> x"
  by (simp only: quot_set_iff)

lemma quot_setD: "a \<in> A \<div> x \<Longrightarrow> x * a \<in> A"
  by (simp only: quot_set_iff)

lemma quot_set_quot_set [simp]: "A \<div> x \<div> y = A \<div> x * y"
  by (rule set_eqI) (simp add: quot_set_iff mult.assoc)

lemma quot_set_one [simp]: "A \<div> (1::_::monoid_mult) = A"
  by (rule set_eqI) (simp add: quot_set_iff)

lemma ideal_quot_set_ideal [simp]: "ideal (ideal B \<div> x) = (ideal B) \<div> (x::_::comm_ring)"
proof
  show "ideal (ideal B \<div> x) \<subseteq> ideal B \<div> x"
  proof
    fix b
    assume "b \<in> ideal (ideal B \<div> x)"
    thus "b \<in> ideal B \<div> x"
    proof (induct b rule: ideal.span_induct')
      case base
      show ?case by (simp add: quot_set_iff ideal.span_zero)
    next
      case (step b q p)
      hence "x * b \<in> ideal B" and "x * p \<in> ideal B" by (simp_all add: quot_set_iff)
      hence "x * b + q * (x * p) \<in> ideal B"
        by (intro ideal.span_add ideal.span_scale[where c=q])
      thus ?case by (simp only: quot_set_iff algebra_simps)
    qed
  qed
qed (fact ideal.span_superset)

lemma quot_set_image_times: "inj ((*) x) \<Longrightarrow> ((*) x ` A) \<div> x = A"
  by (simp add: quot_set_def inj_vimage_image_eq)

subsection \<open>Direct Decompositions of Polynomial Rings\<close>

context pm_powerprod
begin

definition normal_form :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field)"
  where "normal_form F p = (SOME q. (punit.red (punit.reduced_GB F))\<^sup>*\<^sup>* p q \<and> \<not> punit.is_red (punit.reduced_GB F) q)"

text \<open>Of course, @{const normal_form} could be defined in a much more general context.\<close>

context
  fixes X :: "'x set"
  assumes fin_X: "finite X"
begin

context
  fixes F :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) set"
  assumes F_sub: "F \<subseteq> P[X]"
begin

lemma normal_form:
  shows "(punit.red (punit.reduced_GB F))\<^sup>*\<^sup>* p (normal_form F p)" (is ?thesis1)
    and "\<not> punit.is_red (punit.reduced_GB F) (normal_form F p)" (is ?thesis2)
proof -
  from fin_X F_sub have "finite (punit.reduced_GB F)" by (rule finite_reduced_GB_Polys)
  hence "wfP (punit.red (punit.reduced_GB F))\<inverse>\<inverse>" by (rule punit.red_wf_finite)
  then obtain q where "(punit.red (punit.reduced_GB F))\<^sup>*\<^sup>* p q"
    and "\<not> punit.is_red (punit.reduced_GB F) q" unfolding punit.is_red_def not_not
    by (rule relation.wf_imp_nf_ex)
  hence "(punit.red (punit.reduced_GB F))\<^sup>*\<^sup>* p q \<and> \<not> punit.is_red (punit.reduced_GB F) q" ..
  hence "?thesis1 \<and> ?thesis2" unfolding normal_form_def by (rule someI)
  thus ?thesis1 and ?thesis2 by simp_all
qed

lemma normal_form_unique:
  assumes "(punit.red (punit.reduced_GB F))\<^sup>*\<^sup>* p q" and "\<not> punit.is_red (punit.reduced_GB F) q"
  shows "normal_form F p = q"
proof (rule relation.ChurchRosser_unique_final)
  from fin_X F_sub have "punit.is_Groebner_basis (punit.reduced_GB F)" by (rule reduced_GB_is_GB_Polys)
  thus "relation.is_ChurchRosser (punit.red (punit.reduced_GB F))"
    by (simp only: punit.is_Groebner_basis_def)
next
  show "(punit.red (punit.reduced_GB F))\<^sup>*\<^sup>* p (normal_form F p)" by (rule normal_form)
next
  have "\<not> punit.is_red (punit.reduced_GB F) (normal_form F p)" by (rule normal_form)
  thus "relation.is_final (punit.red (punit.reduced_GB F)) (normal_form F p)"
    by (simp add: punit.is_red_def)
next
  from assms(2) show "relation.is_final (punit.red (punit.reduced_GB F)) q"
    by (simp add: punit.is_red_def)
qed fact

lemma normal_form_id_iff: "normal_form F p = p \<longleftrightarrow> (\<not> punit.is_red (punit.reduced_GB F) p)"
proof
  assume "normal_form F p = p"
  with normal_form(2)[of p] show "\<not> punit.is_red (punit.reduced_GB F) p" by simp
next
  assume "\<not> punit.is_red (punit.reduced_GB F) p"
  with rtranclp.rtrancl_refl show "normal_form F p = p" by (rule normal_form_unique)
qed

lemma normal_form_normal_form: "normal_form F (normal_form F p) = normal_form F p"
  by (simp add: normal_form_id_iff normal_form)

lemma normal_form_zero: "normal_form F 0 = 0"
  by (simp add: normal_form_id_iff punit.irred_0)

lemma normal_form_map_scale: "normal_form F (c \<cdot> p) = c \<cdot> (normal_form F p)"
  by (intro normal_form_unique punit.is_irred_map_scale normal_form)
    (simp add: punit.map_scale_eq_monom_mult punit.red_rtrancl_mult normal_form)

lemma normal_form_uminus: "normal_form F (- p) = - normal_form F p"
  by (intro normal_form_unique punit.red_rtrancl_uminus normal_form)
      (simp add: punit.is_red_uminus normal_form)

lemma normal_form_plus_normal_form:
  "normal_form F (normal_form F p + normal_form F q) = normal_form F p + normal_form F q"
  by (intro normal_form_unique rtranclp.rtrancl_refl punit.is_irred_plus normal_form)

lemma normal_form_minus_normal_form:
  "normal_form F (normal_form F p - normal_form F q) = normal_form F p - normal_form F q"
  by (intro normal_form_unique rtranclp.rtrancl_refl punit.is_irred_minus normal_form)

lemma normal_form_ideal_Polys: "normal_form (ideal F \<inter> P[X]) = normal_form F"
proof -
  let ?F = "ideal F \<inter> P[X]"
  from fin_X have eq: "punit.reduced_GB ?F = punit.reduced_GB F"
  proof (rule reduced_GB_unique_Polys)
    from fin_X F_sub show "punit.is_reduced_GB (punit.reduced_GB F)"
      by (rule reduced_GB_is_reduced_GB_Polys)
  next
    from fin_X F_sub have "ideal (punit.reduced_GB F) = ideal F" by (rule reduced_GB_ideal_Polys)
    also have "\<dots> = ideal (ideal F \<inter> P[X])"
    proof (intro subset_antisym ideal.span_subset_spanI)
      from ideal.span_superset[of F] F_sub have "F \<subseteq> ideal F \<inter> P[X]" by simp
      thus "F \<subseteq> ideal (ideal F \<inter> P[X])" using ideal.span_superset by (rule subset_trans)
    qed blast
    finally show "ideal (punit.reduced_GB F) = ideal (ideal F \<inter> P[X])" .
  qed blast
  show ?thesis by (rule ext) (simp only: normal_form_def eq)
qed

lemma normal_form_diff_in_ideal: "p - normal_form F p \<in> ideal F"
proof -
  from normal_form(1) have "p - normal_form F p \<in> ideal (punit.reduced_GB F)"
    by (rule punit.red_rtranclp_diff_in_pmdl[simplified])
  also from fin_X F_sub have "\<dots> = ideal F" by (rule reduced_GB_ideal_Polys)
  finally show ?thesis .
qed

lemma normal_form_zero_iff: "normal_form F p = 0 \<longleftrightarrow> p \<in> ideal F"
proof
  assume "normal_form F p = 0"
  with normal_form_diff_in_ideal[of p] show "p \<in> ideal F" by simp
next
  assume "p \<in> ideal F"
  hence "p - (p - normal_form F p) \<in> ideal F" using normal_form_diff_in_ideal
    by (rule ideal.span_diff)
  also from fin_X F_sub have "\<dots> = ideal (punit.reduced_GB F)" by (rule reduced_GB_ideal_Polys[symmetric])
  finally have *: "normal_form F p \<in> ideal (punit.reduced_GB F)" by simp
  show "normal_form F p = 0"
  proof (rule ccontr)
    from fin_X F_sub have "punit.is_Groebner_basis (punit.reduced_GB F)" by (rule reduced_GB_is_GB_Polys)
    moreover note *
    moreover assume "normal_form F p \<noteq> 0"
    ultimately obtain g where "g \<in> punit.reduced_GB F" and "g \<noteq> 0"
      and a: "lpp g adds lpp (normal_form F p)" by (rule punit.GB_adds_lt[simplified])
    note this(1, 2)
    moreover from \<open>normal_form F p \<noteq> 0\<close> have "lpp (normal_form F p) \<in> keys (normal_form F p)"
      by (rule punit.lt_in_keys)
    ultimately have "punit.is_red (punit.reduced_GB F) (normal_form F p)"
      using a by (rule punit.is_red_addsI[simplified])
    with normal_form(2) show False ..
  qed
qed

lemma normal_form_eq_iff: "normal_form F p = normal_form F q \<longleftrightarrow> p - q \<in> ideal F"
proof -
  have "p - q - (normal_form F p - normal_form F q) = (p - normal_form F p) - (q - normal_form F q)"
    by simp
  also from normal_form_diff_in_ideal normal_form_diff_in_ideal have "\<dots> \<in> ideal F"
    by (rule ideal.span_diff)
  finally have *: "p - q - (normal_form F p - normal_form F q) \<in> ideal F" .
  show ?thesis
  proof
    assume "normal_form F p = normal_form F q"
    with * show "p - q \<in> ideal F" by simp
  next
    assume "p - q \<in> ideal F"
    hence "p - q - (p - q - (normal_form F p - normal_form F q)) \<in> ideal F" using *
      by (rule ideal.span_diff)
    hence "normal_form F (normal_form F p - normal_form F q) = 0" by (simp add: normal_form_zero_iff)
    thus "normal_form F p = normal_form F q" by (simp add: normal_form_minus_normal_form)
  qed
qed

lemma Polys_closed_normal_form:
  assumes "p \<in> P[X]"
  shows "normal_form F p \<in> P[X]"
proof -
  from fin_X F_sub have "punit.reduced_GB F \<subseteq> P[X]" by (rule reduced_GB_Polys)
  with fin_X show ?thesis using assms normal_form(1)
    by (rule punit.dgrad_p_set_closed_red_rtrancl[OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum])
qed

lemma image_normal_form_iff:
  "p \<in> normal_form F ` P[X] \<longleftrightarrow> (p \<in> P[X] \<and> \<not> punit.is_red (punit.reduced_GB F) p)"
proof
  assume "p \<in> normal_form F ` P[X]"
  then obtain q where "q \<in> P[X]" and p: "p = normal_form F q" ..
  from this(1) show "p \<in> P[X] \<and> \<not> punit.is_red (punit.reduced_GB F) p" unfolding p
    by (intro conjI Polys_closed_normal_form normal_form)
next
  assume "p \<in> P[X] \<and> \<not> punit.is_red (punit.reduced_GB F) p"
  hence "p \<in> P[X]" and "\<not> punit.is_red (punit.reduced_GB F) p" by simp_all
  from this(2) have "normal_form F p = p" by (simp add: normal_form_id_iff)
  from this[symmetric] \<open>p \<in> P[X]\<close> show "p \<in> normal_form F ` P[X]" by (rule image_eqI)
qed

end

lemma direct_decomp_ideal_insert:
  fixes F and f
  defines "I \<equiv> ideal (insert f F)"
  defines "L \<equiv> (ideal F \<div> f) \<inter> P[X]"
  assumes "F \<subseteq> P[X]" and "f \<in> P[X]"
  shows "direct_decomp (I \<inter> P[X]) [ideal F \<inter> P[X], (*) f ` normal_form L ` P[X]]"
    (is "direct_decomp _ ?ss")
proof (rule direct_decompI_alt)
  fix qs
  assume "qs \<in> listset ?ss"
  then obtain x y where x: "x \<in> ideal F \<inter> P[X]" and y: "y \<in> (*) f ` normal_form L ` P[X]"
    and qs: "qs = [x, y]" by (rule listset_doubletonE)
  have "sum_list qs = x + y" by (simp add: qs)
  also have "\<dots> \<in> I \<inter> P[X]" unfolding I_def
  proof (intro IntI ideal.span_add Polys_closed_plus)
    have "ideal F \<subseteq> ideal (insert f F)" by (rule ideal.span_mono) blast
    with x show "x \<in> ideal (insert f F)" and "x \<in> P[X]" by blast+
  next
    from y obtain p where "p \<in> P[X]" and y: "y = f * normal_form L p" by blast
    have "f \<in> ideal (insert f F)" by (rule ideal.span_base) simp
    hence "normal_form L p * f \<in> ideal (insert f F)" by (rule ideal.span_scale)
    thus "y \<in> ideal (insert f F)" by (simp only: mult.commute y)

    have "L \<subseteq> P[X]" by (simp add: L_def)
    hence "normal_form L p \<in> P[X]" using \<open>p \<in> P[X]\<close> by (rule Polys_closed_normal_form)
    with assms(4) show "y \<in> P[X]" unfolding y by (rule Polys_closed_times)
  qed
  finally show "sum_list qs \<in> I \<inter> P[X]" .
next
  fix a
  assume "a \<in> I \<inter> P[X]"
  hence "a \<in> I" and "a \<in> P[X]" by simp_all
  from assms(3, 4) have "insert f F \<subseteq> P[X]" by simp
  then obtain F0 q0 where "F0 \<subseteq> insert f F" and "finite F0" and q0: "\<And>f0. q0 f0 \<in> P[X]"
    and a: "a = (\<Sum>f0\<in>F0. q0 f0 * f0)"
    using \<open>a \<in> P[X]\<close> \<open>a \<in> I\<close> unfolding I_def by (rule in_idealE_Polys) blast
  obtain q a' where a': "a' \<in> ideal F" and "a' \<in> P[X]" and "q \<in> P[X]" and a: "a = q * f + a'"
  proof (cases "f \<in> F0")
    case True
    with \<open>F0 \<subseteq> insert f F\<close> have "F0 - {f} \<subseteq> F" by blast
    show ?thesis
    proof
      have "(\<Sum>f0\<in>F0 - {f}. q0 f0 * f0) \<in> ideal (F0 - {f})" by (rule ideal.sum_in_spanI)
      also from \<open>F0 - {f} \<subseteq> F\<close> have "\<dots> \<subseteq> ideal F" by (rule ideal.span_mono)
      finally show "(\<Sum>f0\<in>F0 - {f}. q0 f0 * f0) \<in> ideal F" .
    next
      show "(\<Sum>f0\<in>F0 - {f}. q0 f0 * f0) \<in> P[X]"
      proof (intro Polys_closed_sum Polys_closed_times q0)
        fix f0
        assume "f0 \<in> F0 - {f}"
        also have "\<dots> \<subseteq> F0" by blast
        also have "\<dots> \<subseteq> insert f F" by fact
        also have "\<dots> \<subseteq> P[X]" by fact
        finally show "f0 \<in> P[X]" .
      qed
    next
      from \<open>finite F0\<close> True show "a = q0 f * f + (\<Sum>f0\<in>F0 - {f}. q0 f0 * f0)"
        by (simp only: a sum.remove)
    qed fact
  next
    case False
    with \<open>F0 \<subseteq> insert f F\<close> have "F0 \<subseteq> F" by blast
    show ?thesis
    proof
      have "a \<in> ideal F0" unfolding a by (rule ideal.sum_in_spanI)
      also from \<open>F0 \<subseteq> F\<close> have "\<dots> \<subseteq> ideal F" by (rule ideal.span_mono)
      finally show "a \<in> ideal F" .
    next
      show "a = 0 * f + a" by simp
    qed (fact \<open>a \<in> P[X]\<close>, fact zero_in_Polys)
  qed
  let ?a = "f * (normal_form L q)"
  have "L \<subseteq> P[X]" by (simp add: L_def)
  hence "normal_form L q \<in> P[X]" using \<open>q \<in> P[X]\<close> by (rule Polys_closed_normal_form)
  with assms(4) have "?a \<in> P[X]" by (rule Polys_closed_times)
  from \<open>L \<subseteq> P[X]\<close> have "q - normal_form L q \<in> ideal L" by (rule normal_form_diff_in_ideal)
  also have "\<dots> \<subseteq> ideal (ideal F \<div> f)" unfolding L_def by (rule ideal.span_mono) blast
  finally have "f * (q - normal_form L q) \<in> ideal F" by (simp add: quot_set_iff)
  with \<open>a' \<in> ideal F\<close> have "a' + f * (q - normal_form L q) \<in> ideal F" by (rule ideal.span_add)
  hence "a - ?a \<in> ideal F" by (simp add: a algebra_simps)

  define qs where "qs = [a - ?a, ?a]"
  show "\<exists>!qs\<in>listset ?ss. a = sum_list qs"
  proof (intro ex1I conjI allI impI)
    have "a - ?a \<in> ideal F \<inter> P[X]"
    proof
      from assms(4) \<open>a \<in> P[X]\<close> \<open>normal_form L q \<in> P[X]\<close> show "a - ?a \<in> P[X]"
        by (intro Polys_closed_minus Polys_closed_times)
    qed fact
    moreover from \<open>q \<in> P[X]\<close> have "?a \<in> (*) f ` normal_form L ` P[X]" by (intro imageI)
    ultimately show "qs \<in> listset ?ss" using qs_def by (rule listset_doubletonI)
  next
    fix qs0
    assume "qs0 \<in> listset ?ss \<and> a = sum_list qs0"
    hence "qs0 \<in> listset ?ss" and "a = sum_list qs0" by simp_all
    from this(1) obtain x y where "x \<in> ideal F \<inter> P[X]" and "y \<in> (*) f ` normal_form L ` P[X]"
      and qs0: "qs0 = [x, y]" by (rule listset_doubletonE)
    from this(2) obtain a0 where "a0 \<in> P[X]" and y: "y = f * normal_form L a0" by blast
    from \<open>x \<in> ideal F \<inter> P[X]\<close> have "x \<in> ideal F" by simp
    have x: "x = a - y" by (simp add: \<open>a = sum_list qs0\<close> qs0)
    have "f * (normal_form L q - normal_form L a0) = x - (a - ?a)" by (simp add: x y a algebra_simps)
    also from \<open>x \<in> ideal F\<close> \<open>a - ?a \<in> ideal F\<close> have "\<dots> \<in> ideal F" by (rule ideal.span_diff)
    finally have "normal_form L q - normal_form L a0 \<in> ideal F \<div> f" by (rule quot_setI)
    moreover from \<open>L \<subseteq> P[X]\<close> \<open>q \<in> P[X]\<close> \<open>a0 \<in> P[X]\<close> have "normal_form L q - normal_form L a0 \<in> P[X]"
      by (intro Polys_closed_minus Polys_closed_normal_form)
    ultimately have "normal_form L q - normal_form L a0 \<in> L" by (simp add: L_def)
    also have "\<dots> \<subseteq> ideal L" by (fact ideal.span_superset)
    finally have "normal_form L q - normal_form L a0 = 0" using \<open>L \<subseteq> P[X]\<close>
      by (simp only: normal_form_minus_normal_form flip: normal_form_zero_iff)
    thus "qs0 = qs" by (simp add: qs0 qs_def x y)
  qed (simp_all add: qs_def)
qed

corollary direct_decomp_ideal_normal_form:
  assumes "F \<subseteq> P[X]"
  shows "direct_decomp P[X] [ideal F \<inter> P[X], normal_form F ` P[X]]"
proof -
  from assms one_in_Polys have "direct_decomp (ideal (insert 1 F) \<inter> P[X]) [ideal F \<inter> P[X],
                                                (*) 1 ` normal_form ((ideal F \<div> 1) \<inter> P[X]) ` P[X]]"
    by (rule direct_decomp_ideal_insert)
  moreover have "ideal (insert 1 F) = UNIV"
    by (simp add: ideal_eq_UNIV_iff_contains_one ideal.span_base)
  moreover from refl have "((*) 1 \<circ> normal_form F) ` P[X] = normal_form F ` P[X]"
    by (rule image_cong) simp
  ultimately show ?thesis using assms by (simp add: image_comp normal_form_ideal_Polys)
qed

end

subsection \<open>Basic Cone Decompositions\<close>

definition cone :: "((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_0) set"
  where "cone hU = (*) (fst hU) ` P[snd hU]"

lemma coneI: "p = a * h \<Longrightarrow> a \<in> P[U] \<Longrightarrow> p \<in> cone (h, U)"
  by (auto simp: cone_def mult.commute[of a])

lemma coneE:
  assumes "p \<in> cone (h, U)"
  obtains a where "a \<in> P[U]" and "p = a * h"
  using assms by (auto simp: cone_def mult.commute)

lemma cone_empty: "cone (h, {}) = range (\<lambda>c. c \<cdot> h)"
  by (auto simp: Polys_empty map_scale_eq_times intro: coneI elim!: coneE)

lemma cone_zero [simp]: "cone (0, U) = {0}"
  by (auto simp: cone_def intro: zero_in_Polys)

lemma cone_one [simp]: "cone (1::_ \<Rightarrow>\<^sub>0 'a::comm_semiring_1, U) = P[U]"
  by (auto simp: cone_def)

lemma zero_in_cone: "0 \<in> cone hU"
  by (auto simp: cone_def intro!: image_eqI zero_in_Polys)

corollary empty_not_in_map_cone: "{} \<notin> set (map cone ps)"
  using zero_in_cone by fastforce

lemma tip_in_cone: "h \<in> cone (h::_ \<Rightarrow>\<^sub>0 _::comm_semiring_1, U)"
  using _ one_in_Polys by (rule coneI) simp

lemma cone_closed_plus:
  assumes "a \<in> cone hU" and "b \<in> cone hU"
  shows "a + b \<in> cone hU"
proof -
  obtain h U where hU: "hU = (h, U)" using prod.exhaust by blast
  with assms have "a \<in> cone (h, U)" and "b \<in> cone (h, U)" by simp_all
  from this(1) obtain a' where "a' \<in> P[U]" and a: "a = a' * h" by (rule coneE)
  from \<open>b \<in> cone (h, U)\<close> obtain b' where "b' \<in> P[U]" and b: "b = b' * h" by (rule coneE)
  have "a + b = (a' + b') * h" by (simp only: a b algebra_simps)
  moreover from \<open>a' \<in> P[U]\<close> \<open>b' \<in> P[U]\<close> have "a' + b' \<in> P[U]" by (rule Polys_closed_plus)
  ultimately show ?thesis unfolding hU by (rule coneI)
qed

lemma cone_closed_uminus:
  assumes "(a::_ \<Rightarrow>\<^sub>0 _::comm_ring) \<in> cone hU"
  shows "- a \<in> cone hU"
proof -
  obtain h U where hU: "hU = (h, U)" using prod.exhaust by blast
  with assms have "a \<in> cone (h, U)" by simp
  from this(1) obtain a' where "a' \<in> P[U]" and a: "a = a' * h" by (rule coneE)
  have "- a = (- a') * h" by (simp add: a)
  moreover from \<open>a' \<in> P[U]\<close> have "- a' \<in> P[U]" by (rule Polys_closed_uminus)
  ultimately show ?thesis unfolding hU by (rule coneI)
qed

lemma cone_closed_minus:
  assumes "(a::_ \<Rightarrow>\<^sub>0 _::comm_ring) \<in> cone hU" and "b \<in> cone hU"
  shows "a - b \<in> cone hU"
proof -
  from assms(2) have "- b \<in> cone hU" by (rule cone_closed_uminus)
  with assms(1) have "a + (- b) \<in> cone hU" by (rule cone_closed_plus)
  thus ?thesis by simp
qed

lemma cone_closed_times:
  assumes "a \<in> cone (h, U)" and "q \<in> P[U]"
  shows "q * a \<in> cone (h, U)"
proof -
  from assms(1) obtain a' where "a' \<in> P[U]" and a: "a = a' * h" by (rule coneE)
  have "q * a = (q * a') * h" by (simp only: a ac_simps)
  moreover from assms(2) \<open>a' \<in> P[U]\<close> have "q * a' \<in> P[U]" by (rule Polys_closed_times)
  ultimately show ?thesis by (rule coneI)
qed

corollary cone_closed_monom_mult:
  assumes "a \<in> cone (h, U)" and "t \<in> .[U]"
  shows "punit.monom_mult c t a \<in> cone (h, U)"
proof -
  from assms(2) have "monomial c t \<in> P[U]" by (rule Polys_closed_monomial)
  with assms(1) have "monomial c t * a \<in> cone (h, U)" by (rule cone_closed_times)
  thus ?thesis by (simp only: times_monomial_left)
qed

lemma coneD:
  assumes "p \<in> cone (h, U)" and "p \<noteq> 0"
  shows "lpp h adds lpp (p::_ \<Rightarrow>\<^sub>0 _::{comm_semiring_0,semiring_no_zero_divisors})"
proof -
  from assms(1) obtain a where p: "p = a * h" by (rule coneE)
  with assms(2) have "a \<noteq> 0" and "h \<noteq> 0" by auto
  hence "lpp p = lpp a + lpp h" unfolding p by (rule lp_times)
  also have "\<dots> = lpp h + lpp a" by (rule add.commute)
  finally show ?thesis by (rule addsI)
qed

lemma cone_mono_1:
  assumes "h' \<in> P[U]"
  shows "cone (h' * h, U) \<subseteq> cone (h, U)"
proof
  fix p
  assume "p \<in> cone (h' * h, U)"
  then obtain a' where "a' \<in> P[U]" and "p = a' * (h' * h)" by (rule coneE)
  from this(2) have "p = a' * h' * h" by (simp only: mult.assoc)
  moreover from \<open>a' \<in> P[U]\<close> assms have "a' * h' \<in> P[U]" by (rule Polys_closed_times)
  ultimately show "p \<in> cone (h, U)" by (rule coneI)
qed

lemma cone_mono_2:
  assumes "U1 \<subseteq> U2"
  shows "cone (h, U1) \<subseteq> cone (h, U2)"
proof
  from assms have "P[U1] \<subseteq> P[U2]" by (rule Polys_mono)
  fix p
  assume "p \<in> cone (h, U1)"
  then obtain a where "a \<in> P[U1]" and "p = a * h" by (rule coneE)
  note this(2)
  moreover from \<open>a \<in> P[U1]\<close> \<open>P[U1] \<subseteq> P[U2]\<close> have "a \<in> P[U2]" ..
  ultimately show "p \<in> cone (h, U2)" by (rule coneI)
qed

lemma cone_subsetD:
  assumes "cone (h1, U1) \<subseteq> cone (h2::_ \<Rightarrow>\<^sub>0 'a::{comm_ring_1,ring_no_zero_divisors}, U2)"
  shows "h2 dvd h1" and "h1 \<noteq> 0 \<Longrightarrow> U1 \<subseteq> U2"
proof -
  from tip_in_cone assms have "h1 \<in> cone (h2, U2)" ..
  then obtain a1' where "a1' \<in> P[U2]" and h1: "h1 = a1' * h2" by (rule coneE)
  from this(2) have "h1 = h2 * a1'" by (simp only: mult.commute)
  thus "h2 dvd h1" ..

  assume "h1 \<noteq> 0"
  with h1 have "a1' \<noteq> 0" and "h2 \<noteq> 0" by auto
  show "U1 \<subseteq> U2"
  proof
    fix x
    assume "x \<in> U1"
    hence "monomial (1::'a) (Poly_Mapping.single x 1) \<in> P[U1]" (is "?p \<in> _")
      by (intro Polys_closed_monomial PPs_closed_single)
    with refl have "?p * h1 \<in> cone (h1, U1)" by (rule coneI)
    hence "?p * h1 \<in> cone (h2, U2)" using assms ..
    then obtain a where "a \<in> P[U2]" and "?p * h1 = a * h2" by (rule coneE)
    from this(2) have "(?p * a1') * h2 = a * h2" by (simp only: h1 ac_simps)
    hence "?p * a1' = a" using \<open>h2 \<noteq> 0\<close> by (rule times_canc_right)
    with \<open>a \<in> P[U2]\<close> have "a1' * ?p \<in> P[U2]" by (simp add: mult.commute)
    hence "?p \<in> P[U2]" using \<open>a1' \<in> P[U2]\<close> \<open>a1' \<noteq> 0\<close> by (rule times_in_PolysD)
    thus "x \<in> U2" by (simp add: Polys_def PPs_def)
  qed
qed

lemma cone_subset_PolysD:
  assumes "cone (h::_ \<Rightarrow>\<^sub>0 'a::{comm_semiring_1,semiring_no_zero_divisors}, U) \<subseteq> P[X]"
  shows "h \<in> P[X]" and "h \<noteq> 0 \<Longrightarrow> U \<subseteq> X"
proof -
  from tip_in_cone assms show "h \<in> P[X]" ..

  assume "h \<noteq> 0"
  show "U \<subseteq> X"
  proof
    fix x
    assume "x \<in> U"
    hence "monomial (1::'a) (Poly_Mapping.single x 1) \<in> P[U]" (is "?p \<in> _")
      by (intro Polys_closed_monomial PPs_closed_single)
    with refl have "?p * h \<in> cone (h, U)" by (rule coneI)
    hence "?p * h \<in> P[X]" using assms ..
    hence "h * ?p \<in> P[X]" by (simp only: mult.commute)
    hence "?p \<in> P[X]" using \<open>h \<in> P[X]\<close> \<open>h \<noteq> 0\<close> by (rule times_in_PolysD)
    thus "x \<in> X" by (simp add: Polys_def PPs_def)
  qed
qed

lemma cone_subset_PolysI:
  assumes "h \<in> P[X]" and "h \<noteq> 0 \<Longrightarrow> U \<subseteq> X"
  shows "cone (h, U) \<subseteq> P[X]"
proof (cases "h = 0")
  case True
  thus ?thesis by (simp add: zero_in_Polys)
next
  case False
  hence "U \<subseteq> X" by (rule assms(2))
  hence "P[U] \<subseteq> P[X]" by (rule Polys_mono)
  show ?thesis
  proof
    fix a
    assume "a \<in> cone (h, U)"
    then obtain q where "q \<in> P[U]" and a: "a = q * h" by (rule coneE)
    from this(1) \<open>P[U] \<subseteq> P[X]\<close> have "q \<in> P[X]" ..
    from this assms(1) show "a \<in> P[X]" unfolding a by (rule Polys_closed_times)
  qed
qed

lemma cone_image_times: "(*) a ` cone (h, U) = cone (a * h, U)"
  by (auto simp: ac_simps image_image intro!: image_eqI coneI elim!: coneE)

lemma cone_image_times': "(*) a ` cone hU = cone (apfst ((*) a) hU)"
proof -
  obtain h U where "hU = (h, U)" using prod.exhaust by blast
  thus ?thesis by (simp add: cone_image_times)
qed

lemma homogeneous_set_coneI:
  assumes "homogeneous h"
  shows "homogeneous_set (cone (h, U))"
proof (rule homogeneous_setI)
  fix a n
  assume "a \<in> cone (h, U)"
  then obtain q where "q \<in> P[U]" and a: "a = q * h" by (rule coneE)
  from this(1) show "hom_component a n \<in> cone (h, U)" unfolding a
  proof (induct q rule: poly_mapping_plus_induct)
    case 1
    show ?case by (simp add: zero_in_cone)
  next
    case (2 p c t)
    have "p \<in> P[U]"
    proof (intro PolysI subsetI)
      fix s
      assume "s \<in> keys p"
      moreover from 2(2) this have "s \<notin> keys (monomial c t)" by auto
      ultimately have "s \<in> keys (monomial c t + p)" by (rule in_keys_plusI2)
      also from 2(4) have "\<dots> \<subseteq> .[U]" by (rule PolysD)
      finally show "s \<in> .[U]" .
    qed
    hence *: "hom_component (p * h) n \<in> cone (h, U)" by (rule 2(3))
    from 2(1) have "t \<in> keys (monomial c t)" by simp
    hence "t \<in> keys (monomial c t + p)" using 2(2) by (rule in_keys_plusI1)
    also from 2(4) have "\<dots> \<subseteq> .[U]" by (rule PolysD)
    finally have "monomial c t \<in> P[U]" by (rule Polys_closed_monomial)
    with refl have "monomial c t * h \<in> cone (h, U)" (is "?h \<in> _") by (rule coneI)
    from assms have "homogeneous ?h" by (simp add: homogeneous_times)
    hence "hom_component ?h n = (?h when n = poly_deg ?h)" by (rule hom_component_of_homogeneous)
    with \<open>?h \<in> cone (h, U)\<close> have **: "hom_component ?h n \<in> cone (h, U)"
      by (simp add: when_def zero_in_cone)
    have "hom_component ((monomial c t + p) * h) n = hom_component ?h n + hom_component (p * h) n"
      by (simp only: distrib_right hom_component_plus)
    also from ** * have "\<dots> \<in> cone (h, U)" by (rule cone_closed_plus)
    finally show ?case .
  qed
qed

lemma subspace_cone: "phull.subspace (cone hU)"
  using zero_in_cone cone_closed_plus
proof (rule phull.subspaceI)
  fix c a
  assume "a \<in> cone hU"
  moreover obtain h U where hU: "hU = (h, U)" using prod.exhaust by blast
  ultimately have "a \<in> cone (h, U)" by simp
  thus "c \<cdot> a \<in> cone hU" unfolding hU punit.map_scale_eq_monom_mult using zero_in_PPs
    by (rule cone_closed_monom_mult)
qed

lemma direct_decomp_cone_insert:
  fixes h :: "_ \<Rightarrow>\<^sub>0 'a::{comm_ring_1,ring_no_zero_divisors}"
  assumes "x \<notin> U"
  shows "direct_decomp (cone (h, insert x U))
                  [cone (h, U), cone (monomial 1 (Poly_Mapping.single x (Suc 0)) * h, insert x U)]"
proof -
  let ?x = "Poly_Mapping.single x (Suc 0)"
  define xx where "xx = monomial (1::'a) ?x"
  show "direct_decomp (cone (h, insert x U)) [cone (h, U), cone (xx * h, insert x U)]"
    (is "direct_decomp _ ?ss")
  proof (rule direct_decompI_alt)
    fix qs
    assume "qs \<in> listset ?ss"
    then obtain a b where "a \<in> cone (h, U)" and b: "b \<in> cone (xx * h, insert x U)"
      and qs: "qs = [a, b]" by (rule listset_doubletonE)
    note this(1)
    also have "cone (h, U) \<subseteq> cone (h, insert x U)" by (rule cone_mono_2) blast
    finally have a: "a \<in> cone (h, insert x U)" .
    have "cone (xx * h, insert x U) \<subseteq> cone (h, insert x U)"
      by (rule cone_mono_1) (simp add: xx_def Polys_def PPs_closed_single)
    with b have "b \<in> cone (h, insert x U)" ..
    with a have "a + b \<in> cone (h, insert x U)" by (rule cone_closed_plus)
    thus "sum_list qs \<in> cone (h, insert x U)" by (simp add: qs)
  next
    fix a
    assume "a \<in> cone (h, insert x U)"
    then obtain q where "q \<in> P[insert x U]" and a: "a = q * h" by (rule coneE)
    define qU where "qU = except q (- .[U])"
    define qx where "qx = except q .[U]"
    have q: "q = qU + qx" by (simp only: qU_def qx_def add.commute flip: except_decomp)
    have "qU \<in> P[U]" by (rule PolysI) (simp add: qU_def keys_except)
    have x_adds: "?x adds t" if "t \<in> keys qx" for t unfolding adds_poly_mapping le_fun_def
    proof
      fix y
      show "lookup ?x y \<le> lookup t y"
      proof (cases "y = x")
        case True
        from that have "t \<in> keys q" and "t \<notin> .[U]" by (simp_all add: qx_def keys_except)
        from \<open>q \<in> P[insert x U]\<close> have "keys q \<subseteq> .[insert x U]" by (rule PolysD)
        with \<open>t \<in> keys q\<close> have "t \<in> .[insert x U]" ..
        hence "keys t \<subseteq> insert x U" by (rule PPsD)
        moreover from \<open>t \<notin> .[U]\<close> have "\<not> keys t \<subseteq> U" by (simp add: PPs_def)
        ultimately have "x \<in> keys t" by blast
        thus ?thesis by (simp add: lookup_single True in_keys_iff)
      next
        case False
        thus ?thesis by (simp add: lookup_single)
      qed
    qed
    define qx' where "qx' = Poly_Mapping.map_key ((+) ?x) qx"
    have lookup_qx': "lookup qx' = (\<lambda>t. lookup qx (?x + t))"
      by (rule ext) (simp add: qx'_def map_key.rep_eq)
    have "qx' * xx = punit.monom_mult 1 ?x qx'"
      by (simp only: xx_def mult.commute flip: times_monomial_left)
    also have "\<dots> = qx"
      by (auto simp: punit.lookup_monom_mult lookup_qx' add.commute[of ?x] adds_minus
              simp flip: not_in_keys_iff_lookup_eq_zero dest: x_adds intro!: poly_mapping_eqI)
    finally have qx: "qx = qx' * xx" by (rule sym)
    have "qx' \<in> P[insert x U]"
    proof (intro PolysI subsetI)
      fix t
      assume "t \<in> keys qx'"
      hence "t + ?x \<in> keys qx" by (simp only: lookup_qx' in_keys_iff not_False_eq_True add.commute)
      also have "\<dots> \<subseteq> keys q" by (auto simp: qx_def keys_except)
      also from \<open>q \<in> P[insert x U]\<close> have "\<dots> \<subseteq> .[insert x U]" by (rule PolysD)
      finally have "(t + ?x) - ?x \<in> .[insert x U]" by (rule PPs_closed_minus)
      thus "t \<in> .[insert x U]" by simp
    qed
    define qs where "qs = [qU * h, qx' * (xx * h)]"
    show "\<exists>!qs\<in>listset ?ss. a = sum_list qs"
    proof (intro ex1I conjI allI impI)
      from refl \<open>qU \<in> P[U]\<close> have "qU * h \<in> cone (h, U)" by (rule coneI)
      moreover from refl \<open>qx' \<in> P[insert x U]\<close> have "qx' * (xx * h) \<in> cone (xx * h, insert x U)"
        by (rule coneI)
      ultimately show "qs \<in> listset ?ss" using qs_def by (rule listset_doubletonI)
    next
      fix qs0
      assume "qs0 \<in> listset ?ss \<and> a = sum_list qs0"
      hence "qs0 \<in> listset ?ss" and a0: "a = sum_list qs0" by simp_all
      from this(1) obtain p1 p2 where "p1 \<in> cone (h, U)" and p2: "p2 \<in> cone (xx * h, insert x U)"
        and qs0: "qs0 = [p1, p2]" by (rule listset_doubletonE)
      from this(1) obtain qU0 where "qU0 \<in> P[U]" and p1: "p1 = qU0 * h" by (rule coneE)
      from p2 obtain qx0 where p2: "p2 = qx0 * (xx * h)" by (rule coneE)
      show "qs0 = qs"
      proof (cases "h = 0")
        case True
        thus ?thesis by (simp add: qs_def qs0 p1 p2)
      next
        case False
        from a0 have "(qU - qU0) * h = (qx0 - qx') * xx * h"
          by (simp add: a qs0 p1 p2 q qx algebra_simps)
        hence eq: "qU - qU0 = (qx0 - qx') * xx" using False by (rule times_canc_right)
        have "qx0 = qx'"
        proof (rule ccontr)
          assume "qx0 \<noteq> qx'"
          hence "qx0 - qx' \<noteq> 0" by simp
          moreover have "xx \<noteq> 0" by (simp add: xx_def monomial_0_iff)
          ultimately have "lpp ((qx0 - qx') * xx) = lpp (qx0 - qx') + lpp xx"
            by (rule lp_times)
          also have "lpp xx = ?x" by (simp add: xx_def punit.lt_monomial)
          finally have "?x adds lpp (qU - qU0)" by (simp add: eq)
          hence "lookup ?x x \<le> lookup (lpp (qU - qU0)) x" by (simp only: adds_poly_mapping le_fun_def)
          hence "x \<in> keys (lpp (qU - qU0))" by (simp add: in_keys_iff lookup_single)
          moreover have "lpp (qU - qU0) \<in> keys (qU - qU0)"
          proof (rule punit.lt_in_keys)
            from \<open>qx0 - qx' \<noteq> 0\<close> \<open>xx \<noteq> 0\<close> show "qU - qU0 \<noteq> 0" unfolding eq by (rule times_not_zero)
          qed
          ultimately have "x \<in> indets (qU - qU0)" by (rule in_indetsI)
          from \<open>qU \<in> P[U]\<close> \<open>qU0 \<in> P[U]\<close> have "qU - qU0 \<in> P[U]" by (rule Polys_closed_minus)
          hence "indets (qU - qU0) \<subseteq> U" by (rule PolysD)
          with \<open>x \<in> indets (qU - qU0)\<close> have "x \<in> U" ..
          with assms show False ..
        qed
        moreover from this eq have "qU0 = qU" by simp
        ultimately show ?thesis by (simp only: qs_def qs0 p1 p2)
      qed
    qed (simp_all add: qs_def a q qx, simp only: algebra_simps)
  qed
qed

definition valid_decomp :: "'x set \<Rightarrow> ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) \<times> 'x set) list \<Rightarrow> bool"
  where "valid_decomp X ps \<longleftrightarrow> ((\<forall>(h, U)\<in>set ps. h \<in> P[X] \<and> h \<noteq> 0 \<and> U \<subseteq> X))"

definition monomial_decomp :: "((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::{one,zero}) \<times> 'x set) list \<Rightarrow> bool"
  where "monomial_decomp ps \<longleftrightarrow> (\<forall>hU\<in>set ps. is_monomial (fst hU) \<and> punit.lc (fst hU) = 1)"

definition hom_decomp :: "((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::{one,zero}) \<times> 'x set) list \<Rightarrow> bool"
  where "hom_decomp ps \<longleftrightarrow> (\<forall>hU\<in>set ps. homogeneous (fst hU))"

definition cone_decomp :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set \<Rightarrow>
                            ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_0) \<times> 'x set) list \<Rightarrow> bool"
  where "cone_decomp T ps \<longleftrightarrow> direct_decomp T (map cone ps)"

lemma valid_decompI:
  "(\<And>h U. (h, U) \<in> set ps \<Longrightarrow> h \<in> P[X]) \<Longrightarrow> (\<And>h U. (h, U) \<in> set ps \<Longrightarrow> h \<noteq> 0) \<Longrightarrow>
    (\<And>h U. (h, U) \<in> set ps \<Longrightarrow> U \<subseteq> X) \<Longrightarrow> valid_decomp X ps"
  unfolding valid_decomp_def by blast

lemma valid_decompD:
  assumes "valid_decomp X ps" and "(h, U) \<in> set ps"
  shows "h \<in> P[X]" and "h \<noteq> 0" and "U \<subseteq> X"
  using assms unfolding valid_decomp_def by blast+

lemma valid_decompD_finite:
  assumes "finite X" and "valid_decomp X ps" and "(h, U) \<in> set ps"
  shows "finite U"
proof -
  from assms(2, 3) have "U \<subseteq> X" by (rule valid_decompD)
  thus ?thesis using assms(1) by (rule finite_subset)
qed

lemma valid_decomp_Nil: "valid_decomp X []"
  by (simp add: valid_decomp_def)

lemma valid_decomp_concat:
  assumes "\<And>ps. ps \<in> set pss \<Longrightarrow> valid_decomp X ps"
  shows "valid_decomp X (concat pss)"
proof (rule valid_decompI)
  fix h U
  assume "(h, U) \<in> set (concat pss)"
  then obtain ps where "ps \<in> set pss" and "(h, U) \<in> set ps" unfolding set_concat ..
  from this(1) have "valid_decomp X ps" by (rule assms)
  thus "h \<in> P[X]" and "h \<noteq> 0" and "U \<subseteq> X" using \<open>(h, U) \<in> set ps\<close> by (rule valid_decompD)+
qed

corollary valid_decomp_append:
  assumes "valid_decomp X ps" and "valid_decomp X qs"
  shows "valid_decomp X (ps @ qs)"
proof -
  have "valid_decomp X (concat [ps, qs])" by (rule valid_decomp_concat) (auto simp: assms)
  thus ?thesis by simp
qed

lemma valid_decomp_map_times:
  assumes "valid_decomp X ps" and "s \<in> P[X]" and "s \<noteq> (0::_ \<Rightarrow>\<^sub>0 _::semiring_no_zero_divisors)"
  shows "valid_decomp X (map (apfst ((*) s)) ps)"
proof (rule valid_decompI)
  fix h U
  assume "(h, U) \<in> set (map (apfst ((*) s)) ps)"
  then obtain x where "x \<in> set ps" and "(h, U) = apfst ((*) s) x" unfolding set_map ..
  moreover obtain a b where "x = (a, b)" using prod.exhaust by blast
  ultimately have h: "h = s * a" and "(a, U) \<in> set ps" by simp_all
  from assms(1) this(2) have "a \<in> P[X]" and "a \<noteq> 0" and "U \<subseteq> X" by (rule valid_decompD)+
  from assms(2) this(1) show "h \<in> P[X]" unfolding h by (rule Polys_closed_times)
  from assms(3) \<open>a \<noteq> 0\<close> show "h \<noteq> 0" unfolding h by (rule times_not_zero)
  from \<open>U \<subseteq> X\<close> show "U \<subseteq> X" .
qed

lemma monomial_decompI:
  "(\<And>h U. (h, U) \<in> set ps \<Longrightarrow> is_monomial h) \<Longrightarrow> (\<And>h U. (h, U) \<in> set ps \<Longrightarrow> punit.lc h = 1) \<Longrightarrow>
    monomial_decomp ps"
  by (auto simp: monomial_decomp_def)

lemma monomial_decompD:
  assumes "monomial_decomp ps" and "(h, U) \<in> set ps"
  shows "is_monomial h" and "punit.lc h = 1"
  using assms by (auto simp: monomial_decomp_def)

lemma monomial_decomp_append_iff:
  "monomial_decomp (ps @ qs) \<longleftrightarrow> monomial_decomp ps \<and> monomial_decomp qs"
  by (auto simp: monomial_decomp_def)

lemma monomial_decomp_concat:
  "(\<And>ps. ps \<in> set pss \<Longrightarrow> monomial_decomp ps) \<Longrightarrow> monomial_decomp (concat pss)"
  by (induct pss) (auto simp: monomial_decomp_def)

lemma monomial_decomp_map_times:
  assumes "monomial_decomp ps" and "is_monomial f" and "punit.lc f = (1::'a::semiring_1)"
  shows "monomial_decomp (map (apfst ((*) f)) ps)"
proof (rule monomial_decompI)
  fix h U
  assume "(h, U) \<in> set (map (apfst ((*) f)) ps)"
  then obtain x where "x \<in> set ps" and "(h, U) = apfst ((*) f) x" unfolding set_map ..
  moreover obtain a b where "x = (a, b)" using prod.exhaust by blast
  ultimately have h: "h = f * a" and "(a, U) \<in> set ps" by simp_all
  from assms(1) this(2) have "is_monomial a" and "punit.lc a = 1" by (rule monomial_decompD)+
  from this(1) have "monomial (punit.lc a) (lpp a) = a" by (rule punit.monomial_eq_itself)
  moreover define t where "t = lpp a"
  ultimately have a: "a = monomial 1 t" by (simp only: \<open>punit.lc a = 1\<close>)
  from assms(2) have "monomial (punit.lc f) (lpp f) = f" by (rule punit.monomial_eq_itself)
  moreover define s where "s = lpp f"
  ultimately have f: "f = monomial 1 s" by (simp only: assms(3))
  show "is_monomial h" by (simp add: h a f times_monomial_monomial monomial_is_monomial)
  show "punit.lc h = 1" by (simp add: h a f times_monomial_monomial)
qed

lemma monomial_decomp_monomial_in_cone:
  assumes "monomial_decomp ps" and "hU \<in> set ps" and "a \<in> cone hU"
  shows "monomial (lookup a t) t \<in> cone hU"
proof (cases "t \<in> keys a")
  case True
  obtain h U where hU: "hU = (h, U)" using prod.exhaust by blast
  with assms(2) have "(h, U) \<in> set ps" by simp
  with assms(1) have "is_monomial h" by (rule monomial_decompD)
  then obtain c s where h: "h = monomial c s" by (rule is_monomial_monomial)
  from assms(3) obtain q where "q \<in> P[U]" and "a = q * h" unfolding hU by (rule coneE)
  from this(2) have "a = h * q" by (simp only: mult.commute)
  also have "\<dots> = punit.monom_mult c s q" by (simp only: h times_monomial_left)
  finally have a: "a = punit.monom_mult c s q" .
  with True have "t \<in> keys (punit.monom_mult c s q)" by simp
  hence "t \<in> (+) s ` keys q" using punit.keys_monom_mult_subset[simplified] ..
  then obtain u where "u \<in> keys q" and t: "t = s + u" ..
  note this(1)
  also from \<open>q \<in> P[U]\<close> have "keys q \<subseteq> .[U]" by (rule PolysD)
  finally have "u \<in> .[U]" .
  have "monomial (lookup a t) t = monomial (lookup q u) u * h"
    by (simp add: a t punit.lookup_monom_mult h times_monomial_monomial mult.commute)
  moreover from \<open>u \<in> .[U]\<close> have "monomial (lookup q u) u \<in> P[U]" by (rule Polys_closed_monomial)
  ultimately show ?thesis unfolding hU by (rule coneI)
next
  case False
  thus ?thesis by (simp add: zero_in_cone in_keys_iff)
qed

lemma monomial_decomp_sum_list_monomial_in_cone:
  assumes "monomial_decomp ps" and "a \<in> sum_list ` listset (map cone ps)" and "t \<in> keys a"
  obtains c h U where "(h, U) \<in> set ps" and "c \<noteq> 0" and "monomial c t \<in> cone (h, U)"
proof -
  from assms(2) obtain qs where qs_in: "qs \<in> listset (map cone ps)" and a: "a = sum_list qs" ..
  from assms(3) keys_sum_list_subset have "t \<in> Keys (set qs)" unfolding a ..
  then obtain q where "q \<in> set qs" and "t \<in> keys q" by (rule in_KeysE)
  from this(1) obtain i where "i < length qs" and q: "q = qs ! i" by (metis in_set_conv_nth)
  moreover from qs_in have "length qs = length (map cone ps)" by (rule listsetD)
  ultimately have "i < length (map cone ps)" by simp
  moreover from qs_in this have "qs ! i \<in> (map cone ps) ! i" by (rule listsetD)
  ultimately have "ps ! i \<in> set ps" and "q \<in> cone (ps ! i)" by (simp_all add: q)
  with assms(1) have *: "monomial (lookup q t) t \<in> cone (ps ! i)"
    by (rule monomial_decomp_monomial_in_cone)
  obtain h U where psi: "ps ! i = (h, U)" using prod.exhaust by blast
  show ?thesis
  proof
    from \<open>ps ! i \<in> set ps\<close> show "(h, U) \<in> set ps" by (simp only: psi)
  next
    from \<open>t \<in> keys q\<close> show "lookup q t \<noteq> 0" by (simp add: in_keys_iff)
  next
    from * show "monomial (lookup q t) t \<in> cone (h, U)" by (simp only: psi)
  qed
qed

lemma hom_decompI: "(\<And>h U. (h, U) \<in> set ps \<Longrightarrow> homogeneous h) \<Longrightarrow> hom_decomp ps"
  by (auto simp: hom_decomp_def)

lemma hom_decompD: "hom_decomp ps \<Longrightarrow> (h, U) \<in> set ps \<Longrightarrow> homogeneous h"
  by (auto simp: hom_decomp_def)

lemma hom_decomp_append_iff: "hom_decomp (ps @ qs) \<longleftrightarrow> hom_decomp ps \<and> hom_decomp qs"
  by (auto simp: hom_decomp_def)

lemma hom_decomp_concat: "(\<And>ps. ps \<in> set pss \<Longrightarrow> hom_decomp ps) \<Longrightarrow> hom_decomp (concat pss)"
  by (induct pss) (auto simp: hom_decomp_def)

lemma hom_decomp_map_times:
  assumes "hom_decomp ps" and "homogeneous f"
  shows "hom_decomp (map (apfst ((*) f)) ps)"
proof (rule hom_decompI)
  fix h U
  assume "(h, U) \<in> set (map (apfst ((*) f)) ps)"
  then obtain x where "x \<in> set ps" and "(h, U) = apfst ((*) f) x" unfolding set_map ..
  moreover obtain a b where "x = (a, b)" using prod.exhaust by blast
  ultimately have h: "h = f * a" and "(a, U) \<in> set ps" by simp_all
  from assms(1) this(2) have "homogeneous a" by (rule hom_decompD)
  with assms(2) show "homogeneous h" unfolding h by (rule homogeneous_times)
qed

lemma monomial_decomp_imp_hom_decomp:
  assumes "monomial_decomp ps"
  shows "hom_decomp ps"
proof (rule hom_decompI)
  fix h U
  assume "(h, U) \<in> set ps"
  with assms have "is_monomial h" by (rule monomial_decompD)
  then obtain c t where h: "h = monomial c t" by (rule is_monomial_monomial)
  show "homogeneous h" unfolding h by (fact homogeneous_monomial)
qed

lemma cone_decompI: "direct_decomp T (map cone ps) \<Longrightarrow> cone_decomp T ps"
  unfolding cone_decomp_def by blast

lemma cone_decompD: "cone_decomp T ps \<Longrightarrow> direct_decomp T (map cone ps)"
  unfolding cone_decomp_def by blast

lemma cone_decomp_cone_subset:
  assumes "cone_decomp T ps" and "hU \<in> set ps"
  shows "cone hU \<subseteq> T"
proof
  fix p
  assume "p \<in> cone hU"
  from assms(2) obtain i where "i < length ps" and hU: "hU = ps ! i" by (metis in_set_conv_nth)
  define qs where "qs = (map 0 ps)[i := p]"
  have "sum_list qs \<in> T"
  proof (intro direct_decompD listsetI)
    from assms(1) show "direct_decomp T (map cone ps)" by (rule cone_decompD)
  next
    fix j
    assume "j < length (map cone ps)"
    with \<open>i < length ps\<close> \<open>p \<in> cone hU\<close> show "qs ! j \<in> map cone ps ! j"
      by (auto simp: qs_def nth_list_update zero_in_cone hU)
  qed (simp add: qs_def)
  also have "sum_list qs = qs ! i" by (rule sum_list_eq_nthI) (simp_all add: qs_def \<open>i < length ps\<close>)
  also from \<open>i < length ps\<close> have "\<dots> = p" by (simp add: qs_def)
  finally show "p \<in> T" .
qed

lemma cone_decomp_indets:
  assumes "cone_decomp T ps" and "T \<subseteq> P[X]" and "(h, U) \<in> set ps"
  shows "h \<in> P[X]" and "h \<noteq> (0::_ \<Rightarrow>\<^sub>0 _::{comm_semiring_1,semiring_no_zero_divisors}) \<Longrightarrow> U \<subseteq> X"
proof -
  from assms(1, 3) have "cone (h, U) \<subseteq> T" by (rule cone_decomp_cone_subset)
  hence "cone (h, U) \<subseteq> P[X]" using assms(2) by (rule subset_trans)
  thus "h \<in> P[X]" and "h \<noteq> 0 \<Longrightarrow> U \<subseteq> X" by (rule cone_subset_PolysD)+
qed

lemma cone_decomp_closed_plus:
  assumes "cone_decomp T ps" and "a \<in> T" and "b \<in> T"
  shows "a + b \<in> T"
proof -
  from assms(1) have dd: "direct_decomp T (map cone ps)" by (rule cone_decompD)
  then obtain qsa where qsa: "qsa \<in> listset (map cone ps)" and a: "a = sum_list qsa" using assms(2)
    by (rule direct_decompE)
  from dd assms(3) obtain qsb where qsb: "qsb \<in> listset (map cone ps)" and b: "b = sum_list qsb"
    by (rule direct_decompE)
  from qsa have "length qsa = length (map cone ps)" by (rule listsetD)
  moreover from qsb have "length qsb = length (map cone ps)" by (rule listsetD)
  ultimately have "a + b = sum_list (map2 (+) qsa qsb)" by (simp only: sum_list_map2_plus a b)
  also from dd have "sum_list (map2 (+) qsa qsb) \<in> T"
  proof (rule direct_decompD)
    from qsa qsb show "map2 (+) qsa qsb \<in> listset (map cone ps)"
    proof (rule listset_closed_map2)
      fix c p1 p2
      assume "c \<in> set (map cone ps)"
      then obtain hU where c: "c = cone hU" by auto
      assume "p1 \<in> c" and "p2 \<in> c"
      thus "p1 + p2 \<in> c" unfolding c by (rule cone_closed_plus)
    qed
  qed
  finally show ?thesis .
qed

lemma cone_decomp_closed_uminus:
  assumes "cone_decomp T ps" and "(a::_ \<Rightarrow>\<^sub>0 _::comm_ring) \<in> T"
  shows "- a \<in> T"
proof -
  from assms(1) have dd: "direct_decomp T (map cone ps)" by (rule cone_decompD)
  then obtain qsa where qsa: "qsa \<in> listset (map cone ps)" and a: "a = sum_list qsa" using assms(2)
    by (rule direct_decompE)
  from qsa have "length qsa = length (map cone ps)" by (rule listsetD)
  have "- a = sum_list (map uminus qsa)" unfolding a by (induct qsa, simp_all)
  also from dd have "\<dots> \<in> T"
  proof (rule direct_decompD)
    from qsa show "map uminus qsa \<in> listset (map cone ps)"
    proof (rule listset_closed_map)
      fix c p
      assume "c \<in> set (map cone ps)"
      then obtain hU where c: "c = cone hU" by auto
      assume "p \<in> c"
      thus "- p \<in> c" unfolding c by (rule cone_closed_uminus)
    qed
  qed
  finally show ?thesis .
qed

corollary cone_decomp_closed_minus:
  assumes "cone_decomp T ps" and "(a::_ \<Rightarrow>\<^sub>0 _::comm_ring) \<in> T" and "b \<in> T"
  shows "a - b \<in> T"
proof -
  from assms(1, 3) have "- b \<in> T" by (rule cone_decomp_closed_uminus)
  with assms(1, 2) have "a + (- b) \<in> T" by (rule cone_decomp_closed_plus)
  thus ?thesis by simp
qed

lemma cone_decomp_Nil: "cone_decomp {0} []"
  by (auto simp: cone_decomp_def intro: direct_decompI_alt)

lemma cone_decomp_singleton: "cone_decomp (cone (t, U)) [(t, U)]"
  by (simp add: cone_decomp_def direct_decomp_singleton)

lemma cone_decomp_append:
  assumes "direct_decomp T [S1, S2]" and "cone_decomp S1 ps" and "cone_decomp S2 qs"
  shows "cone_decomp T (ps @ qs)"
proof (rule cone_decompI)
  from assms(2) have "direct_decomp S1 (map cone ps)" by (rule cone_decompD)
  with assms(1) have "direct_decomp T ([S2] @ map cone ps)" by (rule direct_decomp_direct_decomp)
  hence "direct_decomp T (S2 # map cone ps)" by simp
  moreover from assms(3) have "direct_decomp S2 (map cone qs)" by (rule cone_decompD)
  ultimately have "direct_decomp T (map cone ps @ map cone qs)" by (intro direct_decomp_direct_decomp)
  thus "direct_decomp T (map cone (ps @ qs))" by simp
qed

lemma cone_decomp_concat:
  assumes "direct_decomp T ss" and "length pss = length ss"
    and "\<And>i. i < length ss \<Longrightarrow> cone_decomp (ss ! i) (pss ! i)"
  shows "cone_decomp T (concat pss)"
  using assms(2, 1, 3)
proof (induct pss ss arbitrary: T rule: list_induct2)
  case Nil
  from Nil(1) show ?case by (simp add: cone_decomp_def)
next
  case (Cons ps pss s ss)
  have "0 < length (s # ss)" by simp
  hence "cone_decomp ((s # ss) ! 0) ((ps # pss) ! 0)" by (rule Cons.prems)
  hence "cone_decomp s ps" by simp
  hence *: "direct_decomp s (map cone ps)" by (rule cone_decompD)
  with Cons.prems(1) have "direct_decomp T (ss @ map cone ps)" by (rule direct_decomp_direct_decomp)
  hence 1: "direct_decomp T [sum_list ` listset ss, sum_list ` listset (map cone ps)]"
    and 2: "direct_decomp (sum_list ` listset ss) ss"
    by (auto dest: direct_decomp_appendD intro!: empty_not_in_map_cone)
  note 1
  moreover from 2 have "cone_decomp (sum_list ` listset ss) (concat pss)"
  proof (rule Cons.hyps)
    fix i
    assume "i < length ss"
    hence "Suc i < length (s # ss)" by simp
    hence "cone_decomp ((s # ss) ! Suc i) ((ps # pss) ! Suc i)" by (rule Cons.prems)
    thus "cone_decomp (ss ! i) (pss ! i)" by simp
  qed
  moreover have "cone_decomp (sum_list ` listset (map cone ps)) ps"
  proof (intro cone_decompI direct_decompI refl)
    from * show "inj_on sum_list (listset (map cone ps))"
      by (simp only: direct_decomp_def bij_betw_def)
  qed
  ultimately have "cone_decomp T (concat pss @ ps)" by (rule cone_decomp_append)
  hence "direct_decomp T (map cone (concat pss) @ map cone ps)" by (simp add: cone_decomp_def)
  hence "direct_decomp T (map cone ps @ map cone (concat pss))"
    using perm_append_swap by (rule direct_decomp_perm)
  thus ?case by (simp add: cone_decomp_def)
qed

lemma cone_decomp_map_times:
  assumes "cone_decomp T ps"
  shows "cone_decomp ((*) s ` T) (map (apfst ((*) (s::_ \<Rightarrow>\<^sub>0 _::{comm_ring_1,ring_no_zero_divisors}))) ps)"
proof (rule cone_decompI)
  from assms have "direct_decomp T (map cone ps)" by (rule cone_decompD)
  hence "direct_decomp ((*) s ` T) (map ((`) ((*) s)) (map cone ps))"
    by (rule direct_decomp_image_times) (rule times_canc_left)
  also have "map ((`) ((*) s)) (map cone ps) = map cone (map (apfst ((*) s)) ps)"
    by (simp add: cone_image_times')
  finally show "direct_decomp ((*) s ` T) (map cone (map (apfst ((*) s)) ps))" .
qed

lemma cone_decomp_perm:
  assumes "cone_decomp T ps" and "perm ps qs"
  shows "cone_decomp T qs"
  using assms(1) unfolding cone_decomp_def
proof (rule direct_decomp_perm)
  from assms(2) show "perm (map cone ps) (map cone qs)"
    by (induct ps qs rule: perm.induct) auto
qed

lemma valid_cone_decomp_subset_Polys:
  assumes "valid_decomp X ps" and "cone_decomp T ps"
  shows "T \<subseteq> P[X]"
proof
  fix p
  assume "p \<in> T"
  from assms(2) have "direct_decomp T (map cone ps)" by (rule cone_decompD)
  then obtain qs where "qs \<in> listset (map cone ps)" and p: "p = sum_list qs" using \<open>p \<in> T\<close>
    by (rule direct_decompE)
  from assms(1) this(1) show "p \<in> P[X]" unfolding p
  proof (induct ps arbitrary: qs)
    case Nil
    from Nil(2) show ?case by (simp add: zero_in_Polys)
  next
    case (Cons a ps)
    obtain h U where a: "a = (h, U)" using prod.exhaust by blast
    hence "(h, U) \<in> set (a # ps)" by simp
    with Cons.prems(1) have "h \<in> P[X]" and "U \<subseteq> X" by (rule valid_decompD)+
    hence "cone a \<subseteq> P[X]" unfolding a by (rule cone_subset_PolysI)
    from Cons.prems(1) have "valid_decomp X ps" by (simp add: valid_decomp_def)
    from Cons.prems(2) have "qs \<in> listset (cone a # map cone ps)" by simp
    then obtain q qs' where "q \<in> cone a" and qs': "qs' \<in> listset (map cone ps)" and qs: "qs = q # qs'"
      by (rule listset_ConsE)
    from this(1) \<open>cone a \<subseteq> P[X]\<close> have "q \<in> P[X]" ..
    moreover from \<open>valid_decomp X ps\<close> qs' have "sum_list qs' \<in> P[X]" by (rule Cons.hyps)
    ultimately have "q + sum_list qs' \<in> P[X]" by (rule Polys_closed_plus)
    thus ?case by (simp add: qs)
  qed
qed

lemma homogeneous_set_cone_decomp:
  assumes "cone_decomp T ps" and "hom_decomp ps"
  shows "homogeneous_set T"
proof (rule homogeneous_set_direct_decomp)
  from assms(1) show "direct_decomp T (map cone ps)" by (rule cone_decompD)
next
  fix cn
  assume "cn \<in> set (map cone ps)"
  then obtain hU where "hU \<in> set ps" and cn: "cn = cone hU" unfolding set_map ..
  moreover obtain h U where hU: "hU = (h, U)" using prod.exhaust by blast
  ultimately have "(h, U) \<in> set ps" by simp
  with assms(2) have "homogeneous h" by (rule hom_decompD)
  thus "homogeneous_set cn" unfolding cn hU by (rule homogeneous_set_coneI)
qed

lemma subspace_cone_decomp:
  assumes "cone_decomp T ps"
  shows "phull.subspace (T::(_ \<Rightarrow>\<^sub>0 _::field) set)"
proof (rule phull.subspace_direct_decomp)
  from assms show "direct_decomp T (map cone ps)" by (rule cone_decompD)
next
  fix cn
  assume "cn \<in> set (map cone ps)"
  then obtain hU where "hU \<in> set ps" and cn: "cn = cone hU" unfolding set_map ..
  show "phull.subspace cn" unfolding cn by (rule subspace_cone)
qed

definition pos_decomp :: "((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) list \<Rightarrow> ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) list"
    ("(_\<^sub>+)" [1000] 999)
    where "pos_decomp ps = filter (\<lambda>p. snd p \<noteq> {}) ps"

definition standard_decomp :: "nat \<Rightarrow> ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) \<times> 'x set) list \<Rightarrow> bool"
  where "standard_decomp k ps \<longleftrightarrow> (\<forall>(h, U)\<in>set (ps\<^sub>+). k \<le> poly_deg h \<and>
                                      (\<forall>d. k \<le> d \<longrightarrow> d \<le> poly_deg h \<longrightarrow>
                                        (\<exists>(h', U')\<in>set ps. poly_deg h' = d \<and> card U \<le> card U')))"

lemma pos_decomp_Nil [simp]: "[]\<^sub>+ = []"
  by (simp add: pos_decomp_def)

lemma pos_decomp_subset: "set (ps\<^sub>+) \<subseteq> set ps"
  by (simp add: pos_decomp_def)

lemma pos_decomp_append: "(ps @ qs)\<^sub>+ = ps\<^sub>+ @ qs\<^sub>+"
  by (simp add: pos_decomp_def)

lemma pos_decomp_concat: "(concat pss)\<^sub>+ = concat (map pos_decomp pss)"
  by (metis (mono_tags, lifting) filter_concat map_eq_conv pos_decomp_def)

lemma pos_decomp_map: "(map (apfst f) ps)\<^sub>+ = map (apfst f) (ps\<^sub>+)"
  by (metis (mono_tags, lifting) pos_decomp_def filter_cong filter_map o_apply snd_apfst)

lemma card_Diff_pos_decomp: "card {(h, U) \<in> set qs - set (qs\<^sub>+). P h} = card {h. (h, {}) \<in> set qs \<and> P h}"
proof -
  have "{h. (h, {}) \<in> set qs \<and> P h} = fst ` {(h, U) \<in> set qs - set (qs\<^sub>+). P h}"
    by (auto simp: pos_decomp_def image_Collect)
  also have "card \<dots> = card {(h, U) \<in> set qs - set (qs\<^sub>+). P h}"
    by (rule card_image, auto simp: pos_decomp_def intro: inj_onI)
  finally show ?thesis by (rule sym)
qed

lemma standard_decompI:
  assumes "\<And>h U. (h, U) \<in> set (ps\<^sub>+) \<Longrightarrow> k \<le> poly_deg h"
    and "\<And>h U d. (h, U) \<in> set (ps\<^sub>+) \<Longrightarrow> k \<le> d \<Longrightarrow> d \<le> poly_deg h \<Longrightarrow>
          (\<exists>h' U'. (h', U') \<in> set ps \<and> poly_deg h' = d \<and> card U \<le> card U')"
  shows "standard_decomp k ps"
  unfolding standard_decomp_def using assms by blast

lemma standard_decompD: "standard_decomp k ps \<Longrightarrow> (h, U) \<in> set (ps\<^sub>+) \<Longrightarrow> k \<le> poly_deg h"
  unfolding standard_decomp_def by blast

lemma standard_decompE:
  assumes "standard_decomp k ps" and "(h, U) \<in> set (ps\<^sub>+)" and "k \<le> d" and "d \<le> poly_deg h"
  obtains h' U' where "(h', U') \<in> set ps" and "poly_deg h' = d" and "card U \<le> card U'"
  using assms unfolding standard_decomp_def by blast

lemma standard_decomp_Nil: "ps\<^sub>+ = [] \<Longrightarrow> standard_decomp k ps"
  by (simp add: standard_decomp_def)

lemma standard_decomp_singleton: "standard_decomp (poly_deg h) [(h, U)]"
  by (simp add: standard_decomp_def pos_decomp_def)

lemma standard_decomp_concat:
  assumes "\<And>ps. ps \<in> set pss \<Longrightarrow> standard_decomp k ps"
  shows "standard_decomp k (concat pss)"
proof (rule standard_decompI)
  fix h U
  assume "(h, U) \<in> set ((concat pss)\<^sub>+)"
  then obtain ps where "ps \<in> set pss" and *: "(h, U) \<in> set (ps\<^sub>+)" by (auto simp: pos_decomp_concat)
  from this(1) have "standard_decomp k ps" by (rule assms)
  thus "k \<le> poly_deg h" using * by (rule standard_decompD)

  fix d
  assume "k \<le> d" and "d \<le> poly_deg h"
  with \<open>standard_decomp k ps\<close> * obtain h' U' where "(h', U') \<in> set ps" and "poly_deg h' = d"
    and "card U \<le> card U'" by (rule standard_decompE)
  note this(2, 3)
  moreover from \<open>(h', U') \<in> set ps\<close> \<open>ps \<in> set pss\<close> have "(h', U') \<in> set (concat pss)" by auto
  ultimately show "\<exists>h' U'. (h', U') \<in> set (concat pss) \<and> poly_deg h' = d \<and> card U \<le> card U'"
    by blast
qed

corollary standard_decomp_append:
  assumes "standard_decomp k ps" and "standard_decomp k qs"
  shows "standard_decomp k (ps @ qs)"
proof -
  have "standard_decomp k (concat [ps, qs])" by (rule standard_decomp_concat) (auto simp: assms)
  thus ?thesis by simp
qed

lemma standard_decomp_map_times:
  assumes "standard_decomp k ps" and "valid_decomp X ps" and "s \<noteq> (0::_ \<Rightarrow>\<^sub>0 'a::semiring_no_zero_divisors)"
  shows "standard_decomp (k + poly_deg s) (map (apfst ((*) s)) ps)"
proof (rule standard_decompI)
  fix h U
  assume "(h, U) \<in> set ((map (apfst ((*) s)) ps)\<^sub>+)"
  then obtain h0 where 1: "(h0, U) \<in> set (ps\<^sub>+)" and h: "h = s * h0" by (fastforce simp: pos_decomp_map)
  from this(1) pos_decomp_subset have "(h0, U) \<in> set ps" ..
  with assms(2) have "h0 \<noteq> 0" by (rule valid_decompD)
  with assms(3) have deg_h: "poly_deg h = poly_deg s + poly_deg h0" unfolding h by (rule poly_deg_times)
  moreover from assms(1) 1 have "k \<le> poly_deg h0" by (rule standard_decompD)
  ultimately show "k + poly_deg s \<le> poly_deg h" by simp

  fix d
  assume "k + poly_deg s \<le> d" and "d \<le> poly_deg h"
  hence "k \<le> d - poly_deg s" and "d - poly_deg s \<le> poly_deg h0" by (simp_all add: deg_h)
  with assms(1) 1 obtain h' U' where 2: "(h', U') \<in> set ps" and "poly_deg h' = d - poly_deg s"
    and "card U \<le> card U'" by (rule standard_decompE)
  from assms(2) this(1) have "h' \<noteq> 0" by (rule valid_decompD)
  with assms(3) have deg_h': "poly_deg (s * h') = poly_deg s + poly_deg h'" by (rule poly_deg_times)
  from 2 have "(s * h', U') \<in> set (map (apfst ((*) s)) ps)" by force
  moreover from \<open>k + poly_deg s \<le> d\<close> \<open>poly_deg h' = d - poly_deg s\<close> have "poly_deg (s * h') = d"
    by (simp add: deg_h')
  ultimately show "\<exists>h' U'. (h', U') \<in> set (map (apfst ((*) s)) ps) \<and> poly_deg h' = d \<and> card U \<le> card U'"
    using \<open>card U \<le> card U'\<close> by fastforce
qed

lemma standard_decomp_nonempty_unique:
  assumes "finite X" and "valid_decomp X ps" and "standard_decomp k ps" and "ps\<^sub>+ \<noteq> []"
  shows "k = Min (poly_deg ` fst ` set (ps\<^sub>+))"
proof -
  let ?A = "poly_deg ` fst ` set (ps\<^sub>+)"
  define m where "m = Min ?A"
  have "finite ?A" by simp
  moreover from assms(4) have "?A \<noteq> {}" by simp
  ultimately have "m \<in> ?A" unfolding m_def by (rule Min_in)
  then obtain h U where "(h, U) \<in> set (ps\<^sub>+)" and m: "m = poly_deg h" by fastforce
  have m_min: "m \<le> poly_deg h'" if "(h', U') \<in> set (ps\<^sub>+)" for h' U'
  proof -
    from that have "poly_deg (fst (h', U')) \<in> ?A" by (intro imageI)
    with \<open>finite ?A\<close> have "m \<le> poly_deg (fst (h', U'))" unfolding m_def by (rule Min_le)
    thus ?thesis by simp
  qed
  show ?thesis
  proof (rule linorder_cases)
    assume "k < m"
    hence "k \<le> poly_deg h" by (simp add: m)
    with assms(3) \<open>(h, U) \<in> set (ps\<^sub>+)\<close> le_refl obtain h' U'
      where "(h', U') \<in> set ps" and "poly_deg h' = k" and "card U \<le> card U'" by (rule standard_decompE)
    from this(2) \<open>k < m\<close> have "\<not> m \<le> poly_deg h'" by simp
    with m_min have "(h', U') \<notin> set (ps\<^sub>+)" by blast
    with \<open>(h', U') \<in> set ps\<close> have "U' = {}" by (simp add: pos_decomp_def)
    with \<open>card U \<le> card U'\<close> have "U = {} \<or> infinite U" by (simp add: card_eq_0_iff)
    thus ?thesis
    proof
      assume "U = {}"
      with \<open>(h, U) \<in> set (ps\<^sub>+)\<close> show ?thesis by (simp add: pos_decomp_def)
    next
      assume "infinite U"
      moreover from assms(1, 2) have "finite U"
      proof (rule valid_decompD_finite)
        from \<open>(h, U) \<in> set (ps\<^sub>+)\<close> show "(h, U) \<in> set ps" by (simp add: pos_decomp_def)
      qed
      ultimately show ?thesis ..
    qed
  next
    assume "m < k"
    hence "\<not> k \<le> m" by simp
    moreover from assms(3) \<open>(h, U) \<in> set (ps\<^sub>+)\<close> have "k \<le> m" unfolding m by (rule standard_decompD)
    ultimately show ?thesis ..
  qed (simp only: m_def)
qed

lemma standard_decomp_SucE:
  assumes "finite X" and "U \<subseteq> X" and "h \<in> P[X]" and "h \<noteq> (0::_ \<Rightarrow>\<^sub>0 'a::{comm_ring_1,ring_no_zero_divisors})"
  obtains ps where "valid_decomp X ps" and "cone_decomp (cone (h, U)) ps"
    and "standard_decomp (Suc (poly_deg h)) ps"
    and "is_monomial h \<Longrightarrow> punit.lc h = 1 \<Longrightarrow> monomial_decomp ps" and "homogeneous h \<Longrightarrow> hom_decomp ps"
proof -
  from assms(2, 1) have "finite U" by (rule finite_subset)
  thus ?thesis using assms(2) that
  proof (induct U arbitrary: thesis rule: finite_induct)
    case empty
    from assms(3, 4) have "valid_decomp X [(h, {})]" by (simp add: valid_decomp_def)
    moreover note cone_decomp_singleton
    moreover have "standard_decomp (Suc (poly_deg h)) [(h, {})]"
      by (rule standard_decomp_Nil) (simp add: pos_decomp_def)
    ultimately show ?case by (rule empty) (simp_all add: monomial_decomp_def hom_decomp_def)
  next
    case (insert x U)
    from insert.prems(1) have "x \<in> X" and "U \<subseteq> X" by simp_all
    from this(2) obtain ps where 0: "valid_decomp X ps" and 1: "cone_decomp (cone (h, U)) ps"
      and 2: "standard_decomp (Suc (poly_deg h)) ps"
      and 3: "is_monomial h \<Longrightarrow> punit.lc h = 1 \<Longrightarrow> monomial_decomp ps"
      and 4: "homogeneous h \<Longrightarrow> hom_decomp ps" by (rule insert.hyps) blast
    let ?x = "monomial (1::'a) (Poly_Mapping.single x (Suc 0))"
    have "?x \<noteq> 0" by (simp add: monomial_0_iff)
    with assms(4) have deg: "poly_deg (?x * h) = Suc (poly_deg h)"
      by (simp add: poly_deg_times poly_deg_monomial deg_pm_single)
    define qs where "qs = [(?x * h, insert x U)]"
    show ?case
    proof (rule insert.prems)
      from \<open>x \<in> X\<close> have "?x \<in> P[X]" by (intro Polys_closed_monomial PPs_closed_single)
      hence "?x * h \<in> P[X]" using assms(3) by (rule Polys_closed_times)
      moreover from \<open>?x \<noteq> 0\<close> assms(4) have "?x * h \<noteq> 0" by (rule times_not_zero)
      ultimately have "valid_decomp X qs" using insert.hyps(1) \<open>x \<in> X\<close> \<open>U \<subseteq> X\<close>
        by (simp add: qs_def valid_decomp_def)
      with 0 show "valid_decomp X (ps @ qs)" by (rule valid_decomp_append)
    next
      show "cone_decomp (cone (h, insert x U)) (ps @ qs)"
      proof (rule cone_decomp_append)
        show "direct_decomp (cone (h, insert x U)) [cone (h, U), cone (?x * h, insert x U)]"
          using insert.hyps(2) by (rule direct_decomp_cone_insert)
      next
        show "cone_decomp (cone (?x * h, insert x U)) qs"
          by (simp add: qs_def cone_decomp_singleton)
      qed (fact 1)
    next
      from standard_decomp_singleton[of "?x * h" "insert x U"]
      have "standard_decomp (Suc (poly_deg h)) qs" by (simp add: deg qs_def)
      with 2 show "standard_decomp (Suc (poly_deg h)) (ps @ qs)" by (rule standard_decomp_append)
    next
      assume "is_monomial h" and "punit.lc h = 1"
      hence "monomial_decomp ps" by (rule 3)
      moreover have "monomial_decomp qs"
      proof -
        have "is_monomial (?x * h)"
          by (metis \<open>is_monomial h\<close> is_monomial_monomial monomial_is_monomial mult.commute
              mult.right_neutral mult_single)
        thus ?thesis by (simp add: monomial_decomp_def qs_def lc_times \<open>punit.lc h = 1\<close>)
      qed
      ultimately show "monomial_decomp (ps @ qs)" by (simp only: monomial_decomp_append_iff)
    next
      assume "homogeneous h"
      hence "hom_decomp ps" by (rule 4)
      moreover from \<open>homogeneous h\<close> have "hom_decomp qs"
        by (simp add: hom_decomp_def qs_def homogeneous_times)
      ultimately show "hom_decomp (ps @ qs)" by (simp only: hom_decomp_append_iff)
    qed
  qed
qed

lemma standard_decomp_geE:
  assumes "finite X" and "valid_decomp X ps"
    and "cone_decomp (T::(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::{comm_ring_1,ring_no_zero_divisors}) set) ps"
    and "standard_decomp k ps" and "k \<le> d"
  obtains qs where "valid_decomp X qs" and "cone_decomp T qs" and "standard_decomp d qs"
    and "monomial_decomp ps \<Longrightarrow> monomial_decomp qs" and "hom_decomp ps \<Longrightarrow> hom_decomp qs"
proof -
  have "\<exists>qs. valid_decomp X qs \<and> cone_decomp T qs \<and> standard_decomp (k + i) qs \<and>
              (monomial_decomp ps \<longrightarrow> monomial_decomp qs) \<and> (hom_decomp ps \<longrightarrow> hom_decomp qs)" for i
  proof (induct i)
    case 0
    from assms(2, 3, 4) show ?case unfolding add_0_right by blast
  next
    case (Suc i)
    then obtain qs where 0: "valid_decomp X qs" and 1: "cone_decomp T qs"
      and 2: "standard_decomp (k + i) qs" and 3: "monomial_decomp ps \<Longrightarrow> monomial_decomp qs"
      and 4: "hom_decomp ps \<Longrightarrow> hom_decomp qs" by blast
    let ?P = "\<lambda>hU. poly_deg (fst hU) \<noteq> k + i"
    define rs where "rs = filter (- ?P) qs"
    define ss where "ss = filter ?P qs"

    have "set rs \<subseteq> set qs" by (auto simp: rs_def)
    have "set ss \<subseteq> set qs" by (auto simp: ss_def)

    define f where "f = (\<lambda>hU. SOME ps'. valid_decomp X ps' \<and> cone_decomp (cone hU) ps' \<and>
                                        standard_decomp (Suc (poly_deg ((fst hU)::('x \<Rightarrow>\<^sub>0 _) \<Rightarrow>\<^sub>0 'a))) ps' \<and>
                                        (monomial_decomp ps \<longrightarrow> monomial_decomp ps') \<and>
                                        (hom_decomp ps \<longrightarrow> hom_decomp ps'))"
    have "valid_decomp X (f hU) \<and> cone_decomp (cone hU) (f hU) \<and> standard_decomp (Suc (k + i)) (f hU) \<and>
          (monomial_decomp ps \<longrightarrow> monomial_decomp (f hU)) \<and> (hom_decomp ps \<longrightarrow> hom_decomp (f hU))"
      if "hU \<in> set rs" for hU
    proof -
      obtain h U where hU: "hU = (h, U)" using prod.exhaust by blast
      with that have eq: "poly_deg (fst hU) = k + i" by (simp add: rs_def)
      from that \<open>set rs \<subseteq> set qs\<close> have "(h, U) \<in> set qs" unfolding hU ..
      with 0 have "U \<subseteq> X" and "h \<in> P[X]" and "h \<noteq> 0" by (rule valid_decompD)+
      with assms(1) obtain ps' where "valid_decomp X ps'" and "cone_decomp (cone (h, U)) ps'"
        and "standard_decomp (Suc (poly_deg h)) ps'"
        and md: "is_monomial h \<Longrightarrow> punit.lc h = 1 \<Longrightarrow> monomial_decomp ps'"
        and hd: "homogeneous h \<Longrightarrow> hom_decomp ps'" by (rule standard_decomp_SucE) blast
      note this(1-3)
      moreover have "monomial_decomp ps'" if "monomial_decomp ps"
      proof -
        from that have "monomial_decomp qs" by (rule 3)
        hence "is_monomial h" and "punit.lc h = 1" using \<open>(h, U) \<in> set qs\<close> by (rule monomial_decompD)+
        thus ?thesis by (rule md)
      qed
      moreover have "hom_decomp ps'" if "hom_decomp ps"
      proof -
        from that have "hom_decomp qs" by (rule 4)
        hence "homogeneous h" using \<open>(h, U) \<in> set qs\<close> by (rule hom_decompD)
        thus ?thesis by (rule hd)
      qed
      ultimately have "valid_decomp X ps' \<and> cone_decomp (cone hU) ps' \<and>
          standard_decomp (Suc (poly_deg (fst hU))) ps' \<and> (monomial_decomp ps \<longrightarrow> monomial_decomp ps') \<and>
          (hom_decomp ps \<longrightarrow> hom_decomp ps')" by (simp add: hU)
      thus ?thesis unfolding f_def eq by (rule someI)
    qed
    hence f1: "\<And>ps. ps \<in> set (map f rs) \<Longrightarrow> valid_decomp X ps"
      and f2: "\<And>hU. hU \<in> set rs \<Longrightarrow> cone_decomp (cone hU) (f hU)"
      and f3: "\<And>ps. ps \<in> set (map f rs) \<Longrightarrow> standard_decomp (Suc (k + i)) ps"
      and f4: "\<And>ps'. monomial_decomp ps \<Longrightarrow> ps' \<in> set (map f rs) \<Longrightarrow> monomial_decomp ps'"
      and f5: "\<And>ps'. hom_decomp ps \<Longrightarrow> ps' \<in> set (map f rs) \<Longrightarrow> hom_decomp ps'" by auto

    define rs' where "rs' = concat (map f rs)"
    show ?case unfolding add_Suc_right
    proof (intro exI conjI impI)
      have "valid_decomp X ss"
      proof (rule valid_decompI)
        fix h U
        assume "(h, U) \<in> set ss"
        hence "(h, U) \<in> set qs" using \<open>set ss \<subseteq> set qs\<close> ..
        with 0 show "h \<in> P[X]" and "h \<noteq> 0" and "U \<subseteq> X" by (rule valid_decompD)+
      qed
      moreover have "valid_decomp X rs'"
        unfolding rs'_def using f1 by (rule valid_decomp_concat)
      ultimately show "valid_decomp X (ss @ rs')" by (rule valid_decomp_append)
    next
      from 1 have "direct_decomp T (map cone qs)" by (rule cone_decompD)
      hence "direct_decomp T ((map cone ss) @ (map cone rs))" unfolding ss_def rs_def
        by (rule direct_decomp_split_map)
      hence ss: "cone_decomp (sum_list ` listset (map cone ss)) ss"
        and "cone_decomp (sum_list ` listset (map cone rs)) rs"
        and T: "direct_decomp T [sum_list ` listset (map cone ss), sum_list ` listset (map cone rs)]"
        by (auto simp: cone_decomp_def dest: direct_decomp_appendD intro!: empty_not_in_map_cone)
      from this(2) have "direct_decomp (sum_list ` listset (map cone rs)) (map cone rs)"
        by (rule cone_decompD)
      hence "cone_decomp (sum_list ` listset (map cone rs)) rs'" unfolding rs'_def
      proof (rule cone_decomp_concat)
        fix i
        assume *: "i < length (map cone rs)"
        hence "rs ! i \<in> set rs" by simp
        hence "cone_decomp (cone (rs ! i)) (f (rs ! i))" by (rule f2)
        with * show "cone_decomp (map cone rs ! i) (map f rs ! i)" by simp
      qed simp
      with T ss show "cone_decomp T (ss @ rs')" by (rule cone_decomp_append)
    next
      have "standard_decomp (Suc (k + i)) ss"
      proof (rule standard_decompI)
        fix h U
        assume "(h, U) \<in> set (ss\<^sub>+)"
        hence "(h, U) \<in> set (qs\<^sub>+)" and "poly_deg h \<noteq> k + i" by (simp_all add: pos_decomp_def ss_def)
        from 2 this(1) have "k + i \<le> poly_deg h" by (rule standard_decompD)
        with \<open>poly_deg h \<noteq> k + i\<close> show "Suc (k + i) \<le> poly_deg h" by simp
  
        fix d'
        assume "Suc (k + i) \<le> d'" and "d' \<le> poly_deg h"
        from this(1) have "k + i \<le> d'" and "d' \<noteq> k + i" by simp_all
        from 2 \<open>(h, U) \<in> set (qs\<^sub>+)\<close> this(1) obtain h' U'
          where "(h', U') \<in> set qs" and "poly_deg h' = d'" and "card U \<le> card U'"
          using \<open>d' \<le> poly_deg h\<close> by (rule standard_decompE)
        moreover from \<open>d' \<noteq> k + i\<close> this(1, 2) have "(h', U') \<in> set ss" by (simp add: ss_def)
        ultimately show "\<exists>h' U'. (h', U') \<in> set ss \<and> poly_deg h' = d' \<and> card U \<le> card U'" by blast
      qed
      moreover have "standard_decomp (Suc (k + i)) rs'"
        unfolding rs'_def using f3 by (rule standard_decomp_concat)
      ultimately show "standard_decomp (Suc (k + i)) (ss @ rs')" by (rule standard_decomp_append)
    next
      assume *: "monomial_decomp ps"
      hence "monomial_decomp qs" by (rule 3)
      hence "monomial_decomp ss" by (simp add: monomial_decomp_def ss_def)
      moreover have "monomial_decomp rs'"
        unfolding rs'_def using f4[OF *] by (rule monomial_decomp_concat)
      ultimately show "monomial_decomp (ss @ rs')" by (simp only: monomial_decomp_append_iff)
    next
      assume *: "hom_decomp ps"
      hence "hom_decomp qs" by (rule 4)
      hence "hom_decomp ss" by (simp add: hom_decomp_def ss_def)
      moreover have "hom_decomp rs'" unfolding rs'_def using f5[OF *] by (rule hom_decomp_concat)
      ultimately show "hom_decomp (ss @ rs')" by (simp only: hom_decomp_append_iff)
    qed
  qed
  then obtain qs where 1: "valid_decomp X qs" and 2: "cone_decomp T qs"
    and "standard_decomp (k + (d - k)) qs" and 4: "monomial_decomp ps \<Longrightarrow> monomial_decomp qs"
    and 5: "hom_decomp ps \<Longrightarrow> hom_decomp qs" by blast
  from this(3) assms(5) have "standard_decomp d qs" by simp
  with 1 2 show ?thesis using 4 5 ..
qed

subsection \<open>Splitting w.r.t. Ideals\<close>

context
  fixes X :: "'x set"
begin

definition splits_wrt :: "(((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) list \<times> ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) list) \<Rightarrow>
                          (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_ring_1) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set \<Rightarrow> bool"
  where "splits_wrt pqs T F \<longleftrightarrow> cone_decomp T (fst pqs @ snd pqs) \<and>
                                (\<forall>hU\<in>set (fst pqs). cone hU \<subseteq> ideal F \<inter> P[X]) \<and>
                                (\<forall>(h, U)\<in>set (snd pqs). cone (h, U) \<subseteq> P[X] \<and> cone (h, U) \<inter> ideal F = {0})"

lemma splits_wrtI:
  assumes "cone_decomp T (ps @ qs)"
    and "\<And>h U. (h, U) \<in> set ps \<Longrightarrow> cone (h, U) \<subseteq> P[X]" and "\<And>h U. (h, U) \<in> set ps \<Longrightarrow> h \<in> ideal F"
    and "\<And>h U. (h, U) \<in> set qs \<Longrightarrow> cone (h, U) \<subseteq> P[X]"
    and "\<And>h U a. (h, U) \<in> set qs \<Longrightarrow> a \<in> cone (h, U) \<Longrightarrow> a \<in> ideal F \<Longrightarrow> a = 0"
  shows "splits_wrt (ps, qs) T F"
  unfolding splits_wrt_def fst_conv snd_conv
proof (intro conjI ballI)
  fix hU
  assume "hU \<in> set ps"
  moreover obtain h U where hU: "hU = (h, U)" using prod.exhaust by blast
  ultimately have "(h, U) \<in> set ps" by simp
  hence "cone (h, U) \<subseteq> P[X]" and "h \<in> ideal F" by (rule assms)+
  from _ this(1) show "cone hU \<subseteq> ideal F \<inter> P[X]" unfolding hU
  proof (rule Int_greatest)
    show "cone (h, U) \<subseteq> ideal F"
    proof
      fix a
      assume "a \<in> cone (h, U)"
      then obtain a' where "a' \<in> P[U]" and a: "a = a' * h" by (rule coneE)
      from \<open>h \<in> ideal F\<close> show "a \<in> ideal F" unfolding a by (rule ideal.span_scale)
    qed
  qed
next
  fix hU
  assume "hU \<in> set qs"
  moreover obtain h U where hU: "hU = (h, U)" using prod.exhaust by blast
  ultimately have "(h, U) \<in> set qs" by simp
  hence "cone (h, U) \<subseteq> P[X]" and "\<And>a. a \<in> cone (h, U) \<Longrightarrow> a \<in> ideal F \<Longrightarrow> a = 0" by (rule assms)+
  moreover have "0 \<in> cone (h, U) \<inter> ideal F"
    by (simp add: zero_in_cone ideal.span_zero)
  ultimately show "case hU of (h, U) \<Rightarrow> cone (h, U) \<subseteq> P[X] \<and> cone (h, U) \<inter> ideal F = {0}"
    by (fastforce simp: hU)
qed (fact assms)+

lemma splits_wrtI_valid_decomp:
  assumes "valid_decomp X ps" and "valid_decomp X qs" and "cone_decomp T (ps @ qs)"
    and "\<And>h U. (h, U) \<in> set ps \<Longrightarrow> h \<in> ideal F"
    and "\<And>h U a. (h, U) \<in> set qs \<Longrightarrow> a \<in> cone (h, U) \<Longrightarrow> a \<in> ideal F \<Longrightarrow> a = 0"
  shows "splits_wrt (ps, qs) T F"
  using assms(3) _ _ _ assms(5)
proof (rule splits_wrtI)
  fix h U
  assume "(h, U) \<in> set ps"
  thus "h \<in> ideal F" by (rule assms(4))
  from assms(1) \<open>(h, U) \<in> set ps\<close> have "h \<in> P[X]" and "U \<subseteq> X" by (rule valid_decompD)+
  thus "cone (h, U) \<subseteq> P[X]" by (rule cone_subset_PolysI)
next
  fix h U
  assume "(h, U) \<in> set qs"
  with assms(2) have "h \<in> P[X]" by (rule valid_decompD)
  moreover from assms(2) \<open>(h, U) \<in> set qs\<close> have "U \<subseteq> X" by (rule valid_decompD)
  ultimately show "cone (h, U) \<subseteq> P[X]" by (rule cone_subset_PolysI)
qed

lemma splits_wrtD:
  assumes "splits_wrt (ps, qs) T F"
  shows "cone_decomp T (ps @ qs)" and "hU \<in> set ps \<Longrightarrow> cone hU \<subseteq> ideal F \<inter> P[X]"
    and "hU \<in> set qs \<Longrightarrow> cone hU \<subseteq> P[X]" and "hU \<in> set qs \<Longrightarrow> cone hU \<inter> ideal F = {0}"
  using assms by (fastforce simp: splits_wrt_def)+

lemma splits_wrt_image_sum_list_fst_subset:
  assumes "splits_wrt (ps, qs) T F"
  shows "sum_list ` listset (map cone ps) \<subseteq> ideal F \<inter> P[X]"
proof
  fix x
  assume x_in: "x \<in> sum_list ` listset (map cone ps)"
  have "listset (map cone ps) \<subseteq> listset (map (\<lambda>_. ideal F \<inter> P[X]) ps)"
  proof (rule listset_mono)
    fix i
    assume i: "i < length (map (\<lambda>_. ideal F \<inter> P[X]) ps)"
    hence "ps ! i \<in> set ps" by simp
    with assms(1) have "cone (ps ! i) \<subseteq> ideal F \<inter> P[X]" by (rule splits_wrtD)
    with i show "map cone ps ! i \<subseteq> map (\<lambda>_. ideal F \<inter> P[X]) ps ! i" by simp
  qed simp
  hence "sum_list ` listset (map cone ps) \<subseteq> sum_list ` listset (map (\<lambda>_. ideal F \<inter> P[X]) ps)"
    by (rule image_mono)
  with x_in have "x \<in> sum_list ` listset (map (\<lambda>_. ideal F \<inter> P[X]) ps)" ..
  then obtain xs where xs: "xs \<in> listset (map (\<lambda>_. ideal F \<inter> P[X]) ps)" and x: "x = sum_list xs" ..
  have 1: "y \<in> ideal F \<inter> P[X]" if "y \<in> set xs" for y
  proof -
    from that obtain i where "i < length xs" and y: "y = xs ! i" by (metis in_set_conv_nth)
    moreover from xs have "length xs = length (map (\<lambda>_. ideal F \<inter> P[X]) ps)"
      by (rule listsetD)
    ultimately have "i < length (map (\<lambda>_. ideal F \<inter> P[X]) ps)" by simp
    moreover from xs this have "xs ! i \<in> (map (\<lambda>_. ideal F \<inter> P[X]) ps) ! i" by (rule listsetD)
    ultimately show "y \<in> ideal F \<inter> P[X]" by (simp add: y)
  qed
  show "x \<in> ideal F \<inter> P[X]" unfolding x
  proof
    show "sum_list xs \<in> ideal F"
    proof (rule ideal.span_closed_sum_list[simplified])
      fix y
      assume "y \<in> set xs"
      hence "y \<in> ideal F \<inter> P[X]" by (rule 1)
      thus "y \<in> ideal F" by simp
    qed
  next
    show "sum_list xs \<in> P[X]"
    proof (rule Polys_closed_sum_list)
      fix y
      assume "y \<in> set xs"
      hence "y \<in> ideal F \<inter> P[X]" by (rule 1)
      thus "y \<in> P[X]" by simp
    qed
  qed
qed

lemma splits_wrt_image_sum_list_snd_subset:
  assumes "splits_wrt (ps, qs) T F"
  shows "sum_list ` listset (map cone qs) \<subseteq> P[X]"
proof
  fix x
  assume x_in: "x \<in> sum_list ` listset (map cone qs)"
  have "listset (map cone qs) \<subseteq> listset (map (\<lambda>_. P[X]) qs)"
  proof (rule listset_mono)
    fix i
    assume i: "i < length (map (\<lambda>_. P[X]) qs)"
    hence "qs ! i \<in> set qs" by simp
    with assms(1) have "cone (qs ! i) \<subseteq> P[X]" by (rule splits_wrtD)
    with i show "map cone qs ! i \<subseteq> map (\<lambda>_. P[X]) qs ! i" by simp
  qed simp
  hence "sum_list ` listset (map cone qs) \<subseteq> sum_list ` listset (map (\<lambda>_. P[X]) qs)"
    by (rule image_mono)
  with x_in have "x \<in> sum_list ` listset (map (\<lambda>_. P[X]) qs)" ..
  then obtain xs where xs: "xs \<in> listset (map (\<lambda>_. P[X]) qs)" and x: "x = sum_list xs" ..
  show "x \<in> P[X]" unfolding x
  proof (rule Polys_closed_sum_list)
    fix y
    assume "y \<in> set xs"
    then obtain i where "i < length xs" and y: "y = xs ! i" by (metis in_set_conv_nth)
    moreover from xs have "length xs = length (map (\<lambda>_. P[X]::(_ \<Rightarrow>\<^sub>0 'a) set) qs)"
      by (rule listsetD)
    ultimately have "i < length (map (\<lambda>_. P[X]) qs)" by simp
    moreover from xs this have "xs ! i \<in> (map (\<lambda>_. P[X]) qs) ! i" by (rule listsetD)
    ultimately show "y \<in> P[X]" by (simp add: y)
  qed
qed

lemma splits_wrt_cone_decomp_1:
  assumes "splits_wrt (ps, qs) T F" and "monomial_decomp qs" and "is_monomial_set (F::(_ \<Rightarrow>\<^sub>0 'a::field) set)"
        \<comment>\<open>The last two assumptions are missing in the paper.\<close>
  shows "cone_decomp (T \<inter> ideal F) ps"
proof -
  from assms(1) have *: "cone_decomp T (ps @ qs)" by (rule splits_wrtD)
  hence "direct_decomp T (map cone ps @ map cone qs)" by (simp add: cone_decomp_def)
  hence 1: "direct_decomp (sum_list ` listset (map cone ps)) (map cone ps)"
    and 2: "direct_decomp T [sum_list ` listset (map cone ps), sum_list ` listset (map cone qs)]"
    by (auto dest: direct_decomp_appendD intro!: empty_not_in_map_cone)
  let ?ss = "[sum_list ` listset (map cone ps), sum_list ` listset (map cone qs)]"
  show ?thesis
  proof (intro cone_decompI direct_decompI)
    from 1 show "inj_on sum_list (listset (map cone ps))" by (simp only: direct_decomp_def bij_betw_def)
  next
    from assms(1) have "sum_list ` listset (map cone ps) \<subseteq> ideal F \<inter> P[X]"
      by (rule splits_wrt_image_sum_list_fst_subset)
    hence sub: "sum_list ` listset (map cone ps) \<subseteq> ideal F" by simp
    show "sum_list ` listset (map cone ps) = T \<inter> ideal F"
    proof (rule set_eqI)
      fix x
      show "x \<in> sum_list ` listset (map cone ps) \<longleftrightarrow> x \<in> T \<inter> ideal F"
      proof
        assume x_in: "x \<in> sum_list ` listset (map cone ps)"
        show "x \<in> T \<inter> ideal F"
        proof (intro IntI)
          have "map (\<lambda>_. 0) qs \<in> listset (map cone qs)" (is "?ys \<in> _")
            by (induct qs) (auto intro: listset_ConsI zero_in_cone simp del: listset.simps(2))
          hence "sum_list ?ys \<in> sum_list ` listset (map cone qs)" by (rule imageI)
          hence "0 \<in> sum_list ` listset (map cone qs)" by simp
          with x_in have "[x, 0] \<in> listset ?ss" using refl by (rule listset_doubletonI)
          with 2 have "sum_list [x, 0] \<in> T" by (rule direct_decompD)
          thus "x \<in> T" by simp
        next
          from x_in sub show "x \<in> ideal F" ..
        qed
      next
        assume "x \<in> T \<inter> ideal F"
        hence "x \<in> T" and "x \<in> ideal F" by simp_all
        from 2 this(1) obtain xs where "xs \<in> listset ?ss" and x: "x = sum_list xs"
          by (rule direct_decompE)
        from this(1) obtain p q where p: "p \<in> sum_list ` listset (map cone ps)"
          and q: "q \<in> sum_list ` listset (map cone qs)" and xs: "xs = [p, q]"
          by (rule listset_doubletonE)
        from \<open>x \<in> ideal F\<close> have "p + q \<in> ideal F" by (simp add: x xs)
        moreover from p sub have "p \<in> ideal F" ..
        ultimately have "p + q - p \<in> ideal F" by (rule ideal.span_diff)
        hence "q \<in> ideal F" by simp
        have "q = 0"
        proof (rule ccontr)
          assume "q \<noteq> 0"
          hence "keys q \<noteq> {}" by simp
          then obtain t where "t \<in> keys q" by blast
          with assms(2) q obtain c h U where "(h, U) \<in> set qs" and "c \<noteq> 0"
            and "monomial c t \<in> cone (h, U)" by (rule monomial_decomp_sum_list_monomial_in_cone)
          moreover from assms(3) \<open>q \<in> ideal F\<close> \<open>t \<in> keys q\<close> have "monomial c t \<in> ideal F"
            by (rule punit.monomial_pmdl_field[simplified])
          ultimately have "monomial c t \<in> cone (h, U) \<inter> ideal F" by simp
          also from assms(1) \<open>(h, U) \<in> set qs\<close> have "\<dots> = {0}" by (rule splits_wrtD)
          finally have "c = 0" by (simp add: monomial_0_iff)
          with \<open>c \<noteq> 0\<close> show False ..
        qed
        with p show "x \<in> sum_list ` listset (map cone ps)" by (simp add: x xs)
      qed
    qed
  qed
qed

text \<open>Together, Theorems \<open>splits_wrt_image_sum_list_fst_subset\<close> and \<open>splits_wrt_cone_decomp_1\<close>
  imply that @{term ps} is also a cone decomposition of @{term "T \<inter> ideal F \<inter> P[X]"}.\<close>

lemma splits_wrt_cone_decomp_2:
  assumes "finite X" and "splits_wrt (ps, qs) T F" and "monomial_decomp qs" and "is_monomial_set F"
    and "F \<subseteq> P[X]"
  shows "cone_decomp (T \<inter> normal_form F ` P[X]) qs"
proof -
  from assms(2) have *: "cone_decomp T (ps @ qs)" by (rule splits_wrtD)
  hence "direct_decomp T (map cone ps @ map cone qs)" by (simp add: cone_decomp_def)
  hence 1: "direct_decomp (sum_list ` listset (map cone qs)) (map cone qs)"
    and 2: "direct_decomp T [sum_list ` listset (map cone ps), sum_list ` listset (map cone qs)]"
    by (auto dest: direct_decomp_appendD intro!: empty_not_in_map_cone)
  let ?ss = "[sum_list ` listset (map cone ps), sum_list ` listset (map cone qs)]"
  let ?G = "punit.reduced_GB F"
  from assms(1, 5) have "?G \<subseteq> P[X]" and G_is_GB: "punit.is_Groebner_basis ?G"
    and ideal_G: "ideal ?G = ideal F"
    by (rule reduced_GB_Polys, rule reduced_GB_is_GB_Polys, rule reduced_GB_ideal_Polys)
  show ?thesis
  proof (intro cone_decompI direct_decompI)
    from 1 show "inj_on sum_list (listset (map cone qs))" by (simp only: direct_decomp_def bij_betw_def)
  next
    from assms(2) have "sum_list ` listset (map cone ps) \<subseteq> ideal F \<inter> P[X]"
      by (rule splits_wrt_image_sum_list_fst_subset)
    hence sub: "sum_list ` listset (map cone ps) \<subseteq> ideal F" by simp
    show "sum_list ` listset (map cone qs) = T \<inter> normal_form F ` P[X]"
    proof (rule set_eqI)
      fix x
      show "x \<in> sum_list ` listset (map cone qs) \<longleftrightarrow> x \<in> T \<inter> normal_form F ` P[X]"
      proof
        assume x_in: "x \<in> sum_list ` listset (map cone qs)"
        show "x \<in> T \<inter> normal_form F ` P[X]"
        proof (intro IntI)
          have "map (\<lambda>_. 0) ps \<in> listset (map cone ps)" (is "?ys \<in> _")
            by (induct ps) (auto intro: listset_ConsI zero_in_cone simp del: listset.simps(2))
          hence "sum_list ?ys \<in> sum_list ` listset (map cone ps)" by (rule imageI)
          hence "0 \<in> sum_list ` listset (map cone ps)" by simp
          from this x_in have "[0, x] \<in> listset ?ss" using refl by (rule listset_doubletonI)
          with 2 have "sum_list [0, x] \<in> T" by (rule direct_decompD)
          thus "x \<in> T" by simp
        next
          from assms(2) have "sum_list ` listset (map cone qs) \<subseteq> P[X]"
            by (rule splits_wrt_image_sum_list_snd_subset)
          with x_in have "x \<in> P[X]" ..
          moreover have "\<not> punit.is_red ?G x"
          proof
            assume "punit.is_red ?G x"
            then obtain g t where "g \<in> ?G" and "t \<in> keys x" and "g \<noteq> 0" and adds: "lpp g adds t"
              by (rule punit.is_red_addsE[simplified])
            from assms(3) x_in this(2) obtain c h U where "(h, U) \<in> set qs" and "c \<noteq> 0"
              and "monomial c t \<in> cone (h, U)" by (rule monomial_decomp_sum_list_monomial_in_cone)
            note this(3)
            moreover have "monomial c t \<in> ideal ?G"
            proof (rule punit.is_red_monomial_monomial_set_in_pmdl[simplified])
              from \<open>c \<noteq> 0\<close> show "is_monomial (monomial c t)" by (rule monomial_is_monomial)
            next
              from assms(1, 5, 4) show "is_monomial_set ?G" by (rule reduced_GB_is_monomial_set_Polys)
            next
              from \<open>c \<noteq> 0\<close> have "t \<in> keys (monomial c t)" by simp
              with \<open>g \<in> ?G\<close> \<open>g \<noteq> 0\<close> show "punit.is_red ?G (monomial c t)" using adds
                by (rule punit.is_red_addsI[simplified])
            qed
            ultimately have "monomial c t \<in> cone (h, U) \<inter> ideal F" by (simp add: ideal_G)
            also from assms(2) \<open>(h, U) \<in> set qs\<close> have "\<dots> = {0}" by (rule splits_wrtD)
            finally have "c = 0" by (simp add: monomial_0_iff)
            with \<open>c \<noteq> 0\<close> show False ..
          qed
          ultimately show "x \<in> normal_form F ` P[X]"
            using assms(1, 5) by (simp add: image_normal_form_iff)
        qed
      next
        assume "x \<in> T \<inter> normal_form F ` P[X]"
        hence "x \<in> T" and "x \<in> normal_form F ` P[X]" by simp_all
        from this(2) assms(1, 5) have "x \<in> P[X]" and irred: "\<not> punit.is_red ?G x"
          by (simp_all add: image_normal_form_iff)
        from 2 \<open>x \<in> T\<close> obtain xs where "xs \<in> listset ?ss" and x: "x = sum_list xs"
          by (rule direct_decompE)
        from this(1) obtain p q where p: "p \<in> sum_list ` listset (map cone ps)"
          and q: "q \<in> sum_list ` listset (map cone qs)" and xs: "xs = [p, q]"
          by (rule listset_doubletonE)
        have "x = p + q" by (simp add: x xs)
        from p sub have "p \<in> ideal F" ..
        have "p = 0"
        proof (rule ccontr)
          assume "p \<noteq> 0"
          hence "keys p \<noteq> {}" by simp
          then obtain t where "t \<in> keys p" by blast
          from assms(4) \<open>p \<in> ideal F\<close> \<open>t \<in> keys p\<close> have 3: "monomial c t \<in> ideal F" for c
            by (rule punit.monomial_pmdl_field[simplified])
          have "t \<notin> keys q"
          proof
            assume "t \<in> keys q"
            with assms(3) q obtain c h U where "(h, U) \<in> set qs" and "c \<noteq> 0"
              and "monomial c t \<in> cone (h, U)" by (rule monomial_decomp_sum_list_monomial_in_cone)
            from this(3) 3 have "monomial c t \<in> cone (h, U) \<inter> ideal F" by simp
            also from assms(2) \<open>(h, U) \<in> set qs\<close> have "\<dots> = {0}" by (rule splits_wrtD)
            finally have "c = 0" by (simp add: monomial_0_iff)
            with \<open>c \<noteq> 0\<close> show False ..
          qed
          with \<open>t \<in> keys p\<close> have "t \<in> keys x" unfolding \<open>x = p + q\<close> by (rule in_keys_plusI1)
          have "punit.is_red ?G x"
          proof -
            note G_is_GB
            moreover from 3 have "monomial 1 t \<in> ideal ?G" by (simp only: ideal_G)
            moreover have "monomial (1::'a) t \<noteq> 0" by (simp add: monomial_0_iff)
            ultimately obtain g where "g \<in> ?G" and "g \<noteq> 0"
              and "lpp g adds lpp (monomial (1::'a) t)" by (rule punit.GB_adds_lt[simplified])
            from this(3) have "lpp g adds t" by (simp add: punit.lt_monomial)
            with \<open>g \<in> ?G\<close> \<open>g \<noteq> 0\<close> \<open>t \<in> keys x\<close> show ?thesis by (rule punit.is_red_addsI[simplified])
          qed
          with irred show False ..
        qed
        with q show "x \<in> sum_list ` listset (map cone qs)" by (simp add: x xs)
      qed
    qed
  qed
qed

lemma quot_monomial_ideal_monomial:
  "ideal (monomial 1 ` S) \<div> monomial 1 (Poly_Mapping.single (x::'x) (1::nat)) =
    ideal (monomial (1::'a::comm_ring_1) ` (\<lambda>s. s - Poly_Mapping.single x 1) ` S)"
proof (rule set_eqI)
  let ?x = "Poly_Mapping.single x (1::nat)"
  fix a
  have "a \<in> ideal (monomial 1 ` S) \<div> monomial 1 ?x \<longleftrightarrow> punit.monom_mult 1 ?x a \<in> ideal (monomial (1::'a) ` S)"
    by (simp only: quot_set_iff times_monomial_left)
  also have "\<dots> \<longleftrightarrow> a \<in> ideal (monomial 1 ` (\<lambda>s. s - ?x) ` S)"
  proof (induct a rule: poly_mapping_plus_induct)
    case 1
    show ?case by (simp add: ideal.span_zero)
  next
    case (2 a c t)
    let ?S = "monomial (1::'a) ` (\<lambda>s. s - ?x) ` S"
    show ?case
    proof
      assume 0: "punit.monom_mult 1 ?x (monomial c t + a) \<in> ideal (monomial 1 ` S)"
      have "is_monomial_set (monomial (1::'a) ` S)"
        by (auto intro!: is_monomial_setI monomial_is_monomial)
      moreover from 0 have 1: "monomial c (?x + t) + punit.monom_mult 1 ?x a \<in> ideal (monomial 1 ` S)"
        by (simp add: punit.monom_mult_monomial punit.monom_mult_dist_right)
      moreover have "?x + t \<in> keys (monomial c (?x + t) + punit.monom_mult 1 ?x a)"
      proof (intro in_keys_plusI1 notI)
        from 2(1) show "?x + t \<in> keys (monomial c (?x + t))" by simp
      next
        assume "?x + t \<in> keys (punit.monom_mult 1 ?x a)"
        also have "\<dots> \<subseteq> (+) ?x ` keys a" by (rule punit.keys_monom_mult_subset[simplified])
        finally obtain s where "s \<in> keys a" and "?x + t = ?x + s" ..
        from this(2) have "t = s" by simp
        with \<open>s \<in> keys a\<close> 2(2) show False by simp
      qed
      ultimately obtain f where "f \<in> monomial (1::'a) ` S" and adds: "lpp f adds ?x + t"
        by (rule punit.keys_monomial_pmdl[simplified])
      from this(1) obtain s where "s \<in> S" and f: "f = monomial 1 s" ..
      from adds have "s adds ?x + t" by (simp add: f punit.lt_monomial)
      hence "s - ?x adds t"
        by (metis (no_types, lifting) add_minus_2 adds_minus adds_triv_right plus_minus_assoc_pm_nat_1)
      then obtain s' where t: "t = (s - ?x) + s'" by (rule addsE)
      from \<open>s \<in> S\<close> have "monomial 1 (s - ?x) \<in> ?S" by (intro imageI)
      also have "\<dots> \<subseteq> ideal ?S" by (rule ideal.span_superset)
      finally have "monomial c s' * monomial 1 (s - ?x) \<in> ideal ?S"
        by (rule ideal.span_scale)
      hence "monomial c t \<in> ideal ?S" by (simp add: times_monomial_monomial t add.commute)
      moreover have "a \<in> ideal ?S"
      proof -
        from \<open>f \<in> monomial 1 ` S\<close> have "f \<in> ideal (monomial 1 ` S)" by (rule ideal.span_base)
        hence "punit.monom_mult c (?x + t - s) f \<in> ideal (monomial 1 ` S)"
          by (rule punit.pmdl_closed_monom_mult[simplified])
        with \<open>s adds ?x + t\<close> have "monomial c (?x + t) \<in> ideal (monomial 1 ` S)"
          by (simp add: f punit.monom_mult_monomial adds_minus)
        with 1 have "monomial c (?x + t) + punit.monom_mult 1 ?x a - monomial c (?x + t) \<in> ideal (monomial 1 ` S)"
          by (rule ideal.span_diff)
        thus ?thesis by (simp add: 2(3) del: One_nat_def)
      qed
      ultimately show "monomial c t + a \<in> ideal ?S"
        by (rule ideal.span_add)
    next
      have "is_monomial_set ?S" by (auto intro!: is_monomial_setI monomial_is_monomial)
      moreover assume 1: "monomial c t + a \<in> ideal ?S"
      moreover from _ 2(2) have "t \<in> keys (monomial c t + a)"
      proof (rule in_keys_plusI1)
        from 2(1) show "t \<in> keys (monomial c t)" by simp
      qed
      ultimately obtain f where "f \<in> ?S" and adds: "lpp f adds t"
        by (rule punit.keys_monomial_pmdl[simplified])
      from this(1) obtain s where "s \<in> S" and f: "f = monomial 1 (s - ?x)" by blast
      from adds have "s - ?x adds t" by (simp add: f punit.lt_monomial)
      hence "s adds ?x + t"
        by (auto simp: adds_poly_mapping le_fun_def lookup_add lookup_minus lookup_single when_def
            split: if_splits)
      then obtain s' where t: "?x + t = s + s'" by (rule addsE)
      from \<open>s \<in> S\<close> have "monomial 1 s \<in> monomial 1 ` S" by (rule imageI)
      also have "\<dots> \<subseteq> ideal (monomial 1 ` S)" by (rule ideal.span_superset)
      finally have "monomial c s' * monomial 1 s \<in> ideal (monomial 1 ` S)"
        by (rule ideal.span_scale)
      hence "monomial c (?x + t) \<in> ideal (monomial 1 ` S)"
        by (simp only: t) (simp add: times_monomial_monomial add.commute)
      moreover have "punit.monom_mult 1 ?x a \<in> ideal (monomial 1 ` S)"
      proof -
        from \<open>f \<in> ?S\<close> have "f \<in> ideal ?S" by (rule ideal.span_base)
        hence "punit.monom_mult c (t - (s - ?x)) f \<in> ideal ?S"
          by (rule punit.pmdl_closed_monom_mult[simplified])
        with \<open>s - ?x adds t\<close> have "monomial c t \<in> ideal ?S"
          by (simp add: f punit.monom_mult_monomial adds_minus)
        with 1 have "monomial c t + a - monomial c t \<in> ideal ?S"
          by (rule ideal.span_diff)
        thus ?thesis by (simp add: 2(3) del: One_nat_def)
      qed
      ultimately have "monomial c (?x + t) + punit.monom_mult 1 ?x a \<in> ideal (monomial 1 ` S)"
        by (rule ideal.span_add)
      thus "punit.monom_mult 1 ?x (monomial c t + a) \<in> ideal (monomial 1 ` S)"
        by (simp add: punit.monom_mult_monomial punit.monom_mult_dist_right)
    qed
  qed
  finally show "a \<in> ideal (monomial 1 ` S) \<div> monomial 1 ?x \<longleftrightarrow> a \<in> ideal (monomial 1 ` (\<lambda>s. s - ?x) ` S)" .
qed

lemma lem_4_2_1:
  assumes "ideal F \<div> monomial 1 t = ideal (monomial (1::'a::comm_ring_1) ` S)"
  shows "cone (monomial 1 t, U) \<subseteq> ideal F \<longleftrightarrow> 0 \<in> S"
proof
  have "monomial 1 t \<in> cone (monomial (1::'a) t, U)" by (rule tip_in_cone)
  also assume "cone (monomial 1 t, U) \<subseteq> ideal F"
  finally have *: "monomial 1 t * 1 \<in> ideal F" by simp
  have "is_monomial_set (monomial (1::'a) ` S)"
    by (auto intro!: is_monomial_setI monomial_is_monomial)
  moreover from * have "1 \<in> ideal (monomial (1::'a) ` S)" by (simp only: quot_set_iff flip: assms)
  moreover have "0 \<in> keys (1::_ \<Rightarrow>\<^sub>0 'a)" by simp
  ultimately obtain g where "g \<in> monomial (1::'a) ` S" and adds: "lpp g adds 0"
    by (rule punit.keys_monomial_pmdl[simplified])
  from this(1) obtain s where "s \<in> S" and g: "g = monomial 1 s" ..
  from adds have "s adds 0" by (simp add: g punit.lt_monomial flip: single_one)
  with \<open>s \<in> S\<close> show "0 \<in> S" by (simp only: adds_zero)
next
  assume "0 \<in> S"
  hence "monomial 1 0 \<in> monomial (1::'a) ` S" by (rule imageI)
  hence "1 \<in> ideal (monomial (1::'a) ` S)" unfolding single_one by (rule ideal.span_base)
  hence eq: "ideal F \<div> monomial 1 t = UNIV" (is "_ \<div> ?t = _")
    by (simp only: assms ideal_eq_UNIV_iff_contains_one)
  show "cone (monomial 1 t, U) \<subseteq> ideal F"
  proof
    fix a
    assume "a \<in> cone (?t, U)"
    then obtain q where a: "a = q * ?t" by (rule coneE)
    have "q \<in> ideal F \<div> ?t" by (simp add: eq)
    thus "a \<in> ideal F" by (simp only: a quot_set_iff mult.commute)
  qed
qed

lemma lem_4_2_2:
  assumes "ideal F \<div> monomial 1 t = ideal (monomial (1::'a::comm_ring_1) ` S)"
  shows "cone (monomial 1 t, U) \<inter> ideal F = {0} \<longleftrightarrow> S \<inter> .[U] = {}"
proof
  let ?t = "monomial (1::'a) t"
  assume eq: "cone (?t, U) \<inter> ideal F = {0}"
  {
    fix s
    assume "s \<in> S"
    hence "monomial 1 s \<in> monomial (1::'a) ` S" (is "?s \<in> _") by (rule imageI)
    hence "?s \<in> ideal (monomial 1 ` S)" by (rule ideal.span_base)
    also have "\<dots> = ideal F \<div> ?t" by (simp only: assms)
    finally have *: "?s * ?t \<in> ideal F" by (simp only: quot_set_iff mult.commute)
    assume "s \<in> .[U]"
    hence "?s \<in> P[U]" by (rule Polys_closed_monomial)
    with refl have "?s * ?t \<in> cone (?t, U)" by (rule coneI)
    with * have "?s * ?t \<in> cone (?t, U) \<inter> ideal F" by simp
    hence False by (simp add: eq times_monomial_monomial monomial_0_iff)
  }
  thus "S \<inter> .[U] = {}" by blast
next
  let ?t = "monomial (1::'a) t"
  assume eq: "S \<inter> .[U] = {}"
  {
    fix a
    assume "a \<in> cone (?t, U)"
    then obtain q where "q \<in> P[U]" and a: "a = q * ?t" by (rule coneE)
    assume "a \<in> ideal F"
    have "a = 0"
    proof (rule ccontr)
      assume "a \<noteq> 0"
      hence "q \<noteq> 0" by (auto simp: a)
      from \<open>a \<in> ideal F\<close> have *: "q \<in> ideal F \<div> ?t" by (simp only: quot_set_iff a mult.commute)
      have "is_monomial_set (monomial (1::'a) ` S)"
        by (auto intro!: is_monomial_setI monomial_is_monomial)
      moreover from * have q_in: "q \<in> ideal (monomial 1 ` S)" by (simp only: assms)
      moreover from \<open>q \<noteq> 0\<close> have "lpp q \<in> keys q" by (rule punit.lt_in_keys)
      ultimately obtain g where "g \<in> monomial (1::'a) ` S" and adds: "lpp g adds lpp q"
        by (rule punit.keys_monomial_pmdl[simplified])
      from this(1) obtain s where "s \<in> S" and g: "g = monomial 1 s" ..
      from \<open>q \<noteq> 0\<close> have "lpp q \<in> keys q" by (rule punit.lt_in_keys)
      also from \<open>q \<in> P[U]\<close> have "\<dots> \<subseteq> .[U]" by (rule PolysD)
      finally have "lpp q \<in> .[U]" .
      moreover from adds have "s adds lpp q" by (simp add: g punit.lt_monomial)
      ultimately have "s \<in> .[U]" by (rule PPs_closed_adds)
      with eq \<open>s \<in> S\<close> show False by blast
    qed
  }
  thus "cone (?t, U) \<inter> ideal F = {0}" using zero_in_cone ideal.span_zero by blast
qed

subsection \<open>Function \<open>split\<close>\<close>

definition max_subset :: "'a set \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a set"
  where "max_subset A P = (ARG_MAX card B. B \<subseteq> A \<and> P B)"

lemma max_subset:
  assumes "finite A" and "B \<subseteq> A" and "P B"
  shows "max_subset A P \<subseteq> A" (is ?thesis1)
    and "P (max_subset A P)" (is ?thesis2)
    and "card B \<le> card (max_subset A P)" (is ?thesis3)
proof -
  from assms(2, 3) have "B \<subseteq> A \<and> P B" by simp
  moreover have "\<forall>C. C \<subseteq> A \<and> P C \<longrightarrow> card C < Suc (card A)"
  proof (intro allI impI, elim conjE)
    fix C
    assume "C \<subseteq> A"
    with assms(1) have "card C \<le> card A" by (rule card_mono)
    thus "card C < Suc (card A)" by simp
  qed
  ultimately have "?thesis1 \<and> ?thesis2" and ?thesis3 unfolding max_subset_def
    by (rule arg_max_natI, rule arg_max_nat_le)
  thus ?thesis1 and ?thesis2 and ?thesis3 by simp_all
qed

function (domintros) split :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'x set \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) set \<Rightarrow>
                                ((((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> ('x set)) list) \<times>
                                 (((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::{zero,one}) \<times> ('x set)) list))"
  where
    "split t U S =
      (if 0 \<in> S then
        ([(monomial 1 t, U)], [])
      else if S \<inter> .[U] = {} then
        ([], [(monomial 1 t, U)])
      else
        let x = SOME x'. x' \<in> U - (max_subset U (\<lambda>V. S \<inter> .[V] = {}));
            (ps0, qs0) = split t (U - {x}) S;
            (ps1, qs1) = split (Poly_Mapping.single x 1 + t) U ((\<lambda>f. f - Poly_Mapping.single x 1) ` S) in
          (ps0 @ ps1, qs0 @ qs1))"
  by auto

text \<open>Function @{const split} is not executable, because this is not necessary.
  With some effort, it could be made executable, though.\<close>

lemma split_domI':
  assumes "finite X" and "fst (snd args) \<subseteq> X" and "finite (snd (snd args))"
  shows "split_dom TYPE('a::{zero,one}) args"
proof -
  let ?m = "\<lambda>args'. card (fst (snd args')) + sum deg_pm (snd (snd args'))"
  from wf_measure[of ?m] assms(2, 3) show ?thesis
  proof (induct args)
    case (less args)
    obtain t U F where args: "args = (t, U, F)" using prod.exhaust by metis
    from less.prems have "U \<subseteq> X" and "finite F" by (simp_all only: args fst_conv snd_conv)
    from this(1) assms(1) have "finite U" by (rule finite_subset)
    have IH: "split_dom TYPE('a) (t', U', F')"
      if "U' \<subseteq> X" and "finite F'" and "card U' + sum deg_pm F' < card U + sum deg_pm F"
      for t' U' F'
      using less.hyps that by (simp add: args)

    define S where "S = max_subset U (\<lambda>V. F \<inter> .[V] = {})"
    define x where "x = (SOME x'. x' \<in> U \<and> x' \<notin> S)"
    show ?case unfolding args
    proof (rule split.domintros, simp_all only: x_def[symmetric] S_def[symmetric])
      fix f
      assume "0 \<notin> F" and "f \<in> F" and "f \<in> .[U]"
      from this(1) have "F \<inter> .[{}] = {}" by simp
      with \<open>finite U\<close> empty_subsetI have "S \<subseteq> U" and "F \<inter> .[S] = {}"
        unfolding S_def by (rule max_subset)+
      have "x \<in> U \<and> x \<notin> S" unfolding x_def
      proof (rule someI_ex)
        from \<open>f \<in> F\<close> \<open>f \<in> .[U]\<close> \<open>F \<inter> .[S] = {}\<close> have "S \<noteq> U" by blast
        with \<open>S \<subseteq> U\<close> show "\<exists>y. y \<in> U \<and> y \<notin> S" by blast
      qed
      hence "x \<in> U" and "x \<notin> S" by simp_all
      {
        assume "\<not> split_dom TYPE('a) (t, U - {x}, F)"
        moreover from _ \<open>finite F\<close> have "split_dom TYPE('a) (t, U - {x}, F)"
        proof (rule IH)
          from \<open>U \<subseteq> X\<close> show "U - {x} \<subseteq> X" by blast
        next
          from \<open>finite U\<close> \<open>x \<in> U\<close> have "card (U - {x}) < card U" by (rule card_Diff1_less)
          thus "card (U - {x}) + sum deg_pm F < card U + sum deg_pm F" by simp
        qed
        ultimately show False ..
      }
      {
        let ?args = "(Poly_Mapping.single x (Suc 0) + t, U, (\<lambda>f. f - Poly_Mapping.single x (Suc 0)) ` F)"
        assume "\<not> split_dom TYPE('a) ?args"
        moreover from \<open>U \<subseteq> X\<close> have "split_dom TYPE('a) ?args"
        proof (rule IH)
          from \<open>finite F\<close> show "finite ((\<lambda>f. f - Poly_Mapping.single x (Suc 0)) ` F)"
            by (rule finite_imageI)
        next
          have "sum deg_pm ((\<lambda>f. f - Poly_Mapping.single x (Suc 0)) ` F) \<le>
                sum (deg_pm \<circ> (\<lambda>f. f - Poly_Mapping.single x (Suc 0))) F"
            using \<open>finite F\<close> by (rule sum_image_le) simp
          also from \<open>finite F\<close> have "\<dots> < sum deg_pm F"
          proof (rule sum_strict_mono_ex1)
            show "\<forall>f\<in>F. (deg_pm \<circ> (\<lambda>f. f - Poly_Mapping.single x (Suc 0))) f \<le> deg_pm f"
              by (simp add: deg_pm_minus_le)
          next
            show "\<exists>f\<in>F. (deg_pm \<circ> (\<lambda>f. f - Poly_Mapping.single x (Suc 0))) f < deg_pm f"
            proof (rule ccontr)
              assume *: "\<not> (\<exists>f\<in>F. (deg_pm \<circ> (\<lambda>f. f - Poly_Mapping.single x (Suc 0))) f < deg_pm f)"
              note \<open>finite U\<close>
              moreover from \<open>x \<in> U\<close> \<open>S \<subseteq> U\<close> have "insert x S \<subseteq> U" by (rule insert_subsetI)
              moreover have "F \<inter> .[insert x S] = {}"
              proof -
                {
                  fix s
                  assume "s \<in> F"
                  with * have "\<not> deg_pm (s - Poly_Mapping.single x (Suc 0)) < deg_pm s" by simp
                  with deg_pm_minus_le[of s "Poly_Mapping.single x (Suc 0)"]
                  have "deg_pm (s - Poly_Mapping.single x (Suc 0)) = deg_pm s" by simp
                  hence "keys s \<inter> keys (Poly_Mapping.single x (Suc 0)) = {}"
                    by (simp only: deg_pm_minus_id_iff)
                  hence "x \<notin> keys s" by simp
                  moreover assume "s \<in> .[insert x S]"
                  ultimately have "s \<in> .[S]" by (fastforce simp: PPs_def)
                  with \<open>s \<in> F\<close> \<open>F \<inter> .[S] = {}\<close> have False by blast
                }
                thus ?thesis by blast
              qed
              ultimately have "card (insert x S) \<le> card S" unfolding S_def by (rule max_subset)
              moreover from \<open>S \<subseteq> U\<close> \<open>finite U\<close> have "finite S" by (rule finite_subset)
              ultimately show False using \<open>x \<notin> S\<close> by simp
            qed
          qed
          finally show "card U + sum deg_pm ((\<lambda>f. f - monomial (Suc 0) x) ` F) < card U + sum deg_pm F"
            by simp
        qed
        ultimately show False ..
      }
    qed
  qed
qed

corollary split_domI: "finite X \<Longrightarrow> U \<subseteq> X \<Longrightarrow> finite S \<Longrightarrow> split_dom TYPE('a::{zero,one}) (t, U, S)"
  using split_domI'[of "(t, U, S)"] by simp

lemma split_empty:
  assumes "finite X" and "U \<subseteq> X"
  shows "split t U {} = ([], [(monomial (1::'a::{zero,one}) t, U)])"
proof -
  have "finite {}" ..
  with assms have "split_dom TYPE('a) (t, U, {})" by (rule split_domI)
  thus ?thesis by (simp add: split.psimps)
qed

lemma split_induct [consumes 3, case_names base1 base2 step]:
  fixes P :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> _"
  assumes "finite X" and "U \<subseteq> X" and "finite S"
  assumes "\<And>t U S. U \<subseteq> X \<Longrightarrow> finite S \<Longrightarrow> 0 \<in> S \<Longrightarrow> P t U S ([(monomial (1::'a::{zero,one}) t, U)], [])"
  assumes "\<And>t U S. U \<subseteq> X \<Longrightarrow> finite S \<Longrightarrow> 0 \<notin> S \<Longrightarrow> S \<inter> .[U] = {} \<Longrightarrow> P t U S ([], [(monomial 1 t, U)])"
  assumes "\<And>t U S V x ps0 ps1 qs0 qs1. U \<subseteq> X \<Longrightarrow> finite S \<Longrightarrow> 0 \<notin> S \<Longrightarrow> S \<inter> .[U] \<noteq> {} \<Longrightarrow> V \<subseteq> U \<Longrightarrow>
              S \<inter> .[V] = {} \<Longrightarrow> (\<And>V'. V' \<subseteq> U \<Longrightarrow> S \<inter> .[V'] = {} \<Longrightarrow> card V' \<le> card V) \<Longrightarrow>
              x \<in> U \<Longrightarrow> x \<notin> V \<Longrightarrow> V = max_subset U (\<lambda>V'. S \<inter> .[V'] = {}) \<Longrightarrow> x = (SOME x'. x' \<in> U - V) \<Longrightarrow>
              (ps0, qs0) = split t (U - {x}) S \<Longrightarrow>
              (ps1, qs1) = split (Poly_Mapping.single x 1 + t) U ((\<lambda>f. f - Poly_Mapping.single x 1) ` S) \<Longrightarrow>
              split t U S = (ps0 @ ps1, qs0 @ qs1) \<Longrightarrow>
              P t (U - {x}) S (ps0, qs0) \<Longrightarrow>
              P (Poly_Mapping.single x 1 + t) U ((\<lambda>f. f - Poly_Mapping.single x 1) ` S) (ps1, qs1) \<Longrightarrow>
              P t U S (ps0 @ ps1, qs0 @ qs1)"
  shows "P t U S (split t U S)"
proof -
  from assms(1-3) have "split_dom TYPE('a) (t, U, S)" by (rule split_domI)
  thus ?thesis using assms(2,3)
  proof (induct t U S rule: split.pinduct)
    case step: (1 t U F)
    from step(4) assms(1) have "finite U" by (rule finite_subset)
    define S where "S = max_subset U (\<lambda>V. F \<inter> .[V] = {})"
    define x where "x = (SOME x'. x' \<in> U \<and> x' \<notin> S)"
    show ?case
    proof (simp add: split.psimps[OF step(1)] S_def[symmetric] x_def[symmetric] split: prod.split, intro allI conjI impI)
      assume "0 \<in> F"
      with step(4, 5) show "P t U F ([(monomial 1 t, U)], [])" by (rule assms(4))
      thus "P t U F ([(monomial 1 t, U)], [])" .
    next
      assume "0 \<notin> F" and "F \<inter> .[U] = {}"
      with step(4, 5) show "P t U F ([], [(monomial 1 t, U)])" by (rule assms(5))
    next
      fix ps0 qs0 ps1 qs1 :: "((_ \<Rightarrow>\<^sub>0 'a) \<times> _) list"
      assume "split (Poly_Mapping.single x (Suc 0) + t) U ((\<lambda>f. f - Poly_Mapping.single x (Suc 0)) ` F) = (ps1, qs1)"
      hence PQ1[symmetric]: "split (Poly_Mapping.single x 1 + t) U ((\<lambda>f. f - Poly_Mapping.single x 1) ` F) = (ps1, qs1)"
        by simp
      assume PQ0[symmetric]: "split t (U - {x}) F = (ps0, qs0)"
      assume "F \<inter> .[U] \<noteq> {}" and "0 \<notin> F"
      from this(2) have "F \<inter> .[{}] = {}" by simp
      with \<open>finite U\<close> empty_subsetI have "S \<subseteq> U" and "F \<inter> .[S] = {}"
        unfolding S_def by (rule max_subset)+
      have S_max: "card S' \<le> card S" if "S' \<subseteq> U" and "F \<inter> .[S'] = {}" for S'
        using \<open>finite U\<close> that unfolding S_def by (rule max_subset)
      have "x \<in> U \<and> x \<notin> S" unfolding x_def
      proof (rule someI_ex)
        from \<open>F \<inter> .[U] \<noteq> {}\<close> \<open>F \<inter> .[S] = {}\<close> have "S \<noteq> U" by blast
        with \<open>S \<subseteq> U\<close> show "\<exists>y. y \<in> U \<and> y \<notin> S" by blast
      qed
      hence "x \<in> U" and "x \<notin> S" by simp_all
      from step(4, 5) \<open>0 \<notin> F\<close> \<open>F \<inter> .[U] \<noteq> {}\<close> \<open>S \<subseteq> U\<close> \<open>F \<inter> .[S] = {}\<close> S_max \<open>x \<in> U\<close> \<open>x \<notin> S\<close> S_def _ PQ0 PQ1
      show "P t U F (ps0 @ ps1, qs0 @ qs1)"
      proof (rule assms(6))
        show "P t (U - {x}) F (ps0, qs0)"
          unfolding PQ0 using \<open>0 \<notin> F\<close> \<open>F \<inter> .[U] \<noteq> {}\<close> _ _ step(5)
        proof (rule step(2))
          from \<open>U \<subseteq> X\<close> show "U - {x} \<subseteq> X" by fastforce
        qed (simp add: x_def S_def)
      next
        show "P (Poly_Mapping.single x 1 + t) U ((\<lambda>f. f - Poly_Mapping.single x 1) ` F) (ps1, qs1)"
          unfolding PQ1 using \<open>0 \<notin> F\<close> \<open>F \<inter> .[U] \<noteq> {}\<close> _ refl PQ0 \<open>U \<subseteq> X\<close>
        proof (rule step(3))
          from \<open>finite F\<close> show "finite ((\<lambda>f. f - Poly_Mapping.single x 1) ` F)" by (rule finite_imageI)
        qed (simp add: x_def S_def)
      next
        show "split t U F = (ps0 @ ps1, qs0 @ qs1)" using \<open>0 \<notin> F\<close> \<open>F \<inter> .[U] \<noteq> {}\<close>
          by (simp add: split.psimps[OF step(1)] Let_def flip: S_def x_def PQ0 PQ1 del: One_nat_def)
      qed (assumption+, simp add: x_def S_def)
    qed
  qed
qed

lemma valid_decomp_split:
  assumes "finite X" and "U \<subseteq> X" and "finite S" and "t \<in> .[X]"
  shows "valid_decomp X (fst ((split t U S)::(_ \<times> (((_ \<Rightarrow>\<^sub>0 'a::zero_neq_one) \<times> _) list))))"
    and "valid_decomp X (snd ((split t U S)::(_ \<times> (((_ \<Rightarrow>\<^sub>0 'a::zero_neq_one) \<times> _) list))))"
          (is "valid_decomp _ (snd ?s)")
proof -
  from assms have "valid_decomp X (fst ?s) \<and> valid_decomp X (snd ?s)"
  proof (induct t U S rule: split_induct)
    case (base1 t U S)
    from base1(1, 4) show ?case by (simp add: valid_decomp_def monomial_0_iff Polys_closed_monomial)
  next
    case (base2 t U S)
    from base2(1, 5) show ?case by (simp add: valid_decomp_def monomial_0_iff Polys_closed_monomial)
  next
    case (step t U S V x ps0 ps1 qs0 qs1)
    from step.hyps(8, 1) have "x \<in> X" ..
    hence "Poly_Mapping.single x 1 \<in> .[X]" by (rule PPs_closed_single)
    hence "Poly_Mapping.single x 1 + t \<in> .[X]" using step.prems by (rule PPs_closed_plus)
    with step.hyps(15, 16) step.prems show ?case by (simp add: valid_decomp_append)
  qed
  thus "valid_decomp X (fst ?s)" and "valid_decomp X (snd ?s)" by simp_all
qed

lemma monomial_decomp_split:
  assumes "finite X" and "U \<subseteq> X" and "finite S"
  shows "monomial_decomp (fst ((split t U S)::(_ \<times> (((_ \<Rightarrow>\<^sub>0 'a::zero_neq_one) \<times> _) list))))"
    and "monomial_decomp (snd ((split t U S)::(_ \<times> (((_ \<Rightarrow>\<^sub>0 'a::zero_neq_one) \<times> _) list))))"
          (is "monomial_decomp (snd ?s)")
proof -
  from assms have "monomial_decomp (fst ?s) \<and> monomial_decomp (snd ?s)"
  proof (induct t U S rule: split_induct)
    case (base1 t U S)
    from base1(1) show ?case by (simp add: monomial_decomp_def monomial_is_monomial)
  next
    case (base2 t U S)
    from base2(1) show ?case by (simp add: monomial_decomp_def monomial_is_monomial)
  next
    case (step t U S V x ps0 ps1 qs0 qs1)
    from step.hyps(15, 16) show ?case by (auto simp: monomial_decomp_def)
  qed
  thus "monomial_decomp (fst ?s)" and "monomial_decomp (snd ?s)" by simp_all
qed

lemma split_splits_wrt:
  assumes "finite X" and "U \<subseteq> X" and "finite S" and "t \<in> .[X]"
    and "ideal F \<div> monomial 1 t = ideal (monomial 1 ` S)"
  shows "splits_wrt (split t U S) (cone (monomial (1::'a::{comm_ring_1,ring_no_zero_divisors}) t, U)) F"
  using assms
proof (induct t U S rule: split_induct)
  case (base1 t U S)
  from base1(3) have "cone (monomial 1 t, U) \<subseteq> ideal F" by (simp only: lem_4_2_1 base1(5))
  show ?case
  proof (rule splits_wrtI)
    fix h0 U0
    assume "(h0, U0) \<in> set [(monomial (1::'a) t, U)]"
    hence h0: "h0 = monomial 1 t" and "U0 = U" by simp_all
    note this(1)
    also have "monomial 1 t \<in> cone (monomial (1::'a) t, U)" by (fact tip_in_cone)
    also have "\<dots> \<subseteq> ideal F" by fact
    finally show "h0 \<in> ideal F" .
    
    from base1(4) have "h0 \<in> P[X]" unfolding h0 by (rule Polys_closed_monomial)
    moreover from base1(1) have "U0 \<subseteq> X" by (simp only: \<open>U0 = U\<close>)
    ultimately show "cone (h0, U0) \<subseteq> P[X]" by (rule cone_subset_PolysI)
  qed (simp_all add: cone_decomp_singleton \<open>U \<subseteq> X\<close>)
next
  case (base2 t U S)
  from base2(4) have "cone (monomial 1 t, U) \<inter> ideal F = {0}" by (simp only: lem_4_2_2 base2(6))
  show ?case
  proof (rule splits_wrtI)
    fix h0 U0
    assume "(h0, U0) \<in> set [(monomial (1::'a) t, U)]"
    hence h0: "h0 = monomial 1 t" and "U0 = U" by simp_all
    note this(1)
    also from base2(5) have "monomial 1 t \<in> P[X]" by (rule Polys_closed_monomial)
    finally have "h0 \<in> P[X]" .
    moreover from base2(1) have "U0 \<subseteq> X" by (simp only: \<open>U0 = U\<close>)
    ultimately show "cone (h0, U0) \<subseteq> P[X]" by (rule cone_subset_PolysI)
  next
    fix h0 U0 a
    assume "(h0, U0) \<in> set [(monomial (1::'a) t, U)]" and "a \<in> cone (h0, U0)"
    hence "a \<in> cone (monomial 1 t, U)" by simp
    moreover assume "a \<in> ideal F"
    ultimately have "a \<in> cone (monomial 1 t, U) \<inter> ideal F" by (rule IntI)
    also have "\<dots> = {0}" by fact
    finally show "a = 0" by simp
  qed (simp_all add: cone_decomp_singleton \<open>U \<subseteq> X\<close>)
next
  case (step t U S V x ps0 ps1 qs0 qs1)
  let ?x = "Poly_Mapping.single x 1"
  from step.prems have 0: "splits_wrt (ps0, qs0) (cone (monomial 1 t, U - {x})) F" by (rule step.hyps)
  have 1: "splits_wrt (ps1, qs1) (cone (monomial 1 (?x + t), U)) F"
  proof (rule step.hyps)
    from step.hyps(8, 1) have "x \<in> X" ..
    hence "?x \<in> .[X]" by (rule PPs_closed_single)
    thus "?x + t \<in> .[X]" using step.prems(1) by (rule PPs_closed_plus)
  next
    have "ideal F \<div> monomial 1 (?x + t) = ideal F \<div> monomial 1 t \<div> monomial 1 ?x"
      by (simp add: times_monomial_monomial add.commute)
    also have "\<dots> = ideal (monomial 1 ` S) \<div> monomial 1 ?x" by (simp only: step.prems)
    finally show "ideal F \<div> monomial 1 (?x + t) = ideal (monomial 1 ` (\<lambda>s. s - ?x) ` S)"
      by (simp only: quot_monomial_ideal_monomial)
  qed

  show ?case
  proof (rule splits_wrtI)
    from step.hyps(8) have U: "insert x U = U" by blast
    have "direct_decomp (cone (monomial (1::'a) t, insert x (U - {x})))
                      [cone (monomial 1 t, U - {x}),
                       cone (monomial 1 (monomial (Suc 0) x) * monomial 1 t, insert x (U - {x}))]"
      by (rule direct_decomp_cone_insert) simp
    hence "direct_decomp (cone (monomial (1::'a) t, U))
                      [cone (monomial 1 t, U - {x}), cone (monomial 1 (?x + t), U)]"
      by (simp add: U times_monomial_monomial)
    moreover from 0 have "cone_decomp (cone (monomial 1 t, U - {x})) (ps0 @ qs0)"
      by (rule splits_wrtD)
    moreover from 1 have "cone_decomp (cone (monomial 1 (?x + t), U)) (ps1 @ qs1)"
      by (rule splits_wrtD)
    ultimately have "cone_decomp (cone (monomial 1 t, U)) ((ps0 @ qs0) @ (ps1 @ qs1))"
      by (rule cone_decomp_append)
    thus "cone_decomp (cone (monomial 1 t, U)) ((ps0 @ ps1) @ qs0 @ qs1)"
      by (rule cone_decomp_perm) (metis append.assoc perm_append1 perm_append2 perm_append_swap)
  next
    fix h0 U0
    assume "(h0, U0) \<in> set (ps0 @ ps1)"
    hence "(h0, U0) \<in> set ps0 \<union> set ps1" by simp
    hence "cone (h0, U0) \<subseteq> ideal F \<inter> P[X]"
    proof
      assume "(h0, U0) \<in> set ps0"
      with 0 show ?thesis by (rule splits_wrtD)
    next
      assume "(h0, U0) \<in> set ps1"
      with 1 show ?thesis by (rule splits_wrtD)
    qed
    hence *: "cone (h0, U0) \<subseteq> ideal F" and "cone (h0, U0) \<subseteq> P[X]" by simp_all
    from this(2) show "cone (h0, U0) \<subseteq> P[X]" .

    from tip_in_cone * show "h0 \<in> ideal F" ..
  next
    fix h0 U0
    assume "(h0, U0) \<in> set (qs0 @ qs1)"
    hence "(h0, U0) \<in> set qs0 \<union> set qs1" by simp
    thus "cone (h0, U0) \<subseteq> P[X]"
    proof
      assume "(h0, U0) \<in> set qs0"
      with 0 show ?thesis by (rule splits_wrtD)
    next
      assume "(h0, U0) \<in> set qs1"
      with 1 show ?thesis by (rule splits_wrtD)
    qed

    from \<open>(h0, U0) \<in> set qs0 \<union> set qs1\<close> have "cone (h0, U0) \<inter> ideal F = {0}"
    proof
      assume "(h0, U0) \<in> set qs0"
      with 0 show ?thesis by (rule splits_wrtD)
    next
      assume "(h0, U0) \<in> set qs1"
      with 1 show ?thesis by (rule splits_wrtD)
    qed
    thus "\<And>a. a \<in> cone (h0, U0) \<Longrightarrow> a \<in> ideal F \<Longrightarrow> a = 0" by blast
  qed
qed

lemma lem_4_5:
  assumes "finite X" and "U \<subseteq> X" and "t \<in> .[X]" and "F \<subseteq> P[X]"
    and "ideal F \<div> monomial 1 t = ideal (monomial (1::'a) ` S)"
    and "cone (monomial (1::'a::field) t', V) \<subseteq> cone (monomial 1 t, U) \<inter> normal_form F ` P[X]"
  shows "V \<subseteq> U" and "S \<inter> .[V] = {}"
proof -
  let ?t = "monomial (1::'a) t"
  let ?t' = "monomial (1::'a) t'"
  from assms(6) have 1: "cone (?t', V) \<subseteq> cone (?t, U)" and 2: "cone (?t', V) \<subseteq> normal_form F ` P[X]"
    by blast+
  from this(1) show "V \<subseteq> U" by (rule cone_subsetD) (simp add: monomial_0_iff)
  
  show "S \<inter> .[V] = {}"
  proof
    let ?t = "monomial (1::'a) t"
    let ?t' = "monomial (1::'a) t'"
    show "S \<inter> .[V] \<subseteq> {}"
    proof
      fix s
      assume "s \<in> S \<inter> .[V]"
      hence "s \<in> S" and "s \<in> .[V]" by simp_all
      from this(2) have "monomial (1::'a) s \<in> P[V]" (is "?s \<in> _") by (rule Polys_closed_monomial)
      with refl have "?s * ?t \<in> cone (?t, V)" by (rule coneI)
      from tip_in_cone 1 have "?t' \<in> cone (?t, U)" ..
      then obtain s' where "s' \<in> P[U]" and t': "?t' = s' * ?t" by (rule coneE)
      note this(1)
      also from assms(2) have "P[U] \<subseteq> P[X]" by (rule Polys_mono)
      finally have "s' \<in> P[X]" .
      have "s' * ?s * ?t = ?s * ?t'" by (simp add: t')
      also from refl \<open>?s \<in> P[V]\<close> have "\<dots> \<in> cone (?t', V)" by (rule coneI)
      finally have "s' * ?s * ?t \<in> cone (?t', V)" .
      hence 1: "s' * ?s * ?t \<in> normal_form F ` P[X]" using 2 ..
      from \<open>s \<in> S\<close> have "?s \<in> monomial 1 ` S" by (rule imageI)
      hence "?s \<in> ideal (monomial 1 ` S)" by (rule ideal.span_base)
      hence "s' * ?s \<in> ideal (monomial 1 ` S)" by (rule ideal.span_scale)
      hence "s' * ?s \<in> ideal F \<div> ?t" by (simp only: assms(5))
      hence "s' * ?s * ?t \<in> ideal F" by (simp only: quot_set_iff mult.commute)
      hence "s' * ?s * ?t \<in> ideal F \<inter> normal_form F ` P[X]" using 1 by (rule IntI)
      also from assms(1, 4) have "\<dots> \<subseteq> {0}"
        by (auto simp: normal_form_normal_form simp flip: normal_form_zero_iff)
      finally have "?s * ?t' = 0" by (simp add: t' ac_simps)
      thus "s \<in> {}" by (simp add: times_monomial_monomial monomial_0_iff)
    qed
  qed (fact empty_subsetI)
qed

lemma lem_4_6:
  assumes "finite X" and "U \<subseteq> X" and "finite S" and "t \<in> .[X]" and "F \<subseteq> P[X]"
    and "ideal F \<div> monomial 1 t = ideal (monomial 1 ` S)"
  assumes "cone (monomial 1 t', V) \<subseteq> cone (monomial 1 t, U) \<inter> normal_form F ` P[X]"
  obtains V' where "(monomial 1 t, V') \<in> set (snd (split t U S))" and "card V \<le> card V'"
proof -
  let ?t = "monomial (1::'a) t"
  let ?t' = "monomial (1::'a) t'"
  from assms(7) have "cone (?t', V) \<subseteq> cone (?t, U)" and "cone (?t', V) \<subseteq> normal_form F ` P[X]"
    by blast+
  from assms(1, 2, 4, 5, 6, 7) have "V \<subseteq> U" and "S \<inter> .[V] = {}" by (rule lem_4_5)+
  with assms(1, 2, 3) show ?thesis using that
  proof (induct t U S arbitrary: V thesis rule: split_induct)
    case (base1 t U S)
    from base1.hyps(3) have "0 \<in> S \<inter> .[V]" using zero_in_PPs by (rule IntI)
    thus ?case by (simp add: base1.prems(2))
  next
    case (base2 t U S)
    show ?case
    proof (rule base2.prems)
      from base2.hyps(1) assms(1) have "finite U" by (rule finite_subset)
      thus "card V \<le> card U" using base2.prems(1) by (rule card_mono)
    qed simp
  next
    case (step t U S V0 x ps0 ps1 qs0 qs1)
    from step.prems(1, 2) have 0: "card V \<le> card V0" by (rule step.hyps)
    from step.hyps(5, 9) have "V0 \<subseteq> U - {x}" by blast
    then obtain V' where 1: "(monomial 1 t, V') \<in> set (snd (ps0, qs0))" and 2: "card V0 \<le> card V'"
      using step.hyps(6) by (rule step.hyps)
    show ?case
    proof (rule step.prems)
      from 1 show "(monomial 1 t, V') \<in> set (snd (ps0 @ ps1, qs0 @ qs1))" by simp
    next
      from 0 2 show "card V \<le> card V'" by (rule le_trans)
    qed
  qed
qed

lemma lem_4_7:
  assumes "finite X" and "S \<subseteq> .[X]" and "g \<in> punit.reduced_GB (monomial (1::'a) ` S)"
    and "cone_decomp (P[X] \<inter> ideal (monomial (1::'a::field) ` S)) ps"
    and "monomial_decomp ps"
  obtains U where "(g, U) \<in> set ps"
proof -
  let ?S = "monomial (1::'a) ` S"
  let ?G = "punit.reduced_GB ?S"
  note assms(1)
  moreover from assms(2) have "?S \<subseteq> P[X]" by (auto intro: Polys_closed_monomial)
  moreover have "is_monomial_set ?S"
    by (auto intro!: is_monomial_setI monomial_is_monomial)
  ultimately have "is_monomial_set ?G" by (rule reduced_GB_is_monomial_set_Polys)
  hence "is_monomial g" using assms(3) by (rule is_monomial_setD)
  hence "g \<noteq> 0" by (rule monomial_not_0)
  moreover from assms(1) \<open>?S \<subseteq> P[X]\<close> have "punit.is_monic_set ?G"
    by (rule reduced_GB_is_monic_set_Polys)
  ultimately have "punit.lc g = 1" using assms(3) by (simp add: punit.is_monic_set_def)
  moreover define t where "t = lpp g"
  moreover from \<open>is_monomial g\<close> have "monomial (punit.lc g) (lpp g) = g"
    by (rule punit.monomial_eq_itself)
  ultimately have g: "g = monomial 1 t" by simp
  hence "t \<in> keys g" by simp
  from assms(3) have "g \<in> ideal ?G" by (rule ideal.span_base)
  also from assms(1) \<open>?S \<subseteq> P[X]\<close> have ideal_G: "\<dots> = ideal ?S" by (rule reduced_GB_ideal_Polys)
  finally have "g \<in> ideal ?S" .
  moreover from assms(3) have "g \<in> P[X]" by rule (intro reduced_GB_Polys assms(1) \<open>?S \<subseteq> P[X]\<close>)
  ultimately have "g \<in> P[X] \<inter> ideal ?S" by simp
  with assms(4) have "g \<in> sum_list ` listset (map cone ps)"
    by (simp only: cone_decomp_def direct_decompD)
  with assms(5) obtain d h U where *: "(h, U) \<in> set ps" and "d \<noteq> 0" and "monomial d t \<in> cone (h, U)"
    using \<open>t \<in> keys g\<close> by (rule monomial_decomp_sum_list_monomial_in_cone)
  from this(3) zero_in_PPs have "punit.monom_mult (1 / d) 0 (monomial d t) \<in> cone (h, U)"
    by (rule cone_closed_monom_mult)
  with \<open>d \<noteq> 0\<close> have "g \<in> cone (h, U)" by (simp add: g punit.monom_mult_monomial)
  then obtain q where "q \<in> P[U]" and g': "g = q * h" by (rule coneE)
  from \<open>g \<noteq> 0\<close> have "q \<noteq> 0" and "h \<noteq> 0" by (auto simp: g')
  hence lt_g': "lpp g = lpp q + lpp h" unfolding g' by (rule lp_times)
  hence adds1: "lpp h adds t" by (simp add: t_def)
  from assms(5) * have "is_monomial h" and "punit.lc h = 1" by (rule monomial_decompD)+
  moreover from this(1) have "monomial (punit.lc h) (lpp h) = h"
    by (rule punit.monomial_eq_itself)
  moreover define s where "s = lpp h"
  ultimately have h: "h = monomial 1 s" by simp
  have "punit.lc q = punit.lc g" by (simp add: g' lc_times \<open>punit.lc h = 1\<close>)
  hence "punit.lc q = 1" by (simp only: \<open>punit.lc g = 1\<close>)
  note tip_in_cone
  also from assms(4) * have "cone (h, U) \<subseteq> P[X] \<inter> ideal ?S" by (rule cone_decomp_cone_subset)
  also have "\<dots> \<subseteq> ideal ?G" by (simp add: ideal_G)
  finally have "h \<in> ideal ?G" .
  from assms(1) \<open>?S \<subseteq> P[X]\<close> have "punit.is_Groebner_basis ?G" by (rule reduced_GB_is_GB_Polys)
  then obtain g' where "g' \<in> ?G" and "g' \<noteq> 0" and adds2: "lpp g' adds lpp h"
    using \<open>h \<in> ideal ?G\<close> \<open>h \<noteq> 0\<close> by (rule punit.GB_adds_lt[simplified])
  from this(3) adds1 have "lpp g' adds t" by (rule adds_trans)
  with _ \<open>g' \<noteq> 0\<close> \<open>t \<in> keys g\<close> have "punit.is_red {g'} g"
    by (rule punit.is_red_addsI[simplified]) simp
  have "g' = g"
  proof (rule ccontr)
    assume "g' \<noteq> g"
    with \<open>g' \<in> ?G\<close> have "{g'} \<subseteq> ?G - {g}" by simp
    with \<open>punit.is_red {g'} g\<close> have red: "punit.is_red (?G - {g}) g" by (rule punit.is_red_subset)
    from assms(1) \<open>?S \<subseteq> P[X]\<close> have "punit.is_auto_reduced ?G" by (rule reduced_GB_is_auto_reduced_Polys)
    hence "\<not> punit.is_red (?G - {g}) g" using assms(3) by (rule punit.is_auto_reducedD)
    thus False using red ..
  qed
  with adds2 have "t adds lpp h" by (simp only: t_def)
  with adds1 have "lpp h = t" by (rule adds_antisym)
  hence "lpp q = 0" using lt_g' by (simp add: t_def)
  hence "monomial (punit.lc q) 0 = q" by (rule punit.lt_eq_min_term_monomial[simplified])
  hence "g = h" by (simp add: \<open>punit.lc q = 1\<close> g')
  with * have "(g, U) \<in> set ps" by simp
  thus ?thesis ..
qed

lemma snd_splitI:
  assumes "finite X" and "U \<subseteq> X" and "finite S" and "0 \<notin> S"
  obtains V where "V \<subseteq> U" and "(monomial 1 t, V) \<in> set (snd (split t U S))"
  using assms
proof (induct t U S arbitrary: thesis rule: split_induct)
  case (base1 t U S)
  from base1.prems(2) base1.hyps(3) show ?case ..
next
  case (base2 t U S)
  from subset_refl show ?case by (rule base2.prems) simp
next
  case (step t U S V0 x ps0 ps1 qs0 qs1)
  from step.hyps(3) obtain V where 1: "V \<subseteq> U - {x}" and 2: "(monomial 1 t, V) \<in> set (snd (ps0, qs0))"
    using step.hyps(15) by blast
  show ?case
  proof (rule step.prems)
    from 1 show "V \<subseteq> U" by blast
  next
    from 2 show "(monomial 1 t, V) \<in> set (snd (ps0 @ ps1, qs0 @ qs1))" by fastforce
  qed
qed

lemma fst_splitE:
  assumes "finite X" and "U \<subseteq> X" and "finite S" and "0 \<notin> S"
    and "(monomial (1::'a) s, V) \<in> set (fst (split t U S))"
  obtains t' x where "t' \<in> .[X]" and "x \<in> X" and "V \<subseteq> U" and "0 \<notin> (\<lambda>s. s - t') ` S"
    and "s = t' + t + Poly_Mapping.single x 1"
    and "(monomial (1::'a::zero_neq_one) s, V) \<in> set (fst (split (t' + t) V ((\<lambda>s. s - t') ` S)))"
    and "set (snd (split (t' + t) V ((\<lambda>s. s - t') ` S))) \<subseteq> (set (snd (split t U S)) :: ((_ \<Rightarrow>\<^sub>0 'a) \<times> _) set)"
  using assms
proof (induct t U S arbitrary: thesis rule: split_induct)
  case (base1 t U S)
  from base1.prems(2) base1.hyps(3) show ?case ..
next
  case (base2 t U S)
  from base2.prems(3) show ?case by simp
next
  case (step t U S V0 x ps0 ps1 qs0 qs1)
  from step.prems(3) have "(monomial 1 s, V) \<in> set ps0 \<union> set ps1" by simp
  thus ?case
  proof
    assume "(monomial 1 s, V) \<in> set ps0"
    hence "(monomial (1::'a) s, V) \<in> set (fst (ps0, qs0))" by (simp only: fst_conv)
    with step.hyps(3) obtain t' x' where "t' \<in> .[X]" and "x' \<in> X" and "V \<subseteq> U - {x}"
      and "0 \<notin> (\<lambda>s. s - t') ` S" and "s = t' + t + Poly_Mapping.single x' 1"
      and "(monomial (1::'a) s, V) \<in> set (fst (split (t' + t) V ((\<lambda>s. s - t') ` S)))"
      and "set (snd (split (t' + t) V ((\<lambda>s. s - t') ` S))) \<subseteq> set (snd (ps0, qs0))"
      using step.hyps(15) by blast
    note this(7)
    also have "set (snd (ps0, qs0)) \<subseteq> set (snd (ps0 @ ps1, qs0 @ qs1))" by simp
    finally have "set (snd (split (t' + t) V ((\<lambda>s. s - t') ` S))) \<subseteq> set (snd (ps0 @ ps1, qs0 @ qs1))" .
    from \<open>V \<subseteq> U - {x}\<close> have "V \<subseteq> U" by blast
    show ?thesis by (rule step.prems) fact+
  next
    assume "(monomial 1 s, V) \<in> set ps1"
    show ?thesis
    proof (cases "0 \<in> (\<lambda>f. f - Poly_Mapping.single x 1) ` S")
      case True
      from step.hyps(2) have fin: "finite ((\<lambda>f. f - Poly_Mapping.single x 1) ` S)"
        by (rule finite_imageI)
      have "split (Poly_Mapping.single x 1 + t) U ((\<lambda>f. f - Poly_Mapping.single x 1) ` S) =
              ([(monomial (1::'a) (Poly_Mapping.single x 1 + t), U)], [])"
        by (simp only: split.psimps[OF split_domI, OF assms(1) step.hyps(1) fin] True if_True)
      hence "ps1 = [(monomial 1 (Poly_Mapping.single x 1 + t), U)]"
        by (simp only: step.hyps(13)[symmetric] prod.inject)
      with \<open>(monomial 1 s, V) \<in> set ps1\<close> have s: "s = Poly_Mapping.single x 1 + t" and "V = U"
        by (auto dest!: monomial_inj)
      show ?thesis
      proof (rule step.prems)
        show "0 \<in> .[X]" by (fact zero_in_PPs)
      next
        from step.hyps(8, 1) show "x \<in> X" ..
      next
        show "V \<subseteq> U" by (simp add: \<open>V = U\<close>)
      next
        from step.hyps(3) show "0 \<notin> (\<lambda>s. s - 0) ` S" by simp
      next
        show "s = 0 + t + Poly_Mapping.single x 1" by (simp add: s add.commute)
      next
        show "(monomial (1::'a) s, V) \<in> set (fst (split (0 + t) V ((\<lambda>s. s - 0) ` S)))"
          using \<open>(monomial 1 s, V) \<in> set ps1\<close> by (simp add: step.hyps(14) \<open>V = U\<close>)
      next
        show "set (snd (split (0 + t) V ((\<lambda>s. s - 0) ` S))) \<subseteq> set (snd (ps0 @ ps1, qs0 @ qs1))"
          by (simp add: step.hyps(14) \<open>V = U\<close>)
      qed
    next
      case False
      moreover from \<open>(monomial 1 s, V) \<in> set ps1\<close> have "(monomial 1 s, V) \<in> set (fst (ps1, qs1))"
        by (simp only: fst_conv)
      ultimately obtain t' x' where "t' \<in> .[X]" and "x' \<in> X" and "V \<subseteq> U"
        and 1: "0 \<notin> (\<lambda>s. s - t') ` (\<lambda>f. f - Poly_Mapping.single x 1) ` S"
        and s: "s = t' + (Poly_Mapping.single x 1 + t) + Poly_Mapping.single x' 1"
        and 2: "(monomial (1::'a) s, V) \<in> set (fst (split (t' + (Poly_Mapping.single x 1 + t)) V
                                            ((\<lambda>s. s - t') ` (\<lambda>f. f - Poly_Mapping.single x 1) ` S)))"
        and 3: "set (snd (split (t' + (Poly_Mapping.single x 1 + t)) V ((\<lambda>s. s - t') ` (\<lambda>f. f - monomial 1 x) ` S))) \<subseteq>
                  set (snd (ps1, qs1))"
        using step.hyps(16) by blast
      have eq: "(\<lambda>s. s - t') ` (\<lambda>f. f - Poly_Mapping.single x 1) ` S =
                (\<lambda>s. s - (t' + Poly_Mapping.single x 1)) ` S"
        by (simp add: image_image add.commute diff_diff_eq)
      show ?thesis
      proof (rule step.prems)
        from step.hyps(8, 1) have "x \<in> X" ..
        hence "Poly_Mapping.single x 1 \<in> .[X]" by (rule PPs_closed_single)
        with \<open>t' \<in> .[X]\<close> show "t' + Poly_Mapping.single x 1 \<in> .[X]" by (rule PPs_closed_plus)
      next
        from 1 show "0 \<notin> (\<lambda>s. s - (t' + Poly_Mapping.single x 1)) ` S"
          by (simp only: eq not_False_eq_True)
      next
        show "s = t' + Poly_Mapping.single x 1 + t + Poly_Mapping.single x' 1" by (simp only: s ac_simps)
      next
        show "(monomial (1::'a) s, V) \<in> set (fst (split (t' + Poly_Mapping.single x 1 + t) V
                                                ((\<lambda>s. s - (t' + Poly_Mapping.single x 1)) ` S)))"
          using 2 by (simp only: eq add.assoc)
      next
        have "set (snd (split (t' + Poly_Mapping.single x 1 + t) V ((\<lambda>s. s - (t' + Poly_Mapping.single x 1)) ` S))) \<subseteq>
              set (snd (ps1, qs1))" (is "?x \<subseteq> _") using 3 by (simp only: eq add.assoc)
        also have "\<dots> \<subseteq> set (snd (ps0 @ ps1, qs0 @ qs1))" by simp
        finally show "?x \<subseteq> set (snd (ps0 @ ps1, qs0 @ qs1))" .
      qed fact+
    qed
  qed
qed

lemma lem_4_8:
  assumes "finite X" and "finite S" and "S \<subseteq> .[X]" and "0 \<notin> S"
    and "g \<in> punit.reduced_GB (monomial (1::'a) ` S)"
  obtains t U where "U \<subseteq> X" and "(monomial (1::'a::field) t, U) \<in> set (snd (split 0 X S))"
    and "poly_deg g = Suc (deg_pm t)"
proof -
  let ?S = "monomial (1::'a) ` S"
  let ?G = "punit.reduced_GB ?S"
  have md1: "monomial_decomp (fst ((split 0 X S)::(_ \<times> (((_ \<Rightarrow>\<^sub>0 'a) \<times> _) list))))"
    and md2: "monomial_decomp (snd ((split 0 X S)::(_ \<times> (((_ \<Rightarrow>\<^sub>0 'a) \<times> _) list))))"
    using assms(1) subset_refl assms(2) by (rule monomial_decomp_split)+
  from assms(3) have 0: "?S \<subseteq> P[X]" by (auto intro: Polys_closed_monomial)
  with assms(1) have "punit.is_auto_reduced ?G" and "punit.is_monic_set ?G"
    and ideal_G: "ideal ?G = ideal ?S" and "0 \<notin> ?G"
    by (rule reduced_GB_is_auto_reduced_Polys, rule reduced_GB_is_monic_set_Polys,
        rule reduced_GB_ideal_Polys, rule reduced_GB_nonzero_Polys)
  from this(2, 4) assms(5) have "punit.lc g = 1" by (auto simp: punit.is_monic_set_def)
  have "is_monomial_set ?S" by (auto intro!: is_monomial_setI monomial_is_monomial)
  with assms(1) 0 have "is_monomial_set ?G" by (rule reduced_GB_is_monomial_set_Polys)
  hence "is_monomial g" using assms(5) by (rule is_monomial_setD)
  moreover define s where "s = lpp g"
  ultimately have g: "g = monomial 1 s" using \<open>punit.lc g = 1\<close> by (metis punit.monomial_eq_itself)
  note assms(1) subset_refl assms(2) zero_in_PPs
  moreover have "ideal ?G \<div> monomial 1 0 = ideal ?S" by (simp add: ideal_G)
  ultimately have "splits_wrt (split 0 X S) (cone (monomial (1::'a) 0, X)) ?G" by (rule split_splits_wrt)
  hence "splits_wrt (fst (split 0 X S), snd (split 0 X S)) P[X] ?G" by simp
  hence "cone_decomp (P[X] \<inter> ideal ?G) (fst (split 0 X S))"
    using md2 \<open>is_monomial_set ?G\<close> by (rule splits_wrt_cone_decomp_1)
  hence "cone_decomp (P[X] \<inter> ideal ?S) (fst (split 0 X S))" by (simp only: ideal_G)
  with assms(1, 3, 5) obtain U where "(g, U) \<in> set (fst (split 0 X S))" using md1 by (rule lem_4_7)
  with assms(1) subset_refl assms(2, 4) obtain t' x where "t' \<in> .[X]" and "x \<in> X" and "U \<subseteq> X"
    and "0 \<notin> (\<lambda>s. s - t') ` S" and s: "s = t' + 0 + Poly_Mapping.single x 1"
    and "(g, U) \<in> set (fst (split (t' + 0) U ((\<lambda>s. s - t') ` S)))"
    and "set (snd (split (t' + 0) U ((\<lambda>s. s - t') ` S))) \<subseteq> (set (snd (split 0 X S)) :: ((_ \<Rightarrow>\<^sub>0 'a) \<times> _) set)"
    unfolding g by (rule fst_splitE)
  let ?S = "(\<lambda>s. s - t') ` S"
  from assms(2) have "finite ?S" by (rule finite_imageI)
  with assms(1) \<open>U \<subseteq> X\<close> obtain V where "V \<subseteq> U"
    and "(monomial (1::'a) (t' + 0), V) \<in> set (snd (split (t' + 0) U ?S))"
    using \<open>0 \<notin> ?S\<close> by (rule snd_splitI)
  note this(2)
  also have "\<dots> \<subseteq> set (snd (split 0 X S))" by fact
  finally have "(monomial (1::'a) t', V) \<in> set (snd (split 0 X S))" by simp
  have "poly_deg g = Suc (deg_pm t')" by (simp add: g s deg_pm_plus deg_pm_single poly_deg_monomial)
  from \<open>V \<subseteq> U\<close> \<open>U \<subseteq> X\<close> have "V \<subseteq> X" by (rule subset_trans)
  show ?thesis by rule fact+
qed

corollary cor_4_9:
  assumes "finite X" and "finite S" and "S \<subseteq> .[X]"
    and "g \<in> punit.reduced_GB (monomial (1::'a::field) ` S)"
  shows "poly_deg g \<le> Suc (Max (poly_deg ` fst ` (set (snd (split 0 X S)) :: ((_ \<Rightarrow>\<^sub>0 'a) \<times> _) set)))"
        (is "_ \<le> Suc (Max (poly_deg ` fst ` ?S))")
proof (cases "0 \<in> S")
  case True
  hence "1 \<in> monomial (1::'a) ` S" by (rule rev_image_eqI) (simp only: single_one)
  hence "1 \<in> ideal (monomial (1::'a) ` S)" by (rule ideal.span_base)
  hence "ideal (monomial (1::'a) ` S) = UNIV" by (simp only: ideal_eq_UNIV_iff_contains_one)
  moreover from assms(3) have "monomial (1::'a) ` S \<subseteq> P[X]" by (auto intro: Polys_closed_monomial)
  ultimately have "punit.reduced_GB (monomial (1::'a) ` S) = {1}"
    using assms(1) by (simp only: ideal_eq_UNIV_iff_reduced_GB_eq_one_Polys)
  with assms(4) show ?thesis by simp
next
  case False
  from finite_set have fin: "finite (poly_deg ` fst ` ?S)" by (intro finite_imageI)
  obtain t U where "(monomial 1 t, U) \<in> ?S" and g: "poly_deg g = Suc (deg_pm t)"
    using assms(1-3) False assms(4) by (rule lem_4_8)
  from this(1) have "poly_deg (fst (monomial (1::'a) t, U)) \<in> poly_deg ` fst ` ?S"
    by (intro imageI)
  hence "deg_pm t \<in> poly_deg ` fst ` ?S" by (simp add: poly_deg_monomial)
  with fin have "deg_pm t \<le> Max (poly_deg ` fst ` ?S)" by (rule Max_ge)
  thus "poly_deg g \<le> Suc (Max (poly_deg ` fst ` ?S))" by (simp add: g)
qed

lemma standard_decomp_snd_split:
  assumes "finite X" and "U \<subseteq> X" and "finite S" and "S \<subseteq> .[X]" and "t \<in> .[X]"
  shows "standard_decomp (deg_pm t) (snd (split t U S) :: ((_ \<Rightarrow>\<^sub>0 'a::field) \<times> _) list)"
  using assms
proof (induct t U S rule: split_induct)
  case (base1 t U S)
  show ?case by (simp add: standard_decomp_Nil)
next
  case (base2 t U S)
  have "deg_pm t = poly_deg (monomial (1::'a) t)" by (simp add: poly_deg_monomial)
  thus ?case by (simp add: standard_decomp_singleton)
next
  case (step t U S V x ps0 ps1 qs0 qs1)
  from step.hyps(15) step.prems have qs0: "standard_decomp (deg_pm t) qs0" by (simp only: snd_conv)
  have "(\<lambda>s. s - Poly_Mapping.single x 1) ` S \<subseteq> .[X]"
  proof
    fix u
    assume "u \<in> (\<lambda>s. s - Poly_Mapping.single x 1) ` S"
    then obtain s where "s \<in> S" and u: "u = s - Poly_Mapping.single x 1" ..
    from this(1) step.prems(1) have "s \<in> .[X]" ..
    thus "u \<in> .[X]" unfolding u by (rule PPs_closed_minus)
  qed
  moreover from _ step.prems(2) have "Poly_Mapping.single x 1 + t \<in> .[X]"
  proof (rule PPs_closed_plus)
    from step.hyps(8, 1) have "x \<in> X" ..
    thus "Poly_Mapping.single x 1 \<in> .[X]" by (rule PPs_closed_single)
  qed
  ultimately have qs1: "standard_decomp (Suc (deg_pm t)) qs1" using step.hyps(16)
    by (simp add: deg_pm_plus deg_pm_single)
  show ?case unfolding snd_conv
  proof (rule standard_decompI)
    fix h U0
    assume "(h, U0) \<in> set ((qs0 @ qs1)\<^sub>+)"
    hence *: "(h, U0) \<in> set (qs0\<^sub>+) \<union> set (qs1\<^sub>+)" by (simp add: pos_decomp_append)
    thus "deg_pm t \<le> poly_deg h"
    proof
      assume "(h, U0) \<in> set (qs0\<^sub>+)"
      with qs0 show ?thesis by (rule standard_decompD)
    next
      assume "(h, U0) \<in> set (qs1\<^sub>+)"
      with qs1 have "Suc (deg_pm t) \<le> poly_deg h" by (rule standard_decompD)
      thus ?thesis by simp
    qed

    fix d
    assume d1: "deg_pm t \<le> d" and d2: "d \<le> poly_deg h"
    from * show "\<exists>t' U'. (t', U') \<in> set (qs0 @ qs1) \<and> poly_deg t' = d \<and> card U0 \<le> card U'"
    proof
      assume "(h, U0) \<in> set (qs0\<^sub>+)"
      with qs0 obtain h' U' where "(h', U') \<in> set qs0" and "poly_deg h' = d" and "card U0 \<le> card U'"
        using d1 d2 by (rule standard_decompE)
      moreover from this(1) have "(h', U') \<in> set (qs0 @ qs1)" by simp
      ultimately show ?thesis by blast
    next
      assume "(h, U0) \<in> set (qs1\<^sub>+)"
      hence "(h, U0) \<in> set qs1" by (simp add: pos_decomp_def)
      from assms(1) step.hyps(1, 2) have "monomial_decomp (snd (split t U S) :: ((_ \<Rightarrow>\<^sub>0 'a) \<times> _) list)"
        by (rule monomial_decomp_split)
      hence md: "monomial_decomp (qs0 @ qs1)" by (simp add: step.hyps(14))
      moreover from \<open>(h, U0) \<in> set qs1\<close> have "(h, U0) \<in> set (qs0 @ qs1)" by simp
      ultimately have "is_monomial h" and "punit.lc h = 1" by (rule monomial_decompD)+
      moreover from this(1) have "monomial (punit.lc h) (lpp h) = h" by (rule punit.monomial_eq_itself)
      moreover define s where "s = lpp h"
      ultimately have h: "h = monomial 1 s" by simp
      from d1 have "deg_pm t = d \<or> Suc (deg_pm t) \<le> d" by auto
      thus ?thesis
      proof
        assume "deg_pm t = d"
        define F where "F = (*) (monomial 1 t) ` monomial (1::'a) ` S"
        have "F \<subseteq> P[X]"
        proof
          fix f
          assume "f \<in> F"
          then obtain u where "u \<in> S" and f: "f = monomial 1 (t + u)"
            by (auto simp: F_def times_monomial_monomial)
          from this(1) step.prems(1) have "u \<in> .[X]" ..
          with step.prems(2) have "t + u \<in> .[X]" by (rule PPs_closed_plus)
          thus "f \<in> P[X]" unfolding f by (rule Polys_closed_monomial)
        qed
        have "ideal F = (*) (monomial 1 t) ` ideal (monomial 1 ` S)"
          by (simp only: ideal.span_image_scale_eq_image_scale F_def)
        moreover have "inj ((*) (monomial (1::'a) t))"
          by (auto intro!: injI simp: times_monomial_left monomial_0_iff dest!: punit.monom_mult_inj_3)
        ultimately have eq: "ideal F \<div> monomial 1 t = ideal (monomial 1 ` S)"
          by (simp only: quot_set_image_times)
        with assms(1) step.hyps(1, 2) step.prems(2)
        have "splits_wrt (split t U S) (cone (monomial (1::'a) t, U)) F" by (rule split_splits_wrt)
        hence "splits_wrt (ps0 @ ps1, qs0 @ qs1) (cone (monomial 1 t, U)) F" by (simp only: step.hyps(14))
        with assms(1) have "cone_decomp (cone (monomial (1::'a) t, U) \<inter> normal_form F ` P[X]) (qs0 @ qs1)"
          using md _ \<open>F \<subseteq> P[X]\<close>
          by (rule splits_wrt_cone_decomp_2)
              (auto intro!: is_monomial_setI monomial_is_monomial simp: F_def times_monomial_monomial)
        hence "cone (monomial 1 s, U0) \<subseteq> cone (monomial (1::'a) t, U) \<inter> normal_form F ` P[X]"
          using \<open>(h, U0) \<in> set (qs0 @ qs1)\<close> unfolding h by (rule cone_decomp_cone_subset)
        with assms(1) step.hyps(1, 2) step.prems(2) \<open>F \<subseteq> P[X]\<close> eq
        obtain U' where "(monomial (1::'a) t, U') \<in> set (snd (split t U S))" and "card U0 \<le> card U'"
          by (rule lem_4_6)
        from this(1) have "(monomial 1 t, U') \<in> set (qs0 @ qs1)" by (simp add: step.hyps(14))
        show ?thesis
        proof (intro exI conjI)
          show "poly_deg (monomial (1::'a) t) = d" by (simp add: poly_deg_monomial \<open>deg_pm t = d\<close>)
        qed fact+
      next
        assume "Suc (deg_pm t) \<le> d"
        with qs1 \<open>(h, U0) \<in> set (qs1\<^sub>+)\<close> obtain h' U' where "(h', U') \<in> set qs1" and "poly_deg h' = d"
          and "card U0 \<le> card U'" using d2 by (rule standard_decompE)
        moreover from this(1) have "(h', U') \<in> set (qs0 @ qs1)" by simp
        ultimately show ?thesis by blast
      qed
    qed
  qed
qed

theorem standard_cone_decomp_snd_split:
  fixes F
  defines "G \<equiv> punit.reduced_GB F"
  defines "ss \<equiv> (split 0 X (lpp ` G)) :: ((_ \<Rightarrow>\<^sub>0 'a::field) \<times> _) list \<times> _"
  defines "d \<equiv> Suc (Max (poly_deg ` fst ` set (snd ss)))"
  assumes "finite X" and "F \<subseteq> P[X]"
  shows "standard_decomp 0 (snd ss)" (is ?thesis1)
    and "cone_decomp (normal_form F ` P[X]) (snd ss)" (is ?thesis2)
    and "(\<And>f. f \<in> F \<Longrightarrow> homogeneous f) \<Longrightarrow> g \<in> G \<Longrightarrow> poly_deg g \<le> d"
proof -
  have "ideal G = ideal F" and "punit.is_Groebner_basis G" and "finite G" and "0 \<notin> G"
    and "G \<subseteq> P[X]" and "punit.is_reduced_GB G" using assms(4, 5) unfolding G_def
    by (rule reduced_GB_ideal_Polys, rule reduced_GB_is_GB_Polys, rule finite_reduced_GB_Polys,
        rule reduced_GB_nonzero_Polys, rule reduced_GB_Polys, rule reduced_GB_is_reduced_GB_Polys)
  define S where "S = lpp ` G"
  note assms(4) subset_refl
  moreover from \<open>finite G\<close> have "finite S" unfolding S_def by (rule finite_imageI)
  moreover from \<open>G \<subseteq> P[X]\<close> have "S \<subseteq> .[X]" unfolding S_def by (rule PPs_closed_image_lpp)
  ultimately have "standard_decomp (deg_pm (0::'x \<Rightarrow>\<^sub>0 nat)) (snd ss)"
    using zero_in_PPs unfolding ss_def S_def by (rule standard_decomp_snd_split)
  thus ?thesis1 by simp

  let ?S = "monomial (1::'a) ` S"
  from \<open>S \<subseteq> .[X]\<close> have "?S \<subseteq> P[X]" by (auto intro: Polys_closed_monomial)
  have "splits_wrt ss (cone (monomial 1 0, X)) ?S"
    using assms(4) subset_refl \<open>finite S\<close> zero_in_PPs unfolding ss_def S_def
    by (rule split_splits_wrt) simp
  hence "splits_wrt (fst ss, snd ss) P[X] ?S" by simp
  with assms(4) have "cone_decomp (P[X] \<inter> normal_form ?S ` P[X]) (snd ss)" using _ _ \<open>?S \<subseteq> P[X]\<close>
  proof (rule splits_wrt_cone_decomp_2)
    from assms(4) subset_refl \<open>finite S\<close> show "monomial_decomp (snd ss)"
      unfolding ss_def S_def by (rule monomial_decomp_split)
  qed (auto intro!: is_monomial_setI monomial_is_monomial)
  moreover have "normal_form ?S ` P[X] = normal_form F ` P[X]"
    by (rule set_eqI)
        (simp add: image_normal_form_iff[OF assms(4)] assms(5) \<open>?S \<subseteq> P[X]\<close>,
         simp add: S_def is_red_reduced_GB_monomial_lt_GB_Polys[OF assms(4)] \<open>G \<subseteq> P[X]\<close> \<open>0 \<notin> G\<close> flip: G_def)
  moreover from assms(4, 5) have "normal_form F ` P[X] \<subseteq> P[X]"
    by (auto intro: Polys_closed_normal_form)
  ultimately show ?thesis2 by (simp only: Int_absorb1)

  assume "\<And>f. f \<in> F \<Longrightarrow> homogeneous f"
  moreover note \<open>punit.is_reduced_GB G\<close> \<open>ideal G = ideal F\<close>
  moreover assume "g \<in> G"
  ultimately have "homogeneous g" by (rule is_reduced_GB_homogeneous)
  moreover have "lpp g \<in> keys g"
  proof (rule punit.lt_in_keys)
    from \<open>g \<in> G\<close> \<open>0 \<notin> G\<close> show "g \<noteq> 0" by blast
  qed
  ultimately have deg_lt: "deg_pm (lpp g) = poly_deg g" by (rule homogeneousD_poly_deg)
  from \<open>g \<in> G\<close> have "monomial 1 (lpp g) \<in> ?S" unfolding S_def by (intro imageI)
  also have "\<dots> = punit.reduced_GB ?S" unfolding S_def G_def using assms(4, 5)
    by (rule reduced_GB_monomial_lt_reduced_GB_Polys[symmetric])
  finally have "monomial 1 (lpp g) \<in> punit.reduced_GB ?S" .
  with assms(4) \<open>finite S\<close> \<open>S \<subseteq> .[X]\<close> have "poly_deg (monomial (1::'a) (lpp g)) \<le> d"
    unfolding d_def ss_def S_def[symmetric] by (rule cor_4_9)
  thus "poly_deg g \<le> d" by (simp add: poly_deg_monomial deg_lt)
qed

subsection \<open>Splitting Ideals\<close>

qualified definition ideal_decomp_aux :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow>
                                          ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) set \<times> ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) list)"
  where "ideal_decomp_aux F f =
              (let J = ideal F; L = (J \<div> f) \<inter> P[X]; L' = lpp ` punit.reduced_GB L in
                 ((*) f ` normal_form L ` P[X], map (apfst ((*) f)) (snd (split 0 X L'))))"

context
  assumes fin_X: "finite X"
begin

lemma ideal_decomp_aux:
  assumes "finite F" and "F \<subseteq> P[X]" and "f \<in> P[X]"
  shows "fst (ideal_decomp_aux F f) \<subseteq> ideal {f}" (is ?thesis1)
    and "ideal F \<inter> fst (ideal_decomp_aux F f) = {0}" (is ?thesis2)
    and "direct_decomp (ideal (insert f F) \<inter> P[X]) [fst (ideal_decomp_aux F f), ideal F \<inter> P[X]]" (is ?thesis3)
    and "cone_decomp (fst (ideal_decomp_aux F f)) (snd (ideal_decomp_aux F f))" (is ?thesis4)
    and "f \<noteq> 0 \<Longrightarrow> valid_decomp X (snd (ideal_decomp_aux F f))" (is "_ \<Longrightarrow> ?thesis5")
    and "f \<noteq> 0 \<Longrightarrow> standard_decomp (poly_deg f) (snd (ideal_decomp_aux F f))" (is "_ \<Longrightarrow> ?thesis6")
    and "homogeneous f \<Longrightarrow> hom_decomp (snd (ideal_decomp_aux F f))" (is "_ \<Longrightarrow> ?thesis7")
proof -
  define J where "J = ideal F"
  define L where "L = (J \<div> f) \<inter> P[X]"
  define S where "S = (*) f ` normal_form L ` P[X]"
  define L' where "L' = lpp ` punit.reduced_GB L"

  have eq: "ideal_decomp_aux F f = (S, map (apfst ((*) f)) (snd (split 0 X L')))"
    by (simp add: J_def ideal_decomp_aux_def Let_def L_def L'_def S_def)

  have L_sub: "L \<subseteq> P[X]" by (simp add: L_def)

  show ?thesis1 unfolding eq fst_conv
  proof
    fix s
    assume "s \<in> S"
    then obtain q where "s = normal_form L q * f" unfolding S_def by (elim imageE) auto
    also have "\<dots> \<in> ideal {f}" by (intro ideal.span_scale ideal.span_base singletonI)
    finally show "s \<in> ideal {f}" .
  qed

  show ?thesis2
  proof (rule set_eqI)
    fix h
    show "h \<in> ideal F \<inter> fst (ideal_decomp_aux F f) \<longleftrightarrow> h \<in> {0}"
    proof
      assume "h \<in> ideal F \<inter> fst (ideal_decomp_aux F f)"
      hence "h \<in> J" and "h \<in> S" by (simp_all add: J_def S_def eq)
      from this(2) obtain q where "q \<in> P[X]" and h: "h = f * normal_form L q" by (auto simp: S_def)
      from fin_X L_sub this(1) have "normal_form L q \<in> P[X]" by (rule Polys_closed_normal_form)
      moreover from \<open>h \<in> J\<close> have "f * normal_form L q \<in> J" by (simp add: h)
      ultimately have "normal_form L q \<in> L" by (simp add: L_def quot_set_iff)
      hence "normal_form L q \<in> ideal L" by (rule ideal.span_base)
      with normal_form_diff_in_ideal[OF fin_X L_sub] have "(q - normal_form L q) + normal_form L q \<in> ideal L"
        by (rule ideal.span_add)
      hence "normal_form L q = 0" using fin_X L_sub by (simp add: normal_form_zero_iff)
      thus "h \<in> {0}" by (simp add: h)
    next
      assume "h \<in> {0}"
      moreover have "0 \<in> (*) f ` normal_form L ` P[X]"
      proof (intro image_eqI)
        from fin_X L_sub show "0 = normal_form L 0" by (simp only: normal_form_zero)
      qed (simp_all add: zero_in_Polys)
      ultimately show "h \<in> ideal F \<inter> fst (ideal_decomp_aux F f)" by (simp add: ideal.span_zero eq S_def)
    qed
  qed

  have "direct_decomp (ideal (insert f F) \<inter> P[X]) [ideal F \<inter> P[X], fst (ideal_decomp_aux F f)]"
    unfolding eq fst_conv S_def L_def J_def using fin_X assms(2, 3) by (rule direct_decomp_ideal_insert)
  thus ?thesis3 using perm.swap by (rule direct_decomp_perm)

  have std: "standard_decomp 0 (snd (split 0 X L') :: ((_ \<Rightarrow>\<^sub>0 'a) \<times> _) list)"
    and "cone_decomp (normal_form L ` P[X]) (snd (split 0 X L'))"
    unfolding L'_def using fin_X \<open>L \<subseteq> P[X]\<close> by (rule standard_cone_decomp_snd_split)+
  from this(2) show ?thesis4 unfolding eq fst_conv snd_conv S_def by (rule cone_decomp_map_times)

  from fin_X \<open>L \<subseteq> P[X]\<close> have "finite (punit.reduced_GB L)" by (rule finite_reduced_GB_Polys)
  hence "finite L'" unfolding L'_def by (rule finite_imageI)
  {
    have "monomial_decomp (snd (split 0 X L') :: ((_ \<Rightarrow>\<^sub>0 'a) \<times> _) list)"
      using fin_X subset_refl \<open>finite L'\<close> by (rule monomial_decomp_split)
    hence "hom_decomp (snd (split 0 X L') :: ((_ \<Rightarrow>\<^sub>0 'a) \<times> _) list)"
      by (rule monomial_decomp_imp_hom_decomp)
    moreover assume "homogeneous f"
    ultimately show ?thesis7 unfolding eq snd_conv by (rule hom_decomp_map_times)
  }

  have vd: "valid_decomp X (snd (split 0 X L') :: ((_ \<Rightarrow>\<^sub>0 'a) \<times> _) list)"
    using fin_X subset_refl \<open>finite L'\<close> zero_in_PPs by (rule valid_decomp_split)
  moreover note assms(3)
  moreover assume "f \<noteq> 0"
  ultimately show ?thesis5 unfolding eq snd_conv by (rule valid_decomp_map_times)

  from std vd \<open>f \<noteq> 0\<close> have "standard_decomp (0 + poly_deg f) (map (apfst ((*) f)) (snd (split 0 X L')))"
    by (rule standard_decomp_map_times)
  thus ?thesis6 by (simp add: eq)
qed

lemma ideal_decompE:
  fixes f0 :: "_ \<Rightarrow>\<^sub>0 'a::field"
  assumes "finite F" and "F \<subseteq> P[X]" and "f0 \<in> P[X]" and "\<And>f. f \<in> F \<Longrightarrow> poly_deg f \<le> poly_deg f0"
  obtains T ps where "valid_decomp X ps" and "standard_decomp (poly_deg f0) ps" and "cone_decomp T ps"
    and "(\<And>f. f \<in> F \<Longrightarrow> homogeneous f) \<Longrightarrow> hom_decomp ps"
    and "direct_decomp (ideal (insert f0 F) \<inter> P[X]) [ideal {f0} \<inter> P[X], T]"
  using assms(1, 2, 4)
proof (induct F arbitrary: thesis)
  case empty
  show ?case
  proof (rule empty.prems)
    show "valid_decomp X []" by (rule valid_decompI) simp_all
  next
    show "standard_decomp (poly_deg f0) []" by (rule standard_decompI) simp_all
  next
    show "cone_decomp {0} []" by (rule cone_decompI) (simp add: direct_decomp_def bij_betw_def)
  next
    have "direct_decomp (ideal {f0} \<inter> P[X]) [ideal {f0} \<inter> P[X]]"
      by (fact direct_decomp_singleton)
    hence "direct_decomp (ideal {f0} \<inter> P[X]) [{0}, ideal {f0} \<inter> P[X]]" by (rule direct_decomp_Cons_zeroI)
    thus "direct_decomp (ideal {f0} \<inter> P[X]) [ideal {f0} \<inter> P[X], {0}]"
      using perm.swap by (rule direct_decomp_perm)
  qed (simp add: hom_decomp_def)
next
  case (insert f F)
  from insert.prems(2) have "F \<subseteq> P[X]" by simp
  moreover have "poly_deg f' \<le> poly_deg f0" if "f' \<in> F" for f'
  proof -
    from that have "f' \<in> insert f F" by simp
    thus ?thesis by (rule insert.prems)
  qed
  ultimately obtain T ps where valid_ps: "valid_decomp X ps" and std_ps: "standard_decomp (poly_deg f0) ps"
    and cn_ps: "cone_decomp T ps" and dd: "direct_decomp (ideal (insert f0 F) \<inter> P[X]) [ideal {f0} \<inter> P[X], T]"
    and hom_ps: "(\<And>f. f \<in> F \<Longrightarrow> homogeneous f) \<Longrightarrow> hom_decomp ps"
    using insert.hyps(3) by metis
  show ?case
  proof (cases "f = 0")
    case True
    show ?thesis
    proof (rule insert.prems)
      from dd show "direct_decomp (ideal (insert f0 (insert f F)) \<inter> P[X]) [ideal {f0} \<inter> P[X], T]"
        by (simp only: insert_commute[of f0] True ideal.span_insert_zero)
    next
      assume "\<And>f'. f' \<in> insert f F \<Longrightarrow> homogeneous f'"
      hence "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" by blast
      thus "hom_decomp ps" by (rule hom_ps)
    qed fact+
  next
    case False
    let ?D = "ideal_decomp_aux (insert f0 F) f"
    from insert.hyps(1) have f0F_fin: "finite (insert f0 F)" by simp
    moreover from \<open>F \<subseteq> P[X]\<close> assms(3) have f0F_sub: "insert f0 F \<subseteq> P[X]" by simp
    moreover from insert.prems(2) have "f \<in> P[X]" by simp
    ultimately have eq: "ideal (insert f0 F) \<inter> fst ?D = {0}" and "valid_decomp X (snd ?D)"
      and cn_D: "cone_decomp (fst ?D) (snd ?D)"
      and "standard_decomp (poly_deg f) (snd ?D)"
      and dd': "direct_decomp (ideal (insert f (insert f0 F)) \<inter> P[X])
                  [fst ?D, ideal (insert f0 F) \<inter> P[X]]"
      and hom_D: "homogeneous f \<Longrightarrow> hom_decomp (snd ?D)"
      by (rule ideal_decomp_aux, auto intro: ideal_decomp_aux simp: False)
    note fin_X this(2-4)
    moreover have "poly_deg f \<le> poly_deg f0" by (rule insert.prems) simp
    ultimately obtain qs where valid_qs: "valid_decomp X qs" and cn_qs: "cone_decomp (fst ?D) qs"
      and std_qs: "standard_decomp (poly_deg f0) qs"
      and hom_qs: "hom_decomp (snd ?D) \<Longrightarrow> hom_decomp qs" by (rule standard_decomp_geE) blast
    let ?T = "sum_list ` listset [T, fst ?D]"
    let ?ps = "ps @ qs"
    show ?thesis
    proof (rule insert.prems)
      from valid_ps valid_qs show "valid_decomp X ?ps" by (rule valid_decomp_append)
    next
      from std_ps std_qs show "standard_decomp (poly_deg f0) ?ps" by (rule standard_decomp_append)
    next
      from dd perm.swap have "direct_decomp (ideal (insert f0 F) \<inter> P[X]) [T, ideal {f0} \<inter> P[X]]"
        by (rule direct_decomp_perm)
      hence "T \<subseteq> ideal (insert f0 F) \<inter> P[X]"
        by (rule direct_decomp_Cons_subsetI) (simp add: ideal.span_zero zero_in_Polys)
      hence "T \<inter> fst ?D \<subseteq> ideal (insert f0 F) \<inter> fst ?D" by blast
      hence "T \<inter> fst ?D \<subseteq> {0}" by (simp only: eq)
      from refl have "direct_decomp ?T [T, fst ?D]"
      proof (intro direct_decompI inj_onI)
        fix xs ys
        assume "xs \<in> listset [T, fst ?D]"
        then obtain x1 x2 where "x1 \<in> T" and "x2 \<in> fst ?D" and xs: "xs = [x1, x2]"
          by (rule listset_doubletonE)
        assume "ys \<in> listset [T, fst ?D]"
        then obtain y1 y2 where "y1 \<in> T" and "y2 \<in> fst ?D" and ys: "ys = [y1, y2]"
          by (rule listset_doubletonE)
        assume "sum_list xs = sum_list ys"
        hence "x1 - y1 = y2 - x2" by (simp add: xs ys) (metis add_diff_cancel_left add_diff_cancel_right)
        moreover from cn_ps \<open>x1 \<in> T\<close> \<open>y1 \<in> T\<close> have "x1 - y1 \<in> T" by (rule cone_decomp_closed_minus)
        moreover from cn_D \<open>y2 \<in> fst ?D\<close> \<open>x2 \<in> fst ?D\<close> have "y2 - x2 \<in> fst ?D"
          by (rule cone_decomp_closed_minus)
        ultimately have "y2 - x2 \<in> T \<inter> fst ?D" by simp
        also have "\<dots> \<subseteq> {0}" by fact
        finally have "x2 = y2" by simp
        with \<open>x1 - y1 = y2 - x2\<close> show "xs = ys" by (simp add: xs ys)
      qed
      thus "cone_decomp ?T ?ps" using cn_ps cn_qs by (rule cone_decomp_append)
    next
      assume "\<And>f'. f' \<in> insert f F \<Longrightarrow> homogeneous f'"
      hence "homogeneous f" and "\<And>f'. f' \<in> F \<Longrightarrow> homogeneous f'" by blast+
      from this(2) have "hom_decomp ps" by (rule hom_ps)
      moreover from \<open>homogeneous f\<close> have "hom_decomp qs" by (intro hom_qs hom_D)
      ultimately show "hom_decomp (ps @ qs)" by (simp only: hom_decomp_append_iff)
    next
      from dd' have "direct_decomp (ideal (insert f0 (insert f F)) \<inter> P[X])
                      [ideal (insert f0 F) \<inter> P[X], fst ?D]"
        by (simp add: insert_commute direct_decomp_perm perm.swap)
      hence "direct_decomp (ideal (insert f0 (insert f F)) \<inter> P[X])
                      ([fst ?D] @ [ideal {f0} \<inter> P[X], T])" using dd by (rule direct_decomp_direct_decomp)
      hence "direct_decomp (ideal (insert f0 (insert f F)) \<inter> P[X]) ([ideal {f0} \<inter> P[X]] @ [T, fst ?D])"
        by (rule direct_decomp_perm) auto
      hence "direct_decomp (ideal (insert f0 (insert f F)) \<inter> P[X]) [sum_list ` listset [ideal {f0} \<inter> P[X]], ?T]"
        by (rule direct_decomp_appendD)
      thus "direct_decomp (ideal (insert f0 (insert f F)) \<inter> P[X]) [ideal {f0} \<inter> P[X], ?T]"
        by (simp add: image_image)
    qed
  qed
qed

subsection \<open>Exact Cone Decompositions\<close>

definition exact_decomp :: "nat \<Rightarrow> ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) \<times> 'x set) list \<Rightarrow> bool"
  where "exact_decomp m ps \<longleftrightarrow> (\<forall>(h, U)\<in>set ps. h \<in> P[X] \<and> U \<subseteq> X) \<and>
                              (\<forall>(h, U)\<in>set ps. \<forall>(h', U')\<in>set ps. poly_deg h = poly_deg h' \<longrightarrow>
                                          m < card U \<longrightarrow> m < card U' \<longrightarrow> (h, U) = (h', U'))"

lemma exact_decompI:
  "(\<And>h U. (h, U) \<in> set ps \<Longrightarrow> h \<in> P[X]) \<Longrightarrow> (\<And>h U. (h, U) \<in> set ps \<Longrightarrow> U \<subseteq> X) \<Longrightarrow>
    (\<And>h h' U U'. (h, U) \<in> set ps \<Longrightarrow> (h', U') \<in> set ps \<Longrightarrow> poly_deg h = poly_deg h' \<Longrightarrow>
            m < card U \<Longrightarrow> m < card U' \<Longrightarrow> (h, U) = (h', U')) \<Longrightarrow>
    exact_decomp m ps"
  unfolding exact_decomp_def by fastforce

lemma exact_decompD:
  assumes "exact_decomp m ps" and "(h, U) \<in> set ps"
  shows "h \<in> P[X]" and "U \<subseteq> X"
    and "(h', U') \<in> set ps \<Longrightarrow> poly_deg h = poly_deg h' \<Longrightarrow> m < card U \<Longrightarrow> m < card U' \<Longrightarrow>
            (h, U) = (h', U')"
  using assms unfolding exact_decomp_def by fastforce+

lemma exact_decompI_zero:
  assumes "\<And>h U. (h, U) \<in> set ps \<Longrightarrow> h \<in> P[X]" and "\<And>h U. (h, U) \<in> set ps \<Longrightarrow> U \<subseteq> X"
    and "\<And>h h' U U'. (h, U) \<in> set (ps\<^sub>+) \<Longrightarrow> (h', U') \<in> set (ps\<^sub>+) \<Longrightarrow> poly_deg h = poly_deg h' \<Longrightarrow>
              (h, U) = (h', U')"
  shows "exact_decomp 0 ps"
  using assms(1, 2)
proof (rule exact_decompI)
  fix h h' and U U' :: "'x set"
  assume "0 < card U"
  hence "U \<noteq> {}" by auto
  moreover assume "(h, U) \<in> set ps"
  ultimately have "(h, U) \<in> set (ps\<^sub>+)" by (simp add: pos_decomp_def)
  assume "0 < card U'"
  hence "U' \<noteq> {}" by auto
  moreover assume "(h', U') \<in> set ps"
  ultimately have "(h', U') \<in> set (ps\<^sub>+)" by (simp add: pos_decomp_def)
  assume "poly_deg h = poly_deg h'"
  with \<open>(h, U) \<in> set (ps\<^sub>+)\<close> \<open>(h', U') \<in> set (ps\<^sub>+)\<close> show "(h, U) = (h', U')" by (rule assms(3))
qed

lemma exact_decompD_zero:
  assumes "exact_decomp 0 ps" and "(h, U) \<in> set (ps\<^sub>+)" and "(h', U') \<in> set (ps\<^sub>+)"
    and "poly_deg h = poly_deg h'"
  shows "(h, U) = (h', U')"
proof -
  from assms(2) have "(h, U) \<in> set ps" and "U \<noteq> {}" by (simp_all add: pos_decomp_def)
  from assms(1) this(1) have "U \<subseteq> X" by (rule exact_decompD)
  hence "finite U" using fin_X by (rule finite_subset)
  with \<open>U \<noteq> {}\<close> have "0 < card U" by (simp add: card_gt_0_iff)
  from assms(3) have "(h', U') \<in> set ps" and "U' \<noteq> {}" by (simp_all add: pos_decomp_def)
  from assms(1) this(1) have "U' \<subseteq> X" by (rule exact_decompD)
  hence "finite U'" using fin_X by (rule finite_subset)
  with \<open>U' \<noteq> {}\<close> have "0 < card U'" by (simp add: card_gt_0_iff)
  show ?thesis by (rule exact_decompD) fact+
qed

lemma exact_decomp_imp_valid_decomp:
  assumes "exact_decomp m ps" and "\<And>h U. (h, U) \<in> set ps \<Longrightarrow> h \<noteq> 0"
  shows "valid_decomp X ps"
proof (rule valid_decompI)
  fix h U
  assume *: "(h, U) \<in> set ps"
  with assms(1) show "h \<in> P[X]" and "U \<subseteq> X" by (rule exact_decompD)+
  from * show "h \<noteq> 0" by (rule assms(2))
qed

lemma exact_decomp_card_X:
  assumes "valid_decomp X ps" and "card X \<le> m"
  shows "exact_decomp m ps"
proof (rule exact_decompI)
  fix h U
  assume "(h, U) \<in> set ps"
  with assms(1) show "h \<in> P[X]" and "U \<subseteq> X" by (rule valid_decompD)+
next
  fix h1 h2 U1 U2
  assume "(h1, U1) \<in> set ps"
  with assms(1) have "U1 \<subseteq> X" by (rule valid_decompD)
  with fin_X have "card U1 \<le> card X" by (rule card_mono)
  also have "\<dots> \<le> m" by (fact assms(2))
  also assume "m < card U1"
  finally show "(h1, U1) = (h2, U2)" by simp
qed

definition \<a> :: "((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) \<times> 'x set) list \<Rightarrow> nat"
  where "\<a> ps = (LEAST k. standard_decomp k ps)"

definition \<b> :: "((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) \<times> 'x set) list \<Rightarrow> nat \<Rightarrow> nat"
  where "\<b> ps i = (LEAST d. \<a> ps \<le> d \<and> (\<forall>(h, U)\<in>set ps. i \<le> card U \<longrightarrow> poly_deg h < d))"

lemma \<a>: "standard_decomp k ps \<Longrightarrow> standard_decomp (\<a> ps) ps"
  unfolding \<a>_def by (rule LeastI)

lemma \<a>_Nil:
  assumes "ps\<^sub>+ = []"
  shows "\<a> ps = 0"
proof -
  from assms have "standard_decomp 0 ps" by (rule standard_decomp_Nil)
  thus ?thesis unfolding \<a>_def by (rule Least_eq_0)
qed

lemma \<a>_nonempty:
  assumes "valid_decomp X ps" and "standard_decomp k ps" and "ps\<^sub>+ \<noteq> []"
  shows "\<a> ps = Min (poly_deg ` fst ` set (ps\<^sub>+))"
  using fin_X assms(1) _ assms(3)
proof (rule standard_decomp_nonempty_unique)
  from assms(2) show "standard_decomp (\<a> ps) ps" by (rule \<a>)
qed

lemma \<a>_nonempty_unique:
  assumes "valid_decomp X ps" and "standard_decomp k ps" and "ps\<^sub>+ \<noteq> []"
  shows "\<a> ps = k"
proof -
  from assms have "\<a> ps = Min (poly_deg ` fst ` set (ps\<^sub>+))" by (rule \<a>_nonempty)
  moreover from fin_X assms have "k = Min (poly_deg ` fst ` set (ps\<^sub>+))"
    by (rule standard_decomp_nonempty_unique)
  ultimately show ?thesis by simp
qed

lemma \<b>:
  shows "\<a> ps \<le> \<b> ps i" and "(h, U) \<in> set ps \<Longrightarrow> i \<le> card U \<Longrightarrow> poly_deg h < \<b> ps i"
proof -
  let ?A = "poly_deg ` fst ` set ps"
  define A where "A = insert (\<a> ps) ?A"
  define m where "m = Suc (Max A)"
  from finite_set have "finite ?A" by (intro finite_imageI)
  hence "finite A" by (simp add: A_def)
  have "\<a> ps \<le> \<b> ps i \<and> (\<forall>(h', U')\<in>set ps. i \<le> card U' \<longrightarrow> poly_deg h' < \<b> ps i)" unfolding \<b>_def
  proof (rule LeastI)
    have "\<a> ps \<in> A" by (simp add: A_def)
    with \<open>finite A\<close> have "\<a> ps \<le> Max A" by (rule Max_ge)
    hence "\<a> ps \<le> m" by (simp add: m_def)
    moreover {
      fix h U
      assume "(h, U) \<in> set ps"
      hence "poly_deg (fst (h, U)) \<in> ?A" by (intro imageI)
      hence "poly_deg h \<in> A" by (simp add: A_def)
      with \<open>finite A\<close> have "poly_deg h \<le> Max A" by (rule Max_ge)
      hence "poly_deg h < m" by (simp add: m_def)
    }
    ultimately show "\<a> ps \<le> m \<and> (\<forall>(h, U)\<in>set ps. i \<le> card U \<longrightarrow> poly_deg h < m)" by blast
  qed
  thus "\<a> ps \<le> \<b> ps i" and "(h, U) \<in> set ps \<Longrightarrow> i \<le> card U \<Longrightarrow> poly_deg h < \<b> ps i" by blast+
qed

lemma \<b>_le:
  "\<a> ps \<le> d \<Longrightarrow> (\<And>h' U'. (h', U') \<in> set ps \<Longrightarrow> i \<le> card U' \<Longrightarrow> poly_deg h' < d) \<Longrightarrow> \<b> ps i \<le> d"
  unfolding \<b>_def by (intro Least_le) blast

lemma \<b>_decreasing:
  assumes "i \<le> j"
  shows "\<b> ps j \<le> \<b> ps i"
proof (rule \<b>_le)
  fix h U
  assume "(h, U) \<in> set ps"
  assume "j \<le> card U"
  with assms(1) have "i \<le> card U" by (rule le_trans)
  with \<open>(h, U) \<in> set ps\<close> show "poly_deg h < \<b> ps i" by (rule \<b>)
qed (fact \<b>)

lemma \<b>_Nil:
  assumes "ps\<^sub>+ = []" and "Suc 0 \<le> i"
  shows "\<b> ps i = 0"
  unfolding \<b>_def
proof (rule Least_eq_0)
  from assms(1) have "\<a> ps = 0" by (rule \<a>_Nil)
  moreover {
    fix h and U::"'x set"
    note assms(2)
    also assume "i \<le> card U"
    finally have "U \<noteq> {}" by auto
    moreover assume "(h, U) \<in> set ps"
    ultimately have "(h, U) \<in> set (ps\<^sub>+)" by (simp add: pos_decomp_def)
    hence False by (simp add: assms)
  }
  ultimately show "\<a> ps \<le> 0 \<and> (\<forall>(h, U)\<in>set ps. i \<le> card U \<longrightarrow> poly_deg h < 0)" by blast
qed

lemma \<b>_zero:
  assumes "ps \<noteq> []"
  shows "Suc (Max (poly_deg ` fst ` set ps)) \<le> \<b> ps 0"
proof -
  from finite_set have "finite (poly_deg ` fst ` set ps)" by (intro finite_imageI)
  moreover from assms have "poly_deg ` fst ` set ps \<noteq> {}" by simp
  moreover have "\<forall>a\<in>poly_deg ` fst ` set ps. a < \<b> ps 0"
  proof
    fix d
    assume "d \<in> poly_deg ` fst ` set ps"
    then obtain p where "p \<in> set ps" and "d = poly_deg (fst p)" by blast
    moreover obtain h U where "p = (h, U)" using prod.exhaust by blast
    ultimately have "(h, U) \<in> set ps" and d: "d = poly_deg h" by simp_all
    from this(1) le0 show "d < \<b> ps 0" unfolding d by (rule \<b>)
  qed
  ultimately have "Max (poly_deg ` fst ` set ps) < \<b> ps 0" by simp
  thus ?thesis by simp
qed

corollary \<b>_zero_gr:
  assumes "(h, U) \<in> set ps"
  shows "poly_deg h < \<b> ps 0"
proof -
  have "poly_deg h \<le> Max (poly_deg ` fst ` set ps)"
  proof (rule Max_ge)
    from finite_set show "finite (poly_deg ` fst ` set ps)" by (intro finite_imageI)
  next
    from assms have "poly_deg (fst (h, U)) \<in> poly_deg ` fst ` set ps" by (intro imageI)
    thus "poly_deg h \<in> poly_deg ` fst ` set ps" by simp
  qed
  also have "\<dots> < Suc \<dots>" by simp
  also have "\<dots> \<le> \<b> ps 0"
  proof (rule \<b>_zero)
    from assms show "ps \<noteq> []" by auto
  qed
  finally show ?thesis .
qed

lemma \<b>_one:
  assumes "valid_decomp X ps" and "standard_decomp k ps"
  shows "\<b> ps (Suc 0) = (if ps\<^sub>+ = [] then 0 else Suc (Max (poly_deg ` fst ` set (ps\<^sub>+))))"
proof (cases "ps\<^sub>+ = []")
  case True
  hence "\<b> ps (Suc 0) = 0" using le_refl by (rule \<b>_Nil)
  with True show ?thesis by simp
next
  case False
  with assms have aP: "\<a> ps = Min (poly_deg ` fst ` set (ps\<^sub>+))" (is "_ = Min ?A") by (rule \<a>_nonempty)
  from pos_decomp_subset finite_set have "finite (set (ps\<^sub>+))" by (rule finite_subset)
  hence "finite ?A" by (intro finite_imageI)
  from False have "?A \<noteq> {}" by simp
  have "\<b> ps (Suc 0) = Suc (Max ?A)" unfolding \<b>_def
  proof (rule Least_equality)
    from \<open>finite ?A\<close> \<open>?A \<noteq> {}\<close> have "\<a> ps \<in> ?A" unfolding aP by (rule Min_in)
    with \<open>finite ?A\<close> have "\<a> ps \<le> Max ?A" by (rule Max_ge)
    hence "\<a> ps \<le> Suc (Max ?A)" by simp
    moreover {
      fix h U
      assume "(h, U) \<in> set ps"
      with fin_X assms(1) have "finite U" by (rule valid_decompD_finite)
      moreover assume "Suc 0 \<le> card U"
      ultimately have "U \<noteq> {}" by auto
      with \<open>(h, U) \<in> set ps\<close> have "(h, U) \<in> set (ps\<^sub>+)" by (simp add: pos_decomp_def)
      hence "poly_deg (fst (h, U)) \<in> ?A" by (intro imageI)
      hence "poly_deg h \<in> ?A" by (simp only: fst_conv)
      with \<open>finite ?A\<close> have "poly_deg h \<le> Max ?A" by (rule Max_ge)
      hence "poly_deg h < Suc (Max ?A)" by simp
    }
    ultimately show "\<a> ps \<le> Suc (Max ?A) \<and> (\<forall>(h, U)\<in>set ps. Suc 0 \<le> card U \<longrightarrow> poly_deg h < Suc (Max ?A))"
      by blast
  next
    fix d
    assume "\<a> ps \<le> d \<and> (\<forall>(h, U)\<in>set ps. Suc 0 \<le> card U \<longrightarrow> poly_deg h < d)"
    hence rl: "poly_deg h < d" if "(h, U) \<in> set ps" and "0 < card U" for h U using that by auto
    have "Max ?A < d" unfolding Max_less_iff[OF \<open>finite ?A\<close> \<open>?A \<noteq> {}\<close>]
    proof
      fix d0
      assume "d0 \<in> poly_deg ` fst ` set (ps\<^sub>+)"
      then obtain h U where "(h, U) \<in> set (ps\<^sub>+)" and d0: "d0 = poly_deg h" by auto
      from this(1) have "(h, U) \<in> set ps" and "U \<noteq> {}" by (simp_all add: pos_decomp_def)
      from fin_X assms(1) this(1) have "finite U" by (rule valid_decompD_finite)
      with \<open>U \<noteq> {}\<close> have "0 < card U" by (simp add: card_gt_0_iff)
      with \<open>(h, U) \<in> set ps\<close> show "d0 < d" unfolding d0 by (rule rl)
    qed
    thus "Suc (Max ?A) \<le> d" by simp
  qed
  with False show ?thesis by simp
qed

corollary \<b>_one_gr:
  assumes "valid_decomp X ps" and "standard_decomp k ps" and "(h, U) \<in> set (ps\<^sub>+)"
  shows "poly_deg h < \<b> ps (Suc 0)"
proof -
  from assms(3) have "ps\<^sub>+ \<noteq> []" by auto
  with assms(1, 2) have eq: "\<b> ps (Suc 0) = Suc (Max (poly_deg ` fst ` set (ps\<^sub>+)))"
    by (simp add: \<b>_one)
  have "poly_deg h \<le> Max (poly_deg ` fst ` set (ps\<^sub>+))"
  proof (rule Max_ge)
    from finite_set show "finite (poly_deg ` fst ` set (ps\<^sub>+))" by (intro finite_imageI)
  next
    from assms(3) have "poly_deg (fst (h, U)) \<in> poly_deg ` fst ` set (ps\<^sub>+)" by (intro imageI)
    thus "poly_deg h \<in> poly_deg ` fst ` set (ps\<^sub>+)" by simp
  qed
  also have "\<dots> < \<b> ps (Suc 0)" by (simp add: eq)
  finally show ?thesis .
qed

lemma \<b>_card_X:
  assumes "exact_decomp m ps" and "Suc (card X) \<le> i"
  shows "\<b> ps i = \<a> ps"
  unfolding \<b>_def
proof (rule Least_equality)
  {
    fix h U
    assume "(h, U) \<in> set ps"
    with assms(1) have "U \<subseteq> X" by (rule exact_decompD)
    note assms(2)
    also assume "i \<le> card U"
    finally have "card X < card U" by simp
    with fin_X have "\<not> U \<subseteq> X" by (auto dest: card_mono leD)
    hence False using \<open>U \<subseteq> X\<close> ..
  }
  thus "\<a> ps \<le> \<a> ps \<and> (\<forall>(h, U)\<in>set ps. i \<le> card U \<longrightarrow> poly_deg h < \<a> ps)" by blast
qed simp

lemma lem_6_1_1:
  assumes "standard_decomp k ps" and "exact_decomp m ps" and "Suc 0 \<le> i"
    and "i \<le> card X" and "\<b> ps (Suc i) \<le> d" and "d < \<b> ps i"
  obtains h U where "(h, U) \<in> set (ps\<^sub>+)" and "poly_deg h = d" and "card U = i"
proof -
  have "ps\<^sub>+ \<noteq> []"
  proof
    assume "ps\<^sub>+ = []"
    hence "\<b> ps i = 0" using assms(3) by (rule \<b>_Nil)
    with assms(6) show False by simp
  qed
  have eq1: "\<b> ps (Suc (card X)) = \<a> ps" using assms(2) le_refl by (rule \<b>_card_X)
  from assms(1) have std: "standard_decomp (\<b> ps (Suc (card X))) ps" unfolding eq1 by (rule \<a>)
  from assms(4) have "Suc i \<le> Suc (card X)" ..
  hence "\<b> ps (Suc (card X)) \<le> \<b> ps (Suc i)" by (rule \<b>_decreasing)
  hence "\<a> ps \<le> \<b> ps (Suc i)" by (simp only: eq1)
  have "\<exists>h U. (h, U) \<in> set ps \<and> i \<le> card U \<and> \<b> ps i \<le> Suc (poly_deg h)"
  proof (rule ccontr)
    assume *: "\<nexists>h U. (h, U) \<in> set ps \<and> i \<le> card U \<and> \<b> ps i \<le> Suc (poly_deg h)"
    note \<open>\<a> ps \<le> \<b> ps (Suc i)\<close>
    also from assms(5, 6) have "\<b> ps (Suc i) < \<b> ps i" by (rule le_less_trans)
    finally have "\<a> ps < \<b> ps i" .
    hence "\<a> ps \<le> \<b> ps i - 1" by simp
    hence "\<b> ps i \<le> \<b> ps i - 1"
    proof (rule \<b>_le)
      fix h U
      assume "(h, U) \<in> set ps" and "i \<le> card U"
      show "poly_deg h < \<b> ps i - 1"
      proof (rule ccontr)
        assume "\<not> poly_deg h < \<b> ps i - 1"
        hence "\<b> ps i \<le> Suc (poly_deg h)" by simp
        with * \<open>(h, U) \<in> set ps\<close> \<open>i \<le> card U\<close> show False by auto
      qed
    qed
    thus False using \<open>\<a> ps < \<b> ps i\<close> by linarith
  qed
  then obtain h U where "(h, U) \<in> set ps" and "i \<le> card U" and "\<b> ps i \<le> Suc (poly_deg h)" by blast
  from assms(3) this(2) have "U \<noteq> {}" by auto
  with \<open>(h, U) \<in> set ps\<close> have "(h, U) \<in> set (ps\<^sub>+)" by (simp add: pos_decomp_def)
  note std this
  moreover have "\<b> ps (Suc (card X)) \<le> d" unfolding eq1 using \<open>\<a> ps \<le> \<b> ps (Suc i)\<close> assms(5)
    by (rule le_trans)
  moreover have "d \<le> poly_deg h"
  proof -
    from assms(6) \<open>\<b> ps i \<le> Suc (poly_deg h)\<close> have "d < Suc (poly_deg h)" by (rule less_le_trans)
    thus ?thesis by simp
  qed
  ultimately obtain h' U' where "(h', U') \<in> set ps" and d: "poly_deg h' = d" and "card U \<le> card U'"
    by (rule standard_decompE)
  from \<open>i \<le> card U\<close> this(3) have "i \<le> card U'" by (rule le_trans)
  with assms(3) have "U' \<noteq> {}" by auto
  with \<open>(h', U') \<in> set ps\<close> have "(h', U') \<in> set (ps\<^sub>+)" by (simp add: pos_decomp_def)
  moreover note \<open>poly_deg h' = d\<close>
  moreover have "card U' = i"
  proof (rule ccontr)
    assume "card U' \<noteq> i"
    with \<open>i \<le> card U'\<close> have "Suc i \<le> card U'" by simp
    with \<open>(h', U') \<in> set ps\<close> have "poly_deg h' < \<b> ps (Suc i)" by (rule \<b>)
    with assms(5) show False by (simp add: d)
  qed
  ultimately show ?thesis ..
qed

corollary lem_6_1_2:
  assumes "standard_decomp k ps" and "exact_decomp 0 ps" and "Suc 0 \<le> i"
    and "i \<le> card X" and "\<b> ps (Suc i) \<le> d" and "d < \<b> ps i"
  obtains h U where "{(h', U') \<in> set (ps\<^sub>+). poly_deg h' = d} = {(h, U)}" and "card U = i"
proof -
  from assms obtain h U where "(h, U) \<in> set (ps\<^sub>+)" and "poly_deg h = d" and "card U = i"
    by (rule lem_6_1_1)
  hence "{(h, U)} \<subseteq> {(h', U') \<in> set (ps\<^sub>+). poly_deg h' = d}" (is "_ \<subseteq> ?A") by simp
  moreover have "?A \<subseteq> {(h, U)}"
  proof
    fix x
    assume "x \<in> ?A"
    then obtain h' U' where "(h', U') \<in> set (ps\<^sub>+)" and "poly_deg h' = d" and x: "x = (h', U')"
      by blast
    note assms(2) \<open>(h, U) \<in> set (ps\<^sub>+)\<close> this(1)
    moreover have "poly_deg h = poly_deg h'" by (simp only: \<open>poly_deg h = d\<close> \<open>poly_deg h' = d\<close>)
    ultimately have "(h, U) = (h', U')" by (rule exact_decompD_zero)
    thus "x \<in> {(h, U)}" by (simp add: x)
  qed
  ultimately have "{(h, U)} = ?A" ..
  hence "?A = {(h, U)}" by (rule sym)
  thus ?thesis using \<open>card U = i\<close> ..
qed

corollary lem_6_1_2':
  assumes "standard_decomp k ps" and "exact_decomp 0 ps" and "Suc 0 \<le> i"
    and "i \<le> card X" and "\<b> ps (Suc i) \<le> d" and "d < \<b> ps i"
  shows "card {(h', U') \<in> set (ps\<^sub>+). poly_deg h' = d} = 1" (is "card ?A = _")
    and "{(h', U') \<in> set (ps\<^sub>+). poly_deg h' = d \<and> card U' = i} = {(h', U') \<in> set (ps\<^sub>+). poly_deg h' = d}"
            (is "?B = _")
    and "card {(h', U') \<in> set (ps\<^sub>+). poly_deg h' = d \<and> card U' = i} = 1"
proof -
  from assms obtain h U where "?A = {(h, U)}" and "card U = i" by (rule lem_6_1_2)
  from this(1) show "card ?A = 1" by simp
  moreover show "?B = ?A"
  proof
    have "(h, U) \<in> ?A" by (simp add: \<open>?A = {(h, U)}\<close>)
    have "?A = {(h, U)}" by fact
    also from \<open>(h, U) \<in> ?A\<close> \<open>card U = i\<close> have "\<dots> \<subseteq> ?B" by simp
    finally show "?A \<subseteq> ?B" .
  qed blast
  ultimately show "card ?B = 1" by simp 
qed

corollary lem_6_1_3:
  assumes "standard_decomp k ps" and "exact_decomp 0 ps" and "Suc 0 \<le> i"
    and "i \<le> card X" and "(h, U) \<in> set (ps\<^sub>+)" and "card U = i"
  shows "\<b> ps (Suc i) \<le> poly_deg h"
proof (rule ccontr)
  define j where "j = (LEAST j'. \<b> ps j' \<le> poly_deg h)"
  assume "\<not> \<b> ps (Suc i) \<le> poly_deg h"
  hence "poly_deg h < \<b> ps (Suc i)" by simp
  from assms(2) le_refl have "\<b> ps (Suc (card X)) = \<a> ps" by (rule \<b>_card_X)
  also from _ assms(5) have "\<dots> \<le> poly_deg h"
  proof (rule standard_decompD)
    from assms(1) show "standard_decomp (\<a> ps) ps" by (rule \<a>)
  qed
  finally have "\<b> ps (Suc (card X)) \<le> poly_deg h" .
  hence 1: "\<b> ps j \<le> poly_deg h" unfolding j_def by (rule LeastI)
  have "Suc i < j"
  proof (rule ccontr)
    assume "\<not> Suc i < j"
    hence "j \<le> Suc i" by simp
    hence "\<b> ps (Suc i) \<le> \<b> ps j" by (rule \<b>_decreasing)
    also have "\<dots> \<le> poly_deg h" by fact
    finally show False using \<open>poly_deg h < \<b> ps (Suc i)\<close> by simp
  qed
  hence eq: "Suc (j - 1) = j" by simp
  note assms(1, 2)
  moreover from assms(3) have "Suc 0 \<le> j - 1"
  proof (rule le_trans)
    from \<open>Suc i < j\<close> show "i \<le> j - 1" by simp
  qed
  moreover have "j - 1 \<le> card X"
  proof -
    have "j \<le> Suc (card X)" unfolding j_def by (rule Least_le) fact
    thus ?thesis by simp
  qed
  moreover from 1 have "\<b> ps (Suc (j - 1)) \<le> poly_deg h" by (simp only: eq)
  moreover have "poly_deg h < \<b> ps (j - 1)"
  proof (rule ccontr)
    assume "\<not> poly_deg h < \<b> ps (j - 1)"
    hence "\<b> ps (j - 1) \<le> poly_deg h" by simp
    hence "j \<le> j - 1" unfolding j_def by (rule Least_le)
    also have "\<dots> < Suc (j - 1)" by simp
    finally show False by (simp only: eq)
  qed
  ultimately obtain h0 U0
    where eq1: "{(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> poly_deg h' = poly_deg h} = {(h0, U0)}"
    and "card U0 = j - 1" by (rule lem_6_1_2)
  from assms(5) have "(h, U) \<in> {(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> poly_deg h' = poly_deg h}" by simp
  hence "(h, U) \<in> {(h0, U0)}" by (simp only: eq1)
  hence "U = U0" by simp
  hence "card U = j - 1" by (simp only: \<open>card U0 = j - 1\<close>)
  hence "i = j - 1" by (simp only: assms(6))
  hence "Suc i = j" by (simp only: eq)
  with \<open>Suc i < j\<close> show False by simp
qed

qualified fun shift_list :: "((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::{comm_ring_1,ring_no_zero_divisors}) \<times> 'x set) \<Rightarrow>
                              'x \<Rightarrow> _ list \<Rightarrow> _ list" where
  "shift_list (h, U) x ps =
        ((punit.monom_mult 1 (Poly_Mapping.single x 1) h, U) # (h, U - {x}) # removeAll (h, U) ps)"

declare shift_list.simps[simp del]

lemma monomial_decomp_shift_list:
  assumes "monomial_decomp ps" and "hU \<in> set ps"
  shows "monomial_decomp (shift_list hU x ps)"
proof -
  let ?x = "Poly_Mapping.single x (1::nat)"
  obtain h U where hU: "hU = (h, U)" using prod.exhaust by blast
  with assms(2) have "(h, U) \<in> set ps" by simp
  with assms(1) have 1: "is_monomial h" and 2: "lcf h = 1" by (rule monomial_decompD)+
  from this(1) have "monomial (lcf h) (lpp h) = h" by (rule punit.monomial_eq_itself)
  moreover define t where "t = lpp h"
  ultimately have "h = monomial 1 t" by (simp only: 2)
  hence "is_monomial (punit.monom_mult 1 ?x h)" and "lcf (punit.monom_mult 1 ?x h) = 1"
    by (simp_all add: punit.monom_mult_monomial monomial_is_monomial)
  with assms(1) 1 2 show ?thesis by (simp add: shift_list.simps monomial_decomp_def hU)
qed

lemma hom_decomp_shift_list:
  assumes "hom_decomp ps" and "hU \<in> set ps"
  shows "hom_decomp (shift_list hU x ps)"
proof -
  let ?x = "Poly_Mapping.single x (1::nat)"
  obtain h U where hU: "hU = (h, U)" using prod.exhaust by blast
  with assms(2) have "(h, U) \<in> set ps" by simp
  with assms(1) have 1: "homogeneous h" by (rule hom_decompD)
  hence "homogeneous (punit.monom_mult 1 ?x h)" by (simp only: homogeneous_monom_mult)
  with assms(1) 1 show ?thesis by (simp add: shift_list.simps hom_decomp_def hU)
qed

lemma valid_decomp_shift_list:
  assumes "valid_decomp X ps" and "(h, U) \<in> set ps" and "x \<in> U"
  shows "valid_decomp X (shift_list (h, U) x ps)"
proof -
  let ?x = "Poly_Mapping.single x (1::nat)"
  from assms(1, 2) have "h \<in> P[X]" and "h \<noteq> 0" and "U \<subseteq> X" by (rule valid_decompD)+
  moreover from this(1) have "punit.monom_mult 1 ?x h \<in> P[X]"
  proof (intro Polys_closed_monom_mult PPs_closed_single)
    from \<open>x \<in> U\<close> \<open>U \<subseteq> X\<close> show "x \<in> X" ..
  qed
  moreover from \<open>U \<subseteq> X\<close> have "U - {x} \<subseteq> X" by blast
  ultimately show ?thesis
    using assms(1) \<open>h \<noteq> 0\<close> by (simp add: valid_decomp_def punit.monom_mult_eq_zero_iff shift_list.simps)
qed

lemma standard_decomp_shift_list:
  assumes "standard_decomp k ps" and "(h1, U1) \<in> set ps" and "(h2, U2) \<in> set ps"
    and "poly_deg h1 = poly_deg h2" and "card U2 \<le> card U1" and "(h1, U1) \<noteq> (h2, U2)" and "x \<in> U2"
  shows "standard_decomp k (shift_list (h2, U2) x ps)"
proof (rule standard_decompI)
  let ?p1 = "(punit.monom_mult 1 (Poly_Mapping.single x 1) h2, U2)"
  let ?p2 = "(h2, U2 - {x})"
  let ?qs = "removeAll (h2, U2) ps"
  fix h U
  assume "(h, U) \<in> set ((shift_list (h2, U2) x ps)\<^sub>+)"
  hence disj: "(h, U) = ?p1 \<or> ((h, U) = ?p2 \<and> U2 - {x} \<noteq> {}) \<or> (h, U) \<in> set (ps\<^sub>+)"
    by (auto simp: pos_decomp_def shift_list.simps split: if_split_asm)
  from assms(7) have "U2 \<noteq> {}" by blast
  with assms(3) have "(h2, U2) \<in> set (ps\<^sub>+)" by (simp add: pos_decomp_def)
  with assms(1) have k_le: "k \<le> poly_deg h2" by (rule standard_decompD)

  let ?x = "Poly_Mapping.single x 1"
  from disj show "k \<le> poly_deg h"
  proof (elim disjE)
    assume "(h, U) = ?p1"
    hence h: "h = punit.monom_mult (1::'a) ?x h2" by simp
    note k_le
    also have "poly_deg h2 \<le> poly_deg h" by (cases "h2 = 0") (simp_all add: h poly_deg_monom_mult)
    finally show ?thesis .
  next
    assume "(h, U) = ?p2 \<and> U2 - {x} \<noteq> {}"
    with k_le show ?thesis by simp
  next
    assume "(h, U) \<in> set (ps\<^sub>+)"
    with assms(1) show ?thesis by (rule standard_decompD)
  qed

  fix d
  assume "k \<le> d" and "d \<le> poly_deg h"
  from disj obtain h' U' where 1: "(h', U') \<in> set (?p1 # ps)" and "poly_deg h' = d"
    and "card U \<le> card U'"
  proof (elim disjE)
    assume "(h, U) = ?p1"
    hence h: "h = punit.monom_mult 1 ?x h2" and "U = U2" by simp_all
    from \<open>d \<le> poly_deg h\<close> have "d \<le> poly_deg h2 \<or> poly_deg h = d"
      by (cases "h2 = 0") (auto simp: h poly_deg_monom_mult deg_pm_single)
    thus ?thesis
    proof
      assume "d \<le> poly_deg h2"
      with assms(1) \<open>(h2, U2) \<in> set (ps\<^sub>+)\<close> \<open>k \<le> d\<close> obtain h' U'
        where "(h', U') \<in> set ps" and "poly_deg h' = d" and "card U2 \<le> card U'"
        by (rule standard_decompE)
      from this(1) have "(h', U') \<in> set (?p1 # ps)" by simp
      moreover note \<open>poly_deg h' = d\<close>
      moreover from \<open>card U2 \<le> card U'\<close> have "card U \<le> card U'" by (simp only: \<open>U = U2\<close>)
      ultimately show ?thesis ..
    next
      have "(h, U) \<in> set (?p1 # ps)" by (simp add: \<open>(h, U) = ?p1\<close>)
      moreover assume "poly_deg h = d"
      ultimately show ?thesis using le_refl ..
    qed
  next
    assume "(h, U) = ?p2 \<and> U2 - {x} \<noteq> {}"
    hence "h = h2" and U: "U = U2 - {x}" by simp_all
    from \<open>d \<le> poly_deg h\<close> this(1) have "d \<le> poly_deg h2" by simp
    with assms(1) \<open>(h2, U2) \<in> set (ps\<^sub>+)\<close> \<open>k \<le> d\<close> obtain h' U'
      where "(h', U') \<in> set ps" and "poly_deg h' = d" and "card U2 \<le> card U'"
      by (rule standard_decompE)
    from this(1) have "(h', U') \<in> set (?p1 # ps)" by simp
    moreover note \<open>poly_deg h' = d\<close>
    moreover from _ \<open>card U2 \<le> card U'\<close> have "card U \<le> card U'" unfolding U
      by (rule le_trans) (metis Diff_empty card_Diff1_le card_infinite finite_Diff_insert order_refl)
    ultimately show ?thesis ..
  next
    assume "(h, U) \<in> set (ps\<^sub>+)"
    from assms(1) this \<open>k \<le> d\<close> \<open>d \<le> poly_deg h\<close> obtain h' U'
      where "(h', U') \<in> set ps" and "poly_deg h' = d" and "card U \<le> card U'"
      by (rule standard_decompE)
    from this(1) have "(h', U') \<in> set (?p1 # ps)" by simp
    thus ?thesis using \<open>poly_deg h' = d\<close> \<open>card U \<le> card U'\<close> ..
  qed
  show "\<exists>h' U'. (h', U') \<in> set (shift_list (h2, U2) x ps) \<and> poly_deg h' = d \<and> card U \<le> card U'"
  proof (cases "(h', U') = (h2, U2)")
    case True
    hence "h' = h2" and "U' = U2" by simp_all
    from assms(2, 6) have "(h1, U1) \<in> set (shift_list (h2, U2) x ps)" by (simp add: shift_list.simps)
    moreover from \<open>poly_deg h' = d\<close> have "poly_deg h1 = d" by (simp only: \<open>h' = h2\<close> assms(4))
    moreover from \<open>card U \<le> card U'\<close> assms(5) have "card U \<le> card U1" by (simp add: \<open>U' = U2\<close>)
    ultimately show ?thesis by blast
  next
    case False
    with 1 have "(h', U') \<in> set (shift_list (h2, U2) x ps)" by (auto simp: shift_list.simps)
    thus ?thesis using \<open>poly_deg h' = d\<close> \<open>card U \<le> card U'\<close> by blast
  qed
qed

lemma cone_decomp_shift_list:
  assumes "valid_decomp X ps" and "cone_decomp T ps" and "(h, U) \<in> set ps" and "x \<in> U"
  shows "cone_decomp T (shift_list (h, U) x ps)"
proof -
  let ?p1 = "(punit.monom_mult 1 (Poly_Mapping.single x 1) h, U)"
  let ?p2 = "(h, U - {x})"
  let ?qs = "removeAll (h, U) ps"
  from assms(3) obtain ps1 ps2 where ps: "ps = ps1 @ (h, U) # ps2" and *: "(h, U) \<notin> set ps1"
    by (meson split_list_first)
  have "count_list ps2 (h, U) = 0"
  proof (rule ccontr)
    from assms(1, 3) have "h \<noteq> 0" by (rule valid_decompD)
    assume "count_list ps2 (h, U) \<noteq> 0"
    hence "1 < count_list ps (h, U)" by (simp add: ps count_list_append)
    also have "\<dots> \<le> count_list (map cone ps) (cone (h, U))" by (fact count_list_map_ge)
    finally have "1 < count_list (map cone ps) (cone (h, U))" .
    with cone_decompD have "cone (h, U) = {0}"
    proof (rule direct_decomp_repeated_eq_zero)
      fix s
      assume "s \<in> set (map cone ps)"
      thus "0 \<in> s" by (auto intro: zero_in_cone)
    qed (fact assms(2))
    with tip_in_cone[of h U] have "h = 0" by simp
    with \<open>h \<noteq> 0\<close> show False ..
  qed
  hence **: "(h, U) \<notin> set ps2" by (simp add: count_list_eq_0_iff)
  have "perm ps ((h, U) # ps1 @ ps2)" (is "perm _ ?ps")
    by (rule perm_sym) (simp only: perm_append_Cons ps)
  with assms(2) have "cone_decomp T ?ps" by (rule cone_decomp_perm)
  hence "direct_decomp T (map cone ?ps)" by (rule cone_decompD)
  hence "direct_decomp T (cone (h, U) # map cone (ps1 @ ps2))" by simp
  hence "direct_decomp T ((map cone (ps1 @ ps2)) @ [cone ?p1, cone ?p2])"
  proof (rule direct_decomp_direct_decomp)
    let ?x = "Poly_Mapping.single x (Suc 0)"
    have "direct_decomp (cone (h, insert x (U - {x})))
              [cone (h, U - {x}), cone (monomial (1::'a) ?x * h, insert x (U - {x}))]"
      by (rule direct_decomp_cone_insert) simp
    with assms(4) show "direct_decomp (cone (h, U)) [cone ?p1, cone ?p2]"
      by (simp add: insert_absorb times_monomial_left direct_decomp_perm perm.swap)
  qed
  hence "direct_decomp T (map cone (ps1 @ ps2 @ [?p1, ?p2]))" by simp
  hence "cone_decomp T (ps1 @ ps2 @ [?p1, ?p2])" by (rule cone_decompI)
  moreover have "perm (ps1 @ ps2 @ [?p1, ?p2]) (?p1 # ?p2 # (ps1 @ ps2))"
  proof -
    have "ps1 @ ps2 @ [?p1, ?p2] = (ps1 @ ps2) @ [?p1, ?p2]" by simp
    also have "perm \<dots> ([?p1, ?p2] @ (ps1 @ ps2))" by (rule perm_append_swap)
    also have "\<dots> = ?p1 # ?p2 # (ps1 @ ps2)" by simp
    finally show ?thesis .
  qed
  ultimately have "cone_decomp T (?p1 # ?p2 # (ps1 @ ps2))" by (rule cone_decomp_perm)
  also from * ** have "ps1 @ ps2 = removeAll (h, U) ps" by (simp add: remove1_append ps)
  finally show ?thesis by (simp only: shift_list.simps)
qed

subsection \<open>Functions \<open>shift\<close> and \<open>exact\<close>\<close>

context
  fixes k m :: nat
begin

context
  fixes d :: nat
begin

definition shift2_inv :: "((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) \<times> 'x set) list \<Rightarrow> bool" where
  "shift2_inv qs \<longleftrightarrow> valid_decomp X qs \<and> standard_decomp k qs \<and> exact_decomp (Suc m) qs \<and>
                         (\<forall>d0<d. card {q \<in> set qs. poly_deg (fst q) = d0 \<and> m < card (snd q)} \<le> 1)"

fun shift1_inv :: "(((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) list \<times> ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) \<times> 'x set) set) \<Rightarrow> bool"
  where "shift1_inv (qs, B) \<longleftrightarrow> B = {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)} \<and> shift2_inv qs"

lemma shift2_invI:
  "valid_decomp X qs \<Longrightarrow> standard_decomp k qs \<Longrightarrow> exact_decomp (Suc m) qs \<Longrightarrow>
    (\<And>d0. d0 < d \<Longrightarrow> card {q \<in> set qs. poly_deg (fst q) = d0 \<and> m < card (snd q)} \<le> 1) \<Longrightarrow>
    shift2_inv qs"
  by (simp add: shift2_inv_def)

lemma shift2_invD:
  assumes "shift2_inv qs"
  shows "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp (Suc m) qs"
    and "d0 < d \<Longrightarrow> card {q \<in> set qs. poly_deg (fst q) = d0 \<and> m < card (snd q)} \<le> 1"
  using assms by (simp_all add: shift2_inv_def)

lemma shift1_invI:
  "B = {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)} \<Longrightarrow> shift2_inv qs \<Longrightarrow> shift1_inv (qs, B)"
  by simp

lemma shift1_invD:
  assumes "shift1_inv (qs, B)"
  shows "B = {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)}" and "shift2_inv qs"
  using assms by simp_all

declare shift1_inv.simps[simp del]

lemma shift1_inv_finite_snd:
  assumes "shift1_inv (qs, B)"
  shows "finite B"
proof (rule finite_subset)
  from assms have "B = {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)}" by (rule shift1_invD)
  also have "\<dots> \<subseteq> set qs" by blast
  finally show "B \<subseteq> set qs" .
qed (fact finite_set)

lemma shift1_inv_some_snd:
  assumes "shift1_inv (qs, B)" and "1 < card B" and "(h, U) = (SOME b. b \<in> B \<and> card (snd b) = Suc m)"
  shows "(h, U) \<in> B" and "(h, U) \<in> set qs" and "poly_deg h = d" and "card U = Suc m"
proof -
  define A where "A = {q \<in> B. card (snd q) = Suc m}"
  define Y where "Y = {q \<in> set qs. poly_deg (fst q) = d \<and> Suc m < card (snd q)}"
  from assms(1) have B: "B = {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)}"
    and inv2: "shift2_inv qs" by (rule shift1_invD)+
  have B': "B = A \<union> Y" by (auto simp: B A_def Y_def)
  have "finite A"
  proof (rule finite_subset)
    show "A \<subseteq> B" unfolding A_def by blast
  next
    from assms(1) show "finite B" by (rule shift1_inv_finite_snd)
  qed
  moreover have "finite Y"
  proof (rule finite_subset)
    show "Y \<subseteq> set qs" unfolding Y_def by blast
  qed (fact finite_set)
  moreover have "A \<inter> Y = {}" by (auto simp: A_def Y_def)
  ultimately have "card (A \<union> Y) = card A + card Y" by (rule card_Un_disjoint)
  with assms(2) have "1 < card A + card Y" by (simp only: B')
  thm card_le_Suc0_iff_eq[OF \<open>finite Y\<close>]
  moreover have "card Y \<le> 1" unfolding One_nat_def card_le_Suc0_iff_eq[OF \<open>finite Y\<close>]
  proof (intro ballI)
    fix q1 q2 :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set"
    obtain h1 U1 where q1: "q1 = (h1, U1)" using prod.exhaust by blast
    obtain h2 U2 where q2: "q2 = (h2, U2)" using prod.exhaust by blast
    assume "q1 \<in> Y"
    hence "(h1, U1) \<in> set qs" and "poly_deg h1 = d" and "Suc m < card U1" by (simp_all add: q1 Y_def)
    assume "q2 \<in> Y"
    hence "(h2, U2) \<in> set qs" and "poly_deg h2 = d" and "Suc m < card U2" by (simp_all add: q2 Y_def)
    from this(2) have "poly_deg h1 = poly_deg h2" by (simp only: \<open>poly_deg h1 = d\<close>)
    from inv2 have "exact_decomp (Suc m) qs" by (rule shift2_invD)
    thus "q1 = q2" unfolding q1 q2 by (rule exact_decompD) fact+
  qed
  ultimately have "0 < card A" by simp
  hence "A \<noteq> {}" by auto
  then obtain a where "a \<in> A" by blast
  have "(h, U) \<in> B \<and> card (snd (h, U)) = Suc m" unfolding assms(3)
  proof (rule someI)
    from \<open>a \<in> A\<close> show "a \<in> B \<and> card (snd a) = Suc m" by (simp add: A_def)
  qed
  thus "(h, U) \<in> B" and "card U = Suc m" by simp_all
  from this(1) show "(h, U) \<in> set qs" and "poly_deg h = d" by (simp_all add: B)
qed

lemma shift1_inv_preserved:
  assumes "shift1_inv (qs, B)" and "1 < card B" and "(h, U) = (SOME b. b \<in> B \<and> card (snd b) = Suc m)"
    and "x = (SOME y. y \<in> U)"
  shows "shift1_inv (shift_list (h, U) x qs, B - {(h, U)})"
proof -
  let ?p1 = "(punit.monom_mult 1 (Poly_Mapping.single x 1) h, U)"
  let ?p2 = "(h, U - {x})"
  let ?qs = "removeAll (h, U) qs"
  let ?B = "B - {(h, U)}"
  from assms(1, 2, 3) have "(h, U) \<in> B" and "(h, U) \<in> set qs" and deg_h: "poly_deg h = d"
    and card_U: "card U = Suc m" by (rule shift1_inv_some_snd)+
  from card_U have "U \<noteq> {}" by auto
  then obtain y where "y \<in> U" by blast
  hence "x \<in> U" unfolding assms(4) by (rule someI)
  with card_U have card_Ux: "card (U - {x}) = m"
    by (metis card_Diff_singleton card_infinite diff_Suc_1 nat.simps(3))
  from assms(1) have B: "B = {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)}"
    and inv2: "shift2_inv qs" by (rule shift1_invD)+
  from inv2 have valid_qs: "valid_decomp X qs" by (rule shift2_invD)
  hence "h \<noteq> 0" using \<open>(h, U) \<in> set qs\<close> by (rule valid_decompD)
  show ?thesis
  proof (intro shift1_invI shift2_invI)
    show "?B = {q \<in> set (shift_list (h, U) x qs). poly_deg (fst q) = d \<and> m < card (snd q)}" (is "_ = ?C")
    proof (rule Set.set_eqI)
      fix b
      show "b \<in> ?B \<longleftrightarrow> b \<in> ?C"
      proof
        assume "b \<in> ?C"
        hence "b \<in> insert ?p1 (insert ?p2 (set ?qs))" and b1: "poly_deg (fst b) = d"
          and b2: "m < card (snd b)" by (simp_all add: shift_list.simps)
        from this(1) show "b \<in> ?B"
        proof (elim insertE)
          assume "b = ?p1"
          with \<open>h \<noteq> 0\<close> have "poly_deg (fst b) = Suc d"
            by (simp add: poly_deg_monom_mult deg_pm_single deg_h)
          thus ?thesis by (simp add: b1)
        next
          assume "b = ?p2"
          hence "card (snd b) = m" by (simp add: card_Ux)
          with b2 show ?thesis by simp
        next
          assume "b \<in> set ?qs"
          with b1 b2 show ?thesis by (auto simp: B)
        qed
      qed (auto simp: B shift_list.simps)
    qed
  next
    from valid_qs \<open>(h, U) \<in> set qs\<close> \<open>x \<in> U\<close> show "valid_decomp X (shift_list (h, U) x qs)"
      by (rule valid_decomp_shift_list)
  next
    from inv2 have std: "standard_decomp k qs" by (rule shift2_invD)
    have "?B \<noteq> {}"
    proof
      assume "?B = {}"
      hence "B \<subseteq> {(h, U)}" by simp
      with _ have "card B \<le> card {(h, U)}" by (rule card_mono) simp
      with assms(2) show False by simp
    qed
    then obtain h' U' where "(h', U') \<in> B" and "(h', U') \<noteq> (h, U)" by auto
    from this(1) have "(h', U') \<in> set qs" and "poly_deg h' = d" and "Suc m \<le> card U'"
      by (simp_all add: B)
    note std this(1) \<open>(h, U) \<in> set qs\<close>
    moreover from \<open>poly_deg h' = d\<close> have "poly_deg h' = poly_deg h" by (simp only: deg_h)
    moreover from \<open>Suc m \<le> card U'\<close> have "card U \<le> card U'" by (simp only: card_U)
    ultimately show "standard_decomp k (shift_list (h, U) x qs)"
      by (rule standard_decomp_shift_list) fact+
  next
    from inv2 have exct: "exact_decomp (Suc m) qs" by (rule shift2_invD)
    show "exact_decomp (Suc m) (shift_list (h, U) x qs)"
    proof (rule exact_decompI)
      fix h' U'
      assume "(h', U') \<in> set (shift_list (h, U) x qs)"
      hence *: "(h', U') \<in> insert ?p1 (insert ?p2 (set ?qs))" by (simp add: shift_list.simps)
      thus "h' \<in> P[X]"
      proof (elim insertE)
        assume "(h', U') = ?p1"
        hence h': "h' = punit.monom_mult 1 (Poly_Mapping.single x 1) h" by simp
        from exct \<open>(h, U) \<in> set qs\<close> have "U \<subseteq> X" by (rule exact_decompD)
        with \<open>x \<in> U\<close> have "x \<in> X" ..
        hence "Poly_Mapping.single x 1 \<in> .[X]" by (rule PPs_closed_single)
        moreover from exct \<open>(h, U) \<in> set qs\<close> have "h \<in> P[X]" by (rule exact_decompD)
        ultimately show ?thesis unfolding h' by (rule Polys_closed_monom_mult)
      next
        assume "(h', U') = ?p2"
        hence "h' = h" by simp
        also from exct \<open>(h, U) \<in> set qs\<close> have "\<dots> \<in> P[X]" by (rule exact_decompD)
        finally show ?thesis .
      next
        assume "(h', U') \<in> set ?qs"
        hence "(h', U') \<in> set qs" by simp
        with exct show ?thesis by (rule exact_decompD)
      qed

      from * show "U' \<subseteq> X"
      proof (elim insertE)
        assume "(h', U') = ?p1"
        hence "U' = U" by simp
        also from exct \<open>(h, U) \<in> set qs\<close> have "\<dots> \<subseteq> X" by (rule exact_decompD)
        finally show ?thesis .
      next
        assume "(h', U') = ?p2"
        hence "U' = U - {x}" by simp
        also have "\<dots> \<subseteq> U" by blast
        also from exct \<open>(h, U) \<in> set qs\<close> have "\<dots> \<subseteq> X" by (rule exact_decompD)
        finally show ?thesis .
      next
        assume "(h', U') \<in> set ?qs"
        hence "(h', U') \<in> set qs" by simp
        with exct show ?thesis by (rule exact_decompD)
      qed
    next
      fix h1 h2 U1 U2
      assume "(h1, U1) \<in> set (shift_list (h, U) x qs)" and "Suc m < card U1"
      hence "(h1, U1) \<in> set qs" using card_U card_Ux by (auto simp: shift_list.simps)
      assume "(h2, U2) \<in> set (shift_list (h, U) x qs)" and "Suc m < card U2"
      hence "(h2, U2) \<in> set qs" using card_U card_Ux by (auto simp: shift_list.simps)
      assume "poly_deg h1 = poly_deg h2"
      from exct show "(h1, U1) = (h2, U2)" by (rule exact_decompD) fact+
    qed
  next
    fix d0
    assume "d0 < d"
    have "finite {q \<in> set qs. poly_deg (fst q) = d0 \<and> m < card (snd q)}" (is "finite ?A")
      by auto
    moreover have "{q \<in> set (shift_list (h, U) x qs). poly_deg (fst q) = d0 \<and> m < card (snd q)} \<subseteq> ?A"
      (is "?C \<subseteq> _")
    proof
      fix q
      assume "q \<in> ?C"
      hence "q = ?p1 \<or> q = ?p2 \<or> q \<in> set ?qs" and 1: "poly_deg (fst q) = d0" and 2: "m < card (snd q)"
        by (simp_all add: shift_list.simps)
      from this(1) show "q \<in> ?A"
      proof (elim disjE)
        assume "q = ?p1"
        with \<open>h \<noteq> 0\<close> have "d \<le> poly_deg (fst q)" by (simp add: poly_deg_monom_mult deg_h)
        with \<open>d0 < d\<close> show ?thesis by (simp only: 1)
      next
        assume "q = ?p2"
        hence "d \<le> poly_deg (fst q)" by (simp add: deg_h)
        with \<open>d0 < d\<close> show ?thesis by (simp only: 1)
      next
        assume "q \<in> set ?qs"
        with 1 2 show ?thesis by simp
      qed
    qed
    ultimately have "card ?C \<le> card ?A" by (rule card_mono)
    also from inv2 \<open>d0 < d\<close> have "\<dots> \<le> 1" by (rule shift2_invD)
    finally show "card ?C \<le> 1" .
  qed
qed

function (domintros) shift1 :: "(((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) list \<times> ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) set) \<Rightarrow>
                                (((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) list \<times>
                                  ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::{comm_ring_1,ring_no_zero_divisors}) \<times> 'x set) set)"
  where
  "shift1 (qs, B) =
      (if 1 < card B then
        let (h, U) = SOME b. b \<in> B \<and> card (snd b) = Suc m; x = SOME y. y \<in> U in
          shift1 (shift_list (h, U) x qs, B - {(h, U)})
      else (qs, B))"
  by auto

lemma shift1_domI:
  assumes "shift1_inv args"
  shows "shift1_dom args"
proof -
  from wf_measure[of "card \<circ> snd"] show ?thesis using assms
  proof (induct)
    case (less args)
    obtain qs B where args: "args = (qs, B)" using prod.exhaust by blast
    have IH: "shift1_dom (qs0, B0)" if "card B0 < card B" and "shift1_inv (qs0, B0)"
      for qs0 and B0::"((_ \<Rightarrow>\<^sub>0 'a) \<times> _) set"
      using _ that(2)
    proof (rule less)
      from that(1) show "((qs0, B0), args) \<in> measure (card \<circ> snd)" by (simp add: args)
    qed
    from less(2) have inv: "shift1_inv (qs, B)" by (simp only: args)
    show ?case unfolding args
    proof (rule shift1.domintros)
      fix h U
      assume hU: "(h, U) = (SOME b. b \<in> B \<and> card (snd b) = Suc m)"
      define x where "x = (SOME y. y \<in> U)"
      assume "Suc 0 < card B"
      hence "1 < card B" by simp
      have "shift1_dom (shift_list (h, U) x qs, B - {(h, U)})"
      proof (rule IH)
        from inv have "finite B" by (rule shift1_inv_finite_snd)
        moreover from inv \<open>1 < card B\<close> hU have "(h, U) \<in> B" by (rule shift1_inv_some_snd)
        ultimately show "card (B - {(h, U)}) < card B" by (rule card_Diff1_less)
      next
        from inv \<open>1 < card B\<close> hU x_def show "shift1_inv (shift_list (h, U) x qs, (B - {(h, U)}))"
          by (rule shift1_inv_preserved)
      qed
      thus "shift1_dom (shift_list (SOME b. b \<in> B \<and> card (snd b) = Suc m) (SOME y. y \<in> U) qs,
                    B - {SOME b. b \<in> B \<and> card (snd b) = Suc m})" by (simp add: hU x_def)
    qed
  qed
qed

lemma shift1_induct [consumes 1, case_names base step]:
  assumes "shift1_inv args"
  assumes "\<And>qs B. shift1_inv (qs, B) \<Longrightarrow> card B \<le> 1 \<Longrightarrow> P (qs, B) (qs, B)"
  assumes "\<And>qs B h U x. shift1_inv (qs, B) \<Longrightarrow> 1 < card B \<Longrightarrow>
            (h, U) = (SOME b. b \<in> B \<and> card (snd b) = Suc m) \<Longrightarrow> x = (SOME y. y \<in> U) \<Longrightarrow>
            finite U \<Longrightarrow> x \<in> U \<Longrightarrow> card (U - {x}) = m \<Longrightarrow>
            P (shift_list (h, U) x qs, B - {(h, U)}) (shift1 (shift_list (h, U) x qs, B - {(h, U)})) \<Longrightarrow>
            P (qs, B) (shift1 (shift_list (h, U) x qs, B - {(h, U)}))"
  shows "P args (shift1 args)"
proof -
  from assms(1) have "shift1_dom args" by (rule shift1_domI)
  thus ?thesis using assms(1)
  proof (induct args rule: shift1.pinduct)
    case step: (1 qs B)
    obtain h U where hU: "(h, U) = (SOME b. b \<in> B \<and> card (snd b) = Suc m)" by (smt prod.exhaust)
    define x where "x = (SOME y. y \<in> U)"
    show ?case
    proof (simp add: shift1.psimps[OF step.hyps(1)] flip: hU x_def del: One_nat_def,
          intro conjI impI)
      let ?args = "(shift_list (h, U) x qs, B - {(h, U)})"
      assume "1 < card B"
      with step.prems have card_U: "card U = Suc m" using hU by (rule shift1_inv_some_snd)
      from card_U have "finite U" using card_infinite by fastforce
      from card_U have "U \<noteq> {}" by auto
      then obtain y where "y \<in> U" by blast
      hence "x \<in> U" unfolding x_def by (rule someI)
      with step.prems \<open>1 < card B\<close> hU x_def \<open>finite U\<close> show "P (qs, B) (shift1 ?args)"
      proof (rule assms(3))
        from \<open>finite U\<close> \<open>x \<in> U\<close> show "card (U - {x}) = m" by (simp add: card_U)
      next
        from \<open>1 < card B\<close> refl hU x_def show "P ?args (shift1 ?args)"
        proof (rule step.hyps)
          from step.prems \<open>1 < card B\<close> hU x_def show "shift1_inv ?args" by (rule shift1_inv_preserved)
        qed
      qed
    next
      assume "\<not> 1 < card B"
      hence "card B \<le> 1" by simp
      with step.prems show "P (qs, B) (qs, B)" by (rule assms(2))
    qed
  qed
qed

lemma shift1_1:
  assumes "shift1_inv args" and "d0 \<le> d"
  shows "card {q \<in> set (fst (shift1 args)). poly_deg (fst q) = d0 \<and> m < card (snd q)} \<le> 1"
  using assms(1)
proof (induct args rule: shift1_induct)
  case (base qs B)
  from assms(2) have "d0 < d \<or> d0 = d" by auto
  thus ?case
  proof
    from base(1) have "shift2_inv qs" by (rule shift1_invD)
    moreover assume "d0 < d"
    ultimately show ?thesis unfolding fst_conv by (rule shift2_invD)
  next
    assume "d0 = d"
    from base(1) have "B = {q \<in> set (fst (qs, B)). poly_deg (fst q) = d0 \<and> m < card (snd q)}"
      unfolding fst_conv \<open>d0 = d\<close> by (rule shift1_invD)
    with base(2) show ?thesis by simp
  qed
qed

lemma shift1_2:
  "shift1_inv args \<Longrightarrow>
    card {q \<in> set (fst (shift1 args)). m < card (snd q)} \<le> card {q \<in> set (fst args). m < card (snd q)}"
proof (induct args rule: shift1_induct)
  case (base qs B)
  show ?case ..
next
  case (step qs B h U x)
  let ?x = "Poly_Mapping.single x (1::nat)"
  let ?p1 = "(punit.monom_mult 1 ?x h, U)"
  let ?A = "{q \<in> set qs. m < card (snd q)}"
  from step(1-3) have card_U: "card U = Suc m" and "(h, U) \<in> set qs" by (rule shift1_inv_some_snd)+
  from step(1) have "shift2_inv qs" by (rule shift1_invD)
  hence "valid_decomp X qs" by (rule shift2_invD)
  hence "h \<noteq> 0" using \<open>(h, U) \<in> set qs\<close> by (rule valid_decompD)
  have fin1: "finite ?A" by auto
  hence fin2: "finite (insert ?p1 ?A)" by simp
  from \<open>(h, U) \<in> set qs\<close> have hU_in: "(h, U) \<in> insert ?p1 ?A" by (simp add: card_U)
  have "?p1 \<noteq> (h, U)"
  proof
    assume "?p1 = (h, U)"
    hence "lpp (punit.monom_mult 1 ?x h) = lpp h" by simp
    with \<open>h \<noteq> 0\<close> show False by (simp add: punit.lt_monom_mult monomial_0_iff)
  qed
  let ?qs = "shift_list (h, U) x qs"
  have "{q \<in> set (fst (?qs, B - {(h, U)})). m < card (snd q)} = (insert ?p1 ?A) - {(h, U)}"
    using step(7) card_U \<open>?p1 \<noteq> (h, U)\<close> by (fastforce simp: shift_list.simps)
  also from fin2 hU_in have "card \<dots> = card (insert ?p1 ?A) - 1" by (simp add: card_Diff_singleton_if)
  also from fin1 have "\<dots> \<le> Suc (card ?A) - 1" by (simp add: card_insert_if)
  also have "\<dots> = card {q \<in> set (fst (qs, B)). m < card (snd q)}" by simp
  finally have "card {q \<in> set (fst (?qs, B - {(h, U)})). m < card (snd q)} \<le>
                  card {q \<in> set (fst (qs, B)). m < card (snd q)}" .
  with step(8) show ?case by (rule le_trans)
qed

lemma shift1_3: "shift1_inv args \<Longrightarrow> cone_decomp T (fst args) \<Longrightarrow> cone_decomp T (fst (shift1 args))"
proof (induct args rule: shift1_induct)
  case (base qs B)
  from base(3) show ?case .
next
  case (step qs B h U x)
  from step.hyps(1) have "shift2_inv qs" by (rule shift1_invD)
  hence "valid_decomp X qs" by (rule shift2_invD)
  moreover from step.prems have "cone_decomp T qs" by (simp only: fst_conv)
  moreover from step.hyps(1-3) have "(h, U) \<in> set qs" by (rule shift1_inv_some_snd)
  ultimately have "cone_decomp T (fst (shift_list (h, U) x qs, B - {(h, U)}))"
    unfolding fst_conv using step.hyps(6) by (rule cone_decomp_shift_list)
  thus ?case by (rule step.hyps(8))
qed

lemma shift1_4:
  "shift1_inv args \<Longrightarrow>
    Max (poly_deg ` fst ` set (fst args)) \<le> Max (poly_deg ` fst ` set (fst (shift1 args)))"
proof (induct args rule: shift1_induct)
  case (base qs B)
  show ?case ..
next
  case (step qs B h U x)
  let ?x = "Poly_Mapping.single x 1"
  let ?p1 = "(punit.monom_mult 1 ?x h, U)"
  let ?qs = "shift_list (h, U) x qs"
  from step(1) have "B = {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)}"
    and inv2: "shift2_inv qs" by (rule shift1_invD)+
  from this(1) have "B \<subseteq> set qs" by auto
  with step(2) have "set qs \<noteq> {}" by auto
  from finite_set have fin: "finite (poly_deg ` fst ` set ?qs)" by (intro finite_imageI)
  have "Max (poly_deg ` fst ` set (fst (qs, B))) \<le> Max (poly_deg ` fst ` set (fst (?qs, B - {(h, U)})))"
    unfolding fst_conv
  proof (rule Max.boundedI)
    from finite_set show "finite (poly_deg ` fst ` set qs)" by (intro finite_imageI)
  next
    from \<open>set qs \<noteq> {}\<close> show "poly_deg ` fst ` set qs \<noteq> {}" by simp
  next
    fix a
    assume "a \<in> poly_deg ` fst ` set qs"
    then obtain q where "q \<in> set qs" and a: "a = poly_deg (fst q)" by blast
    show "a \<le> Max (poly_deg ` fst ` set ?qs)"
    proof (cases "q = (h, U)")
      case True
      hence "a \<le> poly_deg (fst ?p1)" by (cases "h = 0") (simp_all add: a poly_deg_monom_mult)
      also from fin have "\<dots> \<le> Max (poly_deg ` fst ` set ?qs)"
      proof (rule Max_ge)
        have "?p1 \<in> set ?qs" by (simp add: shift_list.simps)
        thus "poly_deg (fst ?p1) \<in> poly_deg ` fst ` set ?qs" by (intro imageI)
      qed
      finally show ?thesis .
    next
      case False
      with \<open>q \<in> set qs\<close> have "q \<in> set ?qs" by (simp add: shift_list.simps)
      hence "a \<in> poly_deg ` fst ` set ?qs" unfolding a by (intro imageI)
      with fin show ?thesis by (rule Max_ge)
    qed
  qed
  thus ?case using step(8) by (rule le_trans)
qed

lemma shift1_5: "shift1_inv args \<Longrightarrow> fst (shift1 args) = [] \<longleftrightarrow> fst args = []"
proof (induct args rule: shift1_induct)
  case (base qs B)
  show ?case ..
next
  case (step qs B h U x)
  let ?p1 = "(punit.monom_mult 1 (Poly_Mapping.single x 1) h, U)"
  let ?qs = "shift_list (h, U) x qs"
  from step(1) have "B = {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)}"
    and inv2: "shift2_inv qs" by (rule shift1_invD)+
  from this(1) have "B \<subseteq> set qs" by auto
  with step(2) have "qs \<noteq> []" by auto
  moreover have "fst (shift1 (?qs, B - {(h, U)})) \<noteq> []"
    by (simp add: step.hyps(8) del: One_nat_def) (simp add: shift_list.simps)
  ultimately show ?case by simp
qed

lemma shift1_6: "shift1_inv args \<Longrightarrow> monomial_decomp (fst args) \<Longrightarrow> monomial_decomp (fst (shift1 args))"
proof (induct args rule: shift1_induct)
  case (base qs B)
  from base(3) show ?case .
next
  case (step qs B h U x)
  from step(1-3) have "(h, U) \<in> set qs" by (rule shift1_inv_some_snd)
  with step.prems have "monomial_decomp (fst (shift_list (h, U) x qs, B - {(h, U)}))"
    unfolding fst_conv by (rule monomial_decomp_shift_list)
  thus ?case by (rule step.hyps)
qed

lemma shift1_7: "shift1_inv args \<Longrightarrow> hom_decomp (fst args) \<Longrightarrow> hom_decomp (fst (shift1 args))"
proof (induct args rule: shift1_induct)
  case (base qs B)
  from base(3) show ?case .
next
  case (step qs B h U x)
  from step(1-3) have "(h, U) \<in> set qs" by (rule shift1_inv_some_snd)
  with step.prems have "hom_decomp (fst (shift_list (h, U) x qs, B - {(h, U)}))"
    unfolding fst_conv by (rule hom_decomp_shift_list)
  thus ?case by (rule step.hyps)
qed

end

lemma shift2_inv_preserved:
  assumes "shift2_inv d qs"
  shows "shift2_inv (Suc d) (fst (shift1 (qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)})))"
proof -
  define args where "args = (qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)})"
  from refl assms have inv1: "shift1_inv d args" unfolding args_def
    by (rule shift1_invI)
  hence "shift1_inv d (shift1 args)" by (induct args rule: shift1_induct)
  hence "shift1_inv d (fst (shift1 args), snd (shift1 args))" by simp
  hence "shift2_inv d (fst (shift1 args))" by (rule shift1_invD)
  hence "valid_decomp X (fst (shift1 args))" and "standard_decomp k (fst (shift1 args))"
    and "exact_decomp (Suc m) (fst (shift1 args))" by (rule shift2_invD)+
  thus "shift2_inv (Suc d) (fst (shift1 args))"
  proof (rule shift2_invI)
    fix d0
    assume "d0 < Suc d"
    hence "d0 \<le> d" by simp
    with inv1 show "card {q \<in> set (fst (shift1 args)). poly_deg (fst q) = d0 \<and> m < card (snd q)} \<le> 1"
      by (rule shift1_1)
  qed
qed

function shift2 :: "nat \<Rightarrow> nat \<Rightarrow> ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) list \<Rightarrow>
                      ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::{comm_ring_1,ring_no_zero_divisors}) \<times> 'x set) list" where
  "shift2 c d qs =
      (if c \<le> d then qs
      else shift2 c (Suc d) (fst (shift1 (qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)}))))"
  by auto
termination proof
  show "wf (measure (\<lambda>(c, d, _). c - d))" by (fact wf_measure)
qed simp

lemma shift2_1: "shift2_inv d qs \<Longrightarrow> shift2_inv c (shift2 c d qs)"
proof (induct c d qs rule: shift2.induct)
  case IH: (1 c d qs)
  show ?case
  proof (subst shift2.simps, simp del: shift2.simps, intro conjI impI)
    assume "c \<le> d"
    show "shift2_inv c qs"
    proof (rule shift2_invI)
      from IH(2) show "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp (Suc m) qs"
        by (rule shift2_invD)+
    next
      fix d0
      assume "d0 < c"
      hence "d0 < d" using \<open>c \<le> d\<close> by (rule less_le_trans)
      with IH(2) show "card {q \<in> set qs. poly_deg (fst q) = d0 \<and> m < card (snd q)} \<le> 1"
        by (rule shift2_invD)
    qed
  next
    assume "\<not> c \<le> d"
    thus "shift2_inv c (shift2 c (Suc d) (fst (shift1 (qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)}))))"
    proof (rule IH)
      from IH(2) show "shift2_inv (Suc d) (fst (shift1 (qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)})))"
        by (rule shift2_inv_preserved)
    qed
  qed
qed

lemma shift2_2:
  "shift2_inv d qs \<Longrightarrow>
    card {q \<in> set (shift2 c d qs). m < card (snd q)} \<le> card {q \<in> set qs. m < card (snd q)}"
proof (induct c d qs rule: shift2.induct)
  case IH: (1 c d qs)
  let ?A = "{q \<in> set (shift2 c (Suc d) (fst (shift1 (qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)})))). m < card (snd q)}"
  show ?case
  proof (subst shift2.simps, simp del: shift2.simps, intro impI)
    assume "\<not> c \<le> d"
    hence "card ?A \<le> card {q \<in> set (fst (shift1 (qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)}))). m < card (snd q)}"
    proof (rule IH)
      show "shift2_inv (Suc d) (fst (shift1 (qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)})))"
        using IH(2) by (rule shift2_inv_preserved)
    qed
    also have "\<dots> \<le> card {q \<in> set (fst (qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)})). m < card (snd q)}"
      using refl IH(2) by (intro shift1_2 shift1_invI)
    finally show "card ?A \<le> card {q \<in> set qs. m < card (snd q)}" by (simp only: fst_conv)
  qed
qed

lemma shift2_3: "shift2_inv d qs \<Longrightarrow> cone_decomp T qs \<Longrightarrow> cone_decomp T (shift2 c d qs)"
proof (induct c d qs rule: shift2.induct)
  case IH: (1 c d qs)
  have inv2: "shift2_inv (Suc d) (fst (shift1 (qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)})))"
    using IH(2) by (rule shift2_inv_preserved)
  show ?case
  proof (subst shift2.simps, simp add: IH.prems del: shift2.simps, intro impI)
    assume "\<not> c \<le> d"
    moreover note inv2
    moreover have "cone_decomp T (fst (shift1 (qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)})))"
    proof (rule shift1_3)
      from refl IH(2) show "shift1_inv d (qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)})"
        by (rule shift1_invI)
    qed (simp add: IH.prems)
    ultimately show "cone_decomp T (shift2 c (Suc d) (fst (shift1 (qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)}))))"
      by (rule IH)
  qed
qed

lemma shift2_4:
  "shift2_inv d qs \<Longrightarrow> Max (poly_deg ` fst ` set qs) \<le> Max (poly_deg ` fst ` set (shift2 c d qs))"
proof (induct c d qs rule: shift2.induct)
  case IH: (1 c d qs)
  let ?args = "(qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)})"
  show ?case
  proof (subst shift2.simps, simp del: shift2.simps, intro impI)
    assume "\<not> c \<le> d"
    have "Max (poly_deg ` fst ` set (fst ?args)) \<le> Max (poly_deg ` fst ` set (fst (shift1 ?args)))"
      using refl IH(2) by (intro shift1_4 shift1_invI)
    also from \<open>\<not> c \<le> d\<close> have "\<dots> \<le> Max (poly_deg ` fst ` set (shift2 c (Suc d) (fst (shift1 ?args))))"
    proof (rule IH)
      from IH(2) show "shift2_inv (Suc d) (fst (shift1 ?args))"
        by (rule shift2_inv_preserved)
    qed
    finally show "Max (poly_deg ` fst ` set qs) \<le> Max (poly_deg ` fst ` set (shift2 c (Suc d) (fst (shift1 ?args))))"
      by (simp only: fst_conv)
  qed
qed

lemma shift2_5:
  "shift2_inv d qs \<Longrightarrow> shift2 c d qs = [] \<longleftrightarrow> qs = []"
proof (induct c d qs rule: shift2.induct)
  case IH: (1 c d qs)
  let ?args = "(qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)})"
  show ?case
  proof (subst shift2.simps, simp del: shift2.simps, intro impI)
    assume "\<not> c \<le> d"
    hence "shift2 c (Suc d) (fst (shift1 ?args)) = [] \<longleftrightarrow> fst (shift1 ?args) = []"
    proof (rule IH)
      from IH(2) show "shift2_inv (Suc d) (fst (shift1 ?args))"
        by (rule shift2_inv_preserved)
    qed
    also from refl IH(2) have "\<dots> \<longleftrightarrow> fst ?args = []" by (intro shift1_5 shift1_invI)
    finally show "shift2 c (Suc d) (fst (shift1 ?args)) = [] \<longleftrightarrow> qs = []" by (simp only: fst_conv)
  qed
qed

lemma shift2_6:
  "shift2_inv d qs \<Longrightarrow> monomial_decomp qs \<Longrightarrow> monomial_decomp (shift2 c d qs)"
proof (induct c d qs rule: shift2.induct)
  case IH: (1 c d qs)
  let ?args = "(qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)})"
  show ?case
  proof (subst shift2.simps, simp del: shift2.simps, intro conjI impI IH)
    from IH(2) show "shift2_inv (Suc d) (fst (shift1 ?args))" by (rule shift2_inv_preserved)
  next
    from refl IH(2) have "shift1_inv d ?args" by (rule shift1_invI)
    moreover from IH(3) have "monomial_decomp (fst ?args)" by simp
    ultimately show "monomial_decomp (fst (shift1 ?args))" by (rule shift1_6)
  qed
qed

lemma shift2_7:
  "shift2_inv d qs \<Longrightarrow> hom_decomp qs \<Longrightarrow> hom_decomp (shift2 c d qs)"
proof (induct c d qs rule: shift2.induct)
  case IH: (1 c d qs)
  let ?args = "(qs, {q \<in> set qs. poly_deg (fst q) = d \<and> m < card (snd q)})"
  show ?case
  proof (subst shift2.simps, simp del: shift2.simps, intro conjI impI IH)
    from IH(2) show "shift2_inv (Suc d) (fst (shift1 ?args))" by (rule shift2_inv_preserved)
  next
    from refl IH(2) have "shift1_inv d ?args" by (rule shift1_invI)
    moreover from IH(3) have "hom_decomp (fst ?args)" by simp
    ultimately show "hom_decomp (fst (shift1 ?args))" by (rule shift1_7)
  qed
qed

definition shift :: "((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) list \<Rightarrow>
                        ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::{comm_ring_1,ring_no_zero_divisors}) \<times> 'x set) list"
  where "shift qs = shift2 (k + card {q \<in> set qs. m < card (snd q)}) k qs"

lemma shift2_inv_init:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp (Suc m) qs"
  shows "shift2_inv k qs"
  using assms
proof (rule shift2_invI)
  fix d0
  assume "d0 < k"
  have "{q \<in> set qs. poly_deg (fst q) = d0 \<and> m < card (snd q)} = {}"
  proof -
    {
      fix q
      assume "q \<in> set qs"
      obtain h U where q: "q = (h, U)" using prod.exhaust by blast
      assume "poly_deg (fst q) = d0" and "m < card (snd q)"
      hence "poly_deg h < k" and "m < card U" using \<open>d0 < k\<close> by (simp_all add: q)
      from this(2) have "U \<noteq> {}" by auto
      with \<open>q \<in> set qs\<close> have "(h, U) \<in> set (qs\<^sub>+)" by (simp add: q pos_decomp_def)
      with assms(2) have "k \<le> poly_deg h" by (rule standard_decompD)
      with \<open>poly_deg h < k\<close> have False by simp
    }
    thus ?thesis by blast
  qed
  thus "card {q \<in> set qs. poly_deg (fst q) = d0 \<and> m < card (snd q)} \<le> 1" by (simp only: card_empty)
qed

lemma shift:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp (Suc m) qs"
  shows "valid_decomp X (shift qs)" and "standard_decomp k (shift qs)" and "exact_decomp m (shift qs)"
proof -
  define c where "c = card {q \<in> set qs. m < card (snd q)}"
  define A where "A = {q \<in> set (shift qs). m < card (snd q)}"
  from assms have "shift2_inv k qs" by (rule shift2_inv_init)
  hence inv2: "shift2_inv (k + c) (shift qs)" and "card A \<le> c"
    unfolding shift_def c_def A_def by (rule shift2_1, rule shift2_2)
  from inv2 have fin: "valid_decomp X (shift qs)" and std: "standard_decomp k (shift qs)"
    and exct: "exact_decomp (Suc m) (shift qs)"
    by (rule shift2_invD)+
  show "valid_decomp X (shift qs)" and "standard_decomp k (shift qs)" by fact+
  have "finite A" by (auto simp: A_def)

  show "exact_decomp m (shift qs)"
  proof (rule exact_decompI)
    fix h U
    assume "(h, U) \<in> set (shift qs)"
    with exct show "h \<in> P[X]" and "U \<subseteq> X" by (rule exact_decompD)+
  next
    fix h1 h2 U1 U2
    assume 1: "(h1, U1) \<in> set (shift qs)" and 2: "(h2, U2) \<in> set (shift qs)"
    assume 3: "poly_deg h1 = poly_deg h2" and 4: "m < card U1" and 5: "m < card U2"
    from 5 have "U2 \<noteq> {}" by auto
    with 2 have "(h2, U2) \<in> set ((shift qs)\<^sub>+)" by (simp add: pos_decomp_def)
    let ?C = "{q \<in> set (shift qs). poly_deg (fst q) = poly_deg h2 \<and> m < card (snd q)}"
    define B where "B = {q \<in> A. k \<le> poly_deg (fst q) \<and> poly_deg (fst q) \<le> poly_deg h2}"
    have "Suc (poly_deg h2) - k \<le> card B"
    proof -
      have "B = (\<Union>d0\<in>{k..poly_deg h2}. {q \<in> A. poly_deg (fst q) = d0})" by (auto simp: B_def)
      also have "card \<dots> = (\<Sum>d0=k..poly_deg h2. card {q \<in> A. poly_deg (fst q) = d0})"
      proof (intro card_UN_disjoint ballI impI)
        fix d0
        from _ \<open>finite A\<close> show "finite {q \<in> A. poly_deg (fst q) = d0}" by (rule finite_subset) blast
      next
        fix d0 d1 :: nat
        assume "d0 \<noteq> d1"
        thus "{q \<in> A. poly_deg (fst q) = d0} \<inter> {q \<in> A. poly_deg (fst q) = d1} = {}" by blast
      qed (fact finite_atLeastAtMost)
      also have "\<dots> \<ge> (\<Sum>d0=k..poly_deg h2. 1)"
      proof (rule sum_mono)
        fix d0
        assume "d0 \<in> {k..poly_deg h2}"
        hence "k \<le> d0" and "d0 \<le> poly_deg h2" by simp_all
        with std \<open>(h2, U2) \<in> set ((shift qs)\<^sub>+)\<close> obtain h' U' where "(h', U') \<in> set (shift qs)"
          and "poly_deg h' = d0" and "card U2 \<le> card U'" by (rule standard_decompE)
        from 5 this(3) have "m < card U'" by (rule less_le_trans)
        with \<open>(h', U') \<in> set (shift qs)\<close> have "(h', U') \<in> {q \<in> A. poly_deg (fst q) = d0}"
          by (simp add: A_def \<open>poly_deg h' = d0\<close>)
        hence "{q \<in> A. poly_deg (fst q) = d0} \<noteq> {}" by blast
        moreover from _ \<open>finite A\<close> have "finite {q \<in> A. poly_deg (fst q) = d0}"
          by (rule finite_subset) blast
        ultimately show "1 \<le> card {q \<in> A. poly_deg (fst q) = d0}"
          by (simp add: card_gt_0_iff Suc_le_eq)
      qed
      also have "(\<Sum>d0=k..poly_deg h2. 1) = Suc (poly_deg h2) - k" by auto
      finally show ?thesis .
    qed
    also from \<open>finite A\<close> _ have "\<dots> \<le> card A" by (rule card_mono) (auto simp: B_def)
    also have "\<dots> \<le> c" by fact
    finally have "poly_deg h2 < k + c" by simp
    with inv2 have "card ?C \<le> 1" by (rule shift2_invD)
    have "finite ?C" by auto
    moreover note \<open>card ?C \<le> 1\<close>
    moreover from 1 3 4 have "(h1, U1) \<in> ?C" by simp
    moreover from 2 5 have "(h2, U2) \<in> ?C" by simp
    ultimately show "(h1, U1) = (h2, U2)" by (auto simp: card_le_Suc0_iff_eq)
  qed
qed

lemma monomial_decomp_shift:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp (Suc m) qs"
    and "monomial_decomp qs"
  shows "monomial_decomp (shift qs)"
proof -
  from assms(1, 2, 3) have "shift2_inv k qs" by (rule shift2_inv_init)
  thus ?thesis unfolding shift_def using assms(4) by (rule shift2_6)
qed

lemma hom_decomp_shift:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp (Suc m) qs"
    and "hom_decomp qs"
  shows "hom_decomp (shift qs)"
proof -
  from assms(1, 2, 3) have "shift2_inv k qs" by (rule shift2_inv_init)
  thus ?thesis unfolding shift_def using assms(4) by (rule shift2_7)
qed

lemma cone_decomp_shift:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp (Suc m) qs"
    and "cone_decomp T qs"
  shows "cone_decomp T (shift qs)"
proof -
  from assms(1, 2, 3) have "shift2_inv k qs" by (rule shift2_inv_init)
  thus ?thesis unfolding shift_def using assms(4) by (rule shift2_3)
qed

lemma Max_shift_ge:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp (Suc m) qs"
  shows "Max (poly_deg ` fst ` set qs) \<le> Max (poly_deg ` fst ` set (shift qs))"
proof -
  from assms(1-3) have "shift2_inv k qs" by (rule shift2_inv_init)
  thus ?thesis unfolding shift_def by (rule shift2_4)
qed

lemma shift_Nil_iff:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp (Suc m) qs"
  shows "shift qs = [] \<longleftrightarrow> qs = []"
proof -
  from assms(1-3) have "shift2_inv k qs" by (rule shift2_inv_init)
  thus ?thesis unfolding shift_def by (rule shift2_5)
qed

end

primrec exact_aux :: "nat \<Rightarrow> nat \<Rightarrow> ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) list \<Rightarrow>
                      ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::{comm_ring_1,ring_no_zero_divisors}) \<times> 'x set) list" where
  "exact_aux k 0 qs = qs" |
  "exact_aux k (Suc m) qs = exact_aux k m (shift k m qs)"

lemma exact_aux:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp m qs"
  shows "valid_decomp X (exact_aux k m qs)" (is ?thesis1)
    and "standard_decomp k (exact_aux k m qs)" (is ?thesis2)
    and "exact_decomp 0 (exact_aux k m qs)" (is ?thesis3)
proof -
  from assms have "?thesis1 \<and> ?thesis2 \<and> ?thesis3"
  proof (induct m arbitrary: qs)
    case 0
    thus ?case by simp
  next
    case (Suc m)
    let ?qs = "shift k m qs"
    have "valid_decomp X (exact_aux k m ?qs) \<and> standard_decomp k (exact_aux k m ?qs) \<and>
          exact_decomp 0 (exact_aux k m ?qs)"
    proof (rule Suc)
      from Suc.prems show "valid_decomp X ?qs" and "standard_decomp k ?qs" and "exact_decomp m ?qs"
        by (rule shift)+
    qed
    thus ?case by simp
  qed
  thus ?thesis1 and ?thesis2 and ?thesis3 by simp_all
qed

lemma monomial_decomp_exact_aux:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp m qs" and "monomial_decomp qs"
  shows "monomial_decomp (exact_aux k m qs)"
  using assms
proof (induct m arbitrary: qs)
  case 0
  thus ?case by simp
next
  case (Suc m)
  let ?qs = "shift k m qs"
  have "monomial_decomp (exact_aux k m ?qs)"
  proof (rule Suc)
    show "valid_decomp X ?qs" and "standard_decomp k ?qs" and "exact_decomp m ?qs"
      using Suc.prems(1, 2, 3) by (rule shift)+
  next
    from Suc.prems show "monomial_decomp ?qs" by (rule monomial_decomp_shift)
  qed
  thus ?case by simp
qed

lemma hom_decomp_exact_aux:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp m qs" and "hom_decomp qs"
  shows "hom_decomp (exact_aux k m qs)"
  using assms
proof (induct m arbitrary: qs)
  case 0
  thus ?case by simp
next
  case (Suc m)
  let ?qs = "shift k m qs"
  have "hom_decomp (exact_aux k m ?qs)"
  proof (rule Suc)
    show "valid_decomp X ?qs" and "standard_decomp k ?qs" and "exact_decomp m ?qs"
      using Suc.prems(1, 2, 3) by (rule shift)+
  next
    from Suc.prems show "hom_decomp ?qs" by (rule hom_decomp_shift)
  qed
  thus ?case by simp
qed

lemma cone_decomp_exact_aux:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp m qs" and "cone_decomp T qs"
  shows "cone_decomp T (exact_aux k m qs)"
  using assms
proof (induct m arbitrary: qs)
  case 0
  thus ?case by simp
next
  case (Suc m)
  let ?qs = "shift k m qs"
  have "cone_decomp T (exact_aux k m ?qs)"
  proof (rule Suc)
    show "valid_decomp X ?qs" and "standard_decomp k ?qs" and "exact_decomp m ?qs"
      using Suc.prems(1, 2, 3) by (rule shift)+
  next
    from Suc.prems show "cone_decomp T ?qs" by (rule cone_decomp_shift)
  qed
  thus ?case by simp
qed

lemma Max_exact_aux_ge:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp m qs"
  shows "Max (poly_deg ` fst ` set qs) \<le> Max (poly_deg ` fst ` set (exact_aux k m qs))"
  using assms
proof (induct m arbitrary: qs)
  case 0
  thus ?case by simp
next
  case (Suc m)
  let ?qs = "shift k m qs"
  from Suc.prems have "Max (poly_deg ` fst ` set qs) \<le> Max (poly_deg ` fst ` set ?qs)"
    by (rule Max_shift_ge)
  also have "\<dots> \<le> Max (poly_deg ` fst ` set (exact_aux k m ?qs))"
  proof (rule Suc)
    from Suc.prems show "valid_decomp X ?qs" and "standard_decomp k ?qs" and "exact_decomp m ?qs"
      by (rule shift)+
  qed
  finally show ?case by simp
qed

lemma exact_aux_Nil_iff:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "exact_decomp m qs"
  shows "exact_aux k m qs = [] \<longleftrightarrow> qs = []"
  using assms
proof (induct m arbitrary: qs)
  case 0
  thus ?case by simp
next
  case (Suc m)
  let ?qs = "shift k m qs"
  have "exact_aux k m ?qs = [] \<longleftrightarrow> ?qs = []"
  proof (rule Suc)
    from Suc.prems show "valid_decomp X ?qs" and "standard_decomp k ?qs" and "exact_decomp m ?qs"
      by (rule shift)+
  qed
  also from Suc.prems have "\<dots> \<longleftrightarrow> qs = []" by (rule shift_Nil_iff)
  finally show ?case by simp
qed

definition exact :: "nat \<Rightarrow> ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) list \<Rightarrow>
                        ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::{comm_ring_1,ring_no_zero_divisors}) \<times> 'x set) list"
  where "exact k qs = exact_aux k (card X) qs"

lemma exact:
  assumes "valid_decomp X qs" and "standard_decomp k qs"
  shows "valid_decomp X (exact k qs)" (is ?thesis1)
    and "standard_decomp k (exact k qs)" (is ?thesis2)
    and "exact_decomp 0 (exact k qs)" (is ?thesis3)
proof -
  from assms(1) le_refl have "exact_decomp (card X) qs" by (rule exact_decomp_card_X)
  with assms show ?thesis1 and ?thesis2 and ?thesis3 unfolding exact_def by (rule exact_aux)+
qed

lemma monomial_decomp_exact:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "monomial_decomp qs"
  shows "monomial_decomp (exact k qs)"
proof -
  from assms(1) le_refl have "exact_decomp (card X) qs" by (rule exact_decomp_card_X)
  with assms(1, 2) show ?thesis unfolding exact_def using assms(3) by (rule monomial_decomp_exact_aux)
qed

lemma hom_decomp_exact:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "hom_decomp qs"
  shows "hom_decomp (exact k qs)"
proof -
  from assms(1) le_refl have "exact_decomp (card X) qs" by (rule exact_decomp_card_X)
  with assms(1, 2) show ?thesis unfolding exact_def using assms(3) by (rule hom_decomp_exact_aux)
qed

lemma cone_decomp_exact:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "cone_decomp T qs"
  shows "cone_decomp T (exact k qs)"
proof -
  from assms(1) le_refl have "exact_decomp (card X) qs" by (rule exact_decomp_card_X)
  with assms(1, 2) show ?thesis unfolding exact_def using assms(3) by (rule cone_decomp_exact_aux)
qed

lemma Max_exact_ge:
  assumes "valid_decomp X qs" and "standard_decomp k qs"
  shows "Max (poly_deg ` fst ` set qs) \<le> Max (poly_deg ` fst ` set (exact k qs))"
proof -
  from assms(1) le_refl have "exact_decomp (card X) qs" by (rule exact_decomp_card_X)
  with assms(1, 2) show ?thesis unfolding exact_def by (rule Max_exact_aux_ge)
qed

lemma exact_Nil_iff:
  assumes "valid_decomp X qs" and "standard_decomp k qs"
  shows "exact k qs = [] \<longleftrightarrow> qs = []"
proof -
  from assms(1) le_refl have "exact_decomp (card X) qs" by (rule exact_decomp_card_X)
  with assms(1, 2) show ?thesis unfolding exact_def by (rule exact_aux_Nil_iff)
qed

corollary \<b>_zero_exact:
  assumes "valid_decomp X qs" and "standard_decomp k qs" and "qs \<noteq> []"
  shows "Suc (Max (poly_deg ` fst ` set qs)) \<le> \<b> (exact k qs) 0"
proof -
  from assms(1, 2) have "Max (poly_deg ` fst ` set qs) \<le> Max (poly_deg ` fst ` set (exact k qs))"
    by (rule Max_exact_ge)
  also have "Suc \<dots> \<le> \<b> (exact k qs) 0"
  proof (rule \<b>_zero)
    from assms show "exact k qs \<noteq> []" by (simp add: exact_Nil_iff)
  qed
  finally show ?thesis by simp
qed

lemma normal_form_exact_decompE:
  assumes "F \<subseteq> P[X]"
  obtains qs where "valid_decomp X qs" and "standard_decomp 0 qs" and "monomial_decomp qs"
    and "cone_decomp (normal_form F ` P[X]) qs" and "exact_decomp 0 qs"
    and "\<And>g. (\<And>f. f \<in> F \<Longrightarrow> homogeneous f) \<Longrightarrow> g \<in> punit.reduced_GB F \<Longrightarrow> poly_deg g \<le> \<b> qs 0"
proof -
  let ?G = "punit.reduced_GB F"
  let ?S = "lpp ` ?G"
  let ?N = "normal_form F ` P[X]"
  define qs::"((_ \<Rightarrow>\<^sub>0 'a) \<times> _) list" where "qs = snd (split 0 X ?S)"
  from fin_X assms have std: "standard_decomp 0 qs" and cn: "cone_decomp ?N qs"
    unfolding qs_def by (rule standard_cone_decomp_snd_split)+
  from fin_X assms have "finite ?G" by (rule finite_reduced_GB_Polys)
  hence "finite ?S" by (rule finite_imageI)
  with fin_X subset_refl have valid: "valid_decomp X qs" unfolding qs_def using zero_in_PPs
    by (rule valid_decomp_split)
  from fin_X subset_refl \<open>finite ?S\<close> have md: "monomial_decomp qs"
    unfolding qs_def by (rule monomial_decomp_split)
  let ?qs = "exact 0 qs"
  from valid std have "valid_decomp X ?qs" and "standard_decomp 0 ?qs" by (rule exact)+
  moreover from valid std md have "monomial_decomp ?qs" by (rule monomial_decomp_exact)
  moreover from valid std cn have "cone_decomp ?N ?qs" by (rule cone_decomp_exact)
  moreover from valid std have "exact_decomp 0 ?qs" by (rule exact)
  moreover have "poly_deg g \<le> \<b> ?qs 0" if "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "g \<in> ?G" for g
  proof (cases "qs = []")
    case True
    from one_in_Polys have "normal_form F 1 \<in> ?N" by (rule imageI)
    also from True cn have "\<dots> = {0}" by (simp add: cone_decomp_def direct_decomp_def bij_betw_def)
    finally have "?G = {1}" using fin_X assms
      by (simp add: normal_form_zero_iff ideal_eq_UNIV_iff_reduced_GB_eq_one_Polys
                flip: ideal_eq_UNIV_iff_contains_one)
    with that(2) show ?thesis by simp
  next
    case False
    from fin_X assms that have "poly_deg g \<le> Suc (Max (poly_deg ` fst ` set qs))"
      unfolding qs_def by (rule standard_cone_decomp_snd_split)
    also from valid std False have "\<dots> \<le> \<b> ?qs 0" by (rule \<b>_zero_exact)
    finally show ?thesis .
  qed
  ultimately show ?thesis ..
qed

end

end

end (* pm_powerprod *)

end (* theory *)
