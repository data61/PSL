(* Author: Alexander Maletzky *)

theory More_Modules
  imports HOL.Modules
begin

text \<open>More facts about modules.\<close>

section \<open>Modules over Commutative Rings\<close>

context module
begin

lemma scale_minus_both [simp]: "(- a) *s (- x) = a *s x"
  by simp

subsection \<open>Submodules Spanned by Sets of Module-Elements\<close>

lemma span_insertI:
  assumes "p \<in> span B"
  shows "p \<in> span (insert r B)"
proof -
  have "B \<subseteq> insert r B" by blast
  hence "span B \<subseteq> span (insert r B)" by (rule span_mono)
  with assms show ?thesis ..
qed

lemma span_insertD:
  assumes "p \<in> span (insert r B)" and "r \<in> span B"
  shows "p \<in> span B"
  using assms(1)
proof (induct p rule: span_induct_alt)
  case base
  show "0 \<in> span B" by (fact span_zero)
next
  case step: (step q b a)
  from step(1) have "b = r \<or> b \<in> B" by simp
  thus "q *s b + a \<in> span B"
  proof
    assume eq: "b = r"
    from step(2) assms(2) show ?thesis unfolding eq by (intro span_add span_scale)
  next
    assume "b \<in> B"
    hence "b \<in> span B" using span_superset ..
    with step(2) show ?thesis by (intro span_add span_scale)
  qed
qed

lemma span_insert_idI:
  assumes "r \<in> span B"
  shows "span (insert r B) = span B"
proof (intro subset_antisym subsetI)
  fix p
  assume "p \<in> span (insert r B)"
  from this assms show "p \<in> span B" by (rule span_insertD)
next
  fix p
  assume "p \<in> span B"
  thus "p \<in> span (insert r B)" by (rule span_insertI)
qed

lemma span_insert_zero: "span (insert 0 B) = span B"
  using span_zero by (rule span_insert_idI)

lemma span_Diff_zero: "span (B - {0}) = span B"
  by (metis span_insert_zero insert_Diff_single)

lemma span_insert_subset:
  assumes "span A \<subseteq> span B" and "r \<in> span B"
  shows "span (insert r A) \<subseteq> span B"
proof
  fix p
  assume "p \<in> span (insert r A)"
  thus "p \<in> span B"
  proof (induct p rule: span_induct_alt)
    case base
    show ?case by (fact span_zero)
  next
    case step: (step q b a)
    show ?case
    proof (intro span_add span_scale)
      from \<open>b \<in> insert r A\<close> show "b \<in> span B"
      proof
        assume "b = r"
        thus "b \<in> span B" using assms(2) by simp
      next
        assume "b \<in> A"
        hence "b \<in> span A" using span_superset ..
        thus "b \<in> span B" using assms(1) ..
      qed
    qed fact
  qed
qed

lemma replace_span:
  assumes "q \<in> span B"
  shows "span (insert q (B - {p})) \<subseteq> span B"
  by (rule span_insert_subset, rule span_mono, fact Diff_subset, fact)

lemma sum_in_spanI: "(\<Sum>b\<in>B. q b *s b) \<in> span B"
  by (auto simp: intro: span_sum span_scale dest: span_base)

lemma span_closed_sum_list: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<in> span B) \<Longrightarrow> sum_list xs \<in> span B"
  by (induct xs) (auto intro: span_zero span_add)

lemma spanE:
  assumes "p \<in> span B"
  obtains A q where "finite A" and "A \<subseteq> B" and "p = (\<Sum>b\<in>A. (q b) *s b)"
  using assms by (auto simp: span_explicit)

lemma span_finite_subset:
  assumes "p \<in> span B"
  obtains A where "finite A" and "A \<subseteq> B" and "p \<in> span A"
proof -
  from assms obtain A q where "finite A" and "A \<subseteq> B" and p: "p = (\<Sum>a\<in>A. q a *s a)"
    by (rule spanE)
  note this(1, 2)
  moreover have "p \<in> span A" unfolding p by (rule sum_in_spanI)
  ultimately show ?thesis ..
qed

lemma span_finiteE:
  assumes "finite B" and "p \<in> span B"
  obtains q where "p = (\<Sum>b\<in>B. (q b) *s b)"
  using assms by (auto simp: span_finite)

lemma span_subset_spanI:
  assumes "A \<subseteq> span B"
  shows "span A \<subseteq> span B"
  using assms subspace_span by (rule span_minimal)

lemma span_insert_cong:
  assumes "span A = span B"
  shows "span (insert p A) = span (insert p B)" (is "?l = ?r")
proof
  have 1: "span (insert p C1) \<subseteq> span (insert p C2)" if "span C1 = span C2" for C1 C2
  proof (rule span_subset_spanI)
    show "insert p C1 \<subseteq> span (insert p C2)"
    proof (rule insert_subsetI)
      show "p \<in> span (insert p C2)" by (rule span_base) simp
    next
      have "C1 \<subseteq> span C1" by (rule span_superset)
      also from that have "\<dots> = span C2" .
      also have "\<dots> \<subseteq> span (insert p C2)" by (rule span_mono) blast
      finally show "C1 \<subseteq> span (insert p C2)" .
    qed
  qed
  from assms show "?l \<subseteq> ?r" by (rule 1)
  from assms[symmetric] show "?r \<subseteq> ?l" by (rule 1)
qed

lemma span_induct' [consumes 1, case_names base step]:
  assumes "p \<in> span B" and "P 0"
    and "\<And>a q p. a \<in> span B \<Longrightarrow> P a \<Longrightarrow> p \<in> B \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> P (a + q *s p)"
  shows "P p"
  using assms(1, 1)
proof (induct p rule: span_induct_alt)
  case base
  from assms(2) show ?case .
next
  case (step q b a)
  from step.hyps(1) have "b \<in> span B" by (rule span_base)
  hence "q *s b \<in> span B" by (rule span_scale)
  with step.prems have "a \<in> span B" by (simp only: span_add_eq)
  hence "P a" by (rule step.hyps)
  show ?case
  proof (cases "q = 0")
    case True
    from \<open>P a\<close> show ?thesis by (simp add: True)
  next
    case False
    with \<open>a \<in> span B\<close> \<open>P a\<close> step.hyps(1) have "P (a + q *s b)" by (rule assms(3))
    thus ?thesis by (simp only: add.commute)
  qed
qed

lemma span_INT_subset: "span (\<Inter>a\<in>A. f a) \<subseteq> (\<Inter>a\<in>A. span (f a))" (is "?l \<subseteq> ?r")
proof
  fix p
  assume "p \<in> ?l"
  show "p \<in> ?r"
  proof
    fix a
    assume "a \<in> A"
    from \<open>p \<in> ?l\<close> show "p \<in> span (f a)"
    proof (induct p rule: span_induct')
      case base
      show ?case by (fact span_zero)
    next
      case (step p q b)
      from step(3) \<open>a \<in> A\<close> have "b \<in> f a" ..
      hence "b \<in> span (f a)" by (rule span_base)
      with step(2) show ?case by (intro span_add span_scale)
    qed
  qed
qed

lemma span_INT: "span (\<Inter>a\<in>A. span (f a)) = (\<Inter>a\<in>A. span (f a))" (is "?l = ?r")
proof
  have "?l \<subseteq> (\<Inter>a\<in>A. span (span (f a)))" by (rule span_INT_subset)
  also have "... = ?r" by (simp add: span_span)
  finally show "?l \<subseteq> ?r" .
qed (fact span_superset)

lemma span_Int_subset: "span (A \<inter> B) \<subseteq> span A \<inter> span B"
proof -
  have "span (A \<inter> B) = span (\<Inter>x\<in>{A, B}. x)" by simp
  also have "\<dots> \<subseteq> (\<Inter>x\<in>{A, B}. span x)" by (fact span_INT_subset)
  also have "\<dots> = span A \<inter> span B" by simp
  finally show ?thesis .
qed

lemma span_Int: "span (span A \<inter> span B) = span A \<inter> span B"
proof -
  have "span (span A \<inter> span B) = span (\<Inter>x\<in>{A, B}. span x)" by simp
  also have "\<dots> = (\<Inter>x\<in>{A, B}. span x)" by (fact span_INT)
  also have "\<dots> = span A \<inter> span B" by simp
  finally show ?thesis .
qed

lemma span_image_scale_eq_image_scale: "span ((*s) q ` F) = (*s) q ` span F" (is "?A = ?B")
proof (intro subset_antisym subsetI)
  fix p
  assume "p \<in> ?A"
  thus "p \<in> ?B"
  proof (induct p rule: span_induct')
    case base
    from span_zero show ?case by (rule rev_image_eqI) simp
  next
    case (step p r a)
    from step.hyps(2) obtain p' where "p' \<in> span F" and p: "p = q *s p'" ..
    from step.hyps(3) obtain a' where "a' \<in> F" and a: "a = q *s a'" ..
    from this(1) have "a' \<in> span F" by (rule span_base)
    hence "r *s a' \<in> span F" by (rule span_scale)
    with \<open>p' \<in> span F\<close> have "p' + r *s a' \<in> span F" by (rule span_add)
    hence "q *s (p' + r *s a') \<in> ?B" by (rule imageI)
    also have "q *s (p' + r *s a') = p + r *s a" by (simp add: a p algebra_simps)
    finally show ?case .
  qed
next
  fix p
  assume "p \<in> ?B"
  then obtain p' where "p' \<in> span F" and "p = q *s p'" ..
  from this(1) show "p \<in> ?A" unfolding \<open>p = q *s p'\<close>
  proof (induct p' rule: span_induct')
    case base
    show ?case by (simp add: span_zero)
  next
    case (step p r a)
    from step.hyps(3) have "q *s a \<in> (*s) q ` F" by (rule imageI)
    hence "q *s a \<in> ?A" by (rule span_base)
    hence "r *s (q *s a) \<in> ?A" by (rule span_scale)
    with step.hyps(2) have "q *s p + r *s (q *s a) \<in> ?A" by (rule span_add)
    also have "q *s p + r *s (q *s a) = q *s (p + r *s a)" by (simp add: algebra_simps)
    finally show ?case .
  qed
qed

end (* module *)

section \<open>Ideals over Commutative Rings\<close>

lemma module_times: "module (*)"
  by (standard, simp_all add: algebra_simps)

interpretation ideal: module times
  by (fact module_times)

declare ideal.scale_scale[simp del]

abbreviation "ideal \<equiv> ideal.span"

lemma ideal_eq_UNIV_iff_contains_one: "ideal B = UNIV \<longleftrightarrow> 1 \<in> ideal B"
proof
  assume *: "1 \<in> ideal B"
  show "ideal B = UNIV"
  proof
    show "UNIV \<subseteq> ideal B"
    proof
      fix x
      from * have "x * 1 \<in> ideal B" by (rule ideal.span_scale)
      thus "x \<in> ideal B" by simp
    qed
  qed simp
qed simp

lemma ideal_eq_zero_iff [iff]: "ideal F = {0} \<longleftrightarrow> F \<subseteq> {0}"
  by (metis empty_subsetI ideal.span_empty ideal.span_eq)

lemma ideal_field_cases:
  obtains "ideal B = {0}" | "ideal (B::'a::field set) = UNIV"
proof (cases "ideal B = {0}")
  case True
  thus ?thesis ..
next
  case False
  hence "\<not> B \<subseteq> {0}" by simp
  then obtain b where "b \<in> B" and "b \<noteq> 0" by blast
  from this(1) have "b \<in> ideal B" by (rule ideal.span_base)
  hence "inverse b * b \<in> ideal B" by (rule ideal.span_scale)
  with \<open>b \<noteq> 0\<close> have "ideal B = UNIV" by (simp add: ideal_eq_UNIV_iff_contains_one)
  thus ?thesis ..
qed

corollary ideal_field_disj: "ideal B = {0} \<or> ideal (B::'a::field set) = UNIV"
  by (rule ideal_field_cases) blast+

lemma image_ideal_subset:
  assumes "\<And>x y. h (x + y) = h x + h y" and "\<And>x y. h (x * y) = h x * h y"
  shows "h ` ideal F \<subseteq> ideal (h ` F)"
proof (intro subsetI, elim imageE)
  fix g f
  assume g: "g = h f"
  assume "f \<in> ideal F"
  thus "g \<in> ideal (h ` F)" unfolding g
  proof (induct f rule: ideal.span_induct_alt)
    case base
    have "h 0 = h (0 + 0)" by simp
    also have "\<dots> = h 0 + h 0" by (simp only: assms(1))
    finally show ?case by (simp add: ideal.span_zero)
  next
    case (step c f g)
    from step.hyps(1) have "h f \<in> ideal (h ` F)"
      by (intro ideal.span_base imageI)
    hence "h c * h f \<in> ideal (h ` F)" by (rule ideal.span_scale)
    hence "h c * h f + h g \<in> ideal (h ` F)"
      using step.hyps(2) by (rule ideal.span_add)
    thus ?case by (simp only: assms)
  qed
qed

lemma image_ideal_eq_surj:
  assumes "\<And>x y. h (x + y) = h x + h y" and "\<And>x y. h (x * y) = h x * h y" and "surj h"
  shows "h ` ideal B = ideal (h ` B)"
proof
  from assms(1, 2) show "h ` ideal B \<subseteq> ideal (h ` B)" by (rule image_ideal_subset)
next
  show "ideal (h ` B) \<subseteq> h ` ideal B"
  proof
    fix b
    assume "b \<in> ideal (h ` B)"
    thus "b \<in> h ` ideal B"
    proof (induct b rule: ideal.span_induct_alt)
      case base
      have "h 0 = h (0 + 0)" by simp
      also have "\<dots> = h 0 + h 0" by (simp only: assms(1))
      finally have "0 = h 0" by simp
      with ideal.span_zero show ?case by (rule rev_image_eqI)
    next
      case (step c b a)
      from assms(3) obtain c' where c: "c = h c'" by (rule surjE)
      from step.hyps(2) obtain a' where "a' \<in> ideal B" and a: "a = h a'" ..
      from step.hyps(1) obtain b' where "b' \<in> B" and b: "b = h b'" ..
      from this(1) have "b' \<in> ideal B" by (rule ideal.span_base)
      hence "c' * b' \<in> ideal B" by (rule ideal.span_scale)
      hence "c' * b' + a' \<in> ideal B" using \<open>a' \<in> _\<close> by (rule ideal.span_add)
      moreover have "c * b + a = h (c' * b' + a')"
        by (simp add: c b a assms(1, 2))
      ultimately show ?case by (rule rev_image_eqI)
    qed
  qed
qed

context
  fixes h :: "'a \<Rightarrow> 'a::comm_ring_1"
  assumes h_plus: "h (x + y) = h x + h y"
  assumes h_times: "h (x * y) = h x * h y"
  assumes h_idem: "h (h x) = h x"
begin

lemma in_idealE_homomorphism_finite:
  assumes "finite B" and "B \<subseteq> range h" and "p \<in> range h" and "p \<in> ideal B"
  obtains q where "\<And>b. q b \<in> range h" and "p = (\<Sum>b\<in>B. q b * b)"
proof -
  from assms(1, 4) obtain q0 where p: "p = (\<Sum>b\<in>B. q0 b * b)" by (rule ideal.span_finiteE)
  define q where "q = (\<lambda>b. h (q0 b))"
  show ?thesis
  proof
    fix b
    show "q b \<in> range h" unfolding q_def by (rule rangeI)
  next
    from assms(3) obtain p' where "p = h p'" ..
    hence "p = h p" by (simp only: h_idem)
    also from \<open>finite B\<close> have "\<dots> = (\<Sum>b\<in>B. q b * h b)" unfolding p
    proof (induct B)
      case empty
      have "h 0 = h (0 + 0)" by simp
      also have "\<dots> = h 0 + h 0" by (simp only: h_plus)
      finally show ?case by simp
    next
      case (insert b B)
      thus ?case by (simp add: h_plus h_times q_def)
    qed
    also from refl have "\<dots> = (\<Sum>b\<in>B. q b * b)"
    proof (rule sum.cong)
      fix b
      assume "b \<in> B"
      hence "b \<in> range h" using assms(2) ..
      then obtain b' where "b = h b'" ..
      thus "q b * h b = q b * b" by (simp only: h_idem)
    qed
    finally show "p = (\<Sum>b\<in>B. q b * b)" .
  qed
qed

corollary in_idealE_homomorphism:
  assumes "B \<subseteq> range h" and "p \<in> range h" and "p \<in> ideal B"
  obtains A q where "finite A" and "A \<subseteq> B" and "\<And>b. q b \<in> range h" and "p = (\<Sum>b\<in>A. q b * b)"
proof -
  from assms(3) obtain A where "finite A" and "A \<subseteq> B" and "p \<in> ideal A"
    by (rule ideal.span_finite_subset)
  from this(2) assms(1) have "A \<subseteq> range h" by (rule subset_trans)
  with \<open>finite A\<close> obtain q where "\<And>b. q b \<in> range h" and "p = (\<Sum>b\<in>A. q b * b)"
    using assms(2) \<open>p \<in> ideal A\<close> by (rule in_idealE_homomorphism_finite) blast
  with \<open>finite A\<close> \<open>A \<subseteq> B\<close> show ?thesis ..
qed

lemma ideal_induct_homomorphism [consumes 3, case_names 0 plus]:
  assumes "B \<subseteq> range h" and "p \<in> range h" and "p \<in> ideal B"
  assumes "P 0" and "\<And>c b a. c \<in> range h \<Longrightarrow> b \<in> B \<Longrightarrow> P a \<Longrightarrow> a \<in> range h \<Longrightarrow> P (c * b + a)"
  shows "P p"
proof -
  from assms(1-3) obtain A q where "finite A" and "A \<subseteq> B" and rl: "\<And>f. q f \<in> range h"
    and p: "p = (\<Sum>f\<in>A. q f * f)" by (rule in_idealE_homomorphism) blast
  show ?thesis unfolding p using \<open>finite A\<close> \<open>A \<subseteq> B\<close>
  proof (induct A)
    case empty
    from assms(4) show ?case by simp
  next
    case (insert a A)
    from insert.hyps(1, 2) have "(\<Sum>f\<in>insert a A. q f * f) = q a * a + (\<Sum>f\<in>A. q f * f)" by simp
    also from rl have "P \<dots>"
    proof (rule assms(5))
      have "a \<in> insert a A" by simp
      thus "a \<in> B" using insert.prems ..
    next
      from insert.prems have "A \<subseteq> B" by simp
      thus "P (\<Sum>f\<in>A. q f * f)" by (rule insert.hyps)
    next
      from insert.prems have "A \<subseteq> B" by simp
      hence "A \<subseteq> range h" using assms(1) by (rule subset_trans)
      with \<open>finite A\<close> show "(\<Sum>f\<in>A. q f * f) \<in> range h"
      proof (induct A)
        case empty
        have "h 0 = h (0 + 0)" by simp
        also have "\<dots> = h 0 + h 0" by (simp only: h_plus)
        finally have "(\<Sum>f\<in>{}. q f * f) = h 0" by simp
        thus ?case by (rule image_eqI) simp
      next
        case (insert a A)
        from insert.prems have "a \<in> range h" and "A \<subseteq> range h" by simp_all
        from this(1) obtain a' where a: "a = h a'" ..
        from \<open>q a \<in> range h\<close> obtain q' where q: "q a = h q'" ..
        from \<open>A \<subseteq> _\<close> have "(\<Sum>f\<in>A. q f * f) \<in> range h" by (rule insert.hyps)
        then obtain m where eq: "(\<Sum>f\<in>A. q f * f) = h m" ..
        from insert.hyps(1, 2) have "(\<Sum>f\<in>insert a A. q f * f) = q a * a + (\<Sum>f\<in>A. q f * f)" by simp
        also have "\<dots> = h (q' * a' + m)" unfolding q by (simp add: a eq h_plus h_times)
        also have "\<dots> \<in> range h" by (rule rangeI)
        finally show ?case .
      qed
    qed
    finally show ?case .
  qed
qed

lemma image_ideal_eq_Int: "h ` ideal B = ideal (h ` B) \<inter> range h"
proof
  from h_plus h_times have "h ` ideal B \<subseteq> ideal (h ` B)" by (rule image_ideal_subset)
  thus "h ` ideal B \<subseteq> ideal (h ` B) \<inter> range h" by blast
next
  show "ideal (h ` B) \<inter> range h \<subseteq> h ` ideal B"
  proof
    fix b
    assume "b \<in> ideal (h ` B) \<inter> range h"
    hence "b \<in> ideal (h ` B)" and "b \<in> range h" by simp_all
    have "h ` B \<subseteq> range h" by blast
    thus "b \<in> h ` ideal B" using \<open>b \<in> range h\<close> \<open>b \<in> ideal (h ` B)\<close>
    proof (induct b rule: ideal_induct_homomorphism)
      case 0
      have "h 0 = h (0 + 0)" by simp
      also have "\<dots> = h 0 + h 0" by (simp only: h_plus)
      finally have "0 = h 0" by simp
      with ideal.span_zero show ?case by (rule rev_image_eqI)
    next
      case (plus c b a)
      from plus.hyps(1) obtain c' where c: "c = h c'" ..
      from plus.hyps(3) obtain a' where "a' \<in> ideal B" and a: "a = h a'" ..
      from plus.hyps(2) obtain b' where "b' \<in> B" and b: "b = h b'" ..
      from this(1) have "b' \<in> ideal B" by (rule ideal.span_base)
      hence "c' * b' \<in> ideal B" by (rule ideal.span_scale)
      hence "c' * b' + a' \<in> ideal B" using \<open>a' \<in> _\<close> by (rule ideal.span_add)
      moreover have "c * b + a = h (c' * b' + a')" by (simp add: a b c h_plus h_times)
      ultimately show ?case by (rule rev_image_eqI)
    qed
  qed
qed

end

end (* theory *)
