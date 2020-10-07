section \<open>Sets and Extended Natural Numbers\<close>

theory ESet_Extensions
imports
  "../Basics/Functions"
  Basic_Extensions
  CCPO_Extensions
begin

  lemma card_lessThan_enat[simp]: "card {..< enat k} = card {..< k}"
  proof -
    have 1: "{..< enat k} = enat ` {..< k}"
      unfolding lessThan_def image_Collect using enat_iless by force
    have "card {..< enat k} = card (enat ` {..< k})" unfolding 1 by rule
    also have "\<dots> = card {..< k}" using card_image inj_enat by metis
    finally show ?thesis by this
  qed
  lemma card_atMost_enat[simp]: "card {.. enat k} = card {.. k}"
  proof -
    have 1: "{.. enat k} = enat ` {.. k}"
      unfolding atMost_def image_Collect using enat_ile by force
    have "card {.. enat k} = card (enat ` {.. k})" unfolding 1 by rule
    also have "\<dots> = card {.. k}" using card_image inj_enat by metis
    finally show ?thesis by this
  qed

  lemma enat_Collect:
    assumes "\<infinity> \<notin> A"
    shows "{i. enat i \<in> A} = the_enat ` A"
    using assms by (safe, force) (metis enat_the_enat)

  lemma Collect_lessThan: "{i. enat i < n} = the_enat ` {..< n}"
  proof -
    have 1: "\<infinity> \<notin> {..< n}" by simp
    have "{i. enat i < n} = {i. enat i \<in> {..< n}}" by simp
    also have "\<dots> = the_enat ` {..< n}" using enat_Collect 1 by this
    finally show ?thesis by this
  qed

  instantiation set :: (type) esize_ccpo
  begin

    function esize_set where "finite A \<Longrightarrow> esize A = enat (card A)" | "infinite A \<Longrightarrow> esize A = \<infinity>"
      by auto termination by lexicographic_order

    lemma esize_iff_empty[iff]: "esize A = 0 \<longleftrightarrow> A = {}" by (cases "finite A", auto)
    lemma esize_iff_infinite[iff]: "esize A = \<infinity> \<longleftrightarrow> infinite A" by force
    lemma esize_singleton[simp]: "esize {a} = eSuc 0" by simp
    lemma esize_infinite_enat[dest, simp]: "infinite A \<Longrightarrow> enat k < esize A" by force

    instance
    proof
      fix A :: "'a set"
      assume 1: "esize A \<noteq> \<infinity>"
      show "finite {B. B \<subseteq> A}" using 1 by simp
    next
      fix A B :: "'a set"
      assume 1: "A \<subseteq> B"
      show "esize A \<le> esize B"
      proof (cases "finite B")
        case False
        show ?thesis using False by auto
      next
        case True
        have 2: "finite A" using True 1 by auto
        show ?thesis using card_mono True 1 2 by auto
      qed
    next
      fix A B :: "'a set"
      assume 1: "esize A \<noteq> \<infinity>" "A \<subset> B"
      show "esize A < esize B" using psubset_card_mono 1 by (cases "finite B", auto)
    qed

  end

  lemma esize_image[simp, intro]:
    assumes "inj_on f A"
    shows "esize (f ` A) = esize A"
    using card_image finite_imageD assms by (cases "finite A", auto)
  lemma esize_insert1[simp]: "a \<notin> A \<Longrightarrow> esize (insert a A) = eSuc (esize A)"
    by (cases "finite A", force+)
  lemma esize_insert2[simp]: "a \<in> A \<Longrightarrow> esize (insert a A) = esize A"
    using insert_absorb by metis
  lemma esize_remove1[simp]: "a \<notin> A \<Longrightarrow> esize (A - {a}) = esize A"
    by (cases "finite A", force+)
  lemma esize_remove2[simp]: "a \<in> A \<Longrightarrow> esize (A - {a}) = epred (esize A)"
    by (cases "finite A", force+)
  lemma esize_union_disjoint[simp]:
    assumes "A \<inter> B = {}"
    shows "esize (A \<union> B) = esize A + esize B"
  proof (cases "finite (A \<union> B)")
    case True
    show ?thesis using card_Un_disjoint assms True by auto
  next
    case False
    show ?thesis using False by (cases "finite A", auto)
  qed
  lemma esize_lessThan[simp]: "esize {..< n} = n"
  proof (cases n)
    case (enat k)
    have 1: "finite {..< n}" unfolding enat by (metis finite_lessThan_enat_iff not_enat_eq)
    show ?thesis using 1 unfolding enat by simp
  next
    case (infinity)
    have 1: "infinite {..< n}" unfolding infinity using infinite_lessThan_infty by simp
    show ?thesis using 1 unfolding infinity by simp
  qed
  lemma esize_atMost[simp]: "esize {.. n} = eSuc n"
  proof (cases n)
    case (enat k)
    have 1: "finite {.. n}" unfolding enat by (metis atMost_iff finite_enat_bounded)
    show ?thesis using 1 unfolding enat by simp
  next
    case (infinity)
    have 1: "infinite {.. n}"
      unfolding infinity
      by (metis atMost_iff enat_ord_code(3) infinite_lessThan_infty infinite_super subsetI)
    show ?thesis using 1 unfolding infinity by simp
  qed

  lemma least_eSuc[simp]:
    assumes "A \<noteq> {}"
    shows "least (eSuc ` A) = eSuc (least A)"
  proof (rule antisym)
    obtain k where 10: "k \<in> A" using assms by blast
    have 11: "eSuc k \<in> eSuc ` A" using 10 by auto
    have 20: "least A \<in> A" using 10 LeastI by metis
    have 21: "least (eSuc ` A) \<in> eSuc ` A" using 11 LeastI by metis
    have 30: "\<And> l. l \<in> A \<Longrightarrow> least A \<le> l" using 10 Least_le by metis
    have 31: "\<And> l. l \<in> eSuc ` A \<Longrightarrow> least (eSuc ` A) \<le> l" using 11 Least_le by metis
    show "least (eSuc ` A) \<le> eSuc (least A)" using 20 31 by auto
    show "eSuc (least A) \<le> least (eSuc ` A)" using 21 30 by auto
  qed

  lemma Inf_enat_eSuc[simp]: "\<Sqinter> (eSuc ` A) = eSuc (\<Sqinter> A)" unfolding Inf_enat_def by simp

  definition lift :: "nat set \<Rightarrow> nat set"
    where "lift A \<equiv> insert 0 (Suc ` A)"

  lemma liftI_0[intro, simp]: "0 \<in> lift A" unfolding lift_def by auto
  lemma liftI_Suc[intro]: "a \<in> A \<Longrightarrow> Suc a \<in> lift A" unfolding lift_def by auto
  lemma liftE[elim]:
    assumes "b \<in> lift A"
    obtains (0) "b = 0" | (Suc) a where "b = Suc a" "a \<in> A"
    using assms unfolding lift_def by auto

  lemma lift_esize[simp]: "esize (lift A) = eSuc (esize A)" unfolding lift_def by auto  
  lemma lift_least[simp]: "least (lift A) = 0" unfolding lift_def by auto

  primrec nth_least :: "'a set \<Rightarrow> nat \<Rightarrow> 'a :: wellorder"
    where "nth_least A 0 = least A" | "nth_least A (Suc n) = nth_least (A - {least A}) n"

  lemma nth_least_wellformed[intro?, simp]:
    assumes "enat n < esize A"
    shows "nth_least A n \<in> A"
  using assms
  proof (induct n arbitrary: A)
    case 0
    show ?case using 0 by simp
  next
    case (Suc n)
    have 1: "A \<noteq> {}" using Suc(2) by auto
    have 2: "enat n < esize (A - {least A})" using Suc(2) 1 by simp
    have 3: "nth_least (A - {least A}) n \<in> A - {least A}" using Suc(1) 2 by this
    show ?case using 3 by simp
  qed

  lemma card_wellformed[intro?, simp]:
    fixes k :: "'a :: wellorder"
    assumes "k \<in> A"
    shows "enat (card {i \<in> A. i < k}) < esize A"
  proof (cases "finite A")
    case False
    show ?thesis using False by simp
  next
    case True
    have 1: "esize {i \<in> A. i < k} < esize A" using True assms by fastforce
    show ?thesis using True 1 by simp
  qed

  lemma nth_least_strict_mono:
    assumes "enat l < esize A" "k < l"
    shows "nth_least A k < nth_least A l"
  using assms
  proof (induct k arbitrary: A l)
    case 0
    obtain l' where 1: "l = Suc l'" using 0(2) by (metis gr0_conv_Suc)
    have 2: "A \<noteq> {}" using 0(1) by auto
    have 3: "enat l' < esize (A - {least A})" using 0(1) 2 unfolding 1 by simp
    have 4: "nth_least (A - {least A}) l' \<in> A - {least A}" using 3 by rule
    show ?case using 1 4 by (auto intro: le_neq_trans)
  next
    case (Suc k)
    obtain l' where 1: "l = Suc l'" using Suc(3) by (metis Suc_lessE)
    have 2: "A \<noteq> {}" using Suc(2) by auto
    show ?case using Suc 2 unfolding 1 by simp
  qed
    
  lemma nth_least_mono[intro, simp]:
    assumes "enat l < esize A" "k \<le> l"
    shows "nth_least A k \<le> nth_least A l"
    using nth_least_strict_mono le_less assms by metis

  lemma card_nth_least[simp]:
    assumes "enat n < esize A"
    shows "card {k \<in> A. k < nth_least A n} = n"
  using assms
  proof (induct n arbitrary: A)
    case 0
    have 1: "{k \<in> A. k < least A} = {}" using least_not_less by auto
    show ?case using nth_least.simps(1) card_empty 1 by metis
  next
    case (Suc n)
    have 1: "A \<noteq> {}" using Suc(2) by auto
    have 2: "enat n < esize (A - {least A})" using Suc(2) 1 by simp
    have 3: "nth_least A 0 < nth_least A (Suc n)" using nth_least_strict_mono Suc(2) by blast
    have 4: "{k \<in> A. k < nth_least A (Suc n)} =
      {least A} \<union> {k \<in> A - {least A}. k < nth_least (A - {least A}) n}" using 1 3 by auto
    have 5: "card {k \<in> A - {least A}. k < nth_least (A - {least A}) n} = n" using Suc(1) 2 by this
    have 6: "finite {k \<in> A - {least A}. k < nth_least (A - {least A}) n}"
      using 5 Collect_empty_eq card_infinite infinite_imp_nonempty least_not_less nth_least.simps(1)
      by (metis (no_types, lifting))
    have "card {k \<in> A. k < nth_least A (Suc n)} =
      card ({least A} \<union> {k \<in> A - {least A}. k < nth_least (A - {least A}) n})" using 4 by simp
    also have "\<dots> = card {least A} + card {k \<in> A - {least A}. k < nth_least (A - {least A}) n}"
      using 6 by simp
    also have "\<dots> = Suc n" using 5 by simp
    finally show ?case by this
  qed

  lemma card_nth_least_le[simp]:
    assumes "enat n < esize A"
    shows "card {k \<in> A. k \<le> nth_least A n} = Suc n"
  proof -
    have 1: "{k \<in> A. k \<le> nth_least A n} = {nth_least A n} \<union> {k \<in> A. k < nth_least A n}"
      using assms by auto
    have 2: "card {k \<in> A. k < nth_least A n} = n" using assms by simp
    have 3: "finite {k \<in> A. k < nth_least A n}"
      using 2 Collect_empty_eq card_infinite infinite_imp_nonempty least_not_less nth_least.simps(1)
      by (metis (no_types, lifting))
    have "card {k \<in> A. k \<le> nth_least A n} = card ({nth_least A n} \<union> {k \<in> A. k < nth_least A n})"
      unfolding 1 by rule
    also have "\<dots> = card {nth_least A n} + card {k \<in> A. k < nth_least A n}" using 3 by simp
    also have "\<dots> = Suc n" using assms by simp
    finally show ?thesis by this
  qed

  lemma nth_least_card:
    fixes k :: nat
    assumes "k \<in> A"
    shows "nth_least A (card {i \<in> A. i < k}) = k"
  proof (rule nat_set_card_equality_less)
    have 1: "enat (card {l \<in> A. l < k}) < esize A"
    proof (cases "finite A")
      case False
      show ?thesis using False by simp
    next
      case True
      have 1: "{l \<in> A. l < k} \<subset> A" using assms by blast
      have 2: "card {l \<in> A. l < k} < card A" using psubset_card_mono True 1 by this
      show ?thesis using True 2 by simp
    qed
    show "nth_least A (card {l \<in> A. l < k}) \<in> A" using 1 by rule
    show "k \<in> A" using assms by this
    show "card {z \<in> A. z < nth_least A (card {i \<in> A. i < k})} = card {z \<in> A. z < k}" using 1 by simp
  qed

  interpretation nth_least:
    bounded_function_pair "{i. enat i < esize A}" "A" "nth_least A" "\<lambda> k. card {i \<in> A. i < k}"
    using nth_least_wellformed card_wellformed by (unfold_locales, blast+)

  interpretation nth_least:
    injection "{i. enat i < esize A}" "A" "nth_least A" "\<lambda> k. card {i \<in> A. i < k}"
    using card_nth_least by (unfold_locales, blast)

  interpretation nth_least:
    surjection "{i. enat i < esize A}" "A" "nth_least A" "\<lambda> k. card {i \<in> A. i < k}"
    for A :: "nat set"
    using nth_least_card by (unfold_locales, blast)

  interpretation nth_least:
    bijection "{i. enat i < esize A}" "A" "nth_least A" "\<lambda> k. card {i \<in> A. i < k}"
    for A :: "nat set"
    by unfold_locales

  lemma nth_least_strict_mono_inverse:
    fixes A :: "nat set"
    assumes "enat k < esize A" "enat l < esize A" "nth_least A k < nth_least A l"
    shows "k < l"
    using assms by (metis not_less_iff_gr_or_eq nth_least_strict_mono)

  lemma nth_least_less_card_less:
    fixes k :: nat
    shows "enat n < esize A \<and> nth_least A n < k \<longleftrightarrow> n < card {i \<in> A. i < k}"
  proof safe
    assume 1: "enat n < esize A" "nth_least A n < k"
    have 2: "nth_least A n \<in> A" using 1(1) by rule
    have "n = card {i \<in> A. i < nth_least A n}" using 1 by simp
    also have "\<dots> < card {i \<in> A. i < k}" using 1(2) 2 by simp
    finally show "n < card {i \<in> A. i < k}" by this
  next
    assume 1: "n < card {i \<in> A. i < k}"
    have "enat n < enat (card {i \<in> A. i < k})" using 1 by simp
    also have "\<dots> = esize {i \<in> A. i < k}" by simp
    also have "\<dots> \<le> esize A" by blast
    finally show 2: "enat n < esize A" by this
    have 3: "n = card {i \<in> A. i < nth_least A n}" using 2 by simp
    have 4: "card {i \<in> A. i < nth_least A n} < card {i \<in> A. i < k}" using 1 2 by simp
    have 5: "nth_least A n \<in> A" using 2 by rule
    show "nth_least A n < k" using 4 5 by simp
  qed

  lemma nth_least_less_esize_less:
    "enat n < esize A \<and> enat (nth_least A n) < k \<longleftrightarrow> enat n < esize {i \<in> A. enat i < k}"
    using nth_least_less_card_less by (cases k, simp+)

  lemma nth_least_le:
    assumes "enat n < esize A"
    shows "n \<le> nth_least A n"
  using assms
  proof (induct n)
    case 0
    show ?case using 0 by simp
  next
    case (Suc n)
    have "n \<le> nth_least A n" using Suc by (metis Suc_ile_eq less_imp_le)
    also have "\<dots> < nth_least A (Suc n)" using nth_least_strict_mono Suc(2) by blast
    finally show ?case by simp
  qed

  lemma nth_least_eq:
    assumes "enat n < esize A" "enat n < esize B"
    assumes "\<And> i. i \<le> nth_least A n \<Longrightarrow> i \<le> nth_least B n \<Longrightarrow> i \<in> A \<longleftrightarrow> i \<in> B"
    shows "nth_least A n = nth_least B n"
  using assms
  proof (induct n arbitrary: A B)
    case 0
    have 1: "least A = least B"
    proof (rule least_eq)
      show "A \<noteq> {}" using 0(1) by simp
      show "B \<noteq> {}" using 0(2) by simp
    next
      fix i
      assume 2: "i \<le> least A" "i \<le> least B"
      show "i \<in> A \<longleftrightarrow> i \<in> B" using 0(3) 2 unfolding nth_least.simps by this
    qed
    show ?case using 1 by simp
  next
    case (Suc n)
    have 1: "A \<noteq> {}" "B \<noteq> {}" using Suc(2, 3) by auto
    have 2: "least A = least B"
    proof (rule least_eq)
      show "A \<noteq> {}" using 1(1) by this
      show "B \<noteq> {}" using 1(2) by this
    next
      fix i
      assume 3: "i \<le> least A" "i \<le> least B"
      have 4: "nth_least A 0 \<le> nth_least A (Suc n)" using Suc(2) by blast
      have 5: "nth_least B 0 \<le> nth_least B (Suc n)" using Suc(3) by blast
      have 6: "i \<le> nth_least A (Suc n)" "i \<le> nth_least B (Suc n)" using 3 4 5 by auto
      show "i \<in> A \<longleftrightarrow> i \<in> B" using Suc(4) 6 by this
    qed
    have 3: "nth_least (A - {least A}) n = nth_least (B - {least B}) n"
    proof (rule Suc(1))
      show "enat n < esize (A - {least A})" using Suc(2) 1(1) by simp
      show "enat n < esize (B - {least B})" using Suc(3) 1(2) by simp
    next
      fix i
      assume 3: "i \<le> nth_least (A - {least A}) n" "i \<le> nth_least (B - {least B}) n"
      have 4: "i \<le> nth_least A (Suc n)" "i \<le> nth_least B (Suc n)" using 3 by simp+
      have 5: "i \<in> A \<longleftrightarrow> i \<in> B" using Suc(4) 4 by this
      show "i \<in> A - {least A} \<longleftrightarrow> i \<in> B - {least B}" using 2 5 by auto
    qed
    show ?case using 3 by simp
  qed

  lemma nth_least_restrict[simp]:
    assumes "enat i < esize {i \<in> s. enat i < k}"
    shows "nth_least {i \<in> s. enat i < k} i = nth_least s i"
  proof (rule nth_least_eq)
    show "enat i < esize {i \<in> s. enat i < k}" using assms by this
    show "enat i < esize s" using nth_least_less_esize_less assms by auto
  next
    fix l
    assume 1: "l \<le> nth_least {i \<in> s. enat i < k} i"
    have 2: "nth_least {i \<in> s. enat i < k} i \<in> {i \<in> s. enat i < k}" using assms by rule
    have "enat l \<le> enat (nth_least {i \<in> s. enat i < k} i)" using 1 by simp
    also have "\<dots> < k" using 2 by simp
    finally show "l \<in> {i \<in> s. enat i < k} \<longleftrightarrow> l \<in> s" by auto
  qed

  lemma least_nth_least[simp]:
    assumes "A \<noteq> {}" "\<And> i. i \<in> A \<Longrightarrow> enat i < esize B"
    shows "least (nth_least B ` A) = nth_least B (least A)"
    using assms by simp

  lemma nth_least_nth_least[simp]:
    assumes "enat n < esize A" "\<And> i. i \<in> A \<Longrightarrow> enat i < esize B"
    shows "nth_least B (nth_least A n) = nth_least (nth_least B ` A) n"
  using assms
  proof (induct n arbitrary: A)
    case 0
    show ?case using 0 by simp
  next
    case (Suc n)
    have 1: "A \<noteq> {}" using Suc(2) by auto
    have 2: "nth_least B ` (A - {least A}) = nth_least B ` A - nth_least B ` {least A}"
    proof (rule inj_on_image_set_diff)
      show "inj_on (nth_least B) {i. enat i < esize B}" using nth_least.inj_on by this
      show "A - {least A} \<subseteq> {i. enat i < esize B}" using Suc(3) by blast
      show "{least A} \<subseteq> {i. enat i < esize B}" using Suc(3) 1 by force
    qed
    have "nth_least B (nth_least A (Suc n)) = nth_least B (nth_least (A - {least A}) n)" by simp
    also have "\<dots> = nth_least (nth_least B ` (A - {least A})) n" using Suc 1 by force
    also have "\<dots> = nth_least (nth_least B ` A - nth_least B ` {least A}) n" unfolding 2 by rule
    also have "\<dots> = nth_least (nth_least B ` A - {nth_least B (least A)}) n" by simp
    also have "\<dots> = nth_least (nth_least B ` A - {least (nth_least B ` A)}) n" using Suc(3) 1 by auto
    also have "\<dots> = nth_least (nth_least B ` A) (Suc n)" by simp
    finally show ?case by this
  qed

  lemma nth_least_Max[simp]:
    assumes "finite A" "A \<noteq> {}"
    shows "nth_least A (card A - 1) = Max A"
  using assms
  proof (induct "card A - 1" arbitrary: A)
    case 0
    have 1: "card A = 1" using 0 by (metis One_nat_def Suc_diff_1 card_gt_0_iff)
    obtain a where 2: "A = {a}" using 1 by rule
    show ?case unfolding 2 by (simp del: insert_iff)
  next
    case (Suc n)
    have 1: "least A \<in> A" using Suc(4) by rule
    have 2: "card (A - {least A}) = Suc n" using Suc(2, 3) 1 by simp
    have 3: "A - {least A} \<noteq> {}" using 2 Suc(3) by fastforce
    have "nth_least A (card A - 1) = nth_least A (Suc n)" unfolding Suc(2) by rule
    also have "\<dots> = nth_least (A - {least A}) n" by simp
    also have "\<dots> = nth_least (A - {least A}) (card (A - {least A}) - 1)" unfolding 2 by simp
    also have "\<dots> = Max (A - {least A})"
    proof (rule Suc(1))
      show "n = card (A - {least A}) - 1" unfolding 2 by simp
      show "finite (A - {least A})" using Suc(3) by simp
      show "A - {least A} \<noteq> {}" using 3 by this
    qed
    also have "\<dots> = Max A" using Suc(3) 3 by simp
    finally show ?case by this
  qed

  lemma nth_least_le_Max:
    assumes "finite A" "A \<noteq> {}" "enat n < esize A"
    shows "nth_least A n \<le> Max A"
  proof -
    have "nth_least A n \<le> nth_least A (card A - 1)"
    proof (rule nth_least_mono)
      show "enat (card A - 1) < esize A" by (metis Suc_diff_1 Suc_ile_eq assms(1) assms(2)
        card_eq_0_iff esize_set.simps(1) not_gr0 order_refl)
      show "n \<le> card A - 1" by (metis Suc_diff_1 Suc_leI antisym_conv assms(1) assms(3)
        enat_ord_simps(2) esize_set.simps(1) le_less neq_iff not_gr0)
    qed
    also have "\<dots> = Max A" using nth_least_Max assms(1, 2) by this
    finally show ?thesis by this
  qed

  lemma nth_least_not_contains:
    fixes k :: nat
    assumes "enat (Suc n) < esize A" "nth_least A n < k" "k < nth_least A (Suc n)"
    shows "k \<notin> A"
  proof
    assume 1: "k \<in> A"
    have 2: "nth_least A (card {i \<in> A. i < k}) = k" using nth_least.right_inverse 1 by this
    have 3: "n < card {i \<in> A. i < k}"
    proof (rule nth_least_strict_mono_inverse)
      show "enat n < esize A" using assms(1) by auto
      show "enat (card {i \<in> A. i < k}) < esize A" using nth_least.g.wellformed 1 by simp
      show "nth_least A n < nth_least A (card {i \<in> A. i < k})" using assms(2) 2 by simp
    qed
    have 4: "card {i \<in> A. i < k} < Suc n"
    proof (rule nth_least_strict_mono_inverse)
      show "enat (card {i \<in> A. i < k}) < esize A" using nth_least.g.wellformed 1 by simp
      show "enat (Suc n) < esize A" using assms(1) by this
      show "nth_least A (card {i \<in> A. i < k}) < nth_least A (Suc n)" using assms(3) 2 by simp
    qed
    show "False" using 3 4 by auto
  qed

  lemma nth_least_Suc[simp]:
    assumes "enat n < esize A"
    shows "nth_least (Suc ` A) n = Suc (nth_least A n)"
  using assms
  proof (induct n arbitrary: A)
    case (0)
    have 1: "A \<noteq> {}" using 0 by auto
    show ?case using 1 by simp
  next
    case (Suc n)
    have 1: "enat n < esize (A - {least A})"
    proof -
      have 2: "A \<noteq> {}" using Suc(2) by auto
      have 3: "least A \<in> A" using LeastI 2 by fast
      have 4: "A = insert (least A) A" using 3 by auto
      have "eSuc (enat n) = enat (Suc n)" by simp
      also have "\<dots> < esize A" using Suc(2) by this
      also have "\<dots> = esize (insert (least A) A)" using 4 by simp
      also have "\<dots> = eSuc (esize (A - {least A}))" using 3 2 by simp
      finally show ?thesis using Extended_Nat.eSuc_mono by metis
    qed
    have "nth_least (Suc ` A) (Suc n) = nth_least (Suc ` A - {least (Suc ` A)}) n" by simp
    also have "\<dots> = nth_least (Suc ` (A - {least A})) n" by simp
    also have "\<dots> = Suc (nth_least (A - {least A}) n)" using Suc(1) 1 by this
    also have "\<dots> = Suc (nth_least A (Suc n))" by simp
    finally show ?case by this
  qed

  lemma nth_least_lift[simp]:
    "nth_least (lift A) 0 = 0"
    "enat n < esize A \<Longrightarrow> nth_least (lift A) (Suc n) = Suc (nth_least A n)"
    unfolding lift_def by simp+

  lemma nth_least_list_card[simp]:
    assumes "enat n \<le> esize A"
    shows "card {k \<in> A. k < nth_least (lift A) n} = n"
    using less_Suc_eq_le assms by (cases n, auto simp del: nth_least.simps)

end