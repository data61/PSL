section \<open>Sets\<close>

theory Set_Extensions
imports
  "HOL-Library.Infinite_Set"
begin

  declare finite_subset[intro]

  lemma set_not_emptyI[intro 0]: "x \<in> S \<Longrightarrow> S \<noteq> {}" by auto
  lemma sets_empty_iffI[intro 0]:
    assumes "\<And> a. a \<in> A \<Longrightarrow> \<exists> b. b \<in> B"
    assumes "\<And> b. b \<in> B \<Longrightarrow> \<exists> a. a \<in> A"
    shows "A = {} \<longleftrightarrow> B = {}"
    using assms by auto
  lemma disjointI[intro 0]:
    assumes "\<And> x. x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> False"
    shows "A \<inter> B = {}"
    using assms by auto
  lemma range_subsetI[intro 0]:
    assumes "\<And> x. f x \<in> S"
    shows "range f \<subseteq> S"
    using assms by blast

  lemma finite_imageI_range:
    assumes "finite (range f)"
    shows "finite (f ` A)"
    using finite_subset image_mono subset_UNIV assms by metis

  lemma inf_img_fin_domE':
    assumes "infinite A"
    assumes "finite (f ` A)"
    obtains y
    where "y \<in> f ` A" "infinite (A \<inter> f -` {y})"
  proof (rule ccontr)
    assume 1: "\<not> thesis"
    have 2: "finite (\<Union> y \<in> f ` A. A \<inter> f -` {y})"
    proof (rule finite_UN_I)
      show "finite (f ` A)" using assms(2) by this
      show "\<And> y. y \<in> f ` A \<Longrightarrow> finite (A \<inter> f -` {y})" using that 1 by blast
    qed
    have 3: "A \<subseteq> (\<Union> y \<in> f ` A. A \<inter> f -` {y})" by blast
    show False using assms(1) 2 3 by blast
  qed

  lemma vimage_singleton[simp]: "f -` {y} = {x. f x = y}" unfolding vimage_def by simp

  lemma these_alt_def: "Option.these S = Some -` S" unfolding Option.these_def by force
  lemma the_vimage_subset: "the -` {a} \<subseteq> {None, Some a}" by auto

  lemma finite_induct_reverse[consumes 1, case_names remove]:
    assumes "finite S"
    assumes "\<And> S. finite S \<Longrightarrow> (\<And> x. x \<in> S \<Longrightarrow> P (S - {x})) \<Longrightarrow> P S"
    shows "P S"
  using assms(1)
  proof (induct rule: finite_psubset_induct)
    case (psubset S)
    show ?case
    proof (rule assms(2))
      show "finite S" using psubset(1) by this
    next
      fix x
      assume 0: "x \<in> S"
      show "P (S - {x})"
      proof (rule psubset(2))
        show "S - {x} \<subset> S" using 0 by auto
      qed
    qed
  qed

  lemma zero_not_in_Suc_image[simp]: "0 \<notin> Suc ` A" by auto

  lemma Collect_split_Suc:
    "\<not> P 0 \<Longrightarrow> {i. P i} = Suc ` {i. P (Suc i)}"
    "P 0 \<Longrightarrow> {i. P i} = {0} \<union> Suc ` {i. P (Suc i)}"
  proof -
    assume "\<not> P 0"
    thus "{i. P i} = Suc ` {i. P (Suc i)}"
      by (auto, metis image_eqI mem_Collect_eq nat.exhaust)
  next
    assume "P 0"
    thus "{i. P i} = {0} \<union> Suc ` {i. P (Suc i)}"
      by (auto, metis imageI mem_Collect_eq not0_implies_Suc)
  qed

  lemma Collect_subsume[simp]:
    assumes "\<And> x. x \<in> A \<Longrightarrow> P x"
    shows "{x \<in> A. P x} = A"
    using assms unfolding simp_implies_def by auto

  lemma Max_ge':
    assumes "finite A" "A \<noteq> {}"
    assumes "b \<in> A" "a \<le> b"
    shows "a \<le> Max A"
    using assms Max_ge_iff by auto

  abbreviation "least A \<equiv> LEAST k. k \<in> A"

  lemma least_contains[intro?, simp]:
    fixes A :: "'a :: wellorder set"
    assumes "k \<in> A"
    shows "least A \<in> A"
    using assms by (metis LeastI)
  lemma least_contains'[intro?, simp]:
    fixes A :: "'a :: wellorder set"
    assumes "A \<noteq> {}"
    shows "least A \<in> A"
    using assms by (metis LeastI equals0I)
  lemma least_least[intro?, simp]:
    fixes A :: "'a :: wellorder set"
    assumes "k \<in> A"
    shows "least A \<le> k"
    using assms by (metis Least_le)
  lemma least_unique:
    fixes A :: "'a :: wellorder set"
    assumes "k \<in> A" "k \<le> least A"
    shows "k = least A"
    using assms by (metis Least_le antisym)
  lemma least_not_less:
    fixes A :: "'a :: wellorder set"
    assumes "k < least A"
    shows "k \<notin> A"
    using assms by (metis not_less_Least)
  lemma leastI2_order[simp]:
    fixes A :: "'a :: wellorder set"
    assumes "A \<noteq> {}" "\<And> k. k \<in> A \<Longrightarrow> (\<And> l. l \<in> A \<Longrightarrow> k \<le> l) \<Longrightarrow> P k"
    shows "P (least A)"
  proof (rule LeastI2_order)
    show "least A \<in> A" using assms(1) by rule
  next
    fix k
    assume 1: "k \<in> A"
    show "least A \<le> k" using 1 by rule
  next
    fix k
    assume 1: "k \<in> A" "\<forall> l. l \<in> A \<longrightarrow> k \<le> l"
    show "P k" using assms(2) 1 by auto
  qed

  lemma least_singleton[simp]:
    fixes a :: "'a :: wellorder"
    shows "least {a} = a"
    by (metis insert_not_empty least_contains' singletonD)

  lemma least_image[simp]:
    fixes f :: "'a :: wellorder \<Rightarrow> 'b :: wellorder"
    assumes "A \<noteq> {}" "\<And> k l. k \<in> A \<Longrightarrow> l \<in> A \<Longrightarrow> k \<le> l \<Longrightarrow> f k \<le> f l"
    shows "least (f ` A) = f (least A)"
  proof (rule leastI2_order)
    show "A \<noteq> {}" using assms(1) by this
  next
    fix k
    assume 1: "k \<in> A" "\<And> i. i \<in> A \<Longrightarrow> k \<le> i"
    show "least (f ` A) = f k"
    proof (rule leastI2_order)
      show "f ` A \<noteq> {}" using assms(1) by simp
    next
      fix l
      assume 2: "l \<in> f ` A" "\<And> i. i \<in> f ` A \<Longrightarrow> l \<le> i"
      show "l = f k" using assms(2) 1 2 by force
    qed
  qed

  lemma least_le:
    fixes A B :: "'a :: wellorder set"
    assumes "B \<noteq> {}"
    assumes "\<And> i. i \<le> least A \<Longrightarrow> i \<le> least B \<Longrightarrow> i \<in> B \<Longrightarrow> i \<in> A"
    shows "least A \<le> least B"
  proof (rule ccontr)
    assume 1: "\<not> least A \<le> least B"
    have 2: "least B \<in> A" using assms(1, 2) 1 by simp
    have 3: "least A \<le> least B" using 2 by rule
    show False using 1 3 by rule
  qed
  lemma least_eq:
    fixes A B :: "'a :: wellorder set"
    assumes "A \<noteq> {}" "B \<noteq> {}"
    assumes "\<And> i. i \<le> least A \<Longrightarrow> i \<le> least B \<Longrightarrow> i \<in> A \<longleftrightarrow> i \<in> B"
    shows "least A = least B"
    using assms by (auto intro: antisym least_le)

  lemma least_Suc[simp]:
    assumes "A \<noteq> {}"
    shows "least (Suc ` A) = Suc (least A)"
  proof (rule antisym)
    obtain k where 10: "k \<in> A" using assms by blast
    have 11: "Suc k \<in> Suc ` A" using 10 by auto
    have 20: "least A \<in> A" using 10 LeastI by metis
    have 21: "least (Suc ` A) \<in> Suc ` A" using 11 LeastI by metis
    have 30: "\<And> l. l \<in> A \<Longrightarrow> least A \<le> l" using 10 Least_le by metis
    have 31: "\<And> l. l \<in> Suc ` A \<Longrightarrow> least (Suc ` A) \<le> l" using 11 Least_le by metis
    show "least (Suc ` A) \<le> Suc (least A)" using 20 31 by auto
    show "Suc (least A) \<le> least (Suc ` A)" using 21 30 by auto
  qed

  lemma least_Suc_diff[simp]: "Suc ` A - {least (Suc ` A)} = Suc ` (A - {least A})"
  proof (cases "A = {}")
    case True
    show ?thesis unfolding True by simp
  next
    case False
    have "Suc ` A - {least (Suc ` A)} = Suc ` A - {Suc (least A)}" using False by simp
    also have "\<dots> = Suc ` A - Suc ` {least A}" by simp
    also have "\<dots> = Suc ` (A - {least A})" by blast
    finally show ?thesis by this
  qed

  lemma Max_diff_least[simp]:
    fixes A :: "'a :: wellorder set"
    assumes "finite A" "A - {least A} \<noteq> {}"
    shows "Max (A - {least A}) = Max A"
  proof -
    have 1: "least A \<in> A" using assms(2) by auto
    obtain a where 2: "a \<in> A - {least A}" using assms(2) by blast
    have "Max A = Max (insert (least A) (A - {least A}))" using insert_absorb 1 by force
    also have "\<dots> = max (least A) (Max (A - {least A}))"
    proof (rule Max_insert)
      show "finite (A - {least A})" using assms(1) by auto
      show "A - {least A} \<noteq> {}" using assms(2) by this
    qed
    also have "\<dots> = Max (A - {least A})"
    proof (rule max_absorb2, rule Max_ge')
      show "finite (A - {least A})" using assms(1) by auto
      show "A - {least A} \<noteq> {}" using assms(2) by this
      show "a \<in> A - {least A}" using 2 by this
      show "least A \<le> a" using 2 by simp
    qed
    finally show ?thesis by rule
  qed

  lemma nat_set_card_equality_less:
    fixes A :: "nat set"
    assumes "x \<in> A" "y \<in> A" "card {z \<in> A. z < x} = card {z \<in> A. z < y}"
    shows "x = y"
  proof (cases x y rule: linorder_cases)
    case less
    have 0: "finite {z \<in> A. z < y}" by simp
    have 1: "{z \<in> A. z < x} \<subset> {z \<in> A. z < y}" using assms(1, 2) less by force
    have 2: "card {z \<in> A. z < x} < card {z \<in> A. z < y}" using psubset_card_mono 0 1 by this
    show ?thesis using assms(3) 2 by simp
  next
    case equal
    show ?thesis using equal by this
  next
    case greater
    have 0: "finite {z \<in> A. z < x}" by simp
    have 1: "{z \<in> A. z < y} \<subset> {z \<in> A. z < x}" using assms(1, 2) greater by force
    have 2: "card {z \<in> A. z < y} < card {z \<in> A. z < x}" using psubset_card_mono 0 1 by this
    show ?thesis using assms(3) 2 by simp
  qed

  lemma nat_set_card_equality_le:
    fixes A :: "nat set"
    assumes "x \<in> A" "y \<in> A" "card {z \<in> A. z \<le> x} = card {z \<in> A. z \<le> y}"
    shows "x = y"
  proof (cases x y rule: linorder_cases)
    case less
    have 0: "finite {z \<in> A. z \<le> y}" by simp
    have 1: "{z \<in> A. z \<le> x} \<subset> {z \<in> A. z \<le> y}" using assms(1, 2) less by force
    have 2: "card {z \<in> A. z \<le> x} < card {z \<in> A. z \<le> y}" using psubset_card_mono 0 1 by this
    show ?thesis using assms(3) 2 by simp
  next
    case equal
    show ?thesis using equal by this
  next
    case greater
    have 0: "finite {z \<in> A. z \<le> x}" by simp
    have 1: "{z \<in> A. z \<le> y} \<subset> {z \<in> A. z \<le> x}" using assms(1, 2) greater by force
    have 2: "card {z \<in> A. z \<le> y} < card {z \<in> A. z \<le> x}" using psubset_card_mono 0 1 by this
    show ?thesis using assms(3) 2 by simp
  qed

  lemma nat_set_card_mono[simp]:
    fixes A :: "nat set"
    assumes "x \<in> A"
    shows "card {z \<in> A. z < x} < card {z \<in> A. z < y} \<longleftrightarrow> x < y"
  proof
    assume 1: "card {z \<in> A. z < x} < card {z \<in> A. z < y}"
    show "x < y"
    proof (rule ccontr)
      assume 2: "\<not> x < y"
      have 3: "card {z \<in> A. z < y} \<le> card {z \<in> A. z < x}" using 2 by (auto intro: card_mono)
      show "False" using 1 3 by simp
    qed
  next
    assume 1: "x < y"
    show "card {z \<in> A. z < x} < card {z \<in> A. z < y}"
    proof (intro psubset_card_mono psubsetI)
      show "finite {z \<in> A. z < y}" by simp
      show "{z \<in> A. z < x} \<subseteq> {z \<in> A. z < y}" using 1 by auto
      show "{z \<in> A. z < x} \<noteq> {z \<in> A. z < y}" using assms 1 by blast
    qed
  qed

  lemma card_one[elim]:
    assumes "card A = 1"
    obtains a
    where "A = {a}"
    using assms by (metis One_nat_def card_Suc_eq)

  lemma image_alt_def: "f ` A = {f x |x. x \<in> A}" by auto

  lemma supset_mono_inductive[mono]:
    assumes "\<And> x. x \<in> B \<longrightarrow> x \<in> C"
    shows "A \<subseteq> B \<longrightarrow> A \<subseteq> C"
    using assms by auto
  lemma Collect_mono_inductive[mono]:
    assumes "\<And> x. P x \<longrightarrow> Q x"
    shows "x \<in> {x. P x} \<longrightarrow> x \<in> {x. Q x}"
    using assms by auto

  lemma image_union_split:
    assumes "f ` (A \<union> B) = g ` C"
    obtains D E
    where "f ` A = g ` D" "f ` B = g ` E" "D \<subseteq> C" "E \<subseteq> C"
    using assms unfolding image_Un
    by (metis (erased, lifting) inf_sup_ord(3) inf_sup_ord(4) subset_imageE)
  lemma image_insert_split:
    assumes "inj g" "f ` insert a B = g ` C"
    obtains d E
    where "f a = g d" "f ` B = g ` E" "d \<in> C" "E \<subseteq> C"
  proof -
    have 1: "f ` ({a} \<union> B) = g ` C" using assms(2) by simp
    obtain D E where 2: "f ` {a} = g ` D" "f ` B = g ` E" "D \<subseteq> C" "E \<subseteq> C"
      using image_union_split 1 by this
    obtain d where 3: "D = {d}" using assms(1) 2(1) by (auto, metis (erased, hide_lams) imageE
      image_empty image_insert inj_image_eq_iff singletonI)
    show ?thesis using that 2 unfolding 3 by simp
  qed

end