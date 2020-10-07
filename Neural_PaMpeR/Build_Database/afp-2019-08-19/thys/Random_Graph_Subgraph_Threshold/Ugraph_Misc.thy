section\<open>Miscellaneous and contributed lemmas\<close>

theory Ugraph_Misc
imports
  "HOL-Probability.Probability"
  Girth_Chromatic.Girth_Chromatic_Misc
begin

lemma sum_square:
  fixes a :: "'i \<Rightarrow> 'a :: {monoid_mult, semiring_0}"
  shows "(\<Sum>i \<in> I. a i)^2 = (\<Sum>i \<in> I. \<Sum>j \<in> I. a i * a j)"
  by (simp only: sum_product power2_eq_square)

lemma sum_split:
  "finite I \<Longrightarrow>
  (\<Sum>i \<in> I. if p i then f i else g i) = (\<Sum>i | i \<in> I \<and> p i. f i) + (\<Sum>i | i \<in> I \<and> \<not>p i. g i)"
  by (simp add: sum.If_cases Int_def)

lemma sum_split2:
  assumes "finite I"
  shows "(\<Sum>i | i \<in> I \<and> P i. if Q i then f i else g i) = (\<Sum>i | i \<in> I \<and> P i \<and> Q i. f i) + (\<Sum>i | i \<in> I \<and> P i \<and> \<not>Q i. g i)"
proof (subst sum.If_cases)
  show "finite {i \<in> I. P i}"
    using assms by simp

  have "{i \<in> I. P i} \<inter> Collect Q = {i \<in> I. P i \<and> Q i}" "{i \<in> I. P i} \<inter> - Collect Q =  {i \<in> I. P i \<and> \<not> Q i}"
    by auto
  thus "sum f ({i \<in> I. P i} \<inter> Collect Q) + sum g ({i \<in> I. P i} \<inter> - Collect Q) = sum f {i \<in> I. P i \<and> Q i} + sum g {i \<in> I. P i \<and> \<not> Q i}"
    by presburger
qed

lemma sum_upper:
  fixes f :: "'i \<Rightarrow> 'a :: ordered_comm_monoid_add"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
  shows "(\<Sum>i | i \<in> I \<and> P i. f i) \<le> sum f I"
proof -
  have "sum f I = (\<Sum>i \<in> I. if P i then f i else f i)"
    by simp
  hence "sum f I = (\<Sum>i | i \<in> I \<and> P i. f i) + (\<Sum>i | i \<in> I \<and> \<not>P i. f i)"
    by (simp only: sum_split[OF \<open>finite I\<close>])
  moreover have "0 \<le> (\<Sum>i | i \<in> I \<and> \<not>P i. f i)"
    by (rule sum_nonneg) (simp add: assms)
  ultimately show ?thesis
    by (metis (full_types) add.comm_neutral add_left_mono)
qed

lemma sum_lower:
  fixes f :: "'i \<Rightarrow> 'a :: ordered_comm_monoid_add"
  assumes "finite I" "i \<in> I" "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i" "x < f i"
  shows "x < sum f I"
proof -
  have "x < f i" by fact
  also have "\<dots> \<le> sum f I"
    using sum_mono2[OF \<open>finite I\<close>, of "{i}" f] assms by auto
  finally show ?thesis .
qed

lemma sum_lower_or_eq:
  fixes f :: "'i \<Rightarrow> 'a :: ordered_comm_monoid_add"
  assumes "finite I" "i \<in> I" "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i" "x \<le> f i"
  shows "x \<le> sum f I"
proof -
  have "x \<le> f i" by fact
  also have "\<dots> \<le> sum f I"
    using sum_mono2[OF \<open>finite I\<close>, of "{i}" f] assms by auto
  finally show ?thesis .
qed

lemma sum_left_div_distrib:
  fixes f :: "'i \<Rightarrow> real"
  shows "(\<Sum>i \<in> I. f i / x) = sum f I / x"
proof -
  have "(\<Sum>i \<in> I. f i / x) = (\<Sum>i \<in> I. f i * (1 / x))"
    by simp
  also have "\<dots> = sum f I * (1 / x)"
    by (rule sum_distrib_right[symmetric])
  also have "\<dots> = sum f I / x"
    by simp
  finally show ?thesis
    .
qed

lemma powr_mono3:
  fixes x::real
  assumes "0 < x" "x < 1" "b \<le> a"
  shows "x powr a \<le> x powr b"
proof -
  have "x powr a = 1 / x powr -a"
    by (simp add: powr_minus_divide)
  also have "\<dots> = (1 / x) powr -a"
    using assms by (simp add: powr_divide)
  also have "\<dots> \<le> (1 / x) powr -b"
    using assms by (simp add: powr_mono)
  also have "\<dots> = 1 / x powr -b"
    using assms by (simp add: powr_divide)
  also have "\<dots> = x powr b"
    by (simp add: powr_minus_divide)
  finally show ?thesis
    .
qed

lemma card_union: "finite A \<Longrightarrow> finite B \<Longrightarrow> card (A \<union> B) = card A + card B - card (A \<inter> B)"
by (metis card_Un_Int[symmetric] diff_add_inverse2)

lemma card_1_element:
  assumes "card E = 1"
  shows "\<exists>a. E = {a}"
proof -
  from assms obtain a where "a \<in> E"
    by force
  let ?E' = "E - {a}"

  have "finite ?E'"
    using assms card_ge_0_finite by force
  hence "card (insert a ?E') = 1 + card ?E'"
    using card_insert by fastforce
  moreover have "E = insert a ?E'"
    using \<open>a \<in> E\<close> by blast
  ultimately have "card E = 1 + card ?E'"
    by simp
  hence "card ?E' = 0"
    using assms by simp
  hence "?E' = {}"
    using \<open>finite ?E'\<close> by simp
  thus ?thesis
    using \<open>a \<in> E\<close> by blast
qed

lemma card_2_elements:
  assumes "card E = 2"
  shows "\<exists>a b. E = {a, b} \<and> a \<noteq> b"
proof -
  from assms obtain a where "a \<in> E"
    by force
  let ?E' = "E - {a}"

  have "finite ?E'"
    using assms card_ge_0_finite by force
  hence "card (insert a ?E') = 1 + card ?E'"
    using card_insert by fastforce
  moreover have "E = insert a ?E'"
    using \<open>a \<in> E\<close> by blast
  ultimately have "card E = 1 + card ?E'"
    by simp
  hence "card ?E' = 1"
    using assms by simp
  then obtain b where "?E' = {b}"
    using card_1_element by blast
  hence "E = {a, b}"
    using \<open>a \<in> E\<close> by blast
  moreover have "a \<noteq> b"
    using \<open>?E' = {b}\<close> by blast
  ultimately show ?thesis
    by blast
qed

lemma bij_lift:
  assumes "bij_betw f A B"
  shows "bij_betw (\<lambda>e. f ` e) (Pow A) (Pow B)"
proof -
  have f: "inj_on f A" "f ` A = B"
    using assms unfolding bij_betw_def by simp_all
  have "inj_on (\<lambda>e. f ` e) (Pow A)"
    unfolding inj_on_def by clarify (metis f(1) inv_into_image_cancel)
  moreover have "(\<lambda>e. f ` e) ` (Pow A) = (Pow B)"
    by (metis f(2) image_Pow_surj)
  ultimately show ?thesis
    unfolding bij_betw_def by simp
qed

lemma card_inj_subs: "inj_on f A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> card (f ` B) = card B"
by (metis card_image subset_inj_on)

lemma image_comp_cong: "(\<And>a. a \<in> A \<Longrightarrow> f a = f (g a)) \<Longrightarrow> f ` A = f ` (g ` A)"
by (auto simp: image_iff)

abbreviation less_fun :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> bool" (infix "\<lless>" 50) where
"f \<lless> g \<equiv> (\<lambda>n. f n / g n) \<longlonglongrightarrow> 0"

context
  fixes f :: "nat \<Rightarrow> real"
begin

  lemma LIMSEQ_power_zero: "f \<longlonglongrightarrow> 0 \<Longrightarrow> 0 < n  \<Longrightarrow> (\<lambda>x. f x ^ n :: real) \<longlonglongrightarrow> 0"
  by (metis power_eq_0_iff tendsto_power)

  lemma LIMSEQ_cong:
    assumes "f \<longlonglongrightarrow> x" "\<forall>\<^sup>\<infinity>n. f n = g n"
    shows "g \<longlonglongrightarrow> x"
  by (rule real_tendsto_sandwich[where f = f and h = f, OF eventually_mono[OF assms(2)] eventually_mono[OF assms(2)]]) (auto simp: assms(1))
  print_statement Lim_transform_eventually


  lemma LIMSEQ_le_zero:
    assumes "g \<longlonglongrightarrow> 0" "\<forall>\<^sup>\<infinity>n. 0 \<le> f n" "\<forall>\<^sup>\<infinity>n. f n \<le> g n"
    shows "f \<longlonglongrightarrow> 0"
  by (rule real_tendsto_sandwich[OF assms(2) assms(3) tendsto_const assms(1)])

  lemma LIMSEQ_const_mult:
    assumes "f \<longlonglongrightarrow> a"
    shows "(\<lambda>x. c * f x) \<longlonglongrightarrow> c * a"
  by (rule tendsto_mult[OF tendsto_const[where k = c] assms])

  lemma LIMSEQ_const_div:
    assumes "f \<longlonglongrightarrow> a" "c \<noteq> 0"
    shows "(\<lambda>x. f x / c) \<longlonglongrightarrow> a / c"
  using LIMSEQ_const_mult[where c = "1/c"] assms by simp

end

lemma quot_bounds:
  fixes x :: "'a :: linordered_field"
  assumes "x \<le> x'" "y' \<le> y" "0 < y" "0 \<le> x" "0 < y'"
  shows "x / y \<le> x' / y'"
proof (rule order_trans)
  have "0 \<le> y"
    using assms by simp
  thus "x / y \<le> x' / y"
    using assms by (simp add: divide_right_mono)
next
  have "0 \<le> x'"
    using assms by simp
  moreover have "0 < y * y'"
    using assms by simp
  ultimately show "x' / y \<le> x' / y'"
    using assms by (simp add: divide_left_mono)
qed

lemma less_fun_bounds:
  assumes "f' \<lless> g'" "\<forall>\<^sup>\<infinity>n. f n \<le> f' n" "\<forall>\<^sup>\<infinity>n. g' n \<le> g n" "\<forall>\<^sup>\<infinity>n. 0 \<le> f n" "\<forall>\<^sup>\<infinity>n. 0 < g n" "\<forall>\<^sup>\<infinity>n. 0 < g' n"
  shows "f \<lless> g"
proof (rule real_tendsto_sandwich)
  show "\<forall>\<^sup>\<infinity>n. 0 \<le> f n / g n"
    using assms(4,5) by eventually_elim simp
next
  show "\<forall>\<^sup>\<infinity>n. f n / g n \<le> f' n / g' n"
    using assms(2-) by eventually_elim (simp only: quot_bounds)
qed (auto intro: assms(1))

lemma less_fun_const_quot:
  assumes "f \<lless> g" "c \<noteq> 0"
  shows "(\<lambda>n. b * f n) \<lless> (\<lambda>n. c * g n)"
proof -
  have "(\<lambda>n. (b * (f n / g n)) / c) \<longlonglongrightarrow> (b * 0) / c"
    using assms by (rule LIMSEQ_const_div[OF LIMSEQ_const_mult])
  hence "(\<lambda>n. (b * (f n / g n)) / c) \<longlonglongrightarrow> 0"
    by simp
  with eventually_sequentiallyI show ?thesis
    by (rule Lim_transform_eventually) simp

qed

lemma partition_set_of_intersecting_sets_by_card:
  assumes "finite A"
  shows "{B. A \<inter> B \<noteq> {}} = (\<Union>n \<in> {1..card A}. {B. card (A \<inter> B) = n})"
proof (rule set_eqI, rule iffI)
  fix B
  assume "B \<in> {B. A \<inter> B \<noteq> {}}"
  hence "0 < card (A \<inter> B)"
    using assms by auto
  moreover have "card (A \<inter> B) \<le> card A"
    using assms by (simp add: card_mono)
  ultimately have "card (A \<inter> B) \<in> {1..card A}"
    by simp
  thus "B \<in> (\<Union>n \<in> {1..card A}. {B. card (A \<inter> B) = n})"
    by blast
qed force

lemma card_set_of_intersecting_sets_by_card:
  assumes "A \<subseteq> I" "finite I" "k \<le> n" "n \<le> card I" "k \<le> card A"
  shows "card {B. B \<subseteq> I \<and> card B = n \<and> card (A \<inter> B) = k} = (card A choose k) * ((card I - card A) choose (n - k))"
proof -
  note finite_A = finite_subset[OF assms(1,2)]

  have "card {B. B \<subseteq> I \<and> card B = n \<and> card (A \<inter> B) = k} = card ({K. K \<subseteq> A \<and> card K = k} \<times> {B'. B' \<subseteq> I - A \<and> card B' = n - k})" (is "card ?lhs = card ?rhs")
    proof (rule bij_betw_same_card[symmetric])
      let ?f = "\<lambda>(K, B'). K \<union> B'"
      have "inj_on ?f ?rhs"
        by (blast intro: inj_onI)
      moreover have "?f ` ?rhs = ?lhs"
        proof (rule set_eqI, rule iffI)
          fix B
          assume "B \<in> ?f ` ?rhs"
          then obtain K B' where K: "K \<subseteq> A" "card K = k" "B' \<subseteq> I - A" "card B' = n - k" "K \<union> B' = B"
            by blast
          show "B \<in> ?lhs"
            proof safe
              fix x assume "x \<in> B" thus "x \<in> I"
                using K \<open>A \<subseteq> I\<close> by blast
            next
              have "card B = card K + card B' - card (K \<inter> B')"
                using K assms by (metis card_union finite_A finite_subset finite_Diff)
              moreover have "K \<inter> B' = {}"
                using K assms by blast
              ultimately show "card B = n"
                using K assms by simp
            next
              have "A \<inter> B = K"
                using K assms(1) by blast
              thus "card (A \<inter> B) = k"
                using K by simp
            qed
        next
          fix B
          assume "B \<in> ?lhs"
          hence B: "B \<subseteq> I" "card B = n" "card (A \<inter> B) = k"
            by auto
          let ?K = "A \<inter> B"
          let ?B' = "B - A"
          have "?K \<subseteq> A" "card ?K = k" "?B' \<subseteq> I - A"
            using B by auto
          moreover have "card ?B' = n - k"
            using B finite_A assms(1) by (metis Int_commute card_Diff_subset_Int finite_Un inf.left_idem le_iff_inf sup_absorb2)
          ultimately have "(?K, ?B') \<in> ?rhs"
            by blast
          moreover have "B = ?f (?K, ?B')"
            by auto
          ultimately show "B \<in> ?f ` ?rhs"
            by blast
        qed
      ultimately show "bij_betw ?f ?rhs ?lhs"
        unfolding bij_betw_def ..
    qed
  also have "\<dots> = (\<Sum>K | K \<subseteq> A \<and> card K = k. card {B'. B' \<subseteq> I - A \<and> card B' = n - k})"
    proof (rule card_SigmaI, safe)
      show "finite {K. K \<subseteq> A \<and> card K = k}"
        by (blast intro: finite_subset[where B = "Pow A"] finite_A)
    next
      fix K
      assume "K \<subseteq> A"
      thus "finite {B'. B' \<subseteq> I - A \<and> card B' = n - card K}"
        using assms by auto
    qed
  also have "\<dots> = card {K. K \<subseteq> A \<and> card K = k} * card {B'. B' \<subseteq> I - A \<and> card B' = n - k}"
    by simp
  also have "\<dots> = (card A choose k) * (card (I - A) choose (n - k))"
    by (simp only: n_subsets[OF finite_A] n_subsets[OF finite_Diff[OF assms(2)]])
  also have "\<dots> = (card A choose k) * ((card I - card A) choose (n - k))"
    by (simp only: card_Diff_subset[OF finite_A assms(1)])
  finally show ?thesis
    .
qed

lemma card_dep_pair_set:
  assumes "finite A" "\<And>a. a \<subseteq> A \<Longrightarrow> finite (f a)"
  shows "card {(a, b). a \<subseteq> A \<and> card a = n \<and> b \<subseteq> f a \<and> card b = g a} = (\<Sum>a | a \<subseteq> A \<and> card a = n. card (f a) choose g a)" (is "card ?S = ?C")
proof -
  have S: "?S = Sigma {a. a \<subseteq> A \<and> card a = n} (\<lambda>a. {b. b \<subseteq> f a \<and> card b = g a})" (is "_ = Sigma ?A ?B")
    by auto

  have "card (Sigma ?A ?B) = (\<Sum>a \<in> {a. a \<subseteq> A \<and> card a = n}. card (?B a))"
    proof (rule card_SigmaI, safe)
      show "finite ?A"
        by (rule finite_subset[OF _ finite_Collect_subsets[OF assms(1)]]) blast
    next
      fix a
      assume "a \<subseteq> A"
      hence "finite (f a)"
        by (fact assms(2))
      thus "finite (?B a)"
        by (rule finite_subset[rotated, OF finite_Collect_subsets]) blast
    qed
  also have "\<dots> = ?C"
    proof (rule sum.cong)
      fix a
      assume "a \<in> {a. a \<subseteq> A \<and> card a = n}"
      hence "finite (f a)"
        using assms(2) by blast
      thus "card (?B a) = card (f a) choose g a"
        by (fact n_subsets)
    qed simp
  finally have "card (Sigma ?A ?B) = ?C"
    .

  thus ?thesis
    by (subst S)
qed

lemma prod_cancel_nat:
  \<comment> \<open>Contributed by Manuel Eberl\<close>
  fixes f::"'a \<Rightarrow> nat"
  assumes "B \<subseteq> A" and "finite A" and "\<forall>x\<in>B. f x \<noteq> 0"
  shows "prod f A / prod f B = prod f (A - B)" (is "?A / ?B = ?C")
proof-
  from prod.subset_diff[OF assms(1,2)] have "?A = ?C * ?B" by auto
  moreover have "?B \<noteq> 0" using assms by (simp add: finite_subset)
  ultimately show ?thesis by simp
qed

lemma prod_id_cancel_nat:
  \<comment> \<open>Contributed by Manuel Eberl\<close>
  fixes A::"nat set"
  assumes "B \<subseteq> A" and "finite A" and "0 \<notin> B"
  shows "\<Prod>A / \<Prod>B = \<Prod>(A-B)"
  using assms(1-2) by (rule prod_cancel_nat) (metis assms(3))

lemma (in prob_space) integrable_squareD:
  \<comment> \<open>Contributed by Johannes Hölzl\<close>
  fixes X :: "_ \<Rightarrow> real"
  assumes "integrable M (\<lambda>x. (X x)^2)" "X \<in> borel_measurable M"
  shows "integrable M X"
proof -
  have "integrable M (\<lambda>x. max 1 ((X x)^2))"
    using assms by auto
  then show "integrable M X"
  proof (rule Bochner_Integration.integrable_bound[OF _ _ always_eventually[OF allI]])
    fix x show "norm (X x) \<le> norm (max 1 ((X x)^2))"
      using abs_le_square_iff[of 1 "X x"] power_increasing[of 1 2 "abs (X x)"]
      by (auto split: split_max)
  qed fact
qed

end
