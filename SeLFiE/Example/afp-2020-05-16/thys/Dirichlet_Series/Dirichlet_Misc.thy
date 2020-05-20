(*
    File:      Dirichlet_Misc.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Miscellaneous auxiliary facts\<close>
theory Dirichlet_Misc
  imports 
    Main 
    "HOL-Number_Theory.Number_Theory"
begin

lemma
  fixes a k :: nat
  assumes "a > 1" "k > 0"
  shows geometric_sum_nat_aux: "(a - 1) * (\<Sum>i<k. a ^ i) = a ^ k - 1"
    and geometric_sum_nat_dvd: "a - 1 dvd a ^ k - 1"
    and geometric_sum_nat:     "(\<Sum>i<k. a ^ i) = (a ^ k - 1) div (a - 1)"
proof -
  have "(real a - 1) * (\<Sum>i<k. real a ^ i) = real a ^ k - 1"
    using assms by (subst geometric_sum) auto
  also have "(real a - 1) * (\<Sum>i<k. real a ^ i) = real ((a - 1) * (\<Sum>i<k. a ^ i))" 
    using assms by (simp add: of_nat_diff)
  also have "real a ^ k - 1 = real (a ^ k - 1)" using assms by (subst of_nat_diff) auto
  finally show *: "(a - 1) * (\<Sum>i<k. a ^ i) = a ^ k - 1" by (subst (asm) of_nat_eq_iff)
  show "a - 1 dvd a ^ k - 1" by (subst * [symmetric]) simp
  from assms show "(\<Sum>i<k. a ^ i) = (a ^ k - 1) div (a - 1)" 
    by (subst * [symmetric]) simp
qed

lemma dvd_div_gt0: "d dvd n \<Longrightarrow> n > 0 \<Longrightarrow> n div d > (0::nat)"
  by (auto elim: dvdE)

lemma Set_filter_insert: 
  "Set.filter P (insert x A) = (if P x then insert x (Set.filter P A) else Set.filter P A)"
  by (auto simp: Set.filter_def)
    
lemma Set_filter_union: "Set.filter P (A \<union> B) = Set.filter P A \<union> Set.filter P B"
  by (auto simp: Set.filter_def)

lemma Set_filter_empty [simp]: "Set.filter P {} = {}"
  by (auto simp: Set.filter_def)
    
lemma Set_filter_image: "Set.filter P (f ` A) = f ` Set.filter (P \<circ> f) A"
  by (auto simp: Set.filter_def)

lemma Set_filter_cong [cong]:
    "(\<And>x. x \<in> A \<Longrightarrow> P x \<longleftrightarrow> Q x) \<Longrightarrow> A = B \<Longrightarrow>  Set.filter P A = Set.filter Q B"
  by (auto simp: Set.filter_def)
    
lemma finite_Set_filter: "finite A \<Longrightarrow> finite (Set.filter P A)"
  by (auto simp: Set.filter_def)

lemma inj_on_insert': "(\<And>B. B \<in> A \<Longrightarrow> x \<notin> B) \<Longrightarrow> inj_on (insert x) A"
  by (auto simp: inj_on_def insert_eq_iff)

lemma
  assumes "finite A" "A \<noteq> {}"
  shows   card_even_subset_aux: "card {B. B \<subseteq> A \<and> even (card B)} = 2 ^ (card A - 1)"
    and   card_odd_subset_aux:  "card {B. B \<subseteq> A \<and> odd (card B)} = 2 ^ (card A - 1)"
    and   card_even_odd_subset: "card {B. B \<subseteq> A \<and> even (card B)} = card {B. B \<subseteq> A \<and> odd (card B)}"
proof -
  from assms have *: "2 * card (Set.filter (even \<circ> card) (Pow A)) = 2 ^ card A"
  proof (induction A rule: finite_ne_induct)
    case (singleton x)
    hence "Pow {x} = {{}, {x}}" by auto
    thus ?case by (simp add: Set_filter_insert)
  next
    case (insert x A)
    note fin = finite_subset[OF _ \<open>finite A\<close>]
    have "Pow (insert x A) = Pow A \<union> insert x ` Pow A" by (rule Pow_insert)
    have "Set.filter (even \<circ> card) (Pow (insert x A)) = 
            Set.filter (even \<circ> card) (Pow A) \<union> 
            insert x ` Set.filter (even \<circ> card \<circ> insert x) (Pow A)"
      unfolding Pow_insert Set_filter_union Set_filter_image by blast
    also have "Set.filter (even \<circ> card \<circ> insert x) (Pow A) = Set.filter (odd \<circ> card) (Pow A)"
      unfolding o_def
      by (intro Set_filter_cong refl, subst card_insert_disjoint) 
         (insert insert.hyps, auto dest: finite_subset)
    also have "card (Set.filter (even \<circ> card) (Pow A) \<union> insert x ` \<dots>) = 
                 card (Set.filter (even \<circ> card) (Pow A)) + card (insert x ` \<dots>)"
      (is "card (?A \<union> ?B) = _")
      by (intro card_Un_disjoint finite_Set_filter finite_imageI) (auto simp:  insert.hyps)
    also have "card ?B = card (Set.filter (odd \<circ> card) (Pow A))"
      using insert.hyps by (intro card_image inj_on_insert') auto
    also have "Set.filter (odd \<circ> card) (Pow A) = Pow A - Set.filter (even \<circ> card) (Pow A)"
      by auto
    also have "card \<dots> = card (Pow A) - card (Set.filter (even \<circ> card) (Pow A))"
      using insert.hyps by (subst card_Diff_subset) (auto simp: finite_Set_filter)
    also have "card (Set.filter (even \<circ> card) (Pow A)) + \<dots> = card (Pow A)"
      by (intro add_diff_inverse_nat, subst not_less, rule card_mono) (insert insert.hyps, auto)  
    also have "2 * \<dots> = 2 ^ card (insert x A)"
      using insert.hyps by (simp add: card_Pow)
    finally show ?case .
  qed
  from * show A: "card {B. B \<subseteq> A \<and> even (card B)} = 2 ^ (card A - 1)"
    by (cases "card A") (simp_all add: Set.filter_def)

  have "Set.filter (odd \<circ> card) (Pow A) = Pow A - Set.filter (even \<circ> card) (Pow A)" by auto
  also have "2 * card \<dots> = 2 * 2 ^ card A - 2 * card (Set.filter (even \<circ> card) (Pow A))"
    using assms by (subst card_Diff_subset) (auto intro!: finite_Set_filter simp: card_Pow)
  also note *
  also have "2 * 2 ^ card A - 2 ^ card A = (2 ^ card A :: nat)" by simp
  finally show B: "card {B. B \<subseteq> A \<and> odd (card B)} = 2 ^ (card A - 1)"
    by (cases "card A") (simp_all add: Set.filter_def)

  from A and B show "card {B. B \<subseteq> A \<and> even (card B)} = card {B. B \<subseteq> A \<and> odd (card B)}" by simp
qed
  
lemma bij_betw_prod_divisors_coprime:
  assumes "coprime a (b :: nat)"
  shows   "bij_betw (\<lambda>x. fst x * snd x) ({d. d dvd a} \<times> {d. d dvd b}) {k. k dvd a * b}"
  unfolding bij_betw_def
proof
  from assms show "inj_on (\<lambda>x. fst x * snd x) ({d. d dvd a} \<times> {d. d dvd b})"
    by (auto simp: inj_on_def coprime_crossproduct_nat coprime_divisors)
  show "(\<lambda>x. fst x * snd x) ` ({d. d dvd a} \<times> {d. d dvd b}) = {k. k dvd a * b}"
  proof safe
    fix x assume "x dvd a * b"
    from division_decomp[OF this] guess b' c' by (elim exE conjE)
    thus "x \<in> (\<lambda>x. fst x * snd x) ` ({d. d dvd a} \<times> {d. d dvd b})" by force
  qed (insert assms, auto intro: mult_dvd_mono)
qed

lemma bij_betw_prime_power_divisors:
  assumes "prime (p :: nat)"
  shows   "bij_betw ((^) p) {..k} {d. d dvd p ^ k}"
  unfolding bij_betw_def
proof 
  from assms have *: "p > 1" by (simp add: prime_gt_Suc_0_nat)
  show "inj_on ((^) p) {..k}" using assms
    by (auto simp: inj_on_def prime_gt_Suc_0_nat power_inject_exp[OF *])
  show "(^) p ` {..k} = {d. d dvd p ^ k}"
    using assms by (auto simp: le_imp_power_dvd divides_primepow_nat)
qed

lemma power_diff':
  assumes "m \<ge> n" "x \<noteq> 0"
  shows   "x ^ (m - n) = (x ^ m div x ^ n :: 'a :: unique_euclidean_semiring)"
proof -
  from assms have "x ^ m = x ^ (m - n) * x ^ n"
    by (subst power_add [symmetric]) simp
  also from assms have "\<dots> div x ^ n = x ^ (m - n)" by simp
  finally show ?thesis ..
qed
  
lemma sum_divisors_coprime_mult:
  assumes "coprime a (b :: nat)"
  shows   "(\<Sum>d | d dvd a * b. f d) = (\<Sum>r | r dvd a. \<Sum>s | s dvd b. f (r * s))"
proof -
  have "(\<Sum>r | r dvd a. \<Sum>s | s dvd b. f (r * s)) =
          (\<Sum>z\<in>{r. r dvd a} \<times> {s. s dvd b}. f (fst z * snd z))"
    by (subst sum.cartesian_product) (simp add: case_prod_unfold)
  also have "\<dots> = (\<Sum>d | d dvd a * b. f d)"
    by (intro sum.reindex_bij_betw bij_betw_prod_divisors_coprime assms)
  finally show ?thesis ..
qed

end
