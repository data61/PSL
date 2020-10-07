(* Author: Alexander Maletzky *)

section \<open>Integer Binomial Coefficients\<close>

theory Binomial_Int
  imports Complex_Main
begin

lemma upper_le_binomial:
  assumes "0 < k" and "k < n"
  shows "n \<le> n choose k"
proof -
  from assms have "1 \<le> n" by simp
  define k' where "k' = (if n div 2 \<le> k then k else n - k)"
  from assms have 1: "k' \<le> n - 1" and 2: "n div 2 \<le> k'" by (auto simp: k'_def)
  from assms(2) have "k \<le> n" by simp
  have "n choose k = n choose k'" by (simp add: k'_def binomial_symmetric[OF \<open>k \<le> n\<close>])
  have "n = n choose 1" by (simp only: choose_one)
  also from \<open>1 \<le> n\<close> have "\<dots> = n choose (n - 1)" by (rule binomial_symmetric)
  also from 1 2 have "\<dots> \<le> n choose k'" by (rule binomial_antimono) simp
  also have "\<dots> = n choose k" by (simp add: k'_def binomial_symmetric[OF \<open>k \<le> n\<close>])
  finally show ?thesis .
qed

text \<open>Restore original sort constraints:\<close>
setup \<open>Sign.add_const_constraint (@{const_name gbinomial}, SOME @{typ "'a::{semidom_divide,semiring_char_0} \<Rightarrow> nat \<Rightarrow> 'a"})\<close>

lemma gbinomial_0_left: "0 gchoose k = (if k = 0 then 1 else 0)"
  by (cases k) simp_all

lemma gbinomial_eq_0_int:
  assumes "n < k"
  shows "(int n) gchoose k = 0"
proof -
  have "\<exists>a\<in>{0..<k}. int n - int a = 0"
  proof
    show "int n - int n = 0" by simp
  next
    from assms show "n \<in> {0..<k}" by simp
  qed
  with finite_atLeastLessThan have eq: "prod (\<lambda>i. int n - int i) {0..<k} = 0" by (rule prod_zero)
  show ?thesis by (simp add: gbinomial_prod_rev eq)
qed

corollary gbinomial_eq_0: "0 \<le> a \<Longrightarrow> a < int k \<Longrightarrow> a gchoose k = 0"
  by (metis nat_eq_iff2 nat_less_iff gbinomial_eq_0_int)

lemma int_binomial: "int (n choose k) = (int n) gchoose k"
proof (cases "k \<le> n")
  case True
  from refl have eq: "(\<Prod>i = 0..<k. int (n - i)) = (\<Prod>i = 0..<k. int n - int i)"
  proof (rule prod.cong)
    fix i
    assume "i \<in> {0..<k}"
    with True show "int (n - i) = int n - int i" by simp
  qed
  show ?thesis
    by (simp add: gbinomial_binomial[symmetric] gbinomial_prod_rev zdiv_int eq)
next
  case False
  thus ?thesis by (simp add: gbinomial_eq_0_int)
qed

lemma falling_fact_pochhammer: "prod (\<lambda>i. a - int i) {0..<k} = (- 1) ^ k * pochhammer (- a) k"
proof -
  have eq: "z ^ Suc n * prod f {0..n} = prod (\<lambda>x. z * f x) {0..n}" for z::int and n f
    by (induct n) (simp_all add: ac_simps)
  show ?thesis
  proof (cases k)
    case 0
    thus ?thesis by (simp add: pochhammer_minus)
  next
    case (Suc n)
    thus ?thesis
      by (simp only: pochhammer_prod atLeastLessThanSuc_atLeastAtMost
          prod.atLeast_Suc_atMost_Suc_shift eq flip: power_mult_distrib) (simp add: of_nat_diff)
  qed
qed

lemma falling_fact_pochhammer': "prod (\<lambda>i. a - int i) {0..<k} = pochhammer (a - int k + 1) k"
  by (simp add: falling_fact_pochhammer pochhammer_minus')

lemma gbinomial_int_pochhammer: "(a::int) gchoose k = (- 1) ^ k * pochhammer (- a) k div fact k"
  by (simp only: gbinomial_prod_rev falling_fact_pochhammer)

lemma gbinomial_int_pochhammer': "a gchoose k = pochhammer (a - int k + 1) k div fact k"
  by (simp only: gbinomial_prod_rev falling_fact_pochhammer')

lemma fact_dvd_pochhammer: "fact k dvd pochhammer (a::int) k"
proof -
  have dvd: "y \<noteq> 0 \<Longrightarrow> ((of_int (x div y))::'a::field_char_0) = of_int x / of_int y \<Longrightarrow> y dvd x"
    for x y :: int
    by (smt dvd_triv_left mult.commute nonzero_eq_divide_eq of_int_eq_0_iff of_int_eq_iff of_int_mult)
  show ?thesis
  proof (cases "0 < a")
    case True
    moreover define n where "n = nat (a - 1) + k"
    ultimately have a: "a = int n - int k + 1" by simp
    from fact_nonzero show ?thesis unfolding a
    proof (rule dvd)
      have "of_int (pochhammer (int n - int k + 1) k div fact k) = (of_int (int n gchoose k)::rat)"
        by (simp only: gbinomial_int_pochhammer')
      also have "\<dots> = of_int (int (n choose k))" by (simp only: int_binomial)
      also have "\<dots> = of_nat (n choose k)" by simp
      also have "\<dots> = (of_nat n) gchoose k" by (fact binomial_gbinomial)
      also have "\<dots> = pochhammer (of_nat n - of_nat k + 1) k / fact k"
        by (fact gbinomial_pochhammer')
      also have "\<dots> = pochhammer (of_int (int n - int k + 1)) k / fact k" by simp
      also have "\<dots> = (of_int (pochhammer (int n - int k + 1) k)) / (of_int (fact k))"
        by (simp only: of_int_fact pochhammer_of_int)
      finally show "of_int (pochhammer (int n - int k + 1) k div fact k) =
                      of_int (pochhammer (int n - int k + 1) k) / rat_of_int (fact k)" .
    qed
  next
    case False
    moreover define n where "n = nat (- a)"
    ultimately have a: "a = - int n" by simp
    from fact_nonzero have "fact k dvd (-1)^k * pochhammer (- int n) k"
    proof (rule dvd)
      have "of_int ((-1)^k * pochhammer (- int n) k div fact k) = (of_int (int n gchoose k)::rat)"
        by (simp only: gbinomial_int_pochhammer)
      also have "\<dots> = of_int (int (n choose k))" by (simp only: int_binomial)
      also have "\<dots> = of_nat (n choose k)" by simp
      also have "\<dots> = (of_nat n) gchoose k" by (fact binomial_gbinomial)
      also have "\<dots> = (-1)^k * pochhammer (- of_nat n) k / fact k"
        by (fact gbinomial_pochhammer)
      also have "\<dots> = (-1)^k * pochhammer (of_int (- int n)) k / fact k" by simp
      also have "\<dots> = (-1)^k * (of_int (pochhammer (- int n) k)) / (of_int (fact k))"
        by (simp only: of_int_fact pochhammer_of_int)
      also have "\<dots> = (of_int ((-1)^k * pochhammer (- int n) k)) / (of_int (fact k))" by simp
      finally show "of_int ((- 1) ^ k * pochhammer (- int n) k div fact k) =
                    of_int ((- 1) ^ k * pochhammer (- int n) k) / rat_of_int (fact k)" .
    qed
    thus ?thesis unfolding a by (metis dvdI dvd_mult_unit_iff' minus_one_mult_self)
  qed
qed

lemma gbinomial_int_negated_upper: "(a gchoose k) = (-1) ^ k * ((int k - a - 1) gchoose k)"
  by (simp add: gbinomial_int_pochhammer pochhammer_minus algebra_simps fact_dvd_pochhammer div_mult_swap)

lemma gbinomial_int_mult_fact: "fact k * (a gchoose k) = (\<Prod>i = 0..<k. a - int i)"
  by (simp only: gbinomial_int_pochhammer' fact_dvd_pochhammer dvd_mult_div_cancel falling_fact_pochhammer')

corollary gbinomial_int_mult_fact': "(a gchoose k) * fact k = (\<Prod>i = 0..<k. a - int i)"
  using gbinomial_int_mult_fact[of k a] by (simp add: ac_simps)

lemma gbinomial_int_binomial:
  "a gchoose k = (if 0 \<le> a then int ((nat a) choose k) else (-1::int)^k * int ((k + (nat (- a)) - 1) choose k))"
  by (auto simp: int_binomial gbinomial_int_negated_upper[of a] int_ops(6))

corollary gbinomial_nneg: "0 \<le> a \<Longrightarrow> a gchoose k = int ((nat a) choose k)"
  by (simp add: gbinomial_int_binomial)

corollary gbinomial_neg: "a < 0 \<Longrightarrow> a gchoose k = (-1::int)^k * int ((k + (nat (- a)) - 1) choose k)"
  by (simp add: gbinomial_int_binomial)

lemma of_int_gbinomial: "of_int (a gchoose k) = (of_int a :: 'a::field_char_0) gchoose k"
proof -
  have of_int_div: "y dvd x \<Longrightarrow> of_int (x div y) = of_int x / (of_int y :: 'a)" for x y :: int by auto
  show ?thesis
    by (simp add: gbinomial_int_pochhammer' gbinomial_pochhammer' of_int_div fact_dvd_pochhammer
        pochhammer_of_int[symmetric])
qed

lemma uminus_one_gbinomial [simp]: "(- 1::int) gchoose k = (- 1) ^ k"
  by (simp add: gbinomial_int_binomial)

lemma gbinomial_int_Suc_Suc: "(x + 1::int) gchoose (Suc k) = (x gchoose k) + (x gchoose (Suc k))"
proof (rule linorder_cases)
  assume 1: "x + 1 < 0"
  hence 2: "x < 0" by simp
  then obtain n where 3: "nat (- x) = Suc n" using not0_implies_Suc by fastforce
  hence 4: "nat (- x - 1) = n" by simp
  show ?thesis
  proof (cases k)
    case 0
    show ?thesis by (simp add: \<open>k = 0\<close>)
  next
    case (Suc k')
    from 1 2 3 4 show ?thesis by (simp add: \<open>k = Suc k'\<close> gbinomial_int_binomial int_distrib(2))
  qed
next
  assume "x + 1 = 0"
  hence "x = - 1" by simp
  thus ?thesis by simp
next
  assume "0 < x + 1"
  hence "0 \<le> x + 1" and "0 \<le> x" and "nat (x + 1) = Suc (nat x)" by simp_all
  thus ?thesis by (simp add: gbinomial_int_binomial)
qed

corollary plus_Suc_gbinomial:
  "(x + (1 + int k)) gchoose (Suc k) = ((x + int k) gchoose k) + ((x + int k) gchoose (Suc k))"
    (is "?l = ?r")
proof -
  have "?l = (x + int k + 1) gchoose (Suc k)" by (simp only: ac_simps)
  also have "\<dots> = ?r" by (fact gbinomial_int_Suc_Suc)
  finally show ?thesis .
qed

lemma gbinomial_int_n_n [simp]: "(int n) gchoose n = 1"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "int (Suc n) gchoose Suc n = (int n + 1) gchoose Suc n" by (simp add: add.commute)
  also have "\<dots> = (int n gchoose n) + (int n gchoose (Suc n))" by (fact gbinomial_int_Suc_Suc)
  finally show ?case by (simp add: Suc gbinomial_eq_0)
qed

lemma gbinomial_int_Suc_n [simp]: "(1 + int n) gchoose n = 1 + int n"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "1 + int (Suc n) gchoose Suc n = (1 + int n) + 1 gchoose Suc n" by simp
  also have "\<dots> = (1 + int n gchoose n) + (1 + int n gchoose (Suc n))" by (fact gbinomial_int_Suc_Suc)
  also have "\<dots> = 1 + int n + (int (Suc n) gchoose (Suc n))" by (simp add: Suc)
  also have "\<dots> = 1 + int (Suc n)" by (simp only: gbinomial_int_n_n)
  finally show ?case .
qed

lemma zbinomial_eq_0_iff [simp]: "a gchoose k = 0 \<longleftrightarrow> (0 \<le> a \<and> a < int k)"
proof
  assume a: "a gchoose k = 0"
  have 1: "b < int k" if "b gchoose k = 0" for b
  proof (rule ccontr)
    assume "\<not> b < int k"
    hence "0 \<le> b" and "k \<le> nat b" by simp_all
    from this(1) have "int ((nat b) choose k) = b gchoose k" by (simp add: gbinomial_int_binomial)
    also have "\<dots> = 0" by (fact that)
    finally show False using \<open>k \<le> nat b\<close> by simp
  qed
  show "0 \<le> a \<and> a < int k"
  proof
    show "0 \<le> a"
    proof (rule ccontr)
      assume "\<not> 0 \<le> a"
      hence "(-1) ^ k * ((int k - a - 1) gchoose k) = a gchoose k"
        by (simp add: gbinomial_int_negated_upper[of a])
      also have "\<dots> = 0" by (fact a)
      finally have "(int k - a - 1) gchoose k = 0" by simp
      hence "int k - a - 1 < int k" by (rule 1)
      with \<open>\<not> 0 \<le> a\<close> show False by simp
    qed
  next
    from a show "a < int k" by (rule 1)
  qed
qed (auto intro: gbinomial_eq_0)

subsection \<open>Sums\<close>

lemma gchoose_rising_sum_nat: "(\<Sum>j\<le>n. int j + int k gchoose k) = (int n + int k + 1) gchoose (Suc k)"
proof -
  have "(\<Sum>j\<le>n. int j + int k gchoose k) = int (\<Sum>j\<le>n. k + j choose k)"
    by (simp add: int_binomial add.commute)
  also have "(\<Sum>j\<le>n. k + j choose k) = (k + n + 1) choose (k + 1)" by (fact choose_rising_sum(1))
  also have "int \<dots> = (int n + int k + 1) gchoose (Suc k)"
    by (simp add: int_binomial ac_simps del: binomial_Suc_Suc)
  finally show ?thesis .
qed

lemma gchoose_rising_sum:
  assumes "0 \<le> n"   \<comment>\<open>Necessary condition.\<close>
  shows "(\<Sum>j=0..n. j + int k gchoose k) = (n + int k + 1) gchoose (Suc k)"
proof -
  from _ refl have "(\<Sum>j=0..n. j + int k gchoose k) = (\<Sum>j\<in>int ` {0..nat n}. j + int k gchoose k)"
  proof (rule sum.cong)
    from assms show "{0..n} = int ` {0..nat n}" by (simp add: image_int_atLeastAtMost)
  qed
  also have "\<dots> = (\<Sum>j\<le>nat n. int j + int k gchoose k)" by (simp add: sum.reindex atMost_atLeast0)
  also have "\<dots> = (int (nat n) + int k + 1) gchoose (Suc k)" by (fact gchoose_rising_sum_nat)
  also from assms have "\<dots> = (n + int k + 1) gchoose (Suc k)" by (simp add: add.assoc add.commute)
  finally show ?thesis .
qed

subsection \<open>Inequalities\<close>

lemma binomial_mono:
  assumes "m \<le> n"
  shows "m choose k \<le> n choose k"
proof -
  define l where "l = n - m"
  with assms have n: "n = m + l" by simp
  have "m choose k \<le> (m + l) choose k"
  proof (induct l)
    case 0
    show ?case by simp
  next
    case *: (Suc l)
    show ?case
    proof (cases k)
      case 0
      thus ?thesis by simp
    next
      case k: (Suc k0)
      note *
      also have "m + l choose k \<le> m + l choose k + (m + l choose k0)" by simp
      also have "\<dots> = m + Suc l choose k" by (simp add: k)
      finally show ?thesis .
    qed
  qed
  thus ?thesis by (simp only: n)
qed

lemma binomial_plus_le:
  assumes "0 < k"
  shows "(m choose k) + (n choose k) \<le> (m + n) choose k"
proof -
  define k0 where "k0 = k - 1"
  with assms have k: "k = Suc k0" by simp
  show ?thesis unfolding k
  proof (induct n)
    case 0
    show ?case by simp
  next
    case (Suc n)
    have "m choose Suc k0 + (Suc n choose Suc k0) = m choose Suc k0 + (n choose Suc k0) + (n choose k0)"
      by (simp only: binomial_Suc_Suc)
    also from Suc have "\<dots> \<le> (m + n) choose Suc k0 + ((m + n) choose k0)"
    proof (rule add_mono)
      have "n \<le> m + n" by simp
      thus "n choose k0 \<le> m + n choose k0" by (rule binomial_mono)
    qed
    also have "\<dots> = m + Suc n choose Suc k0" by simp
    finally show ?case .
  qed
qed

lemma binomial_ineq_1: "2 * ((n + i) choose k) \<le> n choose k + ((n + 2 * i) choose k)"
proof (cases k)
  case 0
  thus ?thesis by simp
next
  case k: (Suc k0)
  show ?thesis unfolding k
  proof (induct i)
    case 0
    thus ?case by simp
  next
    case (Suc i)
    have "2 * (n + Suc i choose Suc k0) = 2 * (n + i choose k0) + 2 * (n + i choose Suc k0)"
      by simp
    also have "\<dots> \<le> (n + 2 * i choose k0 + (Suc (n + 2 * i) choose k0)) + (n choose Suc k0 + (n + 2 * i choose Suc k0))"
    proof (rule add_mono)
      have "n + i choose k0 \<le> n + 2 * i choose k0" by (rule binomial_mono) simp
      moreover have "n + 2 * i choose k0 \<le> Suc (n + 2 * i) choose k0" by (rule binomial_mono) simp
      ultimately show "2 * (n + i choose k0) \<le> n + 2 * i choose k0 + (Suc (n + 2 * i) choose k0)"
        by simp
    qed (fact Suc)
    also have "\<dots> = n choose Suc k0 + (n + 2 * Suc i choose Suc k0)" by simp
    finally show ?case .
  qed
qed

lemma gbinomial_int_nonneg:
  assumes "0 \<le> (x::int)"
  shows "0 \<le> x gchoose k"
proof -
  have "0 \<le> int (nat x choose k)" by simp
  also from assms have "\<dots> = x gchoose k" by (simp add: int_binomial)
  finally show ?thesis .
qed

lemma gbinomial_int_mono:
  assumes "0 \<le> x" and "x \<le> (y::int)"
  shows "x gchoose k \<le> y gchoose k"
proof -
  from assms have "nat x \<le> nat y" by simp
  hence "nat x choose k \<le> nat y choose k" by (rule binomial_mono)
  hence "int (nat x choose k) \<le> int (nat y choose k)" by (simp only: zle_int)
  hence "int (nat x) gchoose k \<le> int (nat y) gchoose k" by (simp only: int_binomial)
  with assms show ?thesis by simp
qed

lemma gbinomial_int_plus_le:
  assumes "0 < k" and "0 \<le> x" and "0 \<le> (y::int)"
  shows "(x gchoose k) + (y gchoose k) \<le> (x + y) gchoose k"
proof -
  from assms(1) have "nat x choose k + (nat y choose k) \<le> nat x + nat y choose k"
    by (rule binomial_plus_le)
  hence "int (nat x choose k + (nat y choose k)) \<le> int (nat x + nat y choose k)"
    by (simp only: zle_int)
  hence "int (nat x) gchoose k + (int (nat y) gchoose k) \<le> int (nat x) + int (nat y) gchoose k"
    by (simp only: int_plus int_binomial)
  with assms(2, 3) show ?thesis by simp
qed

lemma binomial_int_ineq_1:
  assumes "0 \<le> x" and "0 \<le> (y::int)"
  shows "2 * (x + y gchoose k) \<le> x gchoose k + ((x + 2 * y) gchoose k)"
proof -
  from binomial_ineq_1[of "nat x" "nat y" k]
  have "int (2 * (nat x + nat y choose k)) \<le> int (nat x choose k + (nat x + 2 * nat y choose k))"
    by (simp only: zle_int)
  hence "2 * (int (nat x) + int (nat y) gchoose k) \<le> int (nat x) gchoose k + (int (nat x) + 2 * int (nat y) gchoose k)"
    by (simp only: int_binomial int_plus int_ops(7)) simp
  with assms show ?thesis by simp
qed

corollary binomial_int_ineq_2:
  assumes "0 \<le> y" and "y \<le> (x::int)"
  shows "2 * (x gchoose k) \<le> x - y gchoose k + (x + y gchoose k)"
proof -
  from assms(2) have "0 \<le> x - y" by simp
  hence "2 * ((x - y) + y gchoose k) \<le> x - y gchoose k + ((x - y + 2 * y) gchoose k)"
    using assms(1) by (rule binomial_int_ineq_1)
  thus ?thesis by smt
qed

corollary binomial_int_ineq_3:
  assumes "0 \<le> y" and "y \<le> 2 * (x::int)"
  shows "2 * (x gchoose k) \<le> y gchoose k + (2 * x - y gchoose k)"
proof (cases "y \<le> x")
  case True
  hence "0 \<le> x - y" by simp
  moreover from assms(1) have "x - y \<le> x" by simp
  ultimately have "2 * (x gchoose k) \<le> x - (x - y) gchoose k + (x + (x - y) gchoose k)"
    by (rule binomial_int_ineq_2)
  thus ?thesis by simp
next
  case False
  hence "0 \<le> y - x" by simp
  moreover from assms(2) have "y - x \<le> x" by simp
  ultimately have "2 * (x gchoose k) \<le> x - (y - x) gchoose k + (x + (y - x) gchoose k)"
    by (rule binomial_int_ineq_2)
  thus ?thesis by simp
qed

subsection \<open>Backward Difference Operator\<close>

definition bw_diff :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a::{ab_group_add,one}"
  where "bw_diff f x = f x - f (x - 1)"

lemma bw_diff_const [simp]: "bw_diff (\<lambda>_. c) = (\<lambda>_. 0)"
  by (rule ext) (simp add: bw_diff_def)

lemma bw_diff_id [simp]: "bw_diff (\<lambda>x. x) = (\<lambda>_. 1)"
  by (rule ext) (simp add: bw_diff_def)

lemma bw_diff_plus [simp]: "bw_diff (\<lambda>x. f x + g x) = (\<lambda>x. bw_diff f x + bw_diff g x)"
  by (rule ext) (simp add: bw_diff_def)

lemma bw_diff_uminus [simp]: "bw_diff (\<lambda>x. - f x) = (\<lambda>x. - bw_diff f x)"
  by (rule ext) (simp add: bw_diff_def)

lemma bw_diff_minus [simp]: "bw_diff (\<lambda>x. f x - g x) = (\<lambda>x. bw_diff f x - bw_diff g x)"
  by (rule ext) (simp add: bw_diff_def)

lemma bw_diff_const_pow: "(bw_diff ^^ k) (\<lambda>_. c) = (if k = 0 then \<lambda>_. c else (\<lambda>_. 0))"
  by (induct k, simp_all)

lemma bw_diff_id_pow:
  "(bw_diff ^^ k) (\<lambda>x. x) = (if k = 0 then (\<lambda>x. x) else if k = 1 then (\<lambda>_. 1) else (\<lambda>_. 0))"
  by (induct k, simp_all)

lemma bw_diff_plus_pow [simp]:
  "(bw_diff ^^ k) (\<lambda>x. f x + g x) = (\<lambda>x. (bw_diff ^^ k) f x + (bw_diff ^^ k) g x)"
  by (induct k, simp_all)

lemma bw_diff_uminus_pow [simp]: "(bw_diff ^^ k) (\<lambda>x. - f x) = (\<lambda>x. - (bw_diff ^^ k) f x)"
  by (induct k, simp_all)

lemma bw_diff_minus_pow [simp]:
  "(bw_diff ^^ k) (\<lambda>x. f x - g x) = (\<lambda>x. (bw_diff ^^ k) f x - (bw_diff ^^ k) g x)"
  by (induct k, simp_all)

lemma bw_diff_sum_pow [simp]:
  "(bw_diff ^^ k) (\<lambda>x. (\<Sum>i\<in>I. f i x)) = (\<lambda>x. (\<Sum>i\<in>I. (bw_diff ^^ k) (f i) x))"
  by (induct I rule: infinite_finite_induct, simp_all add: bw_diff_const_pow)

lemma bw_diff_gbinomial:
  assumes "0 < k"
  shows "bw_diff (\<lambda>x::int. (x + n) gchoose k) = (\<lambda>x. (x + n - 1) gchoose (k - 1))"
proof (rule ext)
  fix x::int
  from assms have eq: "Suc (k - Suc 0) = k" by simp
  have "x + n gchoose k = (x + n - 1) + 1 gchoose (Suc (k - 1))" by (simp add: eq)
  also have "\<dots> = (x + n - 1) gchoose (k - 1) + ((x + n - 1) gchoose (Suc (k - 1)))"
    by (fact gbinomial_int_Suc_Suc)
  finally show "bw_diff (\<lambda>x. x + n gchoose k) x = x + n - 1 gchoose (k - 1)"
    by (simp add: eq bw_diff_def algebra_simps)
qed

lemma bw_diff_gbinomial_pow:
  "(bw_diff ^^ l) (\<lambda>x::int. (x + n) gchoose k) =
      (if l \<le> k then (\<lambda>x. (x + n - int l) gchoose (k - l)) else (\<lambda>_. 0))"
proof -
  have *: "l0 \<le> k \<Longrightarrow> (bw_diff ^^ l0) (\<lambda>x::int. (x + n) gchoose k) = (\<lambda>x. (x + n - int l0) gchoose (k - l0))"
    for l0
  proof (induct l0)
    case 0
    show ?case by simp
  next
    case (Suc l0)
    from Suc.prems have "0 < k - l0" and "l0 \<le> k" by simp_all
    from this(2) have eq: "(bw_diff ^^ l0) (\<lambda>x. x + n gchoose k) = (\<lambda>x. x + n - int l0 gchoose (k - l0))"
      by (rule Suc.hyps)
    have "(bw_diff ^^ Suc l0) (\<lambda>x. x + n gchoose k) = bw_diff (\<lambda>x. x + (n - int l0) gchoose (k - l0))"
      by (simp add: eq algebra_simps)
    also from \<open>0 < k - l0\<close> have "\<dots> = (\<lambda>x. (x + (n - int l0) - 1) gchoose (k - l0 - 1))"
      by (rule bw_diff_gbinomial)
    also have "\<dots> = (\<lambda>x. x + n - int (Suc l0) gchoose (k - Suc l0))" by (simp add: algebra_simps)
    finally show ?case .
  qed
  show ?thesis
  proof (simp add: * split: if_split, intro impI)
    assume "\<not> l \<le> k"
    hence "(l - k) + k = l" and "l - k \<noteq> 0" by simp_all
    hence "(bw_diff ^^ l) (\<lambda>x. x + n gchoose k) = (bw_diff ^^ ((l - k) + k)) (\<lambda>x. x + n gchoose k)"
      by (simp only:)
    also have "\<dots> = (bw_diff ^^ (l - k)) (\<lambda>_. 1)" by (simp add: * funpow_add)
    also from \<open>l - k \<noteq> 0\<close> have "\<dots> = (\<lambda>_. 0)" by (simp add: bw_diff_const_pow)
    finally show "(bw_diff ^^ l) (\<lambda>x. x + n gchoose k) = (\<lambda>_. 0)" .
  qed
qed

end (* theory *)
