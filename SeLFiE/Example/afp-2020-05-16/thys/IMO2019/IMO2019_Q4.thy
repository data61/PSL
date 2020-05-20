(*
  File:    IMO2019_Q4.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Q4\<close>
theory IMO2019_Q4
  imports "Prime_Distribution_Elementary.More_Dirichlet_Misc"
begin

text \<open>
  Find all pairs \<open>(k, n)\<close> of positive integers such that $k! = \prod_{i=0}^{n-1} (2^n - 2^i)$.
\<close>

subsection \<open>Auxiliary facts\<close>

(* TODO: Move stuff from this section? *)
lemma Sigma_insert: "Sigma (insert x A) f = (\<lambda>y. (x, y)) ` f x \<union> Sigma A f"
  by auto

lemma atLeastAtMost_nat_numeral:
  "{(m::nat)..numeral k} = 
     (if m \<le> numeral k then insert (numeral k) {m..pred_numeral k} else {})"
  by (auto simp: numeral_eq_Suc)

lemma greaterThanAtMost_nat_numeral:
  "{(m::nat)<..numeral k} = 
     (if m < numeral k then insert (numeral k) {m<..pred_numeral k} else {})"
  by (auto simp: numeral_eq_Suc)

lemma fact_ge_power:
  fixes c :: nat
  assumes "fact n0 \<ge> c ^ n0" "c \<le> n0 + 1"
  assumes "n \<ge> n0"
  shows   "fact n \<ge> c ^ n"
  using assms(3,1,2)
proof (induction n rule: dec_induct)
  case (step n)
  have "c * c ^ n \<le> Suc n * fact n"
    using step by (intro mult_mono) auto
  thus ?case by simp
qed auto

lemma prime_multiplicity_prime:
  fixes p q :: "'a :: factorial_semiring"
  assumes "prime p" "prime q"
  shows   "multiplicity p q = (if p = q then 1 else 0)"
  using assms by (auto simp: prime_multiplicity_other)


text \<open>
  We use Legendre's identity from the library. One could easily prove the property in question
  without the library, but it probably still saves a few lines.

  @{const legendre_aux} (related to Legendre's identity) is the multiplicity of a given prime
  in the prime factorisation of \<open>n!\<close>.
\<close>
(* TODO: Move? *)
lemma multiplicity_prime_fact:
  fixes p :: nat
  assumes "prime p"
  shows   "multiplicity p (fact n) = legendre_aux n p"
proof (cases "p \<le> n")
  case True
  have "fact n = (\<Prod>p | prime p \<and> p \<le> n. p ^ legendre_aux n p)"
    using legendre_identity'[of "real n"] by simp
  also have "multiplicity p \<dots> = (\<Sum>q | prime q \<and> q \<le> n. multiplicity p (q ^ legendre_aux n q))"
    using assms by (subst prime_elem_multiplicity_prod_distrib) auto
  also have "\<dots> = (\<Sum>q\<in>{p}. legendre_aux n q)"
    using assms \<open>p \<le> n\<close> prime_multiplicity_other[of p]
    by (intro sum.mono_neutral_cong_right)
       (auto simp: prime_elem_multiplicity_power_distrib prime_multiplicity_prime split: if_splits)
  finally show ?thesis by simp
next
  case False
  hence "multiplicity p (fact n) = 0"
    using assms by (intro not_dvd_imp_multiplicity_0) (auto simp: prime_dvd_fact_iff)
  moreover from False have "legendre_aux (real n) p = 0"
    by (intro legendre_aux_eq_0) auto
  ultimately show ?thesis by simp
qed

text \<open>
  The following are simple and trivial lower and upper bounds for @{const legendre_aux}:
\<close>
lemma legendre_aux_ge:
  assumes "prime p" "k \<ge> 1"
  shows   "legendre_aux k p \<ge> nat \<lfloor>k / p\<rfloor>"
proof (cases "k \<ge> p")
  case True
  have "(\<Sum>m\<in>{1}. nat \<lfloor>k / real p ^ m\<rfloor>) \<le> (\<Sum>m | 0 < m \<and> real p ^ m \<le> k. nat \<lfloor>k / real p ^ m\<rfloor>)"
    using True finite_sum_legendre_aux[of p] assms by (intro sum_mono2) auto
  with assms True show ?thesis by (simp add: legendre_aux_def)
next
  case False
  with assms have "k / p < 1" by (simp add: field_simps)
  hence "nat \<lfloor>k / p\<rfloor> = 0" by simp
  with False show ?thesis
    by (simp add: legendre_aux_eq_0)
qed

lemma legendre_aux_less:
  assumes "prime p" "k \<ge> 1"
  shows   "legendre_aux k p < k / (p - 1)"
proof -
  have "(\<lambda>m. (k / p) * (1 / p) ^ m) sums ((k / p) * (1 / (1 - 1 / p)))"
    using assms prime_gt_1_nat[of p] by (intro sums_mult geometric_sums) (auto simp: field_simps)
  hence sums: "(\<lambda>m. k / p ^ Suc m) sums (k / (p - 1))"
    using assms prime_gt_1_nat[of p] by (simp add: field_simps of_nat_diff)

  have "real (legendre_aux k p) = (\<Sum>m\<in>{0<..nat \<lfloor>log (real p) k\<rfloor>}. of_int \<lfloor>k / real p ^ m\<rfloor>)"
    using assms by (simp add: legendre_aux_altdef1)
  also have "\<dots> = (\<Sum>m<nat \<lfloor>log (real p) k\<rfloor>. of_int \<lfloor>k / real p ^ Suc m\<rfloor>)"
    by (intro sum.reindex_bij_witness[of _ Suc "\<lambda>i. i - 1"]) (auto simp flip: power_Suc)
  also have "\<dots> \<le> (\<Sum>m<nat \<lfloor>log (real p) k\<rfloor>. k / real p ^ Suc m)"
    by (intro sum_mono) auto
  also have "\<dots> < (\<Sum>m. k / real p ^ Suc m)"
    using sums assms prime_gt_1_nat[of p]
    by (intro sum_less_suminf) (auto simp: sums_iff intro!: divide_pos_pos)
  also have "\<dots> = k / (p - 1)"
    using sums by (simp add: sums_iff)
  finally show ?thesis
    using assms prime_gt_1_nat[of p] by (simp add: of_nat_diff)
qed


subsection \<open>Main result\<close>

text \<open>
  Now we move on to the main result: We fix two numbers \<open>n\<close> and \<open>k\<close> with the property
  in question and derive facts from that.

  The triangle number $T = n(n+1)/2$ is of particular importance here, so we introduce an
  abbreviation for it.
\<close>

context
  fixes k n :: nat and rhs T :: nat
  defines "rhs \<equiv> (\<Prod>i<n. 2 ^ n - 2 ^ i)"
  defines "T \<equiv> (n * (n - 1)) div 2"
  assumes pos: "k > 0" "n > 0"
  assumes k_n: "fact k = rhs"
begin

text \<open>
  We can rewrite the right-hand side into a more convenient form:
\<close>
lemma rhs_altdef: "rhs = 2 ^ T * (\<Prod>i=1..n. 2 ^ i - 1)"
proof -
  have "rhs = (\<Prod>i<n. 2 ^ i * (2 ^ (n - i) - 1))"
    by (simp add: rhs_def algebra_simps flip: power_add)
  also have "\<dots> = 2 ^ (\<Sum>i<n. i) * (\<Prod>i<n. 2 ^ (n - i) - 1)"
    by (simp add: prod.distrib power_sum)
  also have "(\<Sum>i<n. i) = T"
    unfolding T_def using Sum_Ico_nat[of 0 n] by (simp add: atLeast0LessThan)
  also have "(\<Prod>i<n. 2 ^ (n - i) - 1) = (\<Prod>i=1..n. 2 ^ i - 1)"
    by (rule prod.reindex_bij_witness[of _ "\<lambda>i. n - i" "\<lambda>i. n - i"]) auto
  finally show ?thesis .
qed

text \<open>
  The multiplicity of 2 in the prime factorisation of the right-hand side is precisely \<open>T\<close>.
\<close>
lemma multiplicity_2_rhs [simp]: "multiplicity 2 rhs = T"
proof -
  have nz: "2 ^ i - 1 \<noteq> (0 :: nat)" if "i \<ge> 1" for i
  proof -
    from \<open>i \<ge> 1\<close> have "2 ^ 0 < (2 ^ i :: nat)"
      by (intro power_strict_increasing) auto
    thus ?thesis by simp
  qed

  have "multiplicity 2 rhs = T + multiplicity 2 (\<Prod>i=1..n. 2 ^ i - 1 :: nat)"
    using nz by (simp add: rhs_altdef prime_elem_multiplicity_mult_distrib)
  also have "multiplicity 2 (\<Prod>i=1..n. 2 ^ i - 1 :: nat) = 0"
    by (intro not_dvd_imp_multiplicity_0) (auto simp: prime_dvd_prod_iff)
  finally show ?thesis by simp
qed

text \<open>
  From Legendre's identities and the associated bounds, it can easily be seen that
  \<open>\<lfloor>k/2\<rfloor> \<le> T < k\<close>:
\<close>
lemma k_gt_T: "k > T"
proof -
  have "T = multiplicity 2 rhs"
    by simp
  also have "rhs = fact k"
    by (simp add: k_n)
  also have "multiplicity 2 (fact k :: nat) = legendre_aux k 2"
    by (simp add: multiplicity_prime_fact)
  also have "\<dots> < k"
    using legendre_aux_less[of 2 k] pos by simp
  finally show ?thesis .
qed

lemma T_ge_half_k: "T \<ge> k div 2"
proof -
  have "k div 2 \<le> legendre_aux k 2"
    using legendre_aux_ge[of 2 k] pos by simp linarith?
  also have "\<dots> = multiplicity 2 (fact k :: nat)"
    by (simp add: multiplicity_prime_fact)
  also have "\<dots> = T" by (simp add: k_n)
  finally show "T \<ge> k div 2" .
qed

text \<open>
  It can also be seen fairly easily that the right-hand side is strictly smaller than $2^{n^2}$:
\<close>
lemma rhs_less: "rhs < 2 ^ n\<^sup>2"
proof -
  have "rhs = 2 ^ T * (\<Prod>i=1..n. 2 ^ i - 1)"
    by (simp add: rhs_altdef)
  also have "(\<Prod>i=1..n. 2 ^ i - 1 :: nat) < (\<Prod>i=1..n. 2 ^ i)"
    using pos by (intro prod_mono_strict) auto
  also have "\<dots> = (\<Prod>i=0..<n. 2 * 2 ^ i)"
    by (intro prod.reindex_bij_witness[of _ Suc "\<lambda>i. i - 1"]) (auto simp flip: power_Suc)
  also have "\<dots> = 2 ^ n * 2 ^ (\<Sum>i=0..<n. i)"
    by (simp add: power_sum prod.distrib)
  also have "(\<Sum>i=0..<n. i) = T"
    unfolding T_def by (simp add: Sum_Ico_nat)
  also have "2 ^ T * (2 ^ n * 2 ^ T :: nat) = 2 ^ (2 * T + n)"
    by (simp flip: power_add power_Suc add: algebra_simps)
  also have "2 * T + n = n ^ 2"
    by (cases "even n") (auto simp: T_def algebra_simps power2_eq_square)
  finally show "rhs < 2 ^ n\<^sup>2"
    by simp
qed

text \<open>
  It is clear that $2^{n^2} \leq 8^T$ and that $8^T < T!$ if $T$ is sufficiently big.
  In this case, `sufficiently big' means \<open>T \<ge> 20\<close> and thereby \<open>n \<ge> 7\<close>. We can therefore
  conclude that \<open>n\<close> must be less than 7.
\<close>
lemma n_less_7: "n < 7"
proof (rule ccontr)
  assume "\<not>n < 7"
  hence "n \<ge> 7" by simp
  have "T \<ge> (7 * 6) div 2"
    unfolding T_def using \<open>n \<ge> 7\<close> by (intro div_le_mono mult_mono) auto
  hence "T \<ge> 21" by simp

  from \<open>n \<ge> 7\<close> have "(n * 2) div 2 \<le> T"
    unfolding T_def by (intro div_le_mono) auto
  hence "T \<ge> n" by simp

  from \<open>T \<ge> 21\<close> have "sqrt (2 * pi * T) * (T / exp 1) ^ T \<le> fact T"
    using fact_bounds[of T] by simp
  have "fact T \<le> (fact k :: nat)"
    using k_gt_T by (intro fact_mono) (auto simp: T_def)
  also have "\<dots> = rhs" by fact
  also have "rhs < 2 ^ n\<^sup>2" by (rule rhs_less)
  also have "n\<^sup>2 = 2 * T + n"
    by (cases "even n") (auto simp: T_def algebra_simps power2_eq_square)
  also have "\<dots> \<le> 3 * T"
    using \<open>T \<ge> n\<close> by (simp add: T_def)
  also have "2 ^ (3 * T) = (8 ^ T :: nat)"
    by (simp add: power_mult)
  finally have "fact T < (8 ^ T :: nat)"
    by simp
  moreover have "fact T \<ge> (8 ^ T :: nat)"
    by (rule fact_ge_power[of _ 20]) (use \<open>T \<ge> 21\<close> in \<open>auto simp: fact_numeral\<close>)
  ultimately show False by simp
qed

text \<open>
  We now only have 6 values for \<open>n\<close> to check. Together with the bounds that we obtained on \<open>k\<close>,
  this only leaves a few combinations of \<open>n\<close> and \<open>k\<close> to check, and we do precisely that
  and find that \<open>n = k = 1\<close> and \<open>n = 2, k = 3\<close> are the only possible combinations.
\<close>
lemma n_k_in_set: "(n, k) \<in> {(1, 1), (2, 3)}"
proof -
  define T' where "T' = (\<lambda>n :: nat. n * (n - 1) div 2)"
  define A :: "(nat \<times> nat) set" where "A = (SIGMA n:{1..6}. {T' n<..2 * T' n + 1})"
  define P where "P = (\<lambda>(n, k). fact k = (\<Prod>i<n. 2 ^ n - 2 ^ i :: nat))"
  have [simp]: "{0<..Suc 0} = {1}" by auto
  have "(n, k) \<in> Set.filter P A"
    using k_n pos T_ge_half_k k_gt_T n_less_7
    by (auto simp: A_def T'_def T_def Set.filter_def P_def rhs_def)
  also have "Set.filter P A = {(1, 1), (2, 3)}"
    by (simp add: P_def Set_filter_insert A_def atMost_nat_numeral atMost_Suc T'_def Sigma_insert 
          greaterThanAtMost_nat_numeral atLeastAtMost_nat_numeral lessThan_nat_numeral fact_numeral
             cong: if_weak_cong)
  finally show ?thesis .
qed

end


text \<open>
  Using this, deriving the final result is now trivial:
\<close>
theorem "{(n, k). n > 0 \<and> k > 0 \<and> fact k = (\<Prod>i<n. 2 ^ n - 2 ^ i :: nat)} = {(1, 1), (2, 3)}"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs" using n_k_in_set by blast
  show "?rhs \<subseteq> ?lhs" by (auto simp: fact_numeral lessThan_nat_numeral)
qed

end