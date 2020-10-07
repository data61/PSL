(*
  File:     Algebraic_Auxiliaries.thy
  Authors:  Daniel Stüwe

  Miscellaneous facts about algebra and number theory
*)
section \<open>Auxiliary Material\<close>
theory Algebraic_Auxiliaries
  imports 
    "HOL-Algebra.Algebra"
    "HOL-Computational_Algebra.Squarefree"
    "HOL-Number_Theory.Number_Theory"
begin
          
hide_const (open) Divisibility.prime

lemma sum_of_bool_eq_card:
  assumes "finite S"
  shows "(\<Sum>a \<in> S. of_bool (P a)) = real (card {a \<in> S . P a })"
proof -
  have "(\<Sum>a \<in> S. of_bool (P a) :: real) = (\<Sum>a \<in> {x\<in>S. P x}. 1)"
    using assms by (intro sum.mono_neutral_cong_right) auto
  thus ?thesis by simp
qed

lemma mod_natE:
  fixes a n b :: nat
  assumes "a mod n = b"
  shows "\<exists> l. a = n * l + b"
  using assms mod_mult_div_eq[of a n] by (metis add.commute)

lemma (in group) r_coset_is_image: "H #> a = (\<lambda> x. x \<otimes> a) ` H"
  unfolding r_coset_def image_def
  by blast

lemma (in group) FactGroup_order:
  assumes "subgroup H G" "finite H"
  shows "order G = order (G Mod H) * card H"
using lagrange assms unfolding FactGroup_def order_def by simp

corollary (in group) FactGroup_order_div:
  assumes "subgroup H G" "finite H"
  shows "order (G Mod H) = order G div card H" 
using assms FactGroup_order subgroupE(2)[OF \<open>subgroup H G\<close>] by (auto simp: order_def)

lemma group_hom_imp_group_hom_image:
  assumes "group_hom G G h"
  shows "group_hom G (G\<lparr>carrier := h  ` carrier G\<rparr>) h"
  using group_hom.axioms[OF assms] group_hom.img_is_subgroup[OF assms] group.subgroup_imp_group
  by(auto intro!: group_hom.intro simp: group_hom_axioms_def hom_def)

theorem homomorphism_thm:
  assumes "group_hom G G h"
  shows "G Mod kernel G (G\<lparr>carrier := h ` carrier G\<rparr>) h \<cong> G \<lparr>carrier := h ` carrier G\<rparr>"
  by (intro group_hom.FactGroup_iso group_hom_imp_group_hom_image assms) simp

lemma is_iso_imp_same_card:
  assumes "H \<cong> G "
  shows "order H = order G"
proof -
  from assms obtain h where "bij_betw h (carrier H) (carrier G)"
    unfolding is_iso_def iso_def
    by blast

  then show ?thesis
    unfolding order_def 
    by (rule bij_betw_same_card)
qed

corollary homomorphism_thm_order:
  assumes "group_hom G G h" 
  shows "order (G\<lparr>carrier := h ` carrier G\<rparr>) * card (kernel G (G\<lparr>carrier := h ` carrier G\<rparr>) h) = order G "
proof -
  have "order (G\<lparr>carrier := h ` carrier G\<rparr>) = order (G Mod (kernel G (G\<lparr>carrier := h ` carrier G\<rparr>) h))"
    using is_iso_imp_same_card[OF homomorphism_thm] \<open>group_hom G G h\<close>
    by fastforce

  moreover have "group G" using \<open>group_hom G G h\<close> group_hom.axioms by blast

  ultimately show ?thesis
    using \<open>group_hom G G h\<close> and group_hom_imp_group_hom_image[OF \<open>group_hom G G h\<close>] 
    unfolding FactGroup_def
    by (simp add: group.lagrange group_hom.subgroup_kernel order_def)
qed

lemma (in group_hom) kernel_subset: "kernel G H h \<subseteq> carrier G"
  using subgroup_kernel G.subgroupE(1) by blast

lemma (in group) proper_subgroup_imp_bound_on_card:
  assumes "H \<subset> carrier G" "subgroup H G" "finite (carrier G)"
  shows "card H \<le> order G div 2"
proof -
  from \<open>finite (carrier G)\<close> have "finite (rcosets H)"
    by (simp add: RCOSETS_def)

  note subgroup.subgroup_in_rcosets[OF \<open>subgroup H G\<close> is_group]
  then obtain J where "J \<noteq> H" "J \<in> rcosets H"
    using rcosets_part_G[OF \<open>subgroup H G\<close>] and \<open>H \<subset> carrier G\<close>
    by (metis Sup_le_iff inf.absorb_iff2 inf.idem inf.strict_order_iff)

  then have "2 \<le> card (rcosets H)"
    using \<open>H \<in> rcosets H\<close> card_mono[OF \<open>finite (rcosets H)\<close>, of "{H, J}"]
    by simp

  then show ?thesis
    using mult_le_mono[of 2 "card (rcosets H)" "card H" "card H"]  
    unfolding lagrange[OF \<open>subgroup H G\<close>]
    by force
qed

lemma cong_exp_trans[trans]: 
  "[a ^ b = c] (mod n) \<Longrightarrow> [a = d] (mod n) \<Longrightarrow> [d ^ b = c] (mod n)"
  "[c = a ^ b] (mod n) \<Longrightarrow> [a = d] (mod n) \<Longrightarrow> [c = d ^ b] (mod n)"
  using cong_pow cong_sym cong_trans by blast+

lemma cong_exp_mod[simp]: 
  "[(a mod n) ^ b = c] (mod n) \<longleftrightarrow> [a ^ b = c] (mod n)"
  "[c = (a mod n) ^ b] (mod n) \<longleftrightarrow> [c = a ^ b] (mod n)"
  by (auto simp add: cong_def mod_simps)

lemma cong_mult_mod[simp]:
  "[(a mod n) * b = c] (mod n) \<longleftrightarrow> [a * b = c] (mod n)"
  "[a * (b mod n) = c] (mod n) \<longleftrightarrow> [a * b = c] (mod n)"
  by (auto simp add: cong_def mod_simps)

lemma cong_add_mod[simp]:
  "[(a mod n) + b = c] (mod n) \<longleftrightarrow> [a + b = c] (mod n)"
  "[a + (b mod n) = c] (mod n) \<longleftrightarrow> [a + b = c] (mod n)"
  "[\<Sum>i\<in>A. f i mod n = c] (mod n) \<longleftrightarrow> [\<Sum>i\<in>A. f i = c] (mod n)"
  by (auto simp add: cong_def mod_simps)

lemma cong_add_trans[trans]:
  "[a = b + x] (mod n) \<Longrightarrow> [x = y] (mod n) \<Longrightarrow> [a = b + y] (mod n)"
  "[a = x + b] (mod n) \<Longrightarrow> [x = y] (mod n) \<Longrightarrow> [a = y + b] (mod n)"
  "[b + x = a] (mod n) \<Longrightarrow> [x = y] (mod n) \<Longrightarrow> [b + y = a] (mod n)"
  "[x + b = a] (mod n) \<Longrightarrow> [x = y] (mod n) \<Longrightarrow> [y + b = a] (mod n)"
  unfolding cong_def
  using mod_simps(1, 2)
  by metis+

lemma cong_mult_trans[trans]:
  "[a = b * x] (mod n) \<Longrightarrow> [x = y] (mod n) \<Longrightarrow> [a = b * y] (mod n)"
  "[a = x * b] (mod n) \<Longrightarrow> [x = y] (mod n) \<Longrightarrow> [a = y * b] (mod n)"
  "[b * x = a] (mod n) \<Longrightarrow> [x = y] (mod n) \<Longrightarrow> [b * y = a] (mod n)"
  "[x * b = a] (mod n) \<Longrightarrow> [x = y] (mod n) \<Longrightarrow> [y * b = a] (mod n)"
  unfolding cong_def
  using mod_simps(4, 5)
  by metis+

lemma cong_diff_trans[trans]:
  "[a = b - x] (mod n) \<Longrightarrow> [x = y] (mod n) \<Longrightarrow> [a = b - y] (mod n)" 
  "[a = x - b] (mod n) \<Longrightarrow> [x = y] (mod n) \<Longrightarrow> [a = y - b] (mod n)" 
  "[b - x = a] (mod n) \<Longrightarrow> [x = y] (mod n) \<Longrightarrow> [b - y = a] (mod n)"
  "[x - b = a] (mod n) \<Longrightarrow> [x = y] (mod n) \<Longrightarrow> [y - b = a] (mod n)"
  for a :: "'a :: {unique_euclidean_semiring, euclidean_ring_cancel}"
  unfolding cong_def
  by (metis mod_diff_eq)+

lemma eq_imp_eq_mod_int: "a = b \<Longrightarrow> [a = b] (mod m)" for a b :: int by simp
lemma eq_imp_eq_mod_nat: "a = b \<Longrightarrow> [a = b] (mod m)" for a b :: nat by simp

lemma cong_pow_I: "a = b \<Longrightarrow> [x^a = x^b](mod n)" by simp

lemma gre1I: "(n = 0 \<Longrightarrow> False) \<Longrightarrow> (1 :: nat) \<le> n"
  by presburger

lemma gre1I_nat: "(n = 0 \<Longrightarrow> False) \<Longrightarrow> (Suc 0 :: nat) \<le> n"
  by presburger

lemma totient_less_not_prime:
  assumes "\<not> prime n" "1 < n"
  shows "totient n < n - 1"
  using totient_imp_prime totient_less assms
  by (metis One_nat_def Suc_pred le_less_trans less_SucE zero_le_one)

lemma power2_diff_nat: "x \<ge> y \<Longrightarrow> (x - y)\<^sup>2 = x\<^sup>2 + y\<^sup>2 - 2 * x * y" for x y :: nat
  by (simp add: algebra_simps power2_eq_square mult_2_right)
     (meson Nat.diff_diff_right le_add2 le_trans mult_le_mono order_refl)

lemma square_inequality: "1 < n \<Longrightarrow> (n + n) \<le> (n * n)" for n :: nat
  by (metis Suc_eq_plus1_left Suc_leI mult_le_mono1 semiring_normalization_rules(4))

lemma square_one_cong_one:
  assumes "[x = 1](mod n)"
  shows "[x^2 = 1](mod n)"
  using assms cong_pow by fastforce 

lemma cong_square_alt_int:
  "prime p \<Longrightarrow> [a * a = 1] (mod p) \<Longrightarrow> [a = 1] (mod p) \<or> [a = p - 1] (mod p)"
  for a p :: "'a :: {normalization_semidom, linordered_idom, unique_euclidean_ring}"
  using dvd_add_triv_right_iff[of p "a - (p - 1)"]
  by (auto simp add: cong_iff_dvd_diff square_diff_one_factored dest!: prime_dvd_multD)

lemma cong_square_alt:
  "prime p \<Longrightarrow> [a * a = 1] (mod p) \<Longrightarrow> [a = 1] (mod p) \<or> [a = p - 1] (mod p)"
  for a p :: nat
  using cong_square_alt_int and cong_int_iff prime_nat_int_transfer
  by (metis (mono_tags) int_ops(2) int_ops(7) less_imp_le_nat of_nat_diff prime_gt_1_nat)

lemma square_minus_one_cong_one:
  fixes n x :: nat
  assumes "1 < n" "[x = n - 1](mod n)"
  shows "[x^2 = 1](mod n)"
proof -
  have "[x^2 = (n - 1) * (n - 1)] (mod n)"
    using cong_mult[OF assms(2) assms(2)]
    by (simp add: algebra_simps power2_eq_square)

  also have "[(n - 1) * (n - 1) = Suc (n * n) - (n + n)] (mod n)" 
    using power2_diff_nat[of 1 n] \<open>1 < n\<close>
    by (simp add: algebra_simps power2_eq_square)

  also have "[Suc (n * n) - (n + n) = Suc (n * n)] (mod n)"
  proof -
    have "n * n + 0 * n = n * n" by linarith
    moreover have "n * n - (n + n) + (n + n) = n * n"
      using square_inequality[OF \<open>1 < n\<close>] le_add_diff_inverse2 by blast
    moreover have "(Suc 0 + 1) * n = n + n"
      by simp
    ultimately show ?thesis
      using square_inequality[OF \<open>1 < n\<close>] 
      by (metis (no_types) Suc_diff_le add_Suc cong_iff_lin_nat)
  qed

  also have "[Suc (n * n) = 1] (mod n)"
    using cong_to_1'_nat by auto

  finally show ?thesis .
qed

lemma odd_prime_gt_2_int:
 "2 < p" if "odd p" "prime p" for p :: int
  using prime_ge_2_int[OF \<open>prime p\<close>] \<open>odd p\<close>
  by (cases "p = 2") auto

lemma odd_prime_gt_2_nat:
 "2 < p" if "odd p" "prime p" for p :: nat
  using prime_ge_2_nat[OF \<open>prime p\<close>] \<open>odd p\<close>
  by (cases "p = 2") auto

lemma gt_one_imp_gt_one_power_if_coprime:
  "1 \<le> x \<Longrightarrow> 1 < n \<Longrightarrow> coprime x n \<Longrightarrow> 1 \<le> x ^ (n - 1) mod n"
  by (rule gre1I) (auto simp: coprime_commute dest: coprime_absorb_left)

lemma residue_one_dvd: "a mod n = 1 \<Longrightarrow> n dvd a - 1" for a n :: nat
  by (fastforce intro!: cong_to_1_nat simp: cong_def)

lemma coprimeI_power_mod:
  fixes x r n :: nat
  assumes "x ^ r mod n = 1" "r \<noteq> 0" "n \<noteq> 0"
  shows "coprime x n"
proof -
  have "coprime (x ^ r mod n) n"
    using coprime_1_right \<open>x ^ r mod n = 1\<close>
    by (simp add: coprime_commute)
  thus ?thesis using \<open>r \<noteq> 0\<close> \<open>n \<noteq> 0\<close> by simp
qed


(* MOVE - EXTRA *)
lemma prime_dvd_choose:
  assumes "0 < k" "k < p" "prime p" 
  shows "p dvd (p choose k)"
proof -
  have "k \<le> p" using \<open>k < p\<close> by auto 

  have "p dvd fact p" using \<open>prime p\<close> by (simp add: prime_dvd_fact_iff)   
  
  moreover have "\<not> p dvd fact k * fact (p - k)"
    unfolding prime_dvd_mult_iff[OF \<open>prime p\<close>] prime_dvd_fact_iff[OF \<open>prime p\<close>] 
    using assms by simp
  
  ultimately show ?thesis
    unfolding binomial_fact_lemma[OF \<open>k \<le> p\<close>, symmetric]
    using assms prime_dvd_multD by blast
qed

lemma cong_eq_0_I: "(\<forall>i\<in>A. [f i mod n = 0] (mod n)) \<Longrightarrow> [\<Sum>i\<in>A. f i = 0] (mod n)"
  using cong_sum by fastforce

lemma power_mult_cong:
  assumes "[x^n = a](mod m)" "[y^n = b](mod m)"
  shows "[(x*y)^n = a*b](mod m)"
  using assms cong_mult[of "x^n" a m "y^n" b] power_mult_distrib
  by metis

lemma
  fixes n :: nat
  assumes "n > 1"
  shows odd_pow_cong: "odd m \<Longrightarrow> [(n - 1) ^ m = n - 1] (mod n)"
  and even_pow_cong: "even m \<Longrightarrow> [(n - 1) ^ m = 1] (mod n)"
proof (induction m)
  case (Suc m)
  case 1
  with Suc have IH: "[(n - 1) ^ m = 1] (mod n)" by auto
  show ?case using \<open>1 < n\<close> cong_mult[OF cong_refl IH] by simp
next
  case (Suc m)
  case 2
  with Suc have IH: "[(n - 1) ^ m = n - 1] (mod n)" by auto
  show ?case 
    using cong_mult[OF cong_refl IH, of "(n - 1)"] and square_minus_one_cong_one[OF \<open>1 < n\<close>, of "n - 1"]
    by (auto simp: power2_eq_square intro: cong_trans)
qed simp_all

lemma cong_mult_uneq':
  fixes a :: "'a::{unique_euclidean_ring, ring_gcd}"
  assumes "coprime d a"
  shows "[b \<noteq> c] (mod a) \<Longrightarrow> [d = e] (mod a) \<Longrightarrow> [b * d \<noteq> c * e] (mod a)"
  using cong_mult_rcancel[OF assms]
  using cong_trans[of "b*d" "c*e" a "c*d"]
  using cong_scalar_left cong_sym by blast

lemma p_coprime_right_nat: "prime p \<Longrightarrow> coprime a p = (\<not> p dvd a)" for p a :: nat
  by (meson coprime_absorb_left coprime_commute not_prime_unit prime_imp_coprime_nat)


lemma squarefree_mult_imp_coprime:
  assumes "squarefree (a * b :: 'a :: semiring_gcd)"
  shows   "coprime a b"
proof (rule coprimeI)
  fix l assume "l dvd a" "l dvd b"
  then obtain a' b' where "a = l * a'" "b = l * b'"
    by (auto elim!: dvdE)
  with assms have "squarefree (l\<^sup>2 * (a' * b'))"
    by (simp add: power2_eq_square mult_ac)
  thus "l dvd 1" by (rule squarefreeD) auto
qed

lemma prime_divisor_exists_strong:
  fixes m :: int
  assumes "m > 1" "\<not>prime m"
  shows   "\<exists>n k. m = n * k \<and> 1 < n \<and> n < m \<and> 1 < k \<and> k < m"
proof -
  from assms obtain n k where nk: "n * k > 1" "n \<ge> 0" "m = n * k" "n \<noteq> 1" "n \<noteq> 0" "k \<noteq> 1"
    using assms unfolding prime_int_iff dvd_def by auto
  from nk have "n > 1" by linarith

  from nk assms have "n * k > 0" by simp
  with \<open>n \<ge> 0\<close> have "k > 0"
    using zero_less_mult_pos by force
  with \<open>k \<noteq> 1\<close> have "k > 1" by linarith
  from nk have "n > 1" by linarith

  from \<open>k > 1\<close> nk have "n < m" "k < m" by simp_all
  with nk \<open>k > 1\<close> \<open>n > 1\<close> show ?thesis by blast
qed

lemma prime_divisor_exists_strong_nat:
  fixes m :: nat
  assumes "1 < m" "\<not>prime m"
  shows   "\<exists>p k. m = p * k \<and> 1 < p \<and> p < m \<and> 1 < k \<and> k < m \<and> prime p"
proof -
  obtain p where p_def: "prime p" "p dvd m" "p \<noteq> m" "1 < p" 
    using assms prime_prime_factor and prime_gt_1_nat
    by blast

  moreover define k where "k = m div p"
  with \<open>p dvd m\<close> have "m = p * k" by simp

  moreover have "p < m" 
    using \<open>p \<noteq> m\<close> dvd_imp_le[OF \<open>p dvd m\<close>] and \<open>m > 1\<close>
    by simp

  moreover have "1 < k" "k < m"
    using \<open>1 < m\<close> \<open>1 < p\<close> and \<open>p \<noteq> m\<close>
    unfolding \<open>m = p * k\<close>
    by (force intro: Suc_lessI Nat.gr0I)+

  ultimately show ?thesis using \<open>1 < m\<close> by blast
qed

(* TODO Remove *)
lemma prime_factorization_eqI:
  assumes "\<And>p. p \<in># P \<Longrightarrow> prime p" "prod_mset P = n"
  shows   "prime_factorization n = P"
  using prime_factorization_prod_mset_primes[of P] assms by simp

lemma prime_factorization_prime_elem:
  assumes "prime_elem p"
  shows   "prime_factorization p = {#normalize p#}"
proof -
  have "prime_factorization p = prime_factorization (normalize p)"
    by (metis normalize_idem prime_factorization_cong)
  also have "\<dots> = {#normalize p#}"
    by (rule prime_factorization_prime) (use assms in auto)
  finally show ?thesis .
qed

lemma size_prime_factorization_eq_Suc_0_iff [simp]:
  "size (prime_factorization n) = Suc 0 \<longleftrightarrow> prime_elem n"
proof
  define u where "u = unit_factor n"
  assume size: "size (prime_factorization n) = Suc 0"
  hence [simp]: "n \<noteq> 0" by auto
  from size obtain p where *: "prime_factorization n = {#p#}"
    by (auto elim!: size_mset_SucE)
  hence p: "p \<in> prime_factors n" by auto

  have "n = u * prod_mset (prime_factorization n)"
    unfolding u_def by (rule prime_decomposition [symmetric])
  with * have "n = u * p" by simp
  also from p have "prime_elem \<dots>"
    by (subst prime_elem_mult_unit_left)
       (auto simp: u_def prime_imp_prime_elem in_prime_factors_iff)
  finally show "prime_elem n" by auto
qed (auto simp: prime_factorization_prime_elem)
(* END TODO *)

(* TODO Move *)
lemma squarefree_prime_elem [simp, intro]:
  fixes p :: "'a :: algebraic_semidom"
  assumes "prime_elem p"
  shows   "squarefree p"
proof (rule squarefreeI)
  fix x assume "x\<^sup>2 dvd p"
  show "is_unit x"
  proof (rule ccontr)
    assume "\<not>is_unit x"
    hence "\<not>is_unit (x\<^sup>2)"
      by (simp add: is_unit_power_iff)
    from assms and this and \<open>x\<^sup>2 dvd p\<close> have "prime_elem (x\<^sup>2)"
      by (rule prime_elem_mono)
    thus False by (simp add: prime_elem_power_iff)
  qed
qed

lemma squarefree_prime [simp, intro]: "prime p \<Longrightarrow> squarefree p"
  by auto

lemma not_squarefree_primepow:
  assumes "primepow n"
  shows   "squarefree n \<longleftrightarrow> prime n"
  using assms by (auto simp: primepow_def squarefree_power_iff prime_power_iff)

lemma prime_factorization_normalize [simp]:
  "prime_factorization (normalize n) = prime_factorization n"
  by (rule prime_factorization_cong) auto

lemma one_prime_factor_iff_primepow: "card (prime_factors n) = Suc 0 \<longleftrightarrow> primepow (normalize n)"
proof
  assume "primepow (normalize n)"
  then obtain p k where pk: "prime p" "normalize n = p ^ k" "k > 0"
    by (auto simp: primepow_def)
  hence "card (prime_factors (normalize n)) = Suc 0"
    by (subst pk) (simp add: prime_factors_power prime_factorization_prime)
  thus "card (prime_factors n) = Suc 0"
    by simp
next
  assume *: "card (prime_factors n) = Suc 0"
  from * have "(\<Prod>p\<in>prime_factors n. p ^ multiplicity p n) = normalize n"
    by (intro prod_prime_factors) auto
  also from * have "card (prime_factors n) = 1" by simp
  then obtain p where p: "prime_factors n = {p}"
    by (elim card_1_singletonE)
  finally have "normalize n = p ^ multiplicity p n"
    by simp
  moreover from p have "prime p" "multiplicity p n > 0"
    by (auto simp: prime_factors_multiplicity)
  ultimately show "primepow (normalize n)"
    unfolding primepow_def by blast
qed

lemma squarefree_imp_prod_prime_factors_eq:
  assumes "squarefree x"
  shows   "\<Prod>(prime_factors x) = normalize x"
proof -
  from assms have [simp]: "x \<noteq> 0" by auto
  have "(\<Prod>p\<in>prime_factors x. p ^ multiplicity p x) = normalize x"
    by (intro prod_prime_factors) auto
  also have "(\<Prod>p\<in>prime_factors x. p ^ multiplicity p x) = (\<Prod>p\<in>prime_factors x. p)"
    using assms by (intro prod.cong refl) (auto simp: squarefree_factorial_semiring')
  finally show ?thesis by simp
qed
(* END TODO *)

end