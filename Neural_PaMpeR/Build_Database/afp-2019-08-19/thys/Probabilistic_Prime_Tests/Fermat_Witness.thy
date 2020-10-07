(*
  File:     Fermat_Witness.thy
  Authors:  Daniel Stüwe

  Fermat witnesses as used in Fermat's test
*)
section \<open>Fermat Witnesses\<close>
theory Fermat_Witness
  imports Euler_Witness Carmichael_Numbers
begin

definition divide_out :: "'a :: factorial_semiring \<Rightarrow> 'a \<Rightarrow> 'a \<times> nat" where
  "divide_out p x = (x div p ^ multiplicity p x, multiplicity p x)"

lemma fst_divide_out [simp]: "fst (divide_out p x) = x div p ^ multiplicity p x"
  and snd_divide_out [simp]: "snd (divide_out p x) = multiplicity p x"
  by (simp_all add: divide_out_def)


function divide_out_aux :: "'a :: factorial_semiring \<Rightarrow> 'a \<times> nat \<Rightarrow> 'a \<times> nat" where
  "divide_out_aux p (x, acc) =
     (if x = 0 \<or> is_unit p \<or> \<not>p dvd x then (x, acc) else divide_out_aux p (x div p, acc + 1))"
  by auto
termination proof (relation "measure (\<lambda>(p, x, _). multiplicity p x)")
  fix p x :: 'a and acc :: nat
  assume "\<not>(x = 0 \<or> is_unit p \<or> \<not>p dvd x)"
  thus "((p, x div p, acc + 1), p, x, acc) \<in> measure (\<lambda>(p, x, _). multiplicity p x)"
    by (auto elim!: dvdE simp: multiplicity_times_same)
qed auto

lemmas [simp del] = divide_out_aux.simps

lemma divide_out_aux_correct:
  "divide_out_aux p z = (fst z div p ^ multiplicity p (fst z), snd z + multiplicity p (fst z))"
proof (induction p z rule: divide_out_aux.induct)
  case (1 p x acc)
  show ?case
  proof (cases "x = 0 \<or> is_unit p \<or> \<not>p dvd x")
    case False
    have "x div p div p ^ multiplicity p (x div p) = x div p ^ multiplicity p x"
      using False
      by (subst dvd_div_mult2_eq [symmetric])
         (auto elim!: dvdE simp: multiplicity_dvd multiplicity_times_same)
    with False show ?thesis using 1
      by (subst divide_out_aux.simps)
         (auto elim: dvdE simp: multiplicity_times_same multiplicity_unit_left
                                not_dvd_imp_multiplicity_0)
  qed (auto simp: divide_out_aux.simps multiplicity_unit_left not_dvd_imp_multiplicity_0)
qed

lemma divide_out_code [code]: "divide_out p x = divide_out_aux p (x, 0)"
  by (simp add: divide_out_aux_correct divide_out_def)

lemma multiplicity_code [code]: "multiplicity p x = snd (divide_out_aux p (x, 0))"
  by (simp add: divide_out_aux_correct)

(* TODO Move *)
lemma multiplicity_times_same_power:
  assumes "x \<noteq> 0" "\<not>is_unit p" "p \<noteq> 0"
  shows   "multiplicity p (p ^ k * x) = multiplicity p x + k"
  using assms by (induction k) (simp_all add: multiplicity_times_same mult.assoc)

lemma divide_out_unique_nat:
  fixes n :: nat
  assumes "\<not>is_unit p" "p \<noteq> 0" "\<not>p dvd m" and "n = p ^ k * m"
  shows   "m = n div p ^ multiplicity p n" and "k = multiplicity p n"
proof -
  from assms have "n \<noteq> 0" by (intro notI) auto
  thus *: "k = multiplicity p n"
    using assms by (auto simp: assms multiplicity_times_same_power not_dvd_imp_multiplicity_0)
  from assms show "m = n div p ^ multiplicity p n"
    unfolding * [symmetric] by auto
qed


context
  fixes a n :: nat 
begin

definition "fermat_liar \<longleftrightarrow> [a^(n-1) = 1] (mod n)"
definition "fermat_witness \<longleftrightarrow> [a^(n-1) \<noteq> 1] (mod n)"

definition "strong_fermat_liar \<longleftrightarrow>
              (\<forall>k m. odd m \<longrightarrow> n - 1 = 2^k * m \<longrightarrow>
                 [a^m = 1](mod n) \<or> (\<exists>i \<in> {0..< k}. [a^(2 ^ i * m) = n-1] (mod n)))"

definition "strong_fermat_witness \<longleftrightarrow> \<not> strong_fermat_liar"

lemma fermat_liar_witness_of_composition[iff]:
  "\<not>fermat_liar = fermat_witness"
  "\<not>fermat_witness = fermat_liar"
  unfolding fermat_liar_def and fermat_witness_def
  by simp_all

lemma strong_fermat_liar_code [code]:
  "strong_fermat_liar \<longleftrightarrow> 
     (let (m, k) = divide_out 2 (n - 1)
      in [a^m = 1](mod n) \<or> (\<exists>i \<in> {0..< k}. [a^(2 ^ i * m) = n-1] (mod n)))"
  (is "?lhs = ?rhs")
proof (cases "n > 1")
  case True
  define m where "m = (n - 1) div 2 ^ multiplicity 2 (n - 1)"
  define k where "k = multiplicity 2 (n - 1)"
  have mk: "odd m \<and> n - 1 = 2 ^ k * m"
    using True multiplicity_decompose[of "n - 1" 2] multiplicity_dvd[of 2 "n - 1"]
    by (auto simp: m_def k_def)
  show ?thesis
  proof
    assume ?lhs
    hence "[a^m = 1] (mod n) \<or> (\<exists>i \<in> {0..< k}. [a^(2 ^ i * m) = n-1] (mod n))"
      using True mk by (auto simp: divide_out_def strong_fermat_liar_def)
    thus ?rhs by (auto simp: Let_def divide_out_def m_def k_def)
  next
    assume ?rhs
    thus ?lhs using divide_out_unique_nat[of 2]
      by (auto simp: strong_fermat_liar_def divide_out_def)
  qed
qed (auto simp: strong_fermat_liar_def divide_out_def)


context
  assumes * : "a \<in> {1 ..< n}"
begin

lemma strong_fermat_witness_iff:
  "strong_fermat_witness =
     (\<exists>k m. odd m \<and> n - 1 = 2 ^ k * m \<and> [a ^ m \<noteq> 1] (mod n) \<and> 
            (\<forall>i\<in>{0..<k}. [a ^ (2 ^ i * m) \<noteq> n-1] (mod n)))"
  unfolding strong_fermat_witness_def strong_fermat_liar_def
  by blast

lemma not_coprime_imp_witness: "\<not>coprime a n \<Longrightarrow> fermat_witness"
  using * lucas_coprime_lemma[of "n-1" a n]
  by (auto simp: fermat_witness_def)

corollary liar_imp_coprime: "fermat_liar \<Longrightarrow> coprime a n"
  using not_coprime_imp_witness fermat_liar_witness_of_composition by blast

lemma fermat_witness_imp_strong_fermat_witness:
  assumes "1 < n" "fermat_witness"
  shows "strong_fermat_witness"
proof -
  from \<open>fermat_witness\<close> have "[a^(n-1) \<noteq> 1] (mod n)"
    unfolding fermat_witness_def .

  obtain k m where "odd m" and n: "n - 1 = 2 ^ k * m"
    using * by (auto intro: multiplicity_decompose'[of "(n-1)" 2])

  moreover have "[a ^ m \<noteq> 1] (mod n)"
    using \<open>[a^(n-1) \<noteq> 1] (mod n)\<close> n ord_divides by auto

  moreover {
    fix i :: nat
    assume "i \<in> {0..<k}"
    hence "i \<le> k - 1" "0 < k" by auto
    then have "[a ^ (2 ^ i * m) \<noteq> n - 1] (mod n)" "[a ^ (2 ^ i * m) \<noteq> 1] (mod n)"
    proof(induction i rule: inc_induct)
      case base
        have * :"a ^ (n - 1) = (a ^ (2 ^ (k - 1) * m))\<^sup>2"
          using \<open>0 < k\<close> n semiring_normalization_rules(27)[of "2 :: nat" "k - 1"]
          by (auto simp flip: power_even_eq simp add: algebra_simps)
  
        case 1
        from * show ?case 
          using \<open>[a^(n-1) \<noteq> 1] (mod n)\<close> and square_minus_one_cong_one[OF \<open>1 < n\<close>] by auto
       
        case 2
        from * show ?case using n \<open>[a^(n-1) \<noteq> 1] (mod n)\<close> and square_one_cong_one by metis
    next
      case (step q)
      then have
        IH2: "[a ^ (2 ^ Suc q * m) \<noteq> 1] (mod n)" using \<open>0 < k\<close> by blast+

      have * : "a ^ (2 ^ Suc q * m) = (a ^ (2 ^ q * m))\<^sup>2"
        by (auto simp flip: power_even_eq simp add: algebra_simps)

      case 1
      from * show ?case using IH2 and square_minus_one_cong_one[OF \<open>1 < n\<close>] by auto

      case 2
      from * show ?case using IH2 and square_one_cong_one by metis
    qed
  }

  ultimately show ?thesis unfolding strong_fermat_witness_iff by blast
qed

corollary strong_fermat_liar_imp_fermat_liar:
  assumes "1 < n" "strong_fermat_liar"
  shows  "fermat_liar" 
    using fermat_witness_imp_strong_fermat_witness assms
    and fermat_liar_witness_of_composition strong_fermat_witness_def
    by blast

lemma euler_liar_is_fermat_liar:
  assumes "1 < n" "euler_liar a n" "coprime a n" "odd n"
  shows "fermat_liar"
proof -
  have "[Jacobi a n = a ^ ((n - 1) div 2)] (mod n)"
    using \<open>euler_liar a n\<close> unfolding euler_witness_def by simp

  hence "[(Jacobi a n)^2 = (a ^ ((n - 1) div 2))^2] (mod n)"
    by (simp add: cong_pow)

  moreover have "Jacobi a n \<in> {1, -1}"
    using Jacobi_values Jacobi_eq_0_iff_not_coprime[of n] \<open>coprime a n\<close> \<open>1 < n\<close>
    by force

  ultimately have "[1 = (a ^ ((n - 1) div 2))^2] (mod n)"
    using cong_int_iff by force

  also have "(a ^ ((n - 1) div 2))^2 = a ^ (n - 1)"
    using \<open>odd n\<close> by (simp flip: power_mult)

  finally show ?thesis 
    using cong_sym fermat_liar_def 
    by blast
qed

corollary fermat_witness_is_euler_witness:
  assumes "1 < n" "fermat_witness" "coprime a n" "odd n"
  shows "euler_witness a n"
  using assms euler_liar_is_fermat_liar fermat_liar_witness_of_composition
  by blast

end
end

lemma one_is_fermat_liar[simp]: "1 < n \<Longrightarrow> fermat_liar 1 n"
  using fermat_liar_def by auto

lemma one_is_strong_fermat_liar[simp]: "1 < n \<Longrightarrow> strong_fermat_liar 1 n"
  using strong_fermat_liar_def by auto

lemma prime_imp_fermat_liar:
  "prime p \<Longrightarrow> a \<in> {1 ..< p} \<Longrightarrow> fermat_liar a p"
  unfolding fermat_liar_def
  using fermat_theorem and nat_dvd_not_less by simp

lemma not_Carmichael_numberD:
  assumes "\<not>Carmichael_number n" "\<not>prime n"  and "1 < n"
  shows "\<exists> a \<in> {2 ..< n} . fermat_witness a n \<and> coprime a n"
proof -
  obtain a where "coprime a n" "[a^(n-1) \<noteq> 1] (mod n)"
    using assms unfolding Carmichael_number_def by blast

  moreover from this and \<open>1 < n\<close> have "a mod n \<in> {1..<n}"
    by (cases "a = 0") (auto intro! : gre1I_nat)

  ultimately have "a mod n \<in> {1 ..< n}"  "coprime (a mod n) n" "[(a mod n)^(n-1) \<noteq> 1] (mod n)"
    using \<open>1 < n\<close> by simp_all

  hence "fermat_witness (a mod n) n"
    using fermat_witness_def by blast

  hence "1 \<noteq> (a mod n)"
    using \<open>1 < n\<close> \<open>(a mod n) \<in> {1 ..< n}\<close> and one_is_fermat_liar fermat_liar_witness_of_composition(1)
    by metis

  thus ?thesis
    using \<open>fermat_witness (a mod n) n\<close> \<open>coprime (a mod n) n\<close> \<open>(a mod n) \<in> {1..<n}\<close>
    by fastforce
qed

proposition prime_imp_strong_fermat_witness:
  fixes p :: nat
  assumes "prime p" "2 < p" "a \<in> {1 ..< p}"
  shows "strong_fermat_liar a p"
proof -
  { fix k m :: nat
    define j where "j \<equiv> LEAST k. [a ^ (2^k * m) = 1] (mod p)"

    have "[a ^ (p - 1) = 1] (mod p)"
      using fermat_theorem[OF \<open>prime p\<close>, of a] \<open>a \<in> {1 ..< p}\<close> by force

    moreover assume "odd m" and n: "p - 1 = 2 ^ k * m"

    ultimately have "[a ^ (2 ^ k * m) = 1] (mod p)" by simp

    moreover assume "[a ^ m \<noteq> 1] (mod p)"
    then have "0 < x" if "[a ^ (2 ^ x * m) = 1] (mod p)" for x
      using that by (auto intro: gr0I)

    ultimately have "0 < j" "j \<le> k" "[a ^ (2 ^ j * m) = 1] (mod p)"
      using LeastI2[of _ k "(<) 0"] Least_le[of _ k] LeastI[of _ k]
      by (simp_all add: j_def)

    moreover from this have "[a ^ (2^(j-1) * m) \<noteq> 1] (mod p)"
      using not_less_Least[of "j - 1" "\<lambda>k. [a ^ (2^k * m) = 1] (mod p)"]
      unfolding j_def by simp

    moreover have "a ^ (2 ^ (j - 1) * m) * a ^ (2 ^ (j - 1) * m) = a ^ (2 ^ j * m)"
      using \<open>0 < j\<close>
      by (simp add: algebra_simps semiring_normalization_rules(27) flip: power2_eq_square power_even_eq)

    ultimately have "(j-1)\<in>{0..<k} " "[a ^ (2 ^ (j-1) * m) = p - 1] (mod p)"
      using cong_square_alt[OF \<open>prime p\<close>, of "a ^ (2 ^ (j-1) * m)"]
      by simp_all
  }

  then show ?thesis unfolding strong_fermat_liar_def by blast
qed

lemma ignore_one:
  fixes P :: "_ \<Rightarrow> nat \<Rightarrow> bool"
  assumes "P 1 n" "1 < n"
  shows "card {a \<in> {1..<n}. P a n} = 1 + card {a. 2 \<le> a \<and> a < n \<and> P a n}"
proof -
  have "insert 1 {a. 2 \<le> a \<and> a < n \<and> P a n} = {a. 1 \<le> a \<and> a < n \<and> P a n}"
    using assms by auto

  moreover have "card (insert 1 {a. 2 \<le> a \<and> a < n \<and> P a n}) = Suc (card {a. 2 \<le> a \<and> a < n \<and> P a n})"
    using card_insert_disjoint by auto
  
  ultimately show ?thesis by force
qed

text \<open>Proofs in the following section are inspired by \cite{Cornwell, MillerRabinTest, lecture_notes}.\<close>

proposition not_Carmichael_number_imp_card_fermat_witness_bound:
  fixes n :: nat
  assumes "\<not>prime n" "\<not>Carmichael_number n" "odd n" "1 < n"
  shows "(n-1) div 2 < card {a \<in> {1 ..< n}. fermat_witness a n}"
    and "(card {a. 2 \<le> a \<and> a < n \<and> strong_fermat_liar a n}) < real (n - 2) / 2"
    and "(card {a. 2 \<le> a \<and> a < n \<and> fermat_liar a n}) < real (n - 2) / 2"
proof -
  define G where "G = Residues_Mult n"
  interpret residues_mult_nat n G
    by unfold_locales (use \<open>n > 1\<close> in \<open>simp_all only: G_def\<close>)
  define h where "h \<equiv> \<lambda>a. a ^ (n - 1) mod n"
  define ker where "ker = kernel G (G\<lparr>carrier := h ` carrier G\<rparr>) h"

  have "finite ker" by (auto simp: ker_def kernel_def)
  moreover have "1 \<in> ker" using \<open>n > 1\<close> by (auto simp: ker_def kernel_def h_def)
  ultimately have [simp]: "card ker > 0"
    by (subst card_gt_0_iff) (auto simp: ker_def kernel_def h_def)

  have totatives_eq: "totatives n = {k\<in>{1..<n}. coprime k n}"
    using totatives_less[of _ n] \<open>n > 1\<close> by (force simp: totatives_def)
  have ker_altdef: "ker = {a \<in> {1..<n}. fermat_liar a n}"
    unfolding ker_def fermat_liar_def carrier_eq kernel_def totatives_eq using \<open>n > 1\<close>
    by (force simp: h_def cong_def intro: coprimeI_power_mod)

  have h_is_hom: "h \<in> hom G G" 
    unfolding hom_def using nat_pow_closed
    by (auto simp: h_def power_mult_distrib mod_simps)
  then interpret h: group_hom G G h
    by unfold_locales

  obtain a where a: "a \<in> {2..<n}" "fermat_witness a n" "coprime a n" 
    using assms power_one not_Carmichael_numberD by blast

  have "h a \<noteq> 1" using a by (auto simp: fermat_witness_def cong_def h_def)
  hence "2 \<le> card {1, h a}" by simp
  also have "\<dots> \<le> card (h ` carrier G)"
  proof (intro card_mono; safe?)
    from \<open>n > 1\<close> have "1 = h 1" by (simp add: h_def)
    also have "\<dots> \<in> h ` carrier G" by (intro imageI) (use \<open>n > 1\<close> in auto)
    finally show "1 \<in> h ` carrier G" .
  next
    show "h a \<in> h ` carrier G"
      using a by (intro imageI) (auto simp: totatives_def)
  qed auto
  also have "\<dots> * card ker = order G"
    using homomorphism_thm_order[OF h.group_hom_axioms] by (simp add: ker_def order_def)
  also have "order G < n - 1"
    using totient_less_not_prime[of n] assms by (simp add: order_eq)
  finally have "card ker < (n - 1) div 2"
    using \<open>odd n\<close> by (auto elim!: oddE)

  have "(n - 1) div 2 < (n - 1) - card ker"
    using \<open>card ker < (n - 1) div 2\<close> by linarith
  also have "\<dots> = card ({1..<n} - ker)"
    by (subst card_Diff_subset) (auto simp: ker_altdef)
  also have "{1..<n} - ker = {a \<in> {1..<n}. fermat_witness a n}"
    by (auto simp: fermat_witness_def fermat_liar_def ker_altdef)
  finally show "(n - 1) div 2 < card {a \<in> {1..<n}. fermat_witness a n}" .

  have "card {a. 2 \<le> a \<and> a < n \<and> fermat_liar a n} \<le> card (ker - {1})"
    by (intro card_mono) (auto simp: ker_altdef fermat_liar_def fermat_witness_def)
  also have "\<dots> = card ker - 1"
    using \<open>n > 1\<close> by (subst card_Diff_subset) (auto simp: ker_altdef fermat_liar_def)
  also have "\<dots> < (n - 2) div 2"
    using \<open>card ker < (n - 1) div 2\<close> \<open>odd n\<close> \<open>card ker > 0\<close> by linarith
  finally show *: "card {a. 2 \<le> a \<and> a < n \<and> fermat_liar a n} < real (n - 2) / 2"
    by simp

  have "card {a. 2 \<le> a \<and> a < n \<and> strong_fermat_liar a n} \<le>
          card {a. 2 \<le> a \<and> a < n \<and> fermat_liar a n}"
    by (intro card_mono) (auto intro!: strong_fermat_liar_imp_fermat_liar)
  moreover note *
  ultimately show "card {a. 2 \<le> a \<and> a < n \<and> strong_fermat_liar a n} < real (n - 2) / 2"
    by simp
qed


proposition Carmichael_number_imp_lower_bound_on_strong_fermat_witness:
  fixes n :: nat
  assumes Carmichael_number: "Carmichael_number n"
  shows "(n - 1) div 2 < card {a \<in> {1..<n}. strong_fermat_witness a n}"
    and "real (card {a . 2 \<le> a \<and> a < n \<and> strong_fermat_liar a n}) < real (n - 2) / 2"
proof -
  from assms have "n > 3" by (intro Carmichael_number_gt_3)
  hence "n - 1 \<noteq> 0" "\<not>is_unit (2 :: nat)" by auto
  obtain k m where "odd m" and n_less: "n - 1 = 2 ^ k * m"
    using multiplicity_decompose'[OF \<open>n - 1 \<noteq> 0\<close> \<open>\<not>is_unit (2::nat)\<close>] by metis

  obtain p l where n: "n = p * l" and "prime p" "\<not> p dvd l" "2 < l"
    using Carmichael_number_imp_squarefree_alt[OF Carmichael_number] 
    by blast

  then have "coprime p l" using prime_imp_coprime_nat by blast

  have "odd n" using Carmichael_number_odd Carmichael_number by simp

  have "2 < n" using \<open>n > 3\<close> \<open>odd n\<close> by presburger

  note prime_gt_1_nat[OF \<open>prime p\<close>]

  have "2 < p" using \<open>odd n\<close> n \<open>prime p\<close> prime_ge_2_nat
               and dvd_triv_left le_neq_implies_less by blast 

  let ?P = "\<lambda> k. (\<forall> a. coprime a p \<longrightarrow> [a^(2^k * m) = 1] (mod p))"
  define j where "j \<equiv> LEAST k. ?P k"

  define H where "H \<equiv> {a \<in> {1..<n} . coprime a n \<and> ([a^(2^(j-1) * m) = 1] (mod n) \<or>
                                                     [a^(2^(j-1) * m) = n - 1] (mod n))}"

  have k : "\<forall>a. coprime a n \<longrightarrow> [a ^ (2 ^ k * m) = 1] (mod n)"
    using Carmichael_number unfolding Carmichael_number_def n_less by blast

  obtain k' m' where "odd m'" and p_less: "p - 1 = 2 ^ k' * m'"
    using \<open>1 < p\<close> by (auto intro: multiplicity_decompose'[of "(p-1)" 2])

  have "p - 1 dvd n - 1"
    using Carmichael_number_imp_dvd[OF Carmichael_number \<open>prime p\<close>] \<open>n = p * l\<close>
    by fastforce

  then have "p - 1 dvd 2 ^ k' * m"
    unfolding n_less p_less
    using \<open>odd m\<close> \<open>odd m'\<close>
      and coprime_dvd_mult_left_iff[of "2^k'" m "2^k"] coprime_dvd_mult_right_iff[of m' "2^k" m]
    by auto

  have k': "\<forall>a. coprime a p \<longrightarrow> [a ^ (2 ^ k' * m) = 1] (mod p)"
  proof safe
    fix a
    assume "coprime a p"
    hence "\<not> p dvd a" using p_coprime_right_nat[OF \<open>prime p\<close>] by simp

    have "[a ^ (2 ^ k' * m') = 1] (mod p)"
     unfolding p_less[symmetric]
      using fermat_theorem \<open>prime p\<close> \<open>\<not> p dvd a\<close> by blast

    then show "[a ^ (2 ^ k' * m) = 1] (mod p)"
      using \<open>p - 1 dvd 2 ^ k' * m\<close>
      unfolding p_less n_less
      by (meson dvd_trans ord_divides)
  qed

  have j_prop: "[a^(2^j * m) = 1] (mod p)" if "coprime a p" for a
    using that LeastI[of ?P k', OF k', folded j_def] cong_modulus_mult coprime_mult_right_iff 
    unfolding j_def n by blast

  have j_least: "[a^(2^i * m) = 1] (mod p)" if "coprime a p" "j \<le> i" for a i
  proof -
    obtain c where i: "i = j + c" using le_iff_add[of j i] \<open>j \<le> i\<close> by blast

    then have "[a ^ (2 ^ i * m) = a ^ (2 ^ (j + c) * m)] (mod p)" by simp
    
    also have "[a ^ (2 ^ (j + c) * m) = (a ^ (2 ^ j * m)) ^ (2 ^ c)] (mod p)"
      by (simp flip: power_mult add: algebra_simps power_add)
    
    also note j_prop[OF \<open>coprime a p\<close>]
   
    also have "[1 ^ (2 ^ c) = 1] (mod p)" by simp
    
    finally show ?thesis .
  qed

  have neq_p: "[p - 1 \<noteq> 1](mod p)"
    using \<open>2 < p\<close> and cong_less_modulus_unique_nat[of "p-1" 1 p]
    by linarith

  have "0 < j"
  proof (rule LeastI2[of ?P k', OF k', folded j_def], rule gr0I)
    fix x
    assume "\<forall>a. coprime a p \<longrightarrow> [a ^ (2 ^ x * m) = 1] (mod p)"
    then have "[(p - 1) ^ (2 ^ x * m) = 1] (mod p)"
      using coprime_diff_one_left_nat[of p]  prime_gt_1_nat[OF \<open>prime p\<close>]
      by simp
    
    moreover assume "x = 0"
    hence "[(p-1)^(2^x*m) = p - 1](mod p)"
      using \<open>odd m\<close> odd_pow_cong[OF _ \<open>odd m\<close>, of p] prime_gt_1_nat[OF \<open>prime p\<close>]
      by auto

    ultimately show False
      using \<open>[p - 1 \<noteq> 1] (mod p)\<close> by (simp add: cong_def)
  qed

  then have "j - 1 < j" by simp

  then obtain x where "coprime x p" "[x^(2^(j-1) * m) \<noteq> 1] (mod p)"
    using not_less_Least[of "j - 1" ?P, folded j_def] unfolding j_def by blast

  define G where "G = Residues_Mult n"
  interpret residues_mult_nat n G
    by unfold_locales (use \<open>n > 3\<close> in \<open>simp_all only: G_def\<close>)

  have H_subset: "H \<subseteq> carrier G" unfolding H_def by (auto simp: totatives_def)

  from \<open>n > 3\<close> have \<open>n > 1\<close> by simp
  interpret H: subgroup H G
  proof (rule subgroupI, goal_cases)
    case 1
    then show ?case using H_subset .
  next
    case 2
    then show ?case unfolding H_def using \<open>1 < n\<close> by force
  next
    case (3 a)
    define y where "y = inv\<^bsub>G\<^esub> a"

    then have "y \<in> carrier G"
      using H_subset \<open>a \<in> H\<close> by (auto simp del: carrier_eq)

    then have "1 \<le> y" "y < n" "coprime y n"
      using totatives_less[of y n] \<open>n > 3\<close> by (auto simp: totatives_def)

    moreover have "[y ^ (2 ^ (j - Suc 0) * m) = Suc 0] (mod n)" 
      if "[y ^ (2 ^ (j - Suc 0) * m) \<noteq> n - Suc 0] (mod n)"
    proof -
      from \<open>a \<in> H\<close> have "[a * y = 1] (mod n)"
        using H_subset r_inv[of a] y_def by (auto simp: cong_def)
      hence "[(a * y) ^ (2 ^ (j - 1) * m) = 1 ^ (2 ^ (j - 1) * m)] (mod n)"
        by (intro cong_pow)
      hence "[(a * y) ^ (2 ^ (j - 1) * m) = 1] (mod n)"
        by simp
      hence * : "[a ^ (2 ^ (j - 1) * m) * y ^ (2 ^ (j - 1) * m) = 1] (mod n)"
          by (simp add: power_mult_distrib) 
      from \<open>a \<in> H\<close> have "1 \<le> a" "a < n" "coprime a n"
        unfolding H_def by auto

      have "[a ^ (2 ^ (j - 1) * m) = 1] (mod n) \<or> [a ^ (2 ^ (j - 1) * m) = n - 1] (mod n)"
        using \<open>a \<in> H\<close> by (auto simp: H_def)
      thus ?thesis
      proof
        note *
        also assume "[a ^ (2 ^ (j - 1) * m) = 1] (mod n)"
        finally show ?thesis by simp
      next
        assume "[a ^ (2 ^ (j - 1) * m) = n - 1] (mod n)"
        then have "[y ^ (2 ^ (j - 1) * m) = n - 1] (mod n)" 
          using minus_one_cong_solve[OF \<open>1 < n\<close>] * \<open>coprime a n\<close> \<open>coprime y n \<close>coprime_power_left_iff
          by blast+
        thus ?thesis using that by simp
      qed
    qed

    ultimately show ?case using \<open>a \<in> H\<close> unfolding H_def y_def by auto
  next
    case (4 a b)
    hence "a \<in> totatives n" "b \<in> totatives n"
      by (auto simp: H_def totatives_def)
    hence "a * b mod n \<in> totatives n"
      using m_closed[of a b] by simp
    hence "a * b mod n \<in> {1..<n}" "coprime (a * b) n"
      using totatives_less[of "a * b" n] \<open>n > 3\<close> by (auto simp: totatives_def)

    moreover define x y where "x = a ^ (2 ^ (j - 1) * m)" and "y = b ^ (2 ^ (j - 1) * m)"
    have "[x * y = 1] (mod n) \<or> [x * y = n - 1] (mod n)"
    proof -
      have *: "x mod n \<in> {1, n - 1}" "y mod n \<in> {1, n - 1}"
        using 4 by (auto simp: H_def x_def y_def cong_def)
      have "[x * y = (x mod n) * (y mod n)] (mod n)"
        by (intro cong_mult) auto
      moreover have "((x mod n) * (y mod n)) mod n \<in> {1, n - 1}"
        using * square_minus_one_cong_one'[OF \<open>1 < n\<close>] \<open>n > 1\<close> by (auto simp: cong_def)
      ultimately show ?thesis using \<open>n > 1\<close> by (simp add: cong_def mod_simps)
    qed

    ultimately show ?case by (auto simp: H_def x_def y_def power_mult_distrib)
  qed

  { obtain a where "[a = x] (mod p)" "[a = 1] (mod l)" "a < p * l"
      using binary_chinese_remainder_unique_nat[of p l x 1]
        and \<open>\<not> p dvd l\<close> \<open>prime p\<close> prime_imp_coprime_nat
      by auto
  
    moreover have "coprime a p"
      using \<open>coprime x p\<close> cong_imp_coprime[OF cong_sym[OF \<open>[a = x] (mod p)\<close>]] coprime_mult_right_iff
      unfolding n by blast
  
    moreover have "coprime a l" 
      using coprime_1_left cong_imp_coprime[OF cong_sym[OF \<open>[a = 1] (mod l)\<close>]]
      by blast

    moreover from \<open>prime p\<close> and \<open>coprime a p\<close> have "a > 0"
      by (intro Nat.gr0I) auto
 
    ultimately have "a \<in> carrier G"
      using \<open>2 < l\<close> by (auto intro: gre1I_nat simp: n totatives_def)
  
    have "[a ^ (2^(j-1) * m) \<noteq> 1] (mod p)"
      using \<open>[x^(2^(j-1) * m) \<noteq> 1] (mod p)\<close> \<open>[a = x] (mod p)\<close> and cong_trans cong_pow cong_sym
      by blast

    then have "[a ^ (2^(j-1) * m) \<noteq> 1] (mod n)"
      using cong_modulus_mult_nat n by fast

    moreover 
    have "[a ^ (2 ^ (j - Suc 0) * m) \<noteq> n - 1] (mod n)"
    proof -
      have "[a ^ (2 ^ (j - 1) * m) = 1] (mod l)"
      using cong_pow[OF \<open>[a = 1] (mod l)\<close>] by auto
  
      moreover have "Suc 0 \<noteq> (n - Suc 0) mod l"
        using n \<open>2 < l\<close> \<open>odd n\<close>
        by (metis mod_Suc_eq mod_less mod_mult_self2_is_0 numeral_2_eq_2 odd_Suc_minus_one zero_neq_numeral)

      then have "[1 \<noteq> n - 1] (mod l)"
          using \<open>2 < l\<close> \<open>odd n\<close> unfolding cong_def by simp

      moreover have "l \<noteq> Suc 0" using \<open>2 < l\<close> by simp

      ultimately have "[a ^ (2 ^ (j - Suc 0) * m) \<noteq> n - 1] (mod l)"
        by (auto simp add: cong_def n mod_simps dest: cong_modulus_mult_nat)

      then show ?thesis
        using cong_modulus_mult_nat mult.commute n by metis
    qed

    ultimately have "a \<notin> H" unfolding H_def by auto
  
    hence "H \<subset> carrier (G)"
      using H_subset subgroup.mem_carrier and \<open>a \<in> carrier (G)\<close> 
      by fast
  }

  have "card H \<le> order G div 2"
    by (intro proper_subgroup_imp_bound_on_card) (use \<open>H \<subset> carrier G\<close> H.is_subgroup in \<open>auto\<close>)
  also from assms have "\<not>prime n" by (auto dest: Carmichael_number_not_prime)
  hence "order G div 2 < (n - 1) div 2"
    using totient_less_not_prime[OF \<open>\<not> prime n\<close> \<open>1 < n\<close>] \<open>odd n\<close>
    by (auto simp add: order_eq elim!: oddE)
  finally have "card H < (n - 1) div 2" .

  {
    { fix a
      assume "1 \<le> a" "a < n"
      hence "a \<in> {1..<n}" by simp
  
      assume "coprime a n"
      then have "coprime a p" 
      unfolding n by simp
                 
      assume "[a ^ (2 ^ (j - 1) * m) \<noteq> 1] (mod n)" 
      hence "[a ^ m \<noteq> 1] (mod n)"
        by (metis dvd_trans dvd_triv_right ord_divides)
    
      moreover assume "strong_fermat_liar a n"
  
      ultimately obtain i where "i \<in> {0 ..< k}" "[a^(2^i * m) = n-1](mod n)"
        unfolding strong_fermat_liar_def using \<open>odd m\<close> n_less by blast
  
      then have "[a ^ (2 ^ i * m) = n - 1] (mod p)"
        unfolding n using cong_modulus_mult_nat by blast
  
      moreover have "[n - 1 \<noteq> 1] (mod p)"
      proof(subst cong_altdef_nat, goal_cases)
        case 1
        then show ?case using \<open>1 < n\<close> by linarith
      next
        case 2
        have "\<not> p dvd 2" using \<open>2 < p\<close> by (simp add: nat_dvd_not_less)

        moreover have "2 \<le> n" using \<open>1 < n\<close> by linarith

        moreover have "p dvd n" using n by simp

        ultimately have "\<not> p dvd n - 2" using dvd_diffD1 by blast
        
        then show ?case by (simp add: numeral_2_eq_2)
      qed

      ultimately have "[a ^ (2 ^ i * m) \<noteq> Suc 0] (mod p)" using cong_sym by (simp add: cong_def)
  
      then have "i < j" using j_least[OF \<open>coprime a p\<close>, of i] by force
  
      have "[(a ^ (2 ^ Suc i * m)) = 1] (mod n)"
        using square_minus_one_cong_one[OF \<open>1 < n\<close> \<open>[a^(2^i * m) = n-1](mod n)\<close>]
        by (simp add: power2_eq_square power_mult power_mult_distrib)
  
      { assume "i < j - 1"
  
        have "(2 :: nat) ^ (j - Suc 0) = ((2 ^ i) * 2 ^ (j - Suc i))"
          unfolding power_add[symmetric] using \<open>i < j - 1\<close> by simp
  
        then have "[a ^ (2 ^ (j - 1) * m) = (a ^ (2 ^ i * m)) ^ (2^(j - 1 - i))] (mod n)"
          by (auto intro!: cong_pow_I simp flip: power_mult simp add: algebra_simps power_add)
          
        also note \<open>[a ^ (2 ^ i * m) = n - 1] (mod n)\<close>
  
        also have "[(n - 1) ^ (2^(j - 1 - i)) = 1] (mod n) "
          using \<open>1 < n\<close> \<open>i < j - 1\<close> using even_pow_cong by auto
  
        finally have False
          using \<open>[a ^ (2 ^ (j - 1) * m) \<noteq> 1] (mod n)\<close>
          by blast
      }

      hence "i = j - 1" using \<open>i < j\<close> by fastforce
  
      hence "[a ^ (2 ^ (j - 1) * m) = n - 1] (mod n)" using \<open>[a^(2^i * m) = n-1](mod n)\<close> by simp
    }
  
    hence "{a \<in> {1..<n}. strong_fermat_liar a n} \<subseteq> H"
      using strong_fermat_liar_imp_fermat_liar[of _ n, OF _ \<open>1 < n\<close>]  liar_imp_coprime
      by (auto simp: H_def)
  }

  moreover have "finite H" unfolding H_def by auto

  ultimately have strong_fermat_liar_bounded: "card {a \<in> {1..<n}. strong_fermat_liar a n} < (n - 1) div 2 "
    using card_mono[of H] le_less_trans[OF _ \<open>card H < (n - 1) div 2\<close>] by blast

  moreover {
    have "{1..<n} - {a \<in> {1..<n}. strong_fermat_liar a n} = {a \<in> {1..<n}. strong_fermat_witness a n}"
      using strong_fermat_witness_def by blast
  
    then have "card {a \<in> {1..<n}. strong_fermat_witness a n} = (n-1) - card {a \<in> {1..<n}. strong_fermat_liar a n}"
      using card_Diff_subset[of "{a \<in> {1..<n}. strong_fermat_liar a n}" "{1..<n}"]
      by fastforce
  }
  
  ultimately show "(n - 1) div 2 < card {a \<in> {1..<n}. strong_fermat_witness a n}"
    by linarith

  show "real (card {a . 2 \<le> a \<and> a < n \<and> strong_fermat_liar a n}) < real (n - 2) / 2"
    using strong_fermat_liar_bounded ignore_one one_is_strong_fermat_liar \<open>1 < n\<close> 
    by simp
qed

corollary strong_fermat_witness_lower_bound:
  assumes "odd n" "n > 2" "\<not>prime n"
  shows   "card {a. 2 \<le> a \<and> a < n \<and> strong_fermat_liar a n} < real (n - 2) / 2"
  using Carmichael_number_imp_lower_bound_on_strong_fermat_witness(2)[of n]
        not_Carmichael_number_imp_card_fermat_witness_bound(2)[of n] assms
  by (cases "Carmichael_number n") auto

end