(*
  File:     Residues_Nat.thy
  Authors:  Daniel Stüwe, Manuel Eberl

  The multiplicative group of the ring of residues modulo n.
*)
section \<open>Residue Rings of Natural Numbers\<close>
theory Residues_Nat
  imports Algebraic_Auxiliaries
begin            

subsection \<open>The multiplicative group of residues modulo \<open>n\<close>\<close>

definition Residues_Mult :: "'a :: {linordered_semidom, euclidean_semiring} \<Rightarrow> 'a monoid" where
  "Residues_Mult p =
     \<lparr>carrier = {x \<in> {1..p} . coprime x p}, monoid.mult = \<lambda>x y. x * y mod p, one = 1\<rparr>"

locale residues_mult_nat =
  fixes n :: nat and G
  assumes n_gt_1: "n > 1"
  defines "G \<equiv> Residues_Mult n"
begin

lemma carrier_eq [simp]: "carrier G = totatives n"
  and mult_eq [simp]:    "(x \<otimes>\<^bsub>G\<^esub> y) = (x * y) mod n"
  and one_eq [simp]:     "\<one>\<^bsub>G\<^esub> = 1"
  by (auto simp: G_def Residues_Mult_def totatives_def)

lemma mult_eq': "(\<otimes>\<^bsub>G\<^esub>) = (\<lambda>x y. (x * y) mod n)"
  by (intro ext; simp)+

sublocale group G
proof(rule groupI, goal_cases)
  case (1 x y)
  from 1 show ?case using n_gt_1
    by (auto intro!: Nat.gr0I simp: coprime_commute coprime_dvd_mult_left_iff
                                    coprime_absorb_left nat_dvd_not_less totatives_def)
next
  case (5 x)
  hence "(\<exists>y. y \<ge> 0 \<and> y < n \<and> [x * y = Suc 0] (mod n))"
    using coprime_iff_invertible'_nat[of n x] n_gt_1
    by (auto simp: totatives_def)
  then obtain y where y: "y \<ge> 0" "y < n" "[x * y = Suc 0] (mod n)" by blast

  from \<open>[x * y = Suc 0] (mod n)\<close> have "gcd (x * y) n = 1"
    by (simp add: cong_gcd_eq)
  hence "coprime y n" by fastforce

  with y n_gt_1 show "\<exists>y\<in>carrier G. y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub>"
    by (intro bexI[of _ y]) (auto simp: totatives_def cong_def mult_ac intro!: Nat.gr0I)
qed (use n_gt_1 in \<open>auto simp: mod_simps algebra_simps totatives_less\<close>)

sublocale comm_group
  by unfold_locales (auto simp: mult_ac)

lemma nat_pow_eq [simp]: "x [^]\<^bsub>G\<^esub> (k :: nat) = (x ^ k) mod n"
  using n_gt_1 by (induction k) (simp_all add: mod_mult_left_eq mod_mult_right_eq mult_ac)

lemma nat_pow_eq': "([^]\<^bsub>G\<^esub>) = (\<lambda>x k. (x ^ k) mod n)"
  by (intro ext) simp

lemma order_eq: "order G = totient n"
  by (simp add: order_def totient_def)

lemma order_less: "\<not>prime n \<Longrightarrow> order G < n - 1"
  using totient_less_not_prime[of n] n_gt_1
  by (auto simp: order_eq)

lemma ord_residue_mult_group:
  assumes "a \<in> totatives n"
  shows   "local.ord a = Pocklington.ord n a"
proof (rule dvd_antisym)
  have "[a ^ local.ord a = 1] (mod n)"
    using pow_ord_eq_1[of a] assms by (auto simp: cong_def)
  thus "Pocklington.ord n a dvd local.ord a"
    by (subst (asm) ord_divides)
next
  show "local.ord a dvd Pocklington.ord n a"
    using assms Pocklington.ord[of a n] n_gt_1 pow_eq_id by (simp add: cong_def)
qed

end


subsection \<open>The ring of residues modulo \<open>n\<close>\<close>

definition Residues_nat :: "nat \<Rightarrow> nat ring" where
  "Residues_nat m = \<lparr>carrier = {0..<m}, monoid.mult = \<lambda>x y. (x * y) mod m, one = 1,
                     ring.zero = 0, add = \<lambda>x y. (x + y) mod m\<rparr>"

locale residues_nat =
  fixes n :: nat and R
  assumes n_gt_1: "n > 1"
  defines "R \<equiv> Residues_nat n"
begin

lemma carrier_eq [simp]: "carrier R = {0..<n}"
  and mult_eq [simp]: "x \<otimes>\<^bsub>R\<^esub> y = (x * y) mod n"
  and add_eq [simp]: "x \<oplus>\<^bsub>R\<^esub> y = (x + y) mod n"
  and one_eq [simp]: "\<one>\<^bsub>R\<^esub> = 1"
  and zero_eq [simp]: "\<zero>\<^bsub>R\<^esub> = 0"
  by (simp_all add: Residues_nat_def R_def)

lemma mult_eq': "(\<otimes>\<^bsub>R\<^esub>) = (\<lambda>x y. (x * y) mod n)"
  and add_eq': "(\<oplus>\<^bsub>R\<^esub>) = (\<lambda>x y. (x + y) mod n)"
  by (intro ext; simp)+

sublocale abelian_group R
proof(rule abelian_groupI, goal_cases)
  case (1 x y)
  then show ?case
    using n_gt_1
    by (auto simp: mod_simps algebra_simps simp flip: less_Suc_eq_le)
next
  case (6 x)
  { assume "x < n" "1 < n"
    hence "n - x \<in> {0..<n}" "((n - x) + x) mod n = 0" if "x \<noteq> 0"
      using that by auto
    moreover have "0 \<in> {0..<n}" "(0 + x) mod n = 0" if "x = 0"
      using that n_gt_1 by auto
    ultimately have "\<exists>y\<in>{0..<n}. (y + x) mod n = 0"
      by meson
  }

  with 6 show ?case using n_gt_1 by auto
qed (use n_gt_1 in \<open>auto simp add: mod_simps algebra_simps\<close>)

sublocale comm_monoid R
  using n_gt_1 by unfold_locales (auto simp: mult_ac mod_simps)

sublocale cring R
  by unfold_locales (auto simp: mod_simps algebra_simps)

lemma Units_eq: "Units R = totatives n"
proof safe
  fix x assume x: "x \<in> Units R"
  then obtain y where y: "[x * y = 1] (mod n)"
    using n_gt_1 by (auto simp: Units_def cong_def)
  hence "coprime x n"
    using cong_imp_coprime cong_sym coprime_1_left coprime_mult_left_iff by metis
  with x show "x \<in> totatives n" by (auto simp: totatives_def Units_def intro!: Nat.gr0I)
next
  fix x assume x: "x \<in> totatives n"
  then obtain y where "y < n" "[x * y = 1] (mod n)"
    using coprime_iff_invertible'_nat[of n x] by (auto simp: totatives_def)
  with x show "x \<in> Units R"
    using n_gt_1 by (auto simp: Units_def mult_ac cong_def totatives_less)
qed

sublocale units: residues_mult_nat n "units_of R"
proof unfold_locales
  show "units_of R \<equiv> Residues_Mult n"
    by (auto simp: units_of_def Units_eq Residues_Mult_def totatives_def Suc_le_eq mult_eq')
qed (use n_gt_1 in auto) 

lemma nat_pow_eq [simp]: "x [^]\<^bsub>R\<^esub> (k :: nat) = (x ^ k) mod n"
  using n_gt_1 by (induction k) (auto simp: mod_simps mult_ac)

lemma nat_pow_eq': "([^]\<^bsub>R\<^esub>) = (\<lambda>x k. (x ^ k) mod n)"
  by (intro ext) simp

end


subsection \<open>The ring of residues modulo a prime\<close>

locale residues_nat_prime =
  fixes p :: nat and R
  assumes prime_p: "prime p"
  defines "R \<equiv> Residues_nat p"
begin

sublocale residues_nat p R
  using prime_gt_1_nat[OF prime_p] by unfold_locales (auto simp: R_def)

lemma carrier_eq' [simp]: "totatives p = {0<..<p}"
  using prime_p by (auto simp: totatives_prime)

lemma order_eq: "order (units_of R) = p - 1"
  using prime_p by (simp add: units.order_eq totient_prime)

lemma order_eq' [simp]: "totient p = p - 1"
  using prime_p by (auto simp: totient_prime)

sublocale field R
proof (rule cring_fieldI)
  show "Units R = carrier R - {\<zero>\<^bsub>R\<^esub>}"
    by (subst Units_eq) (use prime_p in \<open>auto simp: totatives_prime\<close>)
qed

lemma residues_prime_cyclic: "\<exists>x\<in>{0<..<p}. {0<..<p} = {y. \<exists>i. y = x ^ i mod p}"
proof -
  from n_gt_1 have "{0..<p} - {0} = {0<..<p}" by auto
  thus ?thesis using finite_field_mult_group_has_gen by simp
qed

lemma residues_prime_cyclic': "\<exists>x\<in>{0<..<p}. units.ord x = p - 1"
proof -
  from residues_prime_cyclic obtain x
    where x: "x \<in> {0<..<p}" "{0<..<p} = {y. \<exists>i. y = x ^ i mod p}" by metis
  have "units.ord x = p - 1"
  proof (intro antisym)
    show "units.ord x \<le> p - 1"
      using units.ord_dvd_group_order[of x] x(1) by (auto simp: units.order_eq intro!: dvd_imp_le)
  next
    (* TODO FIXME: a bit ugly; could be simplified if we had a theory of finite cyclic rings *)
    have "p - 1 = card {0<..<p}" by simp
    also have "{0<..<p} = {y. \<exists>i. y = x ^ i mod p}" by fact
    also have "card \<dots> \<le> card ((\<lambda>i. x ^ i mod p) ` {..<units.ord x})"
    proof (intro card_mono; safe?)
      fix j :: nat
      have "j = units.ord x * (j div units.ord x) + (j mod units.ord x)"
        by simp
      also have "x [^]\<^bsub>units_of R\<^esub> \<dots> = x [^]\<^bsub>units_of R\<^esub> (units.ord x * (j div units.ord x))
                   \<otimes>\<^bsub>units_of R\<^esub> x [^]\<^bsub>units_of R\<^esub> (j mod units.ord x)"
        using x by (subst units.nat_pow_mult) auto
      also have "x [^]\<^bsub>units_of R\<^esub> (units.ord x * (j div units.ord x)) =
                   (x [^]\<^bsub>units_of R\<^esub> units.ord x) [^]\<^bsub>units_of R\<^esub> (j div units.ord x)"
        using x by (subst units.nat_pow_pow) auto
      also have "x [^]\<^bsub>units_of R\<^esub> units.ord x = 1"
        using x(1) by (subst units.pow_ord_eq_1) auto
      finally have "x ^ j mod p = x ^ (j mod units.ord x) mod p" using n_gt_1 by simp
      thus "x ^ j mod p \<in> (\<lambda>i. x ^ i mod p) ` {..<units.ord x}"
        using units.ord_ge_1[of x] x(1) by force
    qed auto
    also have "\<dots> \<le> card {..<units.ord x}"
      by (intro card_image_le) auto
    also have "\<dots> = units.ord x" by simp
    finally show "p - 1 \<le> units.ord x" .
  qed
  with x show ?thesis by metis
qed

end


subsection \<open>\<open>-1\<close> in residue rings\<close>

lemma minus_one_cong_solve_weak:
  fixes n x :: nat
  assumes "1 < n" "x \<in> totatives n" "y \<in> totatives n"
    and  "[x = n - 1] (mod n)" "[x * y = 1] (mod n)"
  shows "y = n - 1"
proof -
  define G where "G = Residues_Mult n"
  interpret residues_mult_nat n G
    by unfold_locales (use \<open>n > 1\<close> in \<open>simp_all add: G_def\<close>)
  have "[x * (n - 1) = x * n - x] (mod n)"
    by (simp add: algebra_simps)
  also have "[x * n - x = (n - 1) * n - (n - 1)] (mod n)"
    using assms by (intro cong_diff_nat cong_mult) auto
  also have "(n - 1) * n - (n - 1) = (n - 1) ^ 2"
    by (simp add: power2_eq_square algebra_simps)
  also have "[(n - 1)\<^sup>2 = 1] (mod n)"
    using assms by (intro square_minus_one_cong_one) auto
  finally have "x * (n - 1) mod n = 1"
    using \<open>n > 1\<close> by (simp add: cong_def)
  hence "y = n - 1" 
    using inv_unique'[of x "n - 1"] inv_unique'[of x y] minus_one_in_totatives[of n] assms(1-3,5)
    by (simp_all add: mult_ac cong_def)
  then show ?thesis by simp
qed

lemma coprime_imp_mod_not_zero:
  fixes n x :: nat
  assumes "1 < n" "coprime x n"
  shows "0 < x mod n"
  using assms coprime_0_left_iff nat_dvd_not_less by fastforce

lemma minus_one_cong_solve:
  fixes n x :: nat
  assumes "1 < n"
    and eq: "[x = n - 1] (mod n)" "[x * y = 1] (mod n)"
    and coprime: "coprime x n" "coprime y n"
  shows "[y = n - 1](mod n)"
proof -
  have "0 < x mod n" "0 < y mod n"
    using coprime coprime_imp_mod_not_zero \<open>1 < n\<close> by blast+
  moreover have "x mod n < n" "y mod n < n"
    using \<open>1 < n\<close> by auto
  moreover have "[x mod n = n - 1] (mod n)" "[x mod n * (y mod n) = 1] (mod n)"
    using eq by auto
  moreover have "coprime (x mod n) n" "coprime (y mod n) n"
    using coprime coprime_mod_left_iff \<open>1 < n\<close> by auto
  ultimately have "[y mod n = n - 1] (mod n)"
    using minus_one_cong_solve_weak[OF \<open>1 < n\<close>, of "x mod n" "y mod n"]
    by (auto simp: totatives_def)
  then show ?thesis by simp
qed

corollary square_minus_one_cong_one':
  fixes n x :: nat
  assumes "1 < n"
  shows "[(n - 1) * (n - 1) = 1](mod n)"
  using square_minus_one_cong_one[OF assms, of "n - 1"] assms
  by (fastforce simp: power2_eq_square)

end