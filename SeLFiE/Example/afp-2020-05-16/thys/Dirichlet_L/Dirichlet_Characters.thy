(*
    File:      Dirichlet_Characters.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Dirichlet Characters\<close>
theory Dirichlet_Characters
imports
  Multiplicative_Characters
  "HOL-Number_Theory.Residues"
  "Dirichlet_Series.Multiplicative_Function"
begin

text \<open>
  Dirichlet characters are essentially just the characters of the multiplicative group of
  integer residues $\mathbb{ZZ}/n\mathbb{ZZ}$ for some fixed $n$. For convenience, these residues
  are usually represented by natural numbers from $0$ to $n - 1$, and we extend the characters to 
  all natural numbers periodically, so that $\chi(k\mod n) = \chi(k)$ holds.

  Numbers that are not coprime to $n$ are not in the group and therefore are assigned $0$ by
  all characters.
\<close>

subsection \<open>The multiplicative group of residues\<close>

definition residue_mult_group :: "nat \<Rightarrow> nat monoid" where
  "residue_mult_group n = \<lparr> carrier = totatives n, monoid.mult = (\<lambda>x y. (x * y) mod n), one = 1 \<rparr>"

definition principal_dchar :: "nat \<Rightarrow> nat \<Rightarrow> complex" where
  "principal_dchar n = (\<lambda>k. if coprime k n then 1 else 0)"

lemma principal_dchar_coprime [simp]: "coprime k n \<Longrightarrow> principal_dchar n k = 1"
  and principal_dchar_not_coprime [simp]: "\<not>coprime k n \<Longrightarrow> principal_dchar n k = 0"
  by (simp_all add: principal_dchar_def)

lemma principal_dchar_1 [simp]: "principal_dchar n 1 = 1"
  by simp

lemma principal_dchar_minus1 [simp]:
  assumes "n > 0"
  shows   "principal_dchar n (n - Suc 0) = 1"
proof (cases "n = 1")
  case False
  with assms have "n > 1" by linarith
  thus ?thesis using coprime_diff_one_left_nat[of n]
    by (intro principal_dchar_coprime) auto
qed auto

lemma mod_in_totatives: "n > 1 \<Longrightarrow> a mod n \<in> totatives n \<longleftrightarrow> coprime a n"
  by (auto simp: totatives_def mod_greater_zero_iff_not_dvd dest: coprime_common_divisor_nat)

bundle dcharacter_syntax
begin
notation principal_dchar ("\<chi>\<^sub>0\<index>")
end

locale residues_nat =
  fixes n :: nat (structure) and G
  assumes n: "n > 1"
  defines "G \<equiv> residue_mult_group n"
begin

lemma order [simp]: "order G = totient n"
  by (simp add: order_def G_def totient_def residue_mult_group_def)

lemma totatives_mod [simp]: "x \<in> totatives n \<Longrightarrow> x mod n = x"
  using n by (intro mod_less) (auto simp: totatives_def intro!: order.not_eq_order_implies_strict)

lemma principal_dchar_minus1 [simp]: "principal_dchar n (n - Suc 0) = 1"
  using principal_dchar_minus1[of n] n by simp

sublocale finite_comm_group G
proof
  fix x y assume xy: "x \<in> carrier G" "y \<in> carrier G"
  hence "coprime (x * y) n" 
    by (auto simp: G_def residue_mult_group_def totatives_def)
  with xy and n show "x \<otimes>\<^bsub>G\<^esub> y \<in> carrier G"
    using coprime_common_divisor_nat[of "x * y" n]
    by (auto simp: G_def residue_mult_group_def totatives_def
                   mod_greater_zero_iff_not_dvd le_Suc_eq simp del: coprime_mult_left_iff)
next
  fix x y z assume xyz: "x \<in> carrier G" "y \<in> carrier G" "z \<in> carrier G"
  thus "x \<otimes>\<^bsub>G\<^esub> y \<otimes>\<^bsub>G\<^esub> z = x \<otimes>\<^bsub>G\<^esub> (y \<otimes>\<^bsub>G\<^esub> z)"
    by (auto simp: G_def residue_mult_group_def mult_ac mod_mult_right_eq)
next
  fix x assume "x \<in> carrier G"
  with n have "x < n" by (auto simp: G_def residue_mult_group_def totatives_def 
                               intro!: order.not_eq_order_implies_strict)
  thus " \<one>\<^bsub>G\<^esub> \<otimes>\<^bsub>G\<^esub> x = x" and "x \<otimes>\<^bsub>G\<^esub> \<one>\<^bsub>G\<^esub> = x"
    by (simp_all add: G_def residue_mult_group_def)
next
  have "x \<in> Units G" if "x \<in> carrier G" for x unfolding Units_def
  proof safe
    from that have "x > 0" "coprime x n" 
      by (auto simp: G_def residue_mult_group_def totatives_def)
    from \<open>coprime x n\<close> and n obtain y where y: "y < n" "[x * y = 1] (mod n)"
      by (subst (asm) coprime_iff_invertible'_nat) auto
    hence "x * y mod n = 1" 
      using n by (simp add: cong_def mult_ac)
    moreover from y have "coprime y n"
      by (subst coprime_iff_invertible_nat) (auto simp: mult.commute)
    ultimately show "\<exists>a\<in>carrier G. a \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub> \<and> x \<otimes>\<^bsub>G\<^esub> a = \<one>\<^bsub>G\<^esub>" using y
      by (intro bexI[of _ y]) 
         (auto simp: G_def residue_mult_group_def totatives_def mult.commute intro!: Nat.gr0I)
  qed fact+
  thus "carrier G \<subseteq> Units G" ..
qed (insert n, auto simp: G_def residue_mult_group_def mult_ac)


subsection \<open>Definition of Dirichlet characters\<close>

text \<open>
  The following two functions make the connection between Dirichlet characters and the
  multiplicative characters of the residue group.
\<close>
definition c2dc :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> complex)" where
  "c2dc \<chi> = (\<lambda>x. \<chi> (x mod n))"

definition dc2c :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> complex)" where
  "dc2c \<chi> = (\<lambda>x. if x < n then \<chi> x else 0)"

lemma dc2c_c2dc [simp]:
  assumes "character G \<chi>"
  shows   "dc2c (c2dc \<chi>) = \<chi>"
proof -
  interpret character G \<chi> by fact
  show ?thesis
    using n by (auto simp: fun_eq_iff dc2c_def c2dc_def char_eq_0_iff G_def
                           residue_mult_group_def totatives_def)
qed

end

locale dcharacter = residues_nat +
  fixes \<chi> :: "nat \<Rightarrow> complex"
  assumes mult_aux: "a \<in> totatives n \<Longrightarrow> b \<in> totatives n \<Longrightarrow> \<chi> (a * b) = \<chi> a * \<chi> b"
  assumes eq_zero:  "\<not>coprime a n \<Longrightarrow> \<chi> a = 0"
  assumes periodic: "\<chi> (a + n) = \<chi> a"
  assumes one_not_zero: "\<chi> 1 \<noteq> 0"
begin

lemma zero_eq_0 [simp]: "\<chi> 0 = 0"
  using n by (intro eq_zero) auto

lemma Suc_0 [simp]: "\<chi> (Suc 0) = 1"
  using n mult_aux[of 1 1] one_not_zero by (simp add: totatives_def)   

lemma periodic_mult: "\<chi> (a + m * n) = \<chi> a"
proof (induction m)
  case (Suc m)
  have "a + Suc m * n = a + m * n+ n" by simp
  also have "\<chi> \<dots> = \<chi> (a + m * n)" by (rule periodic)
  also have "\<dots> = \<chi> a" by (rule Suc.IH)
  finally show ?case .
qed simp_all

lemma minus_one_periodic [simp]:
  assumes "k > 0"
  shows   "\<chi> (k * n - 1) = \<chi> (n - 1)"
proof -
  have "k * n - 1 = n - 1 + (k - 1) * n"
    using assms n by (simp add: algebra_simps)
  also have "\<chi> \<dots> = \<chi> (n - 1)"
    by (rule periodic_mult)
  finally show ?thesis .
qed

lemma cong:
  assumes "[a = b] (mod n)"
  shows   "\<chi> a = \<chi> b"
proof -
  from assms obtain k1 k2 where *: "b + k1 * n = a + k2 * n"
    by (subst (asm) cong_iff_lin_nat) auto
  have "\<chi> a = \<chi> (a + k2 * n)" by (rule periodic_mult [symmetric])
  also note * [symmetric]
  also have "\<chi> (b + k1 * n) = \<chi> b" by (rule periodic_mult)
  finally show ?thesis .
qed

lemma mod [simp]: "\<chi> (a mod n) = \<chi> a"
  by (rule cong) (simp_all add: cong_def)

lemma mult [simp]: "\<chi> (a * b) = \<chi> a * \<chi> b"
proof (cases "coprime a n \<and> coprime b n")
  case True
  hence "a mod n \<in> totatives n" "b mod n \<in> totatives n"
    using n by (auto simp: totatives_def mod_greater_zero_iff_not_dvd coprime_absorb_right)
  hence "\<chi> ((a mod n) * (b mod n)) = \<chi> (a mod n) * \<chi> (b mod n)"
    by (rule mult_aux)
  also have "\<chi> ((a mod n) * (b mod n)) = \<chi> (a * b)"
    by (rule cong) (auto simp: cong_def mod_mult_eq)
  finally show ?thesis by simp
next
  case False
  hence "\<not>coprime (a * b) n" by simp
  with False show ?thesis by (auto simp: eq_zero)
qed

sublocale mult: completely_multiplicative_function \<chi>
  by standard auto

lemma eq_zero_iff: "\<chi> x = 0 \<longleftrightarrow> \<not>coprime x n"
proof safe
  assume "\<chi> x = 0" and "coprime x n"
  from cong_solve_coprime_nat [OF this(2)] 
    obtain y where "[x * y = Suc 0] (mod n)" by blast
  hence "\<chi> (x * y) = \<chi> (Suc 0)" by (rule cong)
  with \<open>\<chi> x = 0\<close> show False by simp
qed (auto simp: eq_zero)

lemma minus_one': "\<chi> (n - 1) \<in> {-1, 1}"
proof -
  define n' where "n' = n - 2"
  have n: "n = Suc (Suc n')" using n by (simp add: n'_def)
  have "(n - 1) ^ 2 = 1 + (n - 2) * n"
    by (simp add: power2_eq_square algebra_simps n)
  also have "\<chi> \<dots> = 1"
    by (subst periodic_mult) auto
  also have "\<chi> ((n - 1) ^ 2) = \<chi> (n - 1) ^ 2"
    by (rule mult.power)
  finally show ?thesis
    by (subst (asm) power2_eq_1_iff) auto
qed

lemma c2dc_dc2c [simp]: "c2dc (dc2c \<chi>) = \<chi>"
  using n by (auto simp: c2dc_def dc2c_def fun_eq_iff intro!: cong simp: cong_def)

lemma character_dc2c: "character G (dc2c \<chi>)"
  by standard (insert n, auto simp: G_def residue_mult_group_def dc2c_def totatives_def
                              intro!: eq_zero)

sublocale dc2c: character G "dc2c \<chi>"
  by (fact character_dc2c)

lemma dcharacter_inv_character [intro]: "dcharacter n (inv_character \<chi>)"
  by standard (auto simp: inv_character_def eq_zero periodic)

lemma norm: "norm (\<chi> k) = (if coprime k n then 1 else 0)"
proof -
  have "\<chi> k = \<chi> (k mod n)" by (intro cong) (auto simp: cong_def)
  also from n have "\<dots> = dc2c \<chi> (k mod n)" by (simp add: dc2c_def)
  also from n have "norm \<dots> = (if coprime k n then 1 else 0)"
    by (subst dc2c.norm_char) (auto simp: G_def residue_mult_group_def mod_in_totatives)
  finally show ?thesis .
qed

lemma norm_le_1: "norm (\<chi> k) \<le> 1"
  by (subst norm) auto

end


definition dcharacters :: "nat \<Rightarrow> (nat \<Rightarrow> complex) set" where
  "dcharacters n = {\<chi>. dcharacter n \<chi>}"

context residues_nat
begin

lemma character_dc2c: "dcharacter n \<chi> \<Longrightarrow> character G (dc2c \<chi>)"
  using dcharacter.character_dc2c[of n \<chi>] by (simp add: G_def)

lemma dcharacter_c2dc: 
  assumes "character G \<chi>"
  shows   "dcharacter n (c2dc \<chi>)"
proof -
  interpret character G \<chi> by fact
  show ?thesis
  proof
    fix x assume "\<not>coprime x n"
    thus "c2dc \<chi> x = 0"
      by (auto simp: c2dc_def char_eq_0_iff G_def residue_mult_group_def totatives_def)
  qed (insert char_mult char_one n, 
       auto simp: c2dc_def G_def residue_mult_group_def simp del: char_mult char_one)
qed

lemma principal_dchar_altdef: "principal_dchar n = c2dc (principal_char G)"
  using n by (auto simp: c2dc_def principal_dchar_def principal_char_def G_def
                residue_mult_group_def fun_eq_iff mod_in_totatives)

sublocale principal: dcharacter n G "principal_dchar n"
  by (simp add: principal_dchar_altdef dcharacter_c2dc | rule G_def)+

lemma c2dc_principal [simp]: "c2dc (principal_char G) = principal_dchar n"
  by (simp add: principal_dchar_altdef)

lemma dc2c_principal [simp]: "dc2c (principal_dchar n) = principal_char G"
proof -
  have "dc2c (c2dc (principal_char G)) = dc2c (principal_dchar n)"
    by (subst c2dc_principal) (rule refl)
  thus ?thesis by (subst (asm) dc2c_c2dc) simp_all
qed


lemma bij_betw_dcharacters_characters:
  "bij_betw dc2c (dcharacters n) (characters G)"
  by (intro bij_betwI[where ?g = c2dc])
     (auto simp: characters_def dcharacters_def dcharacter_c2dc 
                 character_dc2c dcharacter.c2dc_dc2c)

lemma bij_betw_characters_dcharacters:
  "bij_betw c2dc (characters G) (dcharacters n)"
  by (intro bij_betwI[where ?g = dc2c])
     (auto simp: characters_def dcharacters_def dcharacter_c2dc 
                 character_dc2c dcharacter.c2dc_dc2c)

lemma finite_dcharacters [intro]: "finite (dcharacters n)"
  using bij_betw_finite [OF bij_betw_dcharacters_characters] by auto

lemma card_dcharacters [simp]: "card (dcharacters n) = totient n"
  using bij_betw_same_card [OF bij_betw_dcharacters_characters] card_characters by simp

end

lemma inv_character_eq_principal_dchar_iff [simp]: 
  "inv_character \<chi> = principal_dchar n \<longleftrightarrow> \<chi> = principal_dchar n"
  by (auto simp add: fun_eq_iff inv_character_def principal_dchar_def)


subsection \<open>Sums of Dirichlet characters\<close>

lemma (in dcharacter) sum_dcharacter_totatives:
  "(\<Sum>x\<in>totatives n. \<chi> x) = (if \<chi> = principal_dchar n then of_nat (totient n) else 0)"
proof -
  from n have "(\<Sum>x\<in>totatives n. \<chi> x) = (\<Sum>x\<in>carrier G. dc2c \<chi> x)"
    by (intro sum.cong) (auto simp: totatives_def dc2c_def G_def residue_mult_group_def)
  also have "\<dots> = (if dc2c \<chi> = principal_char G then of_nat (order G) else 0)"
    by (rule dc2c.sum_character)
  also have "dc2c \<chi> = principal_char G \<longleftrightarrow> \<chi> = principal_dchar n"
    by (metis c2dc_dc2c dc2c_principal principal_dchar_altdef)
  finally show ?thesis by simp
qed

lemma (in dcharacter) sum_dcharacter_block:
  "(\<Sum>x<n. \<chi> x) = (if \<chi> = principal_dchar n then of_nat (totient n) else 0)"
proof -
  from n have "(\<Sum>x<n. \<chi> x) = (\<Sum>x\<in>totatives n. \<chi> x)"
    by (intro sum.mono_neutral_right) 
       (auto simp: totatives_def eq_zero_iff intro!: Nat.gr0I order.not_eq_order_implies_strict)
  also have "\<dots> = (if \<chi> = principal_dchar n then of_nat (totient n) else 0)"
    by (rule sum_dcharacter_totatives)
  finally show ?thesis .
qed

lemma (in dcharacter) sum_dcharacter_block':
  "sum \<chi> {Suc 0..n} = (if \<chi> = principal_dchar n then of_nat (totient n) else 0)"
proof -
  let ?f = "\<lambda>k. if k = n then 0 else k" and ?g = "\<lambda>k. if k = 0 then n else k"
  have "sum \<chi> {1..n} = sum \<chi> {..<n}"
    using n by (intro sum.reindex_bij_witness[where j = ?f and i = ?g]) (auto simp: eq_zero_iff)
  thus ?thesis by (simp add: sum_dcharacter_block)
qed

lemma (in dcharacter) sum_lessThan_dcharacter:
  assumes "\<chi> \<noteq> principal_dchar n"
  shows   "(\<Sum>x<m. \<chi> x) = (\<Sum>x<m mod n. \<chi> x)"
proof (induction m rule: less_induct)
  case (less m)
  show ?case
  proof (cases "m < n")
    case True
    thus ?thesis by simp
  next
    case False
    hence "{..<m} = {..<n} \<union> {n..<m}" by auto
    also have "(\<Sum>x\<in>\<dots>. \<chi> x) = (\<Sum>x<n. \<chi> x) + (\<Sum>x\<in>{n..<m}. \<chi> x)"
      by (intro sum.union_disjoint) auto
    also from assms have "(\<Sum>x<n. \<chi> x) = 0"
      by (subst sum_dcharacter_block) simp_all
    also from False have "(\<Sum>x\<in>{n..<m}. \<chi> x) = (\<Sum>x\<in>{..<m - n}. \<chi> (x + n))"
      by (intro sum.reindex_bij_witness[of _ "\<lambda>x. x + n" "\<lambda>x. x - n"]) (auto simp: periodic)
    also have "\<dots> = (\<Sum>x\<in>{..<m - n}. \<chi> x)" by (simp add: periodic)
    also have "\<dots> = (\<Sum>x<(m - n) mod n. \<chi> x)"
      using False and n by (intro less.IH) auto
    also from False and n have "(m - n) mod n = m mod n" 
      by (simp add: mod_geq [symmetric])
    finally show ?thesis by simp
  qed
qed

lemma (in dcharacter) sum_dcharacter_lessThan_le:
  assumes "\<chi> \<noteq> principal_dchar n"
  shows   "norm (\<Sum>x<m. \<chi> x) \<le> totient n"
proof -
  have "(\<Sum>x<m. \<chi> x) = (\<Sum>x<m mod n. \<chi> x)" by (rule sum_lessThan_dcharacter) fact
  also have "\<dots> = (\<Sum>x | x < m mod n \<and> coprime x n. \<chi> x)"
    by (intro sum.mono_neutral_right) (auto simp: eq_zero_iff)
  also have "norm \<dots> \<le> (\<Sum>x | x < m mod n \<and> coprime x n. 1)"
    by (rule sum_norm_le) (auto simp: norm)
  also have "\<dots> = card {x. x < m mod n \<and> coprime x n}" by simp
  also have "\<dots> \<le> card (totatives n)" unfolding of_nat_le_iff
  proof (intro card_mono subsetI)
    fix x assume x: "x \<in> {x. x < m mod n \<and> coprime x n}"
    hence "x < m mod n" by simp
    also have "\<dots> < n" using n by simp
    finally show "x \<in> totatives n" using x
      by (auto simp: totatives_def intro!: Nat.gr0I)
  qed auto
  also have "\<dots> = totient n" by (simp add: totient_def)
  finally show ?thesis .
qed

lemma (in dcharacter) sum_dcharacter_atMost_le:
  assumes "\<chi> \<noteq> principal_dchar n"
  shows   "norm (\<Sum>x\<le>m. \<chi> x) \<le> totient n"
  using sum_dcharacter_lessThan_le[OF assms, of "Suc m"] by (subst (asm) lessThan_Suc_atMost)

lemma (in residues_nat) sum_dcharacters:
  "(\<Sum>\<chi>\<in>dcharacters n. \<chi> x) = (if [x = 1] (mod n) then of_nat (totient n) else 0)"
proof (cases "coprime x n")
  case True
  with n have x: "x mod n \<in> totatives n" by (auto simp: mod_in_totatives)
  have "(\<Sum>\<chi>\<in>dcharacters n. \<chi> x) = (\<Sum>\<chi>\<in>characters G. c2dc \<chi> x)"
    by (rule sum.reindex_bij_betw [OF bij_betw_characters_dcharacters, symmetric])
  also from x have "\<dots> = (\<Sum>\<chi>\<in>characters G. \<chi> (x mod n))"
    by (simp add: c2dc_def)
  also from x have "\<dots> = (if x mod n = 1 then order G else 0)"
    by (subst sum_characters) (unfold G_def residue_mult_group_def, auto)
  also from n have "x mod n = 1 \<longleftrightarrow> [x = 1] (mod n)"
    by (simp add: cong_def)
  finally show ?thesis by simp
next
  case False
  have "x mod n \<noteq> 1"
  proof
    assume *: "x mod n = 1"
    have "gcd (x mod n) n = 1" by (subst *) simp
    also have "gcd (x mod n) n = gcd x n" 
      by (subst gcd.commute) (simp only: gcd_red_nat [symmetric])
    finally show False using \<open>\<not>coprime x n\<close> unfolding coprime_iff_gcd_eq_1 by contradiction
  qed
  from False have "(\<Sum>\<chi>\<in>dcharacters n. \<chi> x) = 0"
    by (intro sum.neutral) (auto simp: dcharacters_def dcharacter.eq_zero)
  with \<open>x mod n \<noteq> 1\<close> and n show ?thesis by (simp add: cong_def)
qed

lemma (in dcharacter) even_dcharacter_linear_sum_eq_0 [simp]:
  assumes "\<chi> \<noteq> principal_dchar n" and "\<chi> (n - 1) = 1"
  shows   "(\<Sum>k=Suc 0..<n. of_nat k * \<chi> k) = 0"
proof -
  have "(\<Sum>k=1..<n. of_nat k * \<chi> k) = (\<Sum>k=1..<n. (of_nat n - of_nat k) * \<chi> (n - k))"
    by (intro sum.reindex_bij_witness[where i = "\<lambda>k. n - k" and j = "\<lambda>k. n - k"])
       (auto simp: of_nat_diff)
  also have "\<dots> = n * (\<Sum>k=1..<n. \<chi> (n - k)) - (\<Sum>k=1..<n. k * \<chi> (n - k))"
    by (simp add: algebra_simps sum_subtractf sum_distrib_left)
  also have "(\<Sum>k=1..<n. \<chi> (n - k)) = (\<Sum>k=1..<n. \<chi> k)"
    by (intro sum.reindex_bij_witness[where i = "\<lambda>k. n - k" and j = "\<lambda>k. n - k"]) auto
  also have "\<dots> = (\<Sum>k<n. \<chi> k)"
    by (intro sum.mono_neutral_left) (auto simp: Suc_le_eq)
  also have "\<dots> = 0" using assms by (simp add: sum_dcharacter_block)
  also have "(\<Sum>k=1..<n. of_nat k * \<chi> (n - k)) = (\<Sum>k=1..<n. k * \<chi> k)"
  proof (intro sum.cong refl)
    fix k assume k: "k \<in> {1..<n}"
    have "of_nat k * \<chi> k = of_nat k * \<chi> ((n - 1) * k)"
      using assms by (subst mult) simp_all
    also have "(n - 1) * k = n - k + (k - 1) * n"
      using k by (simp add: algebra_simps)
    also have "\<chi> \<dots> = \<chi> (n - k)"
      by (rule periodic_mult)
    finally show "of_nat k * \<chi> (n - k) = of_nat k * \<chi> k" ..
  qed
  finally show ?thesis by simp
qed

end
