section\<open>Basics needed\<close>

theory PerfectBasics
imports Main "HOL-Computational_Algebra.Primes" "HOL-Algebra.Exponent"
begin

lemma sum_mono2_nat: "finite (B::nat set) \<Longrightarrow> A <= B \<Longrightarrow> \<Sum> A <= \<Sum> B"
  by (auto simp add: sum_mono2)

(* TODO Move *)
lemma multiplicity_0 [simp]: "multiplicity 0 x = 0" 
  by (cases "x = 0") (auto intro: not_dvd_imp_multiplicity_0)
  

lemma exp_is_max_div:
   assumes m0:"m \<noteq> 0" and p: "prime p"
   shows "~ p dvd (m div (p^(multiplicity p m)))"
proof (rule ccontr)
  assume "~ ~ p dvd (m div (p^(multiplicity p m)))"
  hence a:"p dvd (m div (p^(multiplicity p m)))" by auto
  from m0 have "p^(multiplicity p m) dvd m" by (auto simp add: multiplicity_dvd)
  with a have "p^Suc (multiplicity p m) dvd m"
    by (subst (asm) dvd_div_iff_mult) auto
  with m0 p show False
    by (subst (asm) power_dvd_iff_le_multiplicity) auto
qed

lemma coprime_multiplicity:
  assumes "prime (p::nat)" and "m > 0"
  shows "coprime p (m div (p ^ multiplicity p m))"
proof (rule ccontr)
  assume "\<not> coprime p (m div p ^ multiplicity p m)"
  with \<open>prime p\<close> have "\<exists>q. prime q \<and> q dvd p \<and> q dvd m div p ^ multiplicity p m"
    by (metis dvd_refl prime_imp_coprime)
  with \<open>prime p\<close> have "\<exists>q. q = p \<and> q dvd m div p ^ multiplicity p m"
    by (metis not_prime_1 prime_nat_iff)
  then have "p dvd m div p ^ multiplicity p m"
    by auto
  with assms show False
    by (auto simp add: exp_is_max_div)
qed

lemma add_mult_distrib_three: "(x::nat)*(a+b+c)=x*a+x*b+x*c" 
proof -
  have "(x::nat)*(a+b+c) = x*((a+b)+c)" by auto
  hence "x*(a+b+c) = x*(a+b)+x*c" by (simp add: algebra_simps)
  thus "x*(a+b+c) = x*a+x*b+x*c" by (simp add: algebra_simps) 
qed

lemma nat_interval_minus_zero: "{0..Suc n} = {0} Un {Suc 0..Suc n}" by auto
lemma nat_interval_minus_zero2:
 assumes "n>0"
 shows "{0..n} = {0} Un {Suc 0..n}" by (auto simp add: nat_interval_minus_zero)

theorem simplify_sum_of_powers: "(x - 1::nat) * (\<Sum>i=0 .. n . x^i)  = x^(n + 1) - 1" (is "?l = ?r")
proof (cases)
  assume "n = 0"
  thus "?l = x^(n+1) - 1" by auto
  next
  assume "n~=0"
  hence n0: "n>0" by auto 
  have "?l  = (x::nat)*(\<Sum>i=0 .. n . x^i) - (\<Sum>i=0 .. n . x^i)"
    by (metis diff_mult_distrib nat_mult_1)
  also have "... = (\<Sum>i=0 .. n . x^(Suc i))    - (\<Sum>i=0 .. n . x^i)"
    by (simp add: sum_distrib_left)
  also have "... = (\<Sum>i=Suc 0 .. Suc n . x^i)  - (\<Sum>i=0 .. n . x^i)"
    by (metis sum.shift_bounds_cl_Suc_ivl)
  also with n0
  have "... = ((\<Sum>i=Suc 0 .. n. x^i)+x^(Suc n)) - (x^0 + (\<Sum>i=Suc 0 .. n. x^i))"
    by (auto simp add: sum.union_disjoint nat_interval_minus_zero2)
  finally show "?thesis" by auto
qed

end
