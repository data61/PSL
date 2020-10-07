section\<open>Perfect Number Theorem\<close>

theory Perfect
imports Sigma
begin

definition  perfect :: "nat => bool" where
"perfect m == m>0 & 2*m = sigma m"

theorem perfect_number_theorem:
  assumes even: "even m" and perfect: "perfect m"
  shows "\<exists> n . m = 2^n*(2^(n+1) - 1) \<and> prime ((2::nat)^(n+1) - 1)"
proof                                         
  from perfect have m0: "m>0" by (auto simp add: perfect_def)

  let ?n = "multiplicity 2 m" 
  let ?A = "m div 2^?n"
  let ?np = "(2::nat)^(?n+1) - 1"

  from even m0 have n1: "?n >= 1 " by (simp add: multiplicity_geI)

  have  "2^?n dvd m" by (rule multiplicity_dvd)
  hence "m = 2^?n*?A" by (simp only: dvd_mult_div_cancel) 
  with m0 have mdef: "m=2^?n*?A & coprime 2 ?A"
    using multiplicity_decompose [of m 2] by simp
  moreover with m0 have a0: "?A>0" by (metis nat_0_less_mult_iff)
  moreover
  { from perfect have "2*m=sigma(m)" by (simp add: perfect_def)
    with mdef have "2^(?n+1)*?A=sigma(2^?n*?A)" by auto
  } ultimately have "2^(?n+1)*?A=sigma(2^?n)*sigma(?A)"
    by (simp add: sigma_semimultiplicative)
  hence formula: "2^(?n+1)*?A=(?np)*sigma(?A)"
    by (simp only: sigma_prime_power_two)

  from n1 have "(2::nat)^(?n+1) >= 2^2" by (simp only: power_increasing)
  hence nplarger: "?np>= 3" by auto

  let ?B = "?A div ?np"

  from formula have "?np dvd ?A * 2^(?n+1)"
    by (auto simp add: ac_simps)
  then have "?np dvd ?A"
    using coprime_diff_one_left_nat [of "2 ^ (multiplicity 2 m + 1)"]
    by (auto simp add: coprime_dvd_mult_left_iff)
  then have bdef: "?np*?B = ?A"
    by simp
  with a0 have  b0: "?B>0" by (metis gr0I mult_is_0)

  from nplarger a0 have bsmallera: "?B < ?A" by auto

  have "?B = 1"
  proof (rule ccontr)
    assume "~?B = 1"
    with b0 bsmallera have "1<?B" "?B<?A" by auto
    moreover from bdef have "?B : divisors ?A" by (rule mult_divisors2)
    ultimately have "1+?B+?A <= sigma ?A" by (rule sigma_third_divisor)
    with nplarger have "?np*(1+?A+?B) <= ?np*(sigma ?A)"
      by (auto simp only: nat_mult_le_cancel1)
    with bdef have "?np+?A*?np + ?A*1 <= ?np*(sigma ?A)"
      by (simp only: add_mult_distrib_three mult.commute)
    hence "?np+?A*(?np + 1) <= ?np*(sigma ?A)" by (simp only:add_mult_distrib2)
    with nplarger have "2^(?n+1)*?A < ?np*(sigma ?A)" by(simp add:mult.commute)
    with formula show "False" by auto
  qed

  with bdef have adef: "?A=?np" by auto
  with formula have "?np*2^(?n+1) =(?np)*sigma(?A)" by auto
  with nplarger adef have "?A + 1=sigma(?A)" by auto
  with a0 have "prime ?A" by (simp add: sigma_imp_prime)
  with mdef adef show "m = 2^?n*(?np) & prime ?np" by simp
qed

theorem Euclid_book9_prop36:
  assumes p: "prime (2^(n+1) - (1::nat))"
  shows "perfect ((2^n)*(2^(n+1) - 1))"
proof (unfold perfect_def, auto)
  from assms show "(2::nat)*2^n > Suc 0" by (auto simp add: prime_nat_iff)
next
  have "2 ~= ((2::nat)^(n+1) - 1)" by simp arith
  then have "coprime (2::nat) (2^(n+1) - 1)"
    by (metis p primes_coprime_nat two_is_prime_nat) 
  moreover with p have "2^(n+1) - 1 > (0::nat)"
    by (auto simp add: prime_nat_iff)
  ultimately have  "sigma (2^n*(2^(n+1) - 1)) = (sigma(2^n))*(sigma(2^(n+1) - 1))"
    by (metis sigma_semimultiplicative two_is_prime_nat)
  also from assms have "... = (sigma(2^(n)))*(2^(n+1))"
    by (auto simp add: prime_imp_sigma)
  also have "... = (2^(n+1) - 1)*(2^(n+1))" by(simp add: sigma_prime_power_two)
  finally show "2*(2^n * (2*2^n - Suc 0)) = sigma(2^n*(2*2^n - Suc 0))" by auto
qed

end
