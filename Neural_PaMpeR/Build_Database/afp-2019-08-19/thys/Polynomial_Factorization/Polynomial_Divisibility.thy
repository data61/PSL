(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Polynomial Divisibility\<close>

text \<open>We make a connection between irreducibility of Missing-Polynomial and Factorial-Ring.\<close>


theory Polynomial_Divisibility
imports
  Polynomial_Interpolation.Missing_Polynomial
begin

lemma dvd_gcd_mult: fixes p :: "'a :: semiring_gcd"
  assumes dvd: "k dvd p * q" "k dvd p * r"
  shows "k dvd p * gcd q r"
  by (rule dvd_trans, rule gcd_greatest[OF dvd])
     (auto intro!: mult_dvd_mono simp: gcd_mult_left)

lemma poly_gcd_monic_factor:
  "monic p \<Longrightarrow>  gcd (p * q) (p * r) = p * gcd q r"
  by (rule gcdI [symmetric]) (simp_all add: normalize_mult normalize_monic dvd_gcd_mult)

context
  assumes "SORT_CONSTRAINT('a :: field)"
begin

lemma field_poly_irreducible_dvd_mult[simp]:
  assumes irr: "irreducible (p :: 'a poly)"
  shows "p dvd q * r \<longleftrightarrow> p dvd q \<or> p dvd r"
  using field_poly_irreducible_imp_prime[OF irr] by (simp add: prime_elem_dvd_mult_iff)

lemma irreducible_dvd_pow:
  fixes p :: "'a poly" 
  assumes irr: "irreducible p"  
  shows "p dvd q ^ n \<Longrightarrow> p dvd q"
  using field_poly_irreducible_imp_prime[OF irr] by (rule prime_elem_dvd_power)

lemma irreducible_dvd_prod: fixes p :: "'a poly"
  assumes irr: "irreducible p"
  and dvd: "p dvd prod f as"
  shows "\<exists> a \<in> as. p dvd f a"
  by (insert dvd, induct as rule: infinite_finite_induct, insert irr, auto)

lemma irreducible_dvd_prod_list: fixes p :: "'a poly"
  assumes irr: "irreducible p"
  and dvd: "p dvd prod_list as"
  shows "\<exists> a \<in> set as. p dvd a"
  by (insert dvd, induct as, insert irr, auto)


lemma dvd_mult_imp_degree: fixes p :: "'a poly" 
  assumes "p dvd q * r"
  and "degree p > 0" 
shows "\<exists> s t. irreducible s \<and> p = s * t \<and> (s dvd q \<or> s dvd r)"
proof -
  from irreducible\<^sub>d_factor[OF assms(2)] obtain s t
  where irred: "irreducible s" and p: "p = s * t" by auto
  from \<open>p dvd q * r\<close> p have s: "s dvd q * r" unfolding dvd_def by auto
  from s p irred show ?thesis by auto
qed

end

end
