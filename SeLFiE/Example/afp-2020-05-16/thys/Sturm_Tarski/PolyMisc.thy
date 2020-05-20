(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

theory PolyMisc imports
  "HOL-Computational_Algebra.Polynomial_Factorial"
begin
  
lemma coprime_poly_0:
  "poly p x \<noteq> 0 \<or> poly q x \<noteq> 0" if "coprime p q"
  for x :: "'a :: field"
proof (rule ccontr)
  assume " \<not> (poly p x \<noteq> 0 \<or> poly q x \<noteq> 0)"
  then have "[:-x, 1:] dvd p" "[:-x, 1:] dvd q"
    by (simp_all add: poly_eq_0_iff_dvd)
  with that have "is_unit [:-x, 1:]"
    by (rule coprime_common_divisor)
  then show False
    by (auto simp add: is_unit_pCons_iff)
qed

lemma smult_cancel:
  fixes p::"'a::idom poly"
  assumes "c\<noteq>0" and smult: "smult c p = smult c q" 
  shows "p=q" 
proof -
  have "smult c (p-q)=0" using smult by (metis diff_self smult_diff_right)
  thus ?thesis using \<open>c\<noteq>0\<close> by auto
qed

lemma dvd_monic:
  fixes p q:: "'a :: idom poly" 
  assumes monic:"lead_coeff p=1" and "p dvd (smult c q)" and "c\<noteq>0"
  shows "p dvd q" using assms
proof (cases "q=0 \<or> degree p=0")
  case True
  thus ?thesis using assms
    by (auto elim!: degree_eq_zeroE simp add: const_poly_dvd_iff)
next
  case False
  hence "q\<noteq>0" and "degree p\<noteq>0" by auto
  obtain k where k:"smult c q = p*k" using assms dvd_def by metis
  hence "k\<noteq>0" by (metis False assms(3) mult_zero_right smult_eq_0_iff)
  hence deg_eq:"degree q=degree p + degree k"
    by (metis False assms(3) degree_0 degree_mult_eq degree_smult_eq k)
  have c_dvd:"\<forall>n\<le>degree k. c dvd coeff k (degree k - n)" 
  proof (rule,rule)
    fix n assume "n \<le> degree k "
    thus "c dvd coeff k (degree k - n)"
    proof (induct n rule:nat_less_induct) 
      case (1 n) 
      define T where "T\<equiv>(\<lambda>i. coeff p i * coeff k (degree p+degree k - n - i))"
      have "c * coeff q (degree q - n) = (\<Sum>i\<le>degree q - n. coeff p i * coeff k (degree q - n - i))"
        using coeff_mult[of p k "degree q - n"] k coeff_smult[of c q "degree q -n"] by auto
      also have "...=(\<Sum>i\<le>degree p+degree k - n. T i)"
        using deg_eq unfolding T_def by auto 
      also have "...=(\<Sum>i\<in>{0..<degree p}. T i) + sum T {(degree p)}+ 
                  sum T {degree p + 1..degree p + degree k - n}" 
      proof -
        define C where "C\<equiv>{{0..<degree p}, {degree p},{degree p+1..degree p+degree k-n}}"
        have "\<forall>A\<in>C. finite A" unfolding C_def by auto
        moreover have "\<forall>A\<in>C. \<forall>B\<in>C. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
          unfolding C_def by auto
        ultimately have "sum T (\<Union>C) = sum (sum T) C" 
          using sum.Union_disjoint by auto
        moreover have "\<Union>C={..degree p + degree k - n}" 
          using \<open>n \<le> degree k\<close> unfolding C_def by auto
        moreover have  "sum (sum T) C= sum T {0..<degree p} + sum T {(degree p)} + 
                  sum T {degree p + 1..degree p + degree k - n}"
        proof -
          have "{0..<degree p}\<noteq>{degree p}" 
            by (metis atLeast0LessThan insertI1 lessThan_iff less_imp_not_eq)  
          moreover have "{degree p}\<noteq>{degree p + 1..degree p + degree k - n}" 
            by (metis add.commute add_diff_cancel_right' atLeastAtMost_singleton_iff 
                  diff_self_eq_0 eq_imp_le not_one_le_zero)
          moreover have "{0..<degree p}\<noteq>{degree p + 1..degree p + degree k - n}" 
            using \<open>degree k\<ge>n\<close> \<open>degree p\<noteq>0\<close> by fastforce
          ultimately show ?thesis unfolding C_def by auto
        qed
        ultimately show ?thesis by auto
      qed
      also have "...=(\<Sum>i\<in>{0..<degree p}. T i) +  coeff k (degree k - n)"
      proof -
        have "\<forall>x\<in>{degree p + 1..degree p + degree k - n}. T x=0" 
          using coeff_eq_0[of p] unfolding T_def by simp
        hence "sum T {degree p + 1..degree p + degree k - n}=0" by auto
        moreover have "T (degree p)=coeff k (degree k - n)"
          using monic by (simp add: T_def)
        ultimately show ?thesis by auto
      qed
      finally have c_coeff: "c * coeff q (degree q - n) = sum T {0..<degree p} 
              + coeff k (degree k - n)" .
      moreover have "n\<noteq>0\<Longrightarrow>c dvd sum T {0..<degree p}" 
      proof (rule dvd_sum)
        fix i assume i:"i \<in> {0..<degree p}" and "n\<noteq>0"
        hence "(n+i-degree p)\<le>degree k" using \<open>n \<le> degree k\<close> by auto
        moreover have "n + i - degree p <n" using i \<open>n\<noteq>0\<close> by auto 
        ultimately have "c dvd coeff k (degree k - (n+i-degree p))"
          using 1(1) by auto
        hence "c dvd coeff k (degree p + degree k - n - i)"
          by (metis add_diff_cancel_left' deg_eq diff_diff_left dvd_0_right le_degree 
                  le_diff_conv add.commute ordered_cancel_comm_monoid_diff_class.diff_diff_right)
        thus "c dvd T i" unfolding T_def by auto
      qed
      moreover have "n=0 \<Longrightarrow>?case"
      proof -
        assume "n=0"
        hence "\<forall>i\<in>{0..<degree p}. coeff k (degree p + degree k - n - i) =0" 
          using coeff_eq_0[of k] by simp
        hence "c * coeff q (degree q - n) = coeff k (degree k - n)"
          using c_coeff unfolding T_def by auto
        thus ?thesis by (metis dvdI)
      qed
      ultimately show ?case by (metis dvd_add_right_iff dvd_triv_left)
    qed
  qed
  hence "\<forall>n. c dvd coeff k n"
    by (metis diff_diff_cancel dvd_0_right le_add2 le_add_diff_inverse le_degree)
  then obtain f where f:"\<forall>n. c * f n=coeff k n" unfolding dvd_def by metis
  have " \<forall>\<^sub>\<infinity> n. f n = 0 "  
    by (metis (mono_tags, lifting) MOST_coeff_eq_0 MOST_mono assms(3) f mult_eq_0_iff)
  hence "smult c (Abs_poly f)=k" 
    using f smult.abs_eq[of c "Abs_poly f"] Abs_poly_inverse[of f] coeff_inverse[of k]
    by simp
  hence "q=p* Abs_poly f" using k \<open>c\<noteq>0\<close> smult_cancel by auto
  thus ?thesis unfolding dvd_def by auto
qed

lemma poly_power_n_eq:
  fixes x::"'a :: idom"
  assumes "n\<noteq>0"
  shows "poly ([:-a,1:]^n) x=0 \<longleftrightarrow> (x=a)" using assms 
by (induct n,auto)

lemma poly_power_n_odd:
  fixes x a:: real
  assumes "odd n"
  shows "poly ([:-a,1:]^n) x>0 \<longleftrightarrow> (x>a)" using assms 
proof -
  have "poly ([:-a,1:]^n) x\<ge>0 = (poly [:- a, 1:] x \<ge>0)" 
    unfolding poly_power using zero_le_odd_power[OF \<open>odd n\<close>] by blast
  also have "(poly [:- a, 1:] x \<ge>0) = (x\<ge>a)" by fastforce
  finally have "poly ([:-a,1:]^n) x\<ge>0 = (x\<ge>a)" .
  moreover have "poly ([:-a,1:]^n) x=0 = (x=a)" by(rule poly_power_n_eq, metis assms even_zero)    
  ultimately show ?thesis by linarith
qed

lemma gcd_coprime_poly:
  fixes p q::"'a::{factorial_ring_gcd,semiring_gcd_mult_normalize} poly"
  assumes nz: "p \<noteq> 0 \<or> q \<noteq> 0" and p': "p = p' * gcd p q" and
    q': "q = q' * gcd p q"
  shows "coprime p' q'" 
using gcd_coprime nz p' q' by auto

lemma poly_mod:
  "poly (p mod q) x = poly p x" if "poly q x = 0"
proof -
  from that have "poly (p mod q) x = poly (p div q * q) x + poly (p mod q) x"
    by simp
  also have "\<dots> = poly p x"
    by (simp only: poly_add [symmetric]) simp
  finally show ?thesis .
qed

end
