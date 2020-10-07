(*  Title:      RSAPSS/Cryptinverts.thy
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

section "Correctness proof for RSA"

theory Cryptinverts
imports  Crypt Productdivides  "HOL-Number_Theory.Residues" 
begin

text \<open>
  In this theory we show, that a RSA encrypted message can be decrypted
\<close>

primrec pred:: "nat \<Rightarrow> nat"
where
  "pred 0 = 0"
| "pred (Suc a) = a"

lemma pred_unfold:
  "pred n = n - 1"
  by (induct n) simp_all
  
lemma fermat:
  assumes "prime p" "m mod p \<noteq> 0"
  shows "m^(p-(1::nat)) mod p = 1"
proof -
  from assms have "[m ^ (p - 1) = 1] (mod p)"
    using fermat_theorem [of p m] by (simp add: mod_eq_0_iff_dvd)
  then show ?thesis
    using \<open>prime p\<close> prime_gt_1_nat [of p] by (simp add: cong_def)
qed

lemma cryptinverts_hilf1: "prime p \<Longrightarrow> (m * m ^(k * pred p)) mod p = m mod p"
  apply (cases "m mod p = 0")
  apply (simp add: mod_mult_left_eq)
  apply (simp only: mult.commute [of k "pred p"]
    power_mult mod_mult_right_eq [of "m" "(m^pred p)^k" "p"]
    remainderexp [of "m^pred p" "p" "k", symmetric])
   apply (insert fermat [of p m], auto)
  apply (simp add: mult.commute [of k] power_mult pred_unfold)
  by (metis One_nat_def mod_mult_right_eq mult.right_neutral power_Suc_0 power_mod)

lemma cryptinverts_hilf2: "prime p \<Longrightarrow> m*(m^(k * (pred p) * (pred q))) mod p = m mod p"
  apply (simp add: mult.commute [of "k * pred p" "pred q"] mult.assoc [symmetric])
  apply (rule cryptinverts_hilf1 [of "p" "m" "(pred q) * k"])
  apply simp
  done

lemma cryptinverts_hilf3: "prime q \<Longrightarrow> m*(m^(k * (pred p) * (pred q))) mod q = m mod q"
  by (fact cryptinverts_hilf1)

lemma cryptinverts_hilf4:
  "m ^ x mod (p * q) = m" if "prime p" "prime q" "p \<noteq> q"
    "m < p * q" "x mod (pred p * pred q) = 1"
proof (cases x)
  case 0
  with that show ?thesis
    by simp
next
  case (Suc x)
  with that(5) have "Suc x mod (pred p * pred q) = Suc 0"
    by simp
  then have "pred p * pred q dvd x"
    using dvd_minus_mod [of "(pred p * pred q)" "Suc x"]
    by simp
  then obtain y where "x = pred p * pred q * y" ..
  then have "m ^ Suc x mod p = m mod p" and "m ^ Suc x mod q = m mod q"
    using cryptinverts_hilf2 [of p m y q, OF \<open>prime p\<close>]
      cryptinverts_hilf3 [of q m y p, OF \<open>prime q\<close>]
    by (simp_all add: ac_simps)
  with that Suc show ?thesis
    by (auto intro: specializedtoprimes1a)
qed

lemma primmultgreater: fixes p::nat shows "\<lbrakk> prime p; prime q; p \<noteq> 2; q \<noteq> 2\<rbrakk> \<Longrightarrow> 2 < p*q"
  apply (simp add: prime_nat_iff)
  apply (insert mult_le_mono [of 2 p 2 q])
  apply auto
  done

lemma primmultgreater2: fixes p::nat shows "\<lbrakk>prime p; prime q; p \<noteq> q\<rbrakk> \<Longrightarrow>  2 < p*q"
  apply (cases "p = 2")
   apply simp+
  apply (simp add: prime_nat_iff)
  apply (cases "q = 2")
   apply (simp add: prime_nat_iff)
  apply (erule primmultgreater)
  apply auto
  done

lemma cryptinverts: "\<lbrakk> prime p; prime q; p \<noteq> q; n = p*q; m < n;
    e*d mod ((pred p)*(pred q)) = 1\<rbrakk> \<Longrightarrow> rsa_crypt (rsa_crypt m e n) d n = m"
  apply (insert cryptinverts_hilf4 [of p q m "e*d"])
  apply (insert cryptcorrect [of "p*q" "rsa_crypt m e (p * q)" d])
  apply (insert cryptcorrect [of "p*q" m e])
  apply (insert primmultgreater2 [of p q])
  apply (simp add: prime_nat_iff)
  apply (simp add: cryptcorrect remainderexp [of "m^e" "p*q" d] power_mult [symmetric])
  done

end
