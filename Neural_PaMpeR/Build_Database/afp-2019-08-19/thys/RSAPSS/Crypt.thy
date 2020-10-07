(*  Title:      RSAPSS/Crypt.thy
 
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

section "Definition of rsacrypt"

theory Crypt
imports Main Mod
begin

text \<open>
  This theory defines the rsacrypt function which implements RSA using fast
  exponentiation. An proof, that this function calculates RSA is also given
\<close>

definition rsa_crypt :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  cryptcorrect: "rsa_crypt M e n = M ^ e mod n"

lemma rsa_crypt_code [code]:
  "rsa_crypt M e n = (if e = 0 then 1 mod n
    else if even e then rsa_crypt M (e div 2) n ^ 2 mod n
    else (M * rsa_crypt M (e div 2) n ^ 2 mod n) mod n)"
proof -
  { fix m
    have "(M ^ m mod n)\<^sup>2 mod n = (M ^ m)\<^sup>2 mod n"
      by (simp add: power_mod)
    then have "(M mod n) * ((M ^ m mod n)\<^sup>2 mod n) = (M mod n) * ((M ^ m)\<^sup>2 mod n)"
      by simp
    have "M * (M ^ m mod n)\<^sup>2 mod n = M * (M ^ m)\<^sup>2 mod n"
      by (metis mod_mult_right_eq power_mod)
  }
  then show ?thesis
    by (auto simp add: cryptcorrect power_even_eq remainderexp elim!: evenE oddE)
qed

end

