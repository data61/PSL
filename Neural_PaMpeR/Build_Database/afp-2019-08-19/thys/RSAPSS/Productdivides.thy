(*  Title:      RSAPSS/Productdivides.thy
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

section "Lemmata for modular arithmetic with primes"

theory Productdivides
imports Pdifference
begin

lemma productdivides: "\<lbrakk>x mod a = (0::nat); x mod b = 0; prime a; prime b; a \<noteq> b\<rbrakk> \<Longrightarrow> x mod (a*b) = 0"
  by (simp add: mod_eq_0_iff_dvd primes_coprime divides_mult)

lemma specializedtoprimes1: 
  fixes p::nat 
  shows "\<lbrakk>prime p; prime q; p \<noteq> q; a mod p = b mod p ; a mod q = b mod q\<rbrakk>
         \<Longrightarrow> a mod (p*q) = b mod (p*q)"
by (metis equalmodstrick1 equalmodstrick2 productdivides) 

lemma specializedtoprimes1a:
  fixes p::nat 
  shows "\<lbrakk>prime p; prime q; p \<noteq> q; a mod p = b mod p; a mod q = b mod q; b < p*q \<rbrakk>
    \<Longrightarrow> a mod (p*q) = b"
  by (simp add: specializedtoprimes1)
  
end
