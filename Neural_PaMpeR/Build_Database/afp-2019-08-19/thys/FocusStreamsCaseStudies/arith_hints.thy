(*<*)
(*
   Title:  Theory arith_hints.thy 
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*)
(*>*)
section \<open>Auxiliary arithmetic lemmas\<close>

theory arith_hints
imports Main
begin

lemma arith_mod_neq:
  assumes "a mod n \<noteq> b mod n"
  shows "a \<noteq> b"
  using assms by blast

lemma arith_mod_nzero: 
  fixes i :: nat
  assumes "i < n" and "0 < i"
  shows "0 < (n * t + i) mod n"
  using assms by simp

lemma arith_mult_neq_nzero1:
  fixes i::nat
  assumes "i < n"
         and "0 < i"
  shows "i + n * t \<noteq> n * q"
proof -
  from assms have sg1:"(i + n * t) mod n = i"  by auto
  also have sg2:"(n * q) mod n = 0"  by simp
  from this and assms have "(i + n * t) mod n \<noteq> (n * q) mod n"
    by simp
  from this show ?thesis  by (rule arith_mod_neq)
qed

lemma arith_mult_neq_nzero2:
  fixes i::nat
  assumes "i < n"
         and "0 < i"
  shows "n * t + i \<noteq> n * q"
using assms
by (metis arith_mult_neq_nzero1 add.commute) 

lemma arith_mult_neq_nzero3:
  fixes i::nat
  assumes "i < n"
         and "0 < i"
  shows "n + n * t + i \<noteq> n * qc"
proof -
   from assms have sg1: "n *(Suc t) + i  \<noteq> n * qc"
     by (rule arith_mult_neq_nzero2)
   have sg2: "n + n * t + i = n *(Suc t) + i" by simp
   from sg1 and sg2  show ?thesis  by arith
qed

lemma arith_modZero1:
  "(t + n * t) mod Suc n = 0"
by (metis mod_mult_self1_is_0 mult_Suc)

lemma arith_modZero2:
  "Suc (n + (t + n * t)) mod Suc n = 0"
by (metis add_Suc_right add_Suc_shift mod_mult_self1_is_0 mult_Suc mult.commute)

lemma arith1:
  assumes h1:"Suc n * t = Suc n * q"
  shows "t = q"
using assms
by (metis mult_cancel2 mult.commute neq0_conv zero_less_Suc)

lemma arith2:
  fixes t n q :: "nat"
  assumes h1:"t + n * t = q + n * q"
  shows "t = q"
using assms
by (metis arith1 mult_Suc)

end
