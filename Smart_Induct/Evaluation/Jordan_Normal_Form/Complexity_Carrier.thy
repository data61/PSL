(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Complexity Carrier\<close>

text \<open>We define which properties a carrier of matrices must exhibit, so that it
  can be used for checking complexity proofs.\<close>

theory Complexity_Carrier
imports
  "Abstract-Rewriting.SN_Order_Carrier"
  Ring_Hom_Matrix
  Derivation_Bound
  HOL.Real
begin

class large_real_ordered_semiring_1 = large_ordered_semiring_1 + real_embedding

instance real :: large_real_ordered_semiring_1 ..
instance int :: large_real_ordered_semiring_1 ..
instance rat :: large_real_ordered_semiring_1 ..

text \<open>For complexity analysis, we need a bounding function which tells us how often
  one can strictly decrease a value. To this end, $\delta$-orderings are usually applied
  when working with the reals or rational numbers.\<close>

locale complexity_one_mono_ordered_semiring_1 = one_mono_ordered_semiring_1 default gt 
  for gt :: "'a :: large_ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succ>" 50) and default :: 'a + 
  fixes bound :: "'a \<Rightarrow> nat"
  assumes bound_mono: "\<And> a b. a \<ge> b \<Longrightarrow> bound a \<ge> bound b"
   and bound_plus: "\<And> a b. bound (a + b) \<le> bound a + bound b" 
   and bound_plus_of_nat: "\<And> a n. a \<ge> 0 \<Longrightarrow> bound (a + of_nat n) = bound a + bound (of_nat n)" 
   and bound_zero[simp]: "bound 0 = 0"
   and bound_one: "bound 1 \<ge> 1"
   and bound: "\<And> a. deriv_bound {(a,b). b \<ge> 0 \<and> a \<succ> b} a (bound a)"
begin


lemma bound_linear: "\<exists> c. \<forall> n. bound (of_nat n) \<le> c * n"
proof (rule exI[of _ "bound 1"], intro allI)
  fix n
  show "bound (of_nat n) \<le> bound 1 * n"
  proof (induct n)
    case (Suc n)
    have "bound (of_nat (Suc n)) = bound (1 + of_nat n)" by simp
    also have "... \<le> bound 1 + bound (of_nat n)"
      by (rule bound_plus)
    also have "... \<le> bound 1 + bound 1 * n"
      using Suc by auto
    finally show ?case by auto
  qed simp
qed

lemma bound_of_nat_times: "bound (of_nat n * v) \<le> n * bound v"
proof (induct n)
  case (Suc n)
  have "bound (of_nat (Suc n) * v) = bound (v + of_nat n * v)" by (simp add: field_simps)
  also have "\<dots> \<le> bound v + bound (of_nat n * v)" by (rule bound_plus)
  also have "\<dots> \<le> bound v + n * bound v" using Suc by auto
  finally show ?case by simp 
qed simp

lemma bound_mult_of_nat: "bound (a * of_nat n) \<le> bound a * bound (of_nat n)"
proof (induct n)
  case (Suc n)
  have "bound (a * of_nat (Suc n)) = bound (a + a * of_nat n)" by (simp add: field_simps)
  also have "... \<le> bound a + bound (a * of_nat n)"
    by (rule bound_plus)
  also have "... \<le> bound a + bound a * bound (of_nat n)" using Suc by auto
  also have "... = bound a * (1 + bound (of_nat n))" by (simp add: field_simps)
  also have "... \<le> bound a * (bound (1 + of_nat n))"
  proof (rule mult_le_mono2)
    show "1 + bound(of_nat n) \<le> bound (1 + of_nat n)" using bound_one
    using bound_plus
      unfolding bound_plus_of_nat[OF one_ge_zero] by simp
  qed
  finally show ?case by simp
qed simp

lemma bound_pow_of_nat: "bound (a * of_nat n ^ deg) \<le> bound a * of_nat n ^ deg" 
proof (induct deg)
  case (Suc deg)
  have "bound (a * of_nat n ^ Suc deg) =  bound (of_nat n * (a * of_nat n ^ deg))"
    by (simp add: field_simps)
  also have "\<dots> \<le> n * bound (a * of_nat n ^ deg)"
    by (rule bound_of_nat_times)
  also have "\<dots> \<le> n * (bound a * of_nat n ^ deg)"
    using Suc by auto
  finally show ?case by (simp add: field_simps)
qed simp
end

end
