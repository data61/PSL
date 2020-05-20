(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Binary Exponentiation\<close>

text \<open>This theory defines the standard algorithm for binary exponentiation, or 
  exponentiation by squaring.\<close> 
theory Binary_Exponentiation
imports 
  Main
begin

declare divmod_nat_def[termination_simp]

context monoid_mult
begin
fun binary_power :: "'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "binary_power x n = (if n = 0 then 1 else
    let (d,r) = Divides.divmod_nat n 2; 
       rec = binary_power (x * x) d in 
    if r = 0 then rec else rec * x)"

lemma binary_power[simp]: "binary_power = (^)"
proof (intro ext)
  fix x n
  show "binary_power x n = x ^ n"
  proof (induct x n rule: binary_power.induct)
    case (1 x n)
    show ?case
    proof (cases "n = 0")
      case False
      note IH = 1[OF False]
      obtain d r where n2: "Divides.divmod_nat n 2 = (d,r)" by force
      from divmod_nat_def[of n 2] n2 have dr: "d = n div 2" "r = n mod 2" by auto
      hence r: "r = 0 \<or> r = 1" by auto
      let ?rec = "binary_power (x * x) d"
      have "binary_power x n = (if r = 0 then ?rec else ?rec * x)"
        unfolding binary_power.simps[of x n] n2 using False by auto
      also have "\<dots> = ?rec * x ^ r" using r by (cases "r = 0", auto)
      also have "?rec = (x * x) ^ d"
        by (rule IH[OF _ refl], simp add: n2)
      also have "\<dots> = x ^ (d + d)" unfolding power_add
        using power2_eq_square power_even_eq power_mult by auto
      also have "\<dots> * x ^ r = x ^ (d + d + r)"
        by (simp add: power_add)
      also have "d + d + r = n" unfolding dr by presburger
      finally show ?thesis .
    qed auto
  qed
qed

lemma binary_power_code_unfold[code_unfold]: "(^) = binary_power" 
  by simp

declare binary_power.simps[simp del]
end
end
