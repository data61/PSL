section\<open>Right Complemented Monoid\<close>

theory RightComplementedMonoid
imports LeftComplementedMonoid
begin

class left_pordered_monoid_mult = order + monoid_mult +
  assumes mult_left_mono: "a \<le> b \<Longrightarrow> c * a \<le> c * b"

class integral_left_pordered_monoid_mult = left_pordered_monoid_mult + one_greatest

class right_residuated = ord + times + right_imp +
  assumes right_residual: "(a * x \<le> b) = (x \<le> a r\<rightarrow> b)"

class right_residuated_pordered_monoid = integral_left_pordered_monoid_mult + right_residuated

class right_inf = inf + times + right_imp +
  assumes inf_r_def: "(a \<sqinter> b)  = a * (a r\<rightarrow> b)"

class right_complemented_monoid = right_residuated_pordered_monoid + right_inf +
  assumes left_divisibility: "(a \<le> b) = (\<exists> c . a = b * c)"

sublocale right_complemented_monoid < dual: left_complemented_monoid "\<lambda> a b . b * a" "(\<sqinter>)" "(r\<rightarrow>)" 1 "(\<le>)" "(<)"
  apply unfold_locales
  apply (simp_all add: inf_r_def mult.assoc mult_left_mono)
  apply (simp add: right_residual)
  by (simp add: left_divisibility)

context right_complemented_monoid begin
lemma rcm_D: "a r\<rightarrow> a = 1"
  by (rule dual.lcm_D)

subclass semilattice_inf
    by unfold_locales

lemma right_semilattice_inf: "class.semilattice_inf inf (\<le>) (<)"
  by unfold_locales

  lemma right_one_inf [simp]: "1 \<sqinter> a = a"
    by simp

  lemma right_one_impl [simp]: "1 r\<rightarrow> a = a"
    by simp

  lemma rcm_A: "a * (a r\<rightarrow> b) = b * (b r\<rightarrow> a)"
    by (rule dual.lcm_A)

  lemma rcm_B: "((b * a) r\<rightarrow> c) = (a r\<rightarrow> (b r\<rightarrow> c))"
    by (rule dual.lcm_B)

  lemma rcm_C: "(a \<le> b) = ((a r\<rightarrow> b) = 1)"
    by (rule dual.lcm_C)
  end

class right_complemented_monoid_nole_algebra = right_imp + one_times + right_inf + less_def +
  assumes right_impl_one [simp]: "a r\<rightarrow> a = 1"
  and right_impl_times: "a * (a r\<rightarrow> b) = b * (b r\<rightarrow> a)"
  and right_impl_ded: "((a * b) r\<rightarrow> c) = (b r\<rightarrow> (a r\<rightarrow> c))"

class right_complemented_monoid_algebra = right_complemented_monoid_nole_algebra +
  assumes right_lesseq: "(a \<le> b) = ((a r\<rightarrow> b) = 1)"
begin
end

sublocale right_complemented_monoid_algebra < dual_algebra: left_complemented_monoid_algebra "\<lambda> a b . b * a" inf "(r\<rightarrow>)" "(\<le>)" "(<)" 1
  apply (unfold_locales, simp_all)
  by (rule inf_r_def, rule right_impl_times, rule right_impl_ded, rule right_lesseq)

context right_complemented_monoid_algebra begin

subclass right_complemented_monoid
  apply unfold_locales
  apply simp_all
  apply (simp add: dual_algebra.mult.assoc)
  apply (simp add: dual_algebra.mult_right_mono)
  apply (simp add: dual_algebra.left_residual)
  by (simp add: dual_algebra.right_divisibility)
end

lemma (in right_complemented_monoid) right_complemented_monoid: "class.right_complemented_monoid_algebra (\<le>) (<) 1 (*) inf (r\<rightarrow>)"
  by (unfold_locales, simp_all add: less_le_not_le rcm_A rcm_B rcm_C rcm_D)

(*
sublocale right_complemented_monoid < rcm: right_complemented_monoid_algebra "(\<le>)" "(<)" 1 "( * )" inf "(r\<rightarrow>)"
  by (unfold_locales, simp_all add: less_le_not_le rcm_A rcm_B rcm_C rcm_D)
*)

end
