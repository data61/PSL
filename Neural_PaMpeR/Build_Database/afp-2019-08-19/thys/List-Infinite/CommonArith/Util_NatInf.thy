(*  Title:      Util_NatInf.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

section \<open>Results for natural arithmetics with infinity\<close>

theory Util_NatInf
imports "HOL-Library.Extended_Nat"
begin

subsection \<open>Arithmetic operations with @{typ enat}\<close>

subsubsection \<open>Additional definitions\<close>

instantiation enat :: modulo
begin

definition
  div_enat_def [code del]: "
  a div b \<equiv> (case a of
    (enat x) \<Rightarrow> (case b of (enat y) \<Rightarrow> enat (x div y) | \<infinity> \<Rightarrow> 0) |
    \<infinity> \<Rightarrow> (case b of (enat y) \<Rightarrow> ((case y of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> \<infinity>)) | \<infinity> \<Rightarrow> \<infinity> ))"
definition
  mod_enat_def [code del]: "
  a mod b \<equiv> (case a of
    (enat x) \<Rightarrow> (case b of (enat y) \<Rightarrow> enat (x mod y) | \<infinity> \<Rightarrow> a) |
    \<infinity> \<Rightarrow> \<infinity>)"

instance ..

end


lemmas enat_arith_defs =
  zero_enat_def one_enat_def
  plus_enat_def diff_enat_def times_enat_def div_enat_def mod_enat_def
declare zero_enat_def[simp]


lemmas ineq0_conv_enat[simp] = i0_less[symmetric, unfolded zero_enat_def]

lemmas iless_eSuc0_enat[simp] = iless_eSuc0[unfolded zero_enat_def]


subsubsection \<open>Addition, difference, order\<close>

lemma diff_eq_conv_nat: "(x - y = (z::nat)) = (if y < x then x = y + z else z = 0)"
by auto
lemma idiff_eq_conv: "
  (x - y = (z::enat)) =
  (if y < x then x = y + z else if x \<noteq> \<infinity> then z = 0 else z = \<infinity>)"
by (case_tac x, case_tac y, case_tac z, auto, case_tac z, auto)
lemmas idiff_eq_conv_enat = idiff_eq_conv[unfolded zero_enat_def]

lemma less_eq_idiff_eq_sum: "y \<le> (x::enat) \<Longrightarrow> (z \<le> x - y) = (z + y \<le> x)"
by (case_tac x, case_tac y, case_tac z, fastforce+)


lemma eSuc_pred: "0 < n \<Longrightarrow> eSuc (n - eSuc 0) = n"
apply (case_tac n)
apply (simp add: eSuc_enat)+
done
lemmas eSuc_pred_enat = eSuc_pred[unfolded zero_enat_def]
lemmas iadd_0_enat[simp] = add_0_left[where 'a = enat, unfolded zero_enat_def]
lemmas iadd_0_right_enat[simp] = add_0_right[where 'a=enat, unfolded zero_enat_def]

lemma ile_add1: "(n::enat) \<le> n + m"
by (case_tac m, case_tac n, simp_all)
lemma ile_add2: "(n::enat) \<le> m + n"
by (simp only: add.commute[of m] ile_add1)

lemma iadd_iless_mono: "\<lbrakk> (i::enat) < j; k < l \<rbrakk> \<Longrightarrow> i + k < j + l"
by (case_tac i, case_tac k, case_tac j, case_tac l, simp_all)

lemma trans_ile_iadd1: "i \<le> (j::enat) \<Longrightarrow> i \<le> j + m"
by (rule order_trans[OF _ ile_add1])
lemma trans_ile_iadd2: "i \<le> (j::enat) \<Longrightarrow> i \<le> m + j"
by (rule order_trans[OF _ ile_add2])

lemma trans_iless_iadd1: "i < (j::enat) \<Longrightarrow> i < j + m"
by (rule order_less_le_trans[OF _ ile_add1])
lemma trans_iless_iadd2: "i < (j::enat) \<Longrightarrow> i < m + j"
by (rule order_less_le_trans[OF _ ile_add2])

lemma iadd_ileD1: "m + k \<le> (n::enat) \<Longrightarrow> m \<le> n"
by (case_tac m, case_tac n, case_tac k, simp_all)

lemma iadd_ileD2: "m + k \<le> (n::enat) \<Longrightarrow> k \<le> n"
by (rule iadd_ileD1, simp only: add.commute[of m])


lemma idiff_ile_mono: "m \<le> (n::enat) \<Longrightarrow> m - l \<le> n - l"
by (case_tac m, case_tac n, case_tac l, simp_all)

lemma idiff_ile_mono2: "m \<le> (n::enat) \<Longrightarrow> l - n \<le> l - m"
by (case_tac m, case_tac n, case_tac l, simp_all, case_tac l, simp_all)

lemma idiff_iless_mono: "\<lbrakk> m < (n::enat); l \<le> m \<rbrakk> \<Longrightarrow> m - l < n - l"
by (case_tac m, case_tac n, case_tac l, simp_all, case_tac l, simp_all)

lemma idiff_iless_mono2: "\<lbrakk> m < (n::enat); m < l \<rbrakk> \<Longrightarrow> l - n \<le> l - m"
by (case_tac m, case_tac n, case_tac l, simp_all, case_tac l, simp_all)


subsubsection \<open>Multiplication and division\<close>

lemmas imult_infinity_enat[simp] = imult_infinity[unfolded zero_enat_def]
lemmas imult_infinity_right_enat[simp] = imult_infinity_right[unfolded zero_enat_def]

lemma idiv_enat_enat[simp, code]: "enat a div enat b = enat (a div b)"
unfolding div_enat_def by simp

lemma idiv_infinity: "0 < n \<Longrightarrow> (\<infinity>::enat) div n = \<infinity>"
unfolding div_enat_def
apply (case_tac n, simp_all)
apply (rename_tac n1, case_tac n1, simp_all)
done

lemmas idiv_infinity_enat[simp] = idiv_infinity[unfolded zero_enat_def]

lemma idiv_infinity_right[simp]: "n \<noteq> \<infinity> \<Longrightarrow> n div (\<infinity>::enat) = 0"
unfolding div_enat_def by (case_tac n, simp_all)

lemma idiv_infinity_if: "n div \<infinity> = (if n = \<infinity> then \<infinity> else 0::enat)"
unfolding div_enat_def
by (case_tac n, simp_all)

lemmas idiv_infinity_if_enat = idiv_infinity_if[unfolded zero_enat_def]

lemmas imult_0_enat[simp] = mult_zero_left[where 'a=enat,unfolded zero_enat_def]
lemmas imult_0_right_enat[simp] = mult_zero_right[where 'a=enat,unfolded zero_enat_def]

lemmas imult_is_0_enat = imult_is_0[unfolded zero_enat_def]
lemmas enat_0_less_mult_iff_enat = enat_0_less_mult_iff[unfolded zero_enat_def]

lemma imult_infinity_if: "\<infinity> * n = (if n = 0 then 0 else \<infinity>::enat)"
by (case_tac n, simp_all)
lemma imult_infinity_right_if: "n * \<infinity> = (if n = 0 then 0 else \<infinity>::enat)"
by (case_tac n, simp_all)
lemmas imult_infinity_if_enat = imult_infinity_if[unfolded zero_enat_def]
lemmas imult_infinity_right_if_enat = imult_infinity_right_if[unfolded zero_enat_def]

lemmas imult_is_infinity_enat = imult_is_infinity[unfolded zero_enat_def]

lemma idiv_by_0: "(a::enat) div 0 = 0"
unfolding div_enat_def by (case_tac a, simp_all)
lemmas idiv_by_0_enat[simp, code] = idiv_by_0[unfolded zero_enat_def]

lemma idiv_0: "0 div (a::enat) = 0"
unfolding div_enat_def by (case_tac a, simp_all)
lemmas idiv_0_enat[simp, code] = idiv_0[unfolded zero_enat_def]

lemma imod_by_0: "(a::enat) mod 0 = a"
unfolding mod_enat_def by (case_tac a, simp_all)
lemmas imod_by_0_enat[simp, code] = imod_by_0[unfolded zero_enat_def]

lemma imod_0: "0 mod (a::enat) = 0"
unfolding mod_enat_def by (case_tac a, simp_all)
lemmas imod_0_enat[simp, code] = imod_0[unfolded zero_enat_def]

lemma imod_enat_enat[simp, code]: "enat a mod enat b = enat (a mod b)"
unfolding mod_enat_def by simp
lemma imod_infinity[simp, code]: "\<infinity> mod n = (\<infinity>::enat)"
unfolding mod_enat_def by simp
lemma imod_infinity_right[simp, code]: "n mod (\<infinity>::enat) = n"
unfolding mod_enat_def by (case_tac n) simp_all

lemma idiv_self: "\<lbrakk> 0 < (n::enat); n \<noteq> \<infinity> \<rbrakk> \<Longrightarrow> n div n = 1"
by (case_tac n, simp_all add: one_enat_def)
lemma imod_self: "n \<noteq> \<infinity> \<Longrightarrow> (n::enat) mod n = 0"
by (case_tac n, simp_all)

lemma idiv_iless: "m < (n::enat) \<Longrightarrow> m div n = 0"
by (case_tac m, simp_all) (case_tac n, simp_all)
lemma imod_iless: "m < (n::enat) \<Longrightarrow> m mod n = m"
by (case_tac m, simp_all) (case_tac n, simp_all)

lemma imod_iless_divisor: "\<lbrakk> 0 < (n::enat); m \<noteq> \<infinity> \<rbrakk>  \<Longrightarrow> m mod n < n"
by (case_tac m, simp_all) (case_tac n, simp_all)
lemma imod_ile_dividend: "(m::enat) mod n \<le> m"
by (case_tac m, simp_all) (case_tac n, simp_all)
lemma idiv_ile_dividend: "(m::enat) div n \<le> m"
by (case_tac m, simp_all) (case_tac n, simp_all)

lemma idiv_imult2_eq: "(a::enat) div (b * c) = a div b div c"
apply (case_tac a, case_tac b, case_tac c, simp_all add: div_mult2_eq)
apply (simp add: imult_infinity_if)
apply (case_tac "b = 0", simp)
apply (case_tac "c = 0", simp)
apply (simp add: idiv_infinity[OF enat_0_less_mult_iff[THEN iffD2]])
done

lemma imult_ile_mono: "\<lbrakk> (i::enat) \<le> j; k \<le> l \<rbrakk> \<Longrightarrow> i * k \<le> j * l"
apply (case_tac i, case_tac j, case_tac k, case_tac l, simp_all add: mult_le_mono)
apply (case_tac k, case_tac l, simp_all)
apply (case_tac k, case_tac l, simp_all)
done

lemma imult_ile_mono1: "(i::enat) \<le> j \<Longrightarrow> i * k \<le> j * k"
by (rule imult_ile_mono[OF _ order_refl])

lemma imult_ile_mono2: "(i::enat) \<le> j \<Longrightarrow> k * i \<le> k * j"
by (rule imult_ile_mono[OF order_refl])

lemma imult_iless_mono1: "\<lbrakk> (i::enat) < j; 0 < k; k \<noteq> \<infinity> \<rbrakk> \<Longrightarrow> i * k \<le> j * k"
by (case_tac i, case_tac j, case_tac k, simp_all)
lemma imult_iless_mono2: "\<lbrakk> (i::enat) < j; 0 < k; k \<noteq> \<infinity> \<rbrakk> \<Longrightarrow> k * i \<le> k * j"
by (simp only: mult.commute[of k], rule imult_iless_mono1)

lemma imod_1: "(enat m) mod eSuc 0 = 0"
by (simp add: eSuc_enat)
lemmas imod_1_enat[simp, code] = imod_1[unfolded zero_enat_def]

lemma imod_iadd_self2: "(m + enat n) mod (enat n) = m mod (enat n)"
by (case_tac m, simp_all)

lemma imod_iadd_self1: "(enat n + m) mod (enat n) = m mod (enat n)"
by (simp only: add.commute[of _ m] imod_iadd_self2)

lemma idiv_imod_equality: "(m::enat) div n * n + m mod n + k = m + k"
by (case_tac m, simp_all) (case_tac n, simp_all)
lemma imod_idiv_equality: "(m::enat) div n * n + m mod n = m"
by (insert idiv_imod_equality[of m n 0], simp)

lemma idiv_ile_mono: "m \<le> (n::enat) \<Longrightarrow> m div k \<le> n div k"
apply (case_tac "k = 0", simp)
apply (case_tac m, case_tac k, simp_all)
apply (case_tac n)
 apply (simp add: div_le_mono)
apply (simp add: idiv_infinity)
apply (simp add: i0_lb[unfolded zero_enat_def])
done
lemma idiv_ile_mono2: "\<lbrakk> 0 < m; m \<le> (n::enat) \<rbrakk> \<Longrightarrow> k div n \<le> k div m"
apply (case_tac "n = 0", simp)
apply (case_tac m, case_tac k, simp_all)
apply (case_tac n)
 apply (simp add: div_le_mono2)
apply simp
done

end
