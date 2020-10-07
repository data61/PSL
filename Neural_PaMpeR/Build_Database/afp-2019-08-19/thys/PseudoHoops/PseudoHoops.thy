section\<open>Pseudo-Hoops\<close>

theory PseudoHoops
imports RightComplementedMonoid
begin

lemma drop_assumption:
  "p \<Longrightarrow> True"
  by simp

class pseudo_hoop_algebra = left_complemented_monoid_algebra + right_complemented_monoid_nole_algebra +
  assumes left_right_impl_times: "(a l\<rightarrow> b) * a = a * (a r\<rightarrow> b)"
begin
  definition 
    "inf_rr a b  = a * (a r\<rightarrow> b)"

  definition
    "lesseq_r a b = (a r\<rightarrow> b = 1)"

  definition
    "less_r a b = (lesseq_r a b \<and> \<not> lesseq_r b a)"
end

(*
sublocale pseudo_hoop_algebra < right: right_complemented_monoid_algebra lesseq_r less_r 1 "( * )" inf_rr "(r\<rightarrow>)";
  apply unfold_locales;
  apply simp_all;
  apply (simp add: less_r_def);
  apply (simp add: inf_rr_def);
  apply (rule right_impl_times, rule right_impl_ded);
  by (simp add: lesseq_r_def);
*)

context pseudo_hoop_algebra begin

  lemma right_complemented_monoid_algebra: "class.right_complemented_monoid_algebra lesseq_r less_r 1 (*) inf_rr (r\<rightarrow>)"
   (* by unfold_locales;*)
  apply unfold_locales
  apply simp_all
  apply (simp add: less_r_def)
  apply (simp add: inf_rr_def)
  apply (rule right_impl_times, rule right_impl_ded)
  by (simp add: lesseq_r_def)

  lemma inf_rr_inf [simp]: "inf_rr = (\<sqinter>)"
    by (unfold fun_eq_iff, simp add: inf_rr_def inf_l_def left_right_impl_times)


  lemma lesseq_lesseq_r: "lesseq_r a b = (a \<le> b)"
  proof -
    interpret A: right_complemented_monoid_algebra lesseq_r less_r 1 "(*)" inf_rr "(r\<rightarrow>)"
      by (rule right_complemented_monoid_algebra)
    show "lesseq_r a b = (a \<le> b)"
      apply (subst  le_iff_inf)
      apply (subst A.dual_algebra.inf.absorb_iff1 [of a b])
      apply (unfold inf_rr_inf [THEN sym])
      by simp
  qed
  lemma [simp]: "lesseq_r = (\<le>)"
    apply (unfold fun_eq_iff, simp add: lesseq_lesseq_r) done

  lemma [simp]: "less_r = (<)"
    by (unfold fun_eq_iff, simp add: less_r_def less_le_not_le)
    

  subclass right_complemented_monoid_algebra 
    apply (cut_tac right_complemented_monoid_algebra)
    by simp
  end

sublocale pseudo_hoop_algebra < 
     pseudo_hoop_dual: pseudo_hoop_algebra "\<lambda> a b . b * a" "(\<sqinter>)" "(r\<rightarrow>)" "(\<le>)" "(<)" 1 "(l\<rightarrow>)"
  apply unfold_locales
  apply (simp add: inf_l_def)
  apply simp
  apply (simp add: left_impl_times)
  apply (simp add: left_impl_ded)
  by (simp add: left_right_impl_times)

context pseudo_hoop_algebra begin
lemma commutative_ps: "(\<forall> a b . a * b = b * a) = ((l\<rightarrow>) = (r\<rightarrow>))"
  apply (simp add: fun_eq_iff)
  apply safe
  apply (rule antisym)
  apply (simp add: right_residual [THEN sym])
  apply (subgoal_tac "x * (x l\<rightarrow> xa) =  (x l\<rightarrow> xa) * x")
  apply (drule drop_assumption)
  apply simp
  apply (simp add: left_residual)
  apply simp
  apply (simp add: left_residual [THEN sym])
  apply (simp add: right_residual)
  apply (rule antisym)
  apply (simp add: left_residual)
  apply (simp add: right_residual [THEN sym])
  apply (simp add: left_residual)
  by (simp add: right_residual [THEN sym])

lemma lemma_2_4_5: "a l\<rightarrow> b \<le> (c l\<rightarrow> a) l\<rightarrow> (c l\<rightarrow> b)"
  apply (simp add: left_residual [THEN sym] mult.assoc)
  apply (rule_tac y = "(a l\<rightarrow> b) * a" in order_trans)
  apply (rule mult_left_mono)
  by (simp_all add: left_residual)

end

context pseudo_hoop_algebra begin

lemma lemma_2_4_6: "a r\<rightarrow> b \<le> (c r\<rightarrow> a) r\<rightarrow> (c r\<rightarrow> b)"
  by (rule pseudo_hoop_dual.lemma_2_4_5)

primrec
  imp_power_l:: "'a => nat \<Rightarrow> 'a \<Rightarrow> 'a" ("(_) l-(_)\<rightarrow> (_)" [65,0,65] 65) where 
   "a l-0\<rightarrow> b = b" |
   "a l-(Suc n)\<rightarrow> b = (a l\<rightarrow> (a l-n\<rightarrow> b))"

primrec
  imp_power_r:: "'a => nat \<Rightarrow> 'a \<Rightarrow> 'a" ("(_) r-(_)\<rightarrow> (_)" [65,0,65] 65) where 
   "a r-0\<rightarrow> b = b" |
   "a r-(Suc n)\<rightarrow> b = (a r\<rightarrow> (a r-n\<rightarrow> b))"

lemma lemma_2_4_7_a: "a l-n\<rightarrow> b = a ^ n l\<rightarrow> b" 
  apply (induct_tac n)
  by (simp_all add: left_impl_ded)

lemma lemma_2_4_7_b: "a r-n\<rightarrow> b = a ^ n r\<rightarrow> b" 
  apply (induct_tac n)
  by (simp_all add: right_impl_ded [THEN sym] power_commutes)

lemma lemma_2_5_8_a [simp]: "a * b \<le> a"
  by (rule dual_algebra.H)

lemma lemma_2_5_8_b [simp]: "a * b \<le> b"
  by (rule H)


lemma lemma_2_5_9_a: "a \<le> b l\<rightarrow> a"
  by (simp add: left_residual [THEN sym] dual_algebra.H)

lemma lemma_2_5_9_b: "a \<le> b r\<rightarrow> a"
  by (simp add: right_residual [THEN sym] H)

lemma lemma_2_5_11: "a * b \<le> a \<sqinter> b"
  by simp

lemma lemma_2_5_12_a: "a \<le> b \<Longrightarrow>  c l\<rightarrow> a \<le> c l\<rightarrow> b"
  apply (subst left_residual [THEN sym])
  apply (subst left_impl_times)
  apply (rule_tac y = "(a l\<rightarrow> c) * b" in order_trans)
  apply (simp add: mult_left_mono)
  by (rule H)

lemma lemma_2_5_13_a: "a \<le> b \<Longrightarrow>  b l\<rightarrow> c \<le> a l\<rightarrow> c"
  apply (simp add: left_residual [THEN sym])
  apply (rule_tac y = "(b l\<rightarrow> c) * b" in order_trans)
  apply (simp add: mult_left_mono)
  by (simp add: left_residual)

lemma lemma_2_5_14: "(b l\<rightarrow> c) * (a l\<rightarrow> b) \<le> a l\<rightarrow> c"
  apply (simp add: left_residual [THEN sym])
  apply (simp add: mult.assoc)
  apply (subst left_impl_times)
  apply (subst mult.assoc [THEN sym])
  apply (subst left_residual)
  by (rule dual_algebra.H)

lemma lemma_2_5_16: "(a l\<rightarrow> b) \<le>  (b l\<rightarrow> c) r\<rightarrow> (a l\<rightarrow> c)"
  apply (simp add: right_residual [THEN sym])
  by (rule lemma_2_5_14)

lemma lemma_2_5_18: "(a l\<rightarrow> b) \<le>  a * c l\<rightarrow> b * c"
  apply (simp add: left_residual  [THEN sym])
  apply (subst mult.assoc  [THEN sym])
  apply (rule mult_right_mono)
  apply (subst left_impl_times)
  by (rule H)

end

context pseudo_hoop_algebra begin

lemma lemma_2_5_12_b: "a \<le> b \<Longrightarrow>  c r\<rightarrow> a \<le> c r\<rightarrow> b"
  by (rule pseudo_hoop_dual.lemma_2_5_12_a)

lemma lemma_2_5_13_b: "a \<le> b \<Longrightarrow>  b r\<rightarrow> c \<le> a r\<rightarrow> c"
  by (rule pseudo_hoop_dual.lemma_2_5_13_a)

lemma lemma_2_5_15: "(a r\<rightarrow> b) * (b r\<rightarrow> c) \<le> a r\<rightarrow> c"
  by (rule pseudo_hoop_dual.lemma_2_5_14)

lemma lemma_2_5_17: "(a r\<rightarrow> b) \<le>  (b r\<rightarrow> c) l\<rightarrow> (a r\<rightarrow> c)"
  by (rule pseudo_hoop_dual.lemma_2_5_16)

lemma lemma_2_5_19: "(a r\<rightarrow> b) \<le>  c * a r\<rightarrow> c * b"
  by (rule pseudo_hoop_dual.lemma_2_5_18)

definition
  "lower_bound A = {a . \<forall> x \<in> A . a \<le> x}"

definition
  "infimum A = {a \<in> lower_bound A . (\<forall> x \<in> lower_bound A . x \<le> a)}"

lemma infimum_unique: "(infimum A = {x}) = (x \<in> infimum A)"
  apply safe
  apply simp
  apply (rule antisym)
  by (simp_all add: infimum_def)

lemma lemma_2_6_20:
  "a \<in> infimum A \<Longrightarrow> b l\<rightarrow> a \<in> infimum (((l\<rightarrow>) b)`A)"
  apply (subst infimum_def)
  apply safe
  apply (simp add: infimum_def lower_bound_def lemma_2_5_12_a)
  by (simp add: infimum_def lower_bound_def left_residual  [THEN sym])

end

context pseudo_hoop_algebra begin

lemma lemma_2_6_21:
  "a \<in> infimum A \<Longrightarrow> b r\<rightarrow> a \<in> infimum (((r\<rightarrow>) b)`A)"
  by (rule pseudo_hoop_dual.lemma_2_6_20)

lemma infimum_pair: "a \<in> infimum {x . x = b \<or> x = c} = (a = b \<sqinter> c)"
  apply (simp add: infimum_def lower_bound_def)
  apply safe
  apply (rule antisym)
  by simp_all
 
lemma lemma_2_6_20_a:
  "a l\<rightarrow> (b \<sqinter> c) = (a l\<rightarrow> b) \<sqinter> (a l\<rightarrow> c)"
  apply (subgoal_tac "b \<sqinter> c \<in> infimum {x . x = b \<or> x = c}")
  apply (drule_tac b = a in lemma_2_6_20)
  apply (case_tac "((l\<rightarrow>) a) ` {x . ((x = b) \<or> (x = c))} = {x . x = a l\<rightarrow> b \<or> x = a l\<rightarrow> c}")
  apply (simp_all add: infimum_pair)
  by auto
end

context pseudo_hoop_algebra begin

lemma lemma_2_6_21_a:
  "a r\<rightarrow> (b \<sqinter> c) = (a r\<rightarrow> b) \<sqinter> (a r\<rightarrow> c)"
  by (rule pseudo_hoop_dual.lemma_2_6_20_a)

lemma mult_mono: "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a * c \<le> b * d"
  apply (rule_tac y = "a * d" in order_trans)
  by (simp_all add: mult_right_mono mult_left_mono)

lemma lemma_2_7_22: "(a l\<rightarrow> b) * (c l\<rightarrow> d) \<le> (a \<sqinter> c) l\<rightarrow> (b \<sqinter> d)"
  apply (rule_tac y = "(a \<sqinter> c l\<rightarrow> b) * (a \<sqinter> c l\<rightarrow> d)" in order_trans)
  apply (rule mult_mono)
  apply (simp_all add: lemma_2_5_13_a)
  apply (rule_tac y = "(a \<sqinter> c l\<rightarrow> b) \<sqinter> (a \<sqinter> c l\<rightarrow> d)" in order_trans)
  apply (rule lemma_2_5_11)
  by (simp add: lemma_2_6_20_a)

end

context pseudo_hoop_algebra begin
lemma lemma_2_7_23: "(a r\<rightarrow> b) * (c r\<rightarrow> d) \<le> (a \<sqinter> c) r\<rightarrow> (b \<sqinter> d)"
  apply (rule_tac y = "(c \<sqinter> a) r\<rightarrow> (d \<sqinter> b)" in order_trans)
  apply (rule pseudo_hoop_dual.lemma_2_7_22)
  by (simp add: inf_commute)

definition
  "upper_bound A = {a . \<forall> x \<in> A . x \<le> a}"

definition
  "supremum A = {a \<in> upper_bound A . (\<forall> x \<in> upper_bound A . a \<le> x)}"

lemma supremum_unique:
  "a \<in> supremum A \<Longrightarrow> b \<in> supremum A \<Longrightarrow> a = b"
  apply (simp add: supremum_def upper_bound_def)
  apply (rule antisym)
  by auto

lemma lemma_2_8_i:
  "a \<in> supremum A \<Longrightarrow> a l\<rightarrow> b \<in> infimum ((\<lambda> x . x l\<rightarrow> b)`A)"
  apply (subst infimum_def)
  apply safe
  apply (simp add: supremum_def upper_bound_def lower_bound_def lemma_2_5_13_a)
  apply (simp add: supremum_def upper_bound_def lower_bound_def left_residual  [THEN sym])
  by (simp add: right_residual)

end


context pseudo_hoop_algebra begin

lemma lemma_2_8_i1:
  "a \<in> supremum A \<Longrightarrow> a r\<rightarrow> b \<in> infimum ((\<lambda> x . x r\<rightarrow> b)`A)"
  by (rule pseudo_hoop_dual.lemma_2_8_i, simp)

definition
  times_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"  (infixl "**" 70) where
  "(A ** B) = {a . \<exists> x \<in> A . \<exists> y \<in> B . a = x * y}"

lemma times_set_assoc: "A ** (B ** C) = (A ** B) ** C"
  apply (simp add: times_set_def)
  apply safe
  apply (rule_tac x = "xa * xb" in exI)
  apply safe
  apply (rule_tac x = xa in bexI)
  apply (rule_tac x = xb in bexI)
  apply simp_all
  apply (subst mult.assoc)
  apply (rule_tac x = ya in bexI)
  apply simp_all
  apply (rule_tac x = xb in bexI)
  apply simp_all
  apply (rule_tac x = "ya * y" in exI)
  apply (subst mult.assoc)
  apply simp
  by auto


primrec power_set :: "'a set \<Rightarrow> nat \<Rightarrow> 'a set" (infixr "*^" 80) where
    power_set_0: "(A *^ 0) = {1}"
  | power_set_Suc: "(A *^ (Suc n)) = (A ** (A *^ n))"


lemma infimum_singleton [simp]: "infimum {a} = {a}"
  apply (simp add: infimum_def lower_bound_def)
  by auto
  

lemma lemma_2_8_ii:
  "a \<in> supremum A \<Longrightarrow> (a ^ n) l\<rightarrow> b \<in> infimum ((\<lambda> x . x l\<rightarrow> b)`(A *^ n))"
  apply (induct_tac n)
  apply simp
  apply (simp add: left_impl_ded)
  apply (drule_tac a = "a ^ n l\<rightarrow> b" and b = a in lemma_2_6_20)
  apply (simp add: infimum_def lower_bound_def times_set_def)
  apply safe
  apply (drule_tac b = "y l\<rightarrow> b" in lemma_2_8_i)
  apply (simp add: infimum_def lower_bound_def times_set_def left_impl_ded)
  apply (rule_tac y = "a l\<rightarrow> y l\<rightarrow> b" in order_trans)
  apply simp_all
  apply (subgoal_tac "(\<forall>xa \<in> A *^ n. x \<le> a l\<rightarrow> xa l\<rightarrow> b)")
  apply simp
  apply safe
  apply (drule_tac b = "xa l\<rightarrow> b" in lemma_2_8_i)
  apply (simp add: infimum_def lower_bound_def)
  apply safe
  apply (subgoal_tac "(\<forall>xb \<in> A. x \<le> xb l\<rightarrow> xa l\<rightarrow> b)")
  apply simp
  apply safe
  apply (subgoal_tac "x \<le> xb * xa l\<rightarrow> b")
  apply (simp add: left_impl_ded)
  apply (subgoal_tac "(\<exists>x \<in> A. \<exists>y \<in> A *^ n. xb * xa = x * y)")
  by auto

lemma power_set_Suc2:
  "A *^ (Suc n) = A *^ n ** A"
  apply (induct_tac n)
  apply (simp add: times_set_def)
  apply simp
  apply (subst times_set_assoc)
  by simp

lemma power_set_add:
  "A *^ (n + m) = (A *^ n) ** (A *^ m)"
  apply (induct_tac m)
  apply simp
  apply (simp add: times_set_def)
  apply simp
  apply (subst times_set_assoc)
  apply (subst times_set_assoc)
  apply (subst power_set_Suc2 [THEN sym])
  by simp
end

context pseudo_hoop_algebra begin

lemma lemma_2_8_ii1:
  "a \<in> supremum A \<Longrightarrow> (a ^ n) r\<rightarrow> b \<in> infimum ((\<lambda> x . x r\<rightarrow> b)`(A *^ n))"
  apply (induct_tac n)
  apply simp
  apply (subst power_Suc2)
  apply (subst power_set_Suc2)
  apply (simp add: right_impl_ded)
  apply (drule_tac a = "a ^ n r\<rightarrow> b" and b = a in lemma_2_6_21)
  apply (simp add: infimum_def lower_bound_def times_set_def)
  apply safe
  apply (drule_tac b = "xa r\<rightarrow> b" in lemma_2_8_i1)
  apply (simp add: infimum_def lower_bound_def times_set_def right_impl_ded)
  apply (rule_tac y = "a r\<rightarrow> xa r\<rightarrow> b" in order_trans)
  apply simp_all
  apply (subgoal_tac "(\<forall>xa \<in> A *^ n. x \<le> a r\<rightarrow> xa r\<rightarrow> b)")
  apply simp
  apply safe
  apply (drule_tac b = "xa r\<rightarrow> b" in lemma_2_8_i1)
  apply (simp add: infimum_def lower_bound_def)
  apply safe
  apply (subgoal_tac "(\<forall>xb \<in> A. x \<le> xb r\<rightarrow> xa r\<rightarrow> b)")
  apply simp
  apply safe
  apply (subgoal_tac "x \<le> xa * xb r\<rightarrow> b")
  apply (simp add: right_impl_ded)
  apply (subgoal_tac "(\<exists>x \<in> A *^ n. \<exists>y \<in> A . xa * xb = x * y)")
  by auto

lemma lemma_2_9_i:
  "b \<in> supremum A \<Longrightarrow> a * b \<in> supremum ((*) a ` A)"
  apply (simp add: supremum_def upper_bound_def)
  apply safe
  apply (simp add: mult_left_mono)
  by (simp add: right_residual)
 
lemma lemma_2_9_i1:
  "b \<in> supremum A \<Longrightarrow> b * a \<in> supremum ((\<lambda> x . x * a) ` A)"
  apply (simp add: supremum_def upper_bound_def)
  apply safe
  apply (simp add: mult_right_mono)
  by (simp add: left_residual)


lemma lemma_2_9_ii:
  "b \<in> supremum A \<Longrightarrow> a \<sqinter> b \<in> supremum ((\<sqinter>) a ` A)"
  apply (subst supremum_def)
  apply safe
  apply (simp add: supremum_def upper_bound_def)
  apply safe
  apply (rule_tac y = x in order_trans)
  apply simp_all
  apply (subst inf_commute)
  apply (subst inf_l_def)
  apply (subst left_right_impl_times)
  apply (frule_tac a = "(b r\<rightarrow> a)" in lemma_2_9_i1)
  apply (simp add: right_residual)
  apply (simp add: supremum_def upper_bound_def)
  apply (simp add: right_residual)
  apply safe
  apply (subgoal_tac "(\<forall>xa \<in> A. b r\<rightarrow> a \<le> xa r\<rightarrow> x)")
  apply simp
  apply safe
  apply (simp add: inf_l_def)
  apply (simp add: left_right_impl_times)
  apply (rule_tac y = "xa r\<rightarrow>  b * (b r\<rightarrow> a)" in order_trans)
  apply simp
  apply (rule lemma_2_5_12_b)
  apply (subst left_residual)
  apply (subgoal_tac "(\<forall>xa\<in>A. xa \<le> (b r\<rightarrow> a) l\<rightarrow> x)")
  apply simp
  apply safe
  apply (subst left_residual [THEN sym])
  apply (rule_tac y = "xaa * (xaa r\<rightarrow> a)" in order_trans)
  apply (rule mult_left_mono)
  apply (rule lemma_2_5_13_b)
  apply simp
  apply (subst right_impl_times)
  by simp

lemma lemma_2_10_24:
  "a \<le> (a l\<rightarrow> b) r\<rightarrow> b"
  by (simp add: right_residual [THEN sym] inf_l_def [THEN sym])

lemma lemma_2_10_25:
  "a \<le> (a l\<rightarrow> b) r\<rightarrow> a"
  by (rule lemma_2_5_9_b)
end

context pseudo_hoop_algebra begin
lemma lemma_2_10_26:
  "a \<le> (a r\<rightarrow> b) l\<rightarrow> b"
  by (rule pseudo_hoop_dual.lemma_2_10_24)

lemma lemma_2_10_27:
  "a \<le> (a r\<rightarrow> b) l\<rightarrow> a"
  by (rule lemma_2_5_9_a)

lemma lemma_2_10_28:
  "b l\<rightarrow> ((a l\<rightarrow> b) r\<rightarrow> a) = b l\<rightarrow> a"
  apply (rule antisym)
  apply (subst left_residual [THEN sym])
  apply (rule_tac y = "((a l\<rightarrow> b) r\<rightarrow> a) \<sqinter> a" in order_trans)
  apply (subst inf_l_def)
  apply (rule_tac y = "(((a l\<rightarrow> b) r\<rightarrow> a) l\<rightarrow> b) * ((a l\<rightarrow> b) r\<rightarrow> a)" in order_trans)
  apply (subst left_impl_times)
  apply simp_all
  apply (rule mult_right_mono)
  apply (rule_tac y = "a l\<rightarrow> b" in order_trans)
  apply (rule lemma_2_5_13_a) 
  apply (fact lemma_2_10_25)
  apply (fact lemma_2_10_26)
  apply (rule lemma_2_5_12_a) 
  by (fact lemma_2_10_25)

end
  
context pseudo_hoop_algebra begin

lemma lemma_2_10_29:
  "b r\<rightarrow> ((a r\<rightarrow> b) l\<rightarrow> a) = b r\<rightarrow> a"
  by (rule pseudo_hoop_dual.lemma_2_10_28)

lemma lemma_2_10_30:
  "((b l\<rightarrow> a) r\<rightarrow> a) l\<rightarrow> a = b l\<rightarrow> a"
  apply (rule antisym)
  apply (simp_all add: lemma_2_10_26)
  apply (rule lemma_2_5_13_a) 
  by (rule lemma_2_10_24)

end

context pseudo_hoop_algebra begin

lemma lemma_2_10_31:
  "((b r\<rightarrow> a) l\<rightarrow> a) r\<rightarrow> a = b r\<rightarrow> a"
  by (rule pseudo_hoop_dual.lemma_2_10_30)


lemma lemma_2_10_32:
  "(((b l\<rightarrow> a) r\<rightarrow> a) l\<rightarrow> b) l\<rightarrow> (b l\<rightarrow> a) = b l\<rightarrow> a"
  proof -
    have "((((b l\<rightarrow> a) r\<rightarrow> a) l\<rightarrow> b) l\<rightarrow> (b l\<rightarrow> a) = (((b l\<rightarrow> a) r\<rightarrow> a) l\<rightarrow> b) l\<rightarrow> (((b l\<rightarrow> a) r\<rightarrow> a) l\<rightarrow> a))"
      by (simp add: lemma_2_10_30)
    also have "\<dots> = ((((b l\<rightarrow> a) r\<rightarrow> a) l\<rightarrow> b) * ((b l\<rightarrow> a) r\<rightarrow> a) l\<rightarrow> a)"
      by (simp add: left_impl_ded)
    also have "\<dots> = (((b l\<rightarrow> a) r\<rightarrow> a) \<sqinter> b) l\<rightarrow> a"
      by (simp add: inf_l_def)
    also have "\<dots> = b l\<rightarrow> a" apply (subgoal_tac "((b l\<rightarrow> a) r\<rightarrow> a) \<sqinter> b = b", simp, rule antisym) 
      by (simp_all add: lemma_2_10_24)
    finally show ?thesis .
  qed

end

context pseudo_hoop_algebra begin

lemma lemma_2_10_33:
  "(((b r\<rightarrow> a) l\<rightarrow> a) r\<rightarrow> b) r\<rightarrow> (b r\<rightarrow> a) = b r\<rightarrow> a"
  by (rule pseudo_hoop_dual.lemma_2_10_32)
end


class pseudo_hoop_sup_algebra = pseudo_hoop_algebra + sup +
  assumes
    sup_comute: "a \<squnion> b = b \<squnion> a"
    and sup_le [simp]: "a \<le> a \<squnion> b"
    and le_sup_equiv: "(a \<le> b) = (a \<squnion> b = b)"
begin
  lemma sup_le_2 [simp]:
    "b \<le> a \<squnion> b"
    by (subst sup_comute, simp)

  lemma le_sup_equiv_r:
    "(a \<squnion> b = b) = (a \<le> b)"
    by (simp add: le_sup_equiv)

  lemma sup_idemp [simp]: 
    "a \<squnion> a = a"
    by (simp add: le_sup_equiv_r)
end

class pseudo_hoop_sup1_algebra = pseudo_hoop_algebra + sup +
  assumes
  sup_def: "a \<squnion> b = ((a l\<rightarrow> b) r\<rightarrow> b) \<sqinter> ((b l\<rightarrow> a) r\<rightarrow> a)"
begin

lemma sup_comute1: "a \<squnion> b = b \<squnion> a"
  apply (simp add: sup_def)
  apply (rule antisym)
  by simp_all

lemma sup_le1 [simp]: "a \<le> a \<squnion> b"
  by (simp add: sup_def lemma_2_10_24 lemma_2_5_9_b)

lemma le_sup_equiv1: "(a \<le> b) = (a \<squnion> b = b)"
  apply safe
  apply (simp add: left_lesseq)
  apply (rule antisym)
  apply (simp add: sup_def)
  apply (simp add: sup_def)
  apply (simp_all add: lemma_2_10_24)
  apply (simp add:  le_iff_inf)
  apply (subgoal_tac "(a \<sqinter> b = a \<sqinter> (a \<squnion> b)) \<and> (a \<sqinter> (a \<squnion> b) = a)")
  apply simp
  apply safe
  apply simp
  apply (rule antisym)
  apply simp
  apply (drule drop_assumption)
  by (simp add: sup_comute1)
  
subclass pseudo_hoop_sup_algebra
  apply unfold_locales
  apply (simp add: sup_comute1)
  apply simp
  by (simp add: le_sup_equiv1)
end


class pseudo_hoop_sup2_algebra = pseudo_hoop_algebra + sup +
  assumes
  sup_2_def: "a \<squnion> b = ((a r\<rightarrow> b) l\<rightarrow> b) \<sqinter> ((b r\<rightarrow> a) l\<rightarrow> a)"

context pseudo_hoop_sup1_algebra begin end

sublocale pseudo_hoop_sup2_algebra < sup1_dual: pseudo_hoop_sup1_algebra "(\<squnion>)" "\<lambda> a b . b * a" "(\<sqinter>)" "(r\<rightarrow>)" "(\<le>)" "(<)" 1 "(l\<rightarrow>)"
  apply unfold_locales
  by (simp add: sup_2_def)

context pseudo_hoop_sup2_algebra begin

lemma sup_comute_2: "a \<squnion> b = b \<squnion> a"
  by (rule  sup1_dual.sup_comute)

lemma sup_le2 [simp]: "a \<le> a \<squnion> b"
  by (rule sup1_dual.sup_le)

lemma le_sup_equiv2: "(a \<le> b) = (a \<squnion> b = b)"
  by (rule sup1_dual.le_sup_equiv)
  
subclass pseudo_hoop_sup_algebra
  apply unfold_locales
  apply (simp add: sup_comute_2)
  apply simp
  by (simp add: le_sup_equiv2)

end

class pseudo_hoop_lattice_a = pseudo_hoop_sup_algebra +
  assumes sup_inf_le_distr: "a \<squnion> (b \<sqinter> c) \<le> (a \<squnion> b) \<sqinter> (a \<squnion> c)"
begin
  lemma sup_lower_upper_bound [simp]:
    "a \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> a \<squnion> b \<le> c"
    apply (subst le_iff_inf)
    apply (subgoal_tac "(a \<squnion> b) \<sqinter> c = (a \<squnion> b) \<sqinter> (a \<squnion> c) \<and> a \<squnion> (b \<sqinter> c) \<le> (a \<squnion> b) \<sqinter> (a \<squnion> c) \<and> a \<squnion> (b \<sqinter> c) = a \<squnion> b")
    apply (rule antisym)
    apply simp
    apply safe
    apply auto[1]
    apply (simp add:  le_sup_equiv)
    apply (rule sup_inf_le_distr)
    by (simp add: le_iff_inf)
end

sublocale pseudo_hoop_lattice_a <  lattice "(\<sqinter>)" "(\<le>)" "(<)" "(\<squnion>)"
  by (unfold_locales, simp_all)

class pseudo_hoop_lattice_b = pseudo_hoop_sup_algebra +
  assumes le_sup_cong: "a \<le> b \<Longrightarrow> a \<squnion> c \<le> b \<squnion> c"

begin
  lemma sup_lower_upper_bound_b [simp]:
    "a \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> a \<squnion> b \<le> c"
    proof -
      assume A: "a \<le> c"
      assume B: "b \<le> c"
      have "a \<squnion> b \<le> c \<squnion> b" by (cut_tac A, simp add: le_sup_cong)
      also have "\<dots> = b \<squnion> c" by (simp add: sup_comute)
      also have "\<dots> \<le> c \<squnion> c" by (cut_tac B, rule le_sup_cong, simp)
      also have "\<dots> = c"  by simp
      finally show ?thesis .
    qed

  lemma  sup_inf_le_distr_b:
    "a \<squnion> (b \<sqinter> c) \<le> (a \<squnion> b) \<sqinter> (a \<squnion> c)"
    apply (rule sup_lower_upper_bound_b)
    apply simp
    apply simp
    apply safe
    apply (subst sup_comute)
    apply (rule_tac y = "b" in order_trans)
    apply simp_all
    apply (rule_tac y = "c" in order_trans)
    by simp_all
end

context pseudo_hoop_lattice_a begin end

sublocale pseudo_hoop_lattice_b <  pseudo_hoop_lattice_a "(\<squnion>)" "(*)" "(\<sqinter>)" "(l\<rightarrow>)" "(\<le>)" "(<)" 1 "(r\<rightarrow>)"
  by (unfold_locales, rule sup_inf_le_distr_b)

class pseudo_hoop_lattice = pseudo_hoop_sup_algebra +
  assumes sup_assoc_1: "a \<squnion> (b \<squnion> c) = (a \<squnion> b) \<squnion> c"
begin
  lemma le_sup_cong_c:
    "a \<le> b \<Longrightarrow> a \<squnion> c \<le> b \<squnion> c"
    proof -
      assume A: "a \<le> b"
      have "a \<squnion> c \<squnion> (b \<squnion> c) = a \<squnion> (c \<squnion> (b \<squnion> c))" by (simp add: sup_assoc_1)
      also have "\<dots> = a \<squnion> ((b \<squnion> c) \<squnion> c)" by (simp add: sup_comute)
      also have "\<dots> = a \<squnion> (b \<squnion> (c \<squnion> c))" by (simp add: sup_assoc_1 [THEN sym])
      also have "\<dots> = (a \<squnion> b) \<squnion> c" by (simp add: sup_assoc_1)
      also have "\<dots> = b \<squnion> c" by (cut_tac A, simp add: le_sup_equiv)
      finally show ?thesis by (simp add: le_sup_equiv)
    qed
end


sublocale pseudo_hoop_lattice <  pseudo_hoop_lattice_b "(\<squnion>)" "(*)" "(\<sqinter>)" "(l\<rightarrow>)" "(\<le>)" "(<)" 1 "(r\<rightarrow>)"
  by (unfold_locales, rule le_sup_cong_c)


sublocale pseudo_hoop_lattice <  semilattice_sup "(\<squnion>)" "(\<le>)" "(<)"
  by (unfold_locales, simp_all)

sublocale pseudo_hoop_lattice <  lattice "(\<sqinter>)" "(\<le>)" "(<)" "(\<squnion>)"
  by unfold_locales

lemma (in pseudo_hoop_lattice_a) supremum_pair [simp]:
  "supremum {a, b} = {a \<squnion> b}" 
  apply (simp add: supremum_def upper_bound_def)
  apply safe
  apply simp_all
  apply (rule antisym)
  by simp_all

sublocale pseudo_hoop_lattice <  distrib_lattice "(\<sqinter>)" "(\<le>)" "(<)" "(\<squnion>)"
  apply unfold_locales
  apply (rule distrib_imp1)
  apply (case_tac "xa \<sqinter> (ya \<squnion> za) \<in> supremum ((\<sqinter>) xa ` {ya, za})")
  apply (simp add: supremum_pair)
  apply (erule notE)
  apply (rule lemma_2_9_ii)
  by (simp add: supremum_pair)

class bounded_semilattice_inf_top = semilattice_inf + order_top
begin
lemma inf_eq_top_iff [simp]:
  "(inf x y = top) = (x = top \<and> y = top)"
  by (simp add: eq_iff)
end

sublocale pseudo_hoop_algebra < bounded_semilattice_inf_top "(\<sqinter>)" "(\<le>)" "(<)" "1"
  by unfold_locales simp

definition (in pseudo_hoop_algebra)
  sup1::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>1" 70) where 
  "a \<squnion>1 b = ((a l\<rightarrow> b) r\<rightarrow> b) \<sqinter> ((b l\<rightarrow> a) r\<rightarrow> a)"

sublocale pseudo_hoop_algebra < sup1: pseudo_hoop_sup1_algebra "(\<squnion>1)" "(*)" "(\<sqinter>)" "(l\<rightarrow>)" "(\<le>)" "(<)" 1 "(r\<rightarrow>)"
  apply unfold_locales 
  by (simp add: sup1_def)



definition (in pseudo_hoop_algebra)
  sup2::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>2" 70) where 
  "a \<squnion>2 b = ((a r\<rightarrow> b) l\<rightarrow> b) \<sqinter> ((b r\<rightarrow> a) l\<rightarrow> a)"

sublocale pseudo_hoop_algebra < sup2: pseudo_hoop_sup2_algebra "(\<squnion>2)" "(*)" "(\<sqinter>)" "(l\<rightarrow>)" "(\<le>)" "(<)" 1 "(r\<rightarrow>)"
  apply unfold_locales 
  by (simp add: sup2_def)

context pseudo_hoop_algebra
begin
  lemma lemma_2_15_i:
    "1 \<in> supremum {a, b} \<Longrightarrow> a * b = a \<sqinter> b"
    apply (rule antisym)
    apply (rule lemma_2_5_11)
    apply (simp add: inf_l_def)
    apply (subst left_impl_times)
    apply (rule mult_right_mono)
    apply (subst right_lesseq)
    apply (subgoal_tac "a \<squnion>1 b = 1")
    apply (simp add: sup1_def)
    apply (rule antisym)
    apply simp
    by (simp add: supremum_def upper_bound_def)

    
  lemma lemma_2_15_ii:
    "1 \<in> supremum {a, b} \<Longrightarrow> a \<le> c \<Longrightarrow> b \<le> d \<Longrightarrow> 1 \<in> supremum {c, d}"
    apply (simp add: supremum_def upper_bound_def)
    apply safe
    apply (drule_tac x = x in spec)
    apply safe
    by simp_all

lemma sup_union:
  "a \<in> supremum A \<Longrightarrow> b \<in> supremum B \<Longrightarrow> supremum {a, b} = supremum (A \<union> B)"
  apply safe
  apply (simp_all add: supremum_def upper_bound_def)
  apply safe
  apply auto
  apply (subgoal_tac "(\<forall>x \<in> A \<union> B. x \<le> xa)")
  by auto

lemma sup_singleton [simp]: "a \<in> supremum {a}"
  by (simp add: supremum_def upper_bound_def)
 

lemma sup_union_singleton: "a \<in> supremum X \<Longrightarrow> supremum {a, b} = supremum (X \<union> {b})"
  apply (rule_tac B = "{b}" in  sup_union)
  by simp_all

lemma sup_le_union [simp]: "a \<le> b \<Longrightarrow> supremum (A \<union> {a, b}) = supremum (A \<union> {b})"
  apply (simp add: supremum_def upper_bound_def)
  by auto

lemma sup_sup_union: "a \<in> supremum A \<Longrightarrow> b \<in> supremum (B \<union> {a}) \<Longrightarrow> b \<in> supremum (A \<union> B)"
  apply (simp add: supremum_def upper_bound_def)
  by auto
  
end

(*
context monoid_mult
begin
lemma "a ^ 2 = a * a"
  by (simp add: power2_eq_square)
end
*)

lemma [simp]:
  "n \<le> 2 ^ n"
  apply (induct_tac n)
  apply auto
  apply (rule_tac y = "1 + 2 ^ n" in order_trans)
  by auto


context pseudo_hoop_algebra
begin

lemma sup_le_union_2:
  "a \<le> b \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> supremum A = supremum ((A - {a}) \<union> {b})"
  apply (case_tac "supremum ((A - {a , b}) \<union> {a, b}) = supremum ((A - {a, b}) \<union> {b})")
  apply (case_tac "((A - {a, b}) \<union> {a, b} = A) \<and> ((A - {a, b}) \<union> {b} = (A - {a}) \<union> {b})")
  apply safe[1] 
  apply simp
  apply simp
  apply (erule notE)
  apply safe [1]
  apply (erule notE)
  apply (rule sup_le_union)
  by simp


  lemma lemma_2_15_iii_0:
    "1 \<in> supremum {a, b} \<Longrightarrow> 1 \<in> supremum {a ^ 2, b ^ 2}"
    apply (frule_tac a = a in lemma_2_9_i)
    apply simp
    apply (frule_tac a = a and b = b in sup_union_singleton)
    apply (subgoal_tac "supremum ({a * a, a * b} \<union> {b}) = supremum ({a * a, b})")
    apply simp_all
    apply (frule_tac a = b in lemma_2_9_i)
    apply simp
    apply (drule_tac a = b and A = "{b * (a * a), b * b}" and b = 1 and B = "{a * a}" in sup_sup_union)
    apply simp
    apply (case_tac "{a * a, b} = {b, a * a}")
    apply simp
    apply auto [1]
    apply simp
    apply (subgoal_tac "supremum {a * a, b * (a * a), b * b} = supremum {a * a, b * b}")
    apply(simp add: power2_eq_square)
    apply (case_tac "b * (a * a) = b * b")
    apply auto[1]
    apply (cut_tac  A = "{a * a, b * (a * a), b * b}" and a = "b * (a * a)" and b = "a * a" in  sup_le_union_2)
    apply simp
    apply simp
    apply simp
    apply (subgoal_tac "({a * a, b * (a * a), b * b} - {b * (a * a)} \<union> {a * a}) = {a * a, b * b}")
    apply simp
    apply auto[1]
    apply (case_tac "a * a = a * b")
    apply (subgoal_tac "{b, a * a, a * b} = {a * a, b}")
    apply simp
    apply auto[1]
    apply (cut_tac  A = "{b, a * a, a * b}" and a = "a * b" and b = "b" in  sup_le_union_2)
    apply simp
    apply simp
    apply simp
    apply (subgoal_tac "{b, a * a, a * b} - {a * b} \<union> {b} = {a * a, b}")
    apply simp
    by auto
   

lemma [simp]: "m \<le> n \<Longrightarrow> a ^ n \<le> a ^ m"
  apply (subgoal_tac "a ^ n = (a ^ m) * (a ^ (n-m))")
  apply simp
  apply (cut_tac a = a and m = "m" and n = "n - m" in power_add)
  by simp

lemma [simp]: "a ^ (2 ^ n) \<le> a ^ n"
  by simp

lemma lemma_2_15_iii_1: "1 \<in> supremum {a, b} \<Longrightarrow> 1 \<in> supremum {a ^ (2 ^ n), b ^ (2 ^ n)}"
  apply (induct_tac n)
  apply auto[1]
  apply (drule drop_assumption)
  apply (drule lemma_2_15_iii_0)
  apply (subgoal_tac "\<forall>a . (a ^ (2::nat) ^ n)\<^sup>2 = a ^ (2::nat) ^ Suc n")
  apply simp
  apply safe
  apply (cut_tac a = aa and m = "2 ^ n" and n = 2 in  power_mult)
  apply auto
  apply (subgoal_tac "((2::nat) ^ n * (2::nat)) = ((2::nat) * (2::nat) ^ n)")
  by simp_all


  lemma lemma_2_15_iii:
    "1 \<in> supremum {a, b} \<Longrightarrow> 1 \<in> supremum {a ^ n, b ^ n}"
    apply (drule_tac n = n in lemma_2_15_iii_1)
    apply (simp add: supremum_def upper_bound_def)
    apply safe
    apply (drule_tac x = x in spec)
    apply safe
    apply (rule_tac y = "a ^ n" in order_trans)
    apply simp_all
    apply (rule_tac y = "b ^ n" in order_trans)
    by simp_all
end

end


