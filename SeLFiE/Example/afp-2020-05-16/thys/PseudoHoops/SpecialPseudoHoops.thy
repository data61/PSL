section\<open>Some Classes of Pseudo-Hoops\<close>

theory SpecialPseudoHoops
imports PseudoHoopFilters PseudoWaisbergAlgebra
begin

class cancel_pseudo_hoop_algebra = pseudo_hoop_algebra + 
  assumes mult_cancel_left: "a * b = a * c \<Longrightarrow> b = c"
  and mult_cancel_right: "b * a = c * a \<Longrightarrow> b = c"
begin
lemma cancel_left_a: "b l\<rightarrow> (a * b) = a"
  apply (rule_tac a = b in mult_cancel_right)
  apply (subst inf_l_def [THEN sym])
  apply (rule antisym)
  by simp_all

lemma cancel_right_a: "b r\<rightarrow> (b * a) = a"
  apply (rule_tac a = b in mult_cancel_left)
  apply (subst inf_r_def [THEN sym])
  apply (rule antisym)
  by simp_all

end

class cancel_pseudo_hoop_algebra_2 = pseudo_hoop_algebra + 
  assumes cancel_left: "b l\<rightarrow> (a * b) = a"
  and cancel_right: "b r\<rightarrow> (b * a) = a"

begin
subclass cancel_pseudo_hoop_algebra
  apply unfold_locales
  apply (subgoal_tac "b = a r\<rightarrow> (a * b) \<and> a r\<rightarrow> (a * b) = a r\<rightarrow> (a * c) \<and> a r\<rightarrow> (a * c) = c")
  apply simp
  apply (rule conjI)
  apply (subst cancel_right)
  apply simp
  apply (rule conjI)
  apply simp
  apply (subst cancel_right)
  apply simp
  apply (subgoal_tac "b = a l\<rightarrow> (b * a) \<and> a l\<rightarrow> (b * a) = a l\<rightarrow> (c * a) \<and> a l\<rightarrow> (c * a) = c")
  apply simp
  apply (rule conjI)
  apply (subst cancel_left)
  apply simp
  apply (rule conjI)
  apply simp
  apply (subst cancel_left)
  by simp
  
end

context cancel_pseudo_hoop_algebra
begin

lemma lemma_4_2_i: "a l\<rightarrow> b = (a * c) l\<rightarrow> (b * c)"
  apply (subgoal_tac "a l\<rightarrow> b = a l\<rightarrow> (c l\<rightarrow> (b * c)) \<and> a l\<rightarrow> (c l\<rightarrow> (b * c)) = (a * c) l\<rightarrow> (b * c)")
  apply simp
  apply (rule conjI)
  apply (simp add: cancel_left_a)
  by (simp add: left_impl_ded)

lemma lemma_4_2_ii: "a r\<rightarrow> b = (c * a) r\<rightarrow> (c * b)"
  apply (subgoal_tac "a r\<rightarrow> b = a r\<rightarrow> (c r\<rightarrow> (c * b)) \<and> a r\<rightarrow> (c r\<rightarrow> (c * b)) = (c * a) r\<rightarrow> (c * b)")
  apply simp
  apply (rule conjI)
  apply (simp add: cancel_right_a)
  by (simp add: right_impl_ded)

lemma lemma_4_2_iii: "(a * c \<le> b * c) = (a \<le> b)"
  by (simp add: left_lesseq lemma_4_2_i [THEN sym])

lemma lemma_4_2_iv: "(c * a \<le> c * b) = (a \<le> b)"
  by (simp add: right_lesseq lemma_4_2_ii [THEN sym])

end

class wajsberg_pseudo_hoop_algebra = pseudo_hoop_algebra +
  assumes wajsberg1: "(a l\<rightarrow> b) r\<rightarrow> b = (b l\<rightarrow> a) r\<rightarrow> a"
  and wajsberg2: "(a r\<rightarrow> b) l\<rightarrow> b = (b r\<rightarrow> a) l\<rightarrow> a"



context wajsberg_pseudo_hoop_algebra
begin

lemma lemma_4_3_i_a: "a \<squnion>1 b = (a l\<rightarrow> b) r\<rightarrow> b"
  by (simp add: sup1_def wajsberg1)

lemma lemma_4_3_i_b: "a \<squnion>1 b = (b l\<rightarrow> a) r\<rightarrow> a"
  by (simp add: sup1_def wajsberg1)

lemma lemma_4_3_ii_a: "a \<squnion>2 b = (a r\<rightarrow> b) l\<rightarrow> b"
  by (simp add: sup2_def wajsberg2)

lemma lemma_4_3_ii_b: "a \<squnion>2 b = (b r\<rightarrow> a) l\<rightarrow> a"
  by (simp add: sup2_def wajsberg2)
end


sublocale wajsberg_pseudo_hoop_algebra < lattice1:pseudo_hoop_lattice_b "(\<squnion>1)" "(*)" "(\<sqinter>)" "(l\<rightarrow>)" "(\<le>)" "(<)" 1 "(r\<rightarrow>)"
  apply unfold_locales
  apply (simp add: lemma_4_3_i_a)
  by (simp add: lemma_2_5_13_b lemma_2_5_13_a)

class zero_one = zero + one


class bounded_wajsberg_pseudo_hoop_algebra = zero_one + wajsberg_pseudo_hoop_algebra +
  assumes zero_smallest [simp]: "0 \<le> a"
begin 
end


sublocale wajsberg_pseudo_hoop_algebra < lattice2:pseudo_hoop_lattice_b "(\<squnion>2)" "(*)" "(\<sqinter>)" "(l\<rightarrow>)" "(\<le>)" "(<)" 1 "(r\<rightarrow>)"
  apply unfold_locales
  apply (simp add: lemma_4_3_ii_a)
  by (simp add: lemma_2_5_13_b lemma_2_5_13_a)

lemma (in wajsberg_pseudo_hoop_algebra) sup1_eq_sup2: "(\<squnion>1) = (\<squnion>2)"
  apply (simp add: fun_eq_iff)
  apply safe
  apply (cut_tac a = x and b = xa in lattice1.supremum_pair)
  apply (cut_tac a = x and b = xa in lattice2.supremum_pair)
  by blast

context bounded_wajsberg_pseudo_hoop_algebra
begin
definition
  "negl a = a l\<rightarrow> 0"
  
definition
  "negr a = a r\<rightarrow> 0"

lemma [simp]: "0 l\<rightarrow> a = 1"
  by (simp add: order [THEN sym])
  
lemma [simp]: "0 r\<rightarrow> a = 1"
  by (simp add: order_r [THEN sym])
end

sublocale bounded_wajsberg_pseudo_hoop_algebra < wajsberg: pseudo_wajsberg_algebra "1"  "(l\<rightarrow>)"  "(r\<rightarrow>)"  "(\<le>)" "(<)" "0" "negl" "negr"
  apply unfold_locales
  apply simp_all
  apply (simp add:  lemma_4_3_i_a [THEN sym])
  apply (rule antisym)
  apply simp_all
  apply (simp add:  lemma_4_3_i_a [THEN sym] lemma_4_3_ii_a [THEN sym])
  apply (rule antisym)
  apply simp_all
  apply (simp add:  lemma_4_3_i_a [THEN sym] lemma_4_3_ii_a [THEN sym])
  apply (rule antisym)
  apply simp_all
  apply (subst left_lesseq [THEN sym])
  apply (simp add: lemma_2_5_16)
  apply (subst right_lesseq [THEN sym])
  apply (simp add: lemma_2_5_17)
  apply (simp add: left_lesseq)
  apply (simp add: less_def)
  apply (simp_all add: negl_def negr_def) 
  apply (subst left_lesseq [THEN sym])
  apply (subgoal_tac "b l\<rightarrow> a = ((b l\<rightarrow> 0) r\<rightarrow> 0) l\<rightarrow> ((a l\<rightarrow> 0) r\<rightarrow> 0)")
  apply (simp add: lemma_2_5_17)
  apply (subst wajsberg1)
  apply simp
  apply (subst wajsberg1)
  apply simp
  apply (subst left_lesseq [THEN sym])
  apply (subgoal_tac "b r\<rightarrow> a = ((b r\<rightarrow> 0) l\<rightarrow> 0) r\<rightarrow> ((a r\<rightarrow> 0) l\<rightarrow> 0)")
  apply (simp add: lemma_2_5_16)
  apply (subst wajsberg2)
  apply simp
  apply (subst wajsberg2)
  apply simp
  apply (simp add: left_impl_ded [THEN sym])
  apply (simp add: right_impl_ded [THEN sym])
  apply (simp add:  lemma_4_3_i_a [THEN sym] lemma_4_3_ii_a [THEN sym])
  apply (rule antisym)
  by simp_all


context pseudo_wajsberg_algebra
begin
  lemma "class.bounded_wajsberg_pseudo_hoop_algebra mult inf_a (l\<rightarrow>) (\<le>) (<) 1 (r\<rightarrow>) (0::'a)"
  apply unfold_locales
  apply (simp add: inf_a_def mult_def W6)
  apply (simp add: strict)
  apply (simp_all add: mult_def order_l strict) 
  apply (simp add: zero_def [THEN sym] C3_a)
  apply (simp add: W6 inf_a_def [THEN sym])
  apply (rule antisym)
  apply simp_all
  apply (simp add: C6 P9 [THEN sym] C5_b)
  apply (simp add: inf_b_def [THEN sym])
  apply (rule antisym)
  apply simp_all
  apply (simp add: inf_b_def [THEN sym])
  apply (rule antisym)
  apply simp_all
  apply (simp add: W6)
  apply (simp add: C6 [THEN sym])
  apply (simp add: P9 C5_a)
  apply (simp add: inf_b_def [THEN sym])
  apply (simp add: W6 inf_a_def [THEN sym])
  apply (rule antisym)
  apply simp_all
  apply (simp add: W2a)
  by (simp add: W2c)

end

class basic_pseudo_hoop_algebra = pseudo_hoop_algebra +
  assumes B1: "(a l\<rightarrow> b) l\<rightarrow> c \<le> ((b l\<rightarrow> a) l\<rightarrow> c) l\<rightarrow> c"
  and B2: "(a r\<rightarrow> b) r\<rightarrow> c \<le> ((b r\<rightarrow> a) r\<rightarrow> c) r\<rightarrow> c"
begin
lemma lemma_4_5_i: "(a l\<rightarrow> b) \<squnion>1 (b l\<rightarrow> a) = 1"
  apply (cut_tac a = a and b = b and c = "(a l\<rightarrow> b) \<squnion>1 (b l\<rightarrow> a)" in B1)
  apply (subgoal_tac "(a l\<rightarrow> b) l\<rightarrow> (a l\<rightarrow> b) \<squnion>1 (b l\<rightarrow> a) = 1 \<and> ((b l\<rightarrow> a) l\<rightarrow> (a l\<rightarrow> b) \<squnion>1 (b l\<rightarrow> a)) = 1")
  apply (erule conjE)
  apply simp
  apply (rule antisym)
  apply simp
  apply simp
  apply safe
  apply (subst left_lesseq [THEN sym])
  apply simp
  apply (subst left_lesseq [THEN sym])
  by simp


lemma lemma_4_5_ii: "(a r\<rightarrow> b) \<squnion>2 (b r\<rightarrow> a) = 1"
  apply (cut_tac a = a and b = b and c = "(a r\<rightarrow> b) \<squnion>2 (b r\<rightarrow> a)" in B2)
  apply (subgoal_tac "(a r\<rightarrow> b) r\<rightarrow> (a r\<rightarrow> b) \<squnion>2 (b r\<rightarrow> a) = 1 \<and> ((b r\<rightarrow> a) r\<rightarrow> (a r\<rightarrow> b) \<squnion>2 (b r\<rightarrow> a)) = 1")
  apply (erule conjE)
  apply simp
  apply (rule antisym)
  apply simp
  apply simp
  apply safe
  apply (subst right_lesseq [THEN sym])
  apply simp
  apply (subst right_lesseq [THEN sym])
  by simp

lemma lemma_4_5_iii: "a l\<rightarrow> b = (a \<squnion>1 b) l\<rightarrow> b"
  apply (rule antisym)
  apply (rule_tac y = "((a l\<rightarrow> b) r\<rightarrow> b) l\<rightarrow> b" in order_trans)
  apply (rule lemma_2_10_26)
  apply (rule lemma_2_5_13_a)
  apply (simp add: sup1_def)
  apply (rule lemma_2_5_13_a)
  by simp


lemma lemma_4_5_iv: "a r\<rightarrow> b = (a \<squnion>2 b) r\<rightarrow> b"
  apply (rule antisym)
  apply (rule_tac y = "((a r\<rightarrow> b) l\<rightarrow> b) r\<rightarrow> b" in order_trans)
  apply (rule lemma_2_10_24)
  apply (rule lemma_2_5_13_b)
  apply (simp add: sup2_def)
  apply (rule lemma_2_5_13_b)
  by simp

lemma lemma_4_5_v: "(a \<squnion>1 b) l\<rightarrow> c = (a l\<rightarrow> c) \<sqinter> (b l\<rightarrow> c)"
  apply (rule antisym)
  apply simp
  apply safe
  apply (rule lemma_2_5_13_a)
  apply simp
  apply (rule lemma_2_5_13_a)
  apply simp
  apply (subst right_lesseq)
  apply (rule antisym)
  apply simp
  apply (rule_tac y = "(a l\<rightarrow> b) l\<rightarrow> ((a l\<rightarrow> c) \<sqinter> (b l\<rightarrow> c) r\<rightarrow> a \<squnion>1 b l\<rightarrow> c)" in order_trans)
  apply (subst left_residual [THEN sym])
  apply simp
  apply (subst lemma_4_5_iii)
  apply (subst right_residual [THEN sym])
  apply (subst left_residual [THEN sym])
  apply (rule_tac y = "b \<sqinter> c" in order_trans)
  apply (subst (2) inf_l_def)
  apply (rule_tac y = "((a l\<rightarrow> c) \<sqinter> (b l\<rightarrow> c)) * ((a \<squnion>1 b) \<sqinter> b)" in order_trans)
  apply (subst (3) inf_l_def)
  apply (simp add: mult.assoc)
  apply (subgoal_tac "(a \<squnion>1 b \<sqinter> b) = b")
  apply simp
  apply (rule antisym, simp)
  apply simp
  apply simp
  apply (rule_tac y = "((b l\<rightarrow> a) l\<rightarrow> ((a l\<rightarrow> c) \<sqinter> (b l\<rightarrow> c) r\<rightarrow> a \<squnion>1 b l\<rightarrow> c)) l\<rightarrow> ((a l\<rightarrow> c) \<sqinter> (b l\<rightarrow> c) r\<rightarrow> a \<squnion>1 b l\<rightarrow> c)" in order_trans)
  apply (rule B1)
  apply (subgoal_tac "(b l\<rightarrow> a) l\<rightarrow> ((a l\<rightarrow> c) \<sqinter> (b l\<rightarrow> c) r\<rightarrow> a \<squnion>1 b l\<rightarrow> c) = 1")
  apply simp
  apply (rule antisym)
  apply simp
  apply (subst left_residual [THEN sym])
  apply simp
  apply (subst lemma_4_5_iii)
  apply (subst right_residual [THEN sym])
  apply (subst left_residual [THEN sym])
  apply (rule_tac y = "a \<sqinter> c" in order_trans)
  apply (subst (2) inf_l_def)
  apply (rule_tac y = "((a l\<rightarrow> c) \<sqinter> (b l\<rightarrow> c)) * ((a \<squnion>1 b) \<sqinter> a)" in order_trans)
  apply (subst (3) inf_l_def)
  apply (subst sup1.sup_comute1)
  apply (simp add: mult.assoc)
  apply (subgoal_tac "(a \<squnion>1 b \<sqinter> a) = a")
  apply simp
  apply (rule antisym, simp)
  apply simp
  by simp


lemma lemma_4_5_vi: "(a \<squnion>2 b) r\<rightarrow> c = (a r\<rightarrow> c) \<sqinter> (b r\<rightarrow> c)"
  apply (rule antisym)
  apply simp
  apply safe
  apply (rule lemma_2_5_13_b)
  apply simp
  apply (rule lemma_2_5_13_b)
  apply simp
  apply (subst left_lesseq)
  apply (rule antisym)
  apply simp
  apply (rule_tac y = "(a r\<rightarrow> b) r\<rightarrow> ((a r\<rightarrow> c) \<sqinter> (b r\<rightarrow> c) l\<rightarrow> a \<squnion>2 b r\<rightarrow> c)" in order_trans)
  apply (subst right_residual [THEN sym])
  apply simp
  apply (subst lemma_4_5_iv)
  apply (subst left_residual [THEN sym])
  apply (subst right_residual [THEN sym])
  apply (rule_tac y = "b \<sqinter> c" in order_trans)
  apply (subst (2) inf_r_def)
  apply (rule_tac y = "((a \<squnion>2 b) \<sqinter> b) * ((a r\<rightarrow> c) \<sqinter> (b r\<rightarrow> c))" in order_trans)
  apply (subst (2) inf_r_def)
  apply (simp add: mult.assoc)
  apply (subgoal_tac "(a \<squnion>2 b \<sqinter> b) = b")
  apply simp
  apply (rule antisym, simp)
  apply simp
  apply simp
  apply (rule_tac y = "((b r\<rightarrow> a) r\<rightarrow> ((a r\<rightarrow> c) \<sqinter> (b r\<rightarrow> c) l\<rightarrow> a \<squnion>2 b r\<rightarrow> c)) r\<rightarrow> ((a r\<rightarrow> c) \<sqinter> (b r\<rightarrow> c) l\<rightarrow> a \<squnion>2 b r\<rightarrow> c)" in order_trans)
  apply (rule B2)
  apply (subgoal_tac "(b r\<rightarrow> a) r\<rightarrow> ((a r\<rightarrow> c) \<sqinter> (b r\<rightarrow> c) l\<rightarrow> a \<squnion>2 b r\<rightarrow> c) = 1")
  apply simp
  apply (rule antisym)
  apply simp
  apply (subst right_residual [THEN sym])
  apply simp
  apply (subst lemma_4_5_iv)
  apply (subst left_residual [THEN sym])
  apply (subst right_residual [THEN sym])
  apply (rule_tac y = "a \<sqinter> c" in order_trans)
  apply (subst (2) inf_r_def)
  apply (rule_tac y = "((a \<squnion>2 b) \<sqinter> a) * ((a r\<rightarrow> c) \<sqinter> (b r\<rightarrow> c))" in order_trans)
  apply (subst (2) inf_r_def)
  apply (subst (2) sup2.sup_comute)
  apply (simp add: mult.assoc)
  apply (subgoal_tac "(a \<squnion>2 b \<sqinter> a) = a")
  apply simp
  apply (rule antisym, simp)
  apply simp
  by simp

lemma lemma_4_5_a: "a \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> a \<squnion>1 b \<le> c"
  apply (subst left_lesseq)
  apply (subst lemma_4_5_v)
  by simp

lemma lemma_4_5_b: "a \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> a \<squnion>2 b \<le> c"
  apply (subst right_lesseq)
  apply (subst lemma_4_5_vi)
  by simp

lemma lemma_4_5: "a \<squnion>1 b = a \<squnion>2 b"
  apply (rule antisym)
  by (simp_all add: lemma_4_5_a lemma_4_5_b)
end

sublocale basic_pseudo_hoop_algebra <  basic_lattice:lattice "(\<sqinter>)" "(\<le>)" "(<)" "(\<squnion>1)"
  apply unfold_locales
  by (simp_all add: lemma_4_5_a)

context pseudo_hoop_lattice begin end

sublocale basic_pseudo_hoop_algebra <  pseudo_hoop_lattice "(\<squnion>1)" "(*)" "(\<sqinter>)" "(l\<rightarrow>)" "(\<le>)" "(<)" 1 "(r\<rightarrow>)"
  apply unfold_locales
  by (simp_all add: basic_lattice.sup_assoc)

class sup_assoc_pseudo_hoop_algebra = pseudo_hoop_algebra +
  assumes sup1_assoc: "a \<squnion>1 (b \<squnion>1 c) = (a \<squnion>1 b) \<squnion>1 c"
  and sup2_assoc: "a \<squnion>2 (b \<squnion>2 c) = (a \<squnion>2 b) \<squnion>2 c"

sublocale sup_assoc_pseudo_hoop_algebra <  sup1_lattice: pseudo_hoop_lattice "(\<squnion>1)" "(*)" "(\<sqinter>)" "(l\<rightarrow>)" "(\<le>)" "(<)" 1 "(r\<rightarrow>)"
  apply unfold_locales
  by (simp add: sup1_assoc)

sublocale sup_assoc_pseudo_hoop_algebra <  sup2_lattice: pseudo_hoop_lattice "(\<squnion>2)" "(*)" "(\<sqinter>)" "(l\<rightarrow>)" "(\<le>)" "(<)" 1 "(r\<rightarrow>)"
  apply unfold_locales
  by (simp add: sup2_assoc)


class sup_assoc_pseudo_hoop_algebra_1 = sup_assoc_pseudo_hoop_algebra +
  assumes union_impl: "(a l\<rightarrow> b) \<squnion>1 (b l\<rightarrow> a) = 1"
  and union_impr: "(a r\<rightarrow> b) \<squnion>1 (b r\<rightarrow> a) = 1"

lemma (in pseudo_hoop_algebra) [simp]: "infimum {a, b} = {a \<sqinter> b}"
  apply (simp add: infimum_def lower_bound_def)
  apply safe
  apply (rule antisym)
  by simp_all

lemma (in pseudo_hoop_lattice) sup_impl_inf:
  "(a \<squnion> b) l\<rightarrow> c = (a l\<rightarrow> c) \<sqinter> (b l\<rightarrow>c)" 
  apply (cut_tac A = "{a, b}" and a = "a \<squnion> b" and b = c in lemma_2_8_i)
  by simp_all

lemma (in pseudo_hoop_lattice) sup_impr_inf:
  "(a \<squnion> b) r\<rightarrow> c = (a r\<rightarrow> c) \<sqinter> (b r\<rightarrow>c)" 
  apply (cut_tac A = "{a, b}" and a = "a \<squnion> b" and b = c in lemma_2_8_i1)
  by simp_all

lemma (in pseudo_hoop_lattice) sup_times:
  "a * (b \<squnion> c) = (a * b) \<squnion> (a * c)" 
  apply (cut_tac A = "{b, c}" and b = "b \<squnion> c" and a = a in lemma_2_9_i)
  by simp_all

lemma (in pseudo_hoop_lattice) sup_times_right:
  "(b \<squnion> c) * a = (b * a) \<squnion> (c * a)" 
  apply (cut_tac A = "{b, c}" and b = "b \<squnion> c" and a = a in lemma_2_9_i1)
  by simp_all

context basic_pseudo_hoop_algebra begin end

sublocale sup_assoc_pseudo_hoop_algebra_1 <  basic_1: basic_pseudo_hoop_algebra  "(*)" "(\<sqinter>)" "(l\<rightarrow>)" "(\<le>)" "(<)" 1 "(r\<rightarrow>)" 
  apply unfold_locales
  apply (subst left_residual [THEN sym])
  apply (rule_tac y = "(a l\<rightarrow> b) \<squnion>1 (b l\<rightarrow> a) l\<rightarrow> c" in order_trans)
  apply (subst sup1_lattice.sup_impl_inf)
  apply (simp add: lemma_2_5_11)
  apply (simp add: union_impl)
   apply (subst right_residual [THEN sym])
  apply (rule_tac y = "(b r\<rightarrow> a) \<squnion>1 (a r\<rightarrow> b) r\<rightarrow> c" in order_trans)
  apply (subst sup1_lattice.sup_impr_inf)
  apply (simp add: lemma_2_5_11)
  by (simp add: union_impr)

context basic_pseudo_hoop_algebra
begin

lemma lemma_4_8_i: "a * (b \<sqinter> c) = (a * b) \<sqinter> (a * c)"
  apply (rule antisym)
  apply simp
  apply (subgoal_tac "a * (b \<sqinter> c) = (a * (b * (b r\<rightarrow> c))) \<squnion>1 (a * (c * (c r\<rightarrow> b)))")
  apply simp
  apply (drule drop_assumption)
  apply (rule_tac y = "(((a * b) \<sqinter> (a * c)) * (b r\<rightarrow> c)) \<squnion>1 (((a * b) \<sqinter> (a * c)) * (c r\<rightarrow> b))" in order_trans)
  apply (subst sup_times [THEN sym])
  apply (simp add: lemma_4_5 lemma_4_5_ii)
  apply (simp add: mult.assoc [THEN sym])  
  apply safe
  apply (rule_tac y = "a * b * (b r\<rightarrow> c)" in order_trans)
  apply simp
  apply simp
  apply (rule_tac y = "a * c * (c r\<rightarrow> b)" in order_trans)
  apply simp
  apply simp
  apply (simp add: inf_r_def [THEN sym])
  apply (subgoal_tac "b \<sqinter> c = c \<sqinter> b")
  apply simp
  apply (rule antisym)
  by simp_all


lemma lemma_4_8_ii: "(b \<sqinter> c) * a = (b * a) \<sqinter> (c * a)"
  apply (rule antisym)
  apply simp
  apply (subgoal_tac "(b \<sqinter> c) * a = (((b l\<rightarrow> c) * b) * a) \<squnion>1 (((c l\<rightarrow> b) * c) * a)")
  apply simp
  apply (drule drop_assumption)
  apply (rule_tac y = "((b l\<rightarrow> c) * ((b * a) \<sqinter> (c * a))) \<squnion>1 ((c l\<rightarrow> b) * ((b * a) \<sqinter> (c * a)))" in order_trans)
  apply (subst sup_times_right [THEN sym])
  apply (simp add: lemma_4_5_i)
  apply (simp add: mult.assoc)  
  apply safe
  apply (rule_tac y = "(b l\<rightarrow> c) * (b * a)" in order_trans)
  apply simp_all
  apply (rule_tac y = "(c l\<rightarrow> b) * (c * a)" in order_trans)
  apply simp_all
  apply (simp add: inf_l_def [THEN sym])
  apply (subgoal_tac "b \<sqinter> c = c \<sqinter> b")
  apply simp
  apply (rule antisym)
  by simp_all

lemma lemma_4_8_iii: "(a l\<rightarrow> b) l\<rightarrow> (b l\<rightarrow> a) = b l\<rightarrow> a"
  apply (rule antisym)
  apply (cut_tac a = a and b = b in lemma_4_5_i)
  apply (unfold sup1_def right_lesseq, simp)
  by (simp add: lemma_2_5_9_a)

 lemma lemma_4_8_iv: "(a r\<rightarrow> b) r\<rightarrow> (b r\<rightarrow> a) = b r\<rightarrow> a"
  apply (rule antisym)
  apply (cut_tac a = a and b = b in lemma_4_5_ii)
  apply (unfold sup2_def left_lesseq, simp)
  by (simp add: lemma_2_5_9_b)

end

context wajsberg_pseudo_hoop_algebra
begin
subclass sup_assoc_pseudo_hoop_algebra_1
  apply unfold_locales
  apply (simp add: lattice1.sup_assoc)
  apply (simp add: lattice2.sup_assoc)
  apply (simp add: lemma_4_3_i_a)
  apply (subgoal_tac "(a l\<rightarrow> b) l\<rightarrow> (b l\<rightarrow> a) = b l\<rightarrow> a")
  apply simp
  apply (subst lemma_2_10_30 [THEN sym])
  apply (subst wajsberg1)
  apply (simp add: lemma_2_10_32)
  apply (subst sup1_eq_sup2)
  apply (simp add: lemma_4_3_ii_a)
  apply (subgoal_tac "(a r\<rightarrow> b) r\<rightarrow> (b r\<rightarrow> a) = b r\<rightarrow> a")
  apply simp
  apply (subst lemma_2_10_31 [THEN sym])
  apply (subst wajsberg2)
  by (simp add: lemma_2_10_33)
end

class bounded_basic_pseudo_hoop_algebra = zero_one + basic_pseudo_hoop_algebra +
  assumes zero_smallest [simp]: "0 \<le> a"
begin 
end

class inf_a = 
  fixes inf_a :: "'a => 'a => 'a" (infixl "\<sqinter>1" 65)


class pseudo_bl_algebra = zero + sup + inf + monoid_mult + ord + left_imp + right_imp +
  assumes  bounded_lattice: "class.bounded_lattice inf (\<le>) (<) sup 0 1"
  and left_residual_bl: "(x * a \<le> b) = (x \<le> a l\<rightarrow> b)"
  and right_residual_bl: "(a * x \<le> b) = (x \<le> a r\<rightarrow> b)"
  and inf_l_bl_def: "a \<sqinter> b = (a l\<rightarrow> b) * a"
  and inf_r_bl_def: "a \<sqinter> b = a * (a r\<rightarrow> b)"
  and impl_sup_bl: "(a l\<rightarrow> b) \<squnion> (b l\<rightarrow> a) = 1"
  and impr_sup_bl: "(a r\<rightarrow> b) \<squnion> (b r\<rightarrow> a) = 1"
begin
end

context pseudo_bl_algebra begin end

sublocale bounded_basic_pseudo_hoop_algebra < basic:pseudo_bl_algebra 1 "(*)" "0"  "(\<sqinter>)" "(\<squnion>1)" "(l\<rightarrow>)" "(r\<rightarrow>)" "(\<le>)" "(<)"
  apply unfold_locales 
  apply (rule zero_smallest) 
  apply (rule left_residual) 
  apply (rule right_residual)
  apply (rule inf_l_def) 
  apply (simp add: inf_r_def [THEN sym]) 
  apply (rule lemma_4_5_i)  
  apply (simp add: lemma_4_5) 
  by (rule lemma_4_5_ii)

sublocale pseudo_bl_algebra < bounded_lattice: bounded_lattice "inf" "(\<le>)" "(<)" "sup" "0" "1"
  by (rule bounded_lattice)

context pseudo_bl_algebra
begin
  lemma impl_one_bl [simp]: "a l\<rightarrow> a = 1"
    apply (rule bounded_lattice.antisym)
    apply simp_all
    apply (subst left_residual_bl [THEN sym])
    by simp

  lemma impr_one_bl [simp]: "a r\<rightarrow> a = 1"
    apply (rule bounded_lattice.antisym)
    apply simp_all
    apply (subst right_residual_bl [THEN sym])
    by simp

  lemma impl_ded_bl: "((a * b) l\<rightarrow> c) = (a l\<rightarrow> (b l\<rightarrow> c))"
    apply (rule bounded_lattice.antisym)
    apply (case_tac "(a * b l\<rightarrow> c \<le> a l\<rightarrow> b l\<rightarrow> c) = ((a * b l\<rightarrow> c) * a \<le> b l\<rightarrow> c)
      \<and> ((a * b l\<rightarrow> c) * a \<le> b l\<rightarrow> c) = (((a * b l\<rightarrow> c) * a) * b \<le> c)
      \<and> (((a * b l\<rightarrow> c) * a) * b \<le> c) = ((a * b l\<rightarrow> c) * (a * b) \<le> c)
      \<and> ((a * b l\<rightarrow> c) * (a * b) \<le> c) = ((a * b l\<rightarrow> c) \<le> (a * b l\<rightarrow> c))")
    apply simp
    apply (erule notE)
    apply (rule conjI)
    apply (simp add: left_residual_bl)
    apply (rule conjI)
    apply (simp add: left_residual_bl)
    apply (rule conjI)
    apply (simp add: mult.assoc)
    apply (simp add: left_residual_bl)
    apply (simp add: left_residual_bl [THEN sym])
    apply (rule_tac y="(b l\<rightarrow> c) * b" in bounded_lattice.order_trans)
    apply (simp add: mult.assoc [THEN sym]) 
    apply (subst inf_l_bl_def [THEN sym])
    apply (subst bounded_lattice.inf_commute)
    apply (subst inf_l_bl_def)
    apply (subst mult.assoc) 
    apply (subst left_residual_bl) 
    apply simp
    apply (subst left_residual_bl) 
    by simp

  lemma impr_ded_bl: "(b * a r\<rightarrow> c) = (a r\<rightarrow> (b r\<rightarrow> c))"
    apply (rule bounded_lattice.antisym)
    apply (case_tac "(b * a r\<rightarrow> c \<le> a r\<rightarrow> b r\<rightarrow> c) = (a * (b * a r\<rightarrow> c) \<le> b r\<rightarrow> c)
      \<and> (a * (b * a r\<rightarrow> c) \<le> b r\<rightarrow> c) = (b * (a * (b * a r\<rightarrow> c)) \<le> c)
      \<and> (b * ( a* (b * a r\<rightarrow> c)) \<le> c) = ((b * a) * (b * a r\<rightarrow> c) \<le> c)
      \<and> ((b * a) * (b * a r\<rightarrow> c) \<le> c) = ((b * a r\<rightarrow> c) \<le> (b * a r\<rightarrow> c))")
    apply simp
    apply (erule notE)
    apply (rule conjI)
    apply (simp add: right_residual_bl)
    apply (rule conjI)
    apply (simp add: right_residual_bl)
    apply (rule conjI)
    apply (simp add: mult.assoc)
    apply (simp add: right_residual_bl)
    apply (simp add: right_residual_bl [THEN sym])
    apply (rule_tac y="b * (b r\<rightarrow> c)" in bounded_lattice.order_trans)
    apply (simp add: mult.assoc) 
    apply (subst inf_r_bl_def [THEN sym])
    apply (subst bounded_lattice.inf_commute)
    apply (subst inf_r_bl_def)
    apply (subst mult.assoc [THEN sym]) 
    apply (subst right_residual_bl) 
    apply simp
    apply (subst right_residual_bl) 
    by simp

  lemma lesseq_impl_bl: "(a \<le> b) = (a l\<rightarrow> b = 1)"
    apply (rule iffI)
    apply (rule  bounded_lattice.antisym)
    apply simp
    apply (simp add: left_residual_bl [THEN sym])
    apply (subgoal_tac "1 \<le> a l\<rightarrow> b")
    apply (subst (asm) left_residual_bl [THEN sym])
    by simp_all


end

context pseudo_bl_algebra
begin
subclass pseudo_hoop_lattice
  apply unfold_locales
  apply (rule inf_l_bl_def)
  apply (simp add: bounded_lattice.less_le_not_le)
  apply (simp add: mult_1_left)
  apply (simp add: mult_1_right)
  apply (simp add: impl_one_bl)
  apply (simp add: inf_l_bl_def [THEN sym])
  apply (rule bounded_lattice.inf_commute)
  apply (rule impl_ded_bl)
  apply (rule lesseq_impl_bl)
  apply (rule inf_r_bl_def)
  apply (simp add: impr_one_bl)
  apply (simp add: inf_r_bl_def [THEN sym])
  apply (rule bounded_lattice.inf_commute)
  apply (rule impr_ded_bl)
  apply (simp add: inf_r_bl_def [THEN sym] inf_l_bl_def [THEN sym])
  apply (rule bounded_lattice.sup_commute)
  apply simp
  apply safe
  apply (rule bounded_lattice.antisym)
  apply simp_all
  apply (subgoal_tac "a \<le>  a \<squnion> b")
  apply simp
  apply (drule drop_assumption)
  apply simp
  by (simp add: bounded_lattice.sup_assoc)

subclass bounded_basic_pseudo_hoop_algebra
  apply unfold_locales
  apply simp_all
  apply (simp add: left_residual [THEN sym])
  apply (rule_tac y = "((a l\<rightarrow> b) \<squnion> (b l\<rightarrow> a)) l\<rightarrow> c" in bounded_lattice.order_trans)
  apply (simp add: sup_impl_inf)
  apply (simp add: impl_sup_bl)

  apply (simp add: right_residual [THEN sym])
  apply (rule_tac y = "((a r\<rightarrow> b) \<squnion> (b r\<rightarrow> a)) r\<rightarrow> c" in bounded_lattice.order_trans)
  apply (simp add: sup_impr_inf)
  by (simp add: impr_sup_bl)

end

class product_pseudo_hoop_algebra = basic_pseudo_hoop_algebra +
  assumes P1: "b l\<rightarrow> b * b \<le> (a \<sqinter> (a l\<rightarrow> b)) l\<rightarrow> b"
  and P2: "b r\<rightarrow> b * b \<le> (a \<sqinter> (a r\<rightarrow> b)) r\<rightarrow> b"
  and P3: "((a l\<rightarrow> b) l\<rightarrow> b) * (c * a l\<rightarrow> d * a) * (c * b l\<rightarrow> d * b) \<le> c l\<rightarrow> d"
  and P4: "((a r\<rightarrow> b) r\<rightarrow> b) * (a * c r\<rightarrow> a * d) * (b * c r\<rightarrow> b * d) \<le> c r\<rightarrow> d"

class cancel_basic_pseudo_hoop_algebra = basic_pseudo_hoop_algebra + cancel_pseudo_hoop_algebra
begin
subclass product_pseudo_hoop_algebra
  apply unfold_locales
  apply (rule_tac y = "1 l\<rightarrow> b" in order_trans)
  apply (cut_tac a = 1 and b = b and c = b in lemma_4_2_i)
  apply simp
  apply (simp add: lemma_2_5_9_a)

  apply (rule_tac y = "1 r\<rightarrow> b" in order_trans)
  apply (cut_tac a = 1 and b = b and c = b in lemma_4_2_ii)
  apply simp
  apply (simp add: lemma_2_5_9_b)
  apply (simp add: lemma_4_2_i [THEN sym])
  by (simp add: lemma_4_2_ii [THEN sym])

end

class simple_pseudo_hoop_algebra = pseudo_hoop_algebra +
  assumes simple: "normalfilters \<inter> properfilters = {{1}}"

class proper = one +
  assumes proper: "\<exists> a . a \<noteq> 1"

class strong_simple_pseudo_hoop_algebra = pseudo_hoop_algebra +
  assumes strong_simple: "properfilters = {{1}}"
begin

subclass proper
  apply unfold_locales
  apply (cut_tac strong_simple)
  apply (simp add: properfilters_def)
  apply (case_tac "{1} = UNIV")
  apply blast
  by blast

lemma lemma_4_12_i_ii: "a \<noteq> 1 \<Longrightarrow> filterof({a}) = UNIV"
  apply (cut_tac strong_simple)
  apply (simp add: properfilters_def)
  apply (subgoal_tac "filterof {a} \<notin> {F \<in> filters. F \<noteq> UNIV}")
  apply (drule drop_assumption)
  apply (drule drop_assumption)
  apply simp
  apply simp
  apply safe
  apply (subgoal_tac "a \<in> filterof {a}")
  apply simp
  apply (subst filterof_def)
  by simp

lemma lemma_4_12_i_iii: "a \<noteq> 1 \<Longrightarrow> (\<exists> n . a ^ n \<le> b)"
  apply (drule lemma_4_12_i_ii)
  apply (simp add: prop_3_2_i)
  by blast

lemma lemma_4_12_i_iv: "a \<noteq> 1 \<Longrightarrow> (\<exists> n . a l-n\<rightarrow> b = 1)"
  apply (subst lemma_2_4_7_a)
  apply (subst left_lesseq [THEN sym])
  by (simp add: lemma_4_12_i_iii)

lemma lemma_4_12_i_v: "a \<noteq> 1 \<Longrightarrow> (\<exists> n . a r-n\<rightarrow> b = 1)"
  apply (subst lemma_2_4_7_b)
  apply (subst right_lesseq [THEN sym])
  by (simp add: lemma_4_12_i_iii)

end

lemma (in pseudo_hoop_algebra) [simp]: "{1} \<in> filters"
  apply (simp add: filters_def)
  apply safe
  apply (rule antisym)
  by simp_all

class strong_simple_pseudo_hoop_algebra_a = pseudo_hoop_algebra + proper +
  assumes strong_simple_a: "a \<noteq> 1 \<Longrightarrow> filterof({a}) = UNIV"
begin
  subclass  strong_simple_pseudo_hoop_algebra
    apply unfold_locales
    apply (simp add: properfilters_def)
    apply safe
    apply simp_all
    apply (case_tac "xb = 1")
    apply simp
    apply (cut_tac a = xb in strong_simple_a)
    apply simp
    apply (simp add: filterof_def)
    apply blast
    apply (cut_tac proper)
    by blast
end

sublocale strong_simple_pseudo_hoop_algebra < strong_simple_pseudo_hoop_algebra_a
  apply unfold_locales
  by (simp add: lemma_4_12_i_ii)

lemma (in pseudo_hoop_algebra) power_impl: "b l\<rightarrow> a = a \<Longrightarrow> b ^ n l\<rightarrow> a = a"
  apply (induct_tac n)
  apply simp
  by (simp add: left_impl_ded)

lemma (in pseudo_hoop_algebra) power_impr: "b r\<rightarrow> a = a \<Longrightarrow> b ^ n r\<rightarrow> a = a"
  apply (induct_tac n)
  apply simp
  by (simp add: right_impl_ded)

context strong_simple_pseudo_hoop_algebra
begin

lemma lemma_4_13_i: "b l\<rightarrow> a = a \<Longrightarrow> a = 1 \<or> b = 1"
  apply safe
  apply (drule_tac a = b and b = a in lemma_4_12_i_iii)
  apply safe
  apply (subst (asm) left_lesseq)
  apply (drule_tac n = n in power_impl)
  by simp

lemma lemma_4_13_ii: "b r\<rightarrow> a = a \<Longrightarrow> a = 1 \<or> b = 1"
  apply safe
  apply (drule_tac a = b and b = a in lemma_4_12_i_iii)
  apply safe
  apply (subst (asm) right_lesseq)
  apply (drule_tac n = n in power_impr)
  by simp
end

class basic_pseudo_hoop_algebra_A = basic_pseudo_hoop_algebra + 
  assumes left_impl_one: "b l\<rightarrow> a = a \<Longrightarrow> a = 1 \<or> b = 1"
  and right_impl_one: "b r\<rightarrow> a = a \<Longrightarrow> a = 1 \<or> b = 1"
begin
subclass linorder
  apply unfold_locales
  apply (cut_tac a = "x" and b = "y" in lemma_4_8_iii)
  apply (drule left_impl_one)
  apply (simp add: left_lesseq)
  by blast

lemma [simp]: "(a l\<rightarrow> b) r\<rightarrow> b \<le> (b l\<rightarrow> a) r\<rightarrow> a"
  apply (case_tac "a = b")
  apply simp
  apply (cut_tac x = a and y =b in linear) 
  apply safe
  apply (subst (asm) left_lesseq)
  apply (simp add: lemma_2_10_24)
  apply (subst (asm) left_lesseq)
  apply simp
  apply (subst left_lesseq)
  apply (cut_tac b = "((a l\<rightarrow> b) r\<rightarrow> b) l\<rightarrow> a" and a = "a l\<rightarrow> b" in left_impl_one)
  apply (simp add: lemma_2_10_32)
  apply (simp add: left_lesseq [THEN sym])
  apply safe
  apply (erule notE)
  by simp

end

context basic_pseudo_hoop_algebra_A begin

lemma [simp]: "(a r\<rightarrow> b) l\<rightarrow> b \<le> (b r\<rightarrow> a) l\<rightarrow> a"
  apply (case_tac "a = b")
  apply simp
  apply (cut_tac x = a and y =b in linear) 
  apply safe
  apply (subst (asm) right_lesseq)
  apply simp
  apply (simp add: lemma_2_10_26)
  apply (unfold right_lesseq)
  apply (cut_tac b = "((a r\<rightarrow> b) l\<rightarrow> b) r\<rightarrow> a" and a = "a r\<rightarrow> b" in right_impl_one)
  apply (simp add: lemma_2_10_33)
  apply (simp add: right_lesseq [THEN sym])
  apply safe
  apply (erule notE)
  by simp

subclass wajsberg_pseudo_hoop_algebra
  apply unfold_locales
  apply (rule antisym)
  apply simp_all
  apply (rule antisym)
  by simp_all

end

class strong_simple_basic_pseudo_hoop_algebra = strong_simple_pseudo_hoop_algebra + basic_pseudo_hoop_algebra
begin
subclass basic_pseudo_hoop_algebra_A
  apply unfold_locales
  apply (simp add: lemma_4_13_i)
  by (simp add: lemma_4_13_ii)

subclass wajsberg_pseudo_hoop_algebra
  by unfold_locales

end

end
