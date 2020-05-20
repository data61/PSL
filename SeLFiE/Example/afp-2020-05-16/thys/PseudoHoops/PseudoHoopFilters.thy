
section\<open>Filters and Congruences\<close>

theory PseudoHoopFilters
imports PseudoHoops
begin

context pseudo_hoop_algebra
begin
definition
  "filters = {F . F \<noteq> {} \<and> (\<forall> a b . a \<in> F \<and> b \<in> F \<longrightarrow> a * b \<in> F) \<and> (\<forall> a b . a \<in> F \<and> a \<le> b \<longrightarrow> b \<in> F)}"

definition
  "properfilters = {F . F \<in> filters \<and> F \<noteq> UNIV}"

definition 
  "maximalfilters = {F . F \<in> filters \<and> (\<forall> A . A \<in> filters \<and> F \<subseteq> A \<longrightarrow> A = F \<or> A = UNIV)}"

definition
  "ultrafilters = properfilters \<inter> maximalfilters"

lemma filter_i: "F \<in> filters \<Longrightarrow> a \<in> F \<Longrightarrow> b \<in> F \<Longrightarrow> a * b \<in> F"
  by (simp add: filters_def)

lemma filter_ii: "F \<in> filters \<Longrightarrow> a \<in> F \<Longrightarrow> a \<le> b \<Longrightarrow> b \<in> F"
 by (simp add: filters_def)

lemma filter_iii [simp]: "F \<in> filters \<Longrightarrow> 1 \<in> F"
  by (auto simp add: filters_def)

lemma filter_left_impl:
  "(F \<in> filters) = ((1 \<in> F) \<and> (\<forall> a b . a \<in> F \<and> a l\<rightarrow> b \<in> F \<longrightarrow> b \<in> F))"
  apply safe
  apply simp
  apply (frule_tac a = "a l\<rightarrow> b" and b = a in filter_i)
  apply simp
  apply simp
  apply (rule_tac a = "(a l\<rightarrow> b) * a" in filter_ii)
  apply simp
  apply simp
  apply (simp add: inf_l_def [THEN sym])
  apply (subst filters_def)
  apply safe
  apply (subgoal_tac "a l\<rightarrow> (b l\<rightarrow> a * b) \<in> F")
  apply blast
  apply (subst left_impl_ded [THEN sym])
  apply (subst left_impl_one)
  apply safe
  apply (subst (asm) left_lesseq)
  by blast

lemma filter_right_impl:
  "(F \<in> filters) = ((1 \<in> F) \<and> (\<forall> a b . a \<in> F \<and> a r\<rightarrow> b \<in> F \<longrightarrow> b \<in> F))"
  apply safe
  apply simp
  apply (frule_tac a = a and b = "a r\<rightarrow> b" in filter_i)
  apply simp
  apply simp
  apply (rule_tac a = "a * (a r\<rightarrow> b)" in filter_ii)
  apply simp
  apply simp
  apply (simp add: inf_r_def [THEN sym])
  apply (subst filters_def)
  apply safe
  apply (subgoal_tac "b r\<rightarrow> (a r\<rightarrow> a * b) \<in> F")
  apply blast
  apply (subst right_impl_ded [THEN sym])
  apply (subst right_impl_one)
  apply safe
  apply (subst (asm) right_lesseq)
  by blast

lemma [simp]: "A \<subseteq> filters \<Longrightarrow> \<Inter> A \<in> filters"
  apply (simp add: filters_def)
  apply safe
  apply (simp add: Inter_eq)
  apply (drule_tac x = "1" in spec)
  apply safe
  apply (erule notE)
  apply (subgoal_tac "x \<in> filters")
  apply simp
  apply (simp add: filters_def)
  apply blast
  apply (frule rev_subsetD)
  apply simp
  apply simp
  apply (frule rev_subsetD)
  apply simp
  apply (subgoal_tac "a \<in> X")
  apply blast
  by blast

definition
  "filterof X = \<Inter> {F . F \<in> filters \<and> X \<subseteq> F}"

lemma [simp]: "filterof X \<in> filters"
  by (auto simp add: filterof_def)

lemma times_le_mono [simp]: "x \<le> y \<Longrightarrow> u \<le> v \<Longrightarrow> x * u \<le> y * v"
  apply (rule_tac y = "x * v" in order_trans)
  by (simp_all add: mult_left_mono mult_right_mono)

lemma prop_3_2_i:
  "filterof X = {a . \<exists> n x . x \<in> X *^ n \<and> x \<le> a}"
  apply safe
  apply (subgoal_tac "{a . \<exists> n x . x \<in> X *^ n \<and> x \<le> a} \<in> filters")
  apply (simp add: filterof_def)
  apply (drule_tac x = "{a::'a. \<exists>(n::nat) x::'a. x \<in> X *^ n \<and> x \<le> a}" in spec)
  apply safe
  apply (rule_tac x = "1::nat" in exI)
  apply (rule_tac x = "xa" in exI)
  apply (simp add: times_set_def)
  apply (drule drop_assumption)
  apply (simp add: filters_def)
  apply safe
  apply (rule_tac x = "1" in exI)
  apply (rule_tac x = "0" in exI)
  apply (rule_tac x = "1" in exI)
  apply simp
  apply (rule_tac x = "n + na" in exI)
  apply (rule_tac x = "x * xa" in exI)
  apply safe
  apply (simp add: power_set_add times_set_def)
  apply blast
  apply simp
  apply (rule_tac x = "n" in exI)
  apply (rule_tac x = "x" in exI)
  apply simp
  apply (simp add: filterof_def)
  apply safe
  apply (rule filter_ii)
  apply simp_all
  apply (subgoal_tac "\<forall>x . x \<in> X *^ n \<longrightarrow> x \<in> xb")
  apply simp
  apply (induct_tac n)
  apply (simp add: power_set_0)
  apply (simp add: power_set_Suc times_set_def)
  apply safe
  apply (rule filter_i)
  apply simp_all
  by blast
  
lemma ultrafilter_union:
  "ultrafilters = {F . F \<in> filters \<and> F \<noteq> UNIV \<and> (\<forall> x . x \<notin> F \<longrightarrow> filterof (F \<union> {x}) = UNIV)}"
  apply (simp add: ultrafilters_def maximalfilters_def properfilters_def filterof_def)
  by auto

lemma filterof_sub: "F \<in> filters \<Longrightarrow> X \<subseteq> F \<Longrightarrow> filterof X \<subseteq> F"
  apply (simp add: filterof_def)
  by blast

lemma filterof_elem [simp]: "x \<in> X \<Longrightarrow> x \<in>  filterof X"
  apply (simp add: filterof_def)
  by blast

lemma [simp]: "filterof X \<in> filters"
  apply (simp add: filters_def  prop_3_2_i)
  apply safe
  apply (rule_tac x = 1 in exI)
  apply (rule_tac x = 0 in exI)
  apply (rule_tac x = 1 in exI)
  apply auto [1]
  apply (rule_tac x = "n + na" in exI)
  apply (rule_tac x = "x * xa" in exI)
  apply safe
  apply (unfold power_set_add)
  apply (simp add: times_set_def)
  apply auto [1]
  apply (rule_tac y = "x * b" in order_trans)
  apply (rule mult_left_mono)
  apply simp
  apply (simp add: mult_right_mono)
  apply (rule_tac x = n in exI)
  apply (rule_tac x = x in exI)
  by simp



lemma singleton_power [simp]: "{a} *^ n = {b . b = a ^ n}"
  apply (induct_tac n)
  apply auto [1]
  by (simp add: times_set_def)

lemma power_pair: "x \<in> {a, b} *^ n \<Longrightarrow> \<exists> i j . i + j = n \<and> x \<le> a ^ i \<and> x \<le> b ^ j"
  apply (subgoal_tac "\<forall> x . x \<in> {a, b} *^ n \<longrightarrow> (\<exists> i j . i + j = n \<and> x \<le> a ^ i \<and> x \<le> b ^ j)")
  apply auto[1]
  apply (drule drop_assumption)
  apply (induct_tac n)
  apply auto [1]
  apply safe
  apply (simp add: times_set_def)
  apply safe
  apply (drule_tac x = y in spec)
  apply safe
  apply (rule_tac x = "i + 1" in exI) 
  apply (rule_tac x = "j" in exI)
  apply simp
  apply (rule_tac y = y in order_trans)
  apply simp_all
  apply (drule_tac x = y in spec)
  apply safe
  apply (rule_tac x = "i" in exI) 
  apply (rule_tac x = "j+1" in exI)
  apply simp
  apply (rule_tac y = y in order_trans)
  by simp_all

lemma filterof_supremum:
  "c \<in> supremum {a, b} \<Longrightarrow> filterof {c} = filterof {a} \<inter> filterof {b}"
  apply safe
  apply (cut_tac X = "{c}" and F = "filterof {a}" in filterof_sub)
  apply simp_all
  apply (simp add: supremum_def upper_bound_def)
  apply safe
  apply (rule_tac  a = a in filter_ii)
  apply simp_all
  apply blast
  apply (cut_tac X = "{c}" and F = "filterof {b}" in filterof_sub)
  apply simp_all
  apply (simp add: supremum_def upper_bound_def)
  apply safe
  apply (rule_tac  a = b in filter_ii)
  apply simp_all
  apply blast
  apply (subst (asm) prop_3_2_i)
  apply simp
  apply (subst (asm) prop_3_2_i)
  apply simp
  apply safe
  apply (cut_tac A = "{a, b}" and a = c and b = x and n = "n + na" in  lemma_2_8_ii1)
  apply simp
  apply (subst prop_3_2_i)
  apply simp
  apply (rule_tac x = "n + na" in exI)
  apply (subgoal_tac "infimum ((\<lambda>xa::'a. xa r\<rightarrow> x) ` ({a, b} *^ (n + na))) = {1}")
  apply simp
  apply (simp add: right_lesseq)
  apply (subst infimum_unique)
  apply (subst infimum_def lower_bound_def)
  apply (subst lower_bound_def)
  apply safe
  apply simp_all
  apply (drule power_pair)
  apply safe
  apply (subst right_residual [THEN sym])
  apply simp
  apply (case_tac "n \<le> i")
  apply (rule_tac y = "a ^ n" in order_trans)
  apply (rule_tac y = "a ^ i" in order_trans)
  apply simp_all
  apply (subgoal_tac "na \<le> j")
  apply (rule_tac y = "b ^ na" in order_trans)
  apply (rule_tac y = "b ^ j" in order_trans)
  by simp_all


definition "d1 a b = (a l\<rightarrow> b) * (b l\<rightarrow> a)"
definition "d2 a b = (a r\<rightarrow> b) * (b r\<rightarrow> a)"


definition "d3 a b = d1 b a"
definition "d4 a b = d2 b a"

lemma [simp]: "(a * b = 1) = (a = 1 \<and> b = 1)"
  apply (rule iffI)
  apply (rule conjI)
  apply (rule antisym)
  apply simp
  apply (rule_tac y = "a*b" in order_trans)
  apply simp
  apply (drule drop_assumption)
  apply simp
  apply (rule antisym)
  apply simp
  apply (rule_tac y = "a*b" in order_trans)
  apply simp
  apply (drule drop_assumption)
  apply simp
  by simp

lemma lemma_3_5_i_1: "(d1 a b = 1) = (a = b)"
  apply (simp add: d1_def left_lesseq [THEN sym])
  by auto

lemma lemma_3_5_i_2: "(d2 a b = 1) = (a = b)"
  apply (simp add: d2_def right_lesseq [THEN sym])
  by auto

lemma lemma_3_5_i_3: "(d3 a b = 1) = (a = b)"
  apply (simp add: d3_def lemma_3_5_i_1)
  by auto

lemma lemma_3_5_i_4: "(d4 a b = 1) = (a = b)"
  apply (simp add: d4_def lemma_3_5_i_2)
  by auto

lemma lemma_3_5_ii_1 [simp]: "d1 a a = 1"
  apply (subst lemma_3_5_i_1)
  by simp

lemma lemma_3_5_ii_2 [simp]: "d2 a a = 1"
  apply (subst lemma_3_5_i_2)
  by simp

lemma lemma_3_5_ii_3 [simp]: "d3 a a = 1"
  apply (subst lemma_3_5_i_3)
  by simp

lemma lemma_3_5_ii_4 [simp]: "d4 a a = 1"
  apply (subst lemma_3_5_i_4)
  by simp

lemma [simp]: "(a l\<rightarrow> 1) = 1"
  by (simp add: left_lesseq [THEN sym])

end

context pseudo_hoop_algebra begin

lemma [simp]: "(a r\<rightarrow> 1) = 1"
  by simp

lemma lemma_3_5_iii_1 [simp]: "d1 a 1 = a"
  by (simp add: d1_def)

lemma lemma_3_5_iii_2 [simp]: "d2 a 1 = a"
  by (simp add: d2_def)

lemma lemma_3_5_iii_3 [simp]: "d3 a 1 = a"
  by (simp add: d3_def d1_def)

lemma lemma_3_5_iii_4 [simp]: "d4 a 1 = a"
  by (simp add: d4_def d2_def)

lemma lemma_3_5_iv_1: "(d1 b c) * (d1 a b) * (d1 b c) \<le> d1 a c"
  apply (simp add: d1_def)
  apply (subgoal_tac "(b l\<rightarrow> c) * (c l\<rightarrow> b) * ((a l\<rightarrow> b) * (b l\<rightarrow> a)) * ((b l\<rightarrow> c) * (c l\<rightarrow> b)) = 
    ((b l\<rightarrow> c) * (c l\<rightarrow> b) * (a l\<rightarrow> b)) * ((b l\<rightarrow> a) * (b l\<rightarrow> c) * (c l\<rightarrow> b))")
  apply simp
  apply (rule mult_mono)
  apply (rule_tac y = "(b l\<rightarrow> c) * (a l\<rightarrow> b)" in order_trans)
  apply (rule mult_right_mono)
  apply simp
  apply (simp add: lemma_2_5_14)
  apply (rule_tac y = "(b l\<rightarrow> a) * (c l\<rightarrow> b)" in order_trans)
  apply (rule mult_right_mono)
  apply simp
  apply (simp add: lemma_2_5_14)
  by (simp add: mult.assoc)

lemma lemma_3_5_iv_2: "(d2 a b) * (d2 b c) * (d2 a b) \<le> d2 a c"
  apply (simp add: d2_def)
  apply (subgoal_tac "(a r\<rightarrow> b) * (b r\<rightarrow> a) * ((b r\<rightarrow> c) * (c r\<rightarrow> b)) * ((a r\<rightarrow> b) * (b r\<rightarrow> a)) = 
    ((a r\<rightarrow> b) * (b r\<rightarrow> a) * (b r\<rightarrow> c)) * ((c r\<rightarrow> b) * (a r\<rightarrow> b) * (b r\<rightarrow> a))")
  apply simp
  apply (rule mult_mono)
  apply (rule_tac y = "(a r\<rightarrow> b) * (b r\<rightarrow> c)" in order_trans)
  apply (rule mult_right_mono)
  apply simp
  apply (simp add: lemma_2_5_15)
  apply (rule_tac y = "(c r\<rightarrow> b) * (b r\<rightarrow> a)" in order_trans)
  apply (rule mult_right_mono)
  apply simp
  apply (simp add: lemma_2_5_15)
  by (simp add: mult.assoc)



lemma lemma_3_5_iv_3: "(d3 a b) * (d3 b c) * (d3 a b) \<le> d3 a c"
  by (simp add: d3_def lemma_3_5_iv_1)

lemma lemma_3_5_iv_4: "(d4 b c) * (d4 a b) * (d4 b c) \<le> d4 a c"
  by (simp add: d4_def lemma_3_5_iv_2)

definition
  "cong_r F a b \<equiv> d1 a b \<in> F"

definition
  "cong_l F a b \<equiv> d2 a b \<in> F"

lemma cong_r_filter: "F \<in> filters \<Longrightarrow> (cong_r F a b) = (a l\<rightarrow> b \<in> F \<and> b l\<rightarrow> a \<in> F)"
  apply (simp add: cong_r_def d1_def)
  apply safe
  apply (rule filter_ii)
  apply simp_all
  apply simp
  apply (rule filter_ii)
  apply simp_all
  apply simp
  by (simp add: filter_i)

lemma cong_r_symmetric: "F \<in> filters \<Longrightarrow> (cong_r F a b) = (cong_r F b a)"
  apply (simp add: cong_r_filter)
  by blast

lemma cong_r_d3: "F \<in> filters \<Longrightarrow> (cong_r F a b) = (d3 a b \<in> F)"
  apply (simp add: d3_def)
  apply (subst cong_r_symmetric)
  by (simp_all add: cong_r_def)


lemma cong_l_filter: "F \<in> filters \<Longrightarrow> (cong_l F a b) = (a r\<rightarrow> b \<in> F \<and> b r\<rightarrow> a \<in> F)"
  apply (simp add: cong_l_def d2_def)
  apply safe
  apply (rule filter_ii)
  apply simp_all
  apply simp
  apply (rule filter_ii)
  apply simp_all
  apply simp
  by (simp add: filter_i)

lemma cong_l_symmetric: "F \<in> filters \<Longrightarrow> (cong_l F a b) = (cong_l F b a)"
  apply (simp add: cong_l_filter)
  by blast

lemma cong_l_d4: "F \<in> filters \<Longrightarrow> (cong_l F a b) = (d4 a b \<in> F)"
  apply (simp add: d4_def)
  apply (subst cong_l_symmetric)
  by (simp_all add: cong_l_def)

lemma cong_r_reflexive: "F \<in> filters \<Longrightarrow> cong_r F a a"
  by (simp add: cong_r_def)

lemma cong_r_transitive: "F \<in> filters \<Longrightarrow> cong_r F a b \<Longrightarrow> cong_r F b c \<Longrightarrow> cong_r F a c"
  apply (simp add: cong_r_filter)
  apply safe
  apply (rule_tac a = "(b l\<rightarrow> c) * (a l\<rightarrow> b)" in filter_ii)
  apply simp_all
  apply (rule filter_i)
  apply simp_all
  apply (simp add: lemma_2_5_14)
  apply (rule_tac a = "(b l\<rightarrow> a) * (c l\<rightarrow> b)" in filter_ii)
  apply simp_all
  apply (rule filter_i)
  apply simp_all
  by (simp add: lemma_2_5_14)



lemma cong_l_reflexive: "F \<in> filters \<Longrightarrow> cong_l F a a"
  by (simp add: cong_l_def)

lemma cong_l_transitive: "F \<in> filters \<Longrightarrow> cong_l F a b \<Longrightarrow> cong_l F b c \<Longrightarrow> cong_l F a c"
  apply (simp add: cong_l_filter)
  apply safe
  apply (rule_tac a = "(a r\<rightarrow> b) * (b r\<rightarrow> c)" in filter_ii)
  apply simp_all
  apply (rule filter_i)
  apply simp_all
  apply (simp add: lemma_2_5_15)
  apply (rule_tac a = "(c r\<rightarrow> b) * (b r\<rightarrow> a)" in filter_ii)
  apply simp_all
  apply (rule filter_i)
  apply simp_all
  by (simp add: lemma_2_5_15)

lemma lemma_3_7_i: "F \<in> filters \<Longrightarrow> F = {a . cong_r F a 1}"
  by (simp add: cong_r_def)

lemma lemma_3_7_ii: "F \<in> filters \<Longrightarrow> F = {a . cong_l F a 1}"
  by (simp add: cong_l_def)

lemma lemma_3_8_i: "F \<in> filters \<Longrightarrow> (cong_r F a b) = (\<exists> x y . x \<in> F \<and> y \<in> F \<and> x * a = y * b)"
  apply (subst cong_r_filter)
  apply safe
  apply (rule_tac x = "a l\<rightarrow> b" in exI)
  apply (rule_tac x = "b l\<rightarrow> a" in exI)
  apply (simp add: left_impl_times)
  apply (subgoal_tac "x \<le> a l\<rightarrow> b")
  apply (simp add: filter_ii)
  apply (simp add: left_residual [THEN sym])
  apply (subgoal_tac "y \<le> b l\<rightarrow> a")
  apply (simp add: filter_ii)
  apply (simp add: left_residual [THEN sym])
  apply (subgoal_tac "y * b = x * a")
  by simp_all

lemma lemma_3_8_ii: "F \<in> filters \<Longrightarrow> (cong_l F a b) = (\<exists> x y . x \<in> F \<and> y \<in> F \<and> a * x = b * y)"
  apply (subst cong_l_filter)
  apply safe
  apply (rule_tac x = "a r\<rightarrow> b" in exI)
  apply (rule_tac x = "b r\<rightarrow> a" in exI)
  apply (simp add: right_impl_times)
  apply (subgoal_tac "x \<le> a r\<rightarrow> b")
  apply (simp add: filter_ii)
  apply (simp add: right_residual [THEN sym])
  apply (subgoal_tac "y \<le> b r\<rightarrow> a")
  apply (simp add: filter_ii)
  apply (simp add: right_residual [THEN sym])
  apply (subgoal_tac "b * y = a * x")
  by simp_all

lemma lemma_3_9_i: "F \<in> filters \<Longrightarrow> cong_r F a b  \<Longrightarrow> cong_r F c d \<Longrightarrow> (a l\<rightarrow> c \<in> F) = (b l\<rightarrow> d \<in> F)"
  apply (simp add: cong_r_filter)
  apply safe
  apply (rule_tac a = "(a l\<rightarrow> d) * (b l\<rightarrow> a)" in filter_ii)
  apply (simp_all add: lemma_2_5_14)
  apply (rule_tac a = "((c l\<rightarrow> d) * (a l\<rightarrow> c)) * (b l\<rightarrow> a)" in filter_ii)
  apply simp_all
  apply (simp add: filter_i)
  apply (rule mult_right_mono)
  apply (simp_all add: lemma_2_5_14)

  apply (rule_tac a = "(b l\<rightarrow> c) * (a l\<rightarrow> b)" in filter_ii)
  apply (simp_all add: lemma_2_5_14)
  apply (rule_tac a = "((d l\<rightarrow> c) * (b l\<rightarrow> d)) * (a l\<rightarrow> b)" in filter_ii)
  apply simp_all
  apply (simp add: filter_i)
  apply (rule mult_right_mono)
  by (simp_all add: lemma_2_5_14)

lemma lemma_3_9_ii: "F \<in> filters \<Longrightarrow> cong_l F a b  \<Longrightarrow> cong_l F c d \<Longrightarrow> (a r\<rightarrow> c \<in> F) = (b r\<rightarrow> d \<in> F)"
  apply (simp add: cong_l_filter)
  apply safe
  apply (rule_tac a = "(b r\<rightarrow> a) * (a r\<rightarrow> d)" in filter_ii)
  apply (simp_all add: lemma_2_5_15)
  apply (rule_tac a = "(b r\<rightarrow> a) * ((a r\<rightarrow> c) * (c r\<rightarrow> d))" in filter_ii)
  apply simp_all
  apply (simp add: filter_i)
  apply (rule mult_left_mono)
  apply (simp_all add: lemma_2_5_15)

  apply (rule_tac a = "(a r\<rightarrow> b) * (b r\<rightarrow> c)" in filter_ii)
  apply (simp_all add: lemma_2_5_15)
  apply (rule_tac a = "(a r\<rightarrow> b) * ((b r\<rightarrow> d) * (d r\<rightarrow> c))" in filter_ii)
  apply simp_all
  apply (simp add: filter_i)
  apply (rule mult_left_mono)
  by (simp_all add: lemma_2_5_15)

definition
  "normalfilters = {F . F \<in> filters \<and> (\<forall> a b . (a l\<rightarrow> b \<in> F) = (a r\<rightarrow> b \<in> F))}"

lemma normalfilter_i:
  "H \<in> normalfilters \<Longrightarrow> a l\<rightarrow> b \<in> H \<Longrightarrow> a r\<rightarrow> b \<in> H"
  by (simp add: normalfilters_def)


lemma normalfilter_ii:
  "H \<in> normalfilters \<Longrightarrow> a r\<rightarrow> b \<in> H \<Longrightarrow> a l\<rightarrow> b \<in> H"
  by (simp add: normalfilters_def)

lemma [simp]: "H \<in> normalfilters \<Longrightarrow> H \<in> filters" 
  by (simp add: normalfilters_def)

lemma lemma_3_10_i_ii:
  "H \<in> normalfilters \<Longrightarrow> {a} ** H = H ** {a}"
  apply (simp add: times_set_def)
  apply safe
  apply simp
  apply (rule_tac x = "a l\<rightarrow> a * y" in bexI)
  apply (simp add: inf_l_def [THEN sym])
  apply (rule antisym)
  apply simp
  apply simp
  apply (rule normalfilter_ii)
  apply simp_all
  apply (rule_tac a = "y" in filter_ii)
  apply simp_all
  apply (simp add: right_residual [THEN sym])
  
  apply (rule_tac x = "a r\<rightarrow> xa * a" in bexI)
  apply (simp add: inf_r_def [THEN sym])
  apply (rule antisym)
  apply simp
  apply simp
  apply (rule normalfilter_i)
  apply simp_all
  apply (rule_tac a = "xa" in filter_ii)
  apply simp_all
  by (simp add: left_residual [THEN sym])


lemma lemma_3_10_ii_iii:
  "H \<in> filters \<Longrightarrow> (\<forall> a . {a} ** H = H ** {a}) \<Longrightarrow> cong_r H = cong_l H"
  apply (subst fun_eq_iff)
  apply (subst fun_eq_iff)
  apply safe
  apply (subst (asm) lemma_3_8_i)
  apply simp_all
  apply safe
  apply (subst lemma_3_8_ii)
  apply simp_all
  apply (subgoal_tac "xb * x \<in> {x} ** H")
  apply (subgoal_tac "y * xa \<in> {xa} ** H")
  apply (drule drop_assumption)
  apply (drule drop_assumption)
  apply (simp add: times_set_def)
  apply safe
  apply (rule_tac x = ya in exI)
  apply simp
  apply (rule_tac x = yb in exI)
  apply simp
  apply (drule_tac x = xa in spec)
  apply (simp add: times_set_def)
  apply auto[1]
  apply (drule_tac x = x in spec)
  apply simp
  apply (simp add: times_set_def)
  apply (rule_tac x = xb in bexI)
  apply simp_all

  apply (subst (asm) lemma_3_8_ii)
  apply simp_all
  apply safe
  apply (subst lemma_3_8_i)
  apply simp_all
  apply (subgoal_tac "x * xb \<in> H ** {x}")
  apply (subgoal_tac "xa * y \<in> H ** {xa}")
  apply (drule drop_assumption)
  apply (drule drop_assumption)
  apply (simp add: times_set_def)
  apply safe
  apply (rule_tac x = xc in exI)
  apply simp
  apply (rule_tac x = xd in exI)
  apply simp
  apply (drule_tac x = xa in spec)
  apply (simp add: times_set_def)
  apply auto[1]
  apply (drule_tac x = x in spec)
  apply (subgoal_tac "x * xb \<in> {x} ** H")
  apply simp
  apply (subst times_set_def)
  by blast

lemma lemma_3_10_i_iii: 
  "H \<in> normalfilters \<Longrightarrow> cong_r H = cong_l H"
  by (simp add: lemma_3_10_i_ii lemma_3_10_ii_iii)

lemma order_impl_l [simp]: "a \<le> b \<Longrightarrow> a l\<rightarrow> b = 1"
  by (simp add: left_lesseq)

end

context pseudo_hoop_algebra begin

lemma impl_l_d1: "(a l\<rightarrow> b) = d1 a (a \<sqinter> b)"
  by (simp add: d1_def lemma_2_6_20_a ) 

lemma impl_r_d2: "(a r\<rightarrow> b) = d2 a (a \<sqinter> b)"
  by (simp add: d2_def lemma_2_6_21_a)

lemma lemma_3_10_iii_i:
  "H \<in> filters \<Longrightarrow> cong_r H = cong_l H \<Longrightarrow> H \<in> normalfilters"
  apply (unfold normalfilters_def)
  apply (simp add: impl_l_d1 impl_r_d2)
  apply safe
  apply (subgoal_tac  "cong_r H a (a \<sqinter> b)")
  apply simp
  apply (subst (asm) cong_l_def)
  apply simp
  apply (subst cong_r_def)
  apply simp
  apply (subgoal_tac  "cong_r H a (a \<sqinter> b)")
  apply (subst (asm) cong_r_def)
  apply simp
  apply simp
  apply (subst cong_l_def)
  by simp


lemma lemma_3_10_ii_i:
  "H \<in> filters \<Longrightarrow>  (\<forall> a . {a} ** H = H ** {a}) \<Longrightarrow> H \<in> normalfilters"
  apply (rule lemma_3_10_iii_i)
  apply simp
  apply (rule lemma_3_10_ii_iii)
  by simp_all

definition
  "allpowers x n = {y . \<exists> i. i < n \<and> y = x ^ i}"

lemma times_set_in: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c = a * b \<Longrightarrow> c \<in> A ** B" 
  apply (simp add: times_set_def)
  by auto

lemma power_set_power: "a \<in> A \<Longrightarrow> a ^ n \<in> A *^ n"
  apply (induct_tac n)
  apply simp
  apply simp
  apply (rule_tac a = a and b = "a ^ n" in times_set_in)
  by simp_all

lemma normal_filter_union: "H \<in> normalfilters \<Longrightarrow> (H \<union> {x}) *^ n = (H ** (allpowers x n)) \<union> {x ^ n} "
  apply (induct_tac n)
  apply (simp add: times_set_def allpowers_def)
  apply safe
  apply simp
  apply (simp add:  times_set_def)
  apply safe
  apply (simp add:  allpowers_def)
  apply safe
  apply (subgoal_tac "x * xa \<in> H ** {x}")
  apply (simp add: times_set_def)
  apply safe
  apply (drule_tac x = "xb" in bspec)
  apply simp
  apply (drule_tac x = "x ^ (i + 1)" in spec)
  apply simp
  apply safe
  apply (erule notE)
  apply (rule_tac x = "i + 1" in exI)
  apply simp
  apply (erule notE)
  apply (simp add: mult.assoc [THEN sym])
  apply (drule_tac a = x in lemma_3_10_i_ii)
  apply (subgoal_tac "H ** {x} = {x} ** H")
  apply simp
  apply (simp add: times_set_def)
  apply auto[1]
  apply simp
  apply (drule_tac x = "xaa" in bspec)
  apply simp
  apply (drule_tac x = "x ^ n" in bspec)
  apply (simp add: allpowers_def)
  apply blast
  apply simp
  apply (drule_tac x = "xaa * xb" in bspec)
  apply (simp add: filter_i)
  apply (simp add: mult.assoc)
  apply (drule_tac x = "ya" in bspec)
  apply (simp add: allpowers_def)
  apply safe
  apply (rule_tac x = i in exI)
  apply simp
  apply simp
  apply (subst (asm)  times_set_def)
  apply (subst (asm)  times_set_def)
  apply simp
  apply safe
  apply (subst (asm) allpowers_def)
  apply (subst (asm) allpowers_def)
  apply safe
  apply (case_tac "i = 0")
  apply simp
  apply (rule_tac a = xa and b = 1 in times_set_in)
  apply blast
  apply (simp add: allpowers_def times_set_def)
  apply safe
  apply simp
  apply (drule_tac x = 1 in bspec)
  apply simp
  apply (drule_tac x = 1 in spec)
  apply simp
  apply (drule_tac x = 0 in spec)
  apply auto[1]
  apply simp
  apply (rule_tac a = xaa and b = "x ^ i" in times_set_in)
  apply blast
  apply (case_tac "i = n")
  apply simp
  apply (simp add: allpowers_def)
  apply safe
  apply (subgoal_tac "x ^ i \<in>  H ** {y . \<exists>i<n. y = x ^ i}")
  apply simp
  apply (rule_tac a = 1 and b = "x ^ i" in times_set_in)
  apply simp
  apply simp
  apply (rule_tac x = i in exI)
  apply simp
  apply simp
  apply (rule power_set_power)
  by simp


lemma lemma_3_11_i: "H \<in> normalfilters \<Longrightarrow> filterof (H \<union> {x}) = {a . \<exists> n h . h \<in> H \<and> h * x ^ n \<le> a}"
  apply (subst prop_3_2_i)
  apply (subst normal_filter_union)
  apply simp_all
  apply safe
  apply (rule_tac x = n in exI)
  apply (rule_tac x = 1 in exI)
  apply simp
  apply (simp_all add: allpowers_def times_set_def)
  apply safe
  apply (rule_tac x = i in exI)
  apply (rule_tac x = xb in exI)
  apply simp
  apply (rule_tac x = "n + 1" in exI)
  apply (rule_tac x = "h * x ^ n" in exI)
  apply safe
  apply (erule notE)
  apply (rule_tac x = h in bexI)
  apply (rule_tac x = "x ^ n" in exI)
  by auto

lemma lemma_3_11_ii: "H \<in> normalfilters \<Longrightarrow> filterof (H \<union> {x}) = {a . \<exists> n h . h \<in> H \<and> (x ^ n) * h \<le> a}"
  apply (subst lemma_3_11_i)
  apply simp_all
  apply safe
  apply (rule_tac x = n in exI)
  apply (subgoal_tac "h * x ^ n \<in> {x ^ n} ** H")
  apply (simp add: times_set_def)
  apply auto[1]
  apply (drule_tac a = "x ^ n" in lemma_3_10_i_ii)
  apply simp
  apply (simp add: times_set_def)
  apply auto[1]
  apply (rule_tac x = n in exI)
  apply (subgoal_tac "(x ^ n) * h \<in> H ** {x ^ n}")
  apply (simp add: times_set_def)
  apply auto[1]
  apply (drule_tac a = "x ^ n" in lemma_3_10_i_ii)
  apply (drule_tac sym)
  apply simp
  apply (simp add: times_set_def)
  by auto

lemma lemma_3_12_i_ii:
  "H \<in> normalfilters \<Longrightarrow> H \<in> ultrafilters \<Longrightarrow> x \<notin> H \<Longrightarrow> (\<exists> n . x ^ n l\<rightarrow> a \<in> H)"
  apply (subst (asm) ultrafilter_union)
  apply clarify
  apply (drule_tac x = x in spec)
  apply clarify
  apply (subst (asm) lemma_3_11_i)
  apply assumption
  apply (subgoal_tac "a \<in> {a::'a. \<exists>(n::nat) h::'a. h \<in> H \<and> h * x ^ n \<le> a}")
  apply clarify
  apply (rule_tac x = n in exI)
  apply (simp add: left_residual)
  apply (rule filter_ii)
  by simp_all


lemma lemma_3_12_ii_i:
  "H \<in> normalfilters \<Longrightarrow> H \<in> properfilters \<Longrightarrow> (\<forall> x a . x \<notin> H \<longrightarrow> (\<exists> n . x ^ n l\<rightarrow> a \<in> H)) \<Longrightarrow> H \<in> maximalfilters"
  apply (subgoal_tac "H \<in> ultrafilters") 
  apply (simp add: ultrafilters_def)
  apply (subst ultrafilter_union)
  apply clarify
  apply (subst (asm) properfilters_def)
  apply clarify
  apply (subst lemma_3_11_i)
  apply simp_all
  apply safe
  apply simp_all
  apply (drule_tac x = x in spec)
  apply clarify
  apply (drule_tac x = xb in spec)
  apply clarify
  apply (rule_tac x = n in exI)
  apply (rule_tac x = "x ^ n l\<rightarrow> xb" in exI)
  apply clarify
  apply (subst inf_l_def [THEN sym])
  by simp

lemma lemma_3_12_i_iii:
  "H \<in> normalfilters \<Longrightarrow> H \<in> ultrafilters \<Longrightarrow> x \<notin> H \<Longrightarrow> (\<exists> n . x ^ n r\<rightarrow> a \<in> H)"
  apply (subst (asm) ultrafilter_union)
  apply clarify
  apply (drule_tac x = x in spec)
  apply clarify
  apply (subst (asm) lemma_3_11_ii)
  apply assumption
  apply (subgoal_tac "a \<in> {a::'a. \<exists>(n::nat) h::'a. h \<in> H \<and> (x ^ n) * h \<le> a}")
  apply clarify
  apply (rule_tac x = n in exI)
  apply (simp add: right_residual)
  apply (rule filter_ii)
  by simp_all


lemma lemma_3_12_iii_i:
  "H \<in> normalfilters \<Longrightarrow> H \<in> properfilters \<Longrightarrow> (\<forall> x a . x \<notin> H \<longrightarrow> (\<exists> n . x ^ n r\<rightarrow> a \<in> H)) \<Longrightarrow> H \<in> maximalfilters"
  apply (subgoal_tac "H \<in> ultrafilters") 
  apply (simp add: ultrafilters_def)
  apply (subst ultrafilter_union)
  apply clarify
  apply (subst (asm) properfilters_def)
  apply clarify
  apply (subst lemma_3_11_ii)
  apply simp_all
  apply safe
  apply simp_all
  apply (drule_tac x = x in spec)
  apply clarify
  apply (drule_tac x = xb in spec)
  apply clarify
  apply (rule_tac x = n in exI)
  apply (rule_tac x = "x ^ n r\<rightarrow> xb" in exI)
  apply clarify
  apply (subst inf_r_def [THEN sym])
  by simp

definition
  "cong H = (\<lambda> x y . cong_l H x y \<and> cong_r H x y)"

definition 
  "congruences = {R . equivp R \<and> (\<forall> a b c d . R a b \<and> R c d \<longrightarrow> R (a * c) (b * d) \<and>  R (a l\<rightarrow> c) (b l\<rightarrow> d) \<and>  R (a r\<rightarrow> c) (b r\<rightarrow> d))}"

lemma cong_l: "H \<in> normalfilters \<Longrightarrow> cong H = cong_l H"
  by (simp add: cong_def lemma_3_10_i_iii)
  
lemma cong_r: "H \<in> normalfilters \<Longrightarrow> cong H = cong_r H"
  by (simp add: cong_def lemma_3_10_i_iii)

lemma cong_equiv: "H \<in> normalfilters \<Longrightarrow> equivp (cong H)"
  apply (simp add: cong_l)
  apply (simp add: equivp_reflp_symp_transp reflp_def refl_on_def cong_l_reflexive cong_l_symmetric symp_def sym_def transp_def trans_def)
  apply safe
  apply (rule cong_l_transitive)
  by simp_all
   
lemma cong_trans: "H \<in> normalfilters \<Longrightarrow> cong H x y \<Longrightarrow> cong H y z \<Longrightarrow> cong H x z"
  apply (drule cong_equiv)
  apply (drule equivp_transp)
  by simp_all

lemma lemma_3_13 [simp]: 
  "H \<in> normalfilters \<Longrightarrow> cong H \<in> congruences"
  apply (subst congruences_def)
  apply safe
  apply (simp add: cong_equiv)
  apply (rule_tac y = "b * c" in cong_trans)
  apply simp_all
  apply (simp add: cong_r lemma_3_8_i)
  apply safe
  apply (rule_tac x = x in exI)
  apply simp
  apply (rule_tac x = y in exI)
  apply (simp add: mult.assoc [THEN sym])
  apply (simp add: cong_l lemma_3_8_ii)
  apply safe
  apply (rule_tac x = xa in exI)
  apply simp
  apply (rule_tac x = ya in exI)
  apply (simp add: mult.assoc)
  apply (rule_tac y = "a l\<rightarrow> d" in cong_trans)
  apply simp
  apply (simp add: cong_r cong_r_filter)
  apply safe
  apply (rule_tac a = "c l\<rightarrow> d" in filter_ii)
  apply simp_all
  apply (subst left_residual [THEN sym])
  apply (simp add: lemma_2_5_14)
  apply (rule_tac a = "d l\<rightarrow> c" in filter_ii)
  apply simp_all
  apply (subst left_residual [THEN sym])
  apply (simp add: lemma_2_5_14)
  apply (subst cong_l)
  apply simp
  apply (simp add: cong_r cong_r_filter cong_l_filter)
  apply safe
  apply (rule_tac a = "b l\<rightarrow> a" in filter_ii)
  apply simp_all
  apply (subst right_residual [THEN sym])
  apply (simp add: lemma_2_5_14)
  apply (rule_tac a = "a l\<rightarrow> b" in filter_ii)
  apply simp_all
  apply (subst right_residual [THEN sym])
  apply (simp add: lemma_2_5_14)

  apply (rule_tac y = "a r\<rightarrow> d" in cong_trans)
  apply simp
  apply (simp add: cong_l cong_l_filter)
  apply safe
  apply (rule_tac a = "c r\<rightarrow> d" in filter_ii)
  apply simp_all
  apply (subst right_residual [THEN sym])
  apply (simp add: lemma_2_5_15)
  apply (rule_tac a = "d r\<rightarrow> c" in filter_ii)
  apply simp_all
  apply (subst right_residual [THEN sym])
  apply (simp add: lemma_2_5_15)

  apply (subst cong_r)
  apply simp
  apply (simp add: cong_l cong_l_filter cong_r_filter)
  apply safe
  apply (rule_tac a = "b r\<rightarrow> a" in filter_ii)
  apply simp_all
  apply (subst left_residual [THEN sym])
  apply (simp add: lemma_2_5_15)
  apply (rule_tac a = "a r\<rightarrow> b" in filter_ii)
  apply simp_all
  apply (subst left_residual [THEN sym])
  by (simp add: lemma_2_5_15)

lemma cong_times: "R \<in> congruences \<Longrightarrow> R a b \<Longrightarrow> R c d \<Longrightarrow> R (a * c) (b * d)"
  by (simp add: congruences_def)

lemma cong_impl_l: "R \<in> congruences \<Longrightarrow> R a b \<Longrightarrow> R c d \<Longrightarrow> R (a l\<rightarrow> c) (b l\<rightarrow> d)"
  by (simp add: congruences_def)

lemma cong_impl_r: "R \<in> congruences \<Longrightarrow> R a b \<Longrightarrow> R c d \<Longrightarrow> R (a r\<rightarrow> c) (b r\<rightarrow> d)"
  by (simp add: congruences_def)

lemma cong_refl [simp]: "R \<in> congruences \<Longrightarrow> R a a"
  by (simp add: congruences_def equivp_reflp)

lemma cong_trans_a: "R \<in> congruences \<Longrightarrow> R a b \<Longrightarrow> R b c \<Longrightarrow> R a c"
  apply (simp add: congruences_def)
  apply (rule_tac y = b in equivp_transp)
  by simp_all

lemma cong_sym: "R \<in> congruences \<Longrightarrow> R a b \<Longrightarrow> R b a"
  by (simp add: congruences_def equivp_symp)

definition
  "normalfilter R = {a . R a 1}"

lemma lemma_3_14 [simp]:
  "R \<in> congruences \<Longrightarrow> (normalfilter R) \<in> normalfilters"
  apply (unfold normalfilters_def)
  apply safe
  apply (simp add: filters_def)
  apply safe
  apply (simp add: normalfilter_def)
  apply (drule_tac x = 1 in spec)
  apply (simp add: congruences_def  equivp_reflp)
  apply (simp add: normalfilter_def)
  apply (drule_tac a = a and c = b and b = 1 and d = 1 and R = R in cong_times)
  apply simp_all
  apply (simp add: normalfilter_def)
  apply (simp add: left_lesseq)
  apply (cut_tac R = R and a = a and b = 1 and c = b and d = b in cong_impl_l)
  apply simp_all
  apply (simp add: cong_sym)
  apply (simp_all add: normalfilter_def)
  apply (cut_tac R = R and a = "a l\<rightarrow> b" and b = 1 and c = a and d = a in cong_times)
  apply simp_all
  apply (simp add: inf_l_def [THEN sym])
  apply (cut_tac R = R and a = a and b = "a \<sqinter> b" and c = b and d = b in cong_impl_r)
  apply simp_all
  apply (simp add: cong_sym)
  apply (cut_tac R = R and c = "a r\<rightarrow> b" and d = 1 and a = a and b = a in cong_times)
  apply simp_all
  apply (simp add: inf_r_def [THEN sym])
  apply (cut_tac R = R and a = a and b = "a \<sqinter> b" and c = b and d = b in cong_impl_l)
  apply simp_all
  by (simp add: cong_sym)
 
lemma lemma_3_15_i:
  "H \<in> normalfilters \<Longrightarrow> normalfilter (cong H) = H"
  by (simp add: normalfilter_def cong_r cong_r_filter)

lemma lemma_3_15_ii:
  "R \<in> congruences \<Longrightarrow> cong (normalfilter R) = R"
  apply (simp add: fun_eq_iff cong_r cong_r_filter)
  apply (simp add: normalfilter_def)
  apply safe
  apply (cut_tac R = R and a = "x l\<rightarrow> xa" and b = 1 and c = x and d = x in cong_times)
  apply simp_all
  apply (cut_tac R = R and a = "xa l\<rightarrow> x" and b = 1 and c = xa and d = xa in cong_times)
  apply simp_all
  apply (simp add: inf_l_def [THEN sym])
  apply (rule_tac b = "x \<sqinter> xa" in cong_trans_a)
  apply simp_all
  apply (subst cong_sym)
  apply simp_all
  apply (subst inf.commute)
  apply simp_all
  apply (cut_tac R = R and a = x and b = xa and c = xa and d = xa in cong_impl_l)
  apply simp_all
  apply (cut_tac R = R and a = xa and b = xa and c = x and d = xa in cong_impl_l)
  by simp_all

lemma lemma_3_15_iii: "H1 \<in> normalfilters \<Longrightarrow> H2 \<in> normalfilters \<Longrightarrow> (H1 \<subseteq> H2) = (cong H1 \<le> cong H2)"
  apply safe
  apply (simp add: cong_l cong_l_filter)
  apply blast
  apply (subgoal_tac "cong H2 x 1")
  apply (simp add: cong_l cong_l_def)
  apply (subgoal_tac "cong H1 x 1")
  apply blast
  by (simp add: cong_l cong_l_def)

definition
  "p x y z = ((x l\<rightarrow> y) r\<rightarrow> z) \<sqinter> ((z l\<rightarrow> y) r\<rightarrow> x)"

lemma lemma_3_16_i: "p x x y = y \<and> p x y y = x"
  apply safe
  apply (simp_all add: p_def)
  apply (rule antisym)
  apply (simp_all add: lemma_2_10_24)
  apply (rule antisym)
  by (simp_all add: lemma_2_10_24)

definition "M x y z = ((y l\<rightarrow> x) r\<rightarrow> x) \<sqinter> ((z l\<rightarrow> y) r\<rightarrow> y) \<sqinter> ((x l\<rightarrow> z) r\<rightarrow> z)"

lemma "M x x y = x \<and> M x y x = x \<and> M y x x = x"
  apply (simp add: M_def)
  apply safe
  apply (rule antisym)
  apply (simp_all add: lemma_2_10_24 lemma_2_5_9_b) 
  apply (rule antisym)
  apply (simp_all add: lemma_2_10_24 lemma_2_5_9_b) 
  apply (rule antisym)
  by (simp_all add: lemma_2_10_24 lemma_2_5_9_b) 
end

end
