(* Title:      Relation Algebra
   Author:     Alasdair Armstrong, Simon Foster, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Tests\<close>

theory Relation_Algebra_Tests
  imports Relation_Algebra
begin

subsection \<open>Tests\<close>

text \<open>Tests or subidentities provide another way of modelling sets. Once more
we prove the basic properties, most of which stem from Maddux's book.\<close>

context relation_algebra
begin

definition is_test :: "'a \<Rightarrow> bool"
  where "is_test x \<equiv> x \<le> 1'"

lemma test_conv: "is_test x \<Longrightarrow> is_test (x\<^sup>\<smile>)"
by (metis conv_e conv_iso is_test_def)

lemma test_conv_var: "is_test x \<Longrightarrow> x\<^sup>\<smile> \<le> 1'"
by (metis test_conv is_test_def)

lemma test_eq_conv [simp]: "is_test x \<Longrightarrow> x\<^sup>\<smile> = x"
proof (rule antisym)
  assume hyp: "is_test x"
  hence "x \<le> x ; (1' \<cdot> x\<^sup>\<smile> ; 1')"
    by (metis inf.commute inf_absorb2 inf_le2 modular_1' mult.right_neutral is_test_def)
  thus "x \<le> x\<^sup>\<smile>"
    by (metis comp_unitr conv_contrav conv_invol eq_iff hyp inf_absorb2 mult_subdistl test_conv_var)
  thus "x\<^sup>\<smile> \<le> x"
    by (metis conv_invol conv_times le_iff_inf)
qed

lemma test_sum: "\<lbrakk>is_test x; is_test y\<rbrakk> \<Longrightarrow> is_test (x + y)"
by (simp add: is_test_def)

lemma test_prod: "\<lbrakk>is_test x; is_test y\<rbrakk> \<Longrightarrow> is_test (x \<cdot> y)"
by (metis le_infI2 is_test_def)

lemma test_comp: "\<lbrakk>is_test x; is_test y\<rbrakk> \<Longrightarrow> is_test (x ; y)"
by (metis mult_isol comp_unitr order_trans is_test_def)

lemma test_comp_eq_mult:
  assumes "is_test x"
    and "is_test y"
  shows "x ; y = x \<cdot> y"
proof (rule antisym)
  show "x ; y \<le> x \<cdot> y"
    by (metis assms comp_unitr inf_absorb2 le_inf_iff mult_onel mult_subdistl mult_subdistr is_test_def)
next
  have "x \<cdot> y \<le> x ; (1' \<cdot> x\<^sup>\<smile> ; y)"
    by (metis comp_unitr modular_1_var)
  thus "x \<cdot> y \<le> x ; y"
    by (metis assms(1) inf_absorb2 le_infI2 mult.left_neutral mult_isol mult_subdistr order_trans test_eq_conv is_test_def)
qed

lemma test_1 [simp]: "is_test x \<Longrightarrow> x ; 1 \<cdot> y = x ; y"
by (metis inf.commute inf.idem inf_absorb2 mult.left_neutral one_conv ra_1 test_comp_eq_mult test_eq_conv is_test_def)

lemma maddux_32 [simp]: "is_test x \<Longrightarrow> -(x ; 1) \<cdot> 1' = -x \<cdot> 1'"
proof (rule antisym)
  assume "is_test x"
  show "-(x ; 1) \<cdot> 1' \<le> -x \<cdot> 1'"
    by (metis maddux_20 comp_anti inf.commute meet_isor)
next
  assume "is_test x"
  have one: "x ; 1 \<cdot> (-x \<cdot> 1') \<le> x ; x\<^sup>\<smile> ; (-x \<cdot> 1')"
    by (metis maddux_16 inf_top_left mult.assoc)
  hence two: "x ; 1 \<cdot> (-x \<cdot> 1') \<le> -x"
    by (metis inf.commute inf_le1 le_infE)
  hence "x ; 1 \<cdot> (-x \<cdot> 1') \<le> x"
    by (metis one inf.commute le_infE meet_iso one_conv \<open>is_test x\<close> eq_iff test_1 test_eq_conv)
  hence "x ; 1 \<cdot> (-x \<cdot> 1') = 0"
    by (metis two galois_aux2 le_iff_inf)
  thus "-x \<cdot> 1' \<le> -(x ; 1) \<cdot> 1'"
    by (metis double_compl galois_aux2 inf.commute inf_le1 le_inf_iff)
qed

lemma test_distr_1 :
  assumes "is_test x"
    and "is_test y"
  shows "x ; z \<cdot> y ; z = (x \<cdot> y) ; z"
proof (rule antisym)
  have "x ; z \<cdot> y ; z \<le> x ; 1 \<cdot> y ; z"
    by (metis inf_top_left meet_iso mult_subdistl)
  also have "\<dots> = x ; y ; z"
    by (metis assms(1) mult.assoc test_1)
  finally show "x ; z \<cdot> y ; z \<le> (x \<cdot> y) ; z"
    by (metis assms test_comp_eq_mult)
next
  show "(x \<cdot> y) ; z \<le> x ; z \<cdot> y ; z"
    by (metis mult_subdistr_var)
qed

lemma maddux_35: "is_test x \<Longrightarrow> x ; y \<cdot> -z = x ; y \<cdot> -(x ; z)"
proof (rule antisym)
  assume "is_test x"
  show "x ; y \<cdot> -z \<le> x ; y \<cdot> -(x ; z)"
    by (metis \<open>is_test x\<close> comp_anti mult_isor mult_onel is_test_def inf.commute inf_le2 le_infI le_infI1)
  have one: "x ; y \<cdot> -(x ; z) \<le> x ; (y \<cdot> -z)"
    by (metis eq_iff le_infE maddux_23)
  hence two: "x ; y \<cdot> -(x ; z) \<le> x ; y"
    by (metis inf_le1)
  have "x ; y \<cdot> -(x ; z) \<le>  x ; -z"
    using one
    by (metis galois_1 le_iff_sup distrib_left sup_compl_top sup_top_right)
  hence "x ; y \<cdot> -(x ; z) \<le> -z"
    by (metis \<open>is_test x\<close> mult_isor mult_onel is_test_def order_trans)
  thus "x ; y \<cdot> -(x ; z) \<le> x ; y \<cdot> -z"
    using two
    by (metis le_inf_iff)
qed

subsection \<open>Test Complements\<close>

text \<open>Text complements are complements of elements that are ``pushed below''
the multiplicative unit.\<close>

definition tc :: "'a \<Rightarrow> 'a" 
  where "tc x = 1' \<cdot> -x"

lemma test_compl_1 [simp]: "is_test x \<Longrightarrow> x + tc x = 1'"
  by (metis is_test_def local.aux4 local.inf.absorb_iff1 local.inf_commute tc_def)

lemma test_compl_2 [simp]: "is_test x \<Longrightarrow> x \<cdot> tc x = 0"
  by (metis galois_aux inf.commute inf_le2 tc_def)

lemma test_test_compl: "is_test x \<Longrightarrow> is_test (tc x)"
  by (simp add: is_test_def tc_def)

lemma test_compl_de_morgan_1: "tc (x + y) = tc x \<cdot> tc y"
  by (metis compl_sup inf.left_commute inf.left_idem meet_assoc tc_def)

lemma test_compl_de_morgan_2: "tc (x \<cdot> y) = tc x + tc y"
  by (metis compl_inf inf_sup_distrib1 tc_def)

lemma test_compl_three [simp]: "tc (tc (tc x)) = tc x"
  by (metis aux4 aux6 de_morgan_3 inf.commute inf_sup_absorb tc_def)

lemma test_compl_double [simp]: "is_test x \<Longrightarrow> tc (tc x) = x"
  by (metis aux6_var compl_inf double_compl inf.commute le_iff_inf tc_def is_test_def)

end (* relation_algebra *)

end

