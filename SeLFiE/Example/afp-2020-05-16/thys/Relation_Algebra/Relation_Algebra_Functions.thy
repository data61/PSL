(* Title:      Relation Algebra
   Author:     Alasdair Armstrong, Simon Foster, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Functions\<close>

theory Relation_Algebra_Functions
  imports Relation_Algebra_Vectors Relation_Algebra_Tests
begin

subsection \<open>Functions\<close>

text \<open>This section collects the most important properties of functions. Most
of them can be found in the books by Maddux and by Schmidt and Str\"ohlein. The
main material is on partial and total functions, injections, surjections,
bijections.\<close>

(* Perhaps this material should be reorganised so that related theorems are
grouped together ... *)

context relation_algebra
begin

definition is_p_fun :: "'a \<Rightarrow> bool"
  where "is_p_fun x \<equiv> x\<^sup>\<smile> ; x \<le> 1'"

definition is_total :: "'a \<Rightarrow> bool"
  where "is_total x \<equiv> 1' \<le> x ; x\<^sup>\<smile>"

definition is_map :: "'a \<Rightarrow> bool"
  where "is_map x \<equiv> is_p_fun x \<and> is_total x"

definition is_inj :: "'a \<Rightarrow> bool"
  where "is_inj x \<equiv> x ; x\<^sup>\<smile> \<le> 1'"

definition is_sur :: "'a \<Rightarrow> bool"
  where "is_sur x \<equiv> 1' \<le> x\<^sup>\<smile> ; x"

text \<open>We distinguish between partial and total bijections. As usual we call
the latter just bijections.\<close>

definition is_p_bij :: "'a \<Rightarrow> bool"
  where "is_p_bij x \<equiv> is_p_fun x \<and> is_inj x \<and> is_sur x"

definition is_bij :: "'a \<Rightarrow> bool"
  where "is_bij x \<equiv> is_map x \<and> is_inj x \<and> is_sur x"

text \<open>Our first set of lemmas relates the various concepts.\<close>

lemma inj_p_fun: "is_inj x \<longleftrightarrow> is_p_fun (x\<^sup>\<smile>)"
by (metis conv_invol is_inj_def is_p_fun_def)

lemma p_fun_inj: "is_p_fun x \<longleftrightarrow> is_inj (x\<^sup>\<smile>)"
by (metis conv_invol inj_p_fun)

lemma sur_total: "is_sur x \<longleftrightarrow> is_total (x\<^sup>\<smile>)"
by (metis conv_invol is_sur_def is_total_def)

lemma total_sur: "is_total x \<longleftrightarrow> is_sur (x\<^sup>\<smile>)"
by (metis conv_invol sur_total)

lemma bij_conv: "is_bij x  \<longleftrightarrow> is_bij (x\<^sup>\<smile>)"
by (metis is_bij_def inj_p_fun is_map_def p_fun_inj sur_total total_sur)

text \<open>Next we show that tests are partial injections.\<close>

lemma test_is_inj_fun: "is_test x \<Longrightarrow> (is_p_fun x \<and> is_inj x)"
by (metis is_inj_def p_fun_inj test_comp test_eq_conv is_test_def)

text \<open>Next we show composition properties.\<close>

lemma p_fun_comp:
  assumes "is_p_fun x" and "is_p_fun y"
  shows "is_p_fun (x ; y)"
proof (unfold is_p_fun_def)
  have "(x ; y)\<^sup>\<smile> ; x ; y = y\<^sup>\<smile> ; x\<^sup>\<smile> ; x ; y"
    by (metis conv_contrav mult.assoc)
  also have "... \<le> y\<^sup>\<smile> ; y"
    by (metis assms(1) is_p_fun_def mult_double_iso mult.right_neutral mult.assoc)
  finally show "(x ; y)\<^sup>\<smile> ; (x ; y) \<le> 1'"
    by (metis assms(2) order_trans is_p_fun_def mult.assoc)
qed

lemma p_fun_mult_var: "x\<^sup>\<smile> ; x \<le> 1' \<Longrightarrow> (x \<cdot> y)\<^sup>\<smile> ; (x \<cdot> y) \<le> 1'"
by (metis conv_times inf_le1 mult_isol_var order_trans)

lemma inj_compose:
  assumes "is_inj x" and "is_inj y"
  shows "is_inj (x ; y)"
by (metis assms conv_contrav inj_p_fun p_fun_comp)

lemma inj_mult_var: "x\<^sup>\<smile> ; x \<le> 1' \<Longrightarrow> (x \<cdot> y)\<^sup>\<smile> ; (x \<cdot> y) \<le> 1'"
by (metis p_fun_mult_var)

lemma total_comp:
  assumes "is_total x" and "is_total y"
  shows "is_total (x ; y)"
by (metis assms inf_top_left le_iff_inf mult.assoc mult.right_neutral one_conv ra_2 is_total_def)

lemma total_add_var: "1' \<le> x\<^sup>\<smile> ; x  \<Longrightarrow> 1' \<le> (x + y)\<^sup>\<smile> ; (x + y)"
by (metis local.conv_add local.inf.absorb2 local.inf.coboundedI1 local.join_interchange local.le_sup_iff)

lemma sur_comp:
  assumes "is_sur x" and "is_sur y"
  shows "is_sur (x ; y)"
by (metis assms conv_contrav sur_total total_comp)

lemma sur_sum_var: "1' \<le> x\<^sup>\<smile> ; x \<Longrightarrow> 1' \<le> (x + y)\<^sup>\<smile> ; (x + y)"
by (metis total_add_var)

lemma map_comp:
  assumes "is_map x" and "is_map y"
  shows "is_map (x ; y)"
by (metis assms is_map_def p_fun_comp total_comp)

lemma bij_comp:
  assumes "is_bij x" and "is_bij y"
  shows "is_bij (x ; y)"
by (metis assms is_bij_def inj_compose map_comp sur_comp)

text \<open>We now show that (partial) functions, unlike relations, distribute over
meets from the left.\<close>

lemma p_fun_distl: "is_p_fun x \<Longrightarrow> x ; (y \<cdot> z) = x ; y \<cdot> x ; z"
proof -
  assume "is_p_fun x"
  hence "x ; (z \<cdot> ((x\<^sup>\<smile> ; x) ; y)) \<le> x ; (z \<cdot> y)"
    by (metis is_p_fun_def inf_le1 le_infI le_infI2 mult_isol mult_isor mult_onel)
  hence  "x ; y \<cdot> x ; z \<le> x ; (z \<cdot> y)"
    by (metis inf.commute mult.assoc order_trans modular_1_var)
  thus "x ; (y \<cdot> z) = x ; y \<cdot> x ; z"
    by (metis eq_iff inf.commute le_infI mult_subdistl)
qed

lemma map_distl: "is_map x \<Longrightarrow> x ; (y \<cdot> z) = x ; y \<cdot> x ; z"
by (metis is_map_def p_fun_distl)

text \<open>Next we prove simple properties of functions which arise in equivalent
definitions of those concepts.\<close>

lemma p_fun_zero: "is_p_fun x \<Longrightarrow> x ; y \<cdot> x ; -y = 0"
by (metis annir inf_compl_bot p_fun_distl)

lemma total_one: "is_total x \<Longrightarrow> x ; 1 = 1"
by (metis conv_invol conv_one inf_top_left le_iff_inf mult.right_neutral one_conv ra_2 is_total_def)

lemma total_1: "is_total x \<Longrightarrow> (\<forall>y. y ; x = 0 \<longrightarrow> y = 0)"
by (metis conv_invol conv_zero inf_bot_left inf_top_left peirce total_one)

lemma surj_one: "is_sur x \<Longrightarrow> 1 ; x = 1"
by (metis conv_contrav conv_invol conv_one sur_total total_one)

lemma surj_1: "is_sur x \<Longrightarrow> (\<forall>y. x ; y = 0 \<longrightarrow> y = 0)"
by (metis comp_res_aux compl_bot_eq conv_contrav conv_one inf.commute inf_top_right surj_one)

lemma bij_is_maprop:
  assumes "is_bij x" and "is_map x"
  shows "x\<^sup>\<smile> ; x  = 1' \<and> x ; x\<^sup>\<smile> = 1'"
by (metis assms is_bij_def eq_iff is_inj_def is_map_def is_p_fun_def is_sur_def is_total_def)

text\<open>We now provide alternative definitions for functions. These can be found
in Schmidt and Str\"ohlein's book.\<close>

lemma p_fun_def_var: "is_p_fun x \<longleftrightarrow> x ; -(1') \<le> -x"
by (metis conv_galois_1 double_compl galois_aux inf.commute is_p_fun_def)

lemma total_def_var_1: "is_total x \<longleftrightarrow> x ; 1 = 1"
by (metis inf_top_right le_iff_inf one_conv total_one is_total_def)

lemma total_def_var_2: "is_total x \<longleftrightarrow> -x \<le> x ; -(1')"
by (metis total_def_var_1 distrib_left sup_compl_top mult.right_neutral galois_aux3)

lemma sur_def_var1: "is_sur x \<longleftrightarrow> 1 ; x = 1"
by (metis conv_contrav conv_one sur_total surj_one total_def_var_1)

lemma sur_def_var2: "is_sur x \<longleftrightarrow> -x \<le> -(1') ; x"
by (metis sur_total total_def_var_2 conv_compl conv_contrav conv_e conv_iso)

lemma inj_def_var1: "is_inj x \<longleftrightarrow> -(1') ; x \<le> -x"
by (metis conv_galois_2 double_compl galois_aux inf.commute is_inj_def)

lemma is_maprop: "is_map x \<longleftrightarrow> x ; -(1') = -x"
by (metis eq_iff is_map_def p_fun_def_var total_def_var_2)

text \<open>Finally we prove miscellaneous properties of functions.\<close>

lemma ss_422iii: "is_p_fun y \<Longrightarrow> (x \<cdot> z ; y\<^sup>\<smile>) ; y = x ; y \<cdot> z"
(* by (smt antisym comp_assoc inf_commute maddux_17 meet_iso mult_isol mult_oner mult_subdistr_var order_trans is_p_fun_def) *)
proof (rule antisym)
  assume "is_p_fun y"
  show "x ; y \<cdot> z \<le> (x \<cdot> z ; y\<^sup>\<smile>) ; y"
    by (metis maddux_17)
  have "(x \<cdot> z ; y\<^sup>\<smile>) ; y \<le> x ; y \<cdot> (z ; (y\<^sup>\<smile> ; y))"
    by (metis mult_subdistr_var mult.assoc)
  also have "\<dots> \<le> x ; y \<cdot> z ; 1'"
    by (metis \<open>is_p_fun y\<close> inf_absorb2 inf_le1 le_infI le_infI2 mult_subdistl is_p_fun_def)
  finally show "(x \<cdot> z ; y\<^sup>\<smile>) ; y \<le> x ; y \<cdot> z"
    by (metis mult.right_neutral)
qed

lemma p_fun_compl: "is_p_fun x \<Longrightarrow> x ; -y \<le> -(x; y)"
by (metis annir galois_aux inf.commute inf_compl_bot p_fun_distl)

lemma ss_422v: "is_p_fun x \<Longrightarrow> x ; -y = x ; 1 \<cdot> -(x ; y)"
by (metis inf.commute inf_absorb2 inf_top_left maddux_23 p_fun_compl)

text \<open>The next property is a Galois connection.\<close>

lemma ss43iii: "is_map x \<longleftrightarrow> (\<forall>y. x ; -y = -(x ; y))"
by standard (metis inf_top_left is_map_def ss_422v total_one, metis is_maprop mult.right_neutral)

text \<open>Next we prove a lemma from Schmidt and Str\"ohlein's book and some of
its consequences. We show the proof in detail since the textbook proof uses
Tarski's rule which we omit.\<close>

lemma ss423: "is_map x \<Longrightarrow> y ; x \<le> z \<longleftrightarrow> y \<le> z ; x\<^sup>\<smile>"
proof
  assume "is_map x" and "y ; x \<le> z"
  hence "y \<le> y ; x ; x\<^sup>\<smile>"
    by (metis is_map_def mult_1_right mult.assoc mult_isol is_total_def)
  thus "y \<le> z ; x\<^sup>\<smile>"
    by (metis \<open>y ; x \<le> z\<close> mult_isor order_trans)
next
  assume "is_map x" and "y \<le> z ; x\<^sup>\<smile>"
  hence "y ; x \<le> z ; x\<^sup>\<smile> ; x"
    by (metis mult_isor)
  also have "\<dots> \<le> z ; 1'"
    by (metis \<open>is_map x\<close> is_map_def mult.assoc mult_isol is_p_fun_def)
  finally show "y ; x \<le> z"
    by (metis mult_1_right)
qed

lemma ss424i: "is_total x \<longleftrightarrow> (\<forall>y. -(x ; y) \<le> x ; -y)"
by (metis galois_aux3 distrib_left sup_compl_top total_def_var_1)

lemma ss434ii: "is_p_fun x \<longleftrightarrow> (\<forall>y. x ; -y \<le> -(x ; y))"
by (metis mult.right_neutral p_fun_compl p_fun_def_var)

lemma is_maprop1: "is_map x \<Longrightarrow> (y \<le> x ; z ; x\<^sup>\<smile> \<longleftrightarrow> y ; x \<le> x ; z)"
by (metis ss423)

lemma is_maprop2: "is_map x \<Longrightarrow> (y ; x \<le> x ; z \<longleftrightarrow> x\<^sup>\<smile> ; y; x \<le> z)"
by standard (metis galois_aux2 inf_commute mult.assoc schroeder_1 ss43iii, metis conv_contrav conv_invol conv_iso mult.assoc ss423)

lemma is_maprop3: "is_map x \<Longrightarrow> (x\<^sup>\<smile> ; y; x \<le> z \<longleftrightarrow> x\<^sup>\<smile> ; y \<le> z ; x\<^sup>\<smile>)"
by (metis ss423)

lemma p_fun_sur_id [simp]:
  assumes "is_p_fun x" and "is_sur x"
  shows "x\<^sup>\<smile> ; x = 1'"
by (metis assms eq_iff is_p_fun_def is_sur_def)

lemma total_inj_id [simp]:
  assumes "is_total x" and "is_inj x"
  shows "x ; x\<^sup>\<smile> = 1'"
by (metis assms conv_invol inj_p_fun p_fun_sur_id sur_total)

lemma bij_inv_1 [simp]: "is_bij x \<Longrightarrow> x ; x\<^sup>\<smile> = 1'"
by (metis bij_is_maprop is_bij_def)

lemma bij_inv_2 [simp]: "is_bij x \<Longrightarrow> x\<^sup>\<smile> ; x = 1'"
by (metis bij_is_maprop is_bij_def)

lemma bij_inv_comm: "is_bij x \<Longrightarrow> x ; x\<^sup>\<smile> = x\<^sup>\<smile> ; x"
by (metis bij_inv_1 bij_inv_2)

lemma is_bijrop: "is_bij x \<Longrightarrow> (y = x ; z \<longleftrightarrow> z = x\<^sup>\<smile> ; y)"
by (metis bij_inv_1 bij_inv_2 mult.assoc mult.left_neutral)

lemma inj_map_monomorph: "\<lbrakk>is_inj x; is_map x\<rbrakk> \<Longrightarrow> (\<forall>y z. y ; x = z ; x \<longrightarrow> y = z)"
by (metis is_map_def mult.assoc mult.right_neutral total_inj_id)

lemma sur_map_epimorph: "\<lbrakk>is_sur x; is_map x\<rbrakk> \<Longrightarrow> (\<forall>y z. x ; y = x ; z \<longrightarrow> y = z)"
by (metis eq_iff mult.assoc mult.left_neutral ss423 is_sur_def)

subsection \<open>Points and Rectangles\<close>

text \<open>Finally here is a section on points and rectangles. This is only a
beginning.\<close>

definition is_point :: "'a \<Rightarrow> bool"
  where "is_point x \<equiv> is_vector x \<and> is_inj x \<and> x \<noteq> 0"

definition is_rectangle :: "'a \<Rightarrow> bool"
  where "is_rectangle x \<equiv> x ; 1 ; x \<le> x"

lemma rectangle_eq [simp]: "is_rectangle x \<longleftrightarrow> x ; 1 ; x = x"
by (metis conv_one dedekind eq_iff inf_top_left mult.assoc one_idem_mult is_rectangle_def)

subsection \<open>Antidomain\<close>

text\<open>This section needs to be linked with domain semirings. We essentially
prove the antidomain semiring axioms. Then we have the abstract properties at
our disposition.\<close>

definition antidom :: "'a \<Rightarrow> 'a" ("a")
  where "a x = 1' \<cdot> (-(x ; 1))"

definition dom :: "'a \<Rightarrow> 'a" ("d")
  where "d x = a (a x)"

lemma antidom_test_comp [simp]: "a x = tc (x ; 1)"
by (metis antidom_def tc_def)

lemma dom_def_aux: "d x = 1' \<cdot> x ; 1"
by (metis antidom_test_comp dom_def double_compl inf_top_left mult.left_neutral one_compl ra_1 tc_def)

lemma dom_def_aux_var: "d x = 1' \<cdot> x ; x\<^sup>\<smile>"
by (metis dom_def_aux one_conv)

lemma antidom_dom [simp]: "a (d x) = a x"
by (metis antidom_test_comp dom_def_aux inf_top_left mult.left_neutral ra_1)

lemma dom_antidom [simp]: "d (a x) = a x"
by (metis antidom_dom dom_def)

lemma dom_verystrict: "d x = 0 \<longleftrightarrow> x = 0"
using dom_def_aux_var local.schroeder_2 by force

lemma a_1 [simp]: "a x ; x = 0"
by (metis antidom_test_comp galois_aux2 maddux_20 mult.left_neutral one_compl ra_1 tc_def)

lemma a_2: "a (x ; y) = a (x ; d y)"
by (metis antidom_test_comp dom_def_aux inf_top_left mult.assoc mult.left_neutral ra_1)

lemma a_3 [simp]: "a x + d x = 1'"
by (metis antidom_def aux4 dom_def_aux double_compl)

lemma test_domain: "x = d x \<longleftrightarrow> x \<le> 1'"
apply standard
 apply (metis dom_def_aux inf_le1)
apply (metis dom_def_aux inf.commute mult.right_neutral test_1 is_test_def)
done

text \<open>At this point we have all the necessary ingredients to prove that
relation algebras form Boolean domain semirings. However, we omit a formal
proof since we haven't formalized the latter.\<close>

lemma dom_one: "x ; 1 = d x ; 1"
by (metis dom_def_aux inf_top_left mult.left_neutral ra_1)

lemma test_dom: "is_test (d x)"
by (metis dom_def_aux inf_le1 is_test_def)

lemma p_fun_dom: "is_p_fun (d x)"
by (metis test_dom test_is_inj_fun)

lemma inj_dom: "is_inj (d x)"
by (metis test_dom test_is_inj_fun)

lemma total_alt_def: "is_total x \<longleftrightarrow> (d x) = 1'"
by (metis dom_def_aux_var le_iff_inf is_total_def)

end (* relation_algebra *)

end

