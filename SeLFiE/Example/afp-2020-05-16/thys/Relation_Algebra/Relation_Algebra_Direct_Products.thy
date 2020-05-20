(* Title:      Relation Algebra
   Author:     Alasdair Armstrong, Simon Foster, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Direct Products\<close>

theory Relation_Algebra_Direct_Products
  imports Relation_Algebra_Functions
begin

text \<open>This section uses the definition of direct products from Schmidt and
Str\"ohlein's book to prove the well known universal property.\<close>

context relation_algebra
begin

definition is_direct_product :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_direct_product x y \<equiv> x\<^sup>\<smile> ; x = 1' \<and> y\<^sup>\<smile> ; y = 1' \<and> x ; x\<^sup>\<smile> \<cdot> y ; y\<^sup>\<smile> = 1' \<and> x\<^sup>\<smile> ; y = 1"

text \<open>We collect some basic properties.\<close>

lemma dp_p_fun1: "is_direct_product x y \<Longrightarrow> is_p_fun x"
by (metis is_direct_product_def eq_refl is_p_fun_def)

lemma dp_sur1: "is_direct_product x y \<Longrightarrow> is_sur x"
by (metis is_direct_product_def eq_refl is_sur_def)

lemma dp_total1: "is_direct_product x y \<Longrightarrow> is_total x"
by (metis is_direct_product_def inf_le1 is_total_def)

lemma dp_map1: "is_direct_product x y \<Longrightarrow> is_map x"
by (metis dp_p_fun1 dp_total1 is_map_def)

lemma dp_p_fun2: "is_direct_product x y \<Longrightarrow> is_p_fun y"
by (metis is_direct_product_def eq_refl is_p_fun_def)

lemma dp_sur2: "is_direct_product x y \<Longrightarrow> is_sur y"
by (metis is_direct_product_def eq_refl is_sur_def)

lemma dp_total2: "is_direct_product x y \<Longrightarrow> is_total y"
by (metis is_direct_product_def inf_le2 is_total_def)

lemma dp_map2: "is_direct_product x y \<Longrightarrow> is_map y"
by (metis dp_p_fun2 dp_total2 is_map_def)

text \<open>Next we prove four auxiliary lemmas.\<close>

lemma dp_aux1 [simp]:
  assumes "is_p_fun z"
    and "is_total w"
    and "x\<^sup>\<smile> ; z = 1"
  shows "(w ; x\<^sup>\<smile> \<cdot> y ; z\<^sup>\<smile>) ; z = y"
by (metis assms inf_top_left mult.assoc ss_422iii total_one inf.commute inf_top_right)

lemma dp_aux2 [simp]:
  assumes "is_p_fun z"
    and "is_total w"
    and "z\<^sup>\<smile> ; x = 1"
  shows "(w ; x\<^sup>\<smile> \<cdot> y ; z\<^sup>\<smile>) ; z = y"
by (metis assms conv_contrav conv_invol conv_one inf_top_left mult.assoc ss_422iii total_one)

lemma dp_aux3 [simp]:
  assumes "is_p_fun z"
    and "is_total w"
    and "x\<^sup>\<smile> ; z = 1"
  shows "(y ; z\<^sup>\<smile> \<cdot> w ; x\<^sup>\<smile>) ; z = y"
by (metis assms dp_aux1 inf.commute)

lemma dp_aux4 [simp]:
  assumes "is_p_fun z"
    and "is_total w"
    and "z\<^sup>\<smile> ; x = 1"
  shows "( y ; z\<^sup>\<smile> \<cdot> w ; x\<^sup>\<smile>) ; z = y"
by (metis assms dp_aux2 inf.commute)

text \<open>Next we define a function which is an isomorphism on projections.\<close>

definition Phi :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<Phi>")
  where "\<Phi> \<equiv> (\<lambda>w x y z. w ; y\<^sup>\<smile> \<cdot> x ; z\<^sup>\<smile>)"

lemma Phi_conv: "(\<Phi> w x y z)\<^sup>\<smile> = y ; w\<^sup>\<smile> \<cdot> z ; x\<^sup>\<smile>"
by (simp add: Phi_def)

text \<open>We prove that @{const Phi} is an isomorphism with respect to the
projections.\<close>

lemma mono_dp_1:
  assumes "is_direct_product w x"
    and "is_direct_product y z"
  shows "\<Phi> w x y z ; y = w"
by (metis assms dp_aux4 is_direct_product_def dp_p_fun1 dp_total2 Phi_def)

lemma mono_dp_2:
  assumes "is_direct_product w x"
    and "is_direct_product y z"
  shows "\<Phi> w x y z ; z = x"
by (metis assms dp_aux1 is_direct_product_def dp_p_fun2 dp_total1 Phi_def)

text \<open>We now show that @{const Phi} is an injective function.\<close>

lemma Phi_map:
  assumes "is_direct_product w x"
    and "is_direct_product y z"
  shows "is_map (\<Phi> w x y z)"
proof -
  have "\<Phi> w x y z ; -(1') = \<Phi> w x y z ; -(y ; y\<^sup>\<smile> \<cdot> z ; z\<^sup>\<smile>)"
    by (metis assms(2) is_direct_product_def)
  also have "... = \<Phi> w x y z ; y ; -(y\<^sup>\<smile>) + \<Phi> w x y z ; z ; -(z\<^sup>\<smile>)"
   by (metis compl_inf assms(2) ss43iii dp_map1 dp_map2 mult.assoc distrib_left)
 also have "... = w ; -(y\<^sup>\<smile>) + x ; -(z\<^sup>\<smile>)"
   by (metis assms mono_dp_1 mono_dp_2)
 also have "... = -(w ; y\<^sup>\<smile>) + -(x ; z\<^sup>\<smile>)"
   by (metis assms(1) ss43iii dp_map1 dp_map2)
 also have "... = -(\<Phi> w x y z)"
   by (metis compl_inf Phi_def)
 finally show ?thesis
   by (metis is_maprop)
qed

lemma Phi_inj:
  assumes "is_direct_product w x"
    and "is_direct_product y z"
  shows "is_inj (\<Phi> w x y z)"
by (metis Phi_def Phi_conv Phi_map assms inj_p_fun is_map_def)

text \<open>Next we show that the converse of @{const Phi} is an injective
function.\<close>

lemma Phi_conv_map:
  assumes "is_direct_product w x"
    and "is_direct_product y z"
  shows "is_map ((\<Phi> w x y z)\<^sup>\<smile>)"
by (metis Phi_conv Phi_def Phi_map assms)

lemma Phi_conv_inj:
  assumes "is_direct_product w x"
    and "is_direct_product y z"
  shows "is_inj ((\<Phi> w x y z)\<^sup>\<smile>)"
by (metis Phi_inj Phi_conv Phi_def assms)

lemma Phi_sur:
  assumes "is_direct_product w x"
  and "is_direct_product y z"
  shows "is_sur (\<Phi> w x y z)"
by (metis assms Phi_conv Phi_def Phi_map is_map_def sur_total)

lemma Phi_conv_sur:
  assumes "is_direct_product w x"
    and "is_direct_product y z"
  shows "is_sur ((\<Phi> w x y z)\<^sup>\<smile>)"
by (metis assms Phi_conv Phi_def Phi_sur)

lemma Phi_bij:
  assumes "is_direct_product w x"
    and "is_direct_product y z"
  shows "is_bij (\<Phi> w x y z)"
by (metis assms Phi_inj Phi_map Phi_sur is_bij_def)

lemma Phi_conv_bij:
  assumes "is_direct_product w x"
    and "is_direct_product y z"
  shows "is_bij ((\<Phi> w x y z)\<^sup>\<smile>)"
by (metis Phi_bij Phi_def Phi_conv assms)

text \<open>Next we construct, for given functions~@{term f} and~@{term g}, a
function~@{term F} which makes the standard product diagram commute, and we
verify these commutation properties.\<close>

definition F :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "F \<equiv> (\<lambda>f x g y. f ; x\<^sup>\<smile> \<cdot> g ; y\<^sup>\<smile>)"

lemma f_proj:
  assumes "is_direct_product x y"
  and "is_map g"
  shows "F f x g y ; x = f"
by (metis assms dp_aux4 F_def is_map_def is_direct_product_def dp_p_fun1)

lemma g_proj:
  assumes "is_direct_product x y"
  and "is_map f"
  shows "F f x g y ; y = g"
by (metis assms dp_aux1 F_def is_map_def is_direct_product_def dp_p_fun2)

text \<open>Finally we show uniqueness of~@{const F}, hence universality of the
construction.\<close>

lemma
  assumes "is_direct_product x y"
  and "is_map f"
  and "is_map g"
  and "is_map G"
  and "f = G ; x"
  and "g = G ; y"
  shows "G = F f x g y"
proof -
  have "F f x g y = G ; (x ; x\<^sup>\<smile>) \<cdot> G ; (y ; y\<^sup>\<smile>)"
    by (metis assms(5) assms(6) F_def mult.assoc)
  also have "\<dots> = G ; (x ; x\<^sup>\<smile> \<cdot> y ; y\<^sup>\<smile>)"
    by (metis assms(4) map_distl)
  thus ?thesis
    by (metis assms(1) is_direct_product_def calculation mult.right_neutral)
qed

end (* relation_algebra *)

end

