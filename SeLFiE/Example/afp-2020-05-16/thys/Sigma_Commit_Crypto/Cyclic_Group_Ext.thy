theory Cyclic_Group_Ext imports 
  CryptHOL.CryptHOL
  "HOL-Number_Theory.Cong"
begin

context cyclic_group begin

lemma generator_pow_order: "\<^bold>g [^] order G = \<one>"
proof(cases "order G > 0")
  case True
  hence fin: "finite (carrier G)" by(simp add: order_gt_0_iff_finite)
  then have [symmetric]: "(\<lambda>x. x \<otimes> \<^bold>g) ` carrier G = carrier G"
    by(rule endo_inj_surj)(auto simp add: inj_on_multc)
  then have "carrier G = (\<lambda> n. \<^bold>g [^] Suc n) ` {..<order G}" using fin 
    by(simp add: carrier_conv_generator image_image)
  then obtain n where n: "\<one> = \<^bold>g [^] Suc n" "n < order G" by auto
  have "n = order G - 1" using n inj_onD[OF inj_on_generator, of 0 "Suc n"] by fastforce
  with True n show ?thesis by auto
qed simp

lemma generator_pow_mult_order: "\<^bold>g [^] (order G * order G) = \<one>"
  using generator_pow_order 
  by (metis generator_closed nat_pow_one nat_pow_pow)

lemma pow_generator_mod: "\<^bold>g [^] (k mod order G) = \<^bold>g [^] k"
proof(cases "order G > 0")
  case True
  obtain n where n: "k = n * order G + k mod order G" by (metis div_mult_mod_eq)
  have "\<^bold>g [^] k = (\<^bold>g [^] order G) [^] n \<otimes> \<^bold>g [^] (k mod order G)" 
    by(subst n)(simp add: nat_pow_mult nat_pow_pow mult_ac)
  then show ?thesis by(simp add: generator_pow_order)
qed simp

lemma pow_carrier_mod: 
  assumes "g \<in> carrier G"
  shows "g [^] (k mod order G) = g [^] k"
  using assms pow_generator_mod 
  by (metis generatorE generator_closed mod_mult_right_eq nat_pow_pow)

lemma pow_generator_mod_int: "\<^bold>g [^] ((k::int) mod order G) = \<^bold>g [^] k"
proof(cases "order G > 0")
  case True
  obtain n :: int where n: "k = n * order G + k mod order G"   
    by (metis div_mult_mod_eq)
  have "\<^bold>g [^] k = (\<^bold>g [^] order G) [^] n \<otimes> \<^bold>g [^] (k mod order G)" 
    apply(subst n)apply(simp add: int_pow_mult int_pow_pow mult_ac)
    by (metis generator_closed int_pow_int int_pow_pow mult.commute)
  then show ?thesis by(simp add: generator_pow_order)
qed simp

lemma pow_generator_eq_iff_cong:
  "finite (carrier G) \<Longrightarrow> \<^bold>g [^] x = \<^bold>g [^] y \<longleftrightarrow> [x = y] (mod order G)"
  apply(subst (1 2) pow_generator_mod[symmetric])
  by(auto simp add: cong_def order_gt_0_iff_finite intro: inj_onD[OF inj_on_generator])

lemma power_distrib: 
  assumes "h \<in> carrier G" 
  shows "\<^bold>g [^] (e :: nat) \<otimes> h [^] e = (\<^bold>g \<otimes> h ) [^] e"
(is "?lhs = ?rhs")
proof-
  obtain x :: nat where x: "h = \<^bold>g [^] x" 
    using assms generatorE by blast
  hence "?lhs = \<^bold>g [^] (e * (1 + x))" 
    by (simp add: nat_pow_mult mult.commute nat_pow_pow)
  also have "... = (\<^bold>g [^] (1 + x)) [^] e" 
    by (metis generator_closed mult.commute nat_pow_pow)
  ultimately show ?thesis 
    by (metis x One_nat_def generator_closed l_one monoid.nat_pow_Suc monoid_axioms nat_pow_0 nat_pow_mult)
qed

lemma neg_power_inverse:
  assumes "g \<in> carrier G" 
    and "x < order G"
  shows "g [^] (order G - (x :: nat)) = inv (g [^] x)"
proof-
  have "inv (g [^] x) = g [^] (- int x)"  
    by (simp add: int_pow_int int_pow_neg assms)
  moreover have "g [^] (order G - (x :: nat)) = g [^] (- int x)"
  proof-
    have "g [^] ((order G - (x :: nat)) mod (order G)) = g [^] ((- int x) mod (order G))" 
    proof-
      have "(order G - (x :: nat)) mod (order G) = (- int x) mod (order G)" 
        using assms(2) zmod_zminus1_eq_if by auto
      thus ?thesis 
        by (metis int_pow_int)
    qed
    thus ?thesis 
    proof -
      have f1: "\<forall>a. a [^] int 0 = \<one>"
        by simp
      have f2: "\<forall>n na. ((na::nat) + n) mod na = n mod na"
        by simp
        have f3: "\<forall>a aa. aa \<otimes> a [^] int 0 = aa \<or> aa \<notin> carrier G"
          by force
        have f4: "\<forall>i a aa. a [^] int 0 \<otimes> aa [^] i = aa [^] (int 0 + i) \<or> aa \<notin> carrier G"
          by force
        have "\<forall>n a. a [^] int (n * 0) = a [^] (int 0 + int 0) \<or> a \<notin> carrier G"
          by simp
        then have f5: "\<forall>a aa. aa [^] int (order G) = a [^] int 0 \<or> aa \<notin> carrier G"
          using f4 f3 f2 f1 by (metis int_pow_closed int_pow_int mod_mult_self2 pow_carrier_mod)
        have "\<forall>n na. int (n - na) = - int na + int n \<or> \<not> na \<le> n"
          by auto
        then show ?thesis
          using f5 f3 by (metis assms(1) assms(2) int_pow_closed int_pow_int int_pow_mult less_imp_le_nat)
      qed
    qed
  ultimately show ?thesis by simp
qed

lemma int_nat_pow: assumes "a \<ge> 0" shows "(\<^bold>g [^] (int (a ::nat))) [^] (b::int)  = \<^bold>g [^] (a*b)"
  using assms 
proof(cases "a >0")
  case True 
  show ?thesis
    using int_pow_pow by blast
next case False
  have "(\<^bold>g [^] (int (a ::nat))) [^] (b::int) = \<one>" using False by simp
  also have "\<^bold>g [^] (a*b) = \<one>" using False by simp
  ultimately show ?thesis by simp
qed

lemma pow_gen_mod_mult:
  shows"(\<^bold>g [^] (a::nat) \<otimes> \<^bold>g [^] (b::nat)) [^] ((c::int)*int (d::nat)) = (\<^bold>g [^] a \<otimes> \<^bold>g [^] b) [^] ((c*int d) mod (order G))"
proof-
  have "(\<^bold>g [^] (a::nat) \<otimes> \<^bold>g [^] (b::nat)) \<in> carrier G" by simp
  then obtain n :: nat where n: "\<^bold>g [^] n = (\<^bold>g [^] (a::nat) \<otimes> \<^bold>g [^] (b::nat))" 
    by (simp add: monoid.nat_pow_mult)
  also obtain r where r: "r = c*int d" by simp
  have 1: "(\<^bold>g [^] (a::nat) \<otimes> \<^bold>g [^] (b::nat)) [^] ((c::int)*int (d::nat)) = (\<^bold>g [^] n) [^] r" using n r by simp
  also have 2:"... = (\<^bold>g [^] n) [^] (r mod (order G))" using pow_generator_mod_int pow_generator_mod 
    by (metis int_nat_pow int_pow_int mod_mult_right_eq zero_le)
  also have 3:"... =  (\<^bold>g [^] a \<otimes> \<^bold>g [^] b) [^] ((c*int d) mod (order G))" using r n by simp
  ultimately show ?thesis using 1 2 3 by simp
qed

lemma cyclic_group_commute: assumes "a \<in> carrier G" "b \<in> carrier G" shows "a \<otimes> b = b \<otimes> a"
(is "?lhs = ?rhs")
proof-
  obtain n :: nat where n: "a = \<^bold>g [^] n" using generatorE assms by auto
  also  obtain k :: nat where k: "b = \<^bold>g [^] k" using generatorE assms by auto
  ultimately have "?lhs =  \<^bold>g [^] n \<otimes> \<^bold>g [^] k" by simp
  then have "... = \<^bold>g [^] (n + k)" by(simp add: nat_pow_mult)
  then have "... = \<^bold>g [^] (k + n)" by(simp add: add.commute)
  then show ?thesis by(simp add: nat_pow_mult n k)
qed

lemma cyclic_group_assoc: 
  assumes "a \<in> carrier G" "b \<in> carrier G" "c \<in> carrier G"
  shows "(a \<otimes> b) \<otimes> c = a \<otimes> (b \<otimes> c)"
(is "?lhs = ?rhs")
proof-
  obtain n :: nat where n: "a = \<^bold>g [^] n" using generatorE assms by auto
  obtain k :: nat where k: "b = \<^bold>g [^] k" using generatorE assms by auto
  obtain j :: nat where j: "c = \<^bold>g [^] j" using generatorE assms by auto 
  have "?lhs = (\<^bold>g [^] n \<otimes> \<^bold>g [^] k) \<otimes> \<^bold>g [^] j" using n k j by simp
  then have "... = \<^bold>g [^] (n + (k + j))" by(simp add: nat_pow_mult add.assoc)
  then show ?thesis by(simp add: nat_pow_mult n k j)
qed
 
lemma l_cancel_inv: 
  assumes "h \<in> carrier G" 
  shows "(\<^bold>g [^] (a :: nat) \<otimes> inv (\<^bold>g [^] a)) \<otimes> h = h"
(is "?lhs = ?rhs")
proof-
  have "?lhs = (\<^bold>g [^] int a \<otimes> inv (\<^bold>g [^] int a)) \<otimes> h" by simp
  then have "... = (\<^bold>g [^] int a \<otimes> (\<^bold>g [^] (- a))) \<otimes> h" using int_pow_neg[symmetric] by simp
  then have "... = \<^bold>g [^] (int a - a)  \<otimes> h" by(simp add: int_pow_mult)
  then have "... = \<^bold>g [^] ((0:: int)) \<otimes> h" by simp
  then show ?thesis by (simp add: assms)
qed

lemma inverse_split: 
  assumes "a \<in> carrier G" and "b \<in> carrier G"
  shows "inv (a \<otimes> b) = inv a \<otimes> inv b"
  by (simp add:  assms comm_group.inv_mult cyclic_group_commute group_comm_groupI)

lemma inverse_pow_pow:
  assumes "a \<in> carrier G"
  shows "inv (a [^] (r::nat)) = (inv a) [^] r"
proof -
  have "a [^] r \<in> carrier G"
    using assms by blast
  then show ?thesis
    by (simp add: assms nat_pow_inv)
qed

lemma l_neq_1_exp_neq_0:
  assumes "l \<in> carrier G" 
    and "l \<noteq> \<one>" 
    and "l = \<^bold>g [^] (t::nat)" 
  shows "t \<noteq> 0"
proof(rule ccontr)
  assume "\<not> (t \<noteq> 0)"
  hence "t = 0" by simp
  hence "\<^bold>g [^] t = \<one>" by simp
  then show "False" using assms by simp
qed

lemma order_gt_1_gen_not_1:
  assumes "order G > 1"
  shows "\<^bold>g \<noteq> \<one>"
proof(rule ccontr)
  assume "\<not> \<^bold>g \<noteq> \<one>"
  hence "\<^bold>g = \<one>" by simp
  hence g_pow_eq_1: "\<^bold>g [^] n = \<one>" for n :: nat by simp
  hence "range (\<lambda>n :: nat. \<^bold>g [^] n) = {\<one>}" by auto
  hence "carrier G \<subseteq> {\<one>}" using generator by auto
  hence "order G < 1" 
    by (metis inj_onD inj_on_generator lessThan_iff g_pow_eq_1 assms less_one neq0_conv)
  with assms show "False" by simp
qed

lemma power_swap: "((\<^bold>g [^] (\<alpha>0::nat)) [^] (r::nat)) = ((\<^bold>g [^] r) [^] \<alpha>0)"
(is "?lhs = ?rhs")
proof-
  have "?lhs = \<^bold>g [^] (\<alpha>0 * r)" using nat_pow_pow mult.commute by auto
  hence "... = \<^bold>g [^] (r * \<alpha>0)" by(metis mult.commute)
  thus ?thesis using nat_pow_pow by auto
qed

lemma gen_power_0:
  fixes r :: nat 
  assumes "\<^bold>g [^] r = \<one>" 
    and "r < order G"
  shows "r = 0" 
  using assms inj_onD inj_on_generator by fastforce

lemma group_eq_pow_eq_mod: 
  fixes a b :: nat 
  assumes "\<^bold>g [^] a = \<^bold>g [^] b" 
    and "order G > 0"
  shows "[a = b] (mod order G)"
proof(cases "a > b")
  case True
  have "\<^bold>g [^] a \<otimes> inv (\<^bold>g [^] b) = \<one>"
    using assms by simp
  hence "\<^bold>g [^] (a - b) = \<one>" 
    by (smt True add_Suc_right assms diff_add_inverse generator_closed group.l_cancel_one' group_l_invI l_inv_ex less_imp_Suc_add nat_pow_closed nat_pow_mult)
  hence "\<^bold>g [^] ((a - b) mod (order G)) = \<one>" using pow_generator_mod by auto
  thus ?thesis using gen_power_0 
    using assms(1) assms(2) order_gt_0_iff_finite pow_generator_eq_iff_cong by blast
next
  case False
  have "\<^bold>g [^] a \<otimes> inv (\<^bold>g [^] b) = \<one>"
    using assms by simp
  hence "\<^bold>g [^] (b - a) = \<one>" 
    by (metis (no_types, lifting) False Group.group.axioms(1) Units_eq add_diff_inverse_nat assms(1) generator_closed group_l_invI l_inv_ex l_neq_1_exp_neq_0 monoid.Units_l_cancel nat_pow_closed nat_pow_mult r_one)
  hence "\<^bold>g [^] ((b - a) mod (order G)) = \<one>" using pow_generator_mod by simp
  thus ?thesis using gen_power_0 
    using assms(1) assms(2) order_gt_0_iff_finite pow_generator_eq_iff_cong by blast
qed


end 

end
