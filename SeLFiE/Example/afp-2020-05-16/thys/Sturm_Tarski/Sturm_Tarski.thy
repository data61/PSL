(*  Title: Sturm-Tarski Theorem
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section "Sturm-Tarski Theorem"

theory Sturm_Tarski
  imports Complex_Main PolyMisc "HOL-Computational_Algebra.Field_as_Ring"
begin

section\<open>Misc\<close>

lemma eventually_at_right:
  fixes x::"'a::{archimedean_field,linorder_topology}"
  shows "eventually P (at_right x) \<longleftrightarrow> (\<exists>b>x. \<forall>y>x. y < b \<longrightarrow> P y)"
proof -
  obtain y where "y>x" using ex_less_of_int by auto  
  thus ?thesis using eventually_at_right[OF \<open>y>x\<close>] by auto
qed

lemma eventually_at_left:
  fixes x::"'a::{archimedean_field,linorder_topology}"
  shows "eventually P (at_left x) \<longleftrightarrow> (\<exists>b<x. \<forall>y>b. y < x \<longrightarrow> P y)"
proof -
  obtain y where "y<x" 
    using linordered_field_no_lb by auto
  thus ?thesis using eventually_at_left[OF \<open>y<x\<close>] by auto
qed

lemma eventually_neg:
  assumes "F\<noteq>bot"  and eve:"eventually (\<lambda>x. P x) F"
  shows "\<not> eventually (\<lambda>x. \<not> P x) F"
proof (rule ccontr)
  assume "\<not> \<not> eventually (\<lambda>x. \<not> P x) F"
  hence "eventually (\<lambda>x. \<not> P x) F" by auto
  hence "eventually (\<lambda>x. False) F" using eventually_conj[OF eve,of "(\<lambda>x. \<not> P x)"] by auto
  thus False using \<open>F\<noteq>bot\<close> eventually_False by auto 
qed

lemma poly_tendsto[simp]:
    "(poly p \<longlongrightarrow> poly p x) (at (x::real))" 
    "(poly p \<longlongrightarrow> poly p x) (at_left (x::real))"
    "(poly p \<longlongrightarrow> poly p x) (at_right (x::real))"
  using isCont_def[where f="poly p"] by (auto simp add:filterlim_at_split)

lemma not_eq_pos_or_neg_iff_1:
  fixes p::"real poly" 
  shows "(\<forall>z. lb<z\<and>z\<le>ub\<longrightarrow>poly p z\<noteq>0) \<longleftrightarrow> 
    (\<forall>z. lb<z\<and>z\<le>ub\<longrightarrow>poly p z>0)\<or>(\<forall>z. lb<z\<and>z\<le>ub\<longrightarrow>poly p z<0)" (is "?Q \<longleftrightarrow> ?P")
proof (rule,rule ccontr)
  assume "?Q" "\<not>?P" 
  then obtain z1 z2 where z1:"lb<z1" "z1\<le>ub" "poly p z1\<le>0" 
                      and z2:"lb<z2" "z2\<le>ub" "poly p z2\<ge>0"
    by auto
  hence "\<exists>z. lb<z\<and>z\<le>ub\<and>poly p z=0"
  proof (cases "poly p z1 = 0 \<or> poly p z2 =0 \<or> z1=z2")
    case True
    thus ?thesis using z1 z2 by auto
  next
    case False
    hence "poly p z1<0" and "poly p z2>0" and "z1\<noteq>z2" using z1(3) z2(3) by auto
    hence "(\<exists>z>z1. z < z2 \<and> poly p z = 0) \<or> (\<exists>z>z2. z < z1 \<and> poly p z = 0)"
      using poly_IVT_neg poly_IVT_pos by (subst (asm) linorder_class.neq_iff,auto) 
    thus ?thesis using z1(1,2) z2(1,2) by (metis less_eq_real_def order.strict_trans2)
  qed
  thus False using \<open>?Q\<close> by auto
next
  assume "?P"
  thus ?Q by auto
qed

lemma not_eq_pos_or_neg_iff_2:
  fixes p::"real poly" 
  shows "(\<forall>z. lb\<le>z\<and>z<ub\<longrightarrow>poly p z\<noteq>0) 
    \<longleftrightarrow>(\<forall>z. lb\<le>z\<and>z<ub\<longrightarrow>poly p z>0)\<or>(\<forall>z. lb\<le>z\<and>z<ub\<longrightarrow>poly p z<0)" (is "?Q\<longleftrightarrow>?P")
proof (rule,rule ccontr)
  assume "?Q" "\<not>?P"
  then obtain z1 z2 where z1:"lb\<le>z1" "z1<ub" "poly p z1\<le>0" 
                      and z2:"lb\<le>z2" "z2<ub" "poly p z2\<ge>0"
    by auto
  hence "\<exists>z. lb\<le>z\<and>z<ub\<and>poly p z=0"
  proof (cases "poly p z1 = 0 \<or> poly p z2 =0 \<or> z1=z2")
    case True
    thus ?thesis using z1 z2 by auto
  next
    case False
    hence "poly p z1<0" and "poly p z2>0" and "z1\<noteq>z2" using z1(3) z2(3) by auto
    hence "(\<exists>z>z1. z < z2 \<and> poly p z = 0) \<or> (\<exists>z>z2. z < z1 \<and> poly p z = 0)"
      using poly_IVT_neg poly_IVT_pos by (subst (asm) linorder_class.neq_iff,auto) 
    thus ?thesis using z1(1,2) z2(1,2) by (meson dual_order.strict_trans not_le)
  qed
  thus False using \<open>?Q\<close> by auto
next
  assume "?P"
  thus ?Q by auto
qed

lemma next_non_root_interval:
  fixes p::"real poly"
  assumes "p\<noteq>0"
  obtains ub where "ub>lb" and "(\<forall>z. lb<z\<and>z\<le>ub\<longrightarrow>poly p z\<noteq>0)" 
proof (cases "(\<exists> r. poly p r=0 \<and> r>lb)")
  case False
  thus ?thesis by (intro that[of "lb+1"],auto)
next
  case True
  define lr where "lr\<equiv>Min {r . poly p r=0 \<and> r>lb}" 
  have "\<forall>z. lb<z\<and>z<lr\<longrightarrow>poly p z\<noteq>0" and "lr>lb" 
    using True lr_def poly_roots_finite[OF \<open>p\<noteq>0\<close>] by auto
  thus ?thesis using that[of "(lb+lr)/2"] by auto 
qed

lemma last_non_root_interval:
  fixes p::"real poly"
  assumes "p\<noteq>0"
  obtains lb where "lb<ub" and "(\<forall>z. lb\<le>z\<and>z<ub\<longrightarrow>poly p z\<noteq>0)"
proof (cases "(\<exists> r. poly p r=0 \<and> r<ub)")
  case False
  thus ?thesis by (intro that[of "ub - 1"]) auto
next
  case True
  define mr where  "mr\<equiv>Max {r . poly p r=0 \<and> r<ub}" 
  have "\<forall>z. mr<z\<and>z<ub\<longrightarrow>poly p z\<noteq>0" and "mr<ub" 
    using True mr_def poly_roots_finite[OF \<open>p\<noteq>0\<close>] by auto
  thus ?thesis using that[of "(mr+ub)/2"] \<open>mr<ub\<close> by auto
qed

section\<open>Bound of polynomials\<close>

definition sgn_pos_inf :: "('a ::linordered_idom) poly \<Rightarrow> 'a" where 
  "sgn_pos_inf p \<equiv> sgn (lead_coeff p)"
definition sgn_neg_inf :: "('a ::linordered_idom) poly \<Rightarrow> 'a" where 
  "sgn_neg_inf p \<equiv> if even (degree p) then sgn (lead_coeff p) else -sgn (lead_coeff p)"

lemma sgn_inf_sym:
  fixes p::"real poly"
  shows "sgn_pos_inf (pcompose p [:0,-1:]) = sgn_neg_inf p" (is "?L=?R")
proof -
  have "?L= sgn (lead_coeff p * (- 1) ^ degree p)" 
    unfolding sgn_pos_inf_def by (subst lead_coeff_comp,auto)
  thus ?thesis unfolding sgn_neg_inf_def 
    by (metis mult.right_neutral mult_minus1_right neg_one_even_power neg_one_odd_power sgn_minus)
qed

lemma poly_pinfty_gt_lc:
  fixes p:: "real poly"
  assumes  "lead_coeff p > 0" 
  shows "\<exists> n. \<forall> x \<ge> n. poly p x \<ge> lead_coeff p" using assms
proof (induct p)
  case 0
  thus ?case by auto
next
  case (pCons a p)
  have "\<lbrakk>a\<noteq>0;p=0\<rbrakk> \<Longrightarrow> ?case" by auto
  moreover have "p\<noteq>0 \<Longrightarrow> ?case"
  proof -
    assume "p\<noteq>0"
    then obtain n1 where gte_lcoeff:"\<forall>x\<ge>n1. lead_coeff p \<le> poly p x" using that pCons by auto
    have gt_0:"lead_coeff p >0" using pCons(3) \<open>p\<noteq>0\<close> by auto
    define n where "n\<equiv>max n1 (1+ \<bar>a\<bar>/(lead_coeff p))"
    show ?thesis 
    proof (rule_tac x=n in exI,rule,rule) 
      fix x assume "n \<le> x"
      hence "lead_coeff p \<le> poly p x" 
        using gte_lcoeff unfolding n_def by auto
      hence " \<bar>a\<bar>/(lead_coeff p) \<ge> \<bar>a\<bar>/(poly p x)" and "poly p x>0" using gt_0
        by (intro frac_le,auto)
      hence "x\<ge>1+ \<bar>a\<bar>/(poly p x)" using \<open>n\<le>x\<close>[unfolded n_def] by auto
      thus "lead_coeff (pCons a p) \<le> poly (pCons a p) x"
        using \<open>lead_coeff p \<le> poly p x\<close> \<open>poly p x>0\<close> \<open>p\<noteq>0\<close>
        by (auto simp add:field_simps)
      qed
    qed
  ultimately show ?case by fastforce
qed

lemma poly_sgn_eventually_at_top:
  fixes p::"real poly"
  shows "eventually (\<lambda>x. sgn (poly p x) = sgn_pos_inf p) at_top"
proof (cases "p=0")
  case True
  thus ?thesis unfolding sgn_pos_inf_def by auto
next
  case False
  obtain ub where ub:"\<forall>x\<ge>ub. sgn (poly p x) = sgn_pos_inf p"
  proof (cases "lead_coeff p>0")
    case True
    thus ?thesis 
      using that poly_pinfty_gt_lc[of p] unfolding sgn_pos_inf_def by fastforce 
  next
    case False
    hence "lead_coeff (-p) > 0" and "lead_coeff p < 0" unfolding lead_coeff_minus
      using leading_coeff_neq_0[OF \<open>p\<noteq>0\<close>] 
      by (auto simp add:not_less_iff_gr_or_eq)
    then obtain n where "\<forall>x\<ge>n. lead_coeff p \<ge> poly p x"
      using poly_pinfty_gt_lc[of "-p"] unfolding lead_coeff_minus by auto
    thus ?thesis using \<open>lead_coeff p<0\<close> that[of n] unfolding sgn_pos_inf_def by fastforce
  qed
  thus ?thesis unfolding eventually_at_top_linorder by auto
qed

lemma poly_sgn_eventually_at_bot:
  fixes p::"real poly"
  shows "eventually (\<lambda>x. sgn (poly p x) = sgn_neg_inf p) at_bot"
using 
  poly_sgn_eventually_at_top[of "pcompose p [:0,-1:]",unfolded poly_pcompose sgn_inf_sym,simplified]
  eventually_filtermap[of _ uminus "at_bot::real filter",folded at_top_mirror]
by auto
   
lemma root_ub:
  fixes p:: "real poly"
  assumes "p\<noteq>0"
  obtains ub where "\<forall>x. poly p x=0 \<longrightarrow> x<ub"
    and "\<forall>x\<ge>ub. sgn (poly p x) = sgn_pos_inf p"
proof -
  obtain ub1 where ub1:"\<forall>x. poly p x=0 \<longrightarrow> x<ub1"
  proof (cases "\<exists> r. poly p r=0")
    case False
    thus ?thesis using that by auto
  next
    case True
    define max_r where "max_r\<equiv>Max {x . poly p x=0}"
    hence "\<forall>x. poly p x=0 \<longrightarrow> x\<le>max_r"
      using  poly_roots_finite[OF \<open>p\<noteq>0\<close>] True by auto
    thus ?thesis using that[of "max_r+1"] 
      by (metis add.commute add_strict_increasing zero_less_one)
  qed
  obtain ub2 where ub2:"\<forall>x\<ge>ub2. sgn (poly p x) = sgn_pos_inf p"
    using poly_sgn_eventually_at_top[unfolded eventually_at_top_linorder] by auto
  define ub where "ub\<equiv>max ub1 ub2"
  have "\<forall>x. poly p x=0 \<longrightarrow> x<ub" using ub1 ub_def 
    by (metis eq_iff less_eq_real_def less_linear max.bounded_iff)
  thus ?thesis using that[of ub] ub2 ub_def by auto
qed

lemma root_lb:
  fixes p:: "real poly"
  assumes "p\<noteq>0"
  obtains lb where "\<forall>x. poly p x=0 \<longrightarrow> x>lb"
    and "\<forall>x\<le>lb. sgn (poly p x) = sgn_neg_inf p"
proof -
  obtain lb1 where lb1:"\<forall>x. poly p x=0 \<longrightarrow> x>lb1"
  proof (cases "\<exists> r. poly p r=0")
    case False
    thus ?thesis using that by auto
  next
    case True
    define min_r where "min_r\<equiv>Min {x . poly p x=0}"
    hence "\<forall>x. poly p x=0 \<longrightarrow> x\<ge>min_r"
      using  poly_roots_finite[OF \<open>p\<noteq>0\<close>] True by auto
    thus ?thesis using that[of "min_r - 1"] by (metis lt_ex order.strict_trans2 that) 
  qed
  obtain lb2 where lb2:"\<forall>x\<le>lb2. sgn (poly p x) = sgn_neg_inf p"
    using poly_sgn_eventually_at_bot[unfolded eventually_at_bot_linorder] by auto
  define lb where  "lb\<equiv>min lb1 lb2"
  have "\<forall>x. poly p x=0 \<longrightarrow> x>lb" using lb1 lb_def 
    by (metis (poly_guards_query) less_not_sym min_less_iff_conj neq_iff)
  thus ?thesis using that[of lb] lb2 lb_def by auto
qed

section\<open>Sign\<close>

definition sign:: "'a::{zero,linorder} \<Rightarrow> int" where
  "sign x\<equiv>(if x>0 then 1 else if x=0 then 0 else -1)"

lemma sign_simps[simp]:
  "x>0 \<Longrightarrow> sign x=1"
  "x=0 \<Longrightarrow> sign x=0"
  "x<0 \<Longrightarrow> sign x=-1"
unfolding sign_def by auto

lemma sign_cases [case_names neg zero pos]:
  "(sign x = -1 \<Longrightarrow> P) \<Longrightarrow> (sign x = 0 \<Longrightarrow> P) \<Longrightarrow> (sign x =1 \<Longrightarrow> P) \<Longrightarrow> P"  
unfolding Sturm_Tarski.sign_def by argo   

lemma sign_times:
  fixes x::"'a::linordered_ring_strict"
  shows "sign (x*y) = sign x * sign y"
  unfolding Sturm_Tarski.sign_def 
  by (auto simp add:zero_less_mult_iff)
   
lemma sign_power:
  fixes x::"'a::linordered_idom"
  shows "sign (x^n) = (if n=0 then 1 else if even n then \<bar>sign x\<bar> else sign x)"
  by (simp add: Sturm_Tarski.sign_def zero_less_power_eq)
    
lemma sgn_sign_eq:
  fixes x::"'a::{linordered_idom}"
  shows "sgn x = of_int (sign x)" 
  unfolding sgn_if by auto

section \<open>Variation and cross\<close>

definition variation :: "real \<Rightarrow>  real \<Rightarrow> int" where
  "variation x y=(if x*y\<ge>0 then 0 else if x<y then 1 else -1)" 

definition cross :: "real poly \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int" where
  "cross p a b=variation (poly p a) (poly p b)"

lemma variation_0[simp]: "variation 0 y=0" "variation x 0=0" 
  unfolding variation_def by auto

lemma variation_comm: "variation x y= - variation y x" unfolding variation_def
  by (auto simp add: mult.commute) 

lemma cross_0[simp]: "cross 0 a b=0" unfolding cross_def by auto

lemma variation_cases:
  "\<lbrakk>x>0;y>0\<rbrakk>\<Longrightarrow>variation x y = 0" 
  "\<lbrakk>x>0;y<0\<rbrakk>\<Longrightarrow>variation x y = -1"
  "\<lbrakk>x<0;y>0\<rbrakk>\<Longrightarrow>variation x y = 1"
  "\<lbrakk>x<0;y<0\<rbrakk>\<Longrightarrow>variation x y = 0"
proof -
  show "\<lbrakk>x>0;y>0\<rbrakk>\<Longrightarrow>variation x y = 0"  unfolding variation_def by auto
  show "\<lbrakk>x>0;y<0\<rbrakk>\<Longrightarrow>variation x y = -1" unfolding variation_def  
    using mult_pos_neg by fastforce
  show "\<lbrakk>x<0;y>0\<rbrakk>\<Longrightarrow>variation x y = 1" unfolding variation_def 
    using mult_neg_pos by fastforce
  show "\<lbrakk>x<0;y<0\<rbrakk>\<Longrightarrow>variation x y = 0" unfolding variation_def 
    using mult_neg_neg by fastforce
qed

lemma variation_congr:
  assumes "sgn x=sgn x'" "sgn y=sgn y'"
  shows "variation x y=variation x' y'" using assms
proof -
  have " 0 \<le> x * y =  (0\<le> x' * y')" using assms by (metis Real_Vector_Spaces.sgn_mult zero_le_sgn_iff)
  moreover hence "\<not> 0\<le>x * y \<Longrightarrow> x < y = (x' < y')" using assms 
    by (metis less_eq_real_def mult_nonneg_nonneg mult_nonpos_nonpos not_le order.strict_trans2 
      zero_le_sgn_iff)
  ultimately show ?thesis unfolding variation_def by auto
qed

lemma variation_mult_pos: 
  assumes "c>0"  
  shows "variation (c*x) y =variation x y" and "variation x (c*y) =variation x y" 
proof -
  have "sgn (c*x) = sgn x" using \<open>c>0\<close> 
    by (simp add: Real_Vector_Spaces.sgn_mult)
  thus "variation (c*x) y =variation x y" using variation_congr by blast 
next
  have "sgn (c*y) = sgn y" using \<open>c>0\<close>
    by (simp add: Real_Vector_Spaces.sgn_mult)
  thus "variation x (c*y) =variation x y" using variation_congr by blast 
qed

lemma variation_mult_neg_1: 
  assumes "c<0"  
  shows "variation (c*x) y =variation x y + (if y=0 then 0 else sign x)" 
  apply (cases x  rule:linorder_cases[of 0] )
  apply (cases y  rule:linorder_cases[of 0], auto simp add: 
    variation_cases mult_neg_pos[OF \<open>c<0\<close>,of x]  mult_neg_neg[OF \<open>c<0\<close>,of x])+ 
done

lemma variation_mult_neg_2: 
  assumes "c<0"  
  shows "variation x (c*y) = variation x y + (if x=0 then 0 else - sign y)" 
unfolding variation_comm[of x "c*y", unfolded variation_mult_neg_1[OF \<open>c<0\<close>, of y x] ] 
  by (auto,subst variation_comm,simp)

lemma cross_no_root:
  assumes "a<b" and no_root:"\<forall>x. a<x\<and>x<b \<longrightarrow> poly p x\<noteq>0"
  shows "cross p a b=0"
proof -
  have "\<lbrakk>poly p a>0;poly p b<0\<rbrakk> \<Longrightarrow> False" using poly_IVT_neg[OF \<open>a<b\<close>] no_root by auto
  moreover have "\<lbrakk>poly p a<0;poly p b>0\<rbrakk> \<Longrightarrow> False" using poly_IVT_pos[OF \<open>a<b\<close>] no_root by auto
  ultimately have "0 \<le> poly p a * poly p b" 
    by (metis less_eq_real_def linorder_neqE_linordered_idom mult_less_0_iff)
  thus ?thesis unfolding cross_def variation_def by simp
qed

section \<open>Tarski query\<close>

definition taq :: "'a::linordered_idom set \<Rightarrow> 'a poly \<Rightarrow> int" where
  "taq s q \<equiv> \<Sum>x\<in>s. sign (poly q x)"

section \<open>Sign at the right\<close>

definition sign_r_pos :: "real poly \<Rightarrow> real \<Rightarrow> bool " 
  where
  "sign_r_pos p x\<equiv> (eventually (\<lambda>x. poly p x>0) (at_right x))"

lemma sign_r_pos_rec:
  fixes p:: "real poly"
  assumes "p\<noteq>0"
  shows "sign_r_pos p x= (if poly p x=0 then sign_r_pos (pderiv p) x else poly p x>0 )"
proof (cases "poly p x=0")
  case True
  have "sign_r_pos (pderiv p) x \<Longrightarrow> sign_r_pos p x" 
  proof (rule ccontr)
    assume "sign_r_pos (pderiv p) x" "\<not> sign_r_pos p x"
    obtain b where "b>x" and b:"\<forall>z. x < z \<and> z < b \<longrightarrow> 0 < poly (pderiv p) z" 
      using \<open>sign_r_pos (pderiv p) x\<close> unfolding sign_r_pos_def eventually_at_right  by auto
    have "\<forall>b>x. \<exists>z>x. z < b \<and> \<not> 0 < poly p z" using \<open>\<not> sign_r_pos p x\<close> 
      unfolding sign_r_pos_def eventually_at_right by auto
    then obtain z where "z>x" and "z<b" and "poly p z\<le>0"
      using \<open>b>x\<close> b by auto
    hence "\<exists>z'>x. z' < z \<and> poly p z = (z - x) * poly (pderiv p) z'"
      using poly_MVT[OF \<open>z>x\<close>] True by (metis diff_0_right)
    hence "\<exists>z'>x. z' < z \<and> poly (pderiv p) z' \<le>0"
      using \<open>poly p z\<le>0\<close>\<open>z>x\<close> by (metis leD le_iff_diff_le_0 mult_le_0_iff)
    thus False using b by (metis \<open>z < b\<close> dual_order.strict_trans not_le)
  qed
  moreover have "sign_r_pos p x \<Longrightarrow> sign_r_pos (pderiv p) x" 
  proof -
    assume "sign_r_pos p x"
    have "pderiv p\<noteq>0" using \<open>poly p x=0\<close> \<open>p\<noteq>0\<close> 
      by (metis monoid_add_class.add.right_neutral monom_0 monom_eq_0 mult_zero_right 
          pderiv_iszero poly_0 poly_pCons)
    obtain ub where "ub>x" and ub: "(\<forall>z. x<z\<and>z<ub\<longrightarrow>poly (pderiv p) z>0) 
          \<or> (\<forall>z. x<z\<and>z<ub\<longrightarrow>poly (pderiv p) z<0)"
      using next_non_root_interval[OF \<open>pderiv p\<noteq>0\<close>, of x,unfolded not_eq_pos_or_neg_iff_1] 
      by (metis order.strict_implies_order)
    have "\<forall>z. x<z\<and>z<ub\<longrightarrow>poly (pderiv p) z<0 \<Longrightarrow> False" 
    proof -
      assume assm:"\<forall>z. x<z\<and>z<ub\<longrightarrow>poly (pderiv p) z<0"
      obtain ub' where "ub'>x" and ub':"\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 < poly p z" 
        using \<open>sign_r_pos p x\<close> unfolding sign_r_pos_def eventually_at_right by auto
      obtain z' where "x<z'" and "z' < (x+(min ub' ub))/2"
          and z':"poly p ((x+min ub' ub)/2) = ((x+min ub' ub)/2 - x) * poly (pderiv p) z'"       
        using poly_MVT[of x "(x+min ub' ub)/2" p] \<open>ub'>x\<close> \<open>ub>x\<close> True by auto
      moreover have "0 < poly p ((x+min ub' ub)/2)"
        using ub'[THEN HOL.spec,of "(x+(min ub' ub))/2"] \<open>z' < (x+min ub' ub)/2\<close> \<open>x<z'\<close>
        by auto
      moreover have "(x+min ub' ub)/2 - x>0" using \<open>ub'>x\<close> \<open>ub>x\<close> by auto 
      ultimately have "poly (pderiv p) z'>0" by (metis zero_less_mult_pos)
      thus False using assm[THEN spec,of z'] \<open>x<z'\<close> \<open>z' < (x+(min ub' ub))/2\<close> by auto
    qed
    hence "\<forall>z. x<z\<and>z<ub\<longrightarrow>poly (pderiv p) z>0" using ub by auto
    thus "sign_r_pos (pderiv p) x" unfolding sign_r_pos_def eventually_at_right 
      using \<open>ub>x\<close> by auto 
  qed
  ultimately show ?thesis using True by auto
next
  case False
  have "sign_r_pos p x \<Longrightarrow> poly p x>0" 
  proof (rule ccontr)
    assume "sign_r_pos p x" "\<not> 0 < poly p x"
    then obtain  ub where "ub>x" and ub: "\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 < poly p z" 
      unfolding sign_r_pos_def eventually_at_right by auto
    hence "poly p ((ub+x)/2) > 0" by auto
    moreover have "poly p x<0" using \<open>\<not> 0 < poly p x\<close> False by auto
    ultimately have "\<exists>z>x. z < (ub + x) / 2 \<and> poly p z = 0"  
      using poly_IVT_pos[of x "((ub + x) / 2)" p] \<open>ub>x\<close> by auto
    thus False using ub by auto
  qed
  moreover have "poly p x>0 \<Longrightarrow> sign_r_pos p x" 
    unfolding sign_r_pos_def
    using order_tendstoD(1)[OF poly_tendsto(1),of 0 p x] eventually_at_split by auto 
  ultimately show ?thesis using False by auto
qed

lemma sign_r_pos_0[simp]:"\<not> sign_r_pos 0 (x::real)" 
  using eventually_False[of "at_right x"] unfolding sign_r_pos_def by auto

lemma sign_r_pos_minus:
  fixes p:: "real poly"
  assumes "p\<noteq>0"
  shows "sign_r_pos p x = (\<not> sign_r_pos (-p) x)"  
proof -
  have "sign_r_pos p x \<or> sign_r_pos (-p) x"
    unfolding sign_r_pos_def eventually_at_right 
    using next_non_root_interval[OF \<open>p\<noteq>0\<close>,unfolded not_eq_pos_or_neg_iff_1] 
    by (metis (erased, hide_lams) le_less minus_zero neg_less_iff_less poly_minus)
  moreover have "sign_r_pos p x \<Longrightarrow> \<not> sign_r_pos (-p) x" unfolding sign_r_pos_def 
    using eventually_neg[OF trivial_limit_at_right_real, of "\<lambda>x. poly p x > 0" x] poly_minus 
    by (metis (lifting) eventually_mono less_asym neg_less_0_iff_less)
  ultimately show ?thesis by auto
qed

lemma sign_r_pos_smult:
  fixes p :: "real poly"
  assumes "c\<noteq>0" "p\<noteq>0"
  shows "sign_r_pos (smult c p) x= (if c>0 then sign_r_pos p x else \<not> sign_r_pos p x)"
  (is "?L=?R")
proof (cases "c>0")
  assume "c>0"
  hence "\<forall>x. (0 < poly (smult c p) x) = (0 < poly p x)" 
    by (subst poly_smult,metis mult_pos_pos zero_less_mult_pos) 
  thus ?thesis unfolding sign_r_pos_def using \<open>c>0\<close> by auto
next
  assume "\<not>(c>0)"
  hence "\<forall>x. (0 < poly (smult c p) x) = (0 < poly (-p) x)"
    by (subst poly_smult, metis assms(1) linorder_neqE_linordered_idom mult_neg_neg mult_zero_right 
      neg_0_less_iff_less poly_minus zero_less_mult_pos2)
  hence "sign_r_pos (smult c p) x=sign_r_pos (-p) x"
    unfolding sign_r_pos_def using \<open>\<not> c>0\<close> by auto
  thus ?thesis using sign_r_pos_minus[OF \<open>p\<noteq>0\<close>, of x] \<open>\<not> c>0\<close> by auto
qed

lemma sign_r_pos_mult:
  fixes p q :: "real poly"
  assumes "p\<noteq>0" "q\<noteq>0"
  shows "sign_r_pos (p*q) x= (sign_r_pos p x \<longleftrightarrow> sign_r_pos q x)"
proof -
  obtain ub where "ub>x" 
      and ub:"(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 < poly p z) \<or> (\<forall>z. x < z \<and> z < ub \<longrightarrow> poly p z < 0)"
    using next_non_root_interval[OF \<open>p\<noteq>0\<close>,of x,unfolded not_eq_pos_or_neg_iff_1]  
    by (metis order.strict_implies_order)
  obtain ub' where "ub'>x" 
      and ub':"(\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 < poly q z) \<or> (\<forall>z. x < z \<and> z < ub' \<longrightarrow> poly q z < 0)"
    using next_non_root_interval[OF \<open>q\<noteq>0\<close>,unfolded not_eq_pos_or_neg_iff_1] 
    by (metis order.strict_implies_order)
  have "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 < poly p z) \<Longrightarrow> (\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 < poly q z) \<Longrightarrow> ?thesis"
    proof -
      assume "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 < poly p z)" "(\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 < poly q z)"
      hence "sign_r_pos p x" and "sign_r_pos q x" unfolding sign_r_pos_def eventually_at_right
        using \<open>ub>x\<close> \<open>ub'>x\<close> by auto
      moreover hence "eventually (\<lambda>z. poly p z>0 \<and> poly q z>0) (at_right x)"
        unfolding sign_r_pos_def using eventually_conj_iff[of _ _ "at_right x"] by auto
      hence "sign_r_pos (p*q) x"
        unfolding sign_r_pos_def poly_mult 
        by (metis (lifting, mono_tags) eventually_mono mult_pos_pos)
      ultimately show ?thesis by auto
    qed
  moreover have "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 > poly p z) \<Longrightarrow> (\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 < poly q z) 
      \<Longrightarrow> ?thesis"
  proof -
    assume "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 > poly p z)" "(\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 < poly q z)"
    hence "sign_r_pos (-p) x" and "sign_r_pos q x" unfolding sign_r_pos_def eventually_at_right
      using \<open>ub>x\<close> \<open>ub'>x\<close> by auto
    moreover hence "eventually (\<lambda>z. poly (-p) z>0 \<and> poly q z>0) (at_right x)"
      unfolding sign_r_pos_def using eventually_conj_iff[of _ _ "at_right x"] by auto
    hence "sign_r_pos (- p*q) x"
      unfolding sign_r_pos_def poly_mult 
      by (metis (lifting, mono_tags) eventually_mono mult_pos_pos)
    ultimately show ?thesis 
      using sign_r_pos_minus \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> by (metis minus_mult_left no_zero_divisors)
  qed
  moreover have "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 < poly p z) \<Longrightarrow> (\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 > poly q z)
      \<Longrightarrow> ?thesis"
  proof -
    assume "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 < poly p z)" "(\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 > poly q z)"
    hence "sign_r_pos p x" and "sign_r_pos (-q) x" unfolding sign_r_pos_def eventually_at_right
      using \<open>ub>x\<close> \<open>ub'>x\<close> by auto
    moreover hence "eventually (\<lambda>z. poly p z>0 \<and> poly (-q) z>0) (at_right x)"
      unfolding sign_r_pos_def using eventually_conj_iff[of _ _ "at_right x"] by auto
    hence "sign_r_pos ( p * (- q)) x"
      unfolding sign_r_pos_def poly_mult 
      by (metis (lifting, mono_tags) eventually_mono mult_pos_pos)
    ultimately show ?thesis 
      using sign_r_pos_minus \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> 
      by (metis minus_mult_right no_zero_divisors)
  qed
  moreover have "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 > poly p z) \<Longrightarrow> (\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 > poly q z) 
      \<Longrightarrow> ?thesis"
  proof -
    assume "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 > poly p z)" "(\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 > poly q z)"
    hence "sign_r_pos (-p) x" and "sign_r_pos (-q) x" 
      unfolding sign_r_pos_def eventually_at_right using \<open>ub>x\<close> \<open>ub'>x\<close> by auto
    moreover hence "eventually (\<lambda>z. poly (-p) z>0 \<and> poly (-q) z>0) (at_right x)"
      unfolding sign_r_pos_def using eventually_conj_iff[of _ _ "at_right x"] by auto
    hence "sign_r_pos (p * q) x"
      unfolding sign_r_pos_def poly_mult poly_minus
      apply (elim eventually_mono[of _ "at_right x"])
      by (auto intro:mult_neg_neg)
    ultimately show ?thesis 
      using sign_r_pos_minus \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> by metis
  qed
  ultimately show ?thesis using ub ub' by auto
qed

lemma sign_r_pos_add:
  fixes p q :: "real poly"
  assumes "poly p x=0" "poly q x\<noteq>0"
  shows "sign_r_pos (p+q) x=sign_r_pos q x"
proof (cases "poly (p+q) x=0")
  case False
  hence "p+q\<noteq>0" by (metis poly_0)
  have "sign_r_pos (p+q) x = (poly q x > 0)"  
    using sign_r_pos_rec[OF \<open>p+q\<noteq>0\<close>] False poly_add \<open>poly p x=0\<close> by auto
  moreover have "sign_r_pos q x=(poly q x > 0)"
    using sign_r_pos_rec[of q x] \<open>poly q x\<noteq>0\<close> poly_0 by force
  ultimately show ?thesis by auto
next
  case True
  hence False using \<open>poly p x=0\<close> \<open>poly q x\<noteq>0\<close> poly_add by auto
  thus ?thesis by auto
qed

lemma sign_r_pos_mod:
  fixes p q :: "real poly"
  assumes "poly p x=0" "poly q x\<noteq>0"
  shows "sign_r_pos (q mod p) x=sign_r_pos q x"
proof -
  have "poly (q div p * p) x=0" using \<open>poly p x=0\<close> poly_mult by auto
  moreover hence "poly (q mod p) x \<noteq> 0" using \<open>poly q x\<noteq>0\<close> 
    by (simp add: assms(1) poly_mod)
  ultimately show ?thesis 
    by (metis div_mult_mod_eq sign_r_pos_add)
qed

lemma sign_r_pos_pderiv:
  fixes p:: "real poly"
  assumes "poly p x=0" "p\<noteq>0"
  shows "sign_r_pos (pderiv p * p) x"
proof -
  have "pderiv p \<noteq>0" 
    by (metis assms(1) assms(2) monoid_add_class.add.right_neutral mult_zero_right pCons_0_0 
      pderiv_iszero poly_0 poly_pCons)
  have "?thesis = (sign_r_pos (pderiv p) x \<longleftrightarrow> sign_r_pos p x)"
    using sign_r_pos_mult[OF \<open>pderiv p \<noteq> 0\<close> \<open>p\<noteq>0\<close>] by auto
  also have "...=((sign_r_pos (pderiv p) x \<longleftrightarrow> sign_r_pos (pderiv p) x))"
    using sign_r_pos_rec[OF \<open>p\<noteq>0\<close>] \<open>poly p x=0\<close> by auto
  finally show ?thesis by auto
qed

lemma sign_r_pos_power:
  fixes p:: "real poly" and a::real
  shows "sign_r_pos ([:-a,1:]^n) a" 
proof (induct n)
  case 0
  thus ?case unfolding sign_r_pos_def eventually_at_right by (simp,metis gt_ex)
next
  case (Suc n)
  have "pderiv ([:-a,1:]^Suc n) = smult (Suc n) ([:-a,1:]^n)" 
  proof -
    have "pderiv [:- a, 1::real:] = 1" by (simp add: pderiv.simps)
    thus ?thesis unfolding pderiv_power_Suc by (metis mult_cancel_left1)
  qed                                                                                    
  moreover have " poly ([:- a, 1:] ^ Suc n) a=0" by (metis old.nat.distinct(2) poly_power_n_eq)
  hence "sign_r_pos ([:- a, 1:] ^ Suc n) a = sign_r_pos (smult (Suc n) ([:-a,1:]^n)) a"
    using sign_r_pos_rec by (metis (erased, hide_lams) calculation pderiv_0)
  hence "sign_r_pos ([:- a, 1:] ^ Suc n) a = sign_r_pos  ([:-a,1:]^n) a"
    using sign_r_pos_smult by auto
  ultimately show ?case using Suc.hyps by auto
qed
section\<open>Jump\<close>

definition jump_poly :: "real poly \<Rightarrow> real poly \<Rightarrow>real \<Rightarrow> int"
 where 
 " jump_poly q p x\<equiv> (if p\<noteq>0 \<and> q\<noteq>0 \<and> odd((order x p) - (order x q) ) then 
                  if sign_r_pos (q*p) x then 1 else -1
                else 0 )"

lemma jump_poly_not_root:"poly p x\<noteq>0\<Longrightarrow> jump_poly q p x=0"
  unfolding  jump_poly_def by (metis even_zero order_root zero_diff)

lemma jump_poly0[simp]: 
    "jump_poly 0 p x = 0"
    "jump_poly q 0 x = 0"
  unfolding jump_poly_def by auto 

lemma jump_poly_smult_1:
  fixes p q::"real poly" and c::real
  shows "jump_poly (smult c q) p x= sign c * jump_poly q p x" (is "?L=?R")
proof (cases "c=0\<or> q=0") 
  case True
  thus ?thesis unfolding jump_poly_def by auto
next
  case False
  hence "c\<noteq>0" and "q\<noteq>0" by auto
  thus ?thesis unfolding jump_poly_def
     using order_smult[OF \<open>c\<noteq>0\<close>] sign_r_pos_smult[OF \<open>c\<noteq>0\<close>, of "q*p" x] \<open>q\<noteq>0\<close> 
     by auto
qed

lemma jump_poly_mult:
  fixes p q p'::"real poly"
  assumes "p'\<noteq>0"
  shows "jump_poly (p'*q) (p'*p) x= jump_poly q p x"
proof (cases "q=0 \<or> p=0")
  case True
  thus ?thesis unfolding jump_poly_def by fastforce
next 
  case False
  then have "q\<noteq>0" "p\<noteq>0" by auto
  have "sign_r_pos (p' * q * (p' * p)) x=sign_r_pos (q * p) x"
  proof (unfold sign_r_pos_def,rule eventually_subst,unfold eventually_at_right)
    obtain b where "b>x" and b:"\<forall>z. x < z \<and> z < b \<longrightarrow> poly (p' * p') z >0" 
    proof (cases "\<exists>z. poly p' z=0 \<and> z>x")
      case True
      define lr where "lr\<equiv>Min {r . poly p' r=0 \<and> r>x}" 
      have "\<forall>z. x<z\<and>z<lr\<longrightarrow>poly p' z\<noteq>0" and "lr>x" 
        using True lr_def poly_roots_finite[OF \<open>p'\<noteq>0\<close>] by auto
      hence "\<forall>z. x < z \<and> z < lr \<longrightarrow> 0 < poly (p' * p') z" 
        by (metis not_real_square_gt_zero poly_mult)
      thus ?thesis using that[OF \<open>lr>x\<close>] by auto
    next
      case False
      have "\<forall>z. x<z\<and>z<x+1\<longrightarrow>poly p' z\<noteq>0" and "x+1>x" 
        using False poly_roots_finite[OF \<open>p'\<noteq>0\<close>]  by auto
      hence "\<forall>z. x < z \<and> z < x+1 \<longrightarrow> 0 < poly (p' * p') z" 
        by (metis not_real_square_gt_zero poly_mult)
      thus ?thesis using that[OF \<open>x+1>x\<close>] by auto
    qed
    show "\<exists>b>x. \<forall>z>x. z < b \<longrightarrow> (0 < poly (p' * q * (p' * p)) z) = (0 < poly (q * p) z)"
    proof (rule_tac x="b" in exI, rule conjI[OF \<open>b>x\<close>],rule allI,rule impI,rule impI)
      fix z assume "x < z"  "z < b"
      hence "0<poly (p'*p') z" using b by auto
      have " (0 < poly (p' * q * (p' * p)) z)=(0<poly (p'*p') z * poly (q*p) z)" 
        by (simp add: mult.commute mult.left_commute)
      also have "...=(0<poly (q*p) z)"
        using \<open>0<poly (p'*p') z\<close> by (metis mult_pos_pos zero_less_mult_pos)
      finally show "(0 < poly (p' * q * (p' * p)) z) = (0 < poly (q * p) z)" .
    qed
  qed
  moreover have " odd (order x (p' * p) - order x (p' * q)) = odd (order x p - order x q)"
    using  False \<open>p'\<noteq>0\<close> \<open>p\<noteq>0\<close> mult_eq_0_iff order_mult
    by (metis add_diff_cancel_left)
  moreover have " p' * q \<noteq> 0 \<longleftrightarrow> q \<noteq> 0" 
    by (metis \<open>p'\<noteq>0\<close> mult_eq_0_iff)
  ultimately show "jump_poly (p' * q) (p' * p) x = jump_poly q p x" unfolding jump_poly_def by auto
qed

lemma jump_poly_1_mult:
  fixes p1 p2::"real poly"
  assumes "poly p1 x\<noteq>0 \<or> poly p2 x\<noteq>0" 
  shows "jump_poly 1 (p1*p2) x= sign (poly p2 x) * jump_poly 1 p1 x 
            + sign (poly p1 x) * jump_poly 1 p2 x" (is "?L=?R")
proof (cases "p1=0 \<or> p2 =0")
  case True
  then show ?thesis by auto
next
  case False
  then have "p1\<noteq>0" "p2\<noteq>0" "p1*p2\<noteq>0" by auto
  have ?thesis when "poly p1 x\<noteq>0"
  proof -
    have [simp]:"order x p1 = 0" using that order_root by blast
    define simpL where "simpL\<equiv>(if p2\<noteq>0 \<and> odd (order x p2) then if (poly p1 x>0) 
    \<longleftrightarrow>  sign_r_pos p2 x then 1::int else -1 else 0)"
    have "?L=simpL"
      unfolding simpL_def jump_poly_def  
      using order_mult[OF \<open>p1*p2\<noteq>0\<close>]
        sign_r_pos_mult[OF \<open>p1\<noteq>0\<close> \<open>p2\<noteq>0\<close>] sign_r_pos_rec[OF \<open>p1\<noteq>0\<close>] \<open>poly p1 x\<noteq>0\<close>
      by auto
    moreover have "poly p1 x>0 \<Longrightarrow> simpL =?R" 
      unfolding simpL_def jump_poly_def using jump_poly_not_root[OF \<open>poly p1 x\<noteq>0\<close>] 
      by auto
    moreover have "poly p1 x<0 \<Longrightarrow> simpL =?R" 
      unfolding simpL_def jump_poly_def using jump_poly_not_root[OF \<open>poly p1 x\<noteq>0\<close>] 
      by auto
    ultimately show "?L=?R" using \<open>poly p1 x\<noteq>0\<close> by (metis linorder_neqE_linordered_idom)
  qed
  moreover have ?thesis when "poly p2 x\<noteq>0"
  proof -
    have [simp]:"order x p2 = 0" using that order_root by blast
    define simpL where "simpL\<equiv>(if p1\<noteq>0 \<and> odd (order x p1) then if (poly p2 x>0) 
    \<longleftrightarrow>  sign_r_pos p1 x then 1::int else -1 else 0)"
    have "?L=simpL"
      unfolding simpL_def jump_poly_def  
      using order_mult[OF \<open>p1*p2\<noteq>0\<close>]
        sign_r_pos_mult[OF \<open>p1\<noteq>0\<close> \<open>p2\<noteq>0\<close>] sign_r_pos_rec[OF \<open>p2\<noteq>0\<close>] \<open>poly p2 x\<noteq>0\<close>
      by auto
    moreover have "poly p2 x>0 \<Longrightarrow> simpL =?R" 
      unfolding simpL_def jump_poly_def using jump_poly_not_root[OF \<open>poly p2 x\<noteq>0\<close>] 
      by auto
    moreover have "poly p2 x<0 \<Longrightarrow> simpL =?R" 
      unfolding simpL_def jump_poly_def using jump_poly_not_root[OF \<open>poly p2 x\<noteq>0\<close>] 
      by auto
    ultimately show "?L=?R" using \<open>poly p2 x\<noteq>0\<close> by (metis linorder_neqE_linordered_idom)
  qed  
  ultimately show ?thesis using assms by auto
qed  
  
lemma jump_poly_mod:
  fixes p q::"real poly" 
  shows "jump_poly q p x= jump_poly (q mod p) p x"
proof (cases "q=0 \<or> p=0")
  case True
  thus ?thesis by fastforce
next
  case False
  then have "p\<noteq>0" "q\<noteq>0" by auto
  define n where "n\<equiv>min (order x q) (order x p)"
  obtain q' where q':"q=[:-x,1:]^n * q'" 
    using n_def  power_le_dvd[OF order_1[of x q], of n] 
    by (metis dvdE min.cobounded2 min.commute)
  obtain p' where p':"p=[:-x,1:]^n * p'" 
    using n_def  power_le_dvd[OF order_1[of x p], of n] 
    by (metis dvdE min.cobounded2)
  have "q'\<noteq>0" and "p'\<noteq>0" using q' p' \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> by auto
  have "order x q'=0 \<or> order x p'=0" 
  proof (rule ccontr)
    assume "\<not> (order x q' = 0 \<or> order x p' = 0)"
    hence "order x q' > 0" and "order x p' > 0" by auto
    hence "order x q>n" and "order x p>n" unfolding q' p' 
      using order_mult[OF \<open>q\<noteq>0\<close>[unfolded q'],of x] order_mult[OF \<open>p\<noteq>0\<close>[unfolded p'],of x] 
          order_power_n_n[of x n]
      by auto
    thus False using n_def by auto
  qed
  have cond:"q' \<noteq> 0 \<and> odd (order x p' - order x q') 
    = (q' mod p' \<noteq>0 \<and> odd(order x p' - order x (q' mod p')))" 
  proof (cases "order x p'=0")
    case True
    thus ?thesis by (metis \<open>q' \<noteq> 0\<close> even_zero zero_diff)
  next
    case False
    hence "order x q'=0" using \<open>order x q'=0 \<or> order x p'=0\<close> by auto
    hence "\<not> [:-x,1:] dvd q'" 
      by (metis \<open>q' \<noteq> 0\<close> order_root poly_eq_0_iff_dvd)
    moreover have "[:-x,1:] dvd p'" using False 
      by (metis order_root poly_eq_0_iff_dvd)
    ultimately have "\<not> [:-x,1:] dvd (q' mod p')"
      by (metis dvd_mod_iff)
    hence "order x (q' mod p') = 0" and "q' mod p' \<noteq>0" 
       apply (metis order_root poly_eq_0_iff_dvd)
      by (metis \<open>\<not> [:- x, 1:] dvd q' mod p'\<close> dvd_0_right)
    thus ?thesis using \<open>order x q'=0\<close> by auto
  qed
  moreover have "q' mod p'\<noteq>0 \<Longrightarrow> poly p' x = 0  
      \<Longrightarrow> sign_r_pos (q' * p') x= sign_r_pos (q' mod p' * p') x" 
  proof -
    assume "q' mod p'\<noteq>0" "poly p' x = 0"
    hence "poly q' x\<noteq>0" using \<open>order x q'=0 \<or> order x p'=0\<close> 
      by (metis \<open>p' \<noteq> 0\<close> \<open>q' \<noteq> 0\<close> order_root)
    hence "sign_r_pos q' x= sign_r_pos (q' mod p') x" 
      using sign_r_pos_mod[OF \<open>poly p' x=0\<close>] by auto 
    thus ?thesis 
      unfolding sign_r_pos_mult[OF \<open>q'\<noteq>0\<close> \<open>p'\<noteq>0\<close>] sign_r_pos_mult[OF \<open>q' mod p'\<noteq>0\<close> \<open>p'\<noteq>0\<close>]
      by auto
  qed
  moreover have "q' mod p' = 0 \<or> poly p' x \<noteq> 0 \<Longrightarrow> jump_poly q' p' x = jump_poly (q' mod p') p' x" 
  proof -
    assume assm:"q' mod p' = 0 \<or> poly p' x \<noteq> 0"
    have "q' mod p' = 0 \<Longrightarrow> ?thesis" unfolding jump_poly_def
      using cond by auto
    moreover have "poly p' x \<noteq> 0 
        \<Longrightarrow> \<not> odd (order x p' - order x q') \<and> \<not> odd(order x p' - order x (q' mod p'))"
      by (metis even_zero order_root zero_diff)
    hence "poly p' x \<noteq> 0 \<Longrightarrow> ?thesis" unfolding jump_poly_def by auto
    ultimately show ?thesis using assm by auto
  qed
  ultimately have " jump_poly q' p' x = jump_poly (q' mod p') p' x" unfolding jump_poly_def by force
  thus ?thesis using p' q' jump_poly_mult by auto
qed 
  
lemma jump_poly_coprime:
  fixes p q:: "real poly"
  assumes "poly p x=0" "coprime p q"
  shows "jump_poly q p x= jump_poly 1 (q*p) x"
proof (cases "p=0 \<or> q=0")
  case True
  then show ?thesis by auto
next
  case False
  then have "p\<noteq>0" "q\<noteq>0" by auto
  then have "poly p x\<noteq>0 \<or> poly q x\<noteq>0" using coprime_poly_0[OF \<open>coprime p q\<close>] by auto    
  then have "poly q x\<noteq>0" using \<open>poly p x=0\<close> by auto
  then have "order x q=0" using order_root by blast
  then have "order x p - order x q = order x (q * p)" 
    using \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> order_mult [of q p x] by auto
  then show ?thesis unfolding jump_poly_def using \<open>q\<noteq>0\<close> by auto   
qed    
 
lemma jump_poly_sgn:
  fixes p q:: "real poly"
  assumes "p\<noteq>0" "poly p x=0"
  shows "jump_poly (pderiv p * q) p x = sign (poly q x)" 
proof (cases "q=0")
  case True
  thus ?thesis by auto 
next
  case False
  have "pderiv p\<noteq>0" using \<open>p\<noteq>0\<close> \<open>poly p x=0\<close>  
    by (metis mult_poly_0_left sign_r_pos_0 sign_r_pos_pderiv)
  have elim_p_order: "order x p - order x (pderiv p * q)=1 - order x q" 
  proof -
    have "order x p - order x (pderiv p * q) = order x p - order x (pderiv p) - order x q" 
      using order_mult \<open>pderiv p\<noteq>0\<close> False by (metis diff_diff_left mult_eq_0_iff) 
    moreover have "order x p - order x (pderiv p) = 1" 
      using order_pderiv[OF \<open>pderiv p\<noteq>0\<close>, of x] \<open>poly p x=0\<close> order_root[of p x] \<open>p\<noteq>0\<close> by auto
    ultimately show ?thesis by auto
  qed
  have elim_p_sign_r_pos:"sign_r_pos (pderiv p * q * p) x=sign_r_pos q x" 
  proof - 
    have "sign_r_pos (pderiv p * q * p) x = (sign_r_pos (pderiv p* p) x \<longleftrightarrow> sign_r_pos q x)"
      by (metis \<open>q \<noteq> 0\<close> \<open>pderiv p \<noteq> 0\<close> assms(1) no_zero_divisors sign_r_pos_mult)
    thus ?thesis using sign_r_pos_pderiv[OF \<open>poly p x=0\<close> \<open>p\<noteq>0\<close>] by auto
  qed 
  define simpleL where "simpleL\<equiv>if pderiv p * q \<noteq> 0 \<and> odd (1 - order x q) then 
      if sign_r_pos q x then 1::int else - 1 else 0"
  have " jump_poly (pderiv p * q) p x =simpleL" 
    unfolding simpleL_def jump_poly_def by (subst elim_p_order, subst elim_p_sign_r_pos,simp)
  moreover have "poly q x=0 \<Longrightarrow> simpleL=sign (poly q x)"
  proof -
    assume "poly q x=0" 
    hence "1-order x q = 0" using \<open>q\<noteq>0\<close> by (metis less_one not_gr0 order_root zero_less_diff) 
    hence "simpleL=0" unfolding simpleL_def by auto
    moreover have "sign (poly q x)=0" using \<open>poly q x=0\<close> by auto
    ultimately show ?thesis by auto
  qed
  moreover have "poly q x\<noteq>0\<Longrightarrow> simpleL=sign (poly q x)"
  proof -
    assume "poly q x\<noteq>0"
    hence "odd (1 - order x q)" by (simp add: order_root)  
    moreover have "pderiv p * q \<noteq> 0" by (metis False \<open>pderiv p \<noteq> 0\<close> no_zero_divisors)
    moreover have "sign_r_pos q x = (poly q x > 0)" 
      using sign_r_pos_rec[OF False] \<open>poly q x\<noteq>0\<close> by auto 
    ultimately have "simpleL=(if poly q x>0 then 1 else - 1)" unfolding simpleL_def by auto
    thus ?thesis using \<open>poly q x\<noteq>0\<close> by auto
  qed
  ultimately show ?thesis by force
qed
 
section \<open>Cauchy index\<close>

definition cindex_poly:: "real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> real poly \<Rightarrow> int" 
  where 
  "cindex_poly a b q p\<equiv> (\<Sum>x\<in>{x. poly p x=0 \<and> a< x\<and> x< b}. jump_poly q p x)"

lemma cindex_poly_0[simp]: "cindex_poly a b 0 p = 0" "cindex_poly a b q 0 = 0" 
  unfolding cindex_poly_def by auto

lemma cindex_poly_cross:
  fixes p::"real poly" and a b::real
  assumes  "a<b" "poly p a\<noteq>0" "poly p b\<noteq>0"
  shows "cindex_poly a b 1 p = cross p a b" 
    using \<open>poly p a\<noteq>0\<close> \<open>poly p b\<noteq>0\<close>
proof (cases "{x. poly p x=0 \<and> a< x\<and> x< b}\<noteq>{}", induct "degree p" arbitrary:p rule:nat_less_induct) 
  case 1
  then have "p\<noteq>0" by force
  define roots where "roots\<equiv>{x.  poly p x=0 \<and> a< x\<and> x< b}"
  have "finite roots" unfolding roots_def using poly_roots_finite[OF \<open>p\<noteq>0\<close>] by auto
  define max_r where "max_r\<equiv>Max roots"
  hence "poly p max_r=0" and "a<max_r" and "max_r<b" 
    using Max_in[OF \<open>finite roots\<close>] "1.prems"  unfolding roots_def by auto
  define max_rp where "max_rp\<equiv>[:-max_r,1:]^order max_r p"
  then obtain p' where p':"p=p'*max_rp" and not_dvd:"\<not> [:-max_r,1:] dvd p'"  
    by (metis \<open>p\<noteq>0\<close> mult.commute order_decomp)
  hence "p'\<noteq>0" and "max_rp\<noteq>0" and "poly p' a\<noteq>0" and "poly p' b\<noteq>0" 
      and  "poly max_rp a\<noteq>0" and "poly max_rp b\<noteq>0" 
    using \<open>p\<noteq>0\<close> \<open>poly p a\<noteq>0\<close> \<open>poly p b\<noteq>0\<close>  by auto
  define max_r_sign where "max_r_sign\<equiv>if odd(order max_r p) then -1 else 1::int"
  define roots' where "roots'\<equiv>{x.  a< x\<and> x< b \<and> poly p' x=0}"
  have "(\<Sum>x\<in>roots. jump_poly 1 p x)= (\<Sum>x\<in>roots'. jump_poly 1 p x)+ jump_poly 1 p max_r"
  proof -
    have "roots=roots' \<union> {x.  a< x\<and> x< b \<and> poly max_rp x=0 }"
      unfolding roots_def roots'_def p' by auto
    moreover have "{x.  a < x \<and> x < b \<and>  poly max_rp x = 0 }={max_r}"
      unfolding max_rp_def using \<open>poly p max_r=0\<close>  
      by (auto simp add: \<open>a<max_r\<close> \<open>max_r<b\<close>,metis "1.prems"(1) neq0_conv order_root)
    moreover hence "roots' \<inter> {x. a< x\<and> x< b \<and> poly max_rp x=0} ={}"
      unfolding roots'_def  using \<open>\<not> [:-max_r,1:] dvd p'\<close> 
      by (metis (mono_tags) Int_insert_right_if0 inf_bot_right mem_Collect_eq poly_eq_0_iff_dvd)
    moreover have "finite roots'" 
      using  p' \<open>p\<noteq>0\<close> by (metis \<open>finite roots\<close> calculation(1) calculation(2) finite_Un)
    ultimately show ?thesis using sum.union_disjoint by auto
  qed
  moreover have "(\<Sum>x\<in>roots'. jump_poly 1 p x) = max_r_sign * cross p' a b"
  proof -
    have "(\<Sum>x\<in>roots'. jump_poly 1 p x) = (\<Sum>x\<in>roots'. max_r_sign * jump_poly 1 p' x)"
    proof (rule sum.cong,rule refl)
      fix x assume "x \<in> roots'" 
      hence "x\<noteq>max_r" using not_dvd unfolding roots'_def 
        by (metis (mono_tags, lifting) mem_Collect_eq poly_eq_0_iff_dvd )
      hence "poly max_rp x\<noteq>0" using poly_power_n_eq unfolding max_rp_def by auto
      hence "order x max_rp=0"  by (metis order_root)
      moreover have "jump_poly 1 max_rp x=0" 
        using \<open>poly max_rp x\<noteq>0\<close> by (metis jump_poly_not_root)
      moreover have "x\<in>roots"
        using \<open>x \<in> roots'\<close> unfolding roots_def roots'_def p' by auto
      hence "x<max_r" 
        using Max_ge[OF \<open>finite roots\<close>,of x] \<open>x\<noteq>max_r\<close> by (fold max_r_def,auto)
      hence "sign (poly max_rp x) = max_r_sign" 
        using \<open>poly max_rp x \<noteq> 0\<close> unfolding max_r_sign_def max_rp_def sign_def
        by (subst poly_power,simp add:linorder_class.not_less zero_less_power_eq)
      ultimately show "jump_poly 1 p x = max_r_sign * jump_poly 1 p' x" 
        using jump_poly_1_mult[of p' x max_rp]  unfolding p' 
        by (simp add: \<open>poly max_rp x \<noteq> 0\<close>)
      qed
      also have "... = max_r_sign * (\<Sum>x\<in>roots'. jump_poly 1 p' x)" 
          by (simp add: sum_distrib_left)
      also have "... = max_r_sign * cross p' a b"
      proof (cases "roots'={}")
        case True
        hence "cross p' a b=0" unfolding roots'_def using cross_no_root[OF \<open>a<b\<close>] by auto 
        thus ?thesis using True by simp
      next
        case False
        moreover have "degree max_rp\<noteq>0" 
          unfolding max_rp_def degree_linear_power 
          by (metis "1.prems"(1) \<open>poly p max_r = 0\<close> order_root)
        hence  "degree p' < degree p" unfolding p' degree_mult_eq[OF \<open>p'\<noteq>0\<close> \<open>max_rp\<noteq>0\<close>]
          by auto
        ultimately have "cindex_poly a b 1 p' = cross p' a b"
          unfolding roots'_def 
          using "1.hyps"[rule_format,of "degree p'" p'] \<open>p'\<noteq>0\<close> \<open>poly p' a\<noteq>0\<close> \<open>poly p' b\<noteq>0\<close> 
          by auto  
        moreover have "cindex_poly a b 1 p' = sum (jump_poly 1 p') roots'" 
          unfolding cindex_poly_def roots'_def
          apply simp
          by (metis (no_types, lifting) )
        ultimately show ?thesis by auto
      qed
      finally show ?thesis .
    qed
    moreover have "max_r_sign * cross p' a b + jump_poly 1 p max_r = cross p a b" (is "?L=?R")
    proof (cases "odd (order max_r p)")
      case True
      have "poly max_rp a < 0" 
        using poly_power_n_odd[OF True,of max_r a] \<open>poly max_rp a\<noteq>0\<close> \<open>max_r>a\<close>  
        unfolding max_rp_def by linarith
      moreover have "poly max_rp b>0 "
        using poly_power_n_odd[OF True,of max_r b] \<open>max_r<b\<close>  
        unfolding max_rp_def by linarith
      ultimately have "?R=cross p' a b + sign (poly p' a)"
        unfolding p' cross_def poly_mult
        using variation_mult_neg_1[of "poly max_rp a", simplified mult.commute]
          variation_mult_pos(2)[of "poly max_rp b", simplified mult.commute] \<open>poly p' b\<noteq>0\<close>
        by auto
      moreover have "?L=- cross p' a b + sign (poly p' b)" 
      proof -
        have " sign_r_pos p' max_r = (poly p' max_r >0)" 
          using sign_r_pos_rec[OF \<open>p'\<noteq>0\<close>] not_dvd by (metis poly_eq_0_iff_dvd)
        moreover have "(poly p' max_r>0) = (poly p' b>0)"
        proof (rule ccontr)             
          assume "(0 < poly p' max_r) \<noteq> (0 < poly p' b)"
          hence "poly p' max_r * poly p' b <0"
            using \<open>poly p' b\<noteq>0\<close> not_dvd[folded poly_eq_0_iff_dvd] 
            by (metis (poly_guards_query) linorder_neqE_linordered_idom mult_less_0_iff)
          then obtain r where "r>max_r" and "r<b" and "poly p' r=0"
            using poly_IVT[OF \<open>max_r<b\<close>] by auto
          hence "r\<in>roots" unfolding roots_def p' using \<open>max_r>a\<close> by auto
          thus False using \<open>r>max_r\<close> Max_ge[OF \<open>finite roots\<close>,of r] unfolding max_r_def by auto
        qed
        moreover have "sign_r_pos max_rp max_r"
          using sign_r_pos_power unfolding max_rp_def by auto
        ultimately show ?thesis 
          using True \<open>poly p' b\<noteq>0\<close> \<open>max_rp\<noteq>0\<close> \<open>p'\<noteq>0\<close> sign_r_pos_mult[OF \<open>p'\<noteq>0\<close> \<open>max_rp\<noteq>0\<close>]
          unfolding max_r_sign_def  p' jump_poly_def 
          by simp  
      qed  
      moreover have "variation (poly p' a) (poly p' b) + sign (poly p' a) 
          = - variation (poly p' a) (poly p' b) + sign (poly p' b)" unfolding cross_def
        by (cases "poly p' b" rule:linorder_cases[of 0], (cases "poly p' a" rule:linorder_cases[of 0], 
          auto simp add:variation_cases \<open>poly p' a \<noteq> 0\<close> \<open>poly p' b \<noteq> 0\<close>)+)
      ultimately show ?thesis unfolding cross_def by auto
    next
      case False
      hence "poly max_rp a > 0" and "poly max_rp b > 0"
        unfolding max_rp_def poly_power 
        using \<open>poly max_rp a\<noteq>0\<close> \<open>poly max_rp b \<noteq> 0\<close>  "1.prems"(1-2) \<open>poly p max_r = 0\<close>
        apply (unfold zero_less_power_eq)
        by auto
      moreover have "poly max_rp b > 0"
        unfolding max_rp_def poly_power
        using \<open>poly max_rp b \<noteq> 0\<close> False max_rp_def poly_power 
          zero_le_even_power[of "order max_r p" "b - max_r"]
        by (auto simp add: le_less)
      ultimately have "?R=cross p' a b"
        apply (simp only: p' mult.commute cross_def) using variation_mult_pos
        by auto
      thus ?thesis unfolding max_r_sign_def jump_poly_def using False by auto
    qed
    ultimately have "sum (jump_poly 1 p) roots = cross p a b " by auto
    then show ?case unfolding roots_def cindex_poly_def by simp
next
  case False 
  hence "cross p a b=0" using cross_no_root[OF \<open>a<b\<close>] by auto
  thus ?thesis using False unfolding cindex_poly_def by (metis sum.empty)
qed 

lemma cindex_poly_mult:
  fixes p q p'::"real poly"
  assumes "p'\<noteq> 0"  
  shows "cindex_poly a b (p' * q ) (p' * p) = cindex_poly a b q p"
proof (cases "p=0")
  case True
  then show ?thesis by auto
next
  case False
  show ?thesis unfolding cindex_poly_def
    apply (rule sum.mono_neutral_cong_right)
    subgoal using \<open>p\<noteq>0\<close> \<open>p'\<noteq>0\<close> by (simp add: poly_roots_finite) 
    subgoal by auto
    subgoal using jump_poly_mult jump_poly_not_root assms by fastforce
    subgoal for x using jump_poly_mult[OF \<open>p'\<noteq>0\<close>] by auto
    done
qed    

lemma cindex_poly_smult_1: 
  fixes p q::"real poly" and c::real
  shows "cindex_poly a b (smult c q) p =  (sign c) * cindex_poly a b q p"
unfolding cindex_poly_def
using sum_distrib_left[THEN sym, of "sign c" "\<lambda>x. jump_poly q p x"
    "{x. poly p x = (0::real) \<and> a < x \<and> x < b}"] jump_poly_smult_1
  by auto

lemma cindex_poly_mod:
  fixes p q::"real poly" 
  shows "cindex_poly a b q p =  cindex_poly a b (q mod p) p"
unfolding cindex_poly_def using jump_poly_mod by auto

lemma cindex_poly_inverse_add:
  fixes p q::"real poly" 
  assumes "coprime p q"
  shows "cindex_poly a b q p + cindex_poly a b p q=cindex_poly a b 1 (q*p)"
    (is "?L=?R")
proof (cases "p=0 \<or> q=0")
  case True
  then show ?thesis by auto
next
  case False
  then have "p\<noteq>0" "q\<noteq>0" by auto
  define A where "A\<equiv>{x. poly p x = 0 \<and> a < x \<and> x < b}"
  define B where "B\<equiv>{x. poly q x = 0 \<and> a < x \<and> x < b}"
  have "?L = sum (\<lambda>x. jump_poly 1 (q*p) x) A + sum (\<lambda>x. jump_poly 1 (q*p) x) B" 
  proof -
    have "cindex_poly a b q p = sum (\<lambda>x. jump_poly 1 (q*p) x) A" unfolding A_def cindex_poly_def
      using jump_poly_coprime[OF _ \<open>coprime p q\<close>] by auto 
    moreover have "coprime q p" using \<open>coprime p q\<close>
      by (simp add: ac_simps)
    hence "cindex_poly a b p q = sum (\<lambda>x. jump_poly 1 (q*p) x) B" unfolding B_def cindex_poly_def
      using jump_poly_coprime [of q _ p] by (auto simp add: ac_simps)
    ultimately show ?thesis by auto
  qed
  moreover have "A \<union> B= {x. poly (q*p) x=0 \<and> a<x \<and> x<b }" unfolding poly_mult A_def B_def by auto
  moreover have "A \<inter> B={}" 
  proof (rule ccontr)
    assume "A \<inter> B\<noteq>{}"
    then obtain x where "x\<in>A" and "x\<in>B" by auto
    hence "poly p x=0" and "poly q x=0" unfolding A_def B_def by auto
    hence "gcd p q\<noteq>1" by (metis poly_1 poly_eq_0_iff_dvd gcd_greatest zero_neq_one)
    thus False using \<open>coprime p q\<close> by auto
  qed
  moreover have "finite A" and "finite B" 
    unfolding A_def B_def using poly_roots_finite \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> by fast+
  ultimately have "cindex_poly a b q p + cindex_poly a b p q 
      = sum (jump_poly 1 (q * p)) {x. poly (q*p) x=0 \<and> a<x \<and> x<b}"
    using sum.union_disjoint by metis 
  then show ?thesis unfolding cindex_poly_def by auto 
qed  

lemma cindex_poly_inverse_add_cross:
  fixes p q::"real poly"
  assumes "a < b" "poly (p * q) a \<noteq>0" "poly (p * q) b \<noteq>0"
  shows "cindex_poly a b q p + cindex_poly a b p q = cross (p * q) a b" (is "?L=?R")
proof -
  have "p\<noteq>0" and "q\<noteq>0" using \<open>poly (p * q) a \<noteq>0\<close> by auto
  define g where "g\<equiv>gcd p q"
  obtain p' q' where p':"p= p'*g" and q':"q=q'*g" 
    using gcd_dvd1 gcd_dvd2 dvd_def[of "gcd p q", simplified mult.commute] g_def by metis
  hence "coprime p' q'" using gcd_coprime \<open>p\<noteq>0\<close> unfolding g_def by auto
  have "p'\<noteq>0" "q'\<noteq>0" "g \<noteq>0" using p' q' \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> by auto
  have "?L=cindex_poly a b q' p' + cindex_poly a b p' q'"
    apply (simp only: p' q' mult.commute)
    using cindex_poly_mult[OF \<open>g\<noteq>0\<close>] cindex_poly_mult[OF \<open>g\<noteq>0\<close>]
    by auto
  also have "... = cindex_poly a b 1 (q' * p')"
    using  cindex_poly_inverse_add[OF \<open>coprime p' q'\<close>, of a b] .
  also have "... = cross (p' * q') a b"
    using cindex_poly_cross[OF \<open>a<b\<close>, of "q'*p'"] \<open>p'\<noteq>0\<close> \<open>q'\<noteq>0\<close> 
      \<open>poly (p * q) a \<noteq>0\<close> \<open>poly (p * q) b \<noteq>0\<close>
    unfolding p' q' 
    apply (subst (2) mult.commute)
    by auto
  also have "... = ?R" 
  proof -
    have "poly (p * q) a = poly (g*g) a * poly (p' * q') a"
        and "poly (p * q) b = poly (g*g) b * poly (p' * q') b"
      unfolding p' q' by auto
    moreover have "poly g a\<noteq>0" using \<open>poly (p * q) a \<noteq>0\<close>
      unfolding p' by auto
    hence "poly (g*g) a>0" 
      by (metis (poly_guards_query) not_real_square_gt_zero poly_mult)
    moreover have "poly g b\<noteq>0" using \<open>poly (p * q) b \<noteq>0\<close>
      unfolding p' by auto
    hence "poly (g*g) b>0" by (metis (poly_guards_query) not_real_square_gt_zero poly_mult)
    ultimately show ?thesis 
      unfolding cross_def using variation_mult_pos by auto
  qed
  finally show "?L = ?R" .
qed
  
lemma cindex_poly_rec:
  fixes p q::"real poly"
  assumes "a < b" "poly (p * q) a \<noteq>0" "poly (p * q) b \<noteq>0"
  shows "cindex_poly a b q p  = cross (p * q) a b  +  cindex_poly a b (- (p mod q)) q" (is "?L=?R")
proof -
  have "q\<noteq>0" using \<open>poly (p * q) a \<noteq>0\<close> by auto
  note cindex_poly_inverse_add_cross[OF assms]
  moreover have "- cindex_poly a b p q = cindex_poly a b (- (p mod q)) q"
    using cindex_poly_mod cindex_poly_smult_1[of a b "-1"]
    by auto
  ultimately show ?thesis by auto
qed

lemma cindex_poly_congr:
  fixes p q:: "real poly"
  assumes "a<a'" "a'<b'" "b'<b" 
  assumes "\<forall>x. ((a<x\<and>x\<le>a') \<or> (b'\<le>x \<and> x<b)) \<longrightarrow> poly p x \<noteq>0"
  shows "cindex_poly a b q p=cindex_poly a' b' q p" 
proof (cases "p=0")
  case True
  then show ?thesis by auto
next
  case False
  show ?thesis unfolding cindex_poly_def
    apply (rule sum.mono_neutral_right)
    subgoal using poly_roots_finite[OF \<open>p\<noteq>0\<close>] by auto
    subgoal using assms by auto
    subgoal using assms(4) by fastforce
    done
qed    
  
lemma greaterThanLessThan_unfold:"{a<..<b} = {x. a<x \<and> x<b}" 
  by fastforce
  
lemma cindex_poly_taq:
  fixes p q::"real poly"
  shows "taq {x. poly p x = 0 \<and> a < x \<and> x < b} q=cindex_poly a b (pderiv p * q) p"
proof (cases "p=0")
  case True
  define S where "S={x. poly p x = 0 \<and> a < x \<and> x < b}"
  have ?thesis when "a\<ge>b" 
  proof -
    have "S = {}" using that unfolding S_def by auto
    then show ?thesis using True unfolding taq_def by (fold S_def,simp)
  qed
  moreover have ?thesis when "a<b"
  proof -
    have "infinite {x. a<x \<and> x<b}" using infinite_Ioo[OF \<open>a<b\<close>] 
      unfolding greaterThanLessThan_unfold by simp
    then have "infinite S" unfolding S_def using True by auto 
    then show ?thesis using True unfolding taq_def by (fold S_def,simp)
  qed
  ultimately show ?thesis by fastforce
next
  case False
  show ?thesis 
    unfolding cindex_poly_def taq_def
    by (rule sum.cong,auto simp add:jump_poly_sgn[OF \<open>p\<noteq>0\<close>]) 
qed  

section\<open>Signed remainder sequence\<close>

function smods:: "real poly \<Rightarrow> real poly \<Rightarrow> (real poly) list" where
  "smods p q= (if p=0 then [] else Cons p (smods q (-(p mod q))))"
by auto
termination
 apply (relation "measure (\<lambda>(p,q).if p=0 then 0 else if q=0 then 1 else 2+degree q)")
 apply simp_all
 apply (metis degree_mod_less)
done

lemma smods_nil_eq:"smods p q = [] \<longleftrightarrow> (p=0)" by auto
lemma smods_singleton:"[x] = smods p q \<Longrightarrow> (p\<noteq>0 \<and> q=0 \<and> x=p)" 
  by (metis list.discI list.inject smods.elims)

lemma smods_0[simp]:
  "smods 0 q = []"
  "smods p 0 = (if p=0 then [] else [p])"
by auto

lemma no_0_in_smods: "0\<notin>set (smods p q)"
  apply (induct "smods p q" arbitrary:p q)
  by (simp,metis list.inject neq_Nil_conv set_ConsD smods.elims)

fun changes:: "('a ::linordered_idom) list \<Rightarrow> int" where
  "changes [] = 0"|
  "changes [_] = 0" |
  "changes (x1#x2#xs) = (if x1*x2<0 then 1+changes (x2#xs) 
                          else if x2=0 then changes (x1#xs) 
                          else changes (x2#xs))"

lemma changes_map_sgn_eq:
  "changes xs = changes (map sgn xs)"
proof (induct xs rule:changes.induct)
  case 1
  show ?case by simp
next
  case 2
  show ?case by simp
next
  case (3 x1 x2 xs)
  moreover have "x1*x2<0 \<longleftrightarrow> sgn x1 * sgn x2 < 0" 
    by (unfold mult_less_0_iff sgn_less sgn_greater,simp)
  moreover have "x2=0 \<longleftrightarrow> sgn x2 =0" by (rule sgn_0_0[symmetric])
  ultimately show ?case by auto
qed

definition changes_poly_at::"('a ::linordered_idom) poly list \<Rightarrow> 'a \<Rightarrow> int" where
  "changes_poly_at ps a= changes (map (\<lambda>p. poly p a) ps)" 

definition changes_poly_pos_inf:: "('a ::linordered_idom) poly list \<Rightarrow> int" where
  "changes_poly_pos_inf ps = changes (map sgn_pos_inf ps)"

definition changes_poly_neg_inf:: "('a ::linordered_idom) poly list \<Rightarrow> int" where
  "changes_poly_neg_inf ps = changes (map sgn_neg_inf ps)"

lemma changes_poly_at_0[simp]:  
  "changes_poly_at [] a =0"
  "changes_poly_at [p] a=0"
unfolding changes_poly_at_def by auto

definition changes_itv_smods:: "real \<Rightarrow> real \<Rightarrow>real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_itv_smods a b p q= (let ps= smods p q in changes_poly_at ps a - changes_poly_at ps b)"

definition changes_gt_smods:: "real \<Rightarrow>real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_gt_smods a p q= (let ps= smods p q in changes_poly_at ps a - changes_poly_pos_inf ps)"

definition changes_le_smods:: "real \<Rightarrow>real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_le_smods b p q= (let ps= smods p q in changes_poly_neg_inf ps - changes_poly_at ps b)"

definition changes_R_smods:: "real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_R_smods p q= (let ps= smods p q in changes_poly_neg_inf ps - changes_poly_pos_inf ps)"

lemma changes_R_smods_0[simp]:
    "changes_R_smods 0 q = 0"
    "changes_R_smods p 0 = 0"
  unfolding changes_R_smods_def changes_poly_neg_inf_def changes_poly_pos_inf_def
  by auto
  
lemma changes_itv_smods_0[simp]:
  "changes_itv_smods a b 0 q = 0"
  "changes_itv_smods a b p 0 = 0"
unfolding changes_itv_smods_def 
by auto

lemma changes_itv_smods_rec:
  assumes "a<b" "poly (p*q) a\<noteq>0" "poly (p*q) b\<noteq>0"
  shows "changes_itv_smods a b p q  = cross (p*q) a b + changes_itv_smods a b q (-(p mod q))"
proof (cases "p=0 \<or> q=0 \<or> p mod q = 0")
  case True
  moreover have "p=0 \<or> q=0 \<Longrightarrow> ?thesis"
    unfolding changes_itv_smods_def changes_poly_at_def by (erule HOL.disjE,auto)
  moreover have "p mod q = 0 \<Longrightarrow> ?thesis"  
    unfolding changes_itv_smods_def changes_poly_at_def cross_def 
    apply (insert assms(2,3))
    apply (subst (asm) (1 2) neq_iff)
    by (auto simp add: variation_cases)
  ultimately show ?thesis by auto 
next
  case False
  hence "p\<noteq>0" "q\<noteq>0" "p mod q\<noteq>0" by auto
  then obtain ps where ps:"smods p q=p#q#-(p mod q)#ps" "smods q (-(p mod q)) = q#-(p mod q)#ps"
    by auto
  define changes_diff where "changes_diff\<equiv>\<lambda>x. changes_poly_at (p#q#-(p mod q)#ps) x 
    - changes_poly_at (q#-(p mod q)#ps) x"
  have "\<And>x. poly p x*poly q x<0 \<Longrightarrow> changes_diff x=1"
    unfolding changes_diff_def changes_poly_at_def by auto
  moreover have "\<And>x. poly p x*poly q x>0 \<Longrightarrow> changes_diff x=0"
    unfolding changes_diff_def changes_poly_at_def  by auto
  ultimately have "changes_diff a - changes_diff b=cross (p*q) a b" 
    unfolding cross_def
    apply (cases rule:neqE[OF \<open>poly (p*q) a\<noteq>0\<close>])
    by (cases rule:neqE[OF \<open>poly (p*q) b\<noteq>0\<close>],auto simp add:variation_cases)+
  thus ?thesis unfolding changes_itv_smods_def changes_diff_def changes_poly_at_def 
    using ps by auto
qed 

lemma changes_smods_congr:
  fixes p q:: "real poly"
  assumes "a\<noteq>a'" "poly p a\<noteq>0"
  assumes "\<forall>p\<in>set (smods p q). \<forall>x. ((a<x\<and>x\<le>a') \<or> (a'\<le>x \<and> x<a)) \<longrightarrow> poly p x \<noteq>0"
  shows "changes_poly_at (smods p q) a = changes_poly_at (smods p q) a'" 
    using assms(2-3) 
proof (induct "smods p q" arbitrary:p q rule:length_induct)
  case 1
  have "p\<noteq>0" using \<open>poly p a \<noteq>0\<close> by auto
  define r1 where "r1\<equiv>- (p mod q)"
  have a_a'_rel:"\<forall>pp\<in>set (smods p q). poly pp a * poly pp a' \<ge>0"
  proof (rule ccontr)
    assume "\<not> (\<forall>pp\<in>set (smods p q). 0 \<le> poly pp a * poly pp a')"
    then obtain pp where pp:"pp\<in>set (smods p q)" " poly pp a * poly pp a'<0"
      using \<open>p\<noteq>0\<close> by (metis less_eq_real_def linorder_neqE_linordered_idom)
    hence "a<a' \<Longrightarrow> False" using "1.prems"(2) poly_IVT[of a a' pp] by auto
    moreover have "a'<a\<Longrightarrow>False" 
      using pp[unfolded mult.commute[of "poly pp a"]] "1.prems"(2) poly_IVT[of a' a pp] by auto
    ultimately show False using \<open>a\<noteq>a'\<close> by force
  qed
  have "q=0 \<Longrightarrow> ?case" by auto
  moreover have "\<lbrakk>q\<noteq>0;poly q a=0\<rbrakk> \<Longrightarrow> ?case"
  proof -     
    assume "q\<noteq>0" "poly q a=0"
    define r2 where "r2\<equiv>- (q mod r1)"
    have "- poly r1 a = poly p a " 
      by (metis \<open>poly q a = 0\<close> add.inverse_inverse add.left_neutral div_mult_mod_eq 
            mult_zero_right poly_add poly_minus poly_mult r1_def)
    hence "r1\<noteq>0" and "poly r1 a\<noteq>0" and "poly p a*poly r1 a<0" using \<open>poly p a\<noteq>0\<close> 
      apply auto
      using mult_less_0_iff by fastforce
    then obtain ps where ps:"smods p q=p#q#r1#ps" "smods r1 r2=r1#ps"
      by (metis \<open>p\<noteq>0\<close> \<open>q \<noteq> 0\<close> r1_def r2_def smods.simps)
    hence "length (smods r1 r2)<length (smods p q)" by auto
    moreover have "(\<forall>p\<in>set (smods r1 r2). \<forall>x. a < x \<and> x \<le> a' \<or> a' \<le> x \<and> x < a \<longrightarrow> poly p x \<noteq> 0)" 
      using "1.prems"(2) unfolding ps by auto
    ultimately have "changes_poly_at (smods r1 r2) a = changes_poly_at (smods r1 r2) a'"
      using "1.hyps" \<open>r1\<noteq>0\<close> \<open>poly r1 a\<noteq>0\<close> by metis 
    moreover have "changes_poly_at (smods p q) a = 1+changes_poly_at (smods r1 r2) a"
      unfolding ps changes_poly_at_def using \<open>poly q a=0\<close> \<open>poly p a*poly r1 a<0\<close> by auto
    moreover have "changes_poly_at (smods p q) a' = 1+changes_poly_at (smods r1 r2) a'"
    proof -
      have "poly p a * poly p a' \<ge>0" and "poly r1 a*poly r1 a'\<ge>0" 
        using a_a'_rel unfolding ps by auto
      moreover have "poly p a'\<noteq>0" and "poly q a'\<noteq>0" and "poly r1 a'\<noteq>0" 
        using "1.prems"(2)[unfolded ps] \<open>a\<noteq>a'\<close> by auto
      ultimately show ?thesis using \<open>poly p a*poly r1 a<0\<close> unfolding ps changes_poly_at_def
        by (auto simp add: zero_le_mult_iff, auto simp add: mult_less_0_iff)
      qed
    ultimately show ?thesis by simp
  qed
  moreover have "\<lbrakk>q\<noteq>0;poly q a\<noteq>0\<rbrakk> \<Longrightarrow> ?case"
  proof -
    assume "q\<noteq>0" "poly q a\<noteq>0"
    then obtain ps where ps:"smods p q=p#q#ps" "smods q r1=q#ps" 
      by (metis \<open>p\<noteq>0\<close> r1_def smods.simps)
    hence "length (smods q r1) < length (smods p q)" by auto
    moreover have "(\<forall>p\<in>set (smods q r1). \<forall>x. a < x \<and> x \<le> a' \<or> a' \<le> x \<and> x < a \<longrightarrow> poly p x \<noteq> 0)" 
      using "1.prems"(2) unfolding ps by auto
    ultimately have "changes_poly_at (smods q r1) a = changes_poly_at (smods q r1) a'"
      using "1.hyps" \<open>q\<noteq>0\<close> \<open>poly q a\<noteq>0\<close> by metis
    moreover have "poly p a'\<noteq>0" and "poly q a'\<noteq>0" 
      using "1.prems"(2)[unfolded ps] \<open>a\<noteq>a'\<close> by auto
    moreover  have "poly p a * poly p a' \<ge>0" and "poly q a*poly q a'\<ge>0" 
      using a_a'_rel unfolding ps by auto
    ultimately show ?thesis unfolding ps changes_poly_at_def using  \<open>poly q a\<noteq>0\<close> \<open>poly p a\<noteq>0\<close>
      by (auto simp add: zero_le_mult_iff,auto simp add: mult_less_0_iff)
  qed
  ultimately show ?case by blast
qed

lemma changes_itv_smods_congr:
  fixes p q:: "real poly"
  assumes "a<a'" "a'<b'" "b'<b" "poly p a\<noteq>0" "poly p b\<noteq>0"
  assumes no_root:"\<forall>p\<in>set (smods p q). \<forall>x. ((a<x\<and>x\<le>a') \<or> (b'\<le>x \<and> x<b)) \<longrightarrow> poly p x \<noteq>0"
  shows "changes_itv_smods a b p q=changes_itv_smods a' b' p q"
proof -
  have "changes_poly_at (smods p q) a = changes_poly_at (smods p q) a'"
    apply (rule changes_smods_congr[OF order.strict_implies_not_eq[OF \<open>a<a'\<close>] \<open>poly p a\<noteq>0\<close>])
    by (metis assms(1) less_eq_real_def less_irrefl less_trans no_root)  
  moreover have "changes_poly_at (smods p q) b = changes_poly_at (smods p q) b'"
    apply (rule changes_smods_congr[OF order.strict_implies_not_eq[OF \<open>b'<b\<close>, 
        symmetric] \<open>poly p b\<noteq>0\<close>])
    by (metis assms(3) less_eq_real_def less_trans no_root)
  ultimately show ?thesis unfolding changes_itv_smods_def Let_def by auto
qed

lemma cindex_poly_changes_itv_mods: 
  assumes "a<b" "poly p a\<noteq>0" "poly p b\<noteq>0"
  shows "cindex_poly a b q p = changes_itv_smods a b p q" using assms
proof (induct "smods p q" arbitrary:p q a b)
  case Nil
  hence "p=0" by (metis smods_nil_eq) 
  thus ?case using \<open>poly p a \<noteq> 0\<close> by simp
next
  case (Cons x1 xs) 
  have "p\<noteq>0" using \<open>poly p a \<noteq> 0\<close> by auto
  obtain a' b' where "a<a'" "a'<b'" "b'<b" 
      and no_root:"\<forall>p\<in>set (smods p q). \<forall>x. ((a<x\<and>x\<le>a') \<or> (b'\<le>x \<and> x<b)) \<longrightarrow> poly p x \<noteq>0"
  proof (induct "smods p q" arbitrary:p q thesis)
    case Nil 
    define a' b' where "a'\<equiv>2/3 * a + 1/3 * b" and "b'\<equiv>1/3*a + 2/3*b"
    have "a < a'" and "a' < b'" and "b' < b" unfolding a'_def b'_def using \<open>a<b\<close> by auto
    moreover have "\<forall>p\<in>set (smods p q). \<forall>x. a < x \<and> x \<le> a' \<or> b' \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0" 
      unfolding \<open>[] = smods p q\<close>[symmetric] by auto
    ultimately show ?case using Nil by auto 
  next
    case (Cons x1 xs)
    define r where "r\<equiv>- (p mod q)"
    then have "smods p q = p # xs" and "smods q r = xs" and "p \<noteq> 0"
      using \<open>x1 # xs = smods p q\<close>
      by (auto simp del: smods.simps simp add: smods.simps [of p q] split: if_splits)
    obtain a1 b1 where 
          "a < a1"  "a1 < b1"  "b1 < b" and  
          a1_b1_no_root:"\<forall>p\<in>set xs. \<forall>x. a < x \<and> x \<le> a1 \<or> b1 \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0"
      using Cons(1)[OF \<open>smods q r=xs\<close>[symmetric]] \<open>smods q r=xs\<close> by auto
    obtain a2 b2 where
          "a<a2" and a2:"\<forall>x. a<x \<and> x\<le>a2 \<longrightarrow> poly p x \<noteq> 0"
          "b2<b" and b2:"\<forall>x. b2\<le>x \<and> x<b \<longrightarrow> poly p x \<noteq> 0"
        using next_non_root_interval[OF \<open>p\<noteq>0\<close>] last_non_root_interval[OF \<open>p\<noteq>0\<close>] 
        by (metis less_numeral_extra(3))
    define a' b' where "a'\<equiv> if b2>a then Min{a1, b2, a2} else min a1 a2" 
        and "b'\<equiv>if a2 <b then Max{ b1, a2, b2} else max b1 b2"
    have "a < a'" "a' < b'" "b' < b" unfolding a'_def b'_def 
        using  \<open>a < a1\<close> \<open>a1 < b1\<close> \<open>b1 < b\<close> \<open>a<a2\<close> \<open>b2<b\<close> \<open>a<b\<close> by auto
    moreover have "\<forall>p\<in>set xs. \<forall>x. a < x \<and> x \<le> a' \<or> b' \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0"
        using a1_b1_no_root unfolding a'_def b'_def by auto
    moreover have "\<forall>x. a < x \<and> x \<le> a' \<or> b' \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0"
        using a2 b2 unfolding a'_def b'_def by auto
    ultimately show ?case using Cons(3)[unfolded \<open>smods p q=p#xs\<close>] by auto
  qed
  have "q=0 \<Longrightarrow> ?case" by simp
  moreover have "q\<noteq>0 \<Longrightarrow> ?case"
  proof -
    assume "q\<noteq>0"
    define r where "r\<equiv>- (p mod q)"
    obtain ps where ps:"smods p q=p#q#ps" "smods q r=q#ps" and "xs=q#ps"
      unfolding r_def using \<open>q\<noteq>0\<close> \<open>p\<noteq>0\<close> \<open>x1 # xs = smods p q\<close> 
      by (metis list.inject smods.simps)
    have "poly p a' \<noteq> 0" "poly p b' \<noteq> 0" "poly q a' \<noteq> 0" "poly q b' \<noteq> 0" 
      using no_root[unfolded ps] \<open>a'>a\<close> \<open>b'<b\<close> by auto
    moreover hence 
          "changes_itv_smods a' b' p q = cross (p * q) a' b' + changes_itv_smods a' b' q r"
          "cindex_poly a' b' q p = cross (p * q) a' b' + cindex_poly a' b' r q"
      using changes_itv_smods_rec[OF \<open>a'<b'\<close>,of p q,folded r_def] 
          cindex_poly_rec[OF \<open>a'<b'\<close>,of p q,folded r_def] by auto 
    moreover have "changes_itv_smods a' b' q r = cindex_poly a' b' r q"
        using  Cons.hyps(1)[of q r a' b'] \<open>a' < b'\<close> \<open>q \<noteq> 0\<close> \<open>xs = q # ps\<close> ps(2)
          \<open>poly q a' \<noteq> 0\<close> \<open>poly q b' \<noteq> 0\<close> by simp
    ultimately have "changes_itv_smods a' b' p q = cindex_poly a' b' q p" by auto
    thus ?thesis 
      using 
          changes_itv_smods_congr[OF \<open>a<a'\<close> \<open>a'<b'\<close> \<open>b'<b\<close> Cons(4,5),of q]
          no_root cindex_poly_congr[OF \<open>a<a'\<close> \<open>a'<b'\<close> \<open>b'<b\<close> ] ps
      by (metis insert_iff list.set(2))
  qed
  ultimately show ?case by metis
qed

lemma root_list_ub:
  fixes ps:: "(real poly) list" and a::real
  assumes "0\<notin>set ps"
  obtains ub where "\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x<ub"
    and "\<forall>x\<ge>ub. \<forall>p\<in>set ps. sgn (poly p x) = sgn_pos_inf p" and "ub>a"
    using assms
proof (induct ps arbitrary:thesis)
  case Nil
  show ?case using Nil(1)[of "a+1"] by auto
next
  case (Cons p ps)
  hence "p\<noteq>0" and "0\<notin>set ps" by auto
  then obtain ub1 where ub1:"\<forall>p\<in>set ps. \<forall>x. poly p x = 0 \<longrightarrow> x < ub1" and
      ub1_sgn:"\<forall>x\<ge>ub1. \<forall>p\<in>set ps. sgn (poly p x) = sgn_pos_inf p" and "ub1>a"
    using Cons.hyps by auto
  obtain ub2 where ub2:"\<forall>x. poly p x = 0 \<longrightarrow> x < ub2" 
      and ub2_sgn: "\<forall>x\<ge>ub2. sgn (poly p x) = sgn_pos_inf p"
    using root_ub[OF \<open>p\<noteq>0\<close>] by auto
  define ub where "ub\<equiv>max ub1 ub2"
  have "\<forall>p\<in>set (p # ps). \<forall>x. poly p x = 0 \<longrightarrow> x < ub" using ub1 ub2 ub_def by force
  moreover have "\<forall>x\<ge>ub. \<forall>p\<in>set (p # ps). sgn (poly p x) = sgn_pos_inf p" 
    using ub1_sgn ub2_sgn ub_def by auto
  ultimately show ?case using Cons(2)[of ub] \<open>ub1>a\<close> ub_def by auto
qed

lemma root_list_lb:
  fixes ps:: "(real poly) list" and b::real
  assumes "0\<notin>set ps"
  obtains lb where "\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x>lb"
    and "\<forall>x\<le>lb. \<forall>p\<in>set ps. sgn (poly p x) = sgn_neg_inf p" and "lb<b"
    using assms
proof (induct ps arbitrary:thesis)
  case Nil
  show ?case using Nil(1)[of "b - 1"] by auto
next
  case (Cons p ps)
  hence "p\<noteq>0" and "0\<notin>set ps" by auto
  then obtain lb1 where lb1:"\<forall>p\<in>set ps. \<forall>x. poly p x = 0 \<longrightarrow> x > lb1" and
      lb1_sgn:"\<forall>x\<le>lb1. \<forall>p\<in>set ps. sgn (poly p x) = sgn_neg_inf p" and "lb1<b"
    using Cons.hyps by auto
  obtain lb2 where lb2:"\<forall>x. poly p x = 0 \<longrightarrow> x > lb2" 
      and lb2_sgn: "\<forall>x\<le>lb2. sgn (poly p x) = sgn_neg_inf p"
    using root_lb[OF \<open>p\<noteq>0\<close>] by auto
  define lb where "lb\<equiv>min lb1 lb2"
  have "\<forall>p\<in>set (p # ps). \<forall>x. poly p x = 0 \<longrightarrow> x > lb" using lb1 lb2 lb_def by force
  moreover have "\<forall>x\<le>lb. \<forall>p\<in>set (p # ps). sgn (poly p x) = sgn_neg_inf p" 
    using lb1_sgn lb2_sgn lb_def by auto
  ultimately show ?case using Cons(2)[of lb] \<open>lb1<b\<close> lb_def by auto
qed

theorem sturm_tarski_interval: 
  assumes "a<b" "poly p a\<noteq>0" "poly p b\<noteq>0"
  shows "taq {x. poly p x=0 \<and> a<x \<and> x<b} q = changes_itv_smods a b p (pderiv p * q)" 
proof -
  have "p\<noteq>0" using \<open>poly p a\<noteq>0\<close> by auto
  thus ?thesis using cindex_poly_taq cindex_poly_changes_itv_mods[OF assms] by auto
qed

theorem sturm_tarski_above: 
  assumes "poly p a\<noteq>0" 
  shows "taq {x. poly p x=0 \<and> a<x} q = changes_gt_smods a p (pderiv p * q)"
proof -
  define ps where "ps\<equiv>smods p (pderiv p * q)"
  have "p\<noteq>0" and "p\<in>set ps" using \<open>poly p a\<noteq>0\<close> ps_def by auto
  obtain ub where ub:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x<ub"
      and ub_sgn:"\<forall>x\<ge>ub. \<forall>p\<in>set ps. sgn (poly p x) = sgn_pos_inf p"
      and "ub>a"
    using root_list_ub[OF no_0_in_smods,of p "pderiv p * q",folded ps_def] 
    by auto
  have "taq {x. poly p x=0 \<and> a<x} q = taq {x. poly p x=0 \<and> a<x \<and> x<ub} q"
    unfolding taq_def by (rule sum.cong,insert ub \<open>p\<in>set ps\<close>,auto)
  moreover have "changes_gt_smods a p (pderiv p * q) = changes_itv_smods a ub p (pderiv p * q)"
  proof -
    have "map (sgn \<circ> (\<lambda>p. poly p ub)) ps = map sgn_pos_inf ps"
      using ub_sgn[THEN spec,of ub,simplified] 
      by (metis (mono_tags, lifting) comp_def list.map_cong0)
    hence "changes_poly_at ps ub=changes_poly_pos_inf ps"
      unfolding changes_poly_pos_inf_def changes_poly_at_def
      by (subst changes_map_sgn_eq,metis map_map)
    thus ?thesis unfolding changes_gt_smods_def changes_itv_smods_def ps_def
      by metis
  qed
  moreover have "poly p ub\<noteq>0" using ub \<open>p\<in>set ps\<close> by auto
  ultimately show ?thesis using sturm_tarski_interval[OF \<open>ub>a\<close> assms] by auto
qed

theorem sturm_tarski_below: 
  assumes "poly p b\<noteq>0" 
  shows "taq {x. poly p x=0 \<and> x<b} q = changes_le_smods b p (pderiv p * q)"
proof -
  define ps where "ps\<equiv>smods p (pderiv p * q)"
  have "p\<noteq>0" and "p\<in>set ps" using \<open>poly p b\<noteq>0\<close> ps_def by auto
  obtain lb where lb:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x>lb"
      and lb_sgn:"\<forall>x\<le>lb. \<forall>p\<in>set ps. sgn (poly p x) = sgn_neg_inf p"
      and "lb<b"
    using root_list_lb[OF no_0_in_smods,of p "pderiv p * q",folded ps_def] 
    by auto
  have "taq {x. poly p x=0 \<and> x<b} q = taq {x. poly p x=0 \<and> lb<x \<and> x<b} q"
    unfolding taq_def by (rule sum.cong,insert lb \<open>p\<in>set ps\<close>,auto)
  moreover have "changes_le_smods b p (pderiv p * q) = changes_itv_smods lb b p (pderiv p * q)"
  proof -
    have "map (sgn \<circ> (\<lambda>p. poly p lb)) ps = map sgn_neg_inf ps"
      using lb_sgn[THEN spec,of lb,simplified] 
      by (metis (mono_tags, lifting) comp_def list.map_cong0)
    hence "changes_poly_at ps lb=changes_poly_neg_inf ps"
      unfolding changes_poly_neg_inf_def changes_poly_at_def
      by (subst changes_map_sgn_eq,metis map_map)
    thus ?thesis unfolding changes_le_smods_def changes_itv_smods_def ps_def
      by metis
  qed
  moreover have "poly p lb\<noteq>0" using lb \<open>p\<in>set ps\<close> by auto
  ultimately show ?thesis using sturm_tarski_interval[OF \<open>lb<b\<close> _ assms] by auto
qed

theorem sturm_tarski_R: 
  shows "taq {x. poly p x=0} q = changes_R_smods p (pderiv p * q)"
proof (cases "p=0")
  case True
  then show ?thesis 
    unfolding taq_def using infinite_UNIV_char_0 by (auto intro!:sum.infinite)
next
  case False
  define ps where "ps\<equiv>smods p (pderiv p * q)"
  have "p\<in>set ps" using ps_def \<open>p\<noteq>0\<close> by auto
  obtain lb where lb:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x>lb"
      and lb_sgn:"\<forall>x\<le>lb. \<forall>p\<in>set ps. sgn (poly p x) = sgn_neg_inf p"
      and "lb<0"
    using root_list_lb[OF no_0_in_smods,of p "pderiv p * q",folded ps_def] 
    by auto
  obtain ub where ub:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x<ub"
      and ub_sgn:"\<forall>x\<ge>ub. \<forall>p\<in>set ps. sgn (poly p x) = sgn_pos_inf p"
      and "ub>0"
    using root_list_ub[OF no_0_in_smods,of p "pderiv p * q",folded ps_def] 
    by auto
  have "taq {x. poly p x=0} q = taq {x. poly p x=0 \<and> lb<x \<and> x<ub} q"
    unfolding taq_def by (rule sum.cong,insert lb ub \<open>p\<in>set ps\<close>,auto)
  moreover have "changes_R_smods p (pderiv p * q) = changes_itv_smods lb ub p (pderiv p * q)"
  proof -
    have "map (sgn \<circ> (\<lambda>p. poly p lb)) ps = map sgn_neg_inf ps"
        and "map (sgn \<circ> (\<lambda>p. poly p ub)) ps = map sgn_pos_inf ps"
      using lb_sgn[THEN spec,of lb,simplified] ub_sgn[THEN spec,of ub,simplified] 
      by (metis (mono_tags, lifting) comp_def list.map_cong0)+
    hence "changes_poly_at ps lb=changes_poly_neg_inf ps
          \<and> changes_poly_at ps ub=changes_poly_pos_inf ps"
      unfolding changes_poly_neg_inf_def changes_poly_at_def changes_poly_pos_inf_def
      by (subst (1 3)  changes_map_sgn_eq,metis map_map)
    thus ?thesis unfolding changes_R_smods_def changes_itv_smods_def ps_def
      by metis
  qed
  moreover have "poly p lb\<noteq>0" and "poly p ub\<noteq>0" using lb ub \<open>p\<in>set ps\<close> by auto
  moreover have "lb<ub" using \<open>lb<0\<close> \<open>0<ub\<close> by auto
  ultimately show ?thesis using sturm_tarski_interval by auto
qed

theorem sturm_interval:
  assumes "a < b" "poly p a \<noteq> 0" "poly p b \<noteq> 0"
  shows "card {x. poly p x = 0 \<and> a < x \<and> x < b} = changes_itv_smods a b p (pderiv p)"
using sturm_tarski_interval[OF assms, unfolded taq_def,of 1] by force

theorem sturm_above:
  assumes "poly p a \<noteq> 0" 
  shows "card {x. poly p x = 0 \<and> a < x} = changes_gt_smods a p (pderiv p)"
using sturm_tarski_above[OF assms, unfolded taq_def,of 1] by force

theorem sturm_below:
  assumes "poly p b \<noteq> 0"
  shows "card {x. poly p x = 0 \<and> x < b} = changes_le_smods b p (pderiv p)"
using sturm_tarski_below[OF assms, unfolded taq_def,of 1] by force

theorem sturm_R:
  shows "card {x. poly p x=0} =  changes_R_smods p (pderiv p)"    
using sturm_tarski_R[of _ 1,unfolded taq_def] by force

end
