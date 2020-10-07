(* Title:      Regular Algebras
   Author:     Simon Foster, Georg Struth
   Maintainer: Simon Foster <s.foster at york.ac.uk>
               Georg Struth <g.struth at sheffield.ac.uk>               
*)

section \<open>Regular Algebras\<close>

theory Regular_Algebras
  imports Dioid_Power_Sum Kleene_Algebra.Finite_Suprema Kleene_Algebra.Kleene_Algebra
begin

subsection \<open>Conway's Classical Axioms\<close>

text \<open>Conway's classical axiomatisation of Regular Algebra from~\cite{Conway}.\<close>
 
class star_dioid = dioid_one_zero + star_op + plus_ord

class conway_dioid = star_dioid +
  assumes C11: "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
  and C12: "(x \<cdot> y)\<^sup>\<star> = 1 + x \<cdot>(y \<cdot> x)\<^sup>\<star> \<cdot> y"

class strong_conway_dioid = conway_dioid +
  assumes  C13: "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"

class C_algebra = strong_conway_dioid +
  assumes C14: "x\<^sup>\<star> = (x\<^bsup>n+1\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>n\<^esup>"

text \<open>We tried to dualise using sublocales, but this causes an infinite loop on dual.dual.dual....\<close>

lemma (in conway_dioid) C11_var: "(x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
proof -
  have "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star> + x\<^sup>\<star> \<cdot> y \<cdot> (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    by (metis C12 distrib_left mult.assoc mult_oner)   
  also have "... = (1 +  x\<^sup>\<star> \<cdot> y \<cdot> (x\<^sup>\<star> \<cdot> y)\<^sup>\<star>) \<cdot> x\<^sup>\<star>"
    by (metis distrib_right mult.assoc mult_onel)
  finally show ?thesis
    by (metis C11 C12 mult_onel mult_oner)
qed

lemma (in conway_dioid) dual_conway_dioid:
  "class.conway_dioid (+) (\<odot>) 1 0 (\<le>) (<) star"
proof
  fix x y z :: 'a
  show "(x \<odot> y) \<odot> z = x \<odot>(y \<odot> z)"
    by (metis mult.assoc opp_mult_def)
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distrib_left opp_mult_def)
  show "x + x = x"
    by (metis add_idem)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
    by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (metis add_zerol)
  show "0 \<odot> x = 0"
    by (metis annir times.opp_mult_def)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis opp_mult_def distrib_right')
  show "x \<odot> 0 = 0"
    by (metis annil opp_mult_def)
  show "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<odot> y)\<^sup>\<star> \<odot> x\<^sup>\<star>"
    by (metis C11_var opp_mult_def)
  show "(x \<odot> y)\<^sup>\<star> = 1 + x \<odot> (y \<odot> x)\<^sup>\<star> \<odot> y"
    by (metis C12 mult.assoc opp_mult_def)
qed

lemma (in strong_conway_dioid) dual_strong_conway_dioid: "class.strong_conway_dioid ((+) ) ((\<odot>) ) 1 0 (\<le>) (<) star"
proof
  fix x y z :: 'a
  show "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult.assoc opp_mult_def)
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distrib_left opp_mult_def)
  show "x + x = x"
    by (metis add_idem)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
    by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (metis add_zerol)
  show "0 \<odot>  x = 0"
    by (metis annir opp_mult_def)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis opp_mult_def distrib_right')
  show "x \<odot> 0 = 0"
    by (metis annil opp_mult_def)
  show "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<odot> y)\<^sup>\<star> \<odot> x\<^sup>\<star>"
    by (metis C11_var opp_mult_def)
  show "(x \<odot> y)\<^sup>\<star> = 1 + x \<odot> (y \<odot> x)\<^sup>\<star> \<odot> y"
    by (metis C12 mult.assoc opp_mult_def)
  show "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>" 
    by (metis C13)
qed

text\<open>Nitpick finds counterexamples to the following claims.\<close>

lemma (in conway_dioid) "1\<^sup>\<star> = 1"
  nitpick [expect=genuine] \<comment> \<open>3-element counterexample\<close>
oops

lemma (in conway_dioid) "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"
  nitpick [expect=genuine] \<comment> \<open>3-element counterexample\<close>
oops

context C_algebra
begin

lemma C_unfoldl [simp]: "1 + x \<cdot>  x\<^sup>\<star> =  x\<^sup>\<star>"
  by (metis C12 mult_onel mult_oner)

lemma C_slide: "(x \<cdot> y)\<^sup>\<star> \<cdot> x = x \<cdot> (y \<cdot> x)\<^sup>\<star>"
proof-
  have "(x \<cdot> y)\<^sup>\<star> \<cdot> x = x + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y \<cdot> x"
    by (metis C12 mult_onel distrib_right')
  also have "... = x \<cdot> (1 + (y \<cdot> x)\<^sup>\<star> \<cdot> y \<cdot> x)"
    by (metis distrib_left mult.assoc mult_oner)
  finally show ?thesis
    by (metis C12 mult.assoc mult_onel mult_oner)
qed

lemma powsum_ub: "i \<le> n \<Longrightarrow> x\<^bsup>i\<^esup> \<le> x\<^bsub>0\<^esub>\<^bsup>n\<^esup>"
proof (induct n)
  case 0 show ?case
    by (metis (hide_lams, mono_tags) "0.prems" eq_iff le_0_eq power_0 powsum_00)
next
  case (Suc n) show ?case
proof -
  { assume aa1: "Suc n \<noteq> i"
    have ff1: "x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup> \<le> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup> \<and> Suc n \<noteq> i"
      using aa1 by fastforce
    have ff2: "\<exists>x\<^sub>1. x\<^bsub>0\<^esub>\<^bsup>n\<^esup> + x\<^sub>1 \<le> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup> \<and> Suc n \<noteq> i"
      using ff1 powsum2 by auto
    have "x\<^bsup>i\<^esup> \<le> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup>"
      by (metis Suc.hyps Suc.prems ff2 le_Suc_eq local.dual_order.trans local.join.le_supE)
  }
  thus "x\<^bsup>i\<^esup> \<le> x\<^bsub>0\<^esub>\<^bsup>Suc n\<^esup>"
    using local.less_eq_def local.powsum_split_var2 by blast
qed
qed

lemma C14_aux: "m \<le> n \<Longrightarrow>  x\<^bsup>m\<^esup> \<cdot> (x\<^bsup>n\<^esup>)\<^sup>\<star> = (x\<^bsup>n\<^esup>)\<^sup>\<star> \<cdot> x\<^bsup>m\<^esup>"
proof -
  assume assm: "m \<le> n"
  hence "x\<^bsup>m\<^esup> \<cdot>  (x\<^bsup>n\<^esup>)\<^sup>\<star> =  x\<^bsup>m\<^esup> \<cdot> (x\<^bsup>n-m\<^esup> \<cdot> x\<^bsup>m\<^esup>)\<^sup>\<star>"
    by (metis (full_types) le_add_diff_inverse2 power_add)
  also have "... = (x\<^bsup>n-m\<^esup> \<cdot> x\<^bsup>m\<^esup>)\<^sup>\<star> \<cdot>  x\<^bsup>m\<^esup>"
    by (metis (hide_lams, mono_tags) C_slide ab_semigroup_add_class.add.commute power_add)
  finally show ?thesis
    by (metis (full_types) assm le_add_diff_inverse ab_semigroup_add_class.add.commute power_add)
qed

end

context dioid_one_zero
begin

lemma opp_power_def:
  "power.power 1 (\<odot>) x n = x\<^bsup>n\<^esup>"
proof (induction n)
  case 0 thus ?case
    by (metis power.power.power_0)
next
  case (Suc n) thus ?case
    by (metis power.power.power_Suc power_Suc2 times.opp_mult_def)
qed

lemma opp_powsum_def: 
  "dioid_one_zero.powsum (+) (\<odot>) 1 0 x m n = x\<^bsub>m\<^esub>\<^bsup>n\<^esup>"
proof -
  have "sum (power.power 1 (\<odot>) x) {m..n + m} = sum ((^) x) {m..n + m}"
    by (induction n, simp_all add:opp_power_def)
  thus ?thesis
    by (simp add: dioid_one_zero.powsum_def[of _ _ _ _ "(\<le>)" "(<)"] dual_dioid_one_zero powsum_def)
qed

end

lemma C14_dual: 
  fixes x::"'a::C_algebra"
  shows "x\<^sup>\<star> = x\<^bsub>0\<^esub>\<^bsup>n\<^esup> \<cdot> (x\<^bsup>n+1\<^esup>)\<^sup>\<star>"
proof -
  have "x\<^sup>\<star> =  (x\<^bsup>n+1\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>n\<^esup>"
    by (rule C14)
  also have "... = (x\<^bsup>n+1\<^esup>)\<^sup>\<star> \<cdot> (\<Sum>i=0..n. x^i)"
    by (subst powsum_def, auto)
  also have "... = (\<Sum>i=0..n. (x\<^bsup>n+1\<^esup>)\<^sup>\<star> \<cdot> x^i)"
    by (metis le0 sum_interval_distl)
  also have "... = (\<Sum>i=0..n. x^i \<cdot> (x\<^bsup>n+1\<^esup>)\<^sup>\<star>)"
    by (auto intro: sum_interval_cong simp only:C14_aux)
  also have "... = x\<^bsub>0\<^esub>\<^bsup>n\<^esup> \<cdot> (x\<^bsup>n+1\<^esup>)\<^sup>\<star>"
    by (simp only: sum_interval_distr[THEN sym] powsum_def Nat.add_0_right)
  finally show ?thesis .
qed

lemma C_algebra: "class.C_algebra (+) (\<odot>) (1::'a::C_algebra) 0 (\<le>) (<) star"
proof
  fix x y :: 'a and n :: nat
  show "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<odot> y)\<^sup>\<star> \<odot> x\<^sup>\<star>"
    by (metis C11_var opp_mult_def)
  show "(x \<odot> y)\<^sup>\<star> = 1 + x \<odot> (y \<odot> x)\<^sup>\<star> \<odot> y"
    by (metis C12 mult.assoc opp_mult_def)
  show "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"
    by (metis C13)
  show "x\<^sup>\<star> = power.power 1 (\<odot>) x (n + 1)\<^sup>\<star> \<odot> dioid_one_zero.powsum (+) (\<odot>) 1 0 x 0 n"
    by (metis C14_dual opp_mult_def opp_power_def opp_powsum_def)
qed (simp_all add: opp_mult_def mult.assoc distrib_left)

subsection \<open>Boffa's Axioms\<close>

text \<open>Boffa's two axiomatisations of Regular Algebra from~\cite{Boffa1,Boffa2}.\<close>

class B1_algebra = conway_dioid +
  assumes R: "x \<cdot> x = x \<Longrightarrow> x\<^sup>\<star> = 1 + x"

class B2_algebra = star_dioid +
  assumes B21: "1 + x \<le> x\<^sup>\<star>"
  and B22 [simp]: "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
  and B23: "\<lbrakk> 1 + x \<le> y; y \<cdot> y = y \<rbrakk> \<Longrightarrow> x\<^sup>\<star> \<le> y"

lemma (in B1_algebra) B1_algebra:
  "class.B1_algebra (+) (\<odot>) 1 0 (\<le>) (<) star"
proof 
  fix x y z :: 'a
  show "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult.assoc opp_mult_def)
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distrib_left opp_mult_def)
  show "x + x = x"
    by (metis add_idem)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
    by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (metis add_zerol)
  show "0 \<odot> x = 0"
    by (metis annir opp_mult_def)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis distrib_right opp_mult_def)
  show "x \<odot> 0 = 0"
    by (metis annil opp_mult_def)
  show "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<odot> y)\<^sup>\<star> \<odot> x\<^sup>\<star>"
    by (metis C11_var opp_mult_def)
  show "(x \<odot> y)\<^sup>\<star> = 1 + x \<odot> (y \<odot> x)\<^sup>\<star> \<odot> y"
    by (metis C12 mult.assoc opp_mult_def)
  show "x \<odot> x = x \<Longrightarrow> x\<^sup>\<star> = 1 + x"
    by (metis R opp_mult_def)
qed

lemma (in B2_algebra) B2_algebra:
  "class.B2_algebra (+) (\<odot>) 1 0 (\<le>) (<) star"
proof
  fix x y z :: 'a
  show "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult.assoc opp_mult_def)
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distrib_left times.opp_mult_def)
  show "x + x = x"
    by (metis add_idem)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (metis add_zerol)
  show "0 \<odot> x = 0"
    by (metis annir opp_mult_def)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis distrib_right opp_mult_def)
  show "x \<odot> 0 = 0"
    by (metis annil opp_mult_def)
  show "1 + x \<le> x\<^sup>\<star>"
    by (metis B21)
  show "x\<^sup>\<star> \<odot> x\<^sup>\<star> = x\<^sup>\<star>"
    by (metis B22 opp_mult_def)
  show "\<lbrakk> 1 + x \<le> y; y \<odot> y = y \<rbrakk> \<Longrightarrow> x\<^sup>\<star> \<le> y"
    by (metis B23 opp_mult_def) 
qed

instance B1_algebra \<subseteq> B2_algebra 
proof
  fix x y :: 'a
  show "1 + x \<le> x\<^sup>\<star>"
    by (metis C12 add_iso_r distrib_right join.sup.cobounded1 mult_onel)
  show two: "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
    by (metis (no_types, lifting) C11_var C12 R add_idem' mult_onel mult_oner)
  show "\<lbrakk> 1 + x \<le> y; y \<cdot> y = y \<rbrakk> \<Longrightarrow> x\<^sup>\<star> \<le> y"
    by (metis (no_types, lifting) C11_var R two distrib_left join.sup.bounded_iff less_eq_def mult.assoc mult.right_neutral)
qed

context B2_algebra
begin

lemma star_ref: "1 \<le> x\<^sup>\<star>"
  using local.B21 by auto

lemma star_plus_one [simp]: "1 + x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis less_eq_def star_ref)

lemma star_trans: "x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis B22 order_refl)

lemma star_trans_eq [simp]: "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis B22)

lemma star_invol [simp]: "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"
  by (metis B21 B22 B23 antisym star_plus_one)
 
lemma star_1l: "x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis local.B21 local.join.sup.boundedE local.mult_isor local.star_trans_eq)

lemma star_one [simp]: "1\<^sup>\<star> = 1"
  by (metis B23 add_idem antisym mult_oner order_refl star_ref)

lemma star_subdist:  "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
  by (meson local.B21 local.B23 local.join.sup.bounded_iff local.star_trans_eq)

lemma star_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
  by (metis less_eq_def star_subdist)

lemma star2: "(1 + x)\<^sup>\<star> = x\<^sup>\<star>"
  by (metis B21 add.commute less_eq_def star_invol star_subdist) 

lemma star_unfoldl: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis local.join.sup.bounded_iff star_1l star_ref)

lemma star_unfoldr: "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  by (metis (full_types) B21 local.join.sup.bounded_iff mult_isol star_trans_eq)

lemma star_ext: "x \<le> x\<^sup>\<star>"
  by (metis B21 local.join.sup.bounded_iff)

lemma star_1r: "x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  by (metis mult_isol star_ext star_trans_eq)

lemma star_unfoldl_eq [simp]: "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
proof -
  have "(1 + x \<cdot> x\<^sup>\<star>) \<cdot> (1 + x \<cdot> x\<^sup>\<star>) = 1 \<cdot> (1 + x \<cdot> x\<^sup>\<star>) + x \<cdot> x\<^sup>\<star> \<cdot> (1 + x \<cdot> x\<^sup>\<star>)"
    by (metis distrib_right)
  also have "... = 1 + x \<cdot> x\<^sup>\<star> + (x \<cdot> x\<^sup>\<star> \<cdot> x \<cdot> x\<^sup>\<star>)"
    by (metis add_assoc' add_idem' distrib_left mult.assoc mult_onel mult_oner)
  also have "... = 1 + x \<cdot> x\<^sup>\<star>"
    by (metis add.assoc add.commute distrib_left less_eq_def mult.assoc star_1l star_trans_eq)
  finally show ?thesis
    by (metis B23 local.join.sup.mono local.join.sup.cobounded1 distrib_left eq_iff mult_1_right star_plus_one star_unfoldl)
qed

lemma star_unfoldr_eq [simp]: "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
proof -
  have "(1 + x\<^sup>\<star> \<cdot> x) \<cdot> (1 + x\<^sup>\<star> \<cdot> x) = 1 \<cdot> (1 + x\<^sup>\<star> \<cdot> x) + x\<^sup>\<star> \<cdot> x \<cdot> (1 + x\<^sup>\<star> \<cdot> x)"
    by (metis distrib_right)
  also have "... = 1 + x\<^sup>\<star> \<cdot> x + (x\<^sup>\<star> \<cdot> x \<cdot> x\<^sup>\<star> \<cdot> x)"
    by (metis add.assoc add_idem' distrib_left mult_1_left mult_1_right mult.assoc)
  also have "... = 1 + x\<^sup>\<star> \<cdot>x"
    by (metis add_assoc' distrib_left mult.assoc mult_oner distrib_right' star_trans_eq star_unfoldl_eq)
  finally show ?thesis
    by (metis B21 B23 add.commute local.join.sup.mono local.join.sup.cobounded1 eq_iff eq_refl mult_1_left distrib_right' star_unfoldl_eq star_unfoldr)
qed                                          

lemma star_prod_unfold_le: "(x \<cdot> y)\<^sup>\<star> \<le> 1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y"
proof -
  have "(1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y) \<cdot> (1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y) = 
        1 \<cdot> (1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y) + (x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y) \<cdot> (1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y)"
    by (metis distrib_right')
  also have "... = 1 + x \<cdot>(y \<cdot> x)\<^sup>\<star> \<cdot> y + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y \<cdot> x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y"
    by (metis add.assoc local.join.sup.cobounded1  distrib_left less_eq_def mult_1_right mult.assoc mult_onel)
  finally have "(1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y) \<cdot> (1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y) = 1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y"
    by (metis add.assoc  distrib_left distrib_right mult.assoc mult_oner star_trans_eq star_unfoldr_eq)
  moreover have "(x \<cdot> y) \<le> 1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y"
    by (metis local.join.sup.cobounded2 mult_1_left mult.assoc mult_double_iso order_trans star_ref)
  ultimately show ?thesis
    by (simp add: local.B23)
qed

lemma star_prod_unfold [simp]: " 1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y = (x \<cdot> y)\<^sup>\<star>"
proof -
  have "1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y \<le> 1 + x \<cdot> (1 + y \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> x) \<cdot> y"
    by (metis local.join.sup.mono mult_double_iso order_refl star_prod_unfold_le)
  also have "... = 1 + x \<cdot> y + x \<cdot> y \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> x \<cdot> y"
    by (metis add.assoc distrib_left mult_1_left mult.assoc distrib_right')
  finally have "1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y \<le> (x \<cdot> y)\<^sup>\<star>"
    by (metis add.assoc distrib_left mult_1_right mult.assoc star_unfoldl_eq star_unfoldr_eq)
  thus ?thesis
    by (metis antisym star_prod_unfold_le)
qed

lemma star_slide1: "(x \<cdot> y)\<^sup>\<star> \<cdot> x \<le> x \<cdot> (y \<cdot> x)\<^sup>\<star>"
proof -
  have "(x \<cdot> y)\<^sup>\<star> \<cdot> x = (1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y) \<cdot> x"
    by (metis star_prod_unfold)
  also have "... = (x + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y \<cdot> x)"
    by (metis mult_onel distrib_right')
  also have "... = x \<cdot> (1 + (y \<cdot> x)\<^sup>\<star> \<cdot> y \<cdot> x)"
    by (metis distrib_left mult.assoc mult_oner)
  finally show ?thesis
    by (metis eq_refl mult.assoc star_unfoldr_eq)
qed

lemma star_slide_var1: "x\<^sup>\<star> \<cdot> x \<le> x \<cdot> x\<^sup>\<star>"
  by (metis mult_onel mult_oner star_slide1)

lemma star_slide: "(x \<cdot> y)\<^sup>\<star> \<cdot> x = x \<cdot> (y \<cdot> x)\<^sup>\<star>"
proof (rule antisym)
  show "(x \<cdot> y)\<^sup>\<star> \<cdot> x \<le> x \<cdot> (y \<cdot> x)\<^sup>\<star>"
    by (metis star_slide1)
  have "x \<cdot> (y \<cdot> x)\<^sup>\<star> = x \<cdot> (1 + y \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> x)"
    by (metis star_prod_unfold)
  also have "... = x + x \<cdot> y \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> x"
    by (metis distrib_left mult.assoc mult_oner)
  also have "... = (1 + x \<cdot> y \<cdot> (x \<cdot> y)\<^sup>\<star>) \<cdot> x"
    by (metis mult_onel distrib_right')
  finally show "x \<cdot> (y \<cdot> x)\<^sup>\<star> \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> x"
    by (metis mult_isor star_unfoldl)
qed

lemma star_rtc1: "1 + x + x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  using local.B21 local.join.sup_least local.star_trans by blast

lemma star_rtc1_eq: "1 + x + x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis B21 B22 less_eq_def)

lemma star_subdist_var_1: "x \<le> (x + y)\<^sup>\<star>"
  using local.join.le_supE local.star_ext by blast

lemma star_subdist_var_2: "x \<cdot> y \<le> (x + y)\<^sup>\<star>"
  by (metis (full_types) local.join.le_supE mult_isol_var star_ext star_trans_eq)

lemma star_subdist_var_3: "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
  by (metis add.commute mult_isol_var star_subdist star_trans_eq)

lemma R_lemma: 
  assumes "x \<cdot> x = x" 
  shows "x\<^sup>\<star> = 1 + x"
proof (rule antisym)
  show "1 + x \<le> x\<^sup>\<star>"
    by (metis B21)
  have "(1 + x) \<cdot> (1 + x) = 1 + x"
    by (metis add.commute add_idem' add.left_commute assms distrib_left mult_onel mult_oner distrib_right')
  thus "x\<^sup>\<star> \<le> 1 + x"
    by (metis B23 order_refl)
qed

lemma star_denest_var_0: "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
proof (rule antisym)
  have one_below: "1 \<le> (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    by (metis mult_isol_var star_one star_ref star_trans_eq)
  have x_below: "x \<le> (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    by (metis mult_isol mult_oner order_trans star_ext star_ref star_slide)
  have y_below: "y \<le> (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    by (metis mult_isol_var mult_onel mult_oner order_trans star_ext star_slide star_unfoldl_eq subdistl)
  from one_below x_below y_below have "1 + x + y \<le> (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    by simp
    moreover have "(x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    by (metis star_trans_eq star_slide mult.assoc)
  ultimately show "(x + y)\<^sup>\<star> \<le> (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    by (metis B23 add_assoc' mult.assoc)
  show "(x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (metis (full_types) add.commute mult_isol_var star_invol star_iso star_subdist_var_1 star_trans_eq)
qed

lemma star_denest: "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  by (metis R_lemma add.commute star_denest_var_0 star_plus_one star_prod_unfold star_slide star_trans_eq)

lemma star_sum_var: "(x + y)\<^sup>\<star>  = (x\<^sup>\<star> + y\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest star_invol)

lemma star_denest_var: "(x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest_var_0 star_slide) 

lemma star_denest_var_2: "(x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest star_denest_var)

lemma star_denest_var_3: "(x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star> \<cdot> (y\<^sup>\<star> \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
  by (metis B22 add_comm mult.assoc star_denest star_denest_var_2)

lemma star_denest_var_4:  "(x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> = (y\<^sup>\<star> \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
  by (metis add_comm star_denest)

lemma star_denest_var_5: "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> = y\<^sup>\<star> \<cdot> (x \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  by (metis add.commute star_denest_var)

lemma star_denest_var_6: "(x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> (x + y)\<^sup>\<star>"
  by (metis mult.assoc star_denest star_denest_var_3)

lemma star_denest_var_7: "(x + y)\<^sup>\<star> = (x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis star_denest star_denest_var star_denest_var_3 star_denest_var_5 star_slide)

lemma star_denest_var_8: "(x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest star_denest_var_6)

lemma star_denest_var_9: " (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> = (x \<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis star_denest star_denest_var_7)

lemma star_slide_var: "x\<^sup>\<star> \<cdot> x = x \<cdot> x\<^sup>\<star>"
  by (metis mult_1_left mult_oner star_slide)

lemma star_sum_unfold: "(x + y)\<^sup>\<star> = x\<^sup>\<star> + x\<^sup>\<star> \<cdot> y \<cdot> (x + y)\<^sup>\<star>"
  by (metis distrib_left mult_1_right mult.assoc star_denest_var star_unfoldl_eq) 

lemma troeger: "x\<^sup>\<star> \<cdot> (y \<cdot> ((x + y)\<^sup>\<star> \<cdot> z) + z) = (x + y)\<^sup>\<star> \<cdot> z"
proof -
  have "x\<^sup>\<star> \<cdot> (y \<cdot> ((x + y)\<^sup>\<star> \<cdot> z) + z) = (x\<^sup>\<star> + x\<^sup>\<star> \<cdot> y \<cdot> (x + y)\<^sup>\<star>) \<cdot> z"
    by (metis add_comm distrib_left mult.assoc distrib_right')
  thus ?thesis
    by (metis star_sum_unfold)
qed

lemma meyer_1: "x\<^sup>\<star> = (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star>" 
proof (rule antisym)
  have "(1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> \<cdot> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> = ((x \<cdot> x)\<^sup>\<star> + x \<cdot> (x \<cdot> x)\<^sup>\<star>) \<cdot> ((x \<cdot> x)\<^sup>\<star> + x \<cdot> (x \<cdot> x)\<^sup>\<star>)"
    by (metis mult.assoc mult_onel distrib_right')
  also have "... = ((x \<cdot> x)\<^sup>\<star> + x \<cdot> (x \<cdot> x)\<^sup>\<star>) \<cdot> (x \<cdot> x)\<^sup>\<star> + ((x \<cdot> x)\<^sup>\<star> + x \<cdot> (x \<cdot> x)\<^sup>\<star>) \<cdot> x \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis distrib_left mult.assoc)
  also have "... = (x \<cdot> x) \<^sup>\<star> \<cdot> (x \<cdot> x)\<^sup>\<star> + x \<cdot> (x \<cdot> x)\<^sup>\<star> \<cdot> (x \<cdot> x)\<^sup>\<star> + (x \<cdot> x)\<^sup>\<star> \<cdot> x \<cdot> (x \<cdot> x)\<^sup>\<star> + x \<cdot> (x \<cdot> x)\<^sup>\<star> \<cdot> x \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis combine_common_factor distrib_right)
  also have "... = (x \<cdot> x)\<^sup>\<star> + x \<cdot> (x \<cdot> x)\<^sup>\<star> + x \<cdot> x \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis add.assoc add_idem' mult.assoc star_slide star_trans_eq)
  also have "... = 1 + x \<cdot> x \<cdot> (x \<cdot> x)\<^sup>\<star> + x \<cdot> (x \<cdot> x)\<^sup>\<star> + x \<cdot> x \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis star_unfoldl_eq)
  also have "... = (x \<cdot> x)\<^sup>\<star> + x \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis add_comm add_idem' add.left_commute star_unfoldl_eq)
    finally have "(1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> \<cdot> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> = (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis mult_1_left distrib_right')
  moreover have "1 + x \<le> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis mult_1_right star_unfoldl_eq subdistl)
  ultimately show "x\<^sup>\<star> \<le> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis B23 mult.assoc)
next
  have "(1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> = (x \<cdot> x)\<^sup>\<star> + x \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis mult_1_left distrib_right')
  thus "(1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis local.add_zeror local.join.sup_least local.mult_isol_var local.mult_oner local.star_ext local.star_invol local.star_iso local.star_subdist_var_2 local.star_trans_eq local.subdistl_eq)
qed

lemma star_zero [simp]: "0\<^sup>\<star> = 1"
  by (metis add_zeror star2 star_one)

lemma star_subsum [simp]: "x\<^sup>\<star> + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
  by (metis add.assoc add_idem star_slide_var star_unfoldl_eq)

lemma prod_star_closure: "x \<le> z\<^sup>\<star> \<Longrightarrow> y \<le> z\<^sup>\<star> \<Longrightarrow> x \<cdot> y \<le> z\<^sup>\<star>"
  by (metis mult_isol_var star_trans_eq)

end

sublocale B2_algebra \<subseteq> B1_algebra
  by unfold_locales (metis star_denest_var_0, metis star_prod_unfold, metis R_lemma)

context B2_algebra
begin

lemma power_le_star: "x\<^bsup>n\<^esup> \<le> x\<^sup>\<star>" 
  by (induct n, simp_all add: star_ref prod_star_closure star_ext) 

lemma star_power_slide: 
  assumes "k \<le> n" 
  shows "x\<^bsup>k \<^esup>\<cdot> (x\<^bsup>n\<^esup>)\<^sup>\<star> = (x\<^bsup>n\<^esup>)\<^sup>\<star> \<cdot> x\<^bsup>k\<^esup>"  
proof -
  from assms have "x\<^bsup>k \<^esup>\<cdot> (x\<^bsup>n\<^esup>)\<^sup>\<star> = (x\<^bsup>k \<^esup>\<cdot> x\<^bsup>n-k\<^esup>)\<^sup>\<star> \<cdot> x\<^bsup>k\<^esup>"
    by (metis (full_types) le_add_diff_inverse2 power_add star_slide)
  with assms show ?thesis 
    by (metis (full_types) le_add_diff_inverse2 ab_semigroup_add_class.add.commute power_add)
qed

lemma powsum_le_star: "x\<^bsub>m\<^esub>\<^bsup>n\<^esup> \<le> x\<^sup>\<star>"
  by (induct n, simp_all add:  powsum2, metis power_le_star, metis  power_Suc power_le_star)

lemma star_sum_power_slide: 
  assumes "m \<le> n"
  shows "x\<^bsub>0\<^esub>\<^bsup>m  \<^esup>\<cdot> (x\<^bsup>n\<^esup>)\<^sup>\<star> = (x\<^bsup>n\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>m\<^esup>" 
using assms
proof (induct m)
  case 0 thus ?case
    by (metis mult_onel mult_oner powsum_00)
next
  case (Suc m) note hyp = this
  have "x\<^bsub>0\<^esub>\<^bsup>Suc m\<^esup> \<cdot> (x\<^bsup>n\<^esup>)\<^sup>\<star> = (x\<^bsub>0\<^esub>\<^bsup>m\<^esup> + x\<^bsup>Suc m\<^esup>) \<cdot> (x\<^bsup>n\<^esup>)\<^sup>\<star>"
    by (simp add:powsum2)
  also have "... = x\<^bsub>0\<^esub>\<^bsup>m \<^esup>\<cdot> (x\<^bsup>n\<^esup>)\<^sup>\<star> + x\<^bsup>Suc m \<^esup>\<cdot> (x\<^bsup>n\<^esup>)\<^sup>\<star>"
    by (metis distrib_right')
  also have "... = (x\<^bsup>n\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>m\<^esup> + x\<^bsup>Suc m \<^esup>\<cdot> (x\<^bsup>n\<^esup>)\<^sup>\<star>"
    by (metis Suc.hyps Suc.prems Suc_leD)
  also have "... = (x\<^bsup>n\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>m\<^esup> + (x\<^bsup>n\<^esup>)\<^sup>\<star> \<cdot> x\<^bsup>Suc m\<^esup>"
    by (metis Suc.prems star_power_slide) 
  also have "... = (x\<^bsup>n\<^esup>)\<^sup>\<star> \<cdot> (x\<^bsub>0\<^esub>\<^bsup>m\<^esup> + x\<^bsup>Suc m\<^esup>)"
    by (metis distrib_left)
  finally show ?case
    by (simp add:powsum2)
qed

lemma aarden_aux:
  assumes "y \<le> y \<cdot> x + z"
  shows "y \<le> y \<cdot> x\<^bsup>(Suc n) \<^esup>+ z \<cdot> x\<^sup>\<star>"
proof (induct n)
  case 0
  have "y \<cdot> x + z \<le> y \<cdot> x\<^bsup>(Suc 0)\<^esup>+ z \<cdot> x\<^sup>\<star>"
    by (metis (mono_tags) One_nat_def add.commute add_iso mult_1_right power_one_right star_plus_one subdistl)
  thus ?case
    by (metis assms order_trans)
next
  case (Suc n)
  have "y \<cdot> x + z \<le> (y \<cdot> x\<^bsup>(Suc n) \<^esup>+ z \<cdot> x\<^sup>\<star>) \<cdot> x + z"
    by (metis Suc add_iso mult_isor)
  also have "... = y \<cdot> x\<^bsup>(Suc n) \<^esup>\<cdot> x + z \<cdot> (x\<^sup>\<star> \<cdot> x + 1)"
    by (subst distrib_right, metis add_assoc' distrib_left mult.assoc mult_oner)
  finally show ?case
    by (metis add.commute assms mult.assoc order_trans power_Suc2 star_unfoldr_eq)
qed

lemma conway_powerstar1: "(x\<^bsup>n+1\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>n \<^esup>\<cdot> (x\<^bsup>n+1\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>n\<^esup>  = (x\<^bsup>n+1\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>n\<^esup>"
proof (cases n)
  case 0 thus ?thesis
    by simp
next
  case (Suc m) thus ?thesis
  proof -
    assume assm: "n = Suc m"
    have "(x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>m+1 \<^esup>\<cdot> (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>m+1\<^esup>  = (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>m+1 \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>m+1\<^esup>"
      by (subgoal_tac "m + 1 \<le> m + 2", metis mult.assoc star_sum_power_slide, simp)
    also have "...  = (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>m+1 \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>m+1\<^esup>"
      by (metis star_trans_eq)
    also have "...  =  (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>(Suc m)+(Suc m)\<^esup>"
      by (simp add: mult.assoc powsum_prod)
    also have "... =  (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> (x\<^bsub>0\<^esub>\<^bsup>Suc m \<^esup>+ x\<^bsub>m + 2\<^esub>\<^bsup>m\<^esup>)"
      by (metis monoid_add_class.add.left_neutral powsum_split_var3 add_2_eq_Suc')
    also have "... =  (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>Suc m \<^esup>+ (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>(m + 2)+ 0\<^esub>\<^bsup>m\<^esup>"
     by (simp add: local.distrib_left)
    also have "... =  (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>Suc m \<^esup>+ (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsup>m+2 \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>m\<^esup>"
      by (subst powsum_shift[THEN sym], metis mult.assoc)
   also have "... =  (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> (x\<^bsub>0\<^esub>\<^bsup>m \<^esup>+  x\<^bsup>m+1\<^esup>) + (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsup>m+2 \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>m\<^esup>"
     by (simp add:powsum2)
   also have "... =  (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>m \<^esup>+ (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsup>m+2 \<^esup>\<cdot> x\<^bsub>0\<^esub>\<^bsup>m \<^esup>+ (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsup>m+1\<^esup>"
     by (metis add.assoc add.commute add.left_commute distrib_left mult.assoc)
   also have "... =  (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>m \<^esup>+ (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>m \<^esup>+ (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsup>m+1\<^esup>"
     by (metis add_idem' distrib_right' star_subsum)
   also have "... =  (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> (x\<^bsub>0\<^esub>\<^bsup>m \<^esup>+ x\<^bsup>m+1\<^esup>)"
     by (metis add_idem' distrib_left)
    also have "... = (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>m+1\<^esup>"
      by (simp add:powsum2)
    finally  show ?thesis 
      by (simp add: assm)
  qed
qed

lemma conway_powerstar2: "1 + x \<le> (x\<^bsup>n+1\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>n\<^esup>"
proof (cases n)
  case 0 show ?thesis
    using "0" local.B21 by auto
next
  case (Suc m) show ?thesis
  proof -
    have one: "x \<le> (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>m+1\<^esup>"
      by (metis Suc_eq_plus1 powsum_ext  mult_isor mult_onel order_trans star_ref)
    have two: "1 \<le> (x\<^bsup>m+2\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>m+1\<^esup>"
      by (metis Suc_eq_plus1 local.join.le_supE mult_isor mult_onel powsum_split_var1 star_ref)
    from one two show ?thesis
      by (metis Suc Suc_eq_plus1 add_2_eq_Suc' local.join.sup_least)
  qed
qed

theorem powerstar: "x\<^sup>\<star> = (x\<^bsup>n+1\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>n\<^esup>"
proof (rule antisym) 
  show "x\<^sup>\<star> \<le> (x\<^bsup>n+1\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>n\<^esup>"
    by (metis conway_powerstar1 conway_powerstar2 mult.assoc B23)
  have "(x\<^bsup>n+1\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>n\<^esup> \<le> (x\<^sup>\<star>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>n\<^esup>"
    by (metis mult_isor power_le_star star_iso)
  also have "... = x\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>n\<^esup>"
    by (metis star_invol)
  also have "... \<le> x\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    by (simp add: local.prod_star_closure powsum_le_star)
  finally show "(x\<^bsup>n+1\<^esup>)\<^sup>\<star> \<cdot> x\<^bsub>0\<^esub>\<^bsup>n \<^esup>\<le> x\<^sup>\<star>"
    by (metis star_trans_eq)
qed

end

sublocale B2_algebra \<subseteq> strong_conway_dioid  
  by  unfold_locales (metis star_invol)

sublocale B2_algebra \<subseteq> C_algebra
  by unfold_locales (metis powerstar)

text \<open>The following fact could neither be verified nor falsified in Isabelle. It does not hold for other reasons.\<close>

lemma (in C_algebra) "x\<cdot>x = x \<longrightarrow> x\<^sup>\<star> = 1+x"
oops

subsection \<open>Boffa Monoid Identities\<close>

typedef ('a , 'b) boffa_mon = "{f :: 'a::{finite,monoid_mult}  \<Rightarrow> 'b::B1_algebra. True}"
  by auto

notation
  Rep_boffa_mon ("_\<^bsub>_\<^esub>")

lemma "finite (range (Rep_boffa_mon M))"
  by (metis finite_code finite_imageI)

abbreviation boffa_pair :: "('a, 'b) boffa_mon \<Rightarrow> 'a::{finite,monoid_mult} \<Rightarrow> 'a \<Rightarrow> 'b::B1_algebra" where
  "boffa_pair x i j \<equiv> \<Sum> { x\<^bsub>k\<^esub> | k. i\<cdot>k = j}"

notation
  boffa_pair ("_\<^bsub>_,_\<^esub>")

abbreviation conway_assms where
  "conway_assms x \<equiv> (\<forall> i j. (x\<^bsub>i \<^esub>\<cdot> x\<^bsub>j\<^esub> \<le> x\<^bsub>i\<cdot>j\<^esub>) \<and> (x\<^bsub>i,i\<^esub>)\<^sup>\<star> = x\<^bsub>i,i\<^esub>)"

lemma pair_one: "x\<^bsub>1,1\<^esub> = x\<^bsub>1\<^esub>"
  by (simp)

definition conway_assm1 where "conway_assm1 x = (\<forall> i j. x\<^bsub>i \<^esub>\<cdot> x\<^bsub>j\<^esub> \<le> x\<^bsub>i\<cdot>j\<^esub>)" 
definition conway_assm2 where "conway_assm2 x = (\<forall>i. x\<^bsub>i,i\<^esub>\<^sup>\<star> = x\<^bsub>i,i\<^esub>)"

lemma pair_star:
  assumes "conway_assm2 x"
  shows "x\<^bsub>1\<^esub>\<^sup>\<star> = x\<^bsub>1\<^esub>"
proof -
  have "x\<^bsub>1\<^esub>\<^sup>\<star> = x\<^bsub>1,1\<^esub>\<^sup>\<star>"
    by simp
  also from assms have "... = x\<^bsub>1,1\<^esub>"
    by (metis (mono_tags) conway_assm2_def)
  finally show ?thesis
    by simp
qed

lemma conway_monoid_one: 
  assumes "conway_assm2 x"
  shows "x\<^bsub>1\<^esub> = 1 + x\<^bsub>1\<^esub>"
proof -
  from assms have "x\<^bsub>1\<^esub> = x\<^bsub>1\<^esub>\<^sup>\<star>"
    by (metis pair_star)
  thus ?thesis
    by (metis star_plus_one)
qed

lemma conway_monoid_split: 
  assumes "conway_assm2 x"
  shows "\<Sum> {x\<^bsub>i \<^esub>| i . i \<in> UNIV} = 1 + \<Sum> {x\<^bsub>i \<^esub>| i . i \<in> UNIV}"
proof -
  have "\<Sum> {x\<^bsub>i \<^esub>| i . i \<in> UNIV} = \<Sum> {x\<^bsub>i \<^esub>| i . i \<in> (insert 1 (UNIV - {1}))}"
    by (metis UNIV_I insert_Diff_single insert_absorb)
  also have "... = \<Sum> (Rep_boffa_mon x ` (insert 1 (UNIV - {1})))"
    by (metis fset_to_im)
  also have "... = x\<^bsub>1\<^esub> + \<Sum> (Rep_boffa_mon x ` (UNIV - {1}))"
    by (subst sum_fun_insert, auto)
  also have "... = x\<^bsub>1\<^esub> + \<Sum> { x\<^bsub>i\<^esub> | i. i\<in>(UNIV - {1})}"
    by (metis fset_to_im)
  also from assms have unfld:"... = 1 + x\<^bsub>1\<^esub> + \<Sum> { x\<^bsub>i\<^esub> | i. i\<in>(UNIV - {1})}"
    by (metis (lifting, no_types) conway_monoid_one)
  finally show ?thesis
    by (metis (lifting, no_types) ac_simps unfld)
qed

lemma boffa_mon_aux1: "{x\<^bsub>i\<cdot>j \<^esub>| i j. i \<in> UNIV \<and> j \<in> UNIV} = {x\<^bsub>i\<^esub> | i. i \<in> UNIV}"
  by (auto, metis monoid_mult_class.mult.left_neutral)

lemma sum_intro' [intro]:
  "\<lbrakk>finite (A :: 'a::join_semilattice_zero set); finite B; \<forall>a\<in>A. \<exists>b\<in>B. a \<le> b \<rbrakk> \<Longrightarrow> \<Sum>A \<le> \<Sum>B"
  by (metis sum_intro)  

lemma boffa_aux2: 
  "conway_assm1 x \<Longrightarrow>
  \<Sum>{x\<^bsub>i\<^esub>\<cdot>x\<^bsub>j \<^esub>| i j. i \<in> UNIV \<and> j \<in> UNIV} \<le> \<Sum>{x\<^bsub>i\<cdot>j\<^esub> | i j. i \<in> UNIV \<and> j \<in> UNIV}"
  unfolding conway_assm1_def
  using [[simproc add: finite_Collect]]
  by force

lemma boffa_aux3: 
  assumes "conway_assm1 x"
  shows "(\<Sum> {x\<^bsub>i\<^esub> | i. i\<in>UNIV}) + (\<Sum> {x\<^bsub>i \<^esub>\<cdot> x\<^bsub>j\<^esub> | i j . i\<in>UNIV \<and> j\<in>UNIV}) = (\<Sum> {x\<^bsub>i\<^esub> | i. i\<in>UNIV})"
proof -
  from assms 
  have "(\<Sum> {x\<^bsub>i\<^esub> | i. i\<in>UNIV}) + (\<Sum> {x\<^bsub>i \<^esub>\<cdot> x\<^bsub>j\<^esub> | i j . i\<in>UNIV \<and> j\<in>UNIV}) \<le> (\<Sum> {x\<^bsub>i\<^esub> | i. i\<in>UNIV})+(\<Sum> {x\<^bsub>i\<cdot>j\<^esub> | i j . i\<in>UNIV \<and> j\<in>UNIV})"
    apply (subst add_iso_r)
    apply (subst boffa_aux2)
    by simp_all
  also have "... = (\<Sum> {x\<^bsub>i\<^esub> | i. i\<in>UNIV})"
    by (metis (mono_tags) add_idem boffa_mon_aux1)
  ultimately show ?thesis
    by (simp add: dual_order.antisym)
qed

lemma conway_monoid_identity:
  assumes "conway_assm1 x" "conway_assm2 x"
  shows "(\<Sum> {x\<^bsub>i\<^esub>|i. i\<in>UNIV})\<^sup>\<star> = (\<Sum> {x\<^bsub>i\<^esub>| i. i\<in>UNIV})"
proof -
  have one:"(\<Sum> {x\<^bsub>i\<^esub>|i. i\<in>UNIV}) \<cdot> (\<Sum> {x\<^bsub>i\<^esub>|i. i\<in>UNIV}) = (1 + (\<Sum> {x\<^bsub>i\<^esub>|i. i\<in>UNIV})) \<cdot> (1 + (\<Sum> {x\<^bsub>i\<^esub>|i. i\<in>UNIV}))"
    by (metis (mono_tags) assms(2) conway_monoid_split)
  also have "... = 1 + (\<Sum> {x\<^bsub>i\<^esub>|i. i\<in>UNIV}) + ((\<Sum> {x\<^bsub>i\<^esub>|i. i\<in>UNIV}) \<cdot> (\<Sum> {x\<^bsub>i\<^esub>|i. i\<in>UNIV}))"
    by (metis (lifting, no_types) calculation less_eq_def mult_isol mult_isol_equiv_subdistl mult_oner)
  also have "... = 1 + (\<Sum> {x\<^bsub>i\<^esub>|i. i\<in>UNIV}) + (\<Sum> {x\<^bsub>i \<^esub>\<cdot> x\<^bsub>j\<^esub> | i j. i\<in>UNIV \<and> j\<in>UNIV})"
    by (simp only: dioid_sum_prod finite_UNIV)
  finally have "\<Sum> {x\<^bsub>i\<^esub> |i. i \<in> UNIV} \<cdot> \<Sum> {x\<^bsub>i\<^esub> |i. i \<in> UNIV} = \<Sum> {x\<^bsub>i\<^esub> |i. i \<in> UNIV}"
    apply (simp only:)
proof -
  assume a1: "\<Sum>{x\<^bsub>i\<^esub> |i. i \<in> UNIV} \<cdot> \<Sum>{x\<^bsub>i\<^esub> |i. i \<in> UNIV} = 1 + \<Sum>{x\<^bsub>i\<^esub> |i. i \<in> UNIV} + \<Sum>{x\<^bsub>i\<^esub> \<cdot> x\<^bsub>j\<^esub> |i j. i \<in> UNIV \<and> j \<in> UNIV}"
  hence "\<Sum>{x\<^bsub>R\<^esub> |R. R \<in> UNIV} \<cdot> \<Sum>{x\<^bsub>R\<^esub> |R. R \<in> UNIV} = \<Sum>{x\<^bsub>R\<^esub> |R. R \<in> UNIV}"
    using assms(1) assms(2) boffa_aux3 conway_monoid_split by fastforce
  thus "1 + \<Sum>{x\<^bsub>i\<^esub> |i. i \<in> UNIV} + \<Sum>{x\<^bsub>i\<^esub> \<cdot> x\<^bsub>j\<^esub> |i j. i \<in> UNIV \<and> j \<in> UNIV} = \<Sum>{x\<^bsub>i\<^esub> |i. i \<in> UNIV}"
    using a1 by simp
qed
  thus ?thesis
    by (metis (mono_tags) one B1_algebra_class.R star_trans_eq)
qed
    
subsection \<open>Conway's Conjectures\<close>

class C0_algebra = strong_conway_dioid +
  assumes C0:  "x \<cdot> y = y \<cdot> z \<Longrightarrow> x\<^sup>\<star> \<cdot> y = y \<cdot> z\<^sup>\<star>"

class C1l_algebra = strong_conway_dioid +
  assumes C1l:  "x \<cdot> y \<le> y \<cdot> z \<Longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y \<cdot> z\<^sup>\<star>"

class C1r_algebra = strong_conway_dioid + 
  assumes C1r:  "y \<cdot> x \<le> z \<cdot> y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<le> z\<^sup>\<star> \<cdot> y"

class C2l_algebra = conway_dioid +
  assumes C2l: "x = y \<cdot> x \<Longrightarrow> x = y\<^sup>\<star> \<cdot> x"

class C2r_algebra = conway_dioid +
  assumes C2r: "x = x \<cdot> y \<Longrightarrow> x = x \<cdot> y\<^sup>\<star>"

class C3l_algebra = conway_dioid + 
  assumes C3l:  "x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"

class C3r_algebra = conway_dioid + 
  assumes C3r:  "y \<cdot> x \<le> y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"

sublocale C1r_algebra \<subseteq> dual: C1l_algebra
  "(+)" "(\<odot>)" "1" "0" "(\<le>)" "(<)" "star"
proof
  fix x y z :: 'a
  show "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult.assoc opp_mult_def)
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distrib_left opp_mult_def)
  show "x + x = x"
    by (metis add_idem)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
    by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (metis add_zerol)
  show "0 \<odot> x = 0"
    by (metis annir opp_mult_def)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis distrib_right opp_mult_def)
  show "x \<odot> 0 = 0"
    by (metis annil opp_mult_def)
  show "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<odot> y)\<^sup>\<star> \<odot> x\<^sup>\<star>"
    by (metis C11_var opp_mult_def)
  show "(x \<odot> y)\<^sup>\<star> = 1 + x \<odot> (y \<odot> x)\<^sup>\<star> \<odot> y"
    by (metis C12 mult.assoc opp_mult_def)
  show "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"
    by (metis C13)
  show "x \<odot> y \<le> y \<odot> z \<Longrightarrow> x\<^sup>\<star> \<odot> y \<le> y \<odot> z\<^sup>\<star>"
    by (metis C1r opp_mult_def)
qed

sublocale C2r_algebra \<subseteq> dual: C2l_algebra
  "(+)" "(\<odot>)" "1" "0" "(\<le>)" "(<)" "star"
proof
  fix x y z :: 'a
  show "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult.assoc opp_mult_def)
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distrib_left opp_mult_def)
  show "x + x = x"
    by (metis add_idem)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
    by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (metis add_zerol)
  show "0 \<odot> x = 0"
    by (metis annir opp_mult_def)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis distrib_right opp_mult_def)
  show "x \<odot> 0 = 0"
    by (metis annil opp_mult_def)
  show "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<odot> y)\<^sup>\<star> \<odot> x\<^sup>\<star>"
    by (metis C11_var opp_mult_def)
  show "(x \<odot> y)\<^sup>\<star> = 1 + x \<odot> (y \<odot> x)\<^sup>\<star> \<odot> y"
    by (metis C12 mult.assoc opp_mult_def)
  show "x = y \<odot> x \<Longrightarrow> x = y\<^sup>\<star> \<odot> x"
    by (metis C2r opp_mult_def)
qed

sublocale C3r_algebra \<subseteq> dual: C3l_algebra
  "(+)" "(\<odot>)" "1" "0" "(\<le>)" "(<)" "star"
proof 
  fix x y z :: 'a
  show "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult.assoc opp_mult_def)
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distrib_left opp_mult_def)
  show "x + x = x"
    by (metis add_idem)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
    by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (metis add_zerol)
  show "0 \<odot> x = 0"
    by (metis annir opp_mult_def)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis distrib_right opp_mult_def)
  show "x \<odot> 0 = 0"
    by (metis annil opp_mult_def)
  show "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<odot> y)\<^sup>\<star> \<odot> x\<^sup>\<star>"
    by (metis C11_var opp_mult_def)
  show "(x \<odot> y)\<^sup>\<star> = 1 + x \<odot> (y \<odot> x)\<^sup>\<star> \<odot> y"
    by (metis C12 mult.assoc opp_mult_def)
  show " x \<odot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<odot> y \<le> y"
    by (metis C3r opp_mult_def)
qed

lemma (in C3l_algebra) k2_var: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  by (metis local.C3l local.join.le_supE local.join.sup.absorb2 local.subdistl)

instance C2l_algebra \<subseteq> B1_algebra
  by (intro_classes, metis C2l monoid_mult_class.mult.left_neutral mult_oner conway_dioid_class.C12)

instance C2r_algebra \<subseteq>  B1_algebra 
  by (intro_classes, metis C2r conway_dioid_class.C12)

text \<open>The following claims are refuted by Nitpick\<close>

lemma (in conway_dioid) 
  assumes "x \<cdot> y = y \<cdot> z \<Longrightarrow> x\<^sup>\<star> \<cdot> y = y \<cdot> z\<^sup>\<star>"
  shows "1\<^sup>\<star> = 1"
(*  nitpick [expect=genuine] -- "3-element counterexample"*)
oops

lemma (in conway_dioid) 
  assumes "x \<cdot> y \<le> y \<cdot> z \<Longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y \<cdot> z\<^sup>\<star>"
  shows "1\<^sup>\<star> = 1"
(*  nitpick [expect=genuine] -- "3-element counterexample"*)
oops

text \<open>The following fact could not be refuted by Nitpick or Quickcheck; but an infinite counterexample exists.\<close>

lemma (in B1_algebra) "x = x\<cdot>y\<longrightarrow> x = x\<cdot>y\<^sup>\<star>"
  oops

instance C3l_algebra \<subseteq> C2l_algebra
  by (intro_classes, metis C3l conway_dioid_class.C12 dual_order.antisym join.sup.cobounded1 mult_isol_var mult_onel order_refl)

sublocale C2l_algebra \<subseteq> C3l_algebra  
proof
  fix x y
  show "x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"
  proof -
    assume "x \<cdot> y \<le> y"
    hence "(x + 1) \<cdot> y = y"
      by (metis less_eq_def mult_onel distrib_right')
    hence "(x + 1)\<^sup>\<star> \<cdot> y = y"
      by (metis C2l)
    hence "x\<^sup>\<star> \<cdot> y = y"
      by (metis C11 C2l add_comm mult_1_left mult_1_right)
    thus "x\<^sup>\<star> \<cdot> y \<le> y"
      by (metis eq_refl) 
  qed
qed

sublocale C1l_algebra \<subseteq> C3l_algebra  
  by unfold_locales (metis  mult_oner C1l C12 C13 add_zeror annir)

sublocale C3l_algebra \<subseteq> C1l_algebra  
proof 
  fix x y z
  show "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"
    by (metis local.C11_var local.C12 local.C3l local.eq_iff local.eq_refl local.join.sup.absorb2 local.join.sup_ge1 local.mult_onel local.mult_oner)
  show "x \<cdot> y \<le> y \<cdot> z \<Longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y \<cdot> z\<^sup>\<star>"
  proof -
    assume assm: "x \<cdot> y \<le> y \<cdot> z"
    have r1:"y \<le> y \<cdot> z\<^sup>\<star>"
      by (metis C12 mult_isol mult_oner order_prop)
    from assm have "x \<cdot> y \<cdot> z\<^sup>\<star> \<le> y \<cdot> z \<cdot>z\<^sup>\<star>"
      by (metis mult_isor)
    also have "... \<le> y \<cdot> z\<^sup>\<star>"
      by (metis local.C12 local.join.sup_commute local.mult_onel local.mult_oner local.subdistl mult_assoc)
    finally have "y + x \<cdot> y \<cdot> z\<^sup>\<star> \<le> y \<cdot> z\<^sup>\<star>"
      by (simp add: r1)
    thus "x\<^sup>\<star> \<cdot> y \<le> y \<cdot> z\<^sup>\<star>"
      by (metis k2_var mult.assoc)
  qed
qed

sublocale C1l_algebra \<subseteq> C2l_algebra
  by (unfold_locales, metis C12 C3l add.commute  local.join.sup.cobounded1 distrib_right less_eq_def mult_1_left order_refl)

sublocale C3r_algebra \<subseteq> C2r_algebra
  by (unfold_locales, metis C12 C3r add.commute  local.join.sup.cobounded1 distrib_left less_eq_def mult_1_right order_refl)

sublocale C2r_algebra \<subseteq> C3r_algebra
  by unfold_locales (metis dual.C3l opp_mult_def)

sublocale C1r_algebra \<subseteq> C3r_algebra
  by unfold_locales (metis dual.C3l opp_mult_def)

sublocale C3r_algebra \<subseteq> C1r_algebra 
  by (unfold_locales, metis dual.C13, metis dual.C1l opp_mult_def)

class C1_algebra = C1l_algebra + C1r_algebra

class C2_algebra = C2l_algebra + C2r_algebra

class C3_algebra = C3l_algebra + C3r_algebra

sublocale C0_algebra \<subseteq> C2_algebra  
  by unfold_locales (metis C12 C13 add_zeror annil mult_oner mult_onel C0)+

sublocale C2_algebra \<subseteq> C0_algebra  
  by unfold_locales (metis C1l C1r eq_iff)

sublocale C2_algebra \<subseteq> C1_algebra ..

sublocale C1_algebra \<subseteq> C2_algebra ..

sublocale C2_algebra \<subseteq> C3_algebra ..

sublocale C3_algebra \<subseteq> C2_algebra ..

subsection \<open>Kozen's Kleene Algebras\<close>

text \<open>Kozen's Kleene Algebras~\cite{Kozen,Kozensemi}.\<close>

class Kl_base = star_dioid +
  assumes Kl: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"

class Kr_base = star_dioid +
  assumes Kr: "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"

class K1l_algebra = Kl_base +
  assumes star_inductl: "x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"

class K1r_algebra = Kr_base +
  assumes star_inductr: "y \<cdot> x \<le> y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"

class K2l_algebra = Kl_base +
  assumes star_inductl_var: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"

class K2r_algebra = Kr_base +
  assumes star_inductr_var: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"

class K1_algebra = K1l_algebra + K1r_algebra

class K2_algebra = K2l_algebra + K2r_algebra

sublocale K1r_algebra \<subseteq> dual: K1l_algebra
  "(+)" "(\<odot>)" "1" "0" "(\<le>)" "(<)" "star"
proof
  fix x y z :: 'a
  show  "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult.assoc opp_mult_def)
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distrib_left opp_mult_def)
  show "x + x = x"
    by (metis add_idem)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
    by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (metis add_zerol)
  show "0 \<odot> x = 0"
    by (metis annir opp_mult_def)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis distrib_right opp_mult_def)
  show "x \<odot> 0 = 0"
    by (metis annil opp_mult_def)
  show "1 + x \<odot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis Kr opp_mult_def)
  show "x \<odot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<odot> y \<le> y"
    by (metis star_inductr opp_mult_def)
qed

sublocale K1l_algebra \<subseteq> B2_algebra
proof
  fix x y :: 'a
  show "1 + x \<le> x\<^sup>\<star>"
    by (metis add_iso_r  local.join.sup.cobounded1 mult_isol mult_oner order_trans Kl)
  show "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
    using local.Kl local.eq_iff local.phl_cons1 local.star_inductl by fastforce
  show "\<lbrakk> 1 + x \<le> y; y \<cdot> y = y \<rbrakk> \<Longrightarrow> x\<^sup>\<star> \<le> y"
    by (metis local.distrib_right' local.join.le_sup_iff local.join.sup.order_iff local.mult_isol local.mult_oner local.star_inductl)
qed

sublocale K1r_algebra \<subseteq> B2_algebra
  by unfold_locales (metis dual.B21 dual.B22 dual.B23 opp_mult_def)+

sublocale K1l_algebra \<subseteq> C2l_algebra
  by (unfold_locales, metis less_eq_def mult_1_left mult.assoc star_inductl star_invol star_one star_plus_one star_trans_eq troeger)

sublocale C2l_algebra \<subseteq> K1l_algebra 
  by (unfold_locales, metis C12 eq_iff mult_1_left mult_1_right, metis C3l)

sublocale K1r_algebra \<subseteq> C2r_algebra
    by unfold_locales (metis dual.C2l opp_mult_def)

sublocale C2r_algebra \<subseteq> K1r_algebra
  by (unfold_locales, metis dual.star_unfoldl opp_mult_def, metis C3r)

sublocale K1_algebra \<subseteq> C0_algebra
  by unfold_locales (metis C1l C1r eq_iff)

sublocale C0_algebra \<subseteq> K1l_algebra ..

sublocale K2r_algebra \<subseteq> dual: K2l_algebra
  "(+)" "(\<odot>)" "1" "0" "(\<le>)" "(<)" "star"
proof 
  fix x y z :: 'a
  show  "x \<odot> y \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult.assoc opp_mult_def)
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distrib_left opp_mult_def)
  show "x + x = x"
    by (metis add_idem)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
    by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (metis add_zerol)
  show "0 \<odot> x = 0"
    by (metis annir opp_mult_def)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis distrib_right opp_mult_def)
  show "x \<odot> 0 = 0"
    by (metis annil opp_mult_def)
  show "1 + x \<odot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis opp_mult_def Kr)
  show "z + x \<odot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<odot> z \<le> y"
    by (metis opp_mult_def star_inductr_var)
qed

sublocale K1l_algebra \<subseteq> K2l_algebra
  by unfold_locales (metis local.join.le_supE  star_inductl order_prop subdistl)

sublocale K2l_algebra \<subseteq> K1l_algebra
  by (unfold_locales, simp add: local.star_inductl_var)

sublocale K1r_algebra \<subseteq> K2r_algebra
  by unfold_locales (metis dual.star_inductl_var opp_mult_def)

sublocale K2r_algebra \<subseteq> K1r_algebra
  by unfold_locales (metis dual.star_inductl opp_mult_def)

sublocale kleene_algebra \<subseteq> K1_algebra
  by (unfold_locales, metis star_unfoldl, metis star_inductl_var, metis star_unfoldr, metis star_inductr_var)

sublocale K1_algebra \<subseteq> K2_algebra ..

sublocale K2_algebra \<subseteq> koz: kleene_algebra
  by (unfold_locales, metis Kl, metis star_inductl_var, metis star_inductr_var)

subsection \<open>Salomaa's Axioms\<close>

text \<open>Salomaa's axiomatisations of Regular Algebra~\cite{Salomaa}.\<close>

class salomaa_base = star_dioid +
  fixes ewp :: "'a \<Rightarrow> bool" 
  assumes S11: "(1 + x)\<^sup>\<star> = x\<^sup>\<star>"
  and  EWP : "ewp x \<longleftrightarrow> (\<exists>y. x = 1 + y \<and> \<not> ewp y)"

class Sr_algebra = salomaa_base +
  assumes S12r: "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
  and Ar : "\<lbrakk> \<not> ewp y; x = x \<cdot> y + z \<rbrakk> \<Longrightarrow> x = z \<cdot> y\<^sup>\<star>"

text \<open>The following claim is ruled out by Nitpick. The unfold law cannot be weakened as in Kleene algebra.\<close>

lemma (in salomaa_base) 
  assumes S12r': "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  and Ar' : "\<lbrakk> \<not> ewp y; x = x \<cdot> y + z \<rbrakk> \<Longrightarrow> x = z \<cdot> y\<^sup>\<star>"
  shows "x\<^sup>\<star> \<le> 1 + x\<^sup>\<star> \<cdot> x"
  (*nitpick [expect=genuine] -- "4-element counterexample"*)
oops

class Sl_algebra = salomaa_base +
  assumes S12l: "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
  and Al : "\<lbrakk> \<not> ewp y; x = y\<cdot>x+z \<rbrakk> \<Longrightarrow> x = y\<^sup>\<star>\<cdot>z"

class S_algebra = Sl_algebra + Sr_algebra

sublocale Sl_algebra \<subseteq> dual: Sr_algebra
  "(+)" "(\<odot>)" "1" "0" "(\<le>)" "(<)" "star" "ewp"
proof
  fix x y z :: 'a
  show "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult.assoc opp_mult_def)
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis distrib_left opp_mult_def)
  show "x + x = x"
    by (metis add_idem)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
    by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (metis add_zerol)
  show "0 \<odot> x = 0"
    by (metis annir times.opp_mult_def)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis opp_mult_def distrib_right')
  show "x \<odot> 0 = 0"
    by (metis annil opp_mult_def)
  show "(1 + x)\<^sup>\<star> = x\<^sup>\<star>"
    by (metis S11)
  show "ewp x = (\<exists>y. x = 1 + y \<and> \<not> ewp y)"
    by (metis EWP)
  show "1 + x\<^sup>\<star> \<odot> x = x\<^sup>\<star>"
    by (metis S12l opp_mult_def)
  show "\<lbrakk> \<not> ewp y; x = x \<odot> y + z \<rbrakk> \<Longrightarrow> x = z \<odot> y\<^sup>\<star>"
    by (metis opp_mult_def Al)
qed

context Sr_algebra
begin

lemma kozen_induct_r: 
  assumes "y \<cdot> x + z \<le> y"
  shows "z \<cdot> x\<^sup>\<star> \<le> y"
proof (cases "ewp x")
  case False thus ?thesis
    by (metis add_commute assms local.Ar local.join.le_supE local.join.sup.orderE local.mult_isor)
next
  case True thus ?thesis
  proof -
    assume "ewp x"
    then obtain x' where assm1: "x = 1 + x'" and assm2: "\<not> ewp x'"
      by (metis EWP) 
    have "y = (z + y) \<cdot> x\<^sup>\<star>"
      by (metis S11 local.join.le_supE assm1 assm2 assms eq_iff less_eq_def Ar subdistl)
    thus "z \<cdot> x\<^sup>\<star> \<le> y"
      by (metis local.join.sup.cobounded1 local.mult_isor)
  qed
qed

end

context Sl_algebra
begin

lemma kozen_induct_l: 
  assumes "x \<cdot> y + z \<le> y"
  shows "x\<^sup>\<star>\<cdot>z \<le> y"
  by (metis dual.kozen_induct_r times.opp_mult_def assms)

end

sublocale Sr_algebra \<subseteq> K2r_algebra
  by unfold_locales (metis S12r order_refl, metis add_comm kozen_induct_r) 

sublocale Sr_algebra \<subseteq> K1r_algebra ..

sublocale Sl_algebra \<subseteq> K2l_algebra
  by unfold_locales (metis S12l order_refl, metis add_comm kozen_induct_l) 

sublocale Sl_algebra \<subseteq> K1l_algebra ..

sublocale S_algebra \<subseteq> K1_algebra ..

sublocale S_algebra \<subseteq> K2_algebra ..

text \<open>The following claim could be refuted.\<close>

lemma (in K2_algebra) "(\<not> 1 \<le>  x) \<longrightarrow>  x = x \<cdot> y + z \<longrightarrow> x = z \<cdot> y\<^sup>\<star>"
oops

class salomaa_conj_r = salomaa_base +
  assumes salomaa_small_unfold:  "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
  assumes salomaa_small_r: "\<lbrakk> \<not> ewp y ; x = x \<cdot> y + 1 \<rbrakk> \<Longrightarrow> x = y\<^sup>\<star>"

sublocale Sr_algebra \<subseteq> salomaa_conj_r
  by (unfold_locales, metis S12r, metis mult_onel Ar)

lemma (in salomaa_conj_r) "(\<not> ewp y) \<and> (x = x \<cdot> y + z) \<longrightarrow> x = z \<cdot> y\<^sup>\<star>"
  (*nitpick [expect=genuine] -- "3-element counterexample"*)
oops

end
