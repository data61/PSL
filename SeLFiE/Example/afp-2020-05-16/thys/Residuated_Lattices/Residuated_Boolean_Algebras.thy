(* Title:      Residuated Boolean Algebras
   Author:     Victor Gomes <vborgesferreiragomes1 at sheffield.ac.uk>
   Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Residuated Boolean Algebras\<close>

theory Residuated_Boolean_Algebras
  imports Residuated_Lattices
begin

subsection \<open>Conjugation on Boolean Algebras\<close>

text \<open>
  Similarly, as in the previous section, we define the conjugation for
  arbitrary residuated functions on boolean algebras.
\<close>

context boolean_algebra
begin

lemma inf_bot_iff_le: "x \<sqinter> y = \<bottom> \<longleftrightarrow> x \<le> -y"
  by (metis le_iff_inf inf_sup_distrib1 inf_top_right sup_bot.left_neutral sup_compl_top compl_inf_bot inf.assoc inf_bot_right)

lemma le_iff_inf_bot: "x \<le> y \<longleftrightarrow> x \<sqinter> -y = \<bottom>"
  by (metis inf_bot_iff_le compl_le_compl_iff inf_commute)
  
lemma indirect_eq: "(\<And>z. x \<le> z \<longleftrightarrow> y \<le> z) \<Longrightarrow> x = y"
  by (metis eq_iff)

text \<open>
  Let $B$ be a boolean algebra. The maps $f$ and $g$ on $B$ are
  a pair of conjugates if and only if for all $x, y \in B$,
  $f(x) \sqcap y = \bot \Leftrightarrow x \sqcap g(t) = \bot$.
\<close>
  
definition conjugation_pair :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "conjugation_pair f g \<equiv> \<forall>x y. f(x) \<sqinter> y = \<bottom> \<longleftrightarrow> x \<sqinter> g(y) = \<bottom>"

lemma conjugation_pair_commute: "conjugation_pair f g \<Longrightarrow> conjugation_pair g f"
  by (auto simp: conjugation_pair_def inf_commute)
  
lemma conjugate_iff_residuated: "conjugation_pair f g = residuated_pair f (\<lambda>x. -g(-x))"
  apply (clarsimp simp: conjugation_pair_def residuated_pair_def inf_bot_iff_le)
  by (metis double_compl)

lemma conjugate_residuated: "conjugation_pair f g \<Longrightarrow> residuated_pair f (\<lambda>x. -g(-x))"
  by (metis conjugate_iff_residuated)
  
lemma residuated_iff_conjugate: "residuated_pair f g = conjugation_pair f (\<lambda>x. -g(-x))"
  apply (clarsimp simp: conjugation_pair_def residuated_pair_def inf_bot_iff_le)
  by (metis double_compl)

text \<open>
  A map $f$ has a conjugate pair if and only if it is residuated.
\<close>
  
lemma conj_residuatedI1: "\<exists>g. conjugation_pair f g \<Longrightarrow> residuated f"
  by (metis conjugate_iff_residuated residuated_def)
  
lemma conj_residuatedI2: "\<exists>g. conjugation_pair g f \<Longrightarrow> residuated f"
  by (metis conj_residuatedI1 conjugation_pair_commute)
  
lemma exist_conjugateI[intro]: "residuated f \<Longrightarrow> \<exists>g. conjugation_pair f g"
  by (metis residuated_def residuated_iff_conjugate)
  
lemma exist_conjugateI2[intro]: "residuated f \<Longrightarrow> \<exists>g. conjugation_pair g f"
  by (metis exist_conjugateI conjugation_pair_commute)

text \<open>
  The conjugate of a residuated function $f$ is unique.
\<close>

lemma unique_conjugate[intro]: "residuated f \<Longrightarrow> \<exists>!g. conjugation_pair f g"
proof - 
  {
    fix g h x assume "conjugation_pair f g" and "conjugation_pair f h"
    hence "g = h"
      apply (unfold conjugation_pair_def)
      apply (rule ext)
      apply (rule antisym)
      by (metis le_iff_inf_bot inf_commute inf_compl_bot)+
  } 
  moreover assume "residuated f"
  ultimately show ?thesis by force
qed
  
lemma unique_conjugate2[intro]: "residuated f \<Longrightarrow> \<exists>!g. conjugation_pair g f"
  by (metis unique_conjugate conjugation_pair_commute)

text \<open>
  Since the conjugate of a residuated map is unique, we define a
  conjugate operation.
\<close>
  
definition conjugate :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "conjugate f \<equiv> THE g. conjugation_pair g f"

lemma conjugate_iff_def: "residuated f \<Longrightarrow> f(x) \<sqinter> y = \<bottom> \<longleftrightarrow> x \<sqinter> conjugate f y = \<bottom>"
  apply (clarsimp simp: conjugate_def dest!: unique_conjugate)
  apply (subgoal_tac "(THE g. conjugation_pair g f) = g")
  apply (clarsimp simp add: conjugation_pair_def)
  apply (rule the1_equality)
  by (auto intro: conjugation_pair_commute)
    
lemma conjugateI1: "residuated f \<Longrightarrow> f(x) \<sqinter> y = \<bottom> \<Longrightarrow> x \<sqinter> conjugate f y = \<bottom>"
  by (metis conjugate_iff_def)
  
lemma conjugateI2: "residuated f \<Longrightarrow> x \<sqinter> conjugate f y = \<bottom> \<Longrightarrow> f(x) \<sqinter> y = \<bottom>"
  by (metis conjugate_iff_def)

text \<open>
  Few more lemmas about conjugation follow.
\<close>
  
lemma residuated_conj1: "residuated f \<Longrightarrow> conjugation_pair f (conjugate f)"
  using conjugateI1 conjugateI2 conjugation_pair_def by auto
  
lemma residuated_conj2: "residuated f \<Longrightarrow> conjugation_pair (conjugate f) f"
  using conjugateI1 conjugateI2 conjugation_pair_def inf_commute by auto
  
lemma conj_residuated: "residuated f \<Longrightarrow> residuated (conjugate f)"
  by (force dest!: residuated_conj2 intro: conj_residuatedI1)
  
lemma conj_involution: "residuated f \<Longrightarrow> conjugate (conjugate f) = f"
  by (metis conj_residuated residuated_conj1 residuated_conj2 unique_conjugate)
  
lemma residual_conj_eq: "residuated f \<Longrightarrow> residual (conjugate f) = (\<lambda>x. -f(-x))"
  apply (unfold residual_def)
  apply (rule the1_equality)
  apply (rule residual_unique)
  apply (auto intro: conj_residuated conjugate_residuated residuated_conj2)
done
  
lemma residual_conj_eq_ext: "residuated f \<Longrightarrow> residual (conjugate f) x = -f(-x)"
  by (metis residual_conj_eq)
  
lemma conj_iso: "residuated f \<Longrightarrow> x \<le> y \<Longrightarrow> conjugate f x \<le> conjugate f y"
  by (metis conj_residuated res_iso)
  
lemma conjugate_strict: "residuated f \<Longrightarrow> conjugate f \<bottom> = \<bottom>"
  by (metis conj_residuated residuated_strict)

lemma conjugate_sup: "residuated f \<Longrightarrow> conjugate f (x \<squnion> y) = conjugate f x \<squnion> conjugate f y"
  by (metis conj_residuated residuated_sup)

lemma conjugate_subinf: "residuated f \<Longrightarrow> conjugate f (x \<sqinter> y) \<le> conjugate f x \<sqinter> conjugate f y"
  by (auto simp: conj_iso)
 
text \<open>
  Next we prove some lemmas from Maddux's article. Similar lemmas have been proved in AFP entry
  for relation algebras. They should be consolidated in the future.
\<close>

lemma maddux1: "residuated f \<Longrightarrow> f(x \<sqinter> - conjugate f(y)) \<le> f(x) \<sqinter> -y"
proof -
  assume assm: "residuated f"
  hence "f(x \<sqinter> - conjugate f(y)) \<le> f x"
    by (metis inf_le1 res_iso)
  moreover have "f(x \<sqinter> - conjugate f (y)) \<sqinter> y = \<bottom>"
    by (metis assm conjugateI2 inf_bot_iff_le inf_le2)
  ultimately show ?thesis
    by (metis inf_bot_iff_le le_inf_iff)
qed

lemma maddux1': "residuated f \<Longrightarrow> conjugate f(x \<sqinter> -f(y)) \<le> conjugate f(x) \<sqinter> -y"
  by (metis conj_involution conj_residuated maddux1)
  
lemma maddux2: "residuated f \<Longrightarrow> f(x) \<sqinter> y \<le> f(x \<sqinter> conjugate f y)"
proof -
  assume resf: "residuated f"
  obtain z where z_def: "z = f(x \<sqinter> conjugate f y)" by auto
  hence "f(x \<sqinter> conjugate f y) \<sqinter> -z = \<bottom>"
    by (metis inf_compl_bot)
  hence "x \<sqinter> conjugate f y \<sqinter> conjugate f (-z) = \<bottom>"
    by (metis conjugate_iff_def resf)
  hence "x \<sqinter> conjugate f (y \<sqinter> -z) = \<bottom>"
    apply (subgoal_tac "conjugate f (y \<sqinter> -z) \<le> conjugate f y \<sqinter> conjugate f (-z)")
    apply (metis (no_types, hide_lams) dual_order.trans inf.commute inf_bot_iff_le inf_left_commute)
    by (metis conj_iso inf_le2 inf_top.left_neutral le_inf_iff resf)
  hence "f(x) \<sqinter> y \<sqinter> -z = \<bottom>"
    by (metis conjugateI2 inf.assoc resf)
  thus ?thesis
    by (metis double_compl inf_bot_iff_le z_def)
qed

lemma maddux2': "residuated f \<Longrightarrow> conjugate f(x) \<sqinter> y \<le> conjugate f(x \<sqinter> f y)"
  by (metis conj_involution conj_residuated maddux2)
  
lemma residuated_conjugate_ineq: "residuated f \<Longrightarrow> conjugate f x \<le> y \<longleftrightarrow> x \<le> -f(-y)"
  by (metis conj_residuated residual_galois residual_conj_eq)

lemma residuated_comp_closed: "residuated f \<Longrightarrow> residuated g \<Longrightarrow> residuated (f o g)"
  by (auto simp add: residuated_def residuated_pair_def)
  
lemma conjugate_comp: "residuated f \<Longrightarrow> residuated g \<Longrightarrow> conjugate (f o g) = conjugate g o conjugate f"
proof (rule ext, rule indirect_eq)
  fix x y
  assume assms: "residuated f" "residuated g" 
  have "conjugate (f o g) x \<le> y \<longleftrightarrow> x \<le> -f(g(-y))"
    apply (subst residuated_conjugate_ineq)
    using assms by (auto intro!: residuated_comp_closed)
  also have "... \<longleftrightarrow> conjugate g (conjugate f x) \<le> y"
    using assms by (simp add: residuated_conjugate_ineq)
  finally show "(conjugate (f \<circ> g) x \<le> y) = ((conjugate g \<circ> conjugate f) x \<le> y)"   
    by auto
qed 

lemma conjugate_comp_ext: "residuated f \<Longrightarrow> residuated g \<Longrightarrow> conjugate (\<lambda>x. f (g x)) x = conjugate g (conjugate f x)"
  using conjugate_comp by (simp add: comp_def)
  
end (* boolean_algebra *)

context complete_boolean_algebra begin

text \<open>
  On a complete boolean algebra, it is possible to give an explicit
  definition of conjugation.
\<close>

lemma conjugate_eq: "residuated f \<Longrightarrow> conjugate f y = \<Sqinter>{x. y \<le> -f(-x)}"
proof -
  assume assm: "residuated f" obtain g where g_def: "g = conjugate f" by auto
  have "g y = \<Sqinter>{x. x \<ge> g y}"
    by (auto intro!: antisym Inf_lower Inf_greatest)
  also have "... = \<Sqinter>{x. -x \<sqinter> g y = \<bottom>}"
    by (simp add: inf_bot_iff_le)
  also have "... = \<Sqinter>{x. f(-x) \<sqinter> y = \<bottom>}"
    by (metis conjugate_iff_def assm g_def)
  finally show ?thesis
    by (simp add: g_def le_iff_inf_bot inf_commute)
qed

end (* complete_boolean_algebra *)

subsection \<open>Residuated Boolean Structures\<close>

text \<open>
  In this section, we present various residuated structures based on
  boolean algebras.
  The left and right conjugation of the multiplicative operation is
  defined, and a number of facts is derived.
\<close>

class residuated_boolean_algebra = boolean_algebra + residuated_pogroupoid
begin

subclass residuated_lgroupoid ..

definition conjugate_l :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<lhd>" 60) where
  "x \<lhd> y \<equiv> -(-x \<leftarrow> y)"

definition conjugate_r :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<rhd>" 60) where
  "x \<rhd> y \<equiv> -(x \<rightarrow> -y)"
  
lemma residual_conjugate_r: "x \<rightarrow> y = -(x \<rhd> -y)"
  by (metis conjugate_r_def double_compl)
  
lemma residual_conjugate_l: "x \<leftarrow> y = -(-x \<lhd> y)"
  by (metis conjugate_l_def double_compl)
  
lemma conjugation_multl: "x\<cdot>y \<sqinter> z = \<bottom> \<longleftrightarrow> x \<sqinter> (z \<lhd> y) = \<bottom>"
  by (metis conjugate_l_def double_compl le_iff_inf_bot resl_galois)

lemma conjugation_multr: "x\<cdot>y \<sqinter> z = \<bottom> \<longleftrightarrow> y \<sqinter> (x \<rhd> z) = \<bottom>"
  by (metis conjugate_r_def inf_bot_iff_le le_iff_inf_bot resr_galois)
  
lemma conjugation_conj: "(x \<lhd> y) \<sqinter> z = \<bottom> \<longleftrightarrow> y \<sqinter> (z \<rhd> x) = \<bottom>"
  by (metis inf_commute conjugation_multr conjugation_multl)

lemma conjugation_pair_multl [simp]: "conjugation_pair (\<lambda>x. x\<cdot>y) (\<lambda>x. x \<lhd> y)"
  by (simp add: conjugation_pair_def conjugation_multl)
  
lemma conjugation_pair_multr [simp]: "conjugation_pair (\<lambda>x. y\<cdot>x) (\<lambda>x. y \<rhd> x)"
  by (simp add: conjugation_pair_def conjugation_multr)
  
lemma conjugation_pair_conj [simp]: "conjugation_pair (\<lambda>x. y \<lhd> x) (\<lambda>x. x \<rhd> y)"
  by (simp add: conjugation_pair_def conjugation_conj)
  
lemma residuated_conjl1 [simp]: "residuated (\<lambda>x. x \<lhd> y)" 
  by (metis conj_residuatedI2 conjugation_pair_multl)
  
lemma residuated_conjl2 [simp]: "residuated (\<lambda>x. y \<lhd> x)" 
  by (metis conj_residuatedI1 conjugation_pair_conj)
  
lemma residuated_conjr1 [simp]: "residuated (\<lambda>x. y \<rhd> x)" 
  by (metis conj_residuatedI2 conjugation_pair_multr)
  
lemma residuated_conjr2 [simp]: "residuated (\<lambda>x. x \<rhd> y)" 
  by (metis conj_residuatedI2 conjugation_pair_conj)
  
lemma conjugate_multr [simp]: "conjugate (\<lambda>x. y\<cdot>x) = (\<lambda>x. y \<rhd> x)"
  by (metis conjugation_pair_multr residuated_conj1 residuated_multr unique_conjugate)
  
lemma conjugate_conjr1 [simp]: "conjugate (\<lambda>x. y \<rhd> x) = (\<lambda>x. y\<cdot>x)"
  by (metis conjugate_multr conj_involution residuated_multr)
  
lemma conjugate_multl [simp]: "conjugate (\<lambda>x. x\<cdot>y) = (\<lambda>x. x \<lhd> y)"
  by (metis conjugation_pair_multl residuated_conj1 residuated_multl unique_conjugate)
 
lemma conjugate_conjl1 [simp]: "conjugate (\<lambda>x. x \<lhd> y) = (\<lambda>x. x\<cdot>y)"
proof -
  have "conjugate (conjugate (\<lambda>x. x\<cdot>y)) = conjugate (\<lambda>x. x \<lhd> y)" by simp
  thus ?thesis
    by (metis conj_involution[OF residuated_multl])
qed

lemma conjugate_conjl2[simp]: "conjugate (\<lambda>x. y \<lhd> x) = (\<lambda>x. x \<rhd> y)"
  by (metis conjugation_pair_conj unique_conjugate residuated_conj1 residuated_conjl2)

lemma conjugate_conjr2[simp]: "conjugate (\<lambda>x. x \<rhd> y) = (\<lambda>x. y \<lhd> x)"
proof -
  have "conjugate (conjugate (\<lambda>x. y \<lhd> x)) = conjugate (\<lambda>x. x \<rhd> y)" by simp
  thus ?thesis
    by (metis conj_involution[OF residuated_conjl2])
qed

lemma conjl1_iso: "x \<le> y \<Longrightarrow> x \<lhd> z \<le> y \<lhd> z"
  by (metis conjugate_l_def compl_mono resl_iso)

lemma conjl2_iso: "x \<le> y \<Longrightarrow> z \<lhd> x \<le> z \<lhd> y"
  by (metis res_iso residuated_conjl2)

lemma conjr1_iso: "x \<le> y \<Longrightarrow> z \<rhd> x \<le> z \<rhd> y"
  by (metis res_iso residuated_conjr1)

lemma conjr2_iso: "x \<le> y \<Longrightarrow> x \<rhd> z \<le> y \<rhd> z"
  by (metis conjugate_r_def compl_mono resr_antitonel)

lemma conjl1_sup: "z \<lhd> (x \<squnion> y) = (z \<lhd> x) \<squnion> (z \<lhd> y)"
  by (metis conjugate_l_def compl_inf resl_distr)

lemma conjl2_sup: "(x \<squnion> y) \<lhd> z = (x \<lhd> z) \<squnion> (y \<lhd> z)"
  by (metis (poly_guards_query) residuated_sup residuated_conjl1)

lemma conjr1_sup: "z \<rhd> (x \<squnion> y) = (z \<rhd> x) \<squnion> (z \<rhd> y)"
  by (metis residuated_sup residuated_conjr1)

lemma conjr2_sup: "(x \<squnion> y) \<rhd> z = (x \<rhd> z) \<squnion> (y \<rhd> z)"
  by (metis conjugate_r_def compl_inf resr_distl)

lemma conjl1_strict: "\<bottom> \<lhd> x = \<bottom>"
  by (metis residuated_strict residuated_conjl1)

lemma conjl2_strict: "x \<lhd> \<bottom> = \<bottom>"
  by (metis residuated_strict residuated_conjl2)

lemma conjr1_strict: "\<bottom> \<rhd> x = \<bottom>"
  by (metis residuated_strict residuated_conjr2)

lemma conjr2_strict: "x \<rhd> \<bottom> = \<bottom>"
  by (metis residuated_strict residuated_conjr1)

lemma conjl1_iff: "x \<lhd> y \<le> z \<longleftrightarrow> x \<le> -(-z\<cdot>y)"
  by (metis conjugate_l_def compl_le_swap1 compl_le_swap2 resl_galois)

lemma conjl2_iff: "x \<lhd> y \<le> z \<longleftrightarrow> y \<le> -(-z \<rhd> x)"
  by (metis conjl1_iff conjugate_r_def compl_le_swap2 double_compl resr_galois)

lemma conjr1_iff: "x \<rhd> y \<le> z \<longleftrightarrow> y \<le> -(x\<cdot>-z)"
  by (metis conjugate_r_def compl_le_swap1 double_compl resr_galois)

lemma conjr2_iff: "x \<rhd> y \<le> z \<longleftrightarrow> x \<le> -(y \<lhd> -z)"
  by (metis conjugation_conj double_compl inf.commute le_iff_inf_bot)

text \<open>
  We apply Maddux's lemmas regarding conjugation of an arbitrary residuated function 
  for each of the 6 functions.
\<close>
  
lemma maddux1a: "a\<cdot>(x \<sqinter> -(a \<rhd> y)) \<le> a\<cdot>x"
  by (insert maddux1 [of "\<lambda>x. a\<cdot>x"]) simp
  
lemma maddux1a': "a\<cdot>(x \<sqinter> -(a \<rhd> y)) \<le> -y"
  by (insert maddux1 [of "\<lambda>x. a\<cdot>x"]) simp
  
lemma maddux1b: "(x \<sqinter> -(y \<lhd> a))\<cdot>a \<le> x\<cdot>a"
  by (insert maddux1 [of "\<lambda>x. x\<cdot>a"]) simp
  
lemma maddux1b': "(x \<sqinter> -(y \<lhd> a))\<cdot>a \<le> -y"
  by (insert maddux1 [of "\<lambda>x. x\<cdot>a"]) simp
  
lemma maddux1c: " a \<lhd> x \<sqinter> -(y \<rhd> a) \<le> a \<lhd> x"
  by (insert maddux1 [of "\<lambda>x. a \<lhd> x"]) simp
  
lemma maddux1c': "a \<lhd> x \<sqinter> -(y \<rhd> a) \<le> -y"
  by (insert maddux1 [of "\<lambda>x. a \<lhd> x"]) simp
  
lemma maddux1d: "a \<rhd> x \<sqinter> -(a\<cdot>y) \<le> a \<rhd> x"
  by (insert maddux1 [of "\<lambda>x. a \<rhd> x"]) simp
  
lemma maddux1d': "a \<rhd> x \<sqinter> -(a\<cdot>y) \<le> -y"
  by (insert maddux1 [of "\<lambda>x. a \<rhd> x"]) simp

lemma maddux1e: "x \<sqinter> -(y\<cdot>a) \<lhd> a \<le> x \<lhd> a"
  by (insert maddux1 [of "\<lambda>x. x \<lhd> a"]) simp
  
lemma maddux1e': "x \<sqinter> -(y\<cdot>a) \<lhd> a \<le> -y"
  by (insert maddux1 [of "\<lambda>x. x \<lhd> a"]) simp
  
lemma maddux1f: "x \<sqinter> -(a \<lhd> y) \<rhd> a \<le> x \<rhd> a"
  by (insert maddux1 [of "\<lambda>x. x \<rhd> a"]) simp
  
lemma maddux1f': "x \<sqinter> -(a \<lhd> y) \<rhd> a \<le> -y"
  by (insert maddux1 [of "\<lambda>x. x \<rhd> a"]) simp

lemma maddux2a: "a\<cdot>x \<sqinter> y \<le> a\<cdot>(x \<sqinter> (a \<rhd> y))"
  by (insert maddux2 [of "\<lambda>x. a\<cdot>x"]) simp
  
lemma maddux2b: "x\<cdot>a \<sqinter> y \<le> (x \<sqinter> (y \<lhd> a))\<cdot>a"
  by (insert maddux2 [of "\<lambda>x. x\<cdot>a"]) simp
  
lemma maddux2c: "(a \<lhd> x) \<sqinter> y \<le> a \<lhd> (x \<sqinter> (y \<rhd> a))"
  by (insert maddux2 [of "\<lambda>x. a \<lhd> x"]) simp
  
lemma maddux2d: "(a \<rhd> x) \<sqinter> y \<le> a \<rhd> (x \<sqinter> a\<cdot>y)"
  by (insert maddux2 [of "\<lambda>x. a \<rhd> x"]) simp

lemma maddux2e: "(x \<lhd> a) \<sqinter> y \<le> (x \<sqinter> y\<cdot>a) \<lhd> a"
  by (insert maddux2 [of "\<lambda>x. x \<lhd> a"]) simp
  
lemma maddux2f: "(x \<rhd> a) \<sqinter> y \<le> (x \<sqinter> (a \<lhd> y)) \<rhd> a"
  by (insert maddux2 [of "\<lambda>x. x \<rhd> a"]) simp
  
text \<open>
  The multiplicative operation $\cdot$ on a residuated boolean algebra is generally not
  associative. We prove some equivalences related to associativity.
\<close>

lemma res_assoc_iff1: "(\<forall>x y z. x\<cdot>(y\<cdot>z) = (x\<cdot>y)\<cdot>z) \<longleftrightarrow> (\<forall>x y z. x \<rhd> (y \<rhd> z) = y\<cdot>x \<rhd> z)"
proof safe
  fix x y z assume "\<forall>x y z. x\<cdot>(y\<cdot>z) = (x\<cdot>y)\<cdot>z"
  thus "x \<rhd> (y \<rhd> z) = y \<cdot> x \<rhd> z"
    using conjugate_comp_ext[of "\<lambda>z. y\<cdot>z" "\<lambda>z. x\<cdot>z"] by auto
next
  fix x y z assume "\<forall>x y z. x \<rhd> (y \<rhd> z) = y\<cdot>x \<rhd> z"
  thus "x\<cdot>(y\<cdot>z) = (x\<cdot>y)\<cdot>z"
    using conjugate_comp_ext[of "\<lambda>z. y \<rhd> z" "\<lambda>z. x \<rhd> z"] by auto
qed

lemma res_assoc_iff2: "(\<forall>x y z. x\<cdot>(y\<cdot>z) = (x\<cdot>y)\<cdot>z) \<longleftrightarrow> (\<forall>x y z. x \<lhd> (y \<cdot> z) = (x \<lhd> z) \<lhd> y)"
proof safe
  fix x y z assume "\<forall>x y z. x\<cdot>(y\<cdot>z) = (x\<cdot>y)\<cdot>z"
  hence "\<forall>x y z. (x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)" by simp
  thus "x \<lhd> (y \<cdot> z) = (x \<lhd> z) \<lhd> y"
    using conjugate_comp_ext[of "\<lambda>x. x\<cdot>z" "\<lambda>x. x\<cdot>y"] by auto
next
  fix x y z assume "\<forall>x y z. x \<lhd> (y \<cdot> z) = (x \<lhd> z) \<lhd> y"
  hence "\<forall>x y z. (x \<lhd> z) \<lhd> y = x \<lhd> (y \<cdot> z)" by simp
  thus "x\<cdot>(y\<cdot>z) = (x\<cdot>y)\<cdot>z" 
    using conjugate_comp_ext[of "\<lambda>z. z \<lhd> y" "\<lambda>x. x \<lhd> z"] by auto
qed
  
lemma res_assoc_iff3: "(\<forall>x y z. x\<cdot>(y\<cdot>z) = (x\<cdot>y)\<cdot>z) \<longleftrightarrow> (\<forall>x y z. (x \<rhd> y) \<lhd> z = x \<rhd> (y \<lhd> z))"
proof safe
  fix x y z assume "\<forall>x y z. x\<cdot>(y\<cdot>z) = (x\<cdot>y)\<cdot>z"
  thus "(x \<rhd> y) \<lhd> z = x \<rhd> (y \<lhd> z)"
    using conjugate_comp_ext[of "\<lambda>u. x\<cdot>u" "\<lambda>u. u\<cdot>z"] and
    conjugate_comp_ext[of "\<lambda>u. u\<cdot>z" "\<lambda>u. x\<cdot>u", symmetric]
    by auto
next
  fix x y z assume "\<forall>x y z. (x \<rhd> y) \<lhd> z = x \<rhd> (y \<lhd> z)"
  thus "x\<cdot>(y\<cdot>z) = (x\<cdot>y)\<cdot>z"
    using conjugate_comp_ext[of "\<lambda>u. x \<rhd> u" "\<lambda>u. u \<lhd> z"] and
    conjugate_comp_ext[of "\<lambda>u. u \<lhd> z" "\<lambda>u. x \<rhd> u", symmetric]
    by auto
qed

end (* residuated_boolean_algebra *)

class unital_residuated_boolean = residuated_boolean_algebra + one +
  assumes mult_onel [simp]: "x\<cdot>1 = x"
  and mult_oner [simp]: "1\<cdot>x = x"
begin

text \<open>
  The following equivalences are taken from J{\'o}sson and Tsinakis.
\<close>

lemma jonsson1a: "(\<exists>f. \<forall>x y. x \<rhd> y = f(x)\<cdot>y) \<longleftrightarrow> (\<forall>x y. x \<rhd> y = (x \<rhd> 1)\<cdot>y)"
  apply standard
  apply force
  apply (rule_tac x="\<lambda>x. x \<rhd> 1" in exI)
  apply force
  done
  
lemma jonsson1b: "(\<forall>x y. x \<rhd> y = (x \<rhd> 1)\<cdot>y) \<longleftrightarrow> (\<forall>x y. x\<cdot>y = (x \<rhd> 1) \<rhd> y)"
proof safe
  fix x y
  assume "\<forall>x y. x \<rhd> y = (x \<rhd> 1)\<cdot>y"
  hence "conjugate (\<lambda>y. x \<rhd> y) = conjugate (\<lambda>y. (x \<rhd> 1)\<cdot>y)" by metis
  thus "x\<cdot>y = (x \<rhd> 1) \<rhd> y" by simp
next
  fix x y
  assume "\<forall>x y. x \<cdot> y = x \<rhd> 1 \<rhd> y"
  thus "x \<rhd> y = (x \<rhd> 1) \<cdot> y"
    by (metis mult_onel)
qed

lemma jonsson1c: "(\<forall>x y. x \<rhd> y = (x \<rhd> 1)\<cdot>y) \<longleftrightarrow> (\<forall>x y. y \<lhd> x = 1 \<lhd> (x \<lhd> y))"
proof safe
  fix x y
  assume "\<forall>x y. x \<rhd> y = (x \<rhd> 1)\<cdot>y"
  hence "(\<lambda>x. x \<rhd> y) = (\<lambda>x. (x \<rhd> 1)\<cdot>y)" by metis
  hence "(\<lambda>x. x \<rhd> y) = (\<lambda>x. x\<cdot>y) o (\<lambda>x. x \<rhd> 1)" by force
  hence "conjugate (\<lambda>x. y \<lhd> x) = (\<lambda>x. x\<cdot>y) o conjugate (\<lambda>x. 1 \<lhd> x)" by simp
  hence "conjugate (conjugate (\<lambda>x. y \<lhd> x)) = conjugate ((\<lambda>x. x\<cdot>y) o conjugate (\<lambda>x. 1 \<lhd> x))" by simp
  hence "(\<lambda>x. y \<lhd> x) = conjugate ((\<lambda>x. x\<cdot>y) o conjugate (\<lambda>x. 1 \<lhd> x))" by simp
  also have "... = conjugate (conjugate (\<lambda>x. 1 \<lhd> x)) o conjugate (\<lambda>x. x\<cdot>y)"
    by (subst conjugate_comp[symmetric]) simp_all
  finally show "y \<lhd> x = 1 \<lhd> (x \<lhd> y)" by simp
next
  fix x y
  assume "\<forall>x y. y \<lhd> x = 1 \<lhd> (x \<lhd> y)"
  hence "(\<lambda>x. y \<lhd> x) = (\<lambda>x. 1 \<lhd> (x \<lhd> y))" by metis
  hence "(\<lambda>x. y \<lhd> x) = (\<lambda>x. 1 \<lhd> x) o conjugate (\<lambda>x. x\<cdot>y)" by force
  hence "conjugate (\<lambda>x. y \<lhd> x) = conjugate ((\<lambda>x. 1 \<lhd> x) o conjugate (\<lambda>x. x\<cdot>y))" by metis
  also have "... = conjugate (conjugate (\<lambda>x. x\<cdot>y)) o conjugate (\<lambda>x. 1 \<lhd> x)"
    by (subst conjugate_comp[symmetric]) simp_all
  finally have "(\<lambda>x. x \<rhd> y) = (\<lambda>x. x\<cdot>y) o (\<lambda>x. x \<rhd> 1)" by simp
  hence "(\<lambda>x. x \<rhd> y) = (\<lambda>x. (x \<rhd> 1) \<cdot> y)" by (simp add: comp_def)
  thus "x \<rhd> y = (x \<rhd> 1) \<cdot> y" by metis
qed

lemma jonsson2a: "(\<exists>g. \<forall>x y. x \<lhd> y = x\<cdot>g(y)) \<longleftrightarrow> (\<forall>x y. x \<lhd> y = x\<cdot>(1 \<lhd> y))"
  apply standard
  apply force
  apply (rule_tac x="\<lambda>x. 1 \<lhd> x" in exI)
  apply force
  done
  
lemma jonsson2b: "(\<forall>x y. x \<lhd> y = x\<cdot>(1 \<lhd> y)) \<longleftrightarrow> (\<forall>x y. x\<cdot>y = x \<lhd> (1 \<lhd> y))"
proof safe
  fix x y
  assume "\<forall>x y. x \<lhd> y = x\<cdot>(1 \<lhd> y)"
  hence "conjugate (\<lambda>x. x \<lhd> y) = conjugate (\<lambda>x. x\<cdot>(1 \<lhd> y))" by metis
  thus "x\<cdot>y = x \<lhd> (1 \<lhd> y)" by simp metis
next
  fix x y
  assume "\<forall>x y. x\<cdot>y = x \<lhd> (1 \<lhd> y)"
  hence "(\<lambda>x. x\<cdot>y) = (\<lambda>x. x \<lhd> (1 \<lhd> y))" by metis
  hence "conjugate (\<lambda>x. x\<cdot>y) = conjugate (\<lambda>x. x \<lhd> (1 \<lhd> y))" by metis
  thus "x \<lhd> y = x \<cdot> (1 \<lhd> y)" by simp metis
qed

lemma jonsson2c: "(\<forall>x y. x \<lhd> y = x\<cdot>(1 \<lhd> y)) \<longleftrightarrow> (\<forall>x y. y \<rhd> x = (x \<rhd> y) \<rhd> 1)"
proof safe
  fix x y
  assume "\<forall>x y. x \<lhd> y = x\<cdot>(1 \<lhd> y)"
  hence "(\<lambda>y. x \<lhd> y) = (\<lambda>y. x\<cdot>(1 \<lhd> y))" by metis
  hence "(\<lambda>y. x \<lhd> y) = (\<lambda>y. x\<cdot>y) o (\<lambda>y. 1 \<lhd> y)" by force
  hence "conjugate (\<lambda>y. y \<rhd> x) = (\<lambda>y. x\<cdot>y) o conjugate (\<lambda>y. y \<rhd> 1)" by force
  hence "conjugate (conjugate (\<lambda>y. y \<rhd> x)) = conjugate ((\<lambda>y. x\<cdot>y) o conjugate (\<lambda>y. y \<rhd> 1))" by metis
  hence "(\<lambda>y. y \<rhd> x) = conjugate ((\<lambda>y. x\<cdot>y) o conjugate (\<lambda>y. y \<rhd> 1))" by simp
  also have "... = conjugate (conjugate (\<lambda>y. y \<rhd> 1)) o conjugate (\<lambda>y. x\<cdot>y)"
    by (subst conjugate_comp[symmetric]) simp_all
  finally have "(\<lambda>y. y \<rhd> x) = (\<lambda>y. x \<rhd> y \<rhd> 1)" by (simp add: comp_def)
  thus "y \<rhd> x = x \<rhd> y \<rhd> 1" by metis 
next
  fix x y
  assume "\<forall>x y. y \<rhd> x = x \<rhd> y \<rhd> 1"
  hence "(\<lambda>y. y \<rhd> x) = (\<lambda>y. x \<rhd> y \<rhd> 1)" by force
  hence "(\<lambda>y. y \<rhd> x) = (\<lambda>y. y \<rhd> 1) o conjugate (\<lambda>y. x\<cdot>y)" by force
  hence "conjugate (\<lambda>y. y \<rhd> x) = conjugate ((\<lambda>y. y \<rhd> 1) o conjugate (\<lambda>y. x\<cdot>y))" by metis
  also have "... = conjugate (conjugate (\<lambda>y. x\<cdot>y)) o conjugate (\<lambda>y. y \<rhd> 1)"
    by (subst conjugate_comp[symmetric]) simp_all
  finally have "(\<lambda>y. x \<lhd> y) = (\<lambda>y. x\<cdot>y) o (\<lambda>y. 1 \<lhd> y)"
    by (metis conjugate_conjr1 conjugate_conjr2 conjugate_multr)
  thus "x \<lhd> y = x \<cdot> (1 \<lhd> y)" by (simp add: comp_def)
qed

lemma jonsson3a: "(\<forall>x. (x \<rhd> 1) \<rhd> 1 = x) \<longleftrightarrow> (\<forall>x. 1 \<lhd> (1 \<lhd> x) = x)"
proof safe
  fix x assume "\<forall>x. x \<rhd> 1 \<rhd> 1 = x"
  thus "1 \<lhd> (1 \<lhd> x) = x"
    by (metis compl_le_swap1 compl_le_swap2 conjr2_iff eq_iff)
next
  fix x assume "\<forall>x. 1 \<lhd> (1 \<lhd> x) = x"
  thus "x \<rhd> 1 \<rhd> 1 = x"
    by (metis conjugate_l_def conjugate_r_def double_compl jipsen2r)
qed

lemma jonsson3b: "(\<forall>x. (x \<rhd> 1) \<rhd> 1 = x) \<Longrightarrow> (x \<sqinter> y) \<rhd> 1 = (x \<rhd> 1) \<sqinter> (y \<rhd> 1)"
proof (rule antisym, auto simp: conjr2_iso)
  assume assm: "\<forall>x. (x \<rhd> 1) \<rhd> 1 = x"
  hence "(x \<rhd> 1) \<sqinter> (y \<rhd> 1) \<rhd> 1 = x \<sqinter> (((x \<rhd> 1) \<sqinter> (y \<rhd> 1) \<rhd> 1) \<sqinter> y)"
    by (metis (no_types) conjr2_iso inf.cobounded2 inf.commute inf.orderE)
  hence "(x \<rhd> 1) \<sqinter> (y \<rhd> 1) \<rhd> 1 \<le> x \<sqinter> y" 
    using inf.orderI inf_left_commute by presburger
  thus "(x \<rhd> 1) \<sqinter> (y \<rhd> 1) \<le> x \<sqinter> y \<rhd> 1" 
    using assm by (metis (no_types) conjr2_iso)
qed

lemma jonsson3c: "\<forall>x. (x \<rhd> 1) \<rhd> 1 = x \<Longrightarrow> x \<rhd> 1 = 1 \<lhd> x"
proof (rule indirect_eq)
  fix z
  assume assms: "\<forall>x. (x \<rhd> 1) \<rhd> 1 = x"
  hence "(x \<rhd> 1) \<sqinter> -z = \<bottom> \<longleftrightarrow> ((x \<rhd> 1) \<sqinter> -z) \<rhd> 1 = \<bottom>"
    by (metis compl_sup conjugation_conj double_compl inf_bot_right sup_bot.left_neutral)
  also have "... \<longleftrightarrow> -z\<cdot>x \<sqinter> 1 = \<bottom>"
    by (metis assms jonsson3b conjugation_multr)
  finally have "(x \<rhd> 1) \<sqinter> -z = \<bottom> \<longleftrightarrow> (1 \<lhd> x) \<sqinter> -z = \<bottom>"
    by (metis conjugation_multl inf.commute)
  thus "(x \<rhd> 1 \<le> z) \<longleftrightarrow> (1 \<lhd> x \<le> z)"
    by (metis le_iff_inf_bot)
qed 

end (* unital_residuated_boolean *)

class residuated_boolean_semigroup = residuated_boolean_algebra + semigroup_mult
begin

subclass residuated_boolean_algebra ..

text \<open>
  The following lemmas hold trivially, since they are equivalent to associativity.
\<close>

lemma res_assoc1: "x \<rhd> (y \<rhd> z) = y\<cdot>x \<rhd> z"
  by (metis res_assoc_iff1 mult_assoc)

lemma res_assoc2: "x \<lhd> (y \<cdot> z) = (x \<lhd> z) \<lhd> y"
  by (metis res_assoc_iff2 mult_assoc)

lemma res_assoc3: "(x \<rhd> y) \<lhd> z = x \<rhd> (y \<lhd> z)"
  by (metis res_assoc_iff3 mult_assoc)

end (*residuated_boolean_semigroup *)

class residuated_boolean_monoid = residuated_boolean_algebra + monoid_mult
begin

subclass unital_residuated_boolean
  by standard auto

subclass residuated_lmonoid ..

lemma jonsson4: "(\<forall>x y. x \<lhd> y = x\<cdot>(1 \<lhd> y)) \<longleftrightarrow> (\<forall>x y. x \<rhd> y = (x \<rhd> 1)\<cdot>y)"
proof safe
  fix x y assume assms: "\<forall>x y. x \<lhd> y = x\<cdot>(1 \<lhd> y)"
  have "x \<rhd> y = (y \<rhd> x) \<rhd> 1"
    by (metis assms jonsson2c)
  also have "... = (y \<rhd> ((x \<rhd> 1) \<rhd> 1)) \<rhd> 1"
    by (metis assms jonsson2b jonsson3a mult_oner)
  also have "... = (((x \<rhd> 1)\<cdot>y) \<rhd> 1) \<rhd> 1"
    by (metis conjugate_r_def double_compl resr3)
  also have "... = (x \<rhd> 1)\<cdot>y"
    by (metis assms jonsson2b jonsson3a mult_oner)
  finally show "x \<rhd> y = (x \<rhd> 1)\<cdot>y" .
next
  fix x y assume assms: "\<forall>x y. x \<rhd> y = (x \<rhd> 1)\<cdot>y"
  have "y \<lhd> x = 1 \<lhd> (x \<lhd> y)"
    by (metis assms jonsson1c)
  also have "... = 1 \<lhd> ((1 \<lhd> (1 \<lhd> x)) \<lhd> y)"
    by (metis assms conjugate_l_def double_compl jonsson1c mult_1_right resl3)
  also have "... = 1 \<lhd> (1 \<lhd> (y\<cdot>(1 \<lhd> x)))"
    by (metis conjugate_l_def double_compl resl3)
  also have "... = y\<cdot>(1 \<lhd> x)"
    by (metis assms jonsson1b jonsson1c jonsson3c mult_onel)
  finally show "y \<lhd> x = y\<cdot>(1 \<lhd> x)".
qed

end (* residuated_boolean_monoid *)

end
