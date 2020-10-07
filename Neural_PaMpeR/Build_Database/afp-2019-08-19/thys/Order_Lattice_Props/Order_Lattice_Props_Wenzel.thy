(* 
  Title: Duality Based on a Data Type
  Author: Georg Struth 
  Maintainer:Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Duality Based on a Data Type\<close>

theory Order_Lattice_Props_Wenzel
  imports Main 
          "HOL-Library.Lattice_Syntax"

begin

subsection \<open>Wenzel's Approach Revisited\<close>

text \<open>This approach is similar to, but inferior to the explicit class-based one. The main caveat is that duality is not involutive 
with this approach, and this allows dualising less theorems.\<close>

text \<open>I copy Wenzel's development \cite{Wenzel} in this subsection and extend it with additional properties. I show only the most important properties.\<close>

datatype 'a dual = dual (un_dual: 'a) ("\<partial>")

notation un_dual ("\<partial>\<^sup>-")

lemma dual_inj: "inj \<partial>"
  using injI by fastforce

lemma dual_surj: "surj \<partial>"
  using dual.exhaust_sel by blast

lemma dual_bij: "bij \<partial>"
  by (simp add: bijI dual_inj dual_surj)

text \<open>Dual is not idempotent, and I see no way of imposing this condition. Yet at least an inverse exists --- namely un-dual..\<close>

lemma dual_inv1 [simp]: "\<partial>\<^sup>- \<circ> \<partial> = id"
  by fastforce

lemma dual_inv2 [simp]: "\<partial> \<circ> \<partial>\<^sup>- = id"
  by fastforce

lemma dual_inv_inj: "inj \<partial>\<^sup>-"
  by (simp add: dual.expand injI)

lemma dual_inv_surj: "surj \<partial>\<^sup>-"
  by (metis dual.sel surj_def)

lemma dual_inv_bij: "bij \<partial>\<^sup>-"
  by (simp add: bij_def dual_inv_inj dual_inv_surj)

lemma dual_iff: "(\<partial> x = y) \<longleftrightarrow> (x = \<partial>\<^sup>- y)"
  by fastforce

text \<open>Isabelle data types come with a number of generic functions.\<close>

text \<open>The functor map-dual lifts functions to dual types. Isabelle's generic definition is not straightforward to 
understand and use. Yet conceptually it can be explained as follows.\<close>

lemma map_dual_def_var [simp]: "(map_dual::('a \<Rightarrow> 'b) \<Rightarrow> 'a dual \<Rightarrow> 'b dual) f = \<partial> \<circ> f \<circ> \<partial>\<^sup>-"  
  unfolding fun_eq_iff comp_def by (metis dual.map_sel dual_iff)

lemma map_dual_def_var2: "\<partial>\<^sup>- \<circ> map_dual f = f \<circ> \<partial>\<^sup>-"
  by (simp add: rewriteL_comp_comp)

lemma map_dual_func1: "map_dual (f \<circ> g) = map_dual f \<circ> map_dual g"
  unfolding fun_eq_iff comp_def by (metis dual.exhaust dual.map) 

lemma map_dual_func2 : "map_dual id = id"
  by simp

text \<open>The functor map-dual has an inverse functor as well.\<close>

definition map_dual_inv :: "('a dual \<Rightarrow> 'b dual) => ('a => 'b)" where
  "map_dual_inv f = \<partial>\<^sup>- \<circ> f \<circ> \<partial>"

lemma map_dual_inv_func1: "map_dual_inv id = id"
  by (simp add: map_dual_inv_def)

lemma map_dual_inv_func2: "map_dual_inv (f \<circ> g) = map_dual_inv f \<circ> map_dual_inv g"
  unfolding fun_eq_iff comp_def map_dual_inv_def by (metis dual_iff)

lemma map_dual_inv1: "map_dual \<circ> map_dual_inv = id"
  unfolding fun_eq_iff map_dual_def_var map_dual_inv_def comp_def id_def
  by (metis dual_iff) 

lemma map_dual_inv2: "map_dual_inv \<circ> map_dual = id"
  unfolding fun_eq_iff map_dual_def_var map_dual_inv_def comp_def id_def
  by (metis dual_iff) 

text \<open>Hence dual is an isomorphism between categories.\<close>

lemma subset_dual: "(\<partial> ` X = Y) \<longleftrightarrow> (X = \<partial>\<^sup>- ` Y)"
  by (metis dual_inj image_comp image_inv_f_f inv_o_cancel dual_inv2)

lemma subset_dual1: "(X \<subseteq> Y) \<longleftrightarrow> (\<partial> ` X \<subseteq> \<partial> ` Y)"
  by (simp add: dual_inj inj_image_subset_iff) 

lemma dual_ball: "(\<forall>x \<in> X. P (\<partial> x)) \<longleftrightarrow> (\<forall>y \<in> \<partial> ` X. P y)"
  by simp

lemma dual_inv_ball: "(\<forall>x \<in> X. P (\<partial>\<^sup>- x)) \<longleftrightarrow> (\<forall>y \<in> \<partial>\<^sup>- ` X. P y)"
  by simp

lemma dual_all: "(\<forall>x. P (\<partial> x)) \<longleftrightarrow> (\<forall>y. P y)"
  by (metis dual.collapse)

lemma dual_inv_all: "(\<forall>x. P (\<partial>\<^sup>- x)) \<longleftrightarrow> (\<forall>y. P y)"
  by (metis dual_inv_surj surj_def)

lemma dual_ex: "(\<exists>x. P (\<partial> x)) \<longleftrightarrow> (\<exists>y. P y)"  
  by (metis UNIV_I bex_imageD dual_surj)

lemma dual_inv_ex: "(\<exists>x. P (\<partial>\<^sup>- x)) \<longleftrightarrow> (\<exists>y. P y)"
  by (metis dual.sel)

lemma dual_Collect: "{\<partial> x |x. P (\<partial> x)} = {y. P y}"
  by (metis dual.exhaust)

lemma dual_inv_Collect: "{\<partial>\<^sup>- x |x. P (\<partial>\<^sup>- x)} = {y. P y}"
  by (metis dual.collapse dual.inject)

lemma fun_dual1: "(f \<circ> \<partial> = g) \<longleftrightarrow> (f = g \<circ> \<partial>\<^sup>-)"
  by auto

lemma fun_dual2: "(\<partial> \<circ> f = g) \<longleftrightarrow> (f = \<partial>\<^sup>- \<circ> g)"
  by auto

lemma fun_dual3: "(f \<circ> (`) \<partial> = g) \<longleftrightarrow> (f = g \<circ> (`) \<partial>\<^sup>-)"
  unfolding fun_eq_iff comp_def by (metis subset_dual)

lemma fun_dual4: "(f = \<partial>\<^sup>- \<circ> g \<circ> (`) \<partial>) \<longleftrightarrow> (\<partial> \<circ> f \<circ> (`) \<partial>\<^sup>- = g)"
  by (metis fun_dual2 fun_dual3 o_assoc)

text \<open>The next facts show incrementally that the dual of a complete lattice is a complete lattice.
This follows once again Wenzel.\<close>

instantiation dual :: (ord) ord
begin  

definition less_eq_dual_def: "(\<le>) = rel_dual (\<ge>)"

definition less_dual_def: "(<) = rel_dual (>)"

instance..

end

lemma less_eq_dual_def_var: "(x \<le> y) = (\<partial>\<^sup>- y \<le> \<partial>\<^sup>- x)"
  apply (rule antisym)
  apply (simp add: dual.rel_sel less_eq_dual_def)
  by (simp add: dual.rel_sel less_eq_dual_def)

lemma less_dual_def_var: "(x < y) = (\<partial>\<^sup>- y < \<partial>\<^sup>- x)"
  by (simp add: dual.rel_sel less_dual_def) 

instance dual :: (preorder) preorder
  apply standard
  apply (simp add: less_dual_def_var less_eq_dual_def_var less_le_not_le)
  apply (simp add: less_eq_dual_def_var)
  by (meson less_eq_dual_def_var order_trans)
 
instance dual :: (order) order
  by (standard, simp add: dual.expand less_eq_dual_def_var)

lemma dual_anti: "x \<le> y \<Longrightarrow> \<partial> y \<le> \<partial> x" 
  by (simp add: dual_inj less_eq_dual_def the_inv_f_f)

lemma dual_anti_iff: "(x \<le> y) = (\<partial> y \<le> \<partial> x)"
  by (simp add: dual_inj less_eq_dual_def the_inv_f_f)

text \<open>map-dual does not map isotone functions to antitone ones. It simply lifts the type!\<close>

lemma "mono f \<Longrightarrow> mono (map_dual f)"
  unfolding map_dual_def_var mono_def by (metis comp_apply dual_anti less_eq_dual_def_var)

instantiation dual :: (lattice) lattice
begin

definition inf_dual_def: "x \<sqinter> y = \<partial> (\<partial>\<^sup>- x \<squnion> \<partial>\<^sup>- y)"

definition sup_dual_def: "x \<squnion> y = \<partial> (\<partial>\<^sup>- x \<sqinter> \<partial>\<^sup>- y)"

instance
  by (standard, simp_all add: dual_inj inf_dual_def sup_dual_def less_eq_dual_def_var the_inv_f_f)

end

instantiation dual :: (complete_lattice) complete_lattice
begin

definition Inf_dual_def: "Inf = \<partial> \<circ> Sup \<circ> (`) \<partial>\<^sup>-"

definition Sup_dual_def: "Sup = \<partial> \<circ> Inf \<circ> (`) \<partial>\<^sup>-"

definition bot_dual_def: "\<bottom> = \<partial> \<top>"

definition top_dual_def: "\<top> = \<partial> \<bottom>"

instance
   by (standard, simp_all add: Inf_dual_def top_dual_def Sup_dual_def bot_dual_def dual_inj le_INF_iff SUP_le_iff INF_lower SUP_upper less_eq_dual_def_var the_inv_f_f)

end

text \<open>Next, directed and filtered sets, upsets, downsets, filters and ideals in posets are defined.\<close>

context ord
begin

definition directed :: "'a set \<Rightarrow> bool" where
 "directed X = (\<forall>Y. finite Y \<and> Y \<subseteq> X \<longrightarrow> (\<exists>x \<in> X. \<forall>y \<in> Y. y \<le> x))"

definition filtered :: "'a set \<Rightarrow> bool" where
 "filtered X = (\<forall>Y. finite Y \<and> Y \<subseteq> X \<longrightarrow> (\<exists>x \<in> X. \<forall>y \<in> Y. x \<le> y))"

definition downset_set :: "'a set \<Rightarrow> 'a set" ("\<Down>") where
  "\<Down>X = {y. \<exists>x \<in> X. y \<le> x}"

definition upset_set :: "'a set \<Rightarrow> 'a set" ("\<Up>") where
 "\<Up>X = {y. \<exists>x \<in> X. x \<le> y}"

end

subsection \<open>Examples that Do Not Dualise\<close>

text \<open>Filtered and directed sets are dual.\<close>

text \<open>Proofs could be simplified if dual was idempotent.\<close>

lemma filtered_directed_dual: "filtered \<circ> (`) \<partial> = directed"
proof-
  {fix X::"'a set"
    have "(filtered \<circ> (`) \<partial>) X = (\<forall>Y. finite (\<partial>\<^sup>- ` Y) \<and> \<partial>\<^sup>- ` Y \<subseteq> X \<longrightarrow> (\<exists>x \<in> X.\<forall>y \<in> (\<partial>\<^sup>- ` Y). \<partial> x \<le> \<partial> y))"
      unfolding filtered_def comp_def by (simp, metis dual_iff finite_subset_image subset_dual subset_dual1)
    also have "... = (\<forall>Y. finite Y \<and> Y \<subseteq> X \<longrightarrow> (\<exists>x \<in> X.\<forall>y \<in> Y. y \<le> x))"
      by (metis dual_anti_iff dual_inv_surj finite_subset_image top.extremum)
    finally have "(filtered \<circ> (`) \<partial>) X = directed X"
      using directed_def by auto}
  thus ?thesis
    unfolding fun_eq_iff by simp 
qed

lemma directed_filtered_dual: "directed \<circ> (`) \<partial> = filtered"
proof-
  {fix X::"'a set"
    have "(directed \<circ> (`) \<partial>) X = (\<forall>Y. finite (\<partial>\<^sup>- ` Y) \<and> \<partial>\<^sup>- ` Y \<subseteq> X \<longrightarrow> (\<exists>x \<in> X.\<forall>y \<in> (\<partial>\<^sup>- ` Y). \<partial> y \<le> \<partial> x))"
      unfolding directed_def comp_def by (simp, metis dual_iff finite_subset_image subset_dual subset_dual1)
  also have "... = (\<forall>Y. finite Y \<and> Y \<subseteq> X \<longrightarrow> (\<exists>x \<in> X.\<forall>y \<in> Y. x \<le> y))"
    unfolding dual_anti_iff[symmetric] by (metis dual_inv_surj finite_subset_image top_greatest)
  finally have "(directed \<circ> (`) \<partial>) X = filtered X"
    using filtered_def by auto}
  thus ?thesis
    unfolding fun_eq_iff by simp
qed

text \<open>This example illustrates the deficiency of the approach. In the class-based approach the second proof is trivial.\<close>

text \<open>The next example shows that this is a systematic problem.\<close>

lemma downset_set_upset_set_dual: "(`) \<partial> \<circ> \<Down> = \<Up> \<circ> (`) \<partial>"
  proof-
    {fix X::"'a set"
  have "((`) \<partial> \<circ> \<Down>) X = {\<partial> y |y. \<exists>x \<in> X. y \<le> x}"
    by (simp add: downset_set_def setcompr_eq_image)
  also have "... = {\<partial> y |y. \<exists>x \<in> X. \<partial> x \<le> \<partial> y}"
    by (meson dual_anti_iff)
  also have "... = {y. \<exists>x \<in> \<partial> ` X. x \<le> y}"
    by (metis (mono_tags, hide_lams) dual.exhaust image_iff)
  finally have "((`) \<partial> \<circ> \<Down>) X = (\<Up> \<circ> (`) \<partial>) X"
    by (simp add: upset_set_def)}
  thus ?thesis
    unfolding fun_eq_iff by simp
qed

lemma upset_set_downset_set_dual: "(`) \<partial> \<circ> \<Up> = \<Down> \<circ> (`) \<partial>"
  unfolding downset_set_def upset_set_def fun_eq_iff comp_def
  apply (safe, force simp: dual_anti)
  by (metis (mono_tags, lifting) dual.exhaust dual_anti_iff mem_Collect_eq rev_image_eqI)

end









