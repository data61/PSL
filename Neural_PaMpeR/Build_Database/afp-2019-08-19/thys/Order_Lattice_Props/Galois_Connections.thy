(* 
  Title: Galois Connections
  Author: Georg Struth 
  Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Galois Connections\<close>

theory Galois_Connections
  imports Order_Lattice_Props

begin

subsection \<open>Definitions and Basic Properties\<close>

text \<open>The approach follows the Compendium of Continuous Lattices~\cite{GierzHKLMS80}, without attempting completeness. 
First, left and right adjoints of a Galois connection are defined.\<close>

definition adj :: "('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" (infixl "\<stileturn>" 70) where 
  "(f \<stileturn> g) = (\<forall>x y. (f x \<le> y) = (x \<le> g y))"

definition "ladj (g::'a::Inf \<Rightarrow> 'b::ord) = (\<lambda>x. \<Sqinter>{y. x \<le> g y})"

definition "radj (f::'a::Sup \<Rightarrow> 'b::ord)  = (\<lambda>y. \<Squnion>{x. f x \<le> y})"

lemma ladj_radj_dual:
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::ord_with_dual"
  shows "ladj f x = \<partial> (radj (\<partial>\<^sub>F f) (\<partial> x))"
proof-
  have "ladj f x = \<partial> (\<Squnion>(\<partial> ` {y. \<partial> (f y) \<le> \<partial> x}))"
    unfolding ladj_def by (metis (no_types, lifting) Collect_cong Inf_dual_var dual_dual_ord dual_iff)
  also have "... =  \<partial> (\<Squnion>{\<partial> y|y. \<partial> (f y) \<le> \<partial> x})"
    by (simp add: setcompr_eq_image)
  ultimately show ?thesis
    unfolding ladj_def radj_def map_dual_def comp_def
    by (smt Collect_cong invol_dual_var)
qed

lemma radj_ladj_dual: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::ord_with_dual"
  shows "radj f x = \<partial> (ladj (\<partial>\<^sub>F f) (\<partial> x))"
  by (metis fun_dual5 invol_dual_var ladj_radj_dual map_dual_def)

lemma ladj_prop: 
  fixes g :: "'b::Inf \<Rightarrow> 'a::ord_with_dual"
  shows "ladj g = Inf \<circ> (-`) g \<circ> \<up>"
  unfolding ladj_def vimage_def upset_prop fun_eq_iff comp_def by simp

lemma radj_prop: 
  fixes f :: "'b::Sup \<Rightarrow> 'a::ord"
  shows "radj f = Sup \<circ> (-`) f \<circ> \<down>"
  unfolding radj_def vimage_def downset_prop fun_eq_iff comp_def by simp

text \<open>The first set of properties holds without any sort assumptions.\<close>

lemma adj_iso1: "f \<stileturn> g \<Longrightarrow> mono f"
  unfolding adj_def mono_def by (meson dual_order.refl dual_order.trans) 

lemma adj_iso2: "f \<stileturn> g \<Longrightarrow> mono g"
  unfolding adj_def mono_def by (meson dual_order.refl dual_order.trans) 

lemma adj_comp: "f \<stileturn> g \<Longrightarrow> adj h k \<Longrightarrow> (f \<circ> h) \<stileturn> (k \<circ> g)"
  by (simp add: adj_def)

lemma adj_dual: 
  fixes f :: "'a::ord_with_dual \<Rightarrow> 'b::ord_with_dual"
  shows "f \<stileturn> g = (\<partial>\<^sub>F g) \<stileturn> (\<partial>\<^sub>F f)"
  unfolding adj_def map_dual_def comp_def by (metis (mono_tags, hide_lams) dual_dual_ord invol_dual_var)

subsection \<open>Properties for (Pre)Orders\<close>

text \<open>The next set of properties holds in preorders or orders.\<close>

lemma adj_cancel1: 
  fixes f :: "'a::preorder \<Rightarrow> 'b::ord"
  shows "f \<stileturn> g \<Longrightarrow> f \<circ> g \<le> id"
  by (simp add: adj_def le_funI)

lemma adj_cancel2: 
  fixes f :: "'a::ord \<Rightarrow> 'b::preorder"
  shows "f \<stileturn> g \<Longrightarrow> id \<le> g \<circ> f"
  by (simp add: adj_def eq_iff le_funI)

lemma adj_prop: 
  fixes f :: "'a::preorder \<Rightarrow>'a"
  shows "f \<stileturn> g \<Longrightarrow> f \<circ> g \<le> g \<circ> f"
  using adj_cancel1 adj_cancel2 order_trans by blast

lemma adj_cancel_eq1: 
  fixes f :: "'a::preorder \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> f \<circ> g \<circ> f = f"
  unfolding adj_def comp_def fun_eq_iff by (meson eq_iff order_refl order_trans)

lemma adj_cancel_eq2: 
  fixes f :: "'a::order \<Rightarrow> 'b::preorder"
  shows "f \<stileturn> g \<Longrightarrow> g \<circ> f \<circ> g = g"
  unfolding adj_def comp_def fun_eq_iff by (meson eq_iff order_refl order_trans) 

lemma adj_idem1: 
  fixes f :: "'a::preorder \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> (f \<circ> g) \<circ> (f \<circ> g) = f \<circ> g"
  by (simp add: adj_cancel_eq1 rewriteL_comp_comp)

lemma adj_idem2: 
  fixes f :: "'a::order \<Rightarrow> 'b::preorder"
  shows "f \<stileturn> g \<Longrightarrow> (g \<circ> f) \<circ> (g \<circ> f) = g \<circ> f"
  by (simp add: adj_cancel_eq2 rewriteL_comp_comp)

lemma adj_iso3: 
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> mono (f \<circ> g)"
   by (simp add: adj_iso1 adj_iso2 monoD monoI)

lemma adj_iso4: 
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> mono (g \<circ> f)"
  by (simp add: adj_iso1 adj_iso2 monoD monoI)

lemma adj_canc1: 
  fixes f :: "'a::order \<Rightarrow> 'b::ord"
  shows "f \<stileturn> g \<Longrightarrow> ((f \<circ> g) x = (f \<circ> g) y \<longrightarrow> g x = g y)"
  unfolding adj_def comp_def by (metis eq_iff)
 
lemma adj_canc2: 
  fixes f :: "'a::ord \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> ((g \<circ> f) x = (g \<circ> f) y \<longrightarrow> f x = f y)"
  unfolding adj_def comp_def by (metis eq_iff)

lemma adj_sur_inv: 
  fixes f :: "'a::preorder \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> ((surj f) = (f \<circ> g = id))"
  unfolding adj_def surj_def comp_def by (metis eq_id_iff eq_iff order_refl order_trans)

lemma adj_surj_inj: 
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> ((surj f) = (inj g))"
  unfolding adj_def inj_def surj_def by (metis eq_iff order_trans)

lemma adj_inj_inv: 
  fixes f :: "'a::preorder \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> ((inj f) = (g \<circ> f = id))"
  by (metis adj_cancel_eq1 eq_id_iff inj_def o_apply)

lemma adj_inj_surj: 
  fixes f :: "'a::order \<Rightarrow> 'b::order" 
  shows "f \<stileturn> g \<Longrightarrow> ((inj f) = (surj g))"
  unfolding adj_def inj_def surj_def by (metis eq_iff order_trans)

lemma surj_id_the_inv: "surj f \<Longrightarrow> g \<circ> f = id \<Longrightarrow> g = the_inv f"
  by (metis comp_apply id_apply inj_on_id inj_on_imageI2 surj_fun_eq the_inv_f_f)

lemma inj_id_the_inv: "inj f \<Longrightarrow> f \<circ> g = id \<Longrightarrow> f = the_inv g"
proof -
  assume a1: "inj f"
  assume "f \<circ> g = id"
  hence "\<forall>x. the_inv g x = f x"
    using a1 by (metis (no_types) comp_apply eq_id_iff inj_on_id inj_on_imageI2 the_inv_f_f)
  thus ?thesis 
    by presburger
qed


subsection \<open>Properties for Complete Lattices\<close>

text \<open>The next laws state that a function between complete lattices preserves infs 
  if and only if it has a lower adjoint.\<close>

lemma radj_Inf_pres: 
  fixes g :: "'b::complete_lattice \<Rightarrow> 'a::complete_lattice"
  shows "(\<exists>f. f \<stileturn> g) \<Longrightarrow> Inf_pres g"
  apply (rule antisym, simp_all add: le_fun_def adj_def, safe)
  apply (meson INF_greatest Inf_lower dual_order.refl dual_order.trans)
  by (meson Inf_greatest dual_order.refl le_INF_iff)

lemma ladj_Sup_pres: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual"
  shows "(\<exists>g. f \<stileturn> g) \<Longrightarrow> Sup_pres f"
  using Sup_pres_map_dual_var adj_dual radj_Inf_pres by blast

lemma radj_adj: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "f \<stileturn> g \<Longrightarrow> g = (radj f)"
  unfolding adj_def radj_def by (metis (mono_tags, lifting) cSup_eq_maximum eq_iff mem_Collect_eq)

lemma ladj_adj: 
  fixes g :: "'b::complete_lattice_with_dual \<Rightarrow> 'a::complete_lattice_with_dual" 
  shows "f \<stileturn> g \<Longrightarrow> f = (ladj g)"
  unfolding adj_def ladj_def by (metis (no_types, lifting) cInf_eq_minimum eq_iff mem_Collect_eq)

lemma Inf_pres_radj_aux: 
  fixes g :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Inf_pres g \<Longrightarrow> (ladj g) \<stileturn> g"
proof-
  assume a: "Inf_pres g"
  {fix x y
   assume b: "ladj g x \<le> y" 
  hence "g (ladj g x) \<le> g y"
    by (simp add: Inf_subdistl_iso a monoD)
  hence "\<Sqinter>{g y |y. x \<le> g y} \<le> g y"
    by (metis a comp_eq_dest_lhs setcompr_eq_image ladj_def)
  hence "x \<le> g y"
    using dual_order.trans le_Inf_iff by blast  
  hence "ladj g x \<le> y \<longrightarrow> x \<le> g y"
    by simp}
  thus ?thesis 
    unfolding adj_def ladj_def by (meson CollectI Inf_lower)
qed

lemma Sup_pres_ladj_aux: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual" 
  shows "Sup_pres f \<Longrightarrow> f \<stileturn> (radj f)"
  by (metis (no_types, hide_lams) Inf_pres_radj_aux Sup_pres_map_dual_var adj_dual fun_dual5 map_dual_def radj_adj)

lemma Inf_pres_radj: 
  fixes g :: "'b::complete_lattice \<Rightarrow> 'a::complete_lattice"
  shows "Inf_pres g \<Longrightarrow> (\<exists>f. f \<stileturn> g)"
  using Inf_pres_radj_aux by fastforce

lemma Sup_pres_ladj: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual"
  shows "Sup_pres f \<Longrightarrow> (\<exists>g. f \<stileturn> g)"
  using Sup_pres_ladj_aux by fastforce

lemma Inf_pres_upper_adj_eq: 
  fixes g :: "'b::complete_lattice \<Rightarrow> 'a::complete_lattice"
  shows "(Inf_pres g) = (\<exists>f. f \<stileturn> g)"
  using radj_Inf_pres Inf_pres_radj by blast

lemma Sup_pres_ladj_eq:
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual"
  shows  "(Sup_pres f) = (\<exists>g. f \<stileturn> g)"
  using Sup_pres_ladj ladj_Sup_pres by blast

lemma Sup_downset_adj: "(Sup::'a::complete_lattice set \<Rightarrow> 'a) \<stileturn> \<down>"
  unfolding adj_def downset_prop Sup_le_iff by force

lemma Sup_downset_adj_var: "(Sup (X::'a::complete_lattice set) \<le> y) = (X \<subseteq> \<down>y)"
  using Sup_downset_adj adj_def by auto

text \<open>Once again many statements arise by duality, which Isabelle usually picks up.\<close>


end