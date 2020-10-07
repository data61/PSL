(* 
  Title: Fixpoint Fusion
  Author: Georg Struth 
  Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Fixpoint Fusion\<close>

theory Fixpoint_Fusion
  imports Galois_Connections

begin

text \<open>Least and greatest fixpoint fusion laws for adjoints in a Galois connection, 
including some variants, are proved in this section. Again, the laws for least and greatest fixpoints are duals. \<close>

lemma lfp_Fix:
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> lfp f = \<Sqinter>(Fix f)"
  unfolding lfp_def Fix_def
  apply (rule antisym)
  apply (simp add: Collect_mono Inf_superset_mono)
  by (metis (mono_tags) Inf_lower lfp_def lfp_unfold mem_Collect_eq)

lemma gfp_Fix:
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> gfp f = \<Squnion>(Fix f)"
  by (simp add: iso_map_dual gfp_to_lfp lfp_Fix Fix_map_dual_var Sup_to_Inf_var)

lemma gfp_little_fusion:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  and g :: "'b::complete_lattice \<Rightarrow> 'b"
  assumes "mono f"
  assumes "h \<circ> f \<le> g \<circ> h"
  shows "h (gfp f) \<le> gfp g"
proof-
  have "h (f (gfp f)) \<le> g (h (gfp f))"
    using assms(2) le_funD by fastforce
  hence "h (gfp f) \<le> g (h (gfp f))"
    by (simp add: assms(1) gfp_fixpoint)
  thus "h (gfp f) \<le> gfp g" 
    by (simp add: gfp_upperbound)
qed

lemma lfp_little_fusion:
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'a"
  and g :: "'b::complete_lattice_with_dual \<Rightarrow> 'b"
  assumes "mono f"
  assumes "g \<circ> h \<le> h \<circ> f"
  shows "lfp g \<le> h (lfp f)"
proof-
  have a: "mono (map_dual f)"
    by (simp add: assms iso_map_dual)
  have "map_dual h \<circ> map_dual f \<le> map_dual g \<circ> map_dual h"
    by (metis assms map_dual_anti map_dual_func1)
  thus ?thesis
    by (metis a comp_eq_elim dual_dual_ord fun_dual1 gfp_little_fusion lfp_dual_var map_dual_def)
qed

lemma gfp_fusion:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  and g :: "'b::complete_lattice \<Rightarrow> 'b"
  assumes "\<exists>f. f \<stileturn> h"
  and "mono f"
  and "mono g"
  and "h \<circ> f = g \<circ> h"
  shows "h (gfp f) = gfp g"
proof-
  have a: "h (gfp f) \<le> gfp g"
    by (simp add: assms(2) assms(4) gfp_little_fusion)
  obtain hl where conn: "\<forall>x y. (hl x \<le> y) \<longleftrightarrow> (x \<le> h y)"
    using assms adj_def by blast 
  have "hl \<circ> g \<le> hl \<circ> g \<circ> h \<circ> hl"
    by (simp add: le_fun_def, meson conn assms(3) monoE order_refl order_trans)
  also have "... = hl \<circ> h \<circ> f \<circ> hl"
    by (simp add: assms(4) comp_assoc)
  finally have "hl \<circ> g \<le> f \<circ> hl"
    by (simp add: le_fun_def, metis conn inf.coboundedI2 inf.orderE order_refl)
  hence "hl (gfp g) \<le> f (hl (gfp g))"
    by (metis comp_eq_dest_lhs gfp_unfold assms(3) le_fun_def)
  hence "hl (gfp g) \<le> gfp f"
    by (simp add: gfp_upperbound)
  hence "gfp g \<le> h (gfp f)"
    by (simp add: conn)
  thus ?thesis
    by (simp add: a eq_iff)
qed

lemma lfp_fusion:
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'a"
  and g :: "'b::complete_lattice_with_dual \<Rightarrow> 'b"
  assumes "\<exists>f. h \<stileturn> f"
  and "mono f"
  and "mono g"
  and "h \<circ> f = g \<circ> h"
  shows "h (lfp f) = lfp g"
proof-
  have a: "\<exists>f. map_dual f \<stileturn> map_dual h"
    using adj_dual assms(1) by auto
  have b: "mono (map_dual f)"
    by (simp add: assms(2) iso_map_dual)
  have c: "mono (map_dual g)"
    by (simp add: assms(3) iso_map_dual)
  have "map_dual h \<circ> map_dual f = map_dual g \<circ> map_dual h"
    by (metis assms(4) map_dual_func1)
  thus ?thesis   
    by (metis a adj_dual b c gfp_fusion ladj_adj ladj_radj_dual lfp_dual_var lfp_to_gfp_var radj_adj)
qed
 
lemma gfp_fusion_inf_pres:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  and g :: "'b::complete_lattice \<Rightarrow> 'b"
  assumes "Inf_pres h"
  and "mono f"
  and "mono g"
  and "h \<circ> f = g \<circ> h"
  shows "h (gfp f) = gfp g"
  by (simp add: Inf_pres_radj assms gfp_fusion)

lemma lfp_fusion_sup_pres:
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'a"
  and g :: "'b::complete_lattice_with_dual \<Rightarrow> 'b"
  assumes "Sup_pres h"
  and "mono f"
  and "mono g"
  and "h \<circ> f = g \<circ> h"
shows "h (lfp f) = lfp g"
  by (simp add: Sup_pres_ladj assms lfp_fusion)

text \<open>The following facts are usueful for the semantics of isotone predicate transformers. 
A dual statement for least fixpoints can be proved, but is not spelled out here.\<close>

lemma k_adju: 
  fixes k :: "'a::order \<Rightarrow> 'b::complete_lattice"
  shows "\<exists>F.\<forall>x. (F::'b \<Rightarrow> 'a \<Rightarrow> 'b) \<stileturn> (\<lambda>k. k y)"
  by (force intro!: fun_eq_iff Inf_pres_radj)

lemma k_adju_var: "\<exists>F. \<forall>x.\<forall>f::'a::order \<Rightarrow> 'b::complete_lattice. (F x \<le> f) = (x \<le> (\<lambda>k. k y) f)"
  using k_adju unfolding adj_def by simp

lemma gfp_fusion_var:
  fixes F :: "('a::order \<Rightarrow> 'b::complete_lattice) \<Rightarrow> 'a \<Rightarrow> 'b"
  and g :: "'b \<Rightarrow> 'b"
  assumes "mono F"
  and "mono g"
  and "\<forall>h. F h x = g (h x)"
  shows "gfp F x = gfp g"
  by (metis (no_types, hide_lams) assms eq_iff gfp_fixpoint gfp_upperbound k_adju_var monoE order_refl)

text \<open>This time, Isabelle is picking up dualities rather inconsistently.\<close>

end