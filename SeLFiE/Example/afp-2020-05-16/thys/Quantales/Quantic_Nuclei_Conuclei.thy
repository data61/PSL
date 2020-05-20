(* Title: Quantic Nuclei and Conuclei
   Author: Georg Struth
   Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Quantic Nuclei and Conuclei\<close>

theory Quantic_Nuclei_Conuclei
  imports Quantale_Models 

begin

text \<open>Quantic nuclei and conuclei are an important part of the structure theory of quantales. I formalise
the basics, following Rosenthal's book~\cite{Rosenthal90}. In the structure theorems, I collect all parts 
of the proof, but do not present the theorems in compact form due to difficulties to speak about subalgebras 
and homomorphic images without explicit carrier sets. Nuclei also arise in the context of complete Heyting algebras,
frames and locales~\cite{Johnstone82}. Their formalisation seems an interesting future task.\<close>

subsection \<open>Nuclei\<close>

definition nucleus :: "('a::quantale \<Rightarrow> 'a::quantale) \<Rightarrow> bool" where 
  "nucleus f = (clop f \<and> (\<forall>x y. f x \<cdot> f y \<le> f (x \<cdot> y)))"

lemma nuc_lax: "nucleus f \<Longrightarrow> f x \<cdot> f y \<le> f (x \<cdot> y)"
  by (simp add: nucleus_def)   

definition unucleus :: "('a::unital_quantale \<Rightarrow> 'a::unital_quantale) \<Rightarrow> bool" where 
  "unucleus f = (nucleus f \<and> 1 \<le> f 1)"

lemma "nucleus f \<Longrightarrow> f \<bottom> = \<bottom>" (*nitpick*)
  oops

lemma "conucleus f \<Longrightarrow> f \<top> = \<top>" (*nitpick*)
  oops

lemma nuc_prop1: "nucleus f \<Longrightarrow> f (x \<cdot> y) = f (x \<cdot> f y)"
  apply (rule antisym)
   apply (simp add: clop_extensive_var clop_iso_var nucleus_def psrpq.mult_isol)
  by (metis clop_alt clop_extensive_var dual_order.trans nucleus_def psrpq.mult_isol_var)

lemma nuc_prop2: "nucleus f \<Longrightarrow> f (x \<cdot> y) = f (f x \<cdot> y)"
  apply (rule antisym)
  apply (simp add: clop_extensive_var clop_iso_var nsrnq.mult_isor nucleus_def)
  by (metis (mono_tags, hide_lams) clop_alt nuc_prop1 nucleus_def)

lemma nuc_comp_prop: "nucleus f \<Longrightarrow>  f (f x \<cdot> f y) = f (x \<cdot> y)"
  using nuc_prop1 nuc_prop2 by force

lemma nucleus_alt_def1: "nucleus f \<Longrightarrow> f x \<rightarrow> f y = x \<rightarrow> f y"
proof (rule antisym)
  assume h: "nucleus f" 
  hence "x \<le> f x"
    by (simp add: clop_def nucleus_def clop_extensive_var)
  thus "f x \<rightarrow> f y \<le> x \<rightarrow> f y"
    by (simp add: bres_anti)
  have "f x \<cdot> (x \<rightarrow> f y) \<le> f x \<cdot> f (x \<rightarrow> f y)"
    using clop_extensive_var h nucleus_def proto_pre_quantale_class.mult_isol by blast
  also have "... \<le> f (x \<cdot> (x \<rightarrow> f y))"
    by (simp add: h nuc_lax)
  also have "... \<le> f (f y)"
    using h by (simp add: bres_canc1 nucleus_def clop_iso_var) 
  finally have "f x \<cdot> (x \<rightarrow> f y) \<le> f y"
    using h by (metis clop_alt dual_order.trans nucleus_def order_refl)
  thus "x \<rightarrow> f y \<le> f x \<rightarrow> f y"
    by (simp add: bres_galois_imp)
qed

lemma nucleus_alt_def2: "nucleus f \<Longrightarrow> f y \<leftarrow> f x = f y \<leftarrow> x"
proof (rule antisym)
  assume h: "nucleus f" 
  hence "x \<le> f x"
    by (simp add: clop_extensive_var nucleus_def)
  thus "f y \<leftarrow> f x \<le> f y \<leftarrow> x"
    by (simp add: fres_anti)
  have "(f y \<leftarrow> x) \<cdot> f x \<le> f (f y \<leftarrow> x) \<cdot> f x"
    using clop_extensive_var h nsrnq.mult_isor nucleus_def by blast
  also have "... \<le> f ((f y \<leftarrow> x) \<cdot> x)"
    by (simp add: h nuc_lax)
  also have "... \<le> f (f y)"
    using clop_iso_var fres_canc1 h nucleus_def by blast
  finally have "(f y \<leftarrow> x) \<cdot> f x \<le> f y"
    using h by (metis clop_alt dual_order.trans nucleus_def order_refl)
  thus "f y \<leftarrow> x \<le> f y \<leftarrow> f x"
    by (simp add: fres_galois)
qed

lemma nucleus_alt_def3: 
  fixes f :: "'a::unital_quantale \<Rightarrow> 'a"
  shows "\<forall>x y. f x \<rightarrow> f y = x \<rightarrow> f y \<Longrightarrow> \<forall>x y. f y \<leftarrow> f x = f y \<leftarrow> x \<Longrightarrow> nucleus f"
proof-
  assume h1: "\<forall>x y. f x \<rightarrow> f y = x \<rightarrow> f y"
  and h2: "\<forall>x y. f y \<leftarrow> f x = f y \<leftarrow> x"
  hence ext: "\<forall>x. x \<le> f x"
    by (metis (full_types) fres_galois fres_one mult.left_neutral)
  have iso: "\<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y"
    by (metis (full_types) bres_galois dual_order.trans h1 ext nsrnqo.mult_oner)
  have trans: "\<forall>x. f (f x) \<le> f x"
    by (metis fres_canc2 fres_galois h2 nsrnqo.mult_onel)
  have lax: "\<forall>x y. f x \<cdot> f y \<le> f (x \<cdot> y)"
    by (metis h1 h2 bres_galois ext fres_galois)
  show ?thesis
    by (simp add: clop_def iso lax le_funI ext trans monoI nucleus_def)
qed

lemma nucleus_alt_def: 
  fixes f :: "'a::unital_quantale \<Rightarrow> 'a"
  shows "nucleus f = (\<forall> x y. f x \<rightarrow> f y = x \<rightarrow> f y \<and> f y \<leftarrow> f x = f y \<leftarrow> x)"
  using nucleus_alt_def1 nucleus_alt_def2 nucleus_alt_def3 by blast

lemma nucleus_alt_def_cor1: "nucleus f \<Longrightarrow> f (x \<rightarrow> y) \<le> x \<rightarrow> f y"
  by (metis bres_galois bres_iso clop_extensive_var fres_galois nucleus_alt_def2 nucleus_def)

lemma nucleus_alt_def_cor2: "nucleus f \<Longrightarrow> f (y \<leftarrow> x) \<le> f y \<leftarrow> x"
  by (metis bres_galois clop_extensive_var fres_galois fres_iso nucleus_alt_def1 nucleus_def)

lemma nucleus_ab_unital: 
  fixes f :: "'a::ab_unital_quantale \<Rightarrow> 'a"
  shows "nucleus f = (\<forall>x y. f x \<rightarrow> f y = x \<rightarrow> f y)"
  by (simp add: bres_fres_eq nucleus_alt_def)

lemma nuc_comp_assoc: "nucleus f \<Longrightarrow> f (x \<cdot> f (y \<cdot> z)) = f (f (x \<cdot> y) \<cdot> z)"
  by (metis mult.assoc nuc_prop1 nuc_prop2)

lemma nuc_Sup_closed: "nucleus f \<Longrightarrow> f \<circ> Sup \<circ> (`) f = (f \<circ> Sup)"
  apply (simp add: nucleus_def fun_eq_iff, safe, rule antisym)
  apply (meson SUP_least Sup_upper clop_alt clop_def monoD)
  by (simp add: SUP_upper2 Sup_le_iff clop_extensive_var clop_iso_var)

lemma nuc_Sup_closed_var: "nucleus f \<Longrightarrow> f (\<Squnion>x \<in> X. f x) = f (\<Squnion>X)"
  by (metis nuc_Sup_closed o_apply)

lemma nuc_Inf_closed: "nucleus f \<Longrightarrow> Sup_closed_set (Fix f)" (* nitpick *)
  oops

lemma nuc_Inf_closed: "nucleus f \<Longrightarrow> Inf_closed_set (Fix f)"   
  by (simp add: clop_Inf_closed nucleus_def)

lemma nuc_comp_distl: "nucleus f \<Longrightarrow> f (x \<cdot> f (\<Squnion>Y)) = f (\<Squnion>y \<in> Y. f (x \<cdot> y))"
  by (metis Sup_distl image_image nuc_Sup_closed_var nuc_prop1)

lemma nuc_comp_distr: "nucleus f \<Longrightarrow> f (f (\<Squnion>X) \<cdot> y) = f (\<Squnion>x \<in> X. f (x \<cdot> y))"
  by (metis image_image Sup_distr nuc_Sup_closed_var nuc_prop2)

lemma "nucleus f \<Longrightarrow> f (x \<cdot> y) = f x \<cdot> f y" (*nitpick*)
  oops

lemma nuc_bres_closed: "nucleus f \<Longrightarrow> f (f x \<rightarrow> f y) = f x \<rightarrow> f y"
  unfolding nucleus_def apply clarsimp
  by (smt clop_closure clop_extensive_var nucleus_alt_def_cor1 nucleus_def order_class.order.antisym rangeI)

lemma "nucleus f \<Longrightarrow> f (x \<rightarrow> y) = f x \<rightarrow> f y" (*nitpick*)
  oops

lemma nuc_fres_closed: "nucleus f \<Longrightarrow> f (f x \<leftarrow> f y) = f x \<leftarrow> f y"
  unfolding nucleus_def apply clarsimp
  by (smt clop_closure clop_extensive_var eq_iff nucleus_alt_def_cor2 nucleus_def rangeI)

lemma nuc_fres_closed: "nucleus f \<Longrightarrow> f (x \<leftarrow> y) = f x \<leftarrow> f y" (*nitpick*)
  oops

lemma nuc_inf_closed: "nucleus f \<Longrightarrow> inf_closed_set (Fix f)"
  by (simp add: Inf_inf_closed nuc_Inf_closed)

lemma nuc_inf_closed_var: "nucleus f \<Longrightarrow> f (f x \<sqinter> f y) = f x \<sqinter> f y"
  by (smt antisym_conv clop_alt clop_extensive_var inf_le2 inf_sup_ord(1) le_inf_iff nucleus_def)

text \<open>Taken together these facts show that, for $f:Q\to Q$, $f[Q]$ forms a quantale with 
composition $f\, (-\cdot -)$ and sup $f\, (\bigsqcup -)$, and that $f:Q\to f[Q]$ is a quantale morphism. 
This is the first part of Theorem 3.1.1 in Rosenthal's book.\<close>

class quantale_with_nuc = quantale + cl_op +
  assumes cl_op_nuc: "cl_op x \<cdot> cl_op y \<le> cl_op (x \<cdot> y)"

begin

subclass clattice_with_clop..

end

class unital_quantale_with_nuc = quantale_with_nuc + unital_quantale +
  assumes one_nuc: "1 \<le> cl_op 1"

lemma nucleus_cl_op: "nucleus (cl_op::'a::quantale_with_nuc \<Rightarrow> 'a)"
  by (simp add: cl_op_class.clop_iso cl_op_nuc  clop_def clop_ext le_funI monoI nucleus_def)

lemma unucleus_cl_op: "unucleus (cl_op::'a::unital_quantale_with_nuc \<Rightarrow> 'a)"
  by (simp add: nucleus_cl_op one_nuc unucleus_def)

instantiation cl_op_im :: (quantale_with_nuc) quantale
begin

lift_definition times_cl_op_im :: "'a::quantale_with_nuc cl_op_im \<Rightarrow> 'a cl_op_im \<Rightarrow> 'a cl_op_im" is "\<lambda>x y. cl_op (x \<cdot> y)"
  by simp

instance
  by (intro_classes; transfer, auto simp: nuc_comp_assoc nuc_comp_distr nucleus_cl_op nuc_comp_distl)

end

instantiation cl_op_im :: (unital_quantale_with_nuc) unital_quantale
begin

lift_definition one_cl_op_im :: "'a::unital_quantale_with_nuc cl_op_im" is "cl_op 1"
  by simp

instance
  by (intro_classes; transfer) (metis clop_closure nsrnqo.mult_onel nuc_prop2 nucleus_cl_op nucleus_def nsrnqo.mult_oner nuc_prop1)+

end


text \<open>The usefulness of these theorems remains unclear; it seems difficult to make them collaborate with concrete nuclei.\<close>

lemma nuc_hom: "Abs_cl_op_im \<circ> cl_op \<in> quantale_homset"
  unfolding quantale_homset_iff comp_def fun_eq_iff
  apply safe
  apply (metis (no_types, lifting) Abs_cl_op_im_inverse Rep_cl_op_im_inverse nuc_comp_prop nucleus_cl_op rangeI times_cl_op_im.rep_eq)
  unfolding Sup_cl_op_im_def by (smt Abs_cl_op_im_inverse SUP_cong image_image map_fun_apply nuc_Sup_closed_var nucleus_cl_op rangeI)

text \<open>This finishes the first statement of Theorem 3.1.1. The second part follows. It states that for every 
surjective quantale homomorphism there is a nucleus such that the range of the nucleus is isomorphic to the range of the surjection.\<close> 
 
lemma quant_morph_nuc:
  fixes f :: "'a::quantale_with_dual \<Rightarrow> 'b::quantale_with_dual"
  assumes "f \<in> quantale_homset" 
  shows "nucleus ((radj f) \<circ> f)"
proof-
  let ?\<phi> = "(radj f) \<circ> f"
  have adj: "f \<stileturn> (radj f)"
    by (simp add: assms quantale_hom_radj)
  hence a: "clop ?\<phi>"
    by (simp add: clop_adj)
  {fix x y
    have "f (?\<phi> x \<cdot> ?\<phi> y) = (f \<circ> ?\<phi>) x \<cdot> (f \<circ> ?\<phi>) y"
      by (metis assms comp_eq_dest_lhs quantale_homset_iff)
  also have "... = f x \<cdot> f y"
    by (simp add: adj adj_cancel_eq1 fun.map_comp)
  also have "... = f (x \<cdot> y)"
    by (metis assms quantale_homset_iff)
  finally have "?\<phi> x \<cdot> ?\<phi> y \<le> ?\<phi> (x \<cdot> y)"
    by (metis adj adj_def comp_apply order_refl)}
  thus ?thesis
    by (simp add: a nucleus_def)
qed 

lemma surj_quantale_hom_bij_on: 
  fixes f :: "'a::quantale_with_dual \<Rightarrow> 'b::quantale_with_dual"
  assumes "surj f"
  and "f \<in> quantale_homset"
  shows "bij_betw f (range (radj f \<circ> f)) UNIV"
  using assms quantale_homset_iff surj_Sup_pres_bij_on by blast

text \<open>This establishes the bijection, extending a similar fact about closure operators and complete lattices (surj-Sup-pres-bij). 
It remains to show that $f$ is a quantale morphism, that is, it preserves Sups and compositions of closed elements with operations 
defined as in the previous instantiation statement. Sup-preservation holds already for closure operators on complete lattices (surj-Sup-pres-iso).
Hence it remains to prove preservation of compositions.\<close>

lemma surj_comp_pres_iso: 
  fixes f :: "'a::quantale_with_dual \<Rightarrow> 'b::quantale_with_dual"
  assumes "f \<in> quantale_homset"
  shows "f ((radj f \<circ> f) (x \<cdot> y)) = f x \<cdot> f y"
proof-
  have "f \<stileturn> (radj f)"
    by (simp add: assms quantale_hom_radj)
  hence "f ((radj f \<circ> f) (x \<cdot> y)) = f (x \<cdot> y)"
    by (metis adj_cancel_eq1 comp_eq_dest_lhs) 
  thus ?thesis
    using assms quantale_homset_iff by auto
qed

text \<open>This establishes the quantale isomorphism and finishes the proof of Theorem 3.1.1.\<close>

text \<open>Next I prove Theorem 3.1.2 in Rosenthal's book. nuc-Inf-closed shows that $\mathit{Fix}\, f$ is Inf-closed. Hence the two following 
lemmas show one direction.\<close>

lemma nuc_bres_pres: "nucleus f \<Longrightarrow> y \<in> Fix f \<Longrightarrow> x \<rightarrow> y \<in> Fix f"
proof -
  assume a1: "nucleus f"
  assume a2: "y \<in> Fix f"
  have "clop f"
    using a1 by (simp add: nucleus_def)
  thus ?thesis
    using a2 a1
    by (metis clop_Fix_range clop_closure clop_extensive_var dual_order.antisym nucleus_alt_def_cor1) 
qed

lemma nuc_fres_pres: "nucleus f \<Longrightarrow> y \<in> Fix f \<Longrightarrow> y \<leftarrow> x \<in> Fix f"
proof -
  assume a1: "nucleus f"
  assume a2: "y \<in> Fix f"
  have "clop f"
    using a1 by (simp add: nucleus_def)
  thus ?thesis
    using a2 a1 by (metis antisym_conv clop_Fix_range clop_closure clop_extensive_var nucleus_alt_def_cor2) 
qed

lemma lax_aux: 
  fixes X :: "'a::quantale set"
  assumes "\<forall>x.\<forall>y \<in> X. x \<rightarrow> y \<in> X"
  and "\<forall>x. \<forall>y \<in> X. y \<leftarrow> x \<in> X"
shows "\<Sqinter>{z \<in> X. x \<le> z} \<cdot> \<Sqinter>{z \<in> X. y \<le> z} \<le> \<Sqinter>{z \<in> X. x \<cdot> y \<le> z}"
proof-
  let ?\<phi> = "\<lambda>x. \<Sqinter>{w \<in> X. x \<le> w}"
  {fix z
  assume a: "x \<cdot> y \<le> z"
  and b: "z \<in> X"
  hence c: "x \<le> z \<leftarrow> y"
    by (simp add: fres_galois)
  hence "z \<leftarrow> y \<in> X"
    by (simp add: assms(2) b)
  hence "?\<phi> x \<le> z \<leftarrow> y"
    by (simp add: Inf_lower c)
  hence d: "y \<le> ?\<phi> x \<rightarrow> z"
    by (simp add: bres_galois_imp fres_galois)
  hence "?\<phi> x  \<rightarrow> z \<in> X"
    by (simp add: assms(1) b)
  hence "?\<phi> x \<cdot> ?\<phi> y \<le> z"
    by (simp add: Inf_lower d bres_galois)}
  thus ?thesis
    by (simp add: le_Inf_iff)
qed

lemma Inf_closed_res_nuc: 
  fixes X :: "'a::quantale set"
  assumes "Inf_closed_set X"
  and  "\<forall>x. \<forall>y \<in> X. x \<rightarrow> y \<in> X"
  and "\<forall>x. \<forall>y \<in> X. y \<leftarrow> x \<in> X"
  shows "nucleus (\<lambda>y. \<Sqinter>{x \<in> X. y \<le> x})"
  unfolding nucleus_def by (simp add: Inf_closed_clop assms lax_aux)

lemma Inf_closed_res_Fix: 
  fixes X :: "'a::quantale set"
  assumes "Inf_closed_set X"
  and  "\<forall>x. \<forall>y \<in> X. x \<rightarrow> y \<in> X"
  and "\<forall>x. \<forall>y \<in> X. y \<leftarrow> x \<in> X"
shows "X = Fix (\<lambda>y. \<Sqinter>{x \<in> X. y \<le> x})"
  unfolding Fix_def
  apply safe
   apply (rule antisym, simp_all add: Inf_lower le_Inf_iff) 
  by (metis (no_types, lifting) Inf_closed_set_def assms(1) mem_Collect_eq subsetI)

text \<open>This finishes the proof of Theorem 3.1.2\<close>


subsection \<open>A Representation Theorem\<close>

text \<open>The final proofs for nuclei lead to Rosenthal's representation theorem for quantales (Theorem 3.1.2).\<close>

lemma down_set_lax_morph: "(\<down> \<circ> Sup) (X::'a::quantale set) \<cdot> (\<down> \<circ> Sup) Y \<subseteq> (\<down> \<circ> Sup) (X \<cdot> Y)"
proof-
  have "\<Squnion>((\<down> \<circ> Sup) X \<cdot> (\<down> \<circ> Sup) Y) = \<Squnion>(X \<cdot> Y)"
    by (smt Sup_downset_adj adj_cancel_eq1 comp_apply comp_dist_mix)
  thus ?thesis
    by (simp add: Sup_downset_adj_var eq_iff)
qed

lemma downset_Sup_nuc: "nucleus (\<down> \<circ> (Sup::'a::quantale set \<Rightarrow> 'a))"
  using Sup_downset_adj clop_adj down_set_lax_morph nucleus_def by blast

lemma downset_surj: "surj_on \<down> (range (\<down> \<circ> Sup))"
  using surj_on_def by fastforce

text \<open>In addition, $\downarrow$ is injective by Lemma downset-inj. Hence it is a bijection between the quantale and the powerset quantale. 
It remains to show that $\downarrow$ is a quantale morphism.\<close>

lemma downset_Sup_pres_var: "\<down> (\<Squnion>X) = (\<down> \<circ> Sup) (\<Down> (X::'a::quantale set))"
  unfolding comp_def downset_prop downset_set_def 
  apply safe
  apply (smt Sup_subset_mono dual_order.refl mem_Collect_eq order_subst1 subset_iff)
  by (smt Sup_mono le_iff_inf le_infI2 mem_Collect_eq)

lemma downset_Sup_pres: "\<down> (\<Squnion>X) = (\<down> \<circ> Sup) (\<Union> (\<down> ` (X::'a::quantale set)))"
  by (metis downset_Sup_pres_var downset_set_prop_var)  

lemma downset_comp_pres: "\<down> ((x::'a::quantale) \<cdot> y) = (\<down> \<circ> Sup) (\<down>x \<cdot> \<down>y)"
  by (metis (no_types, hide_lams) Sup_downset_adj_var comp_apply comp_dist_mix downset_iso_iff dual_order.antisym order_refl)

text \<open>This finishes the proof of Theorem 3.1.2.\<close>
 

subsection \<open>Conuclei\<close>

definition conucleus :: "('a::quantale \<Rightarrow> 'a::quantale) \<Rightarrow> bool" where
  "conucleus f = (coclop f \<and> (\<forall>x y. f x \<cdot> f y \<le> f (x \<cdot> y)))"

lemma conuc_lax: "conucleus f \<Longrightarrow> f x \<cdot> f y \<le> f (x \<cdot> y)"
  by (simp add: conucleus_def)

definition uconucleus :: "('a::unital_quantale \<Rightarrow> 'a::unital_quantale) \<Rightarrow> bool" where 
  "uconucleus f = (conucleus f \<and> f 1 \<le> 1)"

text \<open>Next I prove Theorem 3.1.3.\<close> 

lemma conuc_Sup_closed: "conucleus f \<Longrightarrow> f \<circ> Sup \<circ> (`) f = Sup \<circ> (`) f" 
  unfolding conucleus_def fun_eq_iff comp_def
  by (smt coclop_coextensive_var coclop_idem coclop_iso image_comp image_image le_iff_sup mono_SUP sup.orderE)

lemma conuc_comp_closed: "conucleus f \<Longrightarrow> f (f x \<cdot> f y) = f x \<cdot> f y"
  unfolding conucleus_def by (metis antisym_conv coclop_coextensive_var coclop_idem_var)

text \<open>The sets of fixpoints of conuclei are closed under Sups and composition; hence they form subquantales.\<close>

lemma conuc_Sup_qclosed: "conucleus f \<Longrightarrow> Sup_closed_set (Fix f) \<and> comp_closed_set (Fix f)"
  apply safe
   apply (simp add: coclop_Sup_closed conucleus_def)
  unfolding conucleus_def comp_closed_set_def by (metis coclop_coclosure coclop_coclosure_set coclop_coextensive_var dual_order.antisym)

text \<open>This shows that the subset $\mathit{Fix} f$ of a quantale, for conucleus $f$, is closed under Sups and composition. 
It is therefore a subquantale. $f:f[Q]\to Q$ is an embedding. As before, this could be shown by formalising a type class of quantales with a conucleus operation,
converting the range of the conucleus into a type and providing a sublocale proof. First, this would require showing that the coclosed 
elements of a complete lattice form a complete sublattice. Relative to the proofs for closure operators and nuclei there is nothing to 
be learned. I provide this proof in the section on left-sided elements, where the conucleus can be expressed within the language of quantales.\<close>

text \<open>The second part of Theorem 3.1.3 states that every subquantale of a given quantale is equal to $\mathit{Fix} f$ for some conucleus $f$.\<close>

lemma lax_aux2: 
  fixes X :: "'a::quantale set"
  assumes "Sup_closed_set X"
  and "comp_closed_set X"
  shows "\<Squnion>{z \<in> X. z \<le> x} \<cdot> \<Squnion>{z \<in> X. z \<le> y} \<le> \<Squnion>{z \<in> X. z \<le> x \<cdot> y}"
proof-
  let ?\<phi> = "\<lambda>x. \<Squnion>{z \<in> X. z \<le> x}"
  have "?\<phi> x \<cdot> ?\<phi> y = \<Squnion>{\<Squnion>{v \<cdot> w |v. v \<in> X \<and> v \<le> x} |w. w \<in> X \<and> w \<le> y}"
    by (simp add: Sup_distr Sup_distl setcompr_eq_image)
  also have "... = \<Squnion>{v \<cdot> w |v w. v \<in> X \<and> v \<le> x \<and> w \<in> X \<and> w \<le> y}"
    apply (rule antisym)
    apply (rule Sup_least, clarsimp, smt Collect_mono_iff Sup_subset_mono)
    by (rule Sup_least, clarsimp, smt Sup_upper2 eq_iff mem_Collect_eq)
  also have "... \<le> ?\<phi> (x \<cdot> y)"
    by (smt Collect_mono_iff Sup_subset_mono assms(2) comp_closed_set_def psrpq.mult_isol_var)
  finally show ?thesis
    by force
qed

lemma subquantale_conucleus: 
  fixes X :: "'a::quantale set"
  assumes "Sup_closed_set X"
  and "comp_closed_set X"
  shows "conucleus (\<lambda>x. \<Squnion>{y \<in> X. y \<le> x})" 
  unfolding conucleus_def by (safe, simp_all add: Sup_closed_coclop assms(1) assms(2) lax_aux2)

lemma subquantale_Fix: 
  fixes X :: "'a::quantale set"
  assumes "Sup_closed_set X"
  and "comp_closed_set X"
  shows "X = Fix (\<lambda>x. \<Squnion>{y \<in> X. y \<le> x})"
  unfolding Fix_def
  apply safe
  apply (metis (mono_tags, lifting) Sup_least Sup_upper antisym mem_Collect_eq order_refl)
  by (metis (no_types, lifting) Sup_closed_set_def assms(1) mem_Collect_eq subsetI)

text \<open>This finishes the proof of Theorem 3.1.3\<close>

end
