(* 
  Title: Isotone Transformers Between Complete Lattices
  Author: Georg Struth 
  Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Isotone Transformers Between Complete Lattices\<close>

theory Isotone_Transformers    
  imports "Order_Lattice_Props.Fixpoint_Fusion" 
          "Quantales.Quantale_Star"


begin

text \<open>A transformer is a function between lattices; an isotone transformer preserves the order (or is monotone). In this component, 
statements are developed in a type-driven way. Statements are developed in more general contexts or even the most general one.\<close>

subsection \<open>Basic Properties\<close>

text \<open>First I show that some basic transformers are isotone...\<close>

lemma iso_id: "mono id"
  by (simp add: monoI)

lemma iso_botf: "mono \<bottom>"
  by (simp add: monoI) 

lemma iso_topf: "mono \<top>"
  by (simp add: monoI)

text \<open>... and that compositions, Infs and Sups preserve isotonicity.\<close>

lemma iso_fcomp: "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (f \<circ> g)"
  by (simp add: mono_def)

lemma iso_fSup: 
  fixes F :: "('a::order \<Rightarrow> 'b::complete_lattice) set"
  shows "(\<forall>f \<in> F. mono f) \<Longrightarrow> mono (\<Squnion>F)"
  by (simp add: mono_def SUP_subset_mono)

lemma iso_fsup: "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (f \<squnion> g)"
  unfolding mono_def using sup_mono by fastforce

lemma iso_fInf: 
  fixes F :: "('a::order \<Rightarrow> 'b::complete_lattice) set"
  shows "\<forall>f \<in> F. mono f \<Longrightarrow> mono (\<Sqinter>F)"
  by (simp add: mono_def, safe, rule Inf_greatest, auto simp: INF_lower2)
 
lemma iso_finf: "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (f \<sqinter> g)"
  unfolding mono_def using inf_mono by fastforce
    
lemma fun_isol: "mono f \<Longrightarrow> g \<le> h \<Longrightarrow> (f \<circ> g) \<le> (f \<circ> h)"
  by (simp add: le_fun_def monoD)

lemma fun_isor: "mono f \<Longrightarrow> g \<le> h \<Longrightarrow> (g \<circ> f) \<le> (h \<circ> f)"
  by (simp add: le_fun_def monoD)


subsection \<open>Pre-Quantale of Isotone Transformers\<close>

text \<open>It is well known, and has been formalised within Isabelle, that functions into complete lattices form complete lattices.
In the following proof, this needs to be replayed because isotone functions are considered and closure conditions
need to be respected.

Functions must now be restricted to a single type.\<close>

instantiation iso :: (complete_lattice) unital_pre_quantale 
begin

lift_definition one_iso :: "'a::complete_lattice iso" is id
  by (simp add: iso_id)

lift_definition times_iso :: "'a::complete_lattice iso \<Rightarrow> 'a iso \<Rightarrow> 'a iso" is "(\<circ>)"
  by (simp add: iso_fcomp)

instance 
  by (intro_classes; transfer, simp_all add: comp_assoc fInf_distr_var fInf_subdistl_var)

end

text \<open>I have previously worked in (pre)quantales with many types or quantaloids. Formally, these are categories  
enriched over the category of Sup-lattices (complete lattices with Sup-preserving functions). An advantage 
of the single-typed approach is that the definition of the Kleene star for (pre)quantales is available in this setting.\<close>


subsection \<open>Propositional Hoare Logic for Transformers without Star\<close>

text \<open>The rules of an abstract Propositional Hoare logic are derivable.\<close>

lemma H_iso_cond1: "(x::'a::preorder) \<le> y \<Longrightarrow> y \<le> f z \<Longrightarrow> x \<le> f z"
  using order_trans by auto

lemma H_iso_cond2: "mono f \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> f y \<Longrightarrow> x \<le> f z"
  by (meson mono_def order_subst1)

lemma H_iso_seq: "mono f \<Longrightarrow> x \<le> f y \<Longrightarrow> y \<le> g z \<Longrightarrow> x \<le> f (g z)"
  using H_iso_cond2 by force

lemma H_iso_seq_var: "mono f \<Longrightarrow> x \<le> f y \<Longrightarrow> y \<le> g z \<Longrightarrow> x \<le> (f \<circ> g) z"
  by (simp add: H_iso_cond2)

lemma H_iso_fInf: 
  fixes F :: "('a \<Rightarrow> 'b::complete_lattice) set"
  shows "(\<forall>f \<in> F. x \<le> f y) \<Longrightarrow> x \<le> (\<Sqinter>F) y"
  by (simp add: le_INF_iff)

lemma H_iso_fSup: 
  fixes F :: "('a \<Rightarrow> 'b::complete_lattice) set"
  shows "F \<noteq> {} \<Longrightarrow> (\<forall>f \<in> F. x \<le> f y) \<Longrightarrow> x \<le> (\<Squnion>F) y"
  using SUP_upper2 by fastforce

text \<open>These rules are suitable for weakest liberal preconditions. Order-dual ones, in which the order relation is swapped,
are consistent with other kinds of transformers. In the context of dynamic logic, the first set corresponds to box modalities 
whereas the second one would correspond to diamonds.\<close>


subsection \<open>Kleene Star of Isotone Transformers\<close>
 
text \<open>The Hoare rule for loops requires some preparation. On the way I verify some Kleene-algebra-style axioms for iteration.\<close>

text \<open>First I show that functions form monoids.\<close>

interpretation fun_mon: monoid_mult "id::'a \<Rightarrow> 'a" "(\<circ>)"
  by unfold_locales auto

definition fiter_fun :: "('a \<Rightarrow> 'c::semilattice_inf) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" where 
  "fiter_fun f g = (\<sqinter>) f \<circ> (\<circ>) g"

definition fiter :: "('a \<Rightarrow> 'b::complete_lattice) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where 
  "fiter f g = gfp (fiter_fun f g)" 

definition fiter_id :: "('a::complete_lattice \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where 
  "fiter_id = fiter id"

abbreviation "fpower \<equiv> fun_mon.power"

definition fstar :: "('a::complete_lattice \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "fstar f = (\<Sqinter>i. fpower f i)"

text \<open>The types in the following statements are often more general than those in the prequantale setting. I develop them generally, 
instead of inheriting (most of them) with more restrictive types from the quantale components.\<close>

lemma fiter_fun_exp: "fiter_fun f g h = f \<sqinter> (g \<circ> h)"
  unfolding fiter_fun_def by simp

text \<open>The two lemmas that follow set up the relationship between the star for transformers and those in quantales.\<close>

lemma fiter_qiter1: "Abs_iso (fiter_fun (Rep_iso f) (Rep_iso g) (Rep_iso h)) = qiter_fun f g h"
  unfolding fiter_fun_def qiter_fun_def by (metis Rep_iso_inverse comp_def sup_iso.rep_eq times_iso.rep_eq)

lemma fiter_qiter4: "mono f \<Longrightarrow> mono g \<Longrightarrow> mono h \<Longrightarrow> Rep_iso (qiter_fun (Abs_iso f) (Abs_iso g) (Abs_iso h)) = fiter_fun f g h"
  by (metis Abs_iso_inverse fiter_fun_exp fiter_qiter1 iso_fcomp iso_finf mem_Collect_eq)

text \<open>The type coercions are needed to deal with isotone (monotone) functions, which had to be redefined to one single type above,
in order to cooperate with the type classes for quantales. Having to deal with these coercions would be another drawback of using the 
quantale-based setting for the development.\<close>

lemma iso_fiter_fun: "mono f \<Longrightarrow> mono (fiter_fun f)" 
  by (simp add: fiter_fun_exp le_fun_def mono_def inf.coboundedI2)

lemma iso_fiter_fun2: "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (fiter_fun f g)" 
  by (simp add: fiter_fun_exp le_fun_def mono_def inf.coboundedI2)

lemma fiter_unfoldl: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> mono g \<Longrightarrow> f \<sqinter> (g \<circ> fiter f g) = fiter f g"
  by (metis fiter_def fiter_fun_exp gfp_unfold iso_fiter_fun2)

lemma fiter_inductl: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> mono g \<Longrightarrow> h \<le> f \<sqinter> (g \<circ> h) \<Longrightarrow> h \<le> fiter f g"
  by (simp add: fiter_def fiter_fun_def gfp_upperbound)
 
lemma fiter_fusion: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes "mono f" 
  and "mono g"
shows "fiter f g = fiter_id g \<circ> f"
proof-
  have h1: "mono (fiter_fun id g)"
    by (simp add: assms(2) iso_fiter_fun2 iso_id)
  have h2: "mono (fiter_fun f g)"
    by (simp add: assms(1) assms(2) iso_fiter_fun2)
  have h3: "Inf \<circ> image (\<lambda>x. x \<circ> f) = (\<lambda>x. x \<circ> f) \<circ> Inf" 
    by (simp add: fun_eq_iff image_comp)
  have "(\<lambda>x. x \<circ> f) \<circ> (fiter_fun id g) = (fiter_fun f g) \<circ> (\<lambda>x. x \<circ> f)"
    by (simp add: fun_eq_iff fiter_fun_def) 
  thus ?thesis
    using gfp_fusion_inf_pres
    by (metis fiter_def fiter_id_def h1 h2 h3) 
qed

lemma fpower_supdistl: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "mono f \<Longrightarrow> f \<circ> fstar g \<le> (\<Sqinter>i. f \<circ> fpower g i)"
  by (simp add: Isotone_Transformers.fun_isol fstar_def mono_INF mono_def)

lemma fpower_distr: "fstar f \<circ> g = (\<Sqinter>i. fpower f i \<circ> g)"
  by (auto simp: fstar_def image_comp)

lemma fpower_Sup_subcomm: "mono f \<Longrightarrow> f \<circ> fstar f \<le> fstar f \<circ> f"
  by (metis (mono_tags, lifting) fun_mon.power_commutes le_INF_iff fpower_distr fpower_supdistl)

lemma fpower_inductl: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> mono g \<Longrightarrow> h \<le> g \<sqinter> (f \<circ> h) \<Longrightarrow> h \<le> fpower f i \<circ> g"
  apply (induct i, simp_all) by (metis (no_types, hide_lams) fun.map_comp fun_isol order_trans) 

lemma fpower_inductr: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> mono g \<Longrightarrow> h \<le> g \<sqinter> (h \<circ> f) \<Longrightarrow> h \<le> g \<circ> fpower f i"
  by (induct i, simp_all add: le_fun_def, metis comp_eq_elim fun_mon.power_commutes order_trans)

lemma fiter_fstar: "mono f \<Longrightarrow> fiter_id f \<le> fstar f"
  by (metis (no_types, lifting) fiter_id_def fiter_unfoldl fpower_inductl fstar_def iso_id le_INF_iff o_id order_refl)

lemma iso_fiter_ext: 
  fixes f :: "'a::order \<Rightarrow> 'b::complete_lattice"
  shows "mono f \<Longrightarrow> mono (\<lambda>x. y \<sqinter> f x)"
  by (simp add: le_infI2 mono_def)

lemma fstar_pred_char: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> fiter_id f x = gfp (\<lambda>y. x \<sqinter> f y)"
proof -
  assume hyp: "mono f"
  have "\<forall>g. (id \<sqinter> (f \<circ> g)) x = x \<sqinter> f (g x)"
    by simp
  hence "\<forall>g. fiter_fun id f g x = (\<lambda>y. x \<sqinter> f y) (g x)"
    unfolding fiter_fun_def by simp
  thus ?thesis
    by (simp add: fiter_id_def fiter_def gfp_fusion_var hyp iso_fiter_fun2 iso_id iso_fiter_ext)
qed


subsection \<open>Propositional Hoare Logic Completed\<close>
 
lemma H_weak_loop: "mono f \<Longrightarrow> x \<le> f x \<Longrightarrow> x \<le> fiter_id f x"
  by (force simp: fstar_pred_char gfp_def intro: Sup_upper)

lemma iso_fiter: "mono f \<Longrightarrow> mono (fiter_id f)"
  unfolding mono_def by (subst fstar_pred_char, simp add: mono_def)+ (auto intro: gfp_mono inf_mono) 

text \<open>As already mentioned, a dual Hoare logic can be built for the dual lattice. In this case, weak iteration is defined with respect to Sup.\<close>

text \<open>The following standard construction lifts elements of (meet semi)lattices to transformers.
I allow a more general type.\<close>

definition fqtran :: "'a::inf \<Rightarrow> 'a \<Rightarrow> 'a" where
  "fqtran x \<equiv> \<lambda>y. x \<sqinter> y"

text \<open>The following standard construction lifts elements of boolean algebras to transformers.\<close>

definition bqtran :: "'a::boolean_algebra \<Rightarrow> 'a \<Rightarrow> 'a" ("\<lfloor>_\<rfloor>") where
  "\<lfloor>x\<rfloor> y = -x \<squnion> y"

text \<open>The conditional and while rule of Hoare logic are now derivable.\<close>

lemma bqtran_iso: "mono \<lfloor>x\<rfloor>"
  by (metis bqtran_def monoI order_refl sup.mono)

lemma cond_iso: "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (\<lfloor>x\<rfloor> \<circ> f \<sqinter> \<lfloor>y\<rfloor> \<circ> g)"
  by (simp add: bqtran_iso iso_fcomp iso_finf)

lemma loop_iso: "mono f \<Longrightarrow> mono (fiter_id (\<lfloor>x\<rfloor> \<circ> f) \<circ> \<lfloor>y\<rfloor>)"
  by (simp add: bqtran_iso iso_fcomp iso_fiter)

lemma H_iso_cond: "mono f \<Longrightarrow> mono g \<Longrightarrow>  p \<sqinter> x \<le> f y \<Longrightarrow> q \<sqinter> x \<le> g y \<Longrightarrow> x \<le> (inf (\<lfloor>p\<rfloor> \<circ> f) (\<lfloor>q\<rfloor> \<circ> g)) y"
  by (metis (full_types) bqtran_def comp_apply inf_apply inf_commute le_inf_iff shunt1)

lemma H_iso_loop: "mono f \<Longrightarrow> p \<sqinter> x \<le> f x \<Longrightarrow> x \<le> ((fiter_id (\<lfloor>p\<rfloor> \<circ> f)) \<circ> \<lfloor>q\<rfloor>) (x \<sqinter> q)"
proof-
  assume a: "mono f"
and "p \<sqinter> x \<le> f x"
  hence "x \<le> (\<lfloor>p\<rfloor> \<circ> f) x"
    using H_iso_cond by fastforce 
  hence "x \<le> (fiter_id (\<lfloor>p\<rfloor> \<circ> f)) x"
    by (simp add: H_weak_loop a bqtran_iso iso_fcomp)
  also have "... \<le> (fiter_id (\<lfloor>p\<rfloor> \<circ> f)) (-q \<squnion> (x \<sqinter> q))"
    by (meson a bqtran_iso dual_order.refl iso_fcomp iso_fiter monoD shunt1)
  finally show "x \<le> ((fiter_id (\<lfloor>p\<rfloor> \<circ> f)) \<circ> \<lfloor>q\<rfloor>) (x \<sqinter> q)"
    by (simp add: bqtran_def)
qed

lemma btran_spec: "x \<le> \<lfloor>y\<rfloor> (x \<sqinter> y)"
  by (simp add: bqtran_def sup_inf_distrib1)

lemma btran_neg_spec: "x \<le> \<lfloor>-y\<rfloor> (x - y)"
  by (simp add: btran_spec diff_eq)


subsection \<open>A Propositional Refinement Calculus\<close>

text \<open>Next I derive the laws of an abstract Propositional Refinement Calculus, Morgan-style. 
These are given without the co-called frames, which capture information about local and global variables in variants of this calculus.\<close>

definition "Ri x y z = \<Sqinter>{f z |f. x \<le> f y \<and> mono (f::'a::order \<Rightarrow> 'b::complete_lattice)}"

lemma Ri_least: "mono f \<Longrightarrow> x \<le> f y \<Longrightarrow> Ri x y z \<le> f z"
  unfolding Ri_def by (metis (mono_tags, lifting) Inf_lower mem_Collect_eq)
 
lemma Ri_spec: "x \<le> Ri x y y"
  unfolding Ri_def by (rule Inf_greatest, safe)

lemma Ri_spec_var: "(\<forall>z. Ri x y z \<le> f z) \<Longrightarrow> x \<le> f y"
  using Ri_spec dual_order.trans by blast 

lemma Ri_prop: "mono f \<Longrightarrow> x \<le> f y \<longleftrightarrow> (\<forall>z. Ri x y z \<le> f z)"
  using Ri_least Ri_spec_var by blast

lemma iso_Ri: "mono (Ri x y)"
  unfolding mono_def Ri_def by (auto intro!: Inf_mono) 

lemma Ri_weaken: "x \<le> x' \<Longrightarrow>  y' \<le> y \<Longrightarrow> Ri x y z \<le> Ri x' y' z"
  by (meson H_iso_cond2 Ri_least Ri_spec iso_Ri order.trans)
 
lemma Ri_seq: "Ri x y z \<le> Ri x w (Ri w y z)"
  by (metis (no_types, hide_lams) H_iso_cond2 Ri_prop Ri_spec iso_Ri iso_fcomp o_apply)

lemma Ri_seq_var: "Ri x y z \<le> ((Ri x w) \<circ> (Ri w y)) z"
  by (simp add: Ri_seq)

lemma Ri_Inf: " Ri (\<Sqinter> X) y z \<le> \<Sqinter>{Ri x y z |x. x \<in> X}"
  by (safe intro!: Inf_greatest, simp add: Ri_weaken Inf_lower)

lemma Ri_weak_iter: "Ri x x y  \<le> fiter_id (Ri x x) y"
  by (simp add: H_weak_loop Ri_least Ri_spec iso_Ri iso_fiter)

lemma Ri_cond: "Ri x y z \<le> (inf (\<lfloor>p\<rfloor> \<circ> (Ri (p \<sqinter> x) y)) ((\<lfloor>q\<rfloor> \<circ> (Ri (q \<sqinter> x) y)))) z"
  by (meson H_iso_cond Ri_least Ri_spec bqtran_iso iso_Ri iso_fcomp iso_finf)

lemma Ri_loop: "Ri x (q \<sqinter> x) y \<le> ((fiter_id (\<lfloor>p\<rfloor> \<circ> (Ri (x \<sqinter> p) x))) \<circ> \<lfloor>q\<rfloor>) (q \<sqinter> y)"
proof-
  have "(p \<sqinter> x) \<le> Ri (p \<sqinter> x) x x"
    by (simp add: Ri_spec)
  hence "x \<le> ((fiter_id (\<lfloor>p\<rfloor> \<circ> (Ri (x \<sqinter> p) x))) \<circ> \<lfloor>q\<rfloor>) (q \<sqinter> x)"
    by (metis H_iso_loop inf_commute iso_Ri)
  thus ?thesis
    apply (subst Ri_least, safe, simp_all add: mono_def)
    by (metis bqtran_iso inf_mono iso_Ri iso_fcomp iso_fiter mono_def order_refl)
qed

end
