(* 
  Title: Sup- and Inf-Preserving Transformers Between Complete Lattices
  Author: Georg Struth 
  Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Sup- and Inf-Preserving Transformers between Complete Lattices\<close>

theory Sup_Inf_Preserving_Transformers       
  imports Isotone_Transformers

begin

subsection \<open>Basic Properties\<close>

text \<open>Definitions and basic properties of Sup-preserving and Inf-preserving functions can be found in the Lattice components.
The main purose of the lemmas that follow is to bring properties of isotone transformers into scope.\<close>

lemma Sup_pres_iso: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Sup_pres f \<Longrightarrow> mono f"
  by (simp add: Sup_supdistl_iso)

lemma Inf_pres_iso: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Inf_pres f \<Longrightarrow> mono f"
  by (simp add: Inf_subdistl_iso)

lemma sup_pres_iso: 
  fixes f :: "'a::lattice \<Rightarrow> 'b::lattice"
  shows "sup_pres f \<Longrightarrow> mono f"
  by (metis le_iff_sup mono_def)

lemma inf_pres_iso: 
  fixes f :: "'a::lattice \<Rightarrow> 'b::lattice"
  shows "inf_pres f \<Longrightarrow> mono f"
  by (metis inf.absorb_iff2 monoI)

lemma Sup_sup_dual: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Sup_dual f \<Longrightarrow> sup_dual f"
  by (smt comp_eq_elim image_empty image_insert inf_Inf sup_Sup)

lemma Inf_inf_dual: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Inf_dual f \<Longrightarrow> inf_dual f"
  by (smt comp_eq_elim image_empty image_insert inf_Inf sup_Sup)

lemma Sup_bot_dual: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows"Sup_dual f \<Longrightarrow> bot_dual f"
  by (metis INF_empty Sup_empty comp_eq_elim)

lemma Inf_top_dual: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Inf_dual f \<Longrightarrow> top_dual f"
  by (metis Inf_empty SUP_empty comp_eq_elim)

text \<open>Next I show some basic preservation properties.\<close>

lemma Sup_dual2: "Sup_dual f \<Longrightarrow> Inf_dual g \<Longrightarrow> Sup_pres (g \<circ> f)"
  by (simp add: fun_eq_iff image_comp)

lemma Inf_dual2: "Sup_dual f \<Longrightarrow> Inf_dual g \<Longrightarrow> Inf_pres (f \<circ> g)"
  by (simp add: fun_eq_iff image_comp)
 
lemma Sup_pres_id: "Sup_pres id"
  by simp

lemma Inf_pres_id: "Inf_pres id"
  by simp

lemma Sup_pres_comp: "Sup_pres f \<Longrightarrow> Sup_pres g \<Longrightarrow> Sup_pres (f \<circ> g)"
  by (simp add: fun_eq_iff image_comp)

lemma Inf_pres_comp: "Inf_pres f \<Longrightarrow> Inf_pres g \<Longrightarrow> Inf_pres(f \<circ> g)"
  by (simp add: fun_eq_iff image_comp)

lemma Sup_pres_Sup: 
  fixes F :: "('a::complete_lattice \<Rightarrow> 'b::complete_lattice) set"
  shows "\<forall>f \<in> F. Sup_pres f \<Longrightarrow> Sup_pres (\<Squnion>F)"
proof-
  assume h: "\<forall>f \<in> F. f \<circ> Sup = Sup \<circ> image f"
  hence "\<forall>f \<in> F. f \<circ> Sup \<le> Sup \<circ> image (\<Squnion>F)"
    by (simp add: SUP_subset_mono Sup_upper le_fun_def)
  hence "(\<Squnion>F) \<circ> Sup \<le> Sup \<circ> image (\<Squnion>F)"
    by (simp add: SUP_le_iff le_fun_def)
  thus ?thesis
    by (simp add: Sup_pres_iso h antisym iso_Sup_supdistl iso_fSup)
qed

lemma Inf_pres_Inf: 
  fixes F :: "('a::complete_lattice \<Rightarrow> 'b::complete_lattice) set"
  shows "\<forall>f \<in> F. Inf_pres f \<Longrightarrow> Inf_pres (\<Sqinter>F)"
proof-
  assume h: "\<forall>f \<in> F. f \<circ> Inf = Inf \<circ> image f"
  hence "\<forall>f \<in> F. Inf \<circ> image (\<Sqinter>F) \<le> f \<circ> Inf"
    by (simp add: le_fun_def, safe, meson INF_lower INF_mono)
  hence "Inf \<circ> image (\<Sqinter>F) \<le> (\<Sqinter>F) \<circ> Inf"
    by (simp add: le_INF_iff le_fun_def)
  thus ?thesis
    by (simp add: Inf_pres_iso h antisym iso_Inf_subdistl iso_fInf)
qed

lemma Sup_pres_sup: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Sup_pres f \<Longrightarrow> Sup_pres g \<Longrightarrow> Sup_pres (f \<squnion> g)"
  by (metis Sup_pres_Sup insert_iff singletonD sup_Sup)

lemma Inf_pres_inf: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Inf_pres f \<Longrightarrow> Inf_pres g \<Longrightarrow> Inf_pres (f \<sqinter> g)"
  by (metis Inf_pres_Inf inf_Inf insert_iff singletonD)

lemma Sup_pres_botf: "Sup_pres (\<lambda>x. \<bottom>::'a::complete_lattice)"
  by (simp add: fun_eq_iff)

text \<open>It is important to note that $\lambda x. \bot$ is not Inf-preserving and that $\lambda x. \top$ is not Sup-preserving.\<close>
 
lemma "Inf_pres (\<lambda>x. \<bottom>::'a::complete_lattice)" (*nitpick[show_all]*)
  oops

lemma "Sup_pres (\<lambda>x. \<top>::'a::complete_lattice)" (*nitpick[show_all]*)
  oops

lemma Inf_pres_topf: "Inf_pres (\<lambda>x. \<top>::'a::complete_lattice)"
  by (simp add: fun_eq_iff)

text \<open>In complete boolean algebras, complementation yields an explicit variant of duality, which 
can be expressed within the language.\<close>

lemma uminus_galois: 
  fixes f :: "'a::complete_boolean_algebra \<Rightarrow> 'b::complete_boolean_algebra_alt"
  shows "(uminus f = g) = (uminus g = f)"
  using double_compl by force

lemma uminus_galois_var: 
  fixes f :: "'a::complete_boolean_algebra_alt_with_dual \<Rightarrow> 'b::complete_boolean_algebra_alt_with_dual"
  shows "(\<partial> \<circ> f = g) = (\<partial> \<circ> g = f)"
  by force

lemma uminus_galois_var2: 
  fixes f :: "'a::complete_boolean_algebra_alt_with_dual \<Rightarrow> 'b::complete_boolean_algebra_alt_with_dual"
  shows "(f \<circ> \<partial> = g) = (g \<circ> \<partial> = f)"
  by force

lemma uminus_mono_iff: 
  fixes f :: "'a::complete_boolean_algebra_alt_with_dual \<Rightarrow> 'b::complete_boolean_algebra_alt_with_dual"
  shows "(\<partial> \<circ> f = \<partial> \<circ> g) = (f = g)"
  using uminus_galois_var by force

lemma uminus_epi_iff: 
  fixes f :: "'a::complete_boolean_algebra_alt_with_dual \<Rightarrow> 'b::complete_boolean_algebra_alt_with_dual"
  shows "(f \<circ> \<partial> = g \<circ> \<partial>) = (f = g)"
  using uminus_galois_var2 by force

lemma Inf_pres_Sup_pres: 
  fixes f :: "'a::complete_boolean_algebra_alt_with_dual \<Rightarrow> 'b::complete_boolean_algebra_alt_with_dual"
  shows "(Inf_pres f) = (Sup_pres (\<partial>\<^sub>F f))"
  by (simp add: Inf_pres_map_dual_var)

lemma Sup_pres_Inf_pres: 
  fixes f :: "'a::complete_boolean_algebra_alt_with_dual \<Rightarrow> 'b::complete_boolean_algebra_alt_with_dual"
  shows "(Sup_pres f) = (Inf_pres (\<partial>\<^sub>F f))"
  by (simp add: Sup_pres_map_dual_var)


subsection \<open>Properties of the Kleene Star\<close>

text \<open>I develop the star for Inf-preserving functions only. This is suitable for weakest liberal preconditions. 
The case of sup-preserving functions is dual, and straightforward. The main difference to isotone transformers is that Kleene's fixpoint theorem
now applies, that is, the star can be represented by iteration.\<close>

lemma  H_Inf_pres_fpower:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "Inf_pres f \<Longrightarrow> x \<le> f x \<Longrightarrow> x \<le> fpower f i x"
  apply (induct i, simp_all) using H_iso_cond2 Inf_pres_iso by blast

lemma H_Inf_pres_fstar: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "Inf_pres f \<Longrightarrow> x \<le> f x \<Longrightarrow> x \<le> fstar f x"
  by (simp add: H_Inf_pres_fpower fstar_def le_INF_iff)

lemma fpower_Inf_pres: "Inf_pres f \<Longrightarrow> Inf_pres (fpower f i)"
  by (induct i, simp_all add: Inf_pres_comp)

lemma fstar_Inf_pres: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "Inf_pres f \<Longrightarrow> Inf_pres (fstar f)"
  by (simp add: fstar_def Inf_pres_Inf fpower_Inf_pres)

lemma fstar_unfoldl_var [simp]: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "Inf_pres f \<Longrightarrow> x \<sqinter> f (fstar f x) = fstar f x" 
proof-
  assume hyp: "Inf_pres f"
  have "x \<sqinter> f (fstar f x) = fpower f 0 x \<sqinter> (\<Sqinter>n. fpower f (Suc n) x)"
    by (simp add: fstar_def image_comp) (metis (no_types) comp_apply hyp image_image)
  also have "... = (\<Sqinter>n. fpower f n x)"
    by (subst fInf_unfold, auto)
  finally show ?thesis
    by (simp add: fstar_def image_comp)
qed

lemma fstar_fiter_id: "Inf_pres f \<Longrightarrow> fstar f = fiter_id f"
proof-
  assume hyp: "Inf_pres f"
  {fix x::"'a::complete_lattice"
  have "fstar f x = x \<sqinter> f (fstar f x)"
    by (simp add: hyp)
  hence a: "fstar f x \<le> gfp (\<lambda>y. x \<sqinter> f y)"
    by (metis gfp_upperbound order_refl)
  have "\<forall>y. y \<le> x \<sqinter> f y \<longrightarrow> y \<le> fstar f x"
    by (meson H_Inf_pres_fstar H_iso_cond2 Inf_pres_iso fstar_Inf_pres hyp le_infE)
  hence "fstar f x = gfp (\<lambda>y. x \<sqinter> f y)"
    by (metis a antisym gfp_least)}
  thus ?thesis 
    by (simp add: fun_eq_iff Inf_pres_iso fstar_pred_char hyp)
qed

lemma fstar_unfoldl [simp]: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "Inf_pres f \<Longrightarrow> id \<sqinter> (f \<circ> fstar f) = fstar f"  
  by (simp add: fun_eq_iff)

lemma fpower_Inf_comm: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "Inf_pres f \<Longrightarrow> f (\<Sqinter>i. fpower f i x) = (\<Sqinter>i. fpower f i (f x))"
proof-
  assume "Inf_pres f"
  hence "f (\<Sqinter>i. fpower f i x) = (\<Sqinter>i. fpower f (Suc i) x)"
    by (simp add: fun_eq_iff image_comp)
  also have "... =  (\<Sqinter>i. fpower f i (f x))"
    by (metis comp_eq_dest_lhs fun_mon.power_Suc2) 
  finally show ?thesis .
qed

lemma fstar_comm: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "Inf_pres f \<Longrightarrow> f \<circ> fstar f = fstar f \<circ> f"
  apply (simp add: fun_eq_iff fstar_def image_comp)
  by (metis (mono_tags, lifting) INF_cong comp_eq_dest fun_mon.power_commutes)

lemma fstar_unfoldr [simp]: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "Inf_pres f \<Longrightarrow> id \<sqinter> (fstar f \<circ> f) = fstar f"
  using fstar_comm fstar_unfoldl by fastforce


subsection \<open>Quantales of Inf- and Top-Preserving Transformers\<close>

text \<open>As for itotone transformers, types must now be restricted to a single one. It is well known that Inf-preserving transformers need not be
top-preserving, and that Sup-preserving transformers need not be bot-preserving. This has been shown elsewhere. This does not affect the following proof, 
but it has an impact on how elements are represented. I show only the result for Inf-preserving transformers; that for Sup-preserving ones is dual.\<close>

typedef (overloaded) 'a Inf_pres = "{f::'a::complete_lattice \<Rightarrow> 'a. Inf_pres f}"
  using Inf_pres_topf by blast

setup_lifting type_definition_Inf_pres

instantiation Inf_pres :: (complete_lattice) unital_Sup_quantale 
begin

lift_definition one_Inf_pres :: "'a::complete_lattice Inf_pres" is id
  by (simp add: iso_id)

lift_definition times_Inf_pres :: "'a::complete_lattice Inf_pres \<Rightarrow> 'a Inf_pres \<Rightarrow> 'a Inf_pres" is "(\<circ>)"
  by (simp add: Inf_pres_comp)

lift_definition Sup_Inf_pres :: "'a::complete_lattice Inf_pres set \<Rightarrow> 'a Inf_pres" is Inf
  by (simp add: Inf_pres_Inf)

lift_definition less_eq_Inf_pres :: "'a Inf_pres \<Rightarrow> 'a Inf_pres \<Rightarrow> bool" is "(\<ge>)".

lift_definition  less_Inf_pres :: "'a Inf_pres \<Rightarrow> 'a Inf_pres \<Rightarrow> bool" is "(>)".

instance
  by (intro_classes; transfer, simp_all add: o_assoc Inf_lower Inf_greatest fInf_distr_var fInf_distl_var)

end

text \<open>Three comments seem worth making. Firstly, the result bakes in duality by considering Infs in the function space as 
Sups in the quantale, hence as Infs in the dual quantale. Secondly, the use of Sup-quantales not only reduces the number of proof obligations.
It also copes with the fact that Sups and top are not represented faithfully by this construction. They are generally different from
those in the super-quantale of isotone transformers. But of course they can be defined from Infs as usual. Alternatively, I could have 
proved the results for Inf-quantales, which may have been more straightforward. But Sup-lattices are more conventional.
Thirdly, as in the case of isotone transformers, the proof depends on a restriction to one single type, whereas previous results have 
been obtained for poly-typed quantales or quantaloids.\<close>

end
