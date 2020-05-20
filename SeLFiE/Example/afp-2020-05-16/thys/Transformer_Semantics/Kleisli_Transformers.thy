(* 
  Title: State Transformers and Predicate Transformers Based on the Powerset Monad
  Author: Georg Struth 
  Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>State Transformers and Predicate Transformers Based on the Powerset Monad\<close>

theory Kleisli_Transformers

imports Powerset_Monad 
        Sup_Inf_Preserving_Transformers
begin          


subsection \<open>Backward Diamonds from Kleisli Arrows\<close>

text \<open>First I verify the embedding of the Kleisli category of the powerset functor into its Eilenberg-Moore category. 
This functor maps sets to their mus and functions to their Kleisli liftings. But this is just functoriality of dagger!. 
I model it as a backward diamond operator in the sense of dynamic logic. It corresponds to a strongest postcondition 
operator. In the parlance of program semantics, this is an embedding of state into prediate transformers.\<close>

notation klift ("bd\<^sub>\<F>")

text \<open>bd stands for backward diamond, the index indicates the setting of Kleisli arrows or nondeterministic 
functions. ifbd is its inverse.\<close>

abbreviation ifbd :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> 'b set" ("bd\<^sup>-\<^sub>\<F>") where 
  "bd\<^sup>-\<^sub>\<F> \<equiv> (\<lambda>\<phi>. \<phi> \<circ> \<eta>)"

lemma fbd_set: "bd\<^sub>\<F> f X = {y. \<exists>x. y \<in> f x \<and> x \<in> X}"
  by (force simp: klift_prop) 
 
lemma ifbd_set: "bd\<^sup>-\<^sub>\<F> \<phi> x = {y. y \<in> \<phi> {x}}"
  by simp

text \<open>The two functors form a bijective pair.\<close>

lemma fbd_ifbd_inv2: "Sup_pres \<phi> \<Longrightarrow> (bd\<^sub>\<F> \<circ> bd\<^sup>-\<^sub>\<F>) \<phi> = \<phi>" 
proof -
  assume h: "Sup_pres \<phi>"
  have "(bd\<^sub>\<F> \<circ> bd\<^sup>-\<^sub>\<F>) \<phi> = Sup \<circ> \<P> (\<phi> \<circ> \<eta>)"
    unfolding klift_def by simp
  also have "... = Sup \<circ> \<P> \<phi> \<circ> \<P> \<eta>"
    by (simp add: comp_assoc P_func1)
  also have "... = \<phi> \<circ> Sup \<circ> \<P> \<eta>"
    by (simp add: h)
  also have "... = \<phi> \<circ> id"
    by force
  finally show ?thesis
    by simp
qed

lemma fbd_ifbd_inv2_inv: "(bd\<^sub>\<F> \<circ> bd\<^sup>-\<^sub>\<F>) \<phi> = \<phi> \<Longrightarrow> Sup_pres \<phi>" 
  unfolding fun_eq_iff comp_def by (metis (no_types, lifting) Inf.INF_cong UN_extend_simps(8) klift_prop)

lemma fbd_ifbd_inv2_iff: "((bd\<^sub>\<F> \<circ> bd\<^sup>-\<^sub>\<F>) \<phi> = \<phi>) = (Sup_pres \<phi>)"
  using fbd_ifbd_inv2 fbd_ifbd_inv2_inv by force

lemma fbd_inj: "inj bd\<^sub>\<F>"
  by (meson inj_on_inverseI klift_eta_inv1)

lemma fbd_inj_iff: "(bd\<^sub>\<F> f = bd\<^sub>\<F> g) = (f = g)"
  by (meson injD fbd_inj)

lemma ifbd_inj: "Sup_pres \<phi> \<Longrightarrow> Sup_pres \<psi> \<Longrightarrow> bd\<^sup>-\<^sub>\<F> \<phi> = bd\<^sup>-\<^sub>\<F> \<psi> \<Longrightarrow> \<phi> = \<psi>"
proof-
  assume h1: "Sup_pres \<phi>"
  and h2: "Sup_pres \<psi>" 
  and "bd\<^sup>-\<^sub>\<F> \<phi> = bd\<^sup>-\<^sub>\<F> \<psi>"
  hence "(bd\<^sub>\<F> \<circ> bd\<^sup>-\<^sub>\<F>) \<phi> = (bd\<^sub>\<F> \<circ> bd\<^sup>-\<^sub>\<F>) \<psi>"
    by simp
  thus ?thesis
    by (metis h1 h2 fbd_ifbd_inv2)
qed

lemma ifbd_inj_iff: "Sup_pres \<phi> \<Longrightarrow> Sup_pres \<psi> \<Longrightarrow> (bd\<^sup>-\<^sub>\<F> \<phi> = bd\<^sup>-\<^sub>\<F> \<psi>) = (\<phi> = \<psi>)"
  using ifbd_inj by force

lemma fbd_ifbd_galois: "Sup_pres \<phi> \<Longrightarrow> (bd\<^sup>-\<^sub>\<F> \<phi> = f) = (bd\<^sub>\<F> f = \<phi>)"
  using fbd_ifbd_inv2 by force

lemma fbd_surj: "Sup_pres \<phi> \<Longrightarrow> (\<exists>f. bd\<^sub>\<F> f = \<phi>)"
  using fbd_ifbd_inv2 by auto 

lemma ifbd_surj: "surj bd\<^sup>-\<^sub>\<F>"
  unfolding surj_def by (metis klift_eta_inv1)

text \<open>In addition they preserve the Sup-quantale structure of the powerset algebra. This means that
morphisms preserve compositions, units and Sups, but not Infs, hence also bottom but not top.\<close>

lemma fbd_comp_pres: "bd\<^sub>\<F> (f \<circ>\<^sub>K g) = bd\<^sub>\<F> g \<circ> bd\<^sub>\<F> f"
  unfolding kcomp_klift klift_prop1 by simp

lemma fbd_Sup_pres: "Sup_pres bd\<^sub>\<F>"
  by (force simp: fun_eq_iff klift_def)

lemma fbd_sup_pres: "sup_pres bd\<^sub>\<F>"
  using Sup_sup_pres fbd_Sup_pres by blast

lemma fbd_Disj: "Sup_pres (bd\<^sub>\<F> f)"
  by (simp add: fbd_ifbd_inv2_inv)

lemma fbd_disj: "sup_pres (bd\<^sub>\<F> f)"
  by (simp add: klift_prop)

lemma fbd_bot_pres: "bot_pres bd\<^sub>\<F>"
  unfolding klift_def by fastforce

lemma fbd_zero_pres2 [simp]: "bd\<^sub>\<F> f {} = {}"
  by (simp add: klift_prop)

lemma fbd_iso: "X \<subseteq> Y \<longrightarrow> bd\<^sub>\<F> f X \<subseteq> bd\<^sub>\<F> f Y"
  by (metis fbd_disj le_iff_sup)

text \<open>The following counterexamples show that Infs are not preserved.\<close>

lemma "top_pres bd\<^sub>\<F>" (*nitpick*)
  oops

lemma "inf_pres bd\<^sub>\<F>" (*nitpick*)
  oops

text \<open>Dual preservation statements hold for ifbd ... and even Inf-preservation.\<close>

lemma ifbd_comp_pres: "Sup_pres \<phi> \<Longrightarrow> bd\<^sup>-\<^sub>\<F> (\<phi> \<circ> \<psi>) = bd\<^sup>-\<^sub>\<F> \<psi> \<circ>\<^sub>K bd\<^sup>-\<^sub>\<F> \<phi>"
  by (smt fbd_ifbd_galois fun.map_comp kcomp_def klift_def)

lemma ifbd_Sup_pres: "Sup_pres bd\<^sup>-\<^sub>\<F>"   
  by (simp add: fun_eq_iff)

lemma ifbd_sup_pres: "sup_pres bd\<^sup>-\<^sub>\<F>"
  by force

lemma ifbd_Inf_pres: "Inf_pres bd\<^sup>-\<^sub>\<F>"
  by (simp add: fun_eq_iff)

lemma ifbd_inf_pres: "inf_pres bd\<^sup>-\<^sub>\<F>"
  by force

lemma ifbd_bot_pres: "bot_pres bd\<^sup>-\<^sub>\<F>"
  by auto

lemma ifbd_top_pres: "top_pres bd\<^sup>-\<^sub>\<F>"
  by auto

text \<open>Preservation of units by the Kleisli lifting has been proved in klift-prop3.\<close>

text \<open>These results estabilish the isomorphism between state and predicate transformers given by backward diamonds.
The isomorphism preserves the Sup-quantale structure, but not Infs.\<close>
 


subsection \<open>Backward Diamonds from Relations\<close>

text \<open>Using the isomorphism between binary relations and Kleisli arrows (or state transformers), it is straightforward
to define backward diamonds from relations, by composing isomorphisms. It follows that Sup-quantales of binary relations 
(under relational composition, the identity relation and Sups) are isomorphic to the Sup-quantales of predicate transformers.
Once again, Infs are not preserved.\<close>

definition rbd :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set"  ("bd\<^sub>\<R>") where
  "bd\<^sub>\<R> = bd\<^sub>\<F> \<circ> \<F>"

definition irbd :: "('a set \<Rightarrow> 'b set) \<Rightarrow> ('a \<times> 'b) set"  ("bd\<^sup>-\<^sub>\<R>") where
  "bd\<^sup>-\<^sub>\<R> = \<R> \<circ> bd\<^sup>-\<^sub>\<F>"

lemma rbd_Im: "bd\<^sub>\<R> = (``)"
  unfolding rbd_def klift_def r2f_def fun_eq_iff by force

lemma rbd_set: "bd\<^sub>\<R> R X = {y. \<exists>x \<in> X. (x,y) \<in> R}"
  by (force simp: rbd_Im Image_def)
  
lemma irbd_set: "bd\<^sup>-\<^sub>\<R> \<phi> = {(x,y). y \<in> (\<phi> \<circ> \<eta>) x}"
  by (simp add: irbd_def f2r_def o_def)

lemma irbd_set_var: "bd\<^sup>-\<^sub>\<R> \<phi> = {(x,y). y \<in> \<phi> {x}}"
  by (simp add: irbd_def f2r_def o_def)

lemma rbd_irbd_inv1 [simp]: "bd\<^sup>-\<^sub>\<R> \<circ> bd\<^sub>\<R> = id"
  by (metis (no_types, lifting) comp_eq_dest_lhs eq_id_iff fbd_Disj fbd_ifbd_galois irbd_def r2f_f2r_galois rbd_def)

lemma irbd_rbd_inv2: "Sup_pres \<phi> \<Longrightarrow> (bd\<^sub>\<R> \<circ> bd\<^sup>-\<^sub>\<R>) \<phi> = \<phi>"
  by (metis comp_apply fbd_ifbd_galois irbd_def r2f_f2r_galois rbd_def)

lemma irbd_rbd_inv2_inv: "(bd\<^sub>\<R> \<circ> bd\<^sup>-\<^sub>\<R>) \<phi> = \<phi> \<Longrightarrow> Sup_pres \<phi>"
  by (simp add: rbd_def irbd_def, metis fbd_Disj)

lemma irbd_rbd_inv2_iff: "((bd\<^sub>\<R> \<circ> bd\<^sup>-\<^sub>\<R>) \<phi> = \<phi>) = (Sup_pres \<phi>)"
  using irbd_rbd_inv2 irbd_rbd_inv2_inv by blast

lemma rbd_inj: "inj bd\<^sub>\<R>"
  by (simp add: fbd_inj inj_compose r2f_inj rbd_def)

lemma rbd_translate: "(bd\<^sub>\<R> R = bd\<^sub>\<R> S) = (R = S)"
  by (simp add: rbd_inj inj_eq)

lemma irbd_inj: "Sup_pres \<phi> \<Longrightarrow> Sup_pres \<psi> \<Longrightarrow> bd\<^sup>-\<^sub>\<R> \<phi> = bd\<^sup>-\<^sub>\<R> \<psi> \<Longrightarrow> \<phi> = \<psi>"
  by (metis rbd_Im comp_eq_dest_lhs irbd_rbd_inv2)

lemma irbd_inj_iff: "Sup_pres \<phi> \<Longrightarrow> Sup_pres \<psi> \<Longrightarrow> (bd\<^sup>-\<^sub>\<R> \<phi> = bd\<^sup>-\<^sub>\<R> \<psi>) = (\<phi> = \<psi>)"
  using irbd_inj by force

lemma rbd_surj: "Sup_pres \<phi> \<Longrightarrow> (\<exists>R. bd\<^sub>\<R> R = \<phi>)"
  using irbd_rbd_inv2 by force

lemma irbd_surj: "surj bd\<^sup>-\<^sub>\<R>"
  by (metis UNIV_I fun.set_map imageE rbd_irbd_inv1 surj_def surj_id)

lemma rbd_irbd_galois: "Sup_pres \<phi> \<Longrightarrow> (\<phi> = bd\<^sub>\<R> R) = (R = bd\<^sup>-\<^sub>\<R> \<phi>)"
  by (smt comp_apply fbd_ifbd_galois irbd_def r2f_f2r_galois rbd_def)

lemma rbd_comp_pres: "bd\<^sub>\<R> (R ; S) = bd\<^sub>\<R> S \<circ> bd\<^sub>\<R> R"
  by (simp add: rbd_def r2f_comp_pres fbd_comp_pres)

lemma rbd_Id_pres: "bd\<^sub>\<R> Id = id"
  unfolding rbd_def by simp

lemma rbd_Un_pres: "Sup_pres bd\<^sub>\<R>"
  by (simp add: rbd_def Sup_pres_comp fbd_Sup_pres r2f_Sup_pres)

lemma rbd_un_pres: "sup_pres bd\<^sub>\<R>"
  by (simp add: rbd_def fbd_sup_pres r2f_sup_pres)

lemma "inf_pres bd\<^sub>\<R>" (*nitpick*)
  oops

lemma rbd_disj: "Sup_pres (bd\<^sub>\<R> R)"
  by (simp add: rbd_def fbd_Disj)

lemma rbd_disj2: "sup_pres (bd\<^sub>\<R> R)"
  by (simp add: Image_Un rbd_Im)

lemma rbd_bot_pres: "bot_pres bd\<^sub>\<R>"
  by (simp add: fbd_bot_pres r2f_bot_pres rbd_def)

lemma rbd_zero_pres2 [simp]: "bd\<^sub>\<R> R {} = {}"
  by (simp add: rbd_Im)

lemma rbd_univ: "bd\<^sub>\<R> R UNIV = Range R"
  unfolding rbd_def fun_eq_iff klift_def r2f_def by force

lemma rbd_iso: "X \<subseteq> Y \<Longrightarrow> bd\<^sub>\<R> R X \<subseteq> bd\<^sub>\<R> R Y"
  by (metis le_iff_sup rbd_disj2)

lemma irbd_comp_pres: "Sup_pres \<phi> \<Longrightarrow> bd\<^sup>-\<^sub>\<R> (\<phi> \<circ> \<psi>) = bd\<^sup>-\<^sub>\<R> \<psi> ; bd\<^sup>-\<^sub>\<R> \<phi>"
  by (simp add: ifbd_comp_pres f2r_kcomp_pres irbd_def)

lemma irbd_id_pres [simp]: "bd\<^sup>-\<^sub>\<R> id = Id"
  unfolding irbd_def by simp

lemma irbd_Sup_pres: "Sup_pres bd\<^sup>-\<^sub>\<R>"
  by (simp add: irbd_def Sup_pres_comp ifbd_Sup_pres f2r_Sup_pres)

lemma irbd_sup_pres: "sup_pres bd\<^sup>-\<^sub>\<R>"
  by (simp add: irbd_def ifbd_sup_pres f2r_sup_pres)  

lemma irbd_Inf_pres: "Inf_pres bd\<^sup>-\<^sub>\<R>"
  by (auto simp: fun_eq_iff irbd_def f2r_def)

lemma irbd_inf_pres: "inf_pres bd\<^sup>-\<^sub>\<R>"
  by (auto simp: fun_eq_iff irbd_def f2r_def)

lemma irbd_bot_pres: "bot_pres bd\<^sup>-\<^sub>\<R>"
  by (metis comp_def ifbd_bot_pres f2r_bot_pres irbd_def)

text \<open>This shows that relations are isomorphic to disjunctive forward predicate transformers. In many cases Isabelle picks up
the composition of morphisms in proofs.\<close>


subsection \<open>Forward Boxes on Kleisli Arrows\<close>

text \<open>Forward box operators correspond to weakest liberal preconditions in program semantics. Here, 
Kleisli arrows are mapped to the opposite of the Eilenberg-Moore category, that is, Inf-lattices. 
It follows that the Inf-quantale structure is preserved. Modelling opposition is based on the fact 
that Kleisli arrows can be swapped by going through relations.\<close>

definition ffb :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b set \<Rightarrow> 'a set" ("fb\<^sub>\<F>") where
  "fb\<^sub>\<F> = \<partial>\<^sub>F \<circ> bd\<^sub>\<F> \<circ> op\<^sub>K" 

text \<open>Here, $\partial_F$ is map-dual, which amounts to De Morgan duality. Hence the forward box operator is
obtained from the backward diamond by taking the opposite Kleisli arrow, applying the backward diamond, and then De Morgan
duality.\<close>

lemma ffb_prop: "fb\<^sub>\<F> f = \<partial> \<circ> bd\<^sub>\<F> (op\<^sub>K f) \<circ> \<partial>"
  by (simp add: ffb_def map_dual_def)

lemma ffb_prop_var: "fb\<^sub>\<F> f = uminus \<circ> bd\<^sub>\<F> (op\<^sub>K f) \<circ> uminus"
  by (simp add: dual_set_def ffb_prop)
 
lemma ffb_fbd_dual: "\<partial> \<circ> fb\<^sub>\<F> f = bd\<^sub>\<F> (op\<^sub>K f) \<circ> \<partial>"
  by (simp add: ffb_prop o_assoc)

text \<open>I give a set-theoretic definition of iffb, because the algebraic one below depends on Inf-preservation.\<close>

definition iffb :: "('b set \<Rightarrow> 'a set) \<Rightarrow> 'a \<Rightarrow> 'b set" ("fb\<^sup>-\<^sub>\<F>") where
  "fb\<^sup>-\<^sub>\<F> \<phi> = (\<lambda>x. \<Inter>{X. x \<in> \<phi> X})"

lemma ffb_set: "fb\<^sub>\<F> f = (\<lambda>Y. {x. f x \<subseteq> Y})" 
  by (force simp: fun_eq_iff ffb_prop_var kop_def klift_def f2r_def r2f_def)

text \<open>Forward boxes and backward diamonds are adjoints.\<close>

lemma ffb_fbd_galois: "(bd\<^sub>\<F> f) \<stileturn> (fb\<^sub>\<F> f)"
  unfolding adj_def ffb_set klift_prop by blast

lemma iffb_inv1: "fb\<^sup>-\<^sub>\<F> \<circ> fb\<^sub>\<F> = id"
  unfolding fun_eq_iff ffb_set iffb_def by force

lemma iffb_inv2_aux: "Inf_pres \<phi> \<Longrightarrow> \<Sqinter>{X. x \<in> \<phi> X} \<subseteq> Y \<Longrightarrow> x \<in> \<phi> Y"
proof-
  assume "Inf_pres \<phi>"
    and h1: "\<Sqinter>{X. x \<in> \<phi> X} \<subseteq> Y"
  hence h2: "\<forall>X. \<phi> (\<Sqinter>X) = (\<Inter>x \<in> X. \<phi> x)"
    by (metis comp_eq_dest)
  hence "\<phi> (\<Sqinter>{X. x \<in> \<phi> X}) \<subseteq> \<phi> Y"
    by (metis h1 INF_lower2 cInf_eq_minimum mem_Collect_eq order_refl)
  hence "(\<Sqinter>{\<phi> X |X. x \<in> \<phi> X}) \<subseteq> \<phi> Y" 
    by (metis h2 setcompr_eq_image)
  thus ?thesis
    by (force simp add: subset_iff)
qed

lemma iffb_inv2: "Inf_pres \<phi> \<Longrightarrow> (fb\<^sub>\<F> \<circ> fb\<^sup>-\<^sub>\<F>) \<phi> = \<phi>"
proof-
  assume h: "Inf_pres \<phi>"
  {fix Y
  have "(fb\<^sub>\<F> \<circ> fb\<^sup>-\<^sub>\<F>) \<phi> Y = {x. \<Sqinter>{X. x \<in> \<phi> X} \<subseteq> Y}"
    by (simp add: ffb_set iffb_def)
  hence "\<And>x. x \<in> (fb\<^sub>\<F> \<circ> fb\<^sup>-\<^sub>\<F>) \<phi> Y \<longleftrightarrow> \<Sqinter>{X. x \<in> \<phi> X} \<subseteq> Y"
    by auto
  hence "\<And>x. x \<in> (fb\<^sub>\<F> \<circ> fb\<^sup>-\<^sub>\<F>) \<phi> Y \<longleftrightarrow> x \<in> \<phi> Y" 
    by (auto simp: h iffb_inv2_aux)
  hence  "(fb\<^sub>\<F> \<circ> fb\<^sup>-\<^sub>\<F>) \<phi> Y = \<phi> Y"
    by (simp add: fun_eq_iff set_eq_iff)}
  thus ?thesis
    unfolding fun_eq_iff by simp
qed

lemma iffb_inv2_inv: "(fb\<^sub>\<F> \<circ> fb\<^sup>-\<^sub>\<F>) \<phi> = \<phi> \<Longrightarrow> Inf_pres \<phi>"
  by (auto simp: fun_eq_iff ffb_set iffb_def)

lemma iffb_inv2_iff: "((fb\<^sub>\<F> \<circ> fb\<^sup>-\<^sub>\<F>) \<phi> = \<phi>) = (Inf_pres \<phi>)"
  using iffb_inv2 iffb_inv2_inv by blast

lemma ffb_inj: "inj fb\<^sub>\<F>"
  unfolding inj_def by (metis iffb_inv1 pointfree_idE)

lemma ffb_inj_iff: "(fb\<^sub>\<F> f = fb\<^sub>\<F> g) = (f = g)"
  by (simp add: ffb_inj inj_eq)

lemma ffb_iffb_galois: "Inf_pres \<phi> \<Longrightarrow> (fb\<^sup>-\<^sub>\<F> \<phi> = f) = (fb\<^sub>\<F> f = \<phi>)"
  using ffb_inj_iff iffb_inv2 by force

lemma iffb_inj: "Inf_pres \<phi> \<Longrightarrow> Inf_pres \<psi> \<Longrightarrow> fb\<^sup>-\<^sub>\<F> \<phi> = fb\<^sup>-\<^sub>\<F> \<psi>  \<Longrightarrow> \<phi> = \<psi>"
  by (metis ffb_iffb_galois)

lemma iffb_inj_iff: "Inf_pres \<phi> \<Longrightarrow> Inf_pres \<psi> \<Longrightarrow> (fb\<^sup>-\<^sub>\<F> \<phi> = fb\<^sup>-\<^sub>\<F> \<psi>) = (\<phi> = \<psi>)"
  using iffb_inj by blast

lemma ffb_surj: "Inf_pres \<phi>  \<Longrightarrow> (\<exists>f. fb\<^sub>\<F> f = \<phi>)"
  using iffb_inv2 by auto

lemma iffb_surj: "surj fb\<^sup>-\<^sub>\<F>" 
  using surj_def by (metis comp_apply iffb_inv1 surj_id) 

text \<open>This is now the explicit "definition" of iffb, for Inf-preserving transformers.\<close>

lemma iffb_ifbd_dual: "Inf_pres \<phi> \<Longrightarrow> fb\<^sup>-\<^sub>\<F> \<phi> = (op\<^sub>K \<circ> bd\<^sup>-\<^sub>\<F> \<circ> \<partial>\<^sub>F) \<phi>" 
proof-
  assume h: "Inf_pres \<phi>"
  {fix f
    have "(fb\<^sup>-\<^sub>\<F> \<phi> = f) = ((\<partial>\<^sub>F \<circ> bd\<^sub>\<F> \<circ> op\<^sub>K) f = \<phi>)"
      by (simp add: ffb_def ffb_iffb_galois h)
    also have "... = (op\<^sub>K f = (bd\<^sup>-\<^sub>\<F> \<circ> \<partial>\<^sub>F) \<phi>)"
      by (metis (mono_tags, lifting) comp_apply map_dual_dual ffb_def ffb_surj h klift_eta_inv1 map_dual_dual)
    finally have "(fb\<^sup>-\<^sub>\<F> \<phi> = f) = (f = (op\<^sub>K \<circ> bd\<^sup>-\<^sub>\<F> \<circ> \<partial>\<^sub>F) \<phi>)"
      using kop_galois by auto}
  thus ?thesis
    by blast
qed

lemma fbd_ffb_dual: "\<partial>\<^sub>F \<circ> fb\<^sub>\<F> \<circ> op\<^sub>K = bd\<^sub>\<F>"
proof-
  have "\<partial>\<^sub>F \<circ> fb\<^sub>\<F> \<circ> op\<^sub>K = \<partial>\<^sub>F \<circ> \<partial>\<^sub>F \<circ> bd\<^sub>\<F> \<circ> (op\<^sub>K \<circ> op\<^sub>K)"
    by (simp add: comp_def ffb_def)
  thus ?thesis
    by simp
qed

lemma ffbd_ffb_dual_var: "\<partial> \<circ> bd\<^sub>\<F> f = fb\<^sub>\<F> (op\<^sub>K f) \<circ> \<partial>"
  by (metis ffb_prop fun_dual1 kop_galois)

lemma ifbd_iffb_dual: "Sup_pres \<phi> \<Longrightarrow> bd\<^sup>-\<^sub>\<F> \<phi> = (op\<^sub>K \<circ> fb\<^sup>-\<^sub>\<F> \<circ> \<partial>\<^sub>F) \<phi>" 
proof-
  assume h: "Sup_pres \<phi>"
  hence "Inf_pres (\<partial>\<^sub>F \<phi>)"
    using Sup_pres_Inf_pres by blast
  hence "(op\<^sub>K \<circ> fb\<^sup>-\<^sub>\<F> \<circ> \<partial>\<^sub>F) \<phi> = (op\<^sub>K \<circ> (op\<^sub>K \<circ> bd\<^sup>-\<^sub>\<F> \<circ> \<partial>\<^sub>F) \<circ> \<partial>\<^sub>F) \<phi>"
    by (simp add: iffb_ifbd_dual)
  thus ?thesis
    by (metis comp_def kop_galois map_dual_dual)
qed

lemma ffb_kcomp_pres: "fb\<^sub>\<F> (f \<circ>\<^sub>K g) = fb\<^sub>\<F> f \<circ> fb\<^sub>\<F> g"
proof-
  have "fb\<^sub>\<F> (f \<circ>\<^sub>K g) = \<partial>\<^sub>F (bd\<^sub>\<F> (op\<^sub>K (f \<circ>\<^sub>K g)))"
    by (simp add: ffb_def)
  also have "... = \<partial>\<^sub>F (bd\<^sub>\<F> (op\<^sub>K g \<circ>\<^sub>K op\<^sub>K f))"
    by (simp add: kop_contrav)
  also have "... = \<partial>\<^sub>F (bd\<^sub>\<F> (op\<^sub>K f) \<circ> bd\<^sub>\<F> (op\<^sub>K g))"
    by (simp add: fbd_comp_pres)
  also have "... = \<partial>\<^sub>F (bd\<^sub>\<F> (op\<^sub>K f)) \<circ> \<partial>\<^sub>F (bd\<^sub>\<F> (op\<^sub>K g))"
    by (simp add: map_dual_func1)
  finally show ?thesis
    by (simp add: ffb_def)
qed

lemma ffb_eta_pres: "fb\<^sub>\<F> \<eta> = id"
  unfolding ffb_def by simp

lemma ffb_Sup_dual: "Sup_dual fb\<^sub>\<F>"
  unfolding ffb_prop_var comp_def fun_eq_iff klift_prop kop_def f2r_def r2f_def converse_def by fastforce

lemma ffb_Sup_dual_var: "fb\<^sub>\<F> (\<Squnion>F) = (\<Sqinter>f \<in> F. fb\<^sub>\<F> f)"
  unfolding ffb_prop_var comp_def fun_eq_iff klift_prop kop_def f2r_def r2f_def converse_def by fastforce

lemma ffb_sup_dual: "sup_dual fb\<^sub>\<F>"
  using ffb_Sup_dual Sup_sup_dual by force

lemma ffb_zero_dual: "fb\<^sub>\<F> \<zeta> = (\<lambda>X. UNIV)" 
  unfolding ffb_prop_var kop_def klift_prop fun_eq_iff f2r_def r2f_def by simp

lemma "inf_dual ffb" (*nitpick*)
  oops

text \<open>Once again, only the Sup-quantale structure is preserved.\<close>

lemma iffb_comp_pres:
  assumes "Inf_pres \<phi>"
  assumes "Inf_pres \<psi>"
  shows "fb\<^sup>-\<^sub>\<F> (\<phi> \<circ> \<psi>) = fb\<^sup>-\<^sub>\<F> \<phi> \<circ>\<^sub>K fb\<^sup>-\<^sub>\<F> \<psi>"
    by (metis assms Inf_pres_comp ffb_iffb_galois ffb_kcomp_pres)

lemma iffb_id_pres: "fb\<^sup>-\<^sub>\<F> id = \<eta>"
  unfolding iffb_def by force

lemma iffb_Inf_dual: 
  assumes "\<forall>\<phi> \<in> \<Phi>. Inf_pres \<phi>"
  shows "(fb\<^sup>-\<^sub>\<F> \<circ> Inf) \<Phi> = (Sup \<circ> \<P> fb\<^sup>-\<^sub>\<F>) \<Phi>" 
proof-
  have "Inf_pres (\<Sqinter>\<Phi>)"
    using Inf_pres_Inf assms by blast
  hence "(fb\<^sub>\<F> \<circ> fb\<^sup>-\<^sub>\<F>) (\<Sqinter>\<Phi>) = \<Sqinter>(\<P> (fb\<^sub>\<F> \<circ> fb\<^sup>-\<^sub>\<F>) \<Phi>)"
    by (metis (mono_tags, lifting) INF_cong INF_identity_eq assms iffb_inv2)
  hence "(fb\<^sub>\<F> \<circ> fb\<^sup>-\<^sub>\<F>) (\<Sqinter>\<Phi>) = fb\<^sub>\<F> (\<Squnion>(\<P> fb\<^sup>-\<^sub>\<F> \<Phi>))"
    by (simp add: Setcompr_eq_image ffb_Sup_dual_var image_comp)
  thus ?thesis
    by (simp add: ffb_inj_iff)
qed  

lemma iffb_Sup_dual: "Sup_dual fb\<^sup>-\<^sub>\<F>"
  by (auto simp: iffb_def fun_eq_iff)
 
lemma iffb_inf_dual: 
  assumes "Inf_pres \<phi>" 
  and "Inf_pres \<psi>"
shows "fb\<^sup>-\<^sub>\<F> (\<phi> \<sqinter> \<psi>) = fb\<^sup>-\<^sub>\<F> \<phi> \<squnion> fb\<^sup>-\<^sub>\<F> \<psi>"
proof -
  have f1: "\<phi> \<sqinter> \<psi> = fb\<^sub>\<F> (fb\<^sup>-\<^sub>\<F> \<phi>) \<sqinter> fb\<^sub>\<F> (fb\<^sup>-\<^sub>\<F> \<psi>)"
    using assms iffb_inv2 by fastforce
  have "\<phi> \<sqinter> \<psi> \<circ> Inter = Inter \<circ> \<P> (\<phi> \<sqinter> \<psi>)"
    using assms Inf_pres_inf by blast
  thus ?thesis
    by (simp add: f1 ffb_iffb_galois ffb_sup_dual)
qed 

lemma  iffb_sup_dual: "fb\<^sup>-\<^sub>\<F> (\<phi> \<squnion> \<psi>) = fb\<^sup>-\<^sub>\<F> \<phi> \<sqinter> fb\<^sup>-\<^sub>\<F> \<psi>"
  unfolding iffb_def by fastforce

lemma iffb_top_pres [simp]: "fb\<^sup>-\<^sub>\<F> \<top> = \<zeta>"
  unfolding iffb_def by simp

text \<open>This establishes the duality between state transformers and weakest liberal preconditions.\<close>


subsection \<open>Forward Box Operators from Relations\<close>

text \<open>Once again one can compose isomorphisms, linking weakest liberal preconditions with relational semantics.
The isomorphism obtained should by now be obvious.\<close>

definition rfb :: "('a \<times> 'b) set \<Rightarrow> 'b set \<Rightarrow> 'a set"  ("fb\<^sub>\<R>") where
  "fb\<^sub>\<R> = fb\<^sub>\<F> \<circ> \<F>"

definition irfb :: "('b set \<Rightarrow> 'a set) \<Rightarrow> ('a \<times> 'b) set" ("fb\<^sup>-\<^sub>\<R>") where
  "fb\<^sup>-\<^sub>\<R> = \<R> \<circ> fb\<^sup>-\<^sub>\<F>"

lemma rfb_rbd_dual: "fb\<^sub>\<R> R = \<partial>\<^sub>F (bd\<^sub>\<R> (R\<inverse>))" 
  by (simp add: rfb_def rbd_def kop_def ffb_def, metis r2f_f2r_galois)

lemma rbd_rfb_dual: "bd\<^sub>\<R> R = \<partial>\<^sub>F (fb\<^sub>\<R> (R\<inverse>))"
  by (simp add: rfb_def rbd_def kop_def ffb_def, metis converse_converse map_dual_dual r2f_f2r_galois)
  
lemma irfb_irbd_dual: "Inf_pres \<phi> \<Longrightarrow> fb\<^sup>-\<^sub>\<R> \<phi> = ((\<smile>) \<circ> bd\<^sup>-\<^sub>\<R>  \<circ> \<partial>\<^sub>F) \<phi>"
  by (simp add: irfb_def irbd_def iffb_ifbd_dual kop_def r2f_f2r_galois)

lemma irbd_irfb_dual: "Sup_pres \<phi> \<Longrightarrow> bd\<^sup>-\<^sub>\<R> \<phi> = ((\<smile>) \<circ> fb\<^sup>-\<^sub>\<R> \<circ> \<partial>\<^sub>F) \<phi>"
  by (simp add: irfb_def irbd_def ifbd_iffb_dual kop_def r2f_f2r_galois)

lemma rfb_set: "fb\<^sub>\<R> R Y = {x. \<forall>y. (x,y) \<in> R \<longrightarrow> y \<in> Y}"
  unfolding rfb_def ffb_prop_var comp_def klift_def f2r_def r2f_def kop_def by force

lemma rfb_rbd_galois: "(bd\<^sub>\<R> R) \<stileturn> (fb\<^sub>\<R> R)"
  by (simp add: ffb_fbd_galois rbd_def rfb_def)

lemma irfb_set: "fb\<^sup>-\<^sub>\<R> \<phi> = {(x, y). \<forall>Y. x \<in> \<phi> Y \<longrightarrow> y \<in> Y}"
  by (simp add: irfb_def iffb_def f2r_def)

lemma irfb_inv1 [simp]: "fb\<^sup>-\<^sub>\<R> \<circ> fb\<^sub>\<R> = id"
  by (simp add: fun_eq_iff rfb_def irfb_def iffb_inv1 pointfree_idE)

lemma irfb_inv2: "Inf_pres \<phi> \<Longrightarrow> (fb\<^sub>\<R> \<circ> fb\<^sup>-\<^sub>\<R>) \<phi> = \<phi>"
  by (simp add: rfb_def irfb_def, metis ffb_iffb_galois r2f_f2r_galois)

lemma rfb_inj: "inj fb\<^sub>\<R>"
  by (simp add: rfb_def ffb_inj inj_compose r2f_inj)

lemma rfb_inj_iff: "(fb\<^sub>\<R> R = fb\<^sub>\<R> S) = (R = S)"
  by (simp add: rfb_inj inj_eq)

lemma irfb_inj: "Inf_pres \<phi> \<Longrightarrow> Inf_pres \<psi> \<Longrightarrow> fb\<^sup>-\<^sub>\<R> \<phi> = fb\<^sup>-\<^sub>\<R> \<psi> \<Longrightarrow> \<phi> = \<psi>"
  unfolding irfb_def using iffb_inj r2f_inj_iff by fastforce

lemma irfb_inf_iff: "Inf_pres \<phi> \<Longrightarrow> Inf_pres \<psi> \<Longrightarrow> (fb\<^sup>-\<^sub>\<R> \<phi> = fb\<^sup>-\<^sub>\<R> \<psi>) = (\<phi> = \<psi>)"
  using irfb_inj by auto

lemma rfb_surj: "Inf_pres \<phi> \<Longrightarrow> (\<exists>R. fb\<^sub>\<R> R = \<phi>)"
  using irfb_inv2 by fastforce

lemma irfb_surj: "surj fb\<^sup>-\<^sub>\<R>" 
  by (simp add: irfb_def comp_surj f2r_surj iffb_surj cong del: image_cong_simp)

lemma rfb_irfb_galois: "Inf_pres \<phi> \<Longrightarrow> (fb\<^sup>-\<^sub>\<R> \<phi> = R) = (fb\<^sub>\<R> R = \<phi>)"
  by (simp add: irfb_def rfb_def, metis ffb_iffb_galois r2f_f2r_galois)

lemma rfb_comp_pres: "fb\<^sub>\<R> (R ; S) = fb\<^sub>\<R> R \<circ> fb\<^sub>\<R> S"
  by (simp add: ffb_kcomp_pres r2f_comp_pres rfb_def)

lemma rfb_Id_pres [simp]: "fb\<^sub>\<R> Id = id"
  unfolding rfb_def ffb_prop by force

lemma rfb_Sup_dual: "Sup_dual fb\<^sub>\<R>"
proof- 
  have "fb\<^sub>\<R> \<circ> \<mu> = fb\<^sub>\<F> \<circ> \<F> \<circ> Sup"
    by (simp add: rfb_def)
  also have "... = fb\<^sub>\<F> \<circ> Sup \<circ> \<P> \<F>"
    by (metis fun.map_comp r2f_Sup_pres)
  also have "... = Inf \<circ> \<P> fb\<^sub>\<F> \<circ> \<P> \<F>"
    by (simp add: ffb_Sup_dual)
  also have "... = Inf \<circ> \<P> (fb\<^sub>\<F> \<circ> \<F>)"
    by (simp add: P_func1 comp_assoc)
  finally show ?thesis
    by (simp add: rfb_def)
qed

lemma rfb_Sup_dual_var: "fb\<^sub>\<R> (\<Squnion>\<phi>) = \<Sqinter>(\<P> fb\<^sub>\<R>) \<phi>"
  by (meson comp_eq_dest rfb_Sup_dual)

lemma rfb_sup_dual: "sup_dual fb\<^sub>\<R>"
  by (simp add: rfb_def ffb_sup_dual r2f_sup_pres)

lemma "inf_dual fb\<^sub>\<R>" (*nitpick*)
  oops

lemma rfb_Inf_pres: "Inf_pres (fb\<^sub>\<R> R)"
  unfolding rfb_def ffb_prop_var comp_def fun_eq_iff klift_def kop_def f2r_def r2f_def converse_def by auto

lemma rfb_inf_pres: "inf_pres (fb\<^sub>\<R> R)"
  unfolding rfb_def ffb_prop_var comp_def fun_eq_iff klift_def kop_def f2r_def r2f_def converse_def by auto

lemma rfb_zero_pres [simp]: "fb\<^sub>\<R> {} X = UNIV"
 unfolding rfb_def ffb_prop_var comp_def fun_eq_iff klift_def kop_def f2r_def r2f_def converse_def by auto

lemma rfb_zero_pres2 [simp]: "fb\<^sub>\<R> R {} = - Domain R"
 unfolding rfb_def ffb_prop_var comp_def fun_eq_iff klift_def kop_def f2r_def r2f_def converse_def by auto

lemma rfb_univ [simp]: "fb\<^sub>\<R> R UNIV = UNIV"
  unfolding rfb_def ffb_prop_var comp_def fun_eq_iff klift_def kop_def f2r_def r2f_def converse_def by auto

lemma rfb_iso: "X \<subseteq> Y \<Longrightarrow> fb\<^sub>\<R> R X \<subseteq> fb\<^sub>\<R> R Y"
  unfolding rfb_def ffb_prop_var comp_def fun_eq_iff klift_def kop_def f2r_def r2f_def converse_def by auto

lemma irfb_comp_pres: 
  assumes "Inf_pres \<phi>"
  assumes "Inf_pres \<psi>"
  shows "fb\<^sup>-\<^sub>\<R> (\<phi> \<circ> \<psi>) = fb\<^sup>-\<^sub>\<R> \<phi> ; fb\<^sup>-\<^sub>\<R> \<psi>"
  by (metis assms rfb_Inf_pres rfb_comp_pres rfb_irfb_galois)

lemma irfb_id_pres [simp]: "fb\<^sup>-\<^sub>\<R> id = Id"
  by (simp add: rfb_irfb_galois)

lemma irfb_Sup_dual: "Sup_dual fb\<^sup>-\<^sub>\<R>"
  by (auto simp: fun_eq_iff irfb_def iffb_def f2r_def)

lemma irfb_Inf_dual: 
  assumes "\<forall>\<phi> \<in> \<Phi>. Inf_pres \<phi>"
  shows "(fb\<^sup>-\<^sub>\<R> \<circ> Inf) \<Phi> = (Sup \<circ> \<P> fb\<^sup>-\<^sub>\<R>) \<Phi>" 
proof-
  have "Inf_pres (\<Sqinter>\<Phi>)"
    using Inf_pres_Inf assms by blast
  hence  "(fb\<^sub>\<R> \<circ> fb\<^sup>-\<^sub>\<R>) (\<Sqinter>\<Phi>) = \<Sqinter>(\<P> (fb\<^sub>\<R> \<circ> fb\<^sup>-\<^sub>\<R>) \<Phi>)"
    by (smt INF_identity_eq Sup.SUP_cong assms irfb_inv2)
  also have "... = \<Sqinter>(\<P> fb\<^sub>\<R> (\<P> fb\<^sup>-\<^sub>\<R> \<Phi>))"
    by (simp add: image_comp)
  also have "... = fb\<^sub>\<R> (\<Squnion>(\<P> fb\<^sup>-\<^sub>\<R> \<Phi>))"
    by (simp add: rfb_Sup_dual_var)
  finally have "(fb\<^sub>\<R> \<circ> fb\<^sup>-\<^sub>\<R>) (\<Sqinter>\<Phi>) = fb\<^sub>\<R> (\<Squnion>(\<P> fb\<^sup>-\<^sub>\<R> \<Phi>))".
  thus ?thesis
    by (simp add: rfb_inj_iff)
qed  

lemma irfb_sup_dual: "sup_dual fb\<^sup>-\<^sub>\<R>"
  by (force simp: fun_eq_iff irfb_def iffb_def f2r_def)

lemma irfb_inf_dual: 
  assumes "Inf_pres \<phi>" 
  and "Inf_pres \<psi>"
  shows "fb\<^sup>-\<^sub>\<R> (\<phi> \<sqinter> \<psi>) = fb\<^sup>-\<^sub>\<R> \<phi> \<squnion> fb\<^sup>-\<^sub>\<R> \<psi>"
  by (metis assms rfb_Inf_pres rfb_irfb_galois rfb_sup_dual)

lemma irfb_top_pres [simp]: "bd\<^sup>-\<^sub>\<R> \<top> = UNIV"
  unfolding irbd_def f2r_def by auto

text \<open>Finally, the adjunctions between the predicate transformers considered so far are revisited.\<close>

lemma ffb_fbd_galois_var: "(bd\<^sub>\<F> f X \<subseteq> Y) = (X \<subseteq> fb\<^sub>\<F> f Y)"
  by (meson adj_def ffb_fbd_galois)

lemma rfb_rbd_galois_var: "(bd\<^sub>\<R> R X \<subseteq> Y) = (X \<subseteq> fb\<^sub>\<R> R Y)"
  by (meson adj_def rfb_rbd_galois)

lemma ffb_fbd: "fb\<^sub>\<F> f Y = \<Union>{X. bd\<^sub>\<F> f X \<subseteq> Y}"
  using ffb_fbd_galois_var by fastforce

lemma rfb_rbd: "fb\<^sub>\<R> R Y = \<Union>{X. bd\<^sub>\<R> R X \<subseteq> Y}"
  using rfb_rbd_galois_var by fastforce 

lemma fbd_ffb: "bd\<^sub>\<F> f X = \<Inter>{Y. X \<subseteq> fb\<^sub>\<F> f Y}"
  using ffb_fbd_galois_var by fastforce 

lemma rbd_rfb: "bd\<^sub>\<R> R X = \<Inter>{Y. X \<subseteq> fb\<^sub>\<R> R Y}"
  using rfb_rbd_galois_var by fastforce 


subsection \<open>The Remaining Modalities\<close>

text \<open>Finally I set up the remaining dual transformers: forward diamonds and backward boxes. 
Most properties are not repeated, only some symmetries and dualities are spelled out.\<close>

text \<open>First, forward diamond operators are introduced, from state transformers and relations; together
with their inverses.\<close>

definition ffd :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b set \<Rightarrow> 'a set" ("fd\<^sub>\<F>") where 
  "fd\<^sub>\<F> = bd\<^sub>\<F> \<circ> op\<^sub>K"

definition iffd :: "('b set \<Rightarrow> 'a set) \<Rightarrow> 'a \<Rightarrow> 'b set" ("fd\<^sup>-\<^sub>\<F>") where 
  "fd\<^sup>-\<^sub>\<F> = op\<^sub>K \<circ> bd\<^sup>-\<^sub>\<F>"

definition rfd :: "('a \<times> 'b) set \<Rightarrow> 'b set \<Rightarrow> 'a set" ("fd\<^sub>\<R>") where 
  "fd\<^sub>\<R> = fd\<^sub>\<F> \<circ> \<F>"

definition irfd :: "('b set \<Rightarrow> 'a set) \<Rightarrow> ('a \<times> 'b) set" ("fd\<^sup>-\<^sub>\<R>") where 
  "fd\<^sup>-\<^sub>\<R> = \<R> \<circ> fd\<^sup>-\<^sub>\<F>"

text \<open>Second, I introduce forward boxes and their inverses.\<close>

definition fbb :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> 'b set" ("bb\<^sub>\<F>") where 
  "bb\<^sub>\<F> = fb\<^sub>\<F> \<circ> op\<^sub>K"

definition ifbb :: "('a  set \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> 'b set" ("bb\<^sup>-\<^sub>\<F>") where 
 "bb\<^sup>-\<^sub>\<F> = op\<^sub>K \<circ> fb\<^sup>-\<^sub>\<F>"

definition rbb :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set" ("bb\<^sub>\<R>") where 
  "bb\<^sub>\<R> = bb\<^sub>\<F> \<circ> \<F>"

definition irbb :: "('a  set \<Rightarrow> 'b set) \<Rightarrow> ('a \<times> 'b) set" ("bb\<^sup>-\<^sub>\<R>") where 
  "bb\<^sup>-\<^sub>\<R> = \<R> \<circ> bb\<^sup>-\<^sub>\<F>"

text \<open>Forward and backward operators of the same type (box or diamond) are related by opposition.\<close>

lemma rfd_rbd: "fd\<^sub>\<R> = bd\<^sub>\<R> \<circ> (\<smile>)"
  by (simp add: rfd_def rbd_def ffd_def kop_def comp_assoc)

lemma irfd_irbd: "fd\<^sup>-\<^sub>\<R> = (\<smile>) \<circ> bd\<^sup>-\<^sub>\<R>"
  by (simp add: irfd_def iffd_def kop_def irbd_def comp_assoc[symmetric])

lemma fbd_ffd: "bd\<^sub>\<F> = fd\<^sub>\<F> \<circ> op\<^sub>K"
  by (simp add: ffd_def kop_def converse_def f2r_def r2f_def klift_def fun_eq_iff)

lemma rbb_rfb: "bb\<^sub>\<R> = fb\<^sub>\<R> \<circ> (\<smile>)"
  by (simp add: rfb_def rbb_def, metis fbb_def kop_def r2f_f2r_galois_var2 rewriteR_comp_comp2)

lemma irbb_irfb: "bb\<^sup>-\<^sub>\<R> = (\<smile>) \<circ> fb\<^sup>-\<^sub>\<R>"
proof-
  have "bb\<^sup>-\<^sub>\<R> = \<R> \<circ> op\<^sub>K \<circ> fb\<^sup>-\<^sub>\<F>"
    by (simp add: irbb_def ifbb_def o_assoc)
  also have "... = \<R> \<circ> \<F> \<circ> (\<smile>) \<circ> \<R> \<circ> fb\<^sup>-\<^sub>\<F>"
    by (simp add: kop_def o_assoc)
  also have "... = (\<smile>) \<circ> fb\<^sup>-\<^sub>\<R>"
    by (simp add: comp_assoc irfb_def)
  finally show ?thesis.
qed

text \<open>Complementation is a natural isomorphism between forwards and backward operators of different type.\<close>

lemma ffd_ffb_demorgan: "\<partial> \<circ> fd\<^sub>\<F> f = fb\<^sub>\<F> f \<circ> \<partial>"
  by (simp add: comp_assoc ffb_prop ffd_def)

lemma iffd_iffb_demorgan: "Sup_pres \<phi> \<Longrightarrow> fd\<^sup>-\<^sub>\<F> \<phi> = (fb\<^sup>-\<^sub>\<F> \<circ> \<partial>\<^sub>F) \<phi>"
  by (smt Sup_pres_Inf_pres comp_apply iffb_ifbd_dual iffd_def map_dual_dual)

lemma ffb_ffd_demorgan: "\<partial> \<circ> fb\<^sub>\<F> f = fd\<^sub>\<F> f \<circ> \<partial>"
  by (simp add: ffb_prop ffd_def rewriteL_comp_comp)

lemma iffb_iffd_demorgan: "Inf_pres \<phi> \<Longrightarrow> fb\<^sup>-\<^sub>\<F> \<phi> = (fd\<^sup>-\<^sub>\<F> \<circ> \<partial>\<^sub>F) \<phi>"
  by (simp add: iffb_ifbd_dual iffd_def)

lemma rfd_rfb_demorgan: "\<partial> \<circ> fd\<^sub>\<R> R = fb\<^sub>\<R> R \<circ> \<partial>"
  by (simp add: rfb_def rfd_def ffd_ffb_demorgan)

lemma irfd_irfb_demorgan: "Sup_pres \<phi> \<Longrightarrow> fd\<^sup>-\<^sub>\<R> \<phi> = (fb\<^sup>-\<^sub>\<R> \<circ> \<partial>\<^sub>F) \<phi>"
  by (simp add: irfb_def irfd_def iffd_iffb_demorgan)

lemma rfb_rfd_demorgan: "\<partial> \<circ> fb\<^sub>\<R> R = fd\<^sub>\<R> R \<circ> \<partial>"
  by (simp add: ffb_ffd_demorgan rfb_def rfd_def)

lemma irfb_irfd_demorgan: "Inf_pres \<phi> \<Longrightarrow> fb\<^sup>-\<^sub>\<R> \<phi>  = (fd\<^sup>-\<^sub>\<R> \<circ> \<partial>\<^sub>F) \<phi>"
  by (simp add: irfb_irbd_dual irfd_irbd)

lemma fbd_fbb_demorgan: "\<partial> \<circ> bd\<^sub>\<F> f = bb\<^sub>\<F> f \<circ> \<partial>"   
  by (simp add: fbb_def fbd_ffd ffd_ffb_demorgan)

lemma ifbd_ifbb_demorgan: "Sup_pres \<phi> \<Longrightarrow> bd\<^sup>-\<^sub>\<F> \<phi> = (bb\<^sup>-\<^sub>\<F> \<circ> \<partial>\<^sub>F) \<phi>"
  by (simp add: ifbd_iffb_dual ifbb_def)  

lemma fbb_fbd_demorgan: "\<partial> \<circ> bb\<^sub>\<F> R = bd\<^sub>\<F> R \<circ> \<partial>"
  by (simp add: fbb_def fbd_ffd ffb_ffd_demorgan)

lemma ifbb_ifbd_demorgan: "Inf_pres \<phi> \<Longrightarrow> bb\<^sup>-\<^sub>\<F> \<phi> = (bd\<^sup>-\<^sub>\<F> \<circ> \<partial>\<^sub>F) \<phi>"
proof-
  assume h: "Inf_pres \<phi>"
  have "bb\<^sup>-\<^sub>\<F> \<phi> = (op\<^sub>K \<circ> fb\<^sup>-\<^sub>\<F>) \<phi>"
    by (simp add: ifbb_def)
  also have "... = (op\<^sub>K \<circ> op\<^sub>K \<circ> bd\<^sup>-\<^sub>\<F>) (\<partial>\<^sub>F \<phi>)"
    by (metis comp_apply h iffb_ifbd_dual) 
  also have "... = (bd\<^sup>-\<^sub>\<F> \<circ> \<partial>\<^sub>F) \<phi>"
    by auto
  finally show ?thesis.
qed

lemma rbd_rbb_demorgan: "\<partial> \<circ> bd\<^sub>\<R> R = bb\<^sub>\<R> R \<circ> \<partial>"
  by (simp add: rbb_def rbd_def fbd_fbb_demorgan)

lemma irbd_irbb_demorgan: "Sup_pres \<phi> \<Longrightarrow> bd\<^sup>-\<^sub>\<R> \<phi> = (bb\<^sup>-\<^sub>\<R> \<circ> \<partial>\<^sub>F) \<phi>"
  by (simp add: irbb_irfb irbd_irfb_dual)

lemma rbb_rbd_demorgan: "\<partial> \<circ> bb\<^sub>\<R> R = bd\<^sub>\<R> R \<circ> \<partial>"
  by (simp add: rbb_def rbd_def fbb_fbd_demorgan)

lemma irbb_irbd_demorgan: "Inf_pres \<phi> \<Longrightarrow> bb\<^sup>-\<^sub>\<R> \<phi> = (bd\<^sup>-\<^sub>\<R> \<circ> \<partial>\<^sub>F) \<phi>"
  by (simp add: irbb_def irbd_def ifbb_ifbd_demorgan)

text \<open>Further symmetries arise by combination.\<close>

lemma ffd_fbb_dual: "\<partial> \<circ> fd\<^sub>\<F> f = bb\<^sub>\<F> (op\<^sub>K f) \<circ> \<partial>"
  by (simp add: fbd_fbb_demorgan ffd_def)

lemma iffd_ifbb_dual: "Sup_pres \<phi> \<Longrightarrow> fd\<^sup>-\<^sub>\<F> \<phi> = (op\<^sub>K \<circ> bb\<^sup>-\<^sub>\<F> \<circ> \<partial>\<^sub>F) \<phi>"
  by (simp add: ifbd_ifbb_demorgan iffd_def)  

lemma fbb_ffd_dual: "\<partial> \<circ> bb\<^sub>\<F> f = fd\<^sub>\<F> (op\<^sub>K f) \<circ> \<partial>"
  by (simp add: fbd_ffd fbb_fbd_demorgan) 

lemma ifbb_iffd_dual: "Inf_pres \<phi> \<Longrightarrow> bb\<^sup>-\<^sub>\<F> \<phi> = (op\<^sub>K \<circ> fd\<^sup>-\<^sub>\<F> \<circ> \<partial>\<^sub>F) \<phi>"
  by (simp add: ifbb_def iffb_iffd_demorgan)

lemma rfd_rbb_dual: "\<partial> \<circ> fd\<^sub>\<R> R = bb\<^sub>\<R> (R\<inverse>) \<circ> \<partial>"
  by (metis fun_dual1 map_dual_def rbd_rbb_demorgan rfb_rbd_dual rfd_rfb_demorgan)

lemma ifd_ibb_dual: "Sup_pres \<phi> \<Longrightarrow> fd\<^sup>-\<^sub>\<R> \<phi> = ((\<smile>) \<circ> bb\<^sup>-\<^sub>\<R> \<circ> \<partial>\<^sub>F) \<phi>"
  by (simp add: irbb_irfb irbd_irfb_dual irfd_irbd)
 
lemma rbb_rfd_dual: "\<partial> \<circ> bb\<^sub>\<R> R = fd\<^sub>\<R> (R\<inverse>) \<circ> \<partial>"
  by (simp add: rbb_rfb rfb_rfd_demorgan)

lemma irbb_irfd_dual: "Inf_pres \<phi> \<Longrightarrow> bb\<^sup>-\<^sub>\<R> \<phi> = ((\<smile>) \<circ> fd\<^sup>-\<^sub>\<R> \<circ> \<partial>\<^sub>F) \<phi>"
  by (simp add: irbb_irfb irfb_irbd_dual irfd_irbd)

lemma ffd_iffd_galois: "Sup_pres \<phi> \<Longrightarrow> (\<phi> = fd\<^sub>\<F> f) = (f = fd\<^sup>-\<^sub>\<F> \<phi>)"
  unfolding ffd_def iffd_def by (metis comp_apply fbd_surj klift_eta_inv1 kop_galois)

lemma rfd_irfd_galois: "Sup_pres \<phi> \<Longrightarrow> (\<phi> = fd\<^sub>\<R> R) = (R = fd\<^sup>-\<^sub>\<R> \<phi>)"
  unfolding irfd_def rfd_def by (metis comp_apply ffd_iffd_galois r2f_f2r_galois)

lemma fbb_ifbb_galois: "Inf_pres \<phi> \<Longrightarrow> (\<phi> = bb\<^sub>\<F> f) = (f = bb\<^sup>-\<^sub>\<F> \<phi>)"
  unfolding fbb_def iffb_def by (metis (no_types, lifting) comp_apply ffb_iffb_galois ifbb_ifbd_demorgan iffb_ifbd_dual kop_galois)

lemma rbb_irbb_galois: "Inf_pres \<phi> \<Longrightarrow> (\<phi> = bb\<^sub>\<R> R) = (R = bb\<^sup>-\<^sub>\<R> \<phi>)"
  apply (simp add: rbb_def irbb_def) using fbb_ifbb_galois r2f_f2r_galois by blast

text \<open>Next I spell out the missing adjunctions.\<close>

lemma ffd_ffb_adj: "fd\<^sub>\<F> f \<stileturn> bb\<^sub>\<F> f"
  by (simp add: fbb_def ffb_fbd_galois ffd_def)

lemma ffd_fbb_galois: "(fd\<^sub>\<F> f X \<subseteq> Y) = (X \<subseteq> bb\<^sub>\<F> f Y)"
  by (simp add: fbb_def ffb_fbd_galois_var ffd_def)

lemma rfd_rfb_adj: "fd\<^sub>\<R> f \<stileturn> bb\<^sub>\<R> f"
  by (simp add: ffd_ffb_adj rbb_def rfd_def)

lemma rfd_rbb_galois: "(fd\<^sub>\<R> R X \<subseteq> Y) = (X \<subseteq> bb\<^sub>\<R> R Y)"
  by (simp add: ffd_fbb_galois rbb_def rfd_def)

text \<open>Finally, forward and backward operators of the same type are linked by conjugation.\<close>

lemma ffd_fbd_conjugation: "(fd\<^sub>\<F> f X \<inter> Y = {}) = (X \<inter> bd\<^sub>\<F> f Y = {})"
proof-
  have "(fd\<^sub>\<F> f X \<inter> Y = {}) = (fd\<^sub>\<F> f X \<subseteq> -Y)"
    by (simp add: disjoint_eq_subset_Compl)
  also have "... = (X \<subseteq> bb\<^sub>\<F> f (-Y))"
    by (simp add: ffd_fbb_galois)
  also have "... = (X \<inter> - bb\<^sub>\<F> f (-Y) = {})"
    by (simp add: disjoint_eq_subset_Compl)
  also have "... = (X \<inter> \<partial> (bb\<^sub>\<F> f (\<partial> Y)) = {})"
    by (simp add: dual_set_def)
  finally show ?thesis
    by (metis (no_types, hide_lams) comp_apply fbb_fbd_demorgan invol_dual_var)
qed

lemma rfd_rbd_conjugation: "((fd\<^sub>\<R> R X) \<inter> Y = {}) = (X \<inter> (bd\<^sub>\<R> R Y) = {})"
  by (simp add: rbd_def rfd_def ffd_fbd_conjugation) 

lemma ffb_fbb_conjugation: "((fb\<^sub>\<F> f X) \<union> Y = UNIV) = (X \<union> (bb\<^sub>\<F> f Y) = UNIV)" 
proof-
  have "((fb\<^sub>\<F> f X) \<union> Y = UNIV) = (-Y \<subseteq> fb\<^sub>\<F> f X)"
    by blast
  also have "... = (bd\<^sub>\<F> f (\<partial> Y) \<subseteq> X)"
    by (simp add: ffb_fbd_galois_var dual_set_def)
  also have "... = (\<partial> (bb\<^sub>\<F> f Y) \<subseteq> X)"
    by (metis comp_def fbb_fbd_demorgan)
  also have "... = (X \<union> (bb\<^sub>\<F> f Y) = UNIV)"
    by (metis compl_le_swap2 dual_set_def join_shunt)
    finally show ?thesis.
qed

lemma rfb_rbb_conjugation: "((fb\<^sub>\<R> R X) \<union> Y = UNIV) = (X \<union> (bb\<^sub>\<R> R Y) = UNIV)" 
  by (simp add: rfb_def rbb_def ffb_fbb_conjugation) 

end