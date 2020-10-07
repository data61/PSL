(* 
  Title: The Powerset Monad, State Transformers and Predicate Transformers
  Author: Georg Struth 
  Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>The Powerset Monad, State Transformers and Predicate Transformers\<close>

theory Powerset_Monad

imports "Order_Lattice_Props.Order_Lattice_Props" 

begin          

notation relcomp (infixl ";" 75) 
  and image ("\<P>")

subsection \<open>The Powerset Monad\<close>

text \<open>First I recall functoriality of the powerset functor.\<close>

lemma P_func1: "\<P> (f \<circ> g) = \<P> f \<circ> \<P> g"
  unfolding fun_eq_iff by force

lemma P_func2: "\<P> id = id"
  by simp

text \<open>Isabelle' type systems doesn't allow formalising arbitrary monads, but instances such as the powerset monad
can still be developed.\<close>

abbreviation eta :: "'a \<Rightarrow> 'a set" ("\<eta>") where
  "\<eta> \<equiv> (\<lambda>x. {x})"

abbreviation mu :: "'a set set \<Rightarrow> 'a set" ("\<mu>") where
  "\<mu> \<equiv> Union"

text \<open>$\eta$ and $\mu$ are natural transformations.\<close>

lemma eta_nt: "\<P> f \<circ> \<eta> = \<eta> \<circ> id f"
  by fastforce
  
lemma mu_nt: "\<mu> \<circ> (\<P> \<circ> \<P>) f = (\<P> f) \<circ> \<mu>" 
  by fastforce

text \<open>They satisfy the following coherence conditions. Explicit typing clarifies that $\eta$ and $\mu$ have different type in these expressions.\<close>
 
lemma pow_assoc: "(\<mu>::'a set set \<Rightarrow> 'a set) \<circ> \<P> (\<mu>::'a set set \<Rightarrow> 'a set) = (\<mu> ::'a set set \<Rightarrow> 'a set) \<circ> (\<mu>::'a set set set \<Rightarrow> 'a set set)"
  using fun_eq_iff by fastforce

lemma pow_un1: "(\<mu>::'a set set \<Rightarrow> 'a set) \<circ> (\<P> (\<eta>:: 'a  \<Rightarrow> 'a set)) = (id::'a set  \<Rightarrow> 'a set)"
  using fun_eq_iff by fastforce
  
lemma pow_un2: "(\<mu>::'a set set \<Rightarrow> 'a set) \<circ> (\<eta>::'a set \<Rightarrow> 'a set set) = (id::'a set \<Rightarrow> 'a set)"
  using fun_eq_iff by fastforce

text \<open>Thus the powerset monad is indeed a monad.\<close>


subsection \<open>Kleisli Category of the Powerset Monad\<close>

text \<open>Next I define the Kleisli composition and Kleisli lifting (Kleisli extension) of Kleisli arrows. 
The Kleisli lifting turns Kleisli arrows into forward predicate transformers.\<close>

definition kcomp :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('b \<Rightarrow> 'c set) \<Rightarrow> ('a  \<Rightarrow> 'c set)" (infixl "\<circ>\<^sub>K" 75) where
  "f \<circ>\<^sub>K g = \<mu> \<circ> \<P> g \<circ> f"     

lemma kcomp_prop: "(f \<circ>\<^sub>K g) x = (\<Squnion>y \<in> f x. g y)"
  by (simp add: kcomp_def)

definition klift :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> 'b set" ("_\<^sup>\<dagger>" [101] 100) where
  "f\<^sup>\<dagger> = \<mu> \<circ> \<P> f"

lemma klift_prop: "(f\<^sup>\<dagger>) X = (\<Squnion>x \<in> X. f x)" 
  by (simp add: klift_def)

lemma kcomp_klift: "f \<circ>\<^sub>K g = g\<^sup>\<dagger> \<circ> f"
  unfolding kcomp_def klift_def by simp

lemma klift_prop1: "(f\<^sup>\<dagger> \<circ> g)\<^sup>\<dagger> = f\<^sup>\<dagger> \<circ> g\<^sup>\<dagger>" 
  unfolding fun_eq_iff klift_def by simp

lemma klift_eta_inv1 [simp]: "f\<^sup>\<dagger> \<circ> \<eta> = f"
  unfolding fun_eq_iff klift_def by simp

lemma klift_eta_pres [simp]: "\<eta>\<^sup>\<dagger> = (id::'a set \<Rightarrow> 'a set)"
  unfolding fun_eq_iff klift_def by simp

lemma klift_id_pres [simp]: "id\<^sup>\<dagger> = \<mu>"
  unfolding klift_def by simp

lemma kcomp_assoc: "(f \<circ>\<^sub>K g) \<circ>\<^sub>K h = f \<circ>\<^sub>K (g \<circ>\<^sub>K h)"
  unfolding kcomp_klift klift_prop1 by force

lemma kcomp_idl [simp]: "\<eta> \<circ>\<^sub>K f = f"
  unfolding kcomp_klift by simp

lemma kcomp_idr [simp]: "f \<circ>\<^sub>K \<eta> = f"
  unfolding kcomp_klift by simp

text \<open>In the following interpretation statement, types are restricted.
This is needed for defining iteration.\<close>

interpretation kmon: monoid_mult "\<eta>" "(\<circ>\<^sub>K)"
  by unfold_locales (simp_all add: kcomp_assoc)
 
text \<open>Next I show that $\eta$ is a (contravariant) functor from Set into the Kleisli category of the powerset monad.
It simply turns functions into Kleisli arrows.\<close>

lemma eta_func1: "\<eta> \<circ> (f \<circ> g) = (\<eta> \<circ> g) \<circ>\<^sub>K (\<eta> \<circ> f)"
  unfolding fun_eq_iff kcomp_def by simp


subsection \<open>Eilenberg-Moore Algebra\<close>

text \<open>It is well known that the Eilenberg-Moore algebras of the powerset monad form complete join semilattices (hence Sup-lattices).\<close>

text \<open>First I verify that every complete lattice with structure map Sup satisfies the laws of Eilenberg-Moore algebras.\<close>

notation Sup ("\<sigma>")

lemma em_assoc [simp]: "\<sigma> \<circ> \<P> (\<sigma>::'a::complete_lattice set \<Rightarrow> 'a) = \<sigma> \<circ> \<mu>"
  apply (standard, rule antisym)
   apply (simp add: SUP_least Sup_subset_mono Sup_upper)
  by (metis (no_types, lifting) SUP_upper2 Sup_least Sup_upper UnionE comp_def)

lemma em_id [simp]: "\<sigma> \<circ> \<eta> = (id::'a::complete_lattice \<Rightarrow> 'a)"
  by (simp add: fun_eq_iff)

text\<open>Hence every Sup-lattice is an Eilenberg-Moore algebra for the powerset monad. 
The morphisms between Eilenberg-Moore algebras of the powerset monad are Sup-preserving maps. 
In particular, powersets with structure map $\mu$ form an Eilenberg-Moore algebra (in fact the free one):\<close>

lemma em_mu_assoc [simp]: "\<mu> \<circ> \<P> \<mu> = \<mu> \<circ> \<mu>"
  by simp
 
lemma em_mu_id [simp]: "\<mu> \<circ> \<eta> = id"
  by simp

text \<open>Next I show that every Eilenberg-Moore algebras for the 
powerset functor is a Sup-lattice.\<close>

class eilenberg_moore_pow = 
  fixes smap :: "'a set \<Rightarrow> 'a"
  assumes smap_assoc: "smap \<circ> \<P> smap = smap \<circ> \<mu>"
  and smap_id: "smap \<circ> \<eta> = id"

begin

definition "sleq = (\<lambda>x y. smap {x,y} = y)"

definition "sle = (\<lambda>x y. sleq x y \<and> y \<noteq> x)"

lemma smap_un1: "smap {x, smap Y} = smap ({x} \<union> Y)" 
proof-
  have "smap {x, smap Y} = smap {smap {x}, smap Y}"
    by (metis comp_apply id_apply smap_id)
  also have "... = (smap \<circ> \<P> smap) {{x}, Y}"
    by simp
  finally show ?thesis
    using local.smap_assoc by auto
qed

lemma smap_comm: "smap {x, smap Y} = smap {smap Y, x}"
  by (simp add: insert_commute)

lemma smap_un2: "smap {smap X, y} = smap (X \<union> {y})"
  using smap_comm smap_un1 by auto 

lemma sleq_refl: "sleq x x"
  by (metis id_apply insert_absorb2 local.smap_id o_apply sleq_def)

lemma sleq_trans: "sleq x y \<Longrightarrow> sleq y z \<Longrightarrow> sleq x z"
  by (metis (no_types, lifting) sleq_def smap_un1 smap_un2 sup_assoc)

lemma sleq_antisym: "sleq x y \<Longrightarrow> sleq y x \<Longrightarrow> x = y"
  by (simp add: insert_commute sleq_def)

lemma smap_ub: "x \<in> A \<Longrightarrow> sleq x (smap A)"
  using insert_absorb sleq_def smap_un1 by fastforce

lemma smap_lub: "(\<And>x. x \<in> A \<Longrightarrow> sleq x z) \<Longrightarrow> sleq (smap A) z"
proof-
  assume h: "\<And>x. x \<in> A \<Longrightarrow> sleq x z"
  have "smap {smap A, z} = smap (A \<union> {z})"
    by (simp add: smap_un2)
  also have "... = smap ((\<Union>x \<in> A. {x,z})  \<union> {z})" 
    by (rule_tac f=smap in arg_cong, auto)
  also have "... = smap {(smap \<circ> \<mu>) {{x,z} |x. x \<in> A}, z}"
    by (simp add: Setcompr_eq_image smap_un2)
  also have "... = smap {(smap \<circ> \<P> smap) {{x,z} |x. x \<in> A}, z}"
    by (simp add: local.smap_assoc)
  also have "... = smap {smap {smap {x,z} |x. x \<in> A}, z}"
    by (simp add: Setcompr_eq_image image_image)
  also have "... = smap {smap {z |x. x \<in> A}, z}"
    by (metis h sleq_def)
  also have "... = smap ({z |x. x \<in> A} \<union> {z})"
    by (simp add: smap_un2)
  also have "... = smap {z}"
     by (rule_tac f=smap in arg_cong, auto)
   finally show ?thesis
     using sleq_def sleq_refl by auto
 qed

sublocale smap_Sup_lat: Sup_lattice smap sleq sle
  by unfold_locales (simp_all add: sleq_refl sleq_antisym sleq_trans smap_ub smap_lub)

text \<open>Hence every complete lattice is an Eilenberg-Moore algebra of $\mathcal{P}$.\<close>

no_notation Sup ("\<sigma>")

end


subsection \<open>Isomorphism between Kleisli Category and Rel\<close>

text \<open>This is again well known---the isomorphism is essentially curry vs uncurry. Kleisli arrows are nondeterministic functions; 
they are also known as state transformers.  Binary relations are very well developed in Isabelle; Kleisli composition of Kleisli 
arrows isn't. Ideally one should therefore use the isomorphism to transport theorems from relations to Kleisli arrows automatically. 
I spell out the isomorphisms and prove that the full quantalic structure, that is, complete lattices plus compositions, 
is preserved by the isomorphisms.\<close>

abbreviation kzero :: "'a \<Rightarrow> 'b set" ("\<zeta>") where
  "\<zeta> \<equiv> (\<lambda>x::'a. {})"

text \<open>First I define the morphisms. The second one is nothing but the graph of a function.\<close>

definition r2f :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b set" ("\<F>") where
  "\<F> R = Image R \<circ> \<eta>" 

definition f2r :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<times> 'b) set" ("\<R>") where
  "\<R> f = {(x,y). y \<in> f x}"

text \<open>The functors form a bijective pair.\<close>

lemma r2f2r_inv1 [simp]: "\<R> \<circ> \<F> = id"
  unfolding f2r_def r2f_def by force

lemma f2r2f_inv2 [simp]: "\<F> \<circ> \<R> = id"
  unfolding f2r_def r2f_def by force

lemma r2f_f2r_galois: "(\<R> f = R) = (\<F> R = f)"
  by (force simp: f2r_def r2f_def)

lemma r2f_f2r_galois_var: "(\<R> \<circ> f = R) = (\<F> \<circ> R = f)"
  by (force simp: f2r_def r2f_def)

lemma r2f_f2r_galois_var2: "(f \<circ> \<R> = R) = (R \<circ> \<F> = f)"
  by (metis (no_types, hide_lams) comp_id f2r2f_inv2 map_fun_def o_assoc r2f2r_inv1)

lemma r2f_inj: "inj \<F>"
  by (meson inj_on_inverseI r2f_f2r_galois)

lemma f2r_inj: "inj \<R>"
  unfolding inj_def using r2f_f2r_galois by metis

lemma r2f_mono: "\<forall>f g. \<F> \<circ> f = \<F> \<circ> g \<longrightarrow> f = g"
  by (force simp: fun_eq_iff r2f_def)

lemma f2r_mono: "\<forall>f g. \<R> \<circ> f = \<R> \<circ> g \<longrightarrow> f = g" 
  by (force simp: fun_eq_iff f2r_def)

lemma r2f_mono_iff: "(\<F> \<circ> f = \<F> \<circ> g) = (f = g)"
  using r2f_mono by blast

lemma f2r_mono_iff : "(\<R> \<circ> f = \<R> \<circ> g) = (f = g)"
  using f2r_mono by blast

lemma r2f_inj_iff: "(\<R> f = \<R> g) = (f = g)"
  by (simp add: f2r_inj inj_eq)

lemma f2r_inj_iff: "(\<F> R = \<F> S) = (R = S)"
  by (simp add: r2f_inj inj_eq)

lemma r2f_surj: "surj \<F>"
  by (metis r2f_f2r_galois surj_def)

lemma f2r_surj: "surj \<R>"
  using r2f_f2r_galois by auto

lemma r2f_epi: "\<forall>f g. f \<circ> \<F> = g \<circ> \<F> \<longrightarrow> f = g"
  by (metis r2f_f2r_galois_var2)

lemma f2r_epi: "\<forall>f g. f \<circ> \<R> = g \<circ> \<R> \<longrightarrow> f = g"
  by (metis r2f_f2r_galois_var2)

lemma r2f_epi_iff: "(f \<circ> \<F> = g \<circ> \<F>) = (f = g)"
  using r2f_epi by blast

lemma f2r_epi_iff: "(f \<circ> \<R> = g \<circ> \<R>) = (f = g)"
  using f2r_epi by blast

lemma r2f_bij: "bij \<F>"
  by (simp add: bijI r2f_inj r2f_surj)

lemma f2r_bij: "bij \<R>"
  by (simp add: bij_def f2r_inj f2r_surj)

text \<open>r2f is essentially curry and f2r is uncurry, yet in Isabelle the type of sets and predicates 
(boolean-valued functions) are different. Collect transforms predicates into sets and the following function
sets into predicates:\<close>

abbreviation "s2p X \<equiv> (\<lambda>x. x \<in> X)"

lemma r2f_curry: "r2f R = Collect \<circ> (curry \<circ> s2p) R"
  by (force simp: r2f_def fun_eq_iff curry_def)

lemma f2r_uncurry: "f2r f = (Collect \<circ> case_prod) (s2p \<circ> f)"
  by (force simp: fun_eq_iff f2r_def)

text \<open>Uncurry is case-prod in Isabelle.\<close>

text \<open>f2r and r2f preserve the quantalic structures of relations and Kleisli arrows. In particular they are functors.\<close>

lemma r2f_comp_pres: "\<F> (R ; S) = \<F> R \<circ>\<^sub>K \<F> S"
  unfolding fun_eq_iff r2f_def kcomp_def by force

lemma r2f_Id_pres [simp]: "\<F> Id = \<eta>"
  unfolding fun_eq_iff r2f_def by simp

lemma r2f_Sup_pres: "Sup_pres \<F>"
  unfolding fun_eq_iff r2f_def by force

lemma r2f_Sup_pres_var: "\<F> (\<Union>R) = (\<Squnion>r \<in> R. \<F> r)" 
  unfolding r2f_def by force

lemma r2f_sup_pres: "sup_pres \<F>"
  unfolding r2f_def by force

lemma r2f_Inf_pres: "Inf_pres \<F>"
  unfolding fun_eq_iff r2f_def by force

lemma r2f_Inf_pres_var: "\<F> (\<Sqinter>R) = (\<Sqinter>r \<in> R. \<F> r)" 
  unfolding r2f_def by force

lemma r2f_inf_pres: "inf_pres \<F>"
  unfolding r2f_def by force

lemma r2f_bot_pres: "bot_pres \<F>"
  by (metis SUP_empty Sup_empty r2f_Sup_pres_var)

lemma r2f_top_pres: "top_pres \<F>"
  by (metis Sup_UNIV r2f_Sup_pres_var r2f_surj)

lemma r2f_leq: "(R \<subseteq> S) = (\<F> R \<le> \<F> S)"
  by (metis le_iff_sup r2f_f2r_galois r2f_sup_pres)

text \<open>Dual statements for f2r hold. Can one automate this?\<close>
 
lemma f2r_kcomp_pres: "\<R> (f \<circ>\<^sub>K g) = \<R> f ; \<R> g"
  by (simp add: r2f_f2r_galois r2f_comp_pres pointfree_idE)

lemma f2r_eta_pres [simp]: "\<R> \<eta> = Id"
  by (simp add: r2f_f2r_galois) 

lemma f2r_Sup_pres:"Sup_pres \<R>"
  by (auto simp: r2f_f2r_galois_var comp_assoc[symmetric] r2f_Sup_pres image_comp)

lemma f2r_Sup_pres_var: "\<R> (\<Squnion>F) = (\<Squnion>f \<in> F. \<R> f)"
  by (simp add: r2f_f2r_galois r2f_Sup_pres_var image_comp)

lemma f2r_sup_pres: "sup_pres \<R>"
  by (simp add: r2f_f2r_galois r2f_sup_pres pointfree_idE)

lemma f2r_Inf_pres: "Inf_pres \<R>"
  by (auto simp: r2f_f2r_galois_var comp_assoc[symmetric] r2f_Inf_pres image_comp)

lemma f2r_Inf_pres_var: "\<R> (\<Sqinter>F) = (\<Inter>f \<in> F. \<R> f)"
  by (simp add: r2f_f2r_galois r2f_Inf_pres_var image_comp)

lemma f2r_inf_pres: "inf_pres \<R>"
  by (simp add: r2f_f2r_galois r2f_inf_pres pointfree_idE)

lemma f2r_bot_pres: "bot_pres \<R>"
  by (simp add: r2f_bot_pres r2f_f2r_galois)

lemma f2r_top_pres: "top_pres \<R>"
  by (simp add: r2f_f2r_galois r2f_top_pres)

lemma f2r_leq: "(f \<le> g) = (\<R> f \<subseteq> \<R> g)"
  by (metis r2f_f2r_galois r2f_leq)

text \<open>Relational subidentities are isomorphic to particular Kleisli arrows.\<close>

lemma r2f_Id_on1: "\<F> (Id_on X) = (\<lambda>x. if x \<in> X then {x} else {})"
  by (force simp add: fun_eq_iff r2f_def Id_on_def)

lemma r2f_Id_on2: "\<F> (Id_on X) \<circ>\<^sub>K f = (\<lambda>x. if x \<in> X then f x else {})"
  unfolding fun_eq_iff Id_on_def r2f_def kcomp_def by auto

lemma r2f_Id_on3: "f \<circ>\<^sub>K \<F> (Id_on X) = (\<lambda>x. X \<inter> f x)"
  unfolding kcomp_def r2f_def Id_on_def fun_eq_iff by auto


subsection \<open>The opposite Kleisli Category\<close>

text \<open>Opposition is funtamental for categories; yet hard to realise in Isabelle in general. Due to the access to relations,
the Kleisli category of the powerset functor is an exception.\<close>

notation converse ("\<smile>")

definition kop :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b \<Rightarrow> 'a set" ("op\<^sub>K") where
  "op\<^sub>K = \<F> \<circ> (\<smile>) \<circ> \<R>"

text \<open>Kop is a contravariant functor.\<close>

lemma kop_contrav: "op\<^sub>K (f \<circ>\<^sub>K g) = op\<^sub>K g \<circ>\<^sub>K op\<^sub>K f"
  unfolding kop_def r2f_def f2r_def converse_def kcomp_def fun_eq_iff comp_def by fastforce

lemma kop_func2 [simp]: "op\<^sub>K \<eta> = \<eta>"
  unfolding kop_def r2f_def f2r_def converse_def comp_def fun_eq_iff by fastforce

lemma converse_idem [simp]: "(\<smile>) \<circ> (\<smile>) = id"
  using comp_def by auto

lemma converse_galois: "((\<smile>) \<circ> f = g) = ((\<smile>) \<circ> g = f)"
  by auto

lemma converse_galois2: "(f \<circ> (\<smile>) = g) = (g \<circ> (\<smile>) = f)"
  apply (simp add: fun_eq_iff)
  by (metis converse_converse)

lemma converse_mono_iff: "((\<smile>) \<circ> f = (\<smile>) \<circ> g) = (f = g)"
  using converse_galois by force

lemma converse_epi_iff: "(f \<circ> (\<smile>) = g \<circ> (\<smile>)) = (f = g)"
  using converse_galois2 by force

lemma kop_idem [simp]: "op\<^sub>K \<circ> op\<^sub>K = id" 
  unfolding kop_def comp_def fun_eq_iff by (metis converse_converse id_apply r2f_f2r_galois)

lemma kop_galois: "(op\<^sub>K f = g) = (op\<^sub>K g = f)"
  by (metis kop_idem pointfree_idE)

lemma kop_galois_var: "(op\<^sub>K \<circ> f = g) = (op\<^sub>K \<circ> g = f)"
  by (auto simp: kop_def f2r_def r2f_def converse_def fun_eq_iff)   

lemma kop_galois_var2: "(f \<circ> op\<^sub>K = g) = (g \<circ> op\<^sub>K = f)"
  by (metis (no_types, hide_lams) comp_assoc comp_id kop_idem)

lemma kop_inj: "inj op\<^sub>K"
  unfolding inj_def by (simp add: f2r_inj_iff kop_def r2f_inj_iff)

lemma kop_inj_iff: "(op\<^sub>K f = op\<^sub>K g) = (f = g)"
  by (simp add: inj_eq kop_inj)

lemma kop_surj: "surj op\<^sub>K"
  unfolding surj_def by (metis kop_galois)

lemma kop_bij: "bij op\<^sub>K"
  by (simp add: bij_def kop_inj kop_surj)

lemma kop_mono: "(op\<^sub>K \<circ> f = op\<^sub>K \<circ> g) \<Longrightarrow> (f = g)"
  by (simp add: fun.inj_map inj_eq kop_inj)

lemma kop_mono_iff: "(op\<^sub>K \<circ> f = op\<^sub>K \<circ> g) = (f = g)"
  using kop_mono by blast

lemma kop_epi: "(f \<circ> op\<^sub>K = g \<circ> op\<^sub>K) \<Longrightarrow> (f = g)"
  by (metis kop_galois_var2)

lemma kop_epi_iff: "(f \<circ> op\<^sub>K = g \<circ> op\<^sub>K) = (f = g)"
  using kop_epi by blast

lemma Sup_pres_kop: "Sup_pres op\<^sub>K"
  unfolding kop_def fun_eq_iff comp_def r2f_def f2r_def converse_def by auto

lemma Inf_pres_kop: "Inf_pres op\<^sub>K"
  unfolding kop_def fun_eq_iff comp_def r2f_def f2r_def converse_def by auto

end