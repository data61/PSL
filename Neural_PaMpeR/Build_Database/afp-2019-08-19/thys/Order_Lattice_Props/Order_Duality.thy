(* 
  Title: Ad-Hoc Duality for Orderings and Lattices
  Author: Georg Struth 
  Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Ad-Hoc Duality for Orderings and Lattices\<close>

theory Order_Duality
  imports Sup_Lattice

begin

text \<open>This component presents an "explicit" formalisation of order and lattice duality. It augments the data type based one
 used by Wenzel in his lattice components \cite{Wenzel}, and complements the "implicit" formalisation given by locales. It uses a functor dual, 
supplied within a type class, which is simply a bijection (isomorphism) between types, with the constraint that
the dual of a dual object is the original object. In Wenzel's formalisation, by contrast, dual is a bijection, but not
 idempotent or involutive. In the past, Preoteasa has used a similar approach with Isabelle~\cite{Preoteasa11b}.\<close>

text \<open>Duality is such a fundamental concept in order and lattice theory that it probably deserves to be included in the type classes
for these objects, as in this section.\<close>

class dual =
  fixes dual :: "'a \<Rightarrow> 'a" ("\<partial>")
  assumes inj_dual: "inj \<partial>"
  and invol_dual [simp]: "\<partial> \<circ> \<partial> = id"

text \<open>This type class allows one to define a type dual. It is actually a dependent type
for which dual can be instantiated.\<close>

typedef (overloaded) 'a dual = "range (dual::'a::dual \<Rightarrow> 'a)"
  by fastforce

setup_lifting type_definition_dual

text \<open>At the moment I have no use for this type.\<close>

context dual
begin

lemma invol_dual_var [simp]: "\<partial> (\<partial> x) = x"
  by (simp add: pointfree_idE)

lemma surj_dual: "surj \<partial>"
  unfolding surj_def by (metis invol_dual_var)

lemma bij_dual: "bij \<partial>"
  by (simp add: bij_def inj_dual surj_dual)

lemma inj_dual_iff: "(\<partial> x = \<partial> y) = (x = y)"
  by (meson inj_dual injD)

lemma dual_iff: "(\<partial> x = y) = (x = \<partial> y)"
  by auto

lemma the_inv_dual: "the_inv \<partial> = \<partial>"
  by (metis comp_apply id_def invol_dual_var inj_dual surj_dual surj_fun_eq the_inv_f_o_f_id)

end

text \<open>In boolean algebras, duality is of course De Morgan duality and can be expressed within the language.\<close>

sublocale boolean_algebra \<subseteq> ba_dual: dual "uminus"  
  by (unfold_locales, simp_all add: inj_def)

definition map_dual:: "('a \<Rightarrow> 'b) \<Rightarrow> 'a::dual \<Rightarrow> 'b::dual" ("\<partial>\<^sub>F") where 
  "\<partial>\<^sub>F f = \<partial> \<circ> f \<circ> \<partial>"  

lemma map_dual_func1: "\<partial>\<^sub>F (f \<circ> g) = \<partial>\<^sub>F f \<circ> \<partial>\<^sub>F g"
  by (metis (no_types, lifting) comp_assoc comp_id invol_dual map_dual_def)

lemma map_dual_func2 [simp]: "\<partial>\<^sub>F id = id"
  by (simp add: map_dual_def)

lemma map_dual_nat_iso: "\<partial>\<^sub>F f \<circ> \<partial> = \<partial> \<circ> id f"
  by (simp add: comp_assoc map_dual_def)

lemma map_dual_invol [simp]: "\<partial>\<^sub>F \<circ> \<partial>\<^sub>F = id"
  unfolding map_dual_def comp_def fun_eq_iff by simp
  
text \<open>Thus map-dual is naturally isomorphic to the identify functor: The function dual is a natural transformation 
between  map-dual and the identity functor, and, because it has a two-sided inverse --- itself, it is a natural isomorphism.\<close>

text \<open>The generic function set-dual provides another natural transformation (see below). Before introducing it, we introduce useful notation 
for a widely used function.\<close>

abbreviation "\<eta> \<equiv> (\<lambda>x. {x})"

lemma eta_inj: "inj \<eta>"
  by simp

definition "set_dual = \<eta> \<circ> \<partial>"

lemma set_dual_prop: "set_dual (\<partial> x) = {x}"
  by (metis comp_apply dual_iff set_dual_def)

text \<open>The next four lemmas show that (functional) image and preimage are functors (on functions). This does not really belong here, 
but it is useful for what follows. The interaction between duality and (pre)images is needed in applications.\<close>

lemma image_func1: "(`) (f \<circ> g) = (`) f \<circ> (`) g"
  unfolding fun_eq_iff by (simp add: image_comp) 

lemma image_func2: "(`) id = id"
  by simp

lemma vimage_func1: "(-`) (f \<circ> g) = (-`) g \<circ> (-`) f"
  unfolding fun_eq_iff by (simp add: vimage_comp)

lemma vimage_func2: "(-`) id = id"
  by simp

lemma iso_image: "mono ((`) f)"
  by (simp add: image_mono monoI)

lemma iso_preimage: "mono ((-`) f)"
  by (simp add: monoI vimage_mono)

context dual
begin

lemma image_dual [simp]: "(`) \<partial> \<circ> (`) \<partial> = id"
  by (metis image_func1 image_func2 invol_dual)

lemma vimage_dual [simp]: "(-`) \<partial> \<circ> (-`) \<partial> = id"
  by (simp add: set.comp)

end

text \<open>The following natural transformation between the powerset functor (image) and the identity functor
is well known.\<close>

lemma power_set_func_nat_trans: "\<eta> \<circ> id f = (`) f \<circ> \<eta>"
  unfolding fun_eq_iff comp_def by simp

text \<open>As an instance, set-dual is a natural transformation with built-in type coercion.\<close>

lemma dual_singleton: "(`) \<partial> \<circ> \<eta> = \<eta> \<circ> \<partial>"  
  by auto

lemma finite_dual [simp]: "finite \<circ> (`) \<partial> = finite"
  unfolding fun_eq_iff comp_def using inj_dual finite_vimageI inj_vimage_image_eq by fastforce

lemma finite_dual_var [simp]: "finite (\<partial> ` X) = finite X"
  by (metis comp_def finite_dual)

lemma subset_dual: "(X = \<partial> ` Y) = (\<partial> ` X = Y)"
  by (metis image_dual pointfree_idE)

lemma subset_dual1: "(X \<subseteq> Y) = (\<partial> ` X \<subseteq> \<partial> ` Y)"
  by (simp add: inj_dual inj_image_subset_iff) 

lemma dual_empty [simp]: "\<partial> ` {} = {}"
  by simp

lemma dual_UNIV [simp]: "\<partial> ` UNIV = UNIV"
  by (simp add: surj_dual)

lemma fun_dual1: "(f = g \<circ> \<partial>) = (f \<circ> \<partial> = g)"
  by (metis comp_assoc comp_id invol_dual)

lemma fun_dual2: "(f = \<partial> \<circ> g) = (\<partial> \<circ> f = g)"
  by (metis comp_assoc fun.map_id invol_dual)

lemma fun_dual3: "(f = g \<circ> (`) \<partial>) = (f \<circ> (`) \<partial> = g)"
  by (metis comp_id image_dual o_assoc)

lemma fun_dual4: "(f = (`) \<partial> \<circ> g) = ((`) \<partial> \<circ> f = g)"
  by (metis comp_assoc id_comp image_dual)

lemma fun_dual5: "(f = \<partial> \<circ> g \<circ> \<partial>) = (\<partial> \<circ> f \<circ> \<partial> = g)"
  by (metis comp_assoc fun_dual1 fun_dual2)

lemma fun_dual6: "(f = (`) \<partial> \<circ> g \<circ> (`) \<partial>) = ((`) \<partial> \<circ> f \<circ> (`) \<partial> = g)"
  by (simp add: comp_assoc fun_dual3 fun_dual4)

lemma fun_dual7: "(f = \<partial> \<circ> g \<circ> (`) \<partial>) = (\<partial> \<circ> f \<circ> (`) \<partial> = g)"
  by (simp add: comp_assoc fun_dual2 fun_dual3)

lemma fun_dual8: "(f = (`) \<partial> \<circ> g \<circ> \<partial>) = ((`) \<partial> \<circ> f \<circ> \<partial> = g)"
  by (simp add: comp_assoc fun_dual1 fun_dual4)

lemma map_dual_dual: "(\<partial>\<^sub>F f = g) = (\<partial>\<^sub>F g = f)"
  by (metis map_dual_invol pointfree_idE)

text \<open>The next facts show incrementally that the dual of a complete lattice is a complete lattice.\<close>

class ord_with_dual = dual + ord +
  assumes ord_dual: "x \<le> y \<Longrightarrow> \<partial> y \<le> \<partial> x"

begin

lemma dual_dual_ord: "(\<partial> x \<le> \<partial> y) = (y \<le> x)"
  by (metis dual_iff ord_dual)

end

lemma ord_pres_dual:
  fixes f :: "'a::ord_with_dual \<Rightarrow> 'b::ord_with_dual"   
  shows "ord_pres f \<Longrightarrow> ord_pres (\<partial>\<^sub>F f)"
  by (simp add: dual_dual_ord map_dual_def ord_pres_def)

lemma map_dual_anti: "(f::'a::ord_with_dual \<Rightarrow> 'b::ord_with_dual) \<le> g  \<Longrightarrow> \<partial>\<^sub>F g \<le> \<partial>\<^sub>F f"
  by (simp add: le_fun_def map_dual_def ord_dual)
  
class preorder_with_dual = ord_with_dual + preorder

begin

lemma less_dual_def_var: "(\<partial> y < \<partial> x) = (x < y)"
  by (simp add: dual_dual_ord less_le_not_le)

end

class order_with_dual = preorder_with_dual + order

lemma iso_map_dual: 
  fixes f :: "'a::order_with_dual \<Rightarrow> 'b::order_with_dual"   
  shows "mono f \<Longrightarrow> mono (\<partial>\<^sub>F f)"
  by (simp add: ord_pres_dual ord_pres_mono)

class lattice_with_dual = lattice + dual +
  assumes sup_dual_def: "\<partial> (x \<squnion> y) = \<partial> x \<sqinter> \<partial> y"

begin

subclass order_with_dual
  by (unfold_locales, metis inf.absorb_iff2 sup_absorb1 sup_commute sup_dual_def)

lemma inf_dual: "\<partial> (x \<sqinter> y) = \<partial> x \<squnion> \<partial> y"
  by (metis invol_dual_var sup_dual_def) 

lemma inf_to_sup: "x \<sqinter> y = \<partial> (\<partial> x \<squnion> \<partial> y)"
  using inf_dual dual_iff by fastforce

lemma sup_to_inf: "x \<squnion> y = \<partial> (\<partial> x \<sqinter> \<partial> y)"
  by (simp add: inf_dual)

end

class bounded_lattice_with_dual = lattice_with_dual + bounded_lattice

begin

lemma bot_dual: "\<partial> \<bottom> = \<top>"
  by (metis dual_dual_ord dual_iff le_bot top_greatest)

lemma top_dual: "\<partial> \<top> = \<bottom>"
  using bot_dual dual_iff by force

end

class boolean_algebra_with_dual = lattice_with_dual + boolean_algebra

sublocale boolean_algebra \<subseteq> badual: boolean_algebra_with_dual _ _ _ _ _ _ _ _ uminus
  by unfold_locales simp_all

class Sup_lattice_with_dual = Sup_lattice + dual +
  assumes Sups_dual_def: "\<partial> \<circ> Sup = Infs \<circ> (`) \<partial>"

class Inf_lattice_with_dual = Inf_lattice + dual +
  assumes Sups_dual_def: "\<partial> \<circ> Supi = Inf \<circ> (`) \<partial>"

class complete_lattice_with_dual = complete_lattice + dual +
  assumes Sups_dual_def: "\<partial> \<circ> Sup = Inf \<circ> (`) \<partial>"

sublocale Sup_lattice_with_dual \<subseteq> sclatd: complete_lattice_with_dual Infs Sup infs "(\<le>)" le sups bots tops "\<partial>"
  by (unfold_locales, simp add: Sups_dual_def)

sublocale Inf_lattice_with_dual \<subseteq> iclatd: complete_lattice_with_dual Inf Supi infi "(\<le>)" le supi boti topi "\<partial>"
  by (unfold_locales, simp add: Sups_dual_def)

context complete_lattice_with_dual
begin

lemma Inf_dual: "\<partial> \<circ> Inf = Sup \<circ> (`) \<partial>"
  by (metis comp_assoc comp_id fun.map_id Sups_dual_def image_dual invol_dual)

lemma Inf_dual_var: "\<partial> (\<Sqinter>X) = \<Squnion>(\<partial> ` X)"
  using comp_eq_dest Inf_dual by fastforce

lemma Inf_to_Sup: "Inf = \<partial> \<circ> Sup \<circ> (`) \<partial>"
  by (auto simp add: Sups_dual_def image_comp)

lemma Inf_to_Sup_var: "\<Sqinter>X = \<partial> (\<Squnion>(\<partial> ` X))"
  using Inf_dual_var dual_iff by fastforce

lemma Sup_to_Inf: "Sup = \<partial> \<circ> Inf \<circ> (`) \<partial>"
  by (auto simp add: Inf_dual image_comp)

lemma Sup_to_Inf_var: "\<Squnion>X = \<partial> (\<Sqinter>(\<partial> ` X))"
  using Sup_to_Inf by force

lemma Sup_dual_def_var: "\<partial> (\<Squnion>X) = \<Sqinter> (\<partial> ` X)"
  using comp_eq_dest Sups_dual_def by fastforce

lemma bot_dual_def: "\<partial> \<top> = \<bottom>"
  by (smt Inf_UNIV Sup_UNIV Sups_dual_def surj_dual o_eq_dest)

lemma top_dual_def: "\<partial> \<bottom> = \<top>"
  using bot_dual_def dual_iff by blast

lemma inf_dual2: "\<partial> (x \<sqinter> y) = \<partial> x \<squnion> \<partial> y"
  by (smt comp_eq_elim Inf_dual Inf_empty Inf_insert SUP_insert inf_top.right_neutral)

lemma sup_dual: "\<partial> (x \<squnion> y) = \<partial> x \<sqinter> \<partial> y"
  by (metis inf_dual2 dual_iff)

subclass lattice_with_dual
  by (unfold_locales, auto simp: inf_dual sup_dual)

subclass bounded_lattice_with_dual..

end

end





