(* 
  Title: Representation Theorems for Orderings and Lattices
  Author: Georg Struth 
  Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Representation Theorems for Orderings and Lattices\<close>

theory Representations
  imports Order_Lattice_Props

begin

subsection \<open>Representation of Posets\<close>

text \<open>The isomorphism between partial orders and downsets with set inclusion is well known. It forms the basis of Priestley and Stone duality.
I show it not only for objects, but also order morphisms, hence establish equivalences and isomorphisms between categories.\<close>

typedef (overloaded) 'a downset = "range (\<down>::'a::ord \<Rightarrow> 'a set)"
  by fastforce

setup_lifting type_definition_downset
  
text \<open>The map ds yields the isomorphism between the set and the powerset level if its range is restricted to downsets.\<close>
  
definition ds :: "'a::ord \<Rightarrow> 'a downset" where 
  "ds = Abs_downset \<circ> \<down>"

text \<open>In a complete lattice, its inverse is Sup.\<close>

definition SSup :: "'a::complete_lattice downset \<Rightarrow> 'a" where
  "SSup = Sup \<circ> Rep_downset"

lemma ds_SSup_inv: "ds \<circ> SSup = (id::'a::complete_lattice downset \<Rightarrow> 'a downset)"
  unfolding ds_def SSup_def
  by (smt Rep_downset Rep_downset_inverse cSup_atMost eq_id_iff imageE o_def ord_class.atMost_def ord_class.downset_prop)

lemma SSup_ds_inv: "SSup \<circ> ds = (id::'a::complete_lattice \<Rightarrow> 'a)"
  unfolding ds_def SSup_def fun_eq_iff id_def comp_def by (simp add: Abs_downset_inverse pointfree_idE) 

instantiation downset :: (ord) order
begin 
  
lift_definition less_eq_downset :: "'a downset \<Rightarrow> 'a downset \<Rightarrow> bool" is "(\<lambda>X Y. Rep_downset X \<subseteq> Rep_downset Y)" .

lift_definition less_downset :: "'a downset \<Rightarrow> 'a downset \<Rightarrow> bool" is "(\<lambda>X Y. Rep_downset X \<subset> Rep_downset Y)" .

instance
  by (intro_classes, transfer, auto simp: Rep_downset_inject less_eq_downset_def)

end

lemma ds_iso: "mono ds"
  unfolding mono_def ds_def fun_eq_iff comp_def
  by (metis Abs_downset_inverse downset_iso_iff less_eq_downset.rep_eq rangeI)
 
lemma ds_faithful: "ds x \<le> ds y \<Longrightarrow> x \<le> (y::'a::order)"
  by (simp add: Abs_downset_inverse downset_faithful ds_def less_eq_downset.rep_eq)

lemma ds_inj: "inj (ds::'a::order \<Rightarrow> 'a downset)"
  by (simp add: ds_faithful dual_order.antisym injI)

lemma ds_surj: "surj ds"
  by (metis (no_types, hide_lams) Rep_downset Rep_downset_inverse ds_def image_iff o_apply surj_def)

lemma ds_bij: "bij (ds::'a::order \<Rightarrow> 'a downset)"
  by (simp add: bijI ds_inj ds_surj)

lemma ds_ord_iso: "ord_iso ds"
  unfolding ord_iso_def comp_def inf_bool_def by (smt UNIV_I ds_bij ds_faithful ds_inj ds_iso ds_surj f_the_inv_into_f inf1I mono_def)

text \<open>The morphishms between orderings and downsets are isotone functions. One can define functors mapping back and forth between these.\<close>

definition map_ds :: "('a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<Rightarrow> ('a downset \<Rightarrow> 'b downset)" where
  "map_ds f = ds \<circ> f \<circ> SSup"

text \<open>This definition is actually contrived. We have shown that a function f between posets P and Q is isotone if and only if the 
inverse image of f maps downclosed sets in Q to downclosed sets in P. There is the following duality: ds is a natural transformation 
between the identity functor and the preimage functor as a contravariant functor from P to Q. Hence orderings with isotone maps and 
downsets with downset-preserving maps are dual, which is a first step towards Stone duality. I don't see a way of proving this with Isabelle, 
as the types of the preimage of f are the wrong way and I don't see how I could capture opposition with what I have.\<close> 

(*lemma "mono (f::'a::complete_lattice \<Rightarrow> 'b::complete_lattimap_ds f = Abs_downset \<circ> (-`) f \<circ> Rep_downset" doesn't work! *)

lemma map_ds_prop: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice" 
  shows "map_ds f \<circ> ds = ds \<circ> f"
  unfolding map_ds_def by (simp add: SSup_ds_inv comp_assoc)

lemma map_ds_prop2: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "map_ds f \<circ> ds = ds \<circ> id f"
  unfolding map_ds_def by (simp add: SSup_ds_inv comp_assoc)

text \<open>This is part of showing that map-ds is naturally isomorphic to the identity functor, ds being the natural isomorphism.\<close>

definition map_SSup :: "('a downset \<Rightarrow> 'b downset) \<Rightarrow> ('a::complete_lattice \<Rightarrow> 'b::complete_lattice)" where
  "map_SSup F = SSup \<circ> F \<circ> ds"

lemma map_ds_iso_pres: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "mono f \<Longrightarrow> mono (map_ds f)"
  unfolding fun_eq_iff mono_def map_ds_def ds_def SSup_def comp_def
  by (metis Abs_downset_inverse Sup_subset_mono downset_iso_iff less_eq_downset.rep_eq rangeI)

lemma map_SSup_iso_pres: 
  fixes F :: "'a::complete_lattice downset \<Rightarrow> 'b::complete_lattice downset"
  shows "mono F \<Longrightarrow> mono (map_SSup F)"
  unfolding fun_eq_iff mono_def map_SSup_def ds_def SSup_def comp_def
  by (metis Abs_downset_inverse Sup_subset_mono downset_iso_iff less_eq_downset.rep_eq rangeI)

lemma map_SSup_prop: 
  fixes F :: "'a::complete_lattice downset \<Rightarrow> 'b::complete_lattice downset"
  shows "ds \<circ> map_SSup F = F \<circ> ds"
  unfolding map_SSup_def by (metis ds_SSup_inv fun.map_id0 id_def rewriteL_comp_comp)

lemma map_SSup_prop2: 
  fixes F :: "'a::complete_lattice downset \<Rightarrow> 'b::complete_lattice downset"
  shows "ds \<circ> map_SSup F = id F \<circ> ds"
  by (simp add: map_SSup_prop)

lemma map_ds_func1: "map_ds id = (id::'a::complete_lattice downset\<Rightarrow> 'a downset)"
  by (simp add: ds_SSup_inv map_ds_def)

lemma map_ds_func2: 
  fixes g :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "map_ds (f \<circ> g) = map_ds f \<circ> map_ds g"
  unfolding map_ds_def fun_eq_iff comp_def ds_def SSup_def
  by (metis Abs_downset_inverse Sup_atMost atMost_def downset_prop rangeI)

lemma map_SSup_func1: "map_SSup (id::'a::complete_lattice downset\<Rightarrow> 'a downset) = id"
  by (simp add: SSup_ds_inv map_SSup_def)

lemma map_SSup_func2: 
  fixes F :: "'c::complete_lattice downset \<Rightarrow> 'b::complete_lattice downset"
  and G :: "'a::complete_lattice downset \<Rightarrow> 'c downset"
  shows "map_SSup (F \<circ> G) = map_SSup F \<circ> map_SSup G"
  unfolding map_SSup_def fun_eq_iff comp_def id_def ds_def
  by (metis comp_apply ds_SSup_inv ds_def id_apply)

lemma map_SSup_map_ds_inv: "map_SSup \<circ> map_ds = (id::('a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<Rightarrow> ('a \<Rightarrow> 'b))"
  by (metis (no_types, hide_lams) SSup_ds_inv comp_def eq_id_iff fun.map_comp fun.map_id0 id_apply map_SSup_prop map_ds_prop)

lemma map_ds_map_SSup_inv: "map_ds \<circ> map_SSup = (id::('a::complete_lattice downset \<Rightarrow> 'b::complete_lattice downset) \<Rightarrow> ('a downset \<Rightarrow> 'b downset))"
  unfolding map_SSup_def map_ds_def SSup_def ds_def id_def comp_def fun_eq_iff
  by (metis (no_types, lifting) Rep_downset Rep_downset_inverse Sup_downset_id image_iff pointfree_idE)

lemma inj_map_ds: "inj (map_ds::('a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<Rightarrow> ('a downset \<Rightarrow> 'b downset))"
  by (metis (no_types, lifting) SSup_ds_inv fun.map_id0 id_comp inj_def map_ds_prop rewriteR_comp_comp2)

lemma inj_map_SSup: "inj (map_SSup::('a::complete_lattice downset \<Rightarrow> 'b::complete_lattice downset) \<Rightarrow> ('a \<Rightarrow> 'b))"
  by (metis inj_on_id inj_on_imageI2 map_ds_map_SSup_inv)

lemma map_ds_map_SSup_iff: 
  fixes g :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "(f = map_ds g) = (map_SSup f = g)"
  by (metis inj_eq inj_map_ds map_ds_map_SSup_inv pointfree_idE)

text \<open>This gives an isomorphism between categories.\<close>

lemma surj_map_ds: "surj (map_ds::('a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<Rightarrow> ('a downset \<Rightarrow> 'b downset))"
  by (simp add: map_ds_map_SSup_iff surj_def)

lemma surj_map_SSup: "surj (map_SSup::('a::complete_lattice_with_dual downset \<Rightarrow> 'b::complete_lattice_with_dual downset) \<Rightarrow> ('a \<Rightarrow> 'b))"
  by (metis map_ds_map_SSup_iff surjI)

text \<open>There is of course a dual result for upsets with the reverse inclusion ordering. Once again, it seems impossible to capture 
the "real" duality that uses the inverse image functor.\<close>

typedef (overloaded) 'a upset = "range (\<up>::'a::ord \<Rightarrow> 'a set)"
  by fastforce

setup_lifting type_definition_upset
    
definition us :: "'a::ord \<Rightarrow> 'a upset" where 
  "us = Abs_upset \<circ> \<up>"

definition IInf :: "'a::complete_lattice upset \<Rightarrow> 'a" where
  "IInf = Inf \<circ> Rep_upset"

lemma us_ds: "us = Abs_upset \<circ> (`) \<partial> \<circ> Rep_downset \<circ> ds \<circ> (\<partial>::'a::ord_with_dual \<Rightarrow> 'a)" 
  unfolding us_def ds_def fun_eq_iff comp_def by (simp add: Abs_downset_inverse upset_to_downset2)

lemma IInf_SSup: "IInf = \<partial> \<circ> SSup \<circ> Abs_downset \<circ> (`) (\<partial>::'a::complete_lattice_with_dual \<Rightarrow> 'a) \<circ> Rep_upset"
  unfolding IInf_def SSup_def fun_eq_iff comp_def
  by (metis (no_types, hide_lams) Abs_downset_inverse Rep_upset Sup_dual_def_var image_iff rangeI subset_dual upset_to_downset3)

lemma us_IInf_inv: "us \<circ> IInf = (id::'a::complete_lattice_with_dual upset \<Rightarrow> 'a upset)"
  unfolding us_def IInf_def fun_eq_iff id_def comp_def
  by (metis (no_types, lifting) Inf_upset_id Rep_upset Rep_upset_inverse f_the_inv_into_f pointfree_idE upset_inj)

lemma IInf_us_inv: "IInf \<circ> us = (id::'a::complete_lattice_with_dual \<Rightarrow> 'a)"
  unfolding us_def IInf_def fun_eq_iff id_def comp_def
  by (metis Abs_upset_inverse Sup_Inf_var Sup_atLeastAtMost Sup_dual_upset_var order_refl rangeI)
 
instantiation upset :: (ord) order
begin
  
lift_definition less_eq_upset :: "'a upset \<Rightarrow> 'a upset \<Rightarrow> bool" is "(\<lambda>X Y. Rep_upset X \<supseteq> Rep_upset Y)" .

lift_definition less_upset :: "'a upset \<Rightarrow> 'a upset \<Rightarrow> bool" is "(\<lambda>X Y. Rep_upset X \<supset> Rep_upset Y)" .

instance
  by (intro_classes, transfer, simp_all add: less_le_not_le less_eq_upset.rep_eq Rep_upset_inject)

end
  
lemma us_iso: "x \<le> y \<Longrightarrow> us x \<le> us (y::'a::order_with_dual)"
  by (simp add: Abs_upset_inverse less_eq_upset.rep_eq upset_anti_iff us_def)
 
lemma us_faithful: "us x \<le> us y \<Longrightarrow> x \<le> (y::'a::order_with_dual)"
  by (simp add: Abs_upset_inverse upset_faithful us_def less_eq_upset.rep_eq)

lemma us_inj: "inj (us::'a::order_with_dual \<Rightarrow> 'a upset)"
  unfolding inj_def by (simp add: us_faithful dual_order.antisym)

lemma us_surj: "surj (us::'a::order_with_dual \<Rightarrow> 'a upset)"
  unfolding surj_def by (metis Rep_upset Rep_upset_inverse comp_def image_iff us_def)

lemma us_bij: "bij (us::'a::order_with_dual \<Rightarrow> 'a upset)"
  by (simp add: bij_def us_surj us_inj)

lemma us_ord_iso: "ord_iso (us::'a::order_with_dual \<Rightarrow> 'a upset)"
  unfolding ord_iso_def 
  by (simp, metis (no_types, lifting) UNIV_I f_the_inv_into_f monoI us_iso us_bij us_faithful us_inj us_surj)

definition map_us :: "('a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<Rightarrow> ('a upset \<Rightarrow> 'b upset)" where
  "map_us f = us \<circ> f \<circ> IInf"

lemma map_us_prop: "map_us f \<circ> (us::'a::complete_lattice_with_dual \<Rightarrow> 'a upset) = us \<circ> id f"
  unfolding map_us_def by (simp add: IInf_us_inv comp_assoc) 

definition map_IInf :: "('a upset \<Rightarrow> 'b upset) \<Rightarrow> ('a::complete_lattice \<Rightarrow> 'b::complete_lattice)" where
  "map_IInf F = IInf \<circ> F \<circ> us"

lemma map_IInf_prop: "(us::'a::complete_lattice_with_dual \<Rightarrow> 'a upset) \<circ> map_IInf F = id F \<circ> us"
proof-
  have "us \<circ> map_IInf F = (us \<circ> IInf) \<circ> F \<circ> us"
    by (simp add: fun.map_comp map_IInf_def)
  thus ?thesis
    by (simp add: us_IInf_inv)
qed

lemma map_us_func1: "map_us id = (id::'a::complete_lattice_with_dual upset \<Rightarrow> 'a upset)"
  unfolding map_us_def fun_eq_iff comp_def us_def id_def IInf_def
  by (metis (no_types, lifting) Inf_upset_id Rep_upset Rep_upset_inverse image_iff pointfree_idE)

lemma map_us_func2: 
  fixes f :: "'c::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual"
  and g :: "'a::complete_lattice_with_dual \<Rightarrow> 'c"
  shows "map_us (f \<circ> g) = map_us f \<circ> map_us g"
  unfolding map_us_def fun_eq_iff comp_def us_def IInf_def
  by (metis Abs_upset_inverse Sup_Inf_var Sup_atLeastAtMost Sup_dual_upset_var order_refl rangeI)

lemma map_IInf_func1: "map_IInf id = (id::'a::complete_lattice_with_dual \<Rightarrow> 'a)"
  unfolding map_IInf_def fun_eq_iff comp_def id_def us_def IInf_def by (simp add: Abs_upset_inverse pointfree_idE)

lemma map_IInf_func2: 
  fixes F :: "'c::complete_lattice_with_dual upset \<Rightarrow> 'b::complete_lattice_with_dual upset"
  and G :: "'a::complete_lattice_with_dual upset \<Rightarrow> 'c upset"
  shows "map_IInf (F \<circ> G) = map_IInf F \<circ> map_IInf G"
  unfolding map_IInf_def fun_eq_iff comp_def id_def us_def
  by (metis comp_apply id_apply us_IInf_inv us_def)

lemma map_IInf_map_us_inv: "map_IInf \<circ> map_us = (id::('a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual) \<Rightarrow> ('a \<Rightarrow> 'b))"
  unfolding map_IInf_def map_us_def IInf_def us_def id_def comp_def fun_eq_iff by (simp add: Abs_upset_inverse pointfree_idE)

lemma map_us_map_IInf_inv: "map_us \<circ> map_IInf = (id::('a::complete_lattice_with_dual upset \<Rightarrow> 'b::complete_lattice_with_dual upset) \<Rightarrow> ('a upset \<Rightarrow> 'b upset))"
  unfolding map_IInf_def map_us_def IInf_def us_def id_def comp_def fun_eq_iff
  by (metis (no_types, lifting) Inf_upset_id Rep_upset Rep_upset_inverse image_iff pointfree_idE)

lemma inj_map_us: "inj (map_us::('a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual) \<Rightarrow> ('a upset \<Rightarrow> 'b upset))"
  unfolding map_us_def us_def IInf_def inj_def comp_def fun_eq_iff
  by (metis (no_types, hide_lams) Abs_upset_inverse Inf_upset_id pointfree_idE rangeI)

lemma inj_map_IInf: "inj (map_IInf::('a::complete_lattice_with_dual upset \<Rightarrow> 'b::complete_lattice_with_dual upset) \<Rightarrow> ('a \<Rightarrow> 'b))"
  unfolding map_IInf_def fun_eq_iff inj_def comp_def IInf_def us_def
  by (metis (no_types, hide_lams) Inf_upset_id Rep_upset Rep_upset_inverse image_iff pointfree_idE)

lemma map_us_map_IInf_iff: 
  fixes g :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual" 
  shows "(f = map_us g) = (map_IInf f = g)"
  by (metis inj_eq inj_map_us map_us_map_IInf_inv pointfree_idE)

lemma map_us_mono_pres: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual"
  shows "mono f \<Longrightarrow> mono (map_us f)"
  unfolding mono_def map_us_def comp_def us_def IInf_def
  by (metis Abs_upset_inverse Inf_superset_mono less_eq_upset.rep_eq rangeI upset_anti_iff)

lemma map_IInf_mono_pres: 
  fixes F :: "'a::complete_lattice_with_dual upset \<Rightarrow> 'b::complete_lattice_with_dual upset"
  shows "mono F \<Longrightarrow> mono (map_IInf F)"
  unfolding mono_def map_IInf_def comp_def us_def IInf_def
  oops 

lemma surj_map_us: "surj (map_us::('a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual) \<Rightarrow> ('a upset \<Rightarrow> 'b upset))"
  by (simp add: map_us_map_IInf_iff surj_def)

lemma surj_map_IInf: "surj (map_IInf::('a::complete_lattice_with_dual upset \<Rightarrow> 'b::complete_lattice_with_dual upset) \<Rightarrow> ('a \<Rightarrow> 'b))"
  by (metis map_us_map_IInf_iff surjI)

text \<open>Hence we have again an isomorphism --- or rather equivalence --- between categories. Here, however, duality is not consistently picked up.\<close>


subsection \<open>Stone's Theorem in the Presence of Atoms\<close>

text \<open>Atom-map is a boolean algebra morphism.\<close>

context boolean_algebra
begin

lemma atom_map_compl_pres: "atom_map (-x) = Collect atom - atom_map x"
proof-
  {fix y
  have "(y \<in> atom_map (-x)) = (atom y \<and> y \<le> -x)"
    by (simp add: atom_map_def)
  also have "... = (atom y \<and> \<not>(y \<le> x))"
    by (metis atom_sup_iff inf.orderE meet_shunt sup_compl_top top.ordering_top_axioms ordering_top.extremum)
   also have "... = (y \<in> Collect atom - atom_map x)"
     using atom_map_def by auto
   finally have "(y \<in> atom_map (-x)) = (y \<in> Collect atom - atom_map x)".}
  thus ?thesis
    by blast
qed

lemma atom_map_sup_pres: "atom_map (x \<squnion> y) = atom_map x \<union> atom_map y"
proof-
  {fix z
  have "(z \<in> atom_map (x \<squnion> y)) = (atom z \<and> z \<le> x \<squnion> y)"
    by (simp add: atom_map_def)
  also have "... = (atom z \<and> (z \<le> x \<or> z \<le> y))"
    using atom_sup_iff by auto
  also have "... = (z \<in> atom_map x \<union> atom_map y)"
    using atom_map_def by auto
  finally have "(z \<in> atom_map (x \<squnion> y)) = (z \<in> atom_map x \<union> atom_map y)"
    by blast}
  thus ?thesis
    by blast
qed

lemma atom_map_inf_pres: "atom_map (x \<sqinter> y) = atom_map x \<inter> atom_map y"
  by (smt Diff_Un atom_map_compl_pres atom_map_sup_pres compl_inf double_compl)

lemma atom_map_minus_pres: "atom_map (x - y) = atom_map x - atom_map y"
  using atom_map_compl_pres atom_map_def diff_eq by auto

end

text \<open>The homomorphic images of boolean algebras under atom-map are boolean algebras 
--- in fact powerset boolean algebras.\<close>

instantiation atoms :: (boolean_algebra) boolean_algebra
begin

lift_definition minus_atoms :: "'a atoms \<Rightarrow> 'a atoms \<Rightarrow> 'a atoms" is "\<lambda>x y. Abs_atoms (Rep_atoms x - Rep_atoms y)".

lift_definition uminus_atoms :: "'a atoms \<Rightarrow> 'a atoms" is  "\<lambda>x. Abs_atoms (Collect atom - Rep_atoms x)".

lift_definition bot_atoms :: "'a atoms" is "Abs_atoms {}".

lift_definition sup_atoms ::  "'a atoms \<Rightarrow> 'a atoms \<Rightarrow> 'a atoms" is "\<lambda>x y. Abs_atoms (Rep_atoms x \<union> Rep_atoms y)".

lift_definition top_atoms :: "'a atoms" is "Abs_atoms (Collect atom)".

lift_definition inf_atoms ::  "'a atoms \<Rightarrow> 'a atoms \<Rightarrow> 'a atoms" is "\<lambda>x y. Abs_atoms (Rep_atoms x \<inter> Rep_atoms y)".

lift_definition less_eq_atoms :: "'a atoms \<Rightarrow> 'a atoms \<Rightarrow> bool" is "(\<lambda>x y. Rep_atoms x \<subseteq> Rep_atoms y)".

lift_definition less_atoms :: "'a atoms \<Rightarrow> 'a atoms \<Rightarrow> bool" is "(\<lambda>x y. Rep_atoms x \<subset> Rep_atoms y)".

instance
  apply intro_classes
                 apply (transfer, simp add: less_le_not_le)
                apply (transfer, simp)
               apply (transfer, blast)
              apply (simp add: Rep_atoms_inject less_eq_atoms.abs_eq)
             apply (transfer, smt Abs_atoms_inverse Rep_atoms atom_map_inf_pres image_iff inf_le1 rangeI)
            apply (transfer, smt Abs_atoms_inverse Rep_atoms atom_map_inf_pres image_iff inf_le2 rangeI)
           apply (transfer, smt Abs_atoms_inverse Rep_atoms atom_map_inf_pres image_iff le_iff_sup rangeI sup_inf_distrib1)
          apply (transfer, smt Abs_atoms_inverse Rep_atoms atom_map_sup_pres image_iff image_iff inf.orderE inf_sup_aci(6) le_iff_sup order_refl rangeI rangeI)
         apply (transfer, smt Abs_atoms_inverse Rep_atoms atom_map_sup_pres image_iff inf_sup_aci(6) le_iff_sup rangeI sup.left_commute sup.right_idem)
        apply (transfer, subst Abs_atoms_inverse, metis (no_types, lifting) Rep_atoms atom_map_sup_pres image_iff rangeI, simp)
       apply transfer using Abs_atoms_inverse atom_map_bot_pres apply blast
      apply (transfer, metis Abs_atoms_inverse Rep_atoms atom_map_compl_pres atom_map_top_pres diff_eq double_compl inf_le1 rangeE rangeI)
     apply (transfer, smt Abs_atoms_inverse Rep_atoms atom_map_inf_pres atom_map_sup_pres image_iff rangeI sup_inf_distrib1)
    apply (transfer, metis (no_types, hide_lams) Abs_atoms_inverse Diff_disjoint Rep_atoms atom_map_compl_pres rangeE rangeI)
   apply (transfer, smt Abs_atoms_inverse uminus_atoms.abs_eq Rep_atoms Un_Diff_cancel atom_map_compl_pres atom_map_inf_pres atom_map_minus_pres atom_map_sup_pres atom_map_top_pres diff_eq double_compl inf_compl_bot_right rangeE rangeI sup_commute sup_compl_top)
  by transfer (smt Abs_atoms_inverse Rep_atoms atom_map_compl_pres atom_map_inf_pres atom_map_minus_pres diff_eq rangeE rangeI)

end

text \<open>The homomorphism atom-map can then be restricted in its output type to the powerset boolean algebra.\<close>

lemma at_map_bot_pres: "at_map \<bottom> = \<bottom>"
  by (simp add: at_map_def atom_map_bot_pres bot_atoms.transfer)

lemma at_map_top_pres: "at_map \<top> = \<top>"
  by (simp add: at_map_def atom_map_top_pres top_atoms.transfer)

lemma at_map_compl_pres: "at_map \<circ> uminus = uminus \<circ> at_map"
  unfolding fun_eq_iff by (simp add: Abs_atoms_inverse at_map_def atom_map_compl_pres uminus_atoms.abs_eq)

lemma at_map_sup_pres: "at_map (x \<squnion> y) = at_map x \<squnion> at_map y"
  unfolding at_map_def comp_def by (metis (mono_tags, lifting) Abs_atoms_inverse atom_map_sup_pres rangeI sup_atoms.transfer)

lemma at_map_inf_pres: "at_map (x \<sqinter> y) = at_map x \<sqinter> at_map y"
  unfolding at_map_def comp_def by (metis (mono_tags, lifting) Abs_atoms_inverse atom_map_inf_pres inf_atoms.transfer rangeI)

lemma at_map_minus_pres: "at_map (x - y) = at_map x - at_map y"
  unfolding at_map_def comp_def by (simp add: Abs_atoms_inverse atom_map_minus_pres minus_atoms.abs_eq)


context atomic_boolean_algebra
begin

text \<open>In atomic boolean algebras, atom-map is an embedding that maps atoms of the boolean algebra to 
those of the powerset boolean algebra. Analogous properties hold for at-map.\<close>

lemma inj_atom_map: "inj atom_map"
proof-
  {fix x y ::'a
    assume "x \<noteq> y"
  hence "x \<sqinter> -y \<noteq> \<bottom> \<or> -x \<sqinter> y \<noteq> \<bottom>"
    by (auto simp: meet_shunt) 
  hence "\<exists>z. atom z \<and> (z \<le> x \<sqinter> -y \<or> z \<le> -x \<sqinter> y)"
    using atomicity by blast
  hence "\<exists>z. atom z \<and> ((z \<in> atom_map x \<and> \<not>(z \<in> atom_map y)) \<or> (\<not>(z \<in> atom_map x) \<and> z \<in> atom_map y))"
    unfolding atom_def atom_map_def by (clarsimp, metis diff_eq inf.orderE meet_shunt_var)
  hence "atom_map x \<noteq> atom_map y"
    by blast}
  thus ?thesis
    by (meson injI)
qed

lemma atom_map_atom_pres: "atom x \<Longrightarrow> atom_map x = {x}"
  unfolding atom_def atom_map_def by (auto simp: bot_less dual_order.order_iff_strict)

lemma atom_map_atom_pres2: "atom x \<Longrightarrow> atom (atom_map x)"
proof-
  assume "atom x"
  hence "atom_map x = {x}"
    by (simp add: atom_map_atom_pres)
  thus "atom (atom_map x)"
    using bounded_lattice_class.atom_def by auto
qed

end

lemma inj_at_map: "inj (at_map::'a::atomic_boolean_algebra \<Rightarrow> 'a atoms)"
  unfolding at_map_def comp_def by (metis (no_types, lifting) Abs_atoms_inverse inj_atom_map inj_def rangeI)

lemma at_map_atom_pres: "atom (x::'a::atomic_boolean_algebra) \<Longrightarrow> at_map x = Abs_atoms {x}"
  unfolding at_map_def comp_def by (simp add: atom_map_atom_pres)

lemma at_map_atom_pres2: "atom (x::'a::atomic_boolean_algebra) \<Longrightarrow> atom (at_map x)"
  unfolding at_map_def comp_def
  by (metis Abs_atoms_inverse atom_def atom_map_atom_pres2 atom_map_bot_pres bot_atoms.abs_eq less_atoms.abs_eq rangeI)

text \<open>Homomorphic images of atomic boolean algebras under atom-map are therefore atomic (rather obviously).\<close>

instance atoms :: (atomic_boolean_algebra) atomic_boolean_algebra
proof intro_classes
  fix x::"'a atoms"
  assume "x \<noteq> \<bottom>"
  hence "\<exists>y. x = at_map y \<and> x \<noteq> \<bottom>"
    unfolding at_map_def comp_def by (metis Abs_atoms_cases rangeE)
  hence "\<exists>y. x = at_map y \<and> (\<exists>z. atom z \<and> z \<le> y)"
    using at_map_bot_pres atomicity by force
  hence "\<exists>y. x = at_map y \<and> (\<exists>z. atom (at_map z) \<and> at_map z \<le> at_map y)"
    by (metis at_map_atom_pres2 at_map_sup_pres sup.orderE sup_ge2)
  thus "\<exists>y. atom y \<and> y \<le> x"
    by fastforce
qed

context complete_boolean_algebra_alt
begin

text \<open>In complete boolean algebras, atom-map is surjective; more precisely it is the left inverse
of Sup, at least for sets of atoms. Below, this statement is made more explicit for at-map.\<close>

lemma surj_atom_map: "Y \<subseteq> Collect atom \<Longrightarrow> Y = atom_map (\<Squnion>Y)"
proof
  assume "Y \<subseteq> Collect atom"
  thus "Y \<subseteq> atom_map (\<Squnion>Y)"
    using Sup_upper atom_map_def by force
next
  assume "Y \<subseteq> Collect atom"
  hence a: "\<forall>y. y \<in> Y \<longrightarrow> atom y"
    by blast
  {fix z
  assume h: "z \<in> Collect atom - Y"
  hence "\<forall>y \<in> Y. y \<sqinter> z = \<bottom>"
    by (metis DiffE a h atom_def dual_order.not_eq_order_implies_strict inf.absorb_iff2 inf_le2 meet_shunt mem_Collect_eq)
  hence "\<Squnion>Y \<sqinter> z = \<bottom>"
    using Sup_least meet_shunt by simp
  hence "z \<notin> atom_map (\<Squnion>Y)"
    using atom_map_bot_pres atom_map_def by force}
  thus  "atom_map (\<Squnion>Y) \<subseteq> Y"
    using atom_map_def by force
qed

text \<open>In this setting, atom-map is a complete boolean algebra morphism.\<close>

lemma atom_map_Sup_pres: "atom_map (\<Squnion>X) = (\<Union>x \<in> X. atom_map x)"
proof-
  {fix z
  have "(z \<in> atom_map (\<Squnion>X)) = (atom z \<and> z \<le> \<Squnion>X)"
    by (simp add: atom_map_def)
  also have "... = (atom z \<and> (\<exists>x \<in> X. z \<le> x))"
    using atom_Sup_iff by auto
  also have "... = (z \<in> (\<Union>x \<in> X. atom_map x))"
    using atom_map_def by auto
  finally have "(z \<in> atom_map (\<Squnion>X)) = (z \<in> (\<Union>x \<in> X. atom_map x))"
    by blast}
  thus ?thesis
    by blast
qed

lemma atom_map_Sup_pres_var: "atom_map \<circ> Sup = Sup \<circ> (`) atom_map"
  unfolding fun_eq_iff comp_def by (simp add: atom_map_Sup_pres) 

text \<open>For Inf-preservation, it is important that Infs are restricted to homomorphic images; 
hence they need to be pushed into the set of all atoms.\<close>

lemma atom_map_Inf_pres: "atom_map (\<Sqinter>X) = Collect atom \<inter> (\<Inter>x \<in> X. atom_map x)"
proof-
  have "atom_map (\<Sqinter>X) = atom_map (-(\<Squnion>x \<in> X. -x))"
    by (smt Collect_cong SUP_le_iff atom_map_def compl_le_compl_iff compl_le_swap1 le_Inf_iff)
  also have "... = Collect atom - atom_map (\<Squnion>x \<in> X. -x)"
    using atom_map_compl_pres by blast
  also have "... = Collect atom - (\<Union>x \<in> X. atom_map (-x))"  
    by (simp add: atom_map_Sup_pres)
  also have "... = Collect atom - (\<Union>x \<in> X. Collect atom - atom_map (x))" 
    using atom_map_compl_pres by blast
  also have "... = Collect atom \<inter> (\<Inter>x \<in> X. atom_map x)"
    by blast
  finally show ?thesis.
qed

end

text \<open>It follows that homomorphic images of complete boolean algebras under atom-map form
complete boolean algebras.\<close>

instantiation atoms :: (complete_boolean_algebra_alt) complete_boolean_algebra_alt
begin

lift_definition Inf_atoms :: "'a::complete_boolean_algebra_alt atoms set \<Rightarrow> 'a::complete_boolean_algebra_alt atoms" is "\<lambda>X. Abs_atoms (Collect atom \<inter> Inter ((`) Rep_atoms X))".

lift_definition  Sup_atoms :: "'a::complete_boolean_algebra_alt atoms set \<Rightarrow> 'a::complete_boolean_algebra_alt atoms" is "\<lambda>X. Abs_atoms (Union ((`) Rep_atoms X))".

instance
  apply (intro_classes; transfer)
       apply (metis (no_types, hide_lams) Abs_atoms_inverse image_iff inf_le1 le_Inf_iff le_infI2 order_refl rangeI surj_atom_map)
      apply (metis (no_types, lifting) Abs_atoms_inverse Int_subset_iff Rep_atoms Sup_upper atom_map_atoms inf_le1 le_INF_iff rangeI surj_atom_map)
     apply (metis Abs_atoms_inverse Rep_atoms SUP_least SUP_upper Sup_upper atom_map_atoms rangeI surj_atom_map)
    apply (metis Abs_atoms_inverse Rep_atoms SUP_least Sup_upper atom_map_atoms rangeI surj_atom_map)
  by simp_all

end

text \<open>Once more, properties proved above can now be restricted to at-map.\<close>

lemma  surj_at_map_var: "at_map \<circ> Sup \<circ> Rep_atoms = (id::'a::complete_boolean_algebra_alt atoms \<Rightarrow> 'a atoms)"
  unfolding at_map_def comp_def fun_eq_iff id_def by (metis Rep_atoms Rep_atoms_inverse Sup_upper atom_map_atoms surj_atom_map)

lemma surj_at_map: "surj (at_map::'a::complete_boolean_algebra_alt \<Rightarrow> 'a atoms)"
  unfolding surj_def at_map_def comp_def by (metis Rep_atoms Rep_atoms_inverse image_iff)

lemma at_map_Sup_pres: "at_map \<circ> Sup = Sup \<circ> (`) (at_map::'a::complete_boolean_algebra_alt \<Rightarrow> 'a atoms)"
  unfolding fun_eq_iff at_map_def comp_def atom_map_Sup_pres by (smt Abs_atoms_inverse Sup.SUP_cong Sup_atoms.transfer UN_extend_simps(10) rangeI)

lemma at_map_Sup_pres_var: "at_map (\<Squnion>X) = (\<Squnion>(x::'a::complete_boolean_algebra_alt) \<in> X. (at_map x))"
  using at_map_Sup_pres comp_eq_elim by blast

lemma at_map_Inf_pres: "at_map (\<Sqinter>X) = Abs_atoms (Collect atom \<sqinter> (\<Sqinter>x \<in> X. (Rep_atoms (at_map (x::'a::complete_boolean_algebra_alt)))))"
  unfolding at_map_def comp_def by (metis (no_types, lifting) Abs_atoms_inverse Sup.SUP_cong atom_map_Inf_pres rangeI)

lemma at_map_Inf_pres_var: "at_map \<circ> Inf = Inf \<circ> (`) (at_map::'a::complete_boolean_algebra_alt \<Rightarrow> 'a atoms)"
  unfolding fun_eq_iff comp_def by (metis Inf_atoms.abs_eq at_map_Inf_pres image_image)

text \<open>Finally, on complete atomic boolean algebras (CABAs), at-map is an isomorphism, that is, a bijection 
that preserves the complete boolean algebra operations. Thus every CABA is isomorphic to a powerset boolean algebra
and every powerset boolean algebra is a CABA. The bijective pair is given by at-map and Sup (defined on the powerset algebra).
This theorem is a little version of Stone's theorem. In the general case, ultrafilters play the role of atoms.\<close>

lemma "Sup \<circ> atom_map = (id::'a::complete_atomic_boolean_algebra \<Rightarrow> 'a)"
  unfolding fun_eq_iff comp_def id_def
  by (metis Union_upper atom_map_atoms inj_atom_map inj_def rangeI surj_atom_map)

lemma inj_at_map_var: "Sup \<circ> Rep_atoms \<circ> at_map  = (id ::'a::complete_atomic_boolean_algebra \<Rightarrow> 'a)"

  unfolding at_map_def comp_def fun_eq_iff id_def
  by (metis Abs_atoms_inverse Union_upper atom_map_atoms inj_atom_map inj_def rangeI surj_atom_map)

lemma bij_at_map: "bij (at_map::'a::complete_atomic_boolean_algebra \<Rightarrow> 'a atoms)"
  unfolding bij_def by (simp add: inj_at_map surj_at_map)

instance atoms :: (complete_atomic_boolean_algebra) complete_atomic_boolean_algebra..

text \<open>A full consideration of Stone duality is left for future work.\<close>

(* Failed attempt to prove Tarski's fixpoint theorem: The problem is that we want to use mono, but this has two type parameters. It doesn't work inside of the one-type-parameter typedef.
Yet isotonicity is needed to prove inhabitance of the type. I could develop a theory of isotone endos and prove the existence of 
lfps and gfps, duplicating the more general facts for mono. But that's not the point. Because of this I see no direct way of proving
Tarski's fixpoint theorem. Any way out?

class complete_lattice_with_iso = complete_lattice +
  fixes f :: "'a \<Rightarrow> 'a"
(*  assumes isof: "x \<le> y \<Longrightarrow> f x \<le> f y"*)

typedef (overloaded) 'a Fix = "Fix (f::'a::complete_lattice_with_iso \<Rightarrow> 'a)" 


setup_lifting type_definition_Fix

*)

end





