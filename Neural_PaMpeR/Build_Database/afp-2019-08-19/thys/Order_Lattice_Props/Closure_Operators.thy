(* 
  Title: Closure and Co-Closure Operators
  Author: Georg Struth 
  Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Closure and Co-Closure Operators\<close>

theory Closure_Operators
  imports Galois_Connections 

begin

subsection \<open>Closure Operators\<close>

text \<open>Closure and coclosure operators in orders and complete lattices are defined in this section,
and some basic properties are proved. Isabelle infers the appropriate types. Facts are 
taken mainly from the Compendium of Continuous Lattices~\cite{GierzHKLMS80} and 
Rosenthal's book on quantales~\cite{Rosenthal90}.\<close>

definition clop :: "('a::order \<Rightarrow> 'a) \<Rightarrow> bool" where
  "clop f = (id \<le> f \<and> mono f \<and> f \<circ> f \<le> f)"

lemma clop_extensive: "clop f \<Longrightarrow> id \<le> f"
  by (simp add: clop_def)

lemma clop_extensive_var: "clop f \<Longrightarrow> x \<le> f x"
  by (simp add: clop_def le_fun_def)

lemma clop_iso: "clop f \<Longrightarrow> mono f"
  by (simp add: clop_def)

lemma clop_iso_var: "clop f \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  by (simp add: clop_def mono_def)

lemma clop_idem: "clop f \<Longrightarrow> f \<circ> f = f"
  by (simp add: antisym clop_def le_fun_def)

lemma clop_Fix_range: "clop f \<Longrightarrow> (Fix f = range f)"
  by (simp add: clop_idem retraction_prop_fix)

lemma clop_idem_var: "clop f \<Longrightarrow> f (f x) = f x"
  by (simp add: clop_idem retraction_prop)

lemma clop_Inf_closed_var: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a" 
  shows "clop f \<Longrightarrow> f \<circ> Inf \<circ> (`) f  = Inf \<circ> (`) f"    
  unfolding clop_def mono_def comp_def le_fun_def 
  by (metis (mono_tags, lifting) antisym id_apply le_INF_iff order_refl)

lemma clop_top:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "clop f \<Longrightarrow> f \<top> = \<top>"
  by (simp add: clop_extensive_var top.extremum_uniqueI)

lemma "clop (f::'a::complete_lattice \<Rightarrow> 'a) \<Longrightarrow> f (\<Squnion>x \<in> X. f x) = (\<Squnion>x \<in> X. f x)" (*nitpick*)
  oops

lemma "clop (f::'a::complete_lattice \<Rightarrow> 'a) \<Longrightarrow> f (f x \<squnion> f y) = f x \<squnion> f y" (*nitpick*)
  oops

lemma  "clop (f::'a::complete_lattice \<Rightarrow> 'a) \<Longrightarrow> f \<bottom> = \<bottom>" (*nitpick *)
  oops
  
lemma "clop (f::'a set \<Rightarrow> 'a set) \<Longrightarrow> f (\<Squnion>x \<in> X. f x) = (\<Squnion>x \<in> X. f x)" (*nitpick*)
  oops

lemma "clop (f::'a set \<Rightarrow> 'a set) \<Longrightarrow> f (f x \<squnion> f y) = f x \<squnion> f y" (*nitpick*)
  oops

lemma  "clop (f::'a set \<Rightarrow> 'a set) \<Longrightarrow> f \<bottom> = \<bottom>" (*nitpick *)
  oops

lemma clop_closure: "clop f \<Longrightarrow> (x \<in> range f) = (f x = x)"
  by (simp add: clop_idem retraction_prop)

lemma clop_closure_set: "clop f \<Longrightarrow> range f = Fix f"
  by (simp add: clop_Fix_range)

lemma clop_closure_prop: "(clop::('a::complete_lattice_with_dual\<Rightarrow> 'a) \<Rightarrow> bool) (Inf \<circ> \<up>)"
  by (simp add: clop_def mono_def)

lemma clop_closure_prop_var: "clop (\<lambda>x::'a::complete_lattice. \<Sqinter>{y. x \<le> y})"
  unfolding clop_def comp_def le_fun_def mono_def by (simp add: Inf_lower le_Inf_iff)

lemma clop_alt: "(clop f) = (\<forall>x y. x \<le> f y \<longleftrightarrow> f x \<le> f y)"
  unfolding clop_def mono_def le_fun_def comp_def id_def by (meson dual_order.refl order_trans)

text \<open>Finally it is shown that adjoints in a Galois connection yield closure operators.\<close>

lemma clop_adj: 
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> clop (g \<circ> f)"
  by (simp add: adj_cancel2 adj_idem2 adj_iso4 clop_def)

text \<open>Closure operators are monads for posets, and monads arise from adjunctions. 
This fact is not formalised at this point. But here is the first step: every function 
can be decomposed into a surjection followed by an injection.\<close>

definition "surj_on f Y = (\<forall>y \<in> Y. \<exists>x. y = f x)"

lemma surj_surj_on: "surj f \<Longrightarrow> surj_on f Y"
  by (simp add: surjD surj_on_def)

lemma fun_surj_inj: "\<exists>g h. f = g \<circ> h \<and> surj_on h (range f) \<and> inj_on g (range f)"
proof-
  obtain h where a: "\<forall>x. f x = h x"
    by blast
  then have "surj_on h (range f)"
    by (metis (mono_tags, lifting) imageE surj_on_def)
  then show ?thesis
    unfolding inj_on_def surj_on_def fun_eq_iff using a by auto
qed

text \<open>Connections between downsets, upsets and closure operators are outlined next.\<close>

lemma preorder_clop: "clop (\<Down>::'a::preorder set \<Rightarrow> 'a set)"
  by (simp add: clop_def downset_set_ext downset_set_iso)

lemma clop_preorder_aux: "clop f \<Longrightarrow> (x \<in> f {y} \<longleftrightarrow> f {x} \<subseteq> f {y})"
  by (simp add: clop_alt)

lemma clop_preorder: "clop f \<Longrightarrow> class.preorder (\<lambda>x y. f {x} \<subseteq> f {y}) (\<lambda>x y. f {x} \<subset> f {y})"
  unfolding clop_def mono_def le_fun_def id_def comp_def by standard (auto simp: subset_not_subset_eq)

lemma preorder_clop_dual: "clop (\<Up>::'a::preorder_with_dual set \<Rightarrow> 'a set)"
  by (simp add: clop_def upset_set_anti upset_set_ext)

text \<open>The closed elements of any closure operator over a complete lattice form an Inf-closed set (a Moore family).\<close>

lemma clop_Inf_closed: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows  "clop f \<Longrightarrow> Inf_closed_set (Fix f)" 
  unfolding clop_def Inf_closed_set_def mono_def le_fun_def comp_def id_def Fix_def
  by (smt Inf_greatest Inf_lower antisym mem_Collect_eq subsetCE)

lemma clop_top_Fix: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows  "clop f \<Longrightarrow> \<top> \<in> Fix f"
  by (simp add: clop_Fix_range clop_closure clop_top)


text \<open>Conversely, every Inf-closed subset of a complete lattice is the set of fixpoints of some closure operator.\<close>
 
lemma Inf_closed_clop: 
  fixes X :: "'a::complete_lattice set"
  shows "Inf_closed_set X \<Longrightarrow> clop (\<lambda>y. \<Sqinter>{x \<in> X. y \<le> x})"
  by (smt Collect_mono_iff Inf_superset_mono clop_alt dual_order.trans le_Inf_iff mem_Collect_eq)

lemma Inf_closed_clop_var: 
  fixes X :: "'a::complete_lattice set"
  shows "clop f \<Longrightarrow> \<forall>x \<in> X. x \<in> range f \<Longrightarrow> \<Sqinter>X \<in> range f"
  by (metis Inf_closed_set_def clop_Fix_range clop_Inf_closed subsetI)

text \<open>It is well known that downsets and upsets over an ordering form subalgebras of the complete powerset lattice.\<close>

typedef (overloaded) 'a downsets = "range (\<Down>::'a::order set \<Rightarrow> 'a set)"
  by fastforce

setup_lifting type_definition_downsets

typedef (overloaded) 'a upsets = "range (\<Up>::'a::order set \<Rightarrow> 'a set)"
  by fastforce

setup_lifting type_definition_upsets

instantiation downsets :: (order) Inf_lattice
begin

lift_definition Inf_downsets :: "'a downsets set \<Rightarrow> 'a downsets" is "Abs_downsets \<circ> Inf \<circ> (`) Rep_downsets".
  
lift_definition less_eq_downsets :: "'a downsets \<Rightarrow> 'a downsets \<Rightarrow> bool" is "\<lambda>X Y. Rep_downsets X \<subseteq> Rep_downsets Y".

lift_definition less_downsets :: "'a downsets \<Rightarrow> 'a downsets \<Rightarrow> bool" is "\<lambda>X Y. Rep_downsets X \<subset> Rep_downsets Y".

instance
  apply intro_classes 
      apply (transfer, simp)
     apply (transfer, blast)
    apply (simp add: Closure_Operators.less_eq_downsets.abs_eq Rep_downsets_inject)
   apply (transfer, smt Abs_downsets_inverse INF_lower Inf_closed_clop_var Rep_downsets image_iff o_def preorder_clop)
  by transfer (smt comp_def Abs_downsets_inverse Inf_closed_clop_var Rep_downsets image_iff le_INF_iff preorder_clop)

end

instantiation upsets :: (order_with_dual) Inf_lattice
begin

lift_definition Inf_upsets :: "'a upsets set \<Rightarrow> 'a upsets" is "Abs_upsets \<circ> Inf \<circ> (`) Rep_upsets".
  
lift_definition less_eq_upsets :: "'a upsets \<Rightarrow> 'a upsets \<Rightarrow> bool" is "\<lambda>X Y. Rep_upsets X \<subseteq> Rep_upsets Y".

lift_definition less_upsets :: "'a upsets \<Rightarrow> 'a upsets \<Rightarrow> bool" is "\<lambda>X Y. Rep_upsets X \<subset> Rep_upsets Y".

instance
  apply intro_classes
      apply (transfer, simp)
     apply (transfer, blast)
    apply (simp add: Closure_Operators.less_eq_upsets.abs_eq Rep_upsets_inject)
   apply (transfer, smt Abs_upsets_inverse Inf_closed_clop_var Inf_lower Rep_upsets comp_apply image_iff preorder_clop_dual)
  by transfer (smt comp_def Abs_upsets_inverse Inf_closed_clop_var Inter_iff Rep_upsets image_iff preorder_clop_dual subsetCE subsetI)

end

text \<open>It has already been shown in the section on representations that the map ds, which maps elements of the order to its downset, is an order 
embedding. However, the duality between the underlying ordering and the lattices of up- and down-closed sets as categories can probably not be expressed, 
as there is no easy access to contravariant functors. \<close>


subsection \<open>Co-Closure Operators\<close>
                                
text \<open>Next, the co-closure (or kernel) operation satisfies dual laws.\<close>

definition coclop :: "('a::order \<Rightarrow> 'a::order) \<Rightarrow> bool" where
  "coclop f = (f \<le> id \<and> mono f \<and> f \<le> f \<circ> f)"

lemma coclop_dual: "(coclop::('a::order_with_dual \<Rightarrow> 'a) \<Rightarrow> bool) = clop \<circ> \<partial>\<^sub>F"
  unfolding coclop_def clop_def id_def mono_def map_dual_def comp_def fun_eq_iff le_fun_def
  by (metis invol_dual_var ord_dual)

lemma coclop_dual_var: 
  fixes f :: "'a::order_with_dual \<Rightarrow> 'a"
  shows "coclop f = clop (\<partial>\<^sub>F f)"
  by (simp add: coclop_dual)

lemma clop_dual: "(clop::('a::order_with_dual \<Rightarrow> 'a) \<Rightarrow> bool) = coclop \<circ> \<partial>\<^sub>F"
  by (simp add: coclop_dual comp_assoc map_dual_invol)

lemma clop_dual_var: 
  fixes f :: "'a::order_with_dual \<Rightarrow> 'a"
  shows "clop f = coclop (\<partial>\<^sub>F f)"
  by (simp add: clop_dual)

lemma coclop_coextensive: "coclop f \<Longrightarrow> f \<le> id"
  by (simp add: coclop_def)

lemma coclop_coextensive_var: "coclop f \<Longrightarrow> f x \<le> x"
  using coclop_def le_funD by fastforce

lemma coclop_iso: "coclop f \<Longrightarrow> mono f"
  by (simp add: coclop_def)

lemma coclop_iso_var: "coclop f \<Longrightarrow> (x \<le> y \<longrightarrow> f x \<le> f y)"
  by (simp add: coclop_iso monoD)

lemma coclop_idem: "coclop f \<Longrightarrow> f \<circ> f = f"
  by (simp add: antisym coclop_def le_fun_def)

lemma coclop_closure: "coclop f \<Longrightarrow> (x \<in> range f) = (f x = x)"
  by (simp add: coclop_idem retraction_prop)

lemma coclop_Fix_range: "coclop f \<Longrightarrow> (Fix f = range f)"
  by (simp add: coclop_idem retraction_prop_fix)

lemma coclop_idem_var: "coclop f \<Longrightarrow> f (f x) = f x"
  by (simp add: coclop_idem retraction_prop)

lemma coclop_Sup_closed_var: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'a"
  shows "coclop f \<Longrightarrow> f \<circ> Sup \<circ> (`) f  = Sup \<circ> (`) f"
  unfolding coclop_def mono_def comp_def le_fun_def 
  by (metis (mono_tags, lifting) SUP_le_iff antisym id_apply order_refl)

lemma Sup_closed_coclop_var: 
  fixes X :: "'a::complete_lattice set"
  shows "coclop f \<Longrightarrow> \<forall>x \<in> X. x \<in> range f \<Longrightarrow> \<Squnion>X \<in> range f"
  by (smt Inf.INF_id_eq Sup.SUP_cong antisym coclop_closure coclop_coextensive_var coclop_iso id_apply mono_SUP)

lemma coclop_bot: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'a"
  shows "coclop f \<Longrightarrow> f \<bottom> = \<bottom>"
  by (simp add: bot.extremum_uniqueI coclop_coextensive_var)

lemma "coclop (f::'a::complete_lattice \<Rightarrow> 'a) \<Longrightarrow> f (\<Sqinter>x \<in> X. f x) = (\<Sqinter>x \<in> X. f x)" (*nitpick*)
  oops

lemma "coclop (f::'a::complete_lattice \<Rightarrow> 'a) \<Longrightarrow> f (f x \<sqinter> f y) = f x \<sqinter> f y" (*nitpick*)
  oops

lemma  "coclop (f::'a::complete_lattice \<Rightarrow> 'a) \<Longrightarrow> f \<top> = \<top>" (*nitpick*) 
  oops
  
lemma "coclop (f::'a set \<Rightarrow> 'a set) \<Longrightarrow> f (\<Sqinter>x \<in> X. f x) = (\<Sqinter>x \<in> X. f x)" (*nitpick*)
  oops

lemma "coclop (f::'a set \<Rightarrow> 'a set) \<Longrightarrow> f (f x \<sqinter> f y) = f x \<sqinter> f y" (*nitpick*)
  oops

lemma  "coclop (f::'a set \<Rightarrow> 'a set) \<Longrightarrow> f \<top> = \<top>" (*nitpick *)
  oops

lemma coclop_coclosure: "coclop f \<Longrightarrow> f x = x \<longleftrightarrow> x \<in> range f"
 by (simp add: coclop_idem retraction_prop)
                                              
lemma coclop_coclosure_set: "coclop f \<Longrightarrow> range f = Fix f"
  by (simp add: coclop_idem retraction_prop_fix)

lemma coclop_coclosure_prop: "(coclop::('a::complete_lattice \<Rightarrow> 'a) \<Rightarrow> bool) (Sup \<circ> \<down>)"
  by (simp add: coclop_def mono_def)

lemma coclop_coclosure_prop_var: "coclop (\<lambda>x::'a::complete_lattice. \<Squnion>{y. y \<le> x})"
  by (metis (mono_tags, lifting) Sup_atMost atMost_def coclop_def comp_apply eq_id_iff eq_refl mono_def)

lemma coclop_alt: "(coclop f) = (\<forall>x y. f x \<le> y \<longleftrightarrow> f x \<le> f y)"
  unfolding coclop_def mono_def le_fun_def comp_def id_def
  by (meson dual_order.refl order_trans)

lemma coclop_adj: 
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> coclop (f \<circ> g)"
  by (simp add: adj_cancel1 adj_idem1 adj_iso3 coclop_def)

text \<open>Finally, a subset of a complete lattice is Sup-closed if and only if it is the set of fixpoints
of some co-closure operator.\<close>

lemma coclop_Sup_closed: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows  "coclop f \<Longrightarrow> Sup_closed_set (Fix f)"
  unfolding coclop_def Sup_closed_set_def mono_def le_fun_def comp_def id_def Fix_def
  by (smt Sup_least Sup_upper antisym_conv mem_Collect_eq subsetCE)

lemma Sup_closed_coclop: 
  fixes X :: "'a::complete_lattice set"
  shows "Sup_closed_set X \<Longrightarrow> coclop (\<lambda>y. \<Squnion>{x \<in> X. x \<le> y})"
  unfolding Sup_closed_set_def coclop_def mono_def le_fun_def comp_def
  apply safe
  apply (metis (no_types, lifting) Sup_least eq_id_iff mem_Collect_eq)
  apply (smt Collect_mono_iff Sup_subset_mono dual_order.trans)
  by (simp add: Collect_mono_iff Sup_subset_mono Sup_upper)


subsection \<open>Complete Lattices of Closed Elements\<close>

text \<open>The machinery developed allows showing that the closed elements in a complete
lattice (with respect to some closure operation) form themselves a complete lattice.\<close>

class cl_op = ord +
  fixes cl_op :: "'a \<Rightarrow> 'a"
  assumes clop_ext: "x \<le> cl_op x"
  and clop_iso: "x \<le> y \<Longrightarrow> cl_op x \<le> cl_op y"
  and clop_wtrans: "cl_op (cl_op x) \<le> cl_op x"

class clattice_with_clop = complete_lattice + cl_op

begin

lemma clop_cl_op: "clop cl_op"
  unfolding clop_def le_fun_def comp_def
  by (simp add: cl_op_class.clop_ext cl_op_class.clop_iso cl_op_class.clop_wtrans order_class.mono_def)

lemma clop_idem [simp]: "cl_op \<circ> cl_op = cl_op"
  using clop_ext clop_wtrans order.antisym by auto

lemma clop_idem_var [simp]: "cl_op (cl_op x) = cl_op x"
  by (simp add: antisym clop_ext clop_wtrans)

lemma clop_range_Fix: "range cl_op = Fix cl_op"
  by (simp add: retraction_prop_fix)

lemma Inf_closed_cl_op_var: 
  fixes X :: "'a set"
  shows "\<forall>x \<in> X. x \<in> range cl_op \<Longrightarrow> \<Sqinter>X \<in> range cl_op"
proof-
  assume h: "\<forall>x \<in> X. x \<in> range cl_op"
  hence "\<forall>x \<in> X. cl_op x = x"
    by (simp add: retraction_prop)
  hence "cl_op (\<Sqinter>X) = \<Sqinter>X"
    by (metis Inf_lower clop_ext clop_iso dual_order.antisym le_Inf_iff)
  thus ?thesis
    by (metis rangeI)
qed

lemma inf_closed_cl_op_var: "x \<in> range cl_op \<Longrightarrow> y \<in> range cl_op \<Longrightarrow> x \<sqinter> y \<in> range cl_op"
  by (smt Inf_closed_cl_op_var UnI1 insert_iff insert_is_Un inf_Inf)

end

typedef (overloaded) 'a::clattice_with_clop cl_op_im = "range (cl_op::'a \<Rightarrow> 'a)"
  by force

setup_lifting type_definition_cl_op_im

lemma cl_op_prop [iff]: "(cl_op (x \<squnion> y) = cl_op y) = (cl_op (x::'a::clattice_with_clop) \<le> cl_op y)"
  by (smt cl_op_class.clop_iso clop_ext clop_wtrans inf_sup_ord(4) le_iff_sup sup.absorb_iff1 sup_left_commute)

lemma cl_op_prop_var [iff]: "(cl_op (x \<squnion> cl_op y) = cl_op y) = (cl_op (x::'a::clattice_with_clop) \<le> cl_op y)"
  by (metis cl_op_prop clattice_with_clop_class.clop_idem_var)

instantiation cl_op_im :: (clattice_with_clop) complete_lattice
begin

lift_definition Inf_cl_op_im :: "'a cl_op_im set \<Rightarrow> 'a cl_op_im" is Inf
  by (simp add: Inf_closed_cl_op_var)
 
lift_definition Sup_cl_op_im :: "'a cl_op_im set \<Rightarrow> 'a cl_op_im" is "\<lambda>X. cl_op (\<Squnion>X)"
  by simp

lift_definition inf_cl_op_im :: "'a cl_op_im \<Rightarrow> 'a cl_op_im \<Rightarrow> 'a cl_op_im" is inf
  by (simp add: inf_closed_cl_op_var)

lift_definition sup_cl_op_im :: "'a cl_op_im \<Rightarrow> 'a cl_op_im \<Rightarrow> 'a cl_op_im" is "\<lambda>x y. cl_op (x \<squnion> y)"
  by simp

lift_definition less_eq_cl_op_im :: "'a cl_op_im \<Rightarrow> 'a cl_op_im \<Rightarrow> bool" is "(\<le>)".

lift_definition less_cl_op_im :: "'a cl_op_im \<Rightarrow> 'a cl_op_im \<Rightarrow> bool" is "(<)".

lift_definition bot_cl_op_im :: "'a cl_op_im" is "cl_op \<bottom>"
  by simp

lift_definition top_cl_op_im :: "'a cl_op_im" is "\<top>"
  by (simp add: clop_cl_op clop_closure clop_top)


instance
  apply (intro_classes; transfer)
                 apply (simp_all add: less_le_not_le Inf_lower Inf_greatest)
      apply (meson clop_cl_op clop_extensive_var dual_order.trans inf_sup_ord(3))
     apply (meson clop_cl_op clop_extensive_var dual_order.trans sup_ge2)
    apply (metis cl_op_class.clop_iso clop_cl_op clop_closure le_sup_iff)
   apply (meson Sup_upper clop_cl_op clop_extensive_var dual_order.trans)
  by (metis Sup_le_iff cl_op_class.clop_iso clop_cl_op clop_closure)

end

text \<open>This statement is perhaps less useful as it might seem, because it is difficult to make it cooperate with concrete closure operators, 
which one would not generally like to define within a type class. Alternatively, a sublocale statement could perhaps be given. It would also 
have been nice to prove this statement for Sup-lattices---this would have cut down the number of proof obligations significantly.
But this would require a tighter integration of these structures. A similar statement could have been proved for co-closure operators. But this would
not lead to new insights.\<close>

text \<open>Next I show that for every surjective Sup-preserving function between complete lattices there is a closure operator 
such that the set of closed elements is isomorphic to the range of the surjection.\<close>

lemma surj_Sup_pres_id:
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual"
  assumes "surj f"
  and "Sup_pres f" 
  shows "f \<circ> (radj f) = id"
proof-
  have "f \<stileturn> (radj f)"
    using Sup_pres_ladj assms(2) radj_adj by auto
  thus ?thesis
    using adj_sur_inv assms(1) by blast
qed

lemma surj_Sup_pres_inj:
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual"
  assumes "surj f"
  and "Sup_pres f" 
  shows "inj (radj f)"
  by (metis assms comp_eq_dest_lhs id_apply injI surj_Sup_pres_id)

lemma surj_Sup_pres_inj_on: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual"
  assumes "surj f"
  and "Sup_pres f" 
  shows "inj_on f (range (radj f \<circ> f))"
  by (smt Sup_pres_ladj_aux adj_idem2 assms(2) comp_apply inj_on_def retraction_prop)

lemma surj_Sup_pres_bij_on: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual"
  assumes "surj f"
  and "Sup_pres f" 
  shows "bij_betw f (range (radj f \<circ> f)) UNIV"
  unfolding bij_betw_def
  apply safe
    apply (simp add: assms(1) assms(2) surj_Sup_pres_inj_on cong del: image_cong_simp)
   apply auto
  apply (metis (mono_tags) UNIV_I assms(1) assms(2) comp_apply id_apply image_image surj_Sup_pres_id surj_def)
  done

text \<open>Thus the restriction of $f$ to the set of closed elements is indeed a bijection. The final fact
shows that it preserves Sups of closed elements, and hence is an isomorphism of complete lattices.\<close>

lemma surj_Sup_pres_iso: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual"
  assumes "surj f"
  and "Sup_pres f" 
  shows "f ((radj f \<circ> f) (\<Squnion>X)) = (\<Squnion>x \<in> X. f x)"
  by (metis assms(1) assms(2) comp_def pointfree_idE surj_Sup_pres_id)


subsection \<open>A Quick Example: Dedekind-MacNeille Completions\<close>

text \<open>I only outline the basic construction. Additional facts about join density, and that the completion yields 
the least complete lattice that contains all Sups and Infs of the underlying posets, are left for future consideration.\<close>

abbreviation "dm \<equiv> lb_set \<circ> ub_set"

lemma up_set_prop: "(X::'a::preorder set) \<noteq> {} \<Longrightarrow> ub_set X = \<Inter>{\<up>x |x. x \<in> X}"
  unfolding ub_set_def upset_def upset_set_def by (safe, simp_all, blast)

lemma lb_set_prop: "(X::'a::preorder set) \<noteq> {} \<Longrightarrow> lb_set X = \<Inter>{\<down>x |x. x \<in> X}"
  unfolding lb_set_def downset_def downset_set_def by (safe, simp_all, blast)

lemma dm_downset_var: "dm {x} = \<down>(x::'a::preorder)"
  unfolding lb_set_def ub_set_def downset_def downset_set_def 
  by (clarsimp, meson order_refl order_trans)

lemma dm_downset: "dm \<circ> \<eta> = (\<down>::'a::preorder \<Rightarrow> 'a set)"
  using dm_downset_var fun.map_cong by fastforce

lemma dm_inj: "inj ((dm::'a::order set \<Rightarrow> 'a set) \<circ> \<eta>)"
  by (simp add: dm_downset downset_inj)

lemma "clop (lb_set \<circ> ub_set)"
  unfolding clop_def lb_set_def ub_set_def
  apply safe
  unfolding le_fun_def comp_def id_def mono_def
  by auto

end

