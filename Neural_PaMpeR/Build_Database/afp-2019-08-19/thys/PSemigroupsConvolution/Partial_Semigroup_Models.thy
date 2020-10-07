(* Title: Models of Partial Semigroups
   Author: Brijesh Dongol, Victor Gomes, Ian J Hayes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Models of Partial Semigroups\<close>

theory Partial_Semigroup_Models
  imports Partial_Semigroups
    
begin
  
text \<open>So far this section collects three models that we need for applications. Other interesting models might be
added in the future. These might include binary relations, formal power series and matrices, paths in graphs under fusion, 
program traces with alternating state and action symbols under fusion, partial orders under series and parallel products.\<close>
  
subsection \<open>Partial Monoids of Segments and Intervals\<close>
  
text \<open>Segments of a partial order are sub partial orders between two points. Segments generalise
intervals in that intervals are segments in linear orders. We formalise segments and intervals as pairs, 
where the first coordinate is smaller than the second one. Algebras of segments and intervals are interesting 
in Rota's work on the foundations of combinatorics as well as for interval logics and duration calculi.\<close>
    
text \<open>First we define the subtype of ordered pairs of one single type.\<close>

typedef 'a dprod = "{(x::'a, y::'a). True}" 
  by simp

setup_lifting type_definition_dprod
  
text \<open>Such pairs form partial semigroups and partial monoids with respect to fusion.\<close>
  
instantiation dprod :: (type) partial_semigroup
begin 

lift_definition D_dprod :: "'a dprod \<Rightarrow> 'a dprod \<Rightarrow> bool" is "\<lambda>x y. (snd x = fst y)" .

lift_definition times_dprod :: "'a dprod \<Rightarrow> 'a dprod \<Rightarrow> 'a dprod" is "\<lambda>x y. (fst x, snd y)"
  by simp

instance 
  by standard (transfer, force)+

end 

instantiation "dprod" :: (type) partial_monoid
begin 

lift_definition E_dprod :: "'a dprod set" is "{x. fst x = snd x}" 
  by simp

instance 
  by standard (transfer,force)+

end 
  
text \<open>Next we define the type of segments.\<close>
  
typedef (overloaded) 'a segment = "{x::('a::order \<times> 'a::order). fst x \<le> snd x}"
  by force

setup_lifting type_definition_segment
  
text \<open>Segments form partial monoids as well.\<close>
  
instantiation segment :: (order) partial_monoid
begin

lift_definition E_segment :: "'a segment set" is "{x. fst x = snd x}"
  by simp 

lift_definition D_segment :: "'a::order segment \<Rightarrow> 'a segment \<Rightarrow> bool" 
  is "\<lambda>x y. (snd x = fst y)" .
    
lift_definition times_segment :: "'a::order segment \<Rightarrow> 'a segment \<Rightarrow> 'a segment" 
  is "\<lambda>x y. if snd x = fst y then (fst x, snd y) else x"
  by auto

instance 
  by standard (transfer, force)+
 
end
  
text \<open>Next we define the function segm that maps segments-as-pairs to segments-as-sets.\<close>
  
definition segm :: "'a::order segment \<Rightarrow> 'a set" where 
  "segm x = {y. fst (Rep_segment x) \<le> y \<and> y \<le> snd (Rep_segment x)}"
  
  thm Rep_segment

lemma segm_sub_morph: "snd (Rep_segment x) = fst (Rep_segment y) \<Longrightarrow> segm x \<union> segm y \<le> segm (x \<cdot> y)"
  apply (simp add: segm_def times_segment.rep_eq, safe)
  using Rep_segment dual_order.trans apply blast
  by (metis (mono_tags, lifting) Rep_segment dual_order.trans mem_Collect_eq)

text \<open>The function segm is not generally a morphism.\<close>
  
lemma "snd (Rep_segment x) = fst (Rep_segment y) \<Longrightarrow> segm x \<union> segm y = segm (x \<cdot> y)" (* nitpick [expect=genuine] *)
oops

text \<open>Intervals are segments over orders that satisfy Halpern and Shoham's  linear order property. This 
is still more general than linearity of the poset.\<close>

class lip_order = order +
  assumes lip: "x \<le> y \<Longrightarrow> (\<forall>v w. (x \<le> v \<and> v \<le> y \<and> x \<le> w \<and> w \<le> y \<longrightarrow> v \<le> w \<or> w \<le> v))"
    
text \<open>The function segm is now a morphism.\<close>
  
lemma segm_morph: "snd (Rep_segment x::('a::lip_order \<times> 'a::lip_order)) = fst (Rep_segment y) 
    \<Longrightarrow> segm x \<union> segm y = segm (x \<cdot> y)"
  apply (simp add: segm_def times_segment_def)
  apply (transfer, clarsimp simp add: Abs_segment_inverse lip, safe)
  apply force+
  by (meson lip order_trans)
    
    
subsection \<open>Cancellative PAM's of Partial Functions\<close>

text \<open>We show that partial functions under disjoint union form a positive cancellative PAM. 
This is interesting for modeling the heap in separation logic.\<close>

type_synonym 'a pfun = "'a \<Rightarrow> 'a option"

definition ortho :: "'a pfun \<Rightarrow> 'a pfun \<Rightarrow> bool"
  where "ortho f g \<equiv> dom f \<inter> dom g = {}"

lemma pfun_comm: "ortho x y \<Longrightarrow> x ++ y = y ++ x"
  by (force simp: ortho_def intro!: map_add_comm)

lemma pfun_canc: "ortho z x \<Longrightarrow> ortho z y \<Longrightarrow> z ++ x = z ++ y \<Longrightarrow> x = y"
  apply (auto simp: ortho_def map_add_def option.case_eq_if fun_eq_iff)
  by (metis domIff dom_restrict option.collapse restrict_map_def)

interpretation pfun: positive_cancellative_pam_one map_add ortho "{Map.empty}" Map.empty
  apply (standard, auto simp: ortho_def pfun_canc)
  by (simp_all add: inf_commute map_add_comm ortho_def pfun_canc)
    
subsection \<open>PAM's of Disjoint Unions of Sets\<close>
  
text \<open>This simple disjoint union construction underlies important compositions of graphs or partial orders,
in particular in the context of complete joins and disjoint unions of graphs and of series and parallel products
of partial orders.\<close>

instantiation set :: (type) pas
begin  

definition D_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "D_set x y \<equiv> x \<inter> y = {}"

definition times_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "times_set x y = x \<union> y"

instance
  by standard (auto simp: D_set_def times_set_def)

end

instantiation set :: (type) pam
begin 

definition E_set :: "'a set set" where
  "E_set = {{}}"

instance
  by standard (auto simp: D_set_def times_set_def E_set_def)

end
    
end


