(* Title:      Subalgebras of Kleene Relation Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Subalgebras of Kleene Relation Algebras\<close>

text \<open>
In this theory we show that the regular elements of a Stone-Kleene relation algebra form a Kleene relation subalgebra.
\<close>

theory Kleene_Relation_Subalgebras

imports Stone_Relation_Algebras.Relation_Subalgebras Kleene_Relation_Algebras

begin

instantiation regular :: (stone_kleene_relation_algebra) kleene_relation_algebra
begin

lift_definition star_regular :: "'a regular \<Rightarrow> 'a regular" is star
  using regular_closed_p regular_closed_star by blast

instance
  apply intro_classes
  apply (metis (mono_tags, lifting) star_regular.rep_eq less_eq_regular.rep_eq left_kleene_algebra_class.star_left_unfold one_regular.rep_eq simp_regular sup_regular.rep_eq times_regular.rep_eq)
  apply (metis (mono_tags, lifting) less_eq_regular.rep_eq left_kleene_algebra_class.star_left_induct simp_regular star_regular.rep_eq sup_regular.rep_eq times_regular.rep_eq)
  apply (metis (mono_tags, lifting) less_eq_regular.rep_eq strong_left_kleene_algebra_class.star_right_induct simp_regular star_regular.rep_eq sup_regular.rep_eq times_regular.rep_eq)
  by simp

end

end

