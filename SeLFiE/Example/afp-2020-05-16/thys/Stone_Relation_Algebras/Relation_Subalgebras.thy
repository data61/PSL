(* Title:      Subalgebras of Relation Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Subalgebras of Relation Algebras\<close>

text \<open>
In this theory we consider the algebraic structure of regular elements, coreflexives, vectors and covectors in Stone relation algebras.
These elements form important subalgebras and substructures of relation algebras.
\<close>

theory Relation_Subalgebras

imports Stone_Algebras.Stone_Construction Relation_Algebras

begin

text \<open>
The regular elements of a Stone relation algebra form a relation subalgebra.
\<close>

instantiation regular :: (stone_relation_algebra) relation_algebra
begin

lift_definition times_regular :: "'a regular \<Rightarrow> 'a regular \<Rightarrow> 'a regular" is times
  using regular_mult_closed regular_closed_p by blast

lift_definition conv_regular :: "'a regular \<Rightarrow> 'a regular" is conv
  using conv_complement by blast

lift_definition one_regular :: "'a regular" is 1
  using regular_one_closed by blast

instance
  apply intro_classes
  apply (metis (mono_tags, lifting) times_regular.rep_eq Rep_regular_inject comp_associative)
  apply (metis (mono_tags, lifting) times_regular.rep_eq Rep_regular_inject mult_right_dist_sup sup_regular.rep_eq)
  apply (metis (mono_tags, lifting) times_regular.rep_eq Rep_regular_inject bot_regular.rep_eq semiring.mult_zero_left)
  apply (simp add: one_regular.rep_eq times_regular.rep_eq Rep_regular_inject[THEN sym])
  using Rep_regular_inject conv_regular.rep_eq apply force
  apply (metis (mono_tags, lifting) Rep_regular_inject conv_dist_sup conv_regular.rep_eq sup_regular.rep_eq)
  apply (metis (mono_tags, lifting) conv_regular.rep_eq times_regular.rep_eq Rep_regular_inject conv_dist_comp)
  by (auto simp add: conv_regular.rep_eq dedekind_1 inf_regular.rep_eq less_eq_regular.rep_eq times_regular.rep_eq)

end

text \<open>
The coreflexives (tests) in an idempotent semiring form a bounded idempotent subsemiring.
\<close>

typedef (overloaded) 'a coreflexive = "coreflexives::'a::non_associative_left_semiring set"
  by auto

lemma simp_coreflexive [simp]:
  "\<exists>y . Rep_coreflexive x \<le> 1"
  using Rep_coreflexive by simp

setup_lifting type_definition_coreflexive

instantiation coreflexive :: (idempotent_semiring) bounded_idempotent_semiring
begin

lift_definition sup_coreflexive :: "'a coreflexive \<Rightarrow> 'a coreflexive \<Rightarrow> 'a coreflexive" is sup
  by simp

lift_definition times_coreflexive :: "'a coreflexive \<Rightarrow> 'a coreflexive \<Rightarrow> 'a coreflexive" is times
  by (simp add: coreflexive_mult_closed)

lift_definition bot_coreflexive :: "'a coreflexive" is bot
  by simp

lift_definition one_coreflexive :: "'a coreflexive" is 1
  by simp

lift_definition top_coreflexive :: "'a coreflexive" is 1
  by simp

lift_definition less_eq_coreflexive :: "'a coreflexive \<Rightarrow> 'a coreflexive \<Rightarrow> bool" is less_eq .

lift_definition less_coreflexive :: "'a coreflexive \<Rightarrow> 'a coreflexive \<Rightarrow> bool" is less .

instance
  apply intro_classes
  apply (simp_all add: less_coreflexive.rep_eq less_eq_coreflexive.rep_eq less_le_not_le)[2]
  apply (meson less_eq_coreflexive.rep_eq order_trans)
  apply (simp_all add: Rep_coreflexive_inject bot_coreflexive.rep_eq less_eq_coreflexive.rep_eq sup_coreflexive.rep_eq)[5]
  apply (simp add: semiring.distrib_left less_eq_coreflexive.rep_eq sup_coreflexive.rep_eq times_coreflexive.rep_eq)
  apply (metis (mono_tags, lifting) sup_coreflexive.rep_eq times_coreflexive.rep_eq Rep_coreflexive_inject mult_right_dist_sup)
  apply (simp add: times_coreflexive.rep_eq bot_coreflexive.rep_eq Rep_coreflexive_inject[THEN sym])
  apply (simp add: one_coreflexive.rep_eq times_coreflexive.rep_eq Rep_coreflexive_inject[THEN sym])
  apply (simp add: one_coreflexive.rep_eq less_eq_coreflexive.rep_eq times_coreflexive.rep_eq)
  apply (simp only: sup_coreflexive.rep_eq top_coreflexive.rep_eq Rep_coreflexive_inject[THEN sym], metis Abs_coreflexive_cases Abs_coreflexive_inverse mem_Collect_eq sup.absorb2)
  apply (simp add: less_eq_coreflexive.rep_eq mult.assoc times_coreflexive.rep_eq)
  apply (metis (mono_tags, lifting) times_coreflexive.rep_eq Rep_coreflexive_inject mult.assoc)
  using Rep_coreflexive_inject one_coreflexive.rep_eq times_coreflexive.rep_eq apply fastforce
  apply (metis (mono_tags, lifting) sup_coreflexive.rep_eq times_coreflexive.rep_eq Rep_coreflexive_inject mult_left_dist_sup)
  by (simp add: times_coreflexive.rep_eq bot_coreflexive.rep_eq Rep_coreflexive_inject[THEN sym])

end

text \<open>
The coreflexives (tests) in a Stone relation algebra form a Stone relation algebra where the pseudocomplement is taken relative to the identity relation and converse is the identity function.
\<close>

instantiation coreflexive :: (stone_relation_algebra) stone_relation_algebra
begin

lift_definition inf_coreflexive :: "'a coreflexive \<Rightarrow> 'a coreflexive \<Rightarrow> 'a coreflexive" is inf
  by (simp add: le_infI1)

lift_definition minus_coreflexive :: "'a coreflexive \<Rightarrow> 'a coreflexive \<Rightarrow> 'a coreflexive" is "\<lambda>x y . x \<sqinter> -y"
  by (simp add: le_infI1)

lift_definition uminus_coreflexive :: "'a coreflexive \<Rightarrow> 'a coreflexive" is "\<lambda>x . -x \<sqinter> 1"
  by simp

lift_definition conv_coreflexive :: "'a coreflexive \<Rightarrow> 'a coreflexive" is id
  by simp

instance
  apply intro_classes
  apply (auto simp: inf_coreflexive.rep_eq less_eq_coreflexive.rep_eq)[3]
  apply simp
  apply (metis (mono_tags, lifting) Rep_coreflexive_inject inf_coreflexive.rep_eq sup_coreflexive.rep_eq sup_inf_distrib1)
  apply (metis (mono_tags, lifting) Rep_coreflexive_inject bot_coreflexive.rep_eq top_greatest coreflexive_pseudo_complement inf_coreflexive.rep_eq less_eq_coreflexive.rep_eq one_coreflexive.rep_eq one_coreflexive_def top_coreflexive_def uminus_coreflexive.rep_eq)
  apply (metis (mono_tags, lifting) Rep_coreflexive_inject maddux_3_21_pp one_coreflexive.rep_eq one_coreflexive_def pp_dist_inf pp_one regular_closed_p sup_coreflexive.rep_eq sup_right_top top_coreflexive_def uminus_coreflexive.rep_eq)
  apply (auto simp: mult.assoc mult_right_dist_sup)[4]
  using Rep_coreflexive_inject conv_coreflexive.rep_eq apply fastforce
  apply (metis (mono_tags) Rep_coreflexive_inject conv_coreflexive.rep_eq)
  apply (metis (mono_tags, lifting) Rep_coreflexive_inject top_greatest conv_coreflexive.rep_eq coreflexive_commutative less_eq_coreflexive.rep_eq one_coreflexive.rep_eq one_coreflexive_def times_coreflexive.rep_eq top_coreflexive_def)
  apply (simp only: conv_coreflexive.rep_eq less_eq_coreflexive.rep_eq one_coreflexive.rep_eq times_coreflexive.rep_eq inf_coreflexive.rep_eq Rep_coreflexive_inject[THEN sym], metis coreflexive_dedekind Rep_coreflexive mem_Collect_eq)
  apply (metis (mono_tags, lifting) Rep_coreflexive Rep_coreflexive_inject coreflexive_pp_dist_comp mem_Collect_eq times_coreflexive.rep_eq uminus_coreflexive.rep_eq)
  by (metis (mono_tags, hide_lams) Rep_coreflexive_inverse inf.commute inf.idem inf_import_p one_coreflexive.rep_eq pp_one uminus_coreflexive.rep_eq)

end

text \<open>
Vectors in a Stone relation algebra form a Stone subalgebra.
\<close>

typedef (overloaded) 'a vector = "vectors::'a::bounded_pre_left_semiring set"
  using surjective_top_closed by blast

lemma simp_vector [simp]:
  "\<exists>y . Rep_vector x * top = Rep_vector x"
  using Rep_vector by simp

setup_lifting type_definition_vector

instantiation vector :: (stone_relation_algebra) stone_algebra
begin

lift_definition sup_vector :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> 'a vector" is sup
  by (simp add: vector_sup_closed)

lift_definition inf_vector :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> 'a vector" is inf
  by (simp add: vector_inf_closed)

lift_definition uminus_vector :: "'a vector \<Rightarrow> 'a vector" is uminus
  by (simp add: vector_complement_closed)

lift_definition bot_vector :: "'a vector" is bot
  by simp

lift_definition top_vector :: "'a vector" is top
  by simp

lift_definition less_eq_vector :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> bool" is less_eq .

lift_definition less_vector :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> bool" is less .

instance
  apply intro_classes
  apply (auto simp: Rep_vector_inject top_vector.rep_eq bot_vector.rep_eq less_le_not_le inf_vector.rep_eq sup_vector.rep_eq less_eq_vector.rep_eq less_vector.rep_eq)[12]
  apply (metis (mono_tags, lifting) Rep_vector_inject inf_vector.rep_eq sup_inf_distrib1 sup_vector.rep_eq)
  apply (metis (mono_tags, lifting) Rep_vector_inject bot_vector_def bot_vector.rep_eq pseudo_complement inf_vector.rep_eq less_eq_vector.rep_eq uminus_vector.rep_eq)
  by (metis (mono_tags, lifting) sup_vector.rep_eq uminus_vector.rep_eq Rep_vector_inverse stone top_vector.abs_eq)

end

text \<open>
Covectors in a Stone relation algebra form a Stone subalgebra.
\<close>

typedef (overloaded) 'a covector = "covectors::'a::bounded_pre_left_semiring set"
  using surjective_top_closed by blast

lemma simp_covector [simp]:
  "\<exists>y . top * Rep_covector x = Rep_covector x"
  using Rep_covector by simp

setup_lifting type_definition_covector

instantiation covector :: (stone_relation_algebra) stone_algebra
begin

lift_definition sup_covector :: "'a covector \<Rightarrow> 'a covector \<Rightarrow> 'a covector" is sup
  by (simp add: covector_sup_closed)

lift_definition inf_covector :: "'a covector \<Rightarrow> 'a covector \<Rightarrow> 'a covector" is inf
  by (simp add: covector_inf_closed)

lift_definition uminus_covector :: "'a covector \<Rightarrow> 'a covector" is uminus
  by (simp add: covector_complement_closed)

lift_definition bot_covector :: "'a covector" is bot
  by simp

lift_definition top_covector :: "'a covector" is top
  by simp

lift_definition less_eq_covector :: "'a covector \<Rightarrow> 'a covector \<Rightarrow> bool" is less_eq .

lift_definition less_covector :: "'a covector \<Rightarrow> 'a covector \<Rightarrow> bool" is less .

instance
  apply intro_classes
  apply (auto simp: Rep_covector_inject less_eq_covector.rep_eq inf_covector.rep_eq bot_covector.rep_eq top_covector.rep_eq sup_covector.rep_eq less_le_not_le less_covector.rep_eq)[12]
  apply (metis (mono_tags, lifting) Rep_covector_inject inf_covector.rep_eq sup_inf_distrib1 sup_covector.rep_eq)
  apply (metis (mono_tags, lifting) Rep_covector_inject bot_covector_def bot_covector.rep_eq pseudo_complement inf_covector.rep_eq less_eq_covector.rep_eq uminus_covector.rep_eq)
  by (metis (mono_tags, lifting) sup_covector.rep_eq uminus_covector.rep_eq Rep_covector_inverse stone top_covector.abs_eq)

end

end

