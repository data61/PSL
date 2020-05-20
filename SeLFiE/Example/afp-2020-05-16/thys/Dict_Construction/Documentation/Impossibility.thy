subsection \<open>Impossibility of hiding sort constraints\<close>
text_raw \<open>\label{sec:impossibility}\<close>

text \<open>Coauthor of this section: Florian Haftmann\<close>

theory Impossibility
imports Main
begin

axiomatization of_prop :: "prop \<Rightarrow> bool" where
of_prop_Trueprop [simp]: "of_prop (Trueprop P) \<longleftrightarrow> P" and
Trueprop_of_prop [simp]: "Trueprop (of_prop Q) \<equiv> PROP Q"

text \<open>A type satisfies the certificate if there is an instance of the class.\<close>

definition is_sg :: "'a itself \<Rightarrow> bool" where
"is_sg TYPE('a) = of_prop OFCLASS('a, semigroup_add_class)"

text \<open>We trick the parser into ignoring the sort constraint of @{const plus}.\<close>

setup \<open>Sign.add_const_constraint (@{const_name plus}, SOME @{typ "'a::{} => 'a \<Rightarrow> 'a"})\<close>

definition sg :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
"sg plus \<longleftrightarrow> plus = Groups.plus \<and> is_sg TYPE('a)" for plus

text \<open>Attempt: Define a type that contains all legal @{const plus} functions.\<close>

typedef (overloaded) 'a Sg = "Collect sg :: ('a \<Rightarrow> 'a \<Rightarrow> 'a) set"
  morphisms the_plus Sg
  unfolding sg_def[abs_def]
  apply (simp add: is_sg_def)

text \<open>We need to prove @{term "OFCLASS('a, semigroup_add_class)"} for arbitrary @{typ 'a}, which is
impossible.\<close>

oops

end
