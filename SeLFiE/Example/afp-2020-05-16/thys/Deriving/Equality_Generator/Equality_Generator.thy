(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
section \<open>Checking Equality Without "="\<close>

theory Equality_Generator
imports
  "../Generator_Aux"
  "../Derive_Manager"
begin

typedecl ('a,'b,'c,'z)type

text \<open>In the following, we define a generator which for a given datatype @{typ "('a,'b,'c,'z)type"}
  constructs an equality-test function of type 
  @{typ "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('z \<Rightarrow> 'z \<Rightarrow> bool) \<Rightarrow> 
    (('a,'b,'c,'z)type \<Rightarrow> ('a,'b,'c,'z)type \<Rightarrow> bool)"}.
  These functions are essential to synthesize conditional equality functions in the container framework,
  where a strict membership in the @{class equal}-class must not be enforced.
\<close>

hide_type "type"

text \<open>Just a constant to define conjunction on lists of booleans, which will
  be used to merge the results when having compared the arguments of identical
  constructors.\<close>

definition list_all_eq :: "bool list \<Rightarrow> bool" where
  "list_all_eq = list_all id "

subsection \<open>Improved Code for Non-Lazy Languages\<close>

text \<open>The following equations will eliminate all occurrences of @{term list_all_eq}
  in the generated code of the equality functions.\<close>

lemma list_all_eq_unfold: 
  "list_all_eq [] = True"
  "list_all_eq [b] = b"
  "list_all_eq (b1 # b2 # bs) = (b1 \<and> list_all_eq (b2 # bs))"
  unfolding list_all_eq_def
  by auto

lemma list_all_eq: "list_all_eq bs \<longleftrightarrow> (\<forall> b \<in> set bs. b)" 
  unfolding list_all_eq_def list_all_iff by auto  

subsection \<open>Partial Equality Property\<close>

text \<open>We require a partial property which can be used in inductive proofs.\<close>

type_synonym 'a equality = "'a \<Rightarrow> 'a \<Rightarrow> bool"

definition pequality :: "'a equality \<Rightarrow> 'a \<Rightarrow> bool"
where
  "pequality aeq x \<longleftrightarrow> (\<forall> y. aeq x y \<longleftrightarrow> x = y)"

lemma pequalityD: "pequality aeq x \<Longrightarrow> aeq x y \<longleftrightarrow> x = y"
  unfolding pequality_def by auto

lemma pequalityI: "(\<And> y. aeq x y \<longleftrightarrow> x = y) \<Longrightarrow> pequality aeq x"
  unfolding pequality_def by auto


subsection \<open>Global equality property\<close>

definition equality :: "'a equality \<Rightarrow> bool" where
  "equality aeq \<longleftrightarrow> (\<forall> x. pequality aeq x)"

lemma equalityD2: "equality aeq \<Longrightarrow> pequality aeq x"
  unfolding equality_def by blast

lemma equalityI2: "(\<And> x. pequality aeq x) \<Longrightarrow> equality aeq" 
  unfolding equality_def by blast
    
lemma equalityD: "equality aeq \<Longrightarrow> aeq x y \<longleftrightarrow> x = y"
  by (rule pequalityD[OF equalityD2])

lemma equalityI: "(\<And> x y. aeq x y \<longleftrightarrow> x = y) \<Longrightarrow> equality aeq"
  by (intro equalityI2 pequalityI)

lemma equality_imp_eq:
  "equality aeq \<Longrightarrow> aeq = (=)" 
  by (intro ext, auto dest: equalityD)

lemma eq_equality: "equality (=)"
  by (rule equalityI, simp)

lemma equality_def': "equality f = (f = (=))" 
  using equality_imp_eq eq_equality by blast


subsection \<open>The Generator\<close>

ML_file \<open>equality_generator.ML\<close>

hide_fact (open) equalityI

end
