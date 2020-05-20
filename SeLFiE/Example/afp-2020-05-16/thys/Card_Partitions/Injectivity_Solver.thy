(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Combinatorial Basics\<close>

theory Injectivity_Solver
imports
  "HOL-Library.Disjoint_Sets"
  "HOL-Library.Monad_Syntax"
  "HOL-Eisbach.Eisbach"
begin

subsection \<open>Preliminaries\<close>

text \<open>
These lemmas shall be added to the Disjoint Set theory.
\<close>

subsubsection \<open>Injectivity and Disjoint Families\<close>

lemma inj_on_impl_disjoint_family_on_singleton:
  assumes "inj_on f A"
  shows "disjoint_family_on (\<lambda>x. {f x}) A"
using assms disjoint_family_on_def inj_on_contraD by fastforce

subsubsection \<open>Cardinality Theorems for Set.bind\<close>

lemma card_bind:
  assumes "finite S"
  assumes "\<forall>X \<in> S. finite (f X)"
  assumes "disjoint_family_on f S"
  shows "card (S \<bind> f) = (\<Sum>x\<in>S. card (f x))"
proof -
  have "card (S \<bind> f) = card (\<Union>(f ` S))"
    by (simp add: bind_UNION)
  also have "card (\<Union>(f ` S)) = (\<Sum>x\<in>S. card (f x))"
    using assms unfolding disjoint_family_on_def by (simp add: card_UN_disjoint)
  finally show ?thesis .
qed

lemma card_bind_constant:
  assumes "finite S"
  assumes "\<forall>X \<in> S. finite (f X)"
  assumes "disjoint_family_on f S"
  assumes "\<And>x. x \<in> S \<Longrightarrow> card (f x) = k"
  shows "card (S \<bind> f) = card S * k"
using assms by (simp add: card_bind)

lemma card_bind_singleton:
  assumes "finite S"
  assumes "inj_on f S"
  shows "card (S \<bind> (\<lambda>x. {f x})) = card S"
using assms by (auto simp add: card_bind_constant inj_on_impl_disjoint_family_on_singleton)

subsection \<open>Third Version of Injectivity Solver\<close>

text \<open>
Here, we provide a third version of the injectivity solver. The original first version was provided
in the AFP entry `Spivey's Generalized Recurrence for Bell Numbers`. From that method, I derived a
second version in the AFP entry `Cardinality of Equivalence Relations`. At roughly the same time,
Makarius improved the injectivity solver in the development version of the first AFP entry. This
third version now includes the improvements of the second version and Makarius improvements
to the first, and it further extends the method to handle the new cases in the cardinality proof
of this AFP entry.

As the implementation of the injectivity solver only evolves in the development branch of the AFP,
the submissions of the three AFP entries that employ the injectivity solver, have to create clones
of the injectivity solver for the identified and needed method adjustments. Ultimately, these three
clones should only remain in the stable branches of the AFP from Isabelle2016 to Isabelle2017
to work with their corresponding release versions.
In the development version, I have now consolidated the three versions here.
In the next step, I will move this version of the injectivity solver in
the @{theory "HOL-Library.Disjoint_Sets"} and it will hopefully only evolve further there.
\<close>

lemma disjoint_family_onI:
  assumes "\<And>i j. i \<in> I \<and> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> (A i) \<inter> (A j) = {}"
  shows "disjoint_family_on A I"
using assms unfolding disjoint_family_on_def by auto

lemma disjoint_bind: "\<And>S T f g. (\<And>s t. S s \<and> T t \<Longrightarrow> f s \<inter> g t = {}) \<Longrightarrow> ({s. S s} \<bind> f) \<inter> ({t. T t} \<bind> g) = {}"
by fastforce

lemma disjoint_bind': "\<And>S T f g. (\<And>s t. s \<in> S \<and> t \<in> T \<Longrightarrow> f s \<inter> g t = {}) \<Longrightarrow> (S \<bind> f) \<inter> (T \<bind> g) = {}"
by fastforce

lemma injectivity_solver_CollectE:
  assumes "a \<in> {x. P x} \<and> a' \<in> {x. P' x}"
  assumes "(P a \<and> P' a') \<Longrightarrow> W"
  shows "W"
using assms by auto

lemma injectivity_solver_prep_assms_Collect:
  assumes "x \<in> {x. P x}"
  shows "P x \<and> P x"
using assms by simp

lemma injectivity_solver_prep_assms: "x \<in> A \<Longrightarrow> x \<in> A \<and> x \<in> A"
  by simp

lemma disjoint_terminal_singleton: "\<And>s t X Y. s \<noteq> t \<Longrightarrow> (X = Y \<Longrightarrow> s = t) \<Longrightarrow> {X} \<inter> {Y} = {}"
by auto

lemma disjoint_terminal_Collect:
  assumes "s \<noteq> t"
  assumes "\<And>x x'. S x \<and> T x' \<Longrightarrow> x = x' \<Longrightarrow> s = t"
  shows "{x. S x} \<inter> {x. T x} = {}"
using assms by auto

lemma disjoint_terminal:
  "s \<noteq> t \<Longrightarrow> (\<And>x x'. x \<in> S \<and> x' \<in> T \<Longrightarrow> x = x' \<Longrightarrow> s = t) \<Longrightarrow> S \<inter> T = {}"
by blast

lemma elim_singleton:
  assumes "x \<in> {s} \<and> x' \<in> {t}"
  obtains "x = s \<and> x' = t"
using assms by blast

method injectivity_solver uses rule =
  insert method_facts,
  use nothing in \<open>
    ((drule injectivity_solver_prep_assms_Collect | drule injectivity_solver_prep_assms)+)?;
    rule disjoint_family_onI;
    ((rule disjoint_bind | rule disjoint_bind')+)?;
    (erule elim_singleton)?;
    (erule disjoint_terminal_singleton | erule disjoint_terminal_Collect | erule disjoint_terminal);
    (elim injectivity_solver_CollectE)?;
    rule rule;
    assumption+
  \<close>

end
