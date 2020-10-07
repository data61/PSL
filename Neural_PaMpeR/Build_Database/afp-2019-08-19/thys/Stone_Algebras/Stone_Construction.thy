(* Title:      Construction of Stone Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Stone Construction\<close>

text \<open>
This theory proves the uniqueness theorem for the triple representation of Stone algebras and the construction theorem of Stone algebras \cite{ChenGraetzer1969,Katrinak1973}.
Every Stone algebra $S$ has an associated triple consisting of
\begin{itemize}
\item the set of regular elements $B(S)$ of $S$,
\item the set of dense elements $D(S)$ of $S$, and
\item the structure map $\varphi(S) : B(S) \to F(D(S))$ defined by $\varphi(x) = {\uparrow} x \cap D(S)$.
\end{itemize}
Here $F(X)$ is the set of filters of a partially ordered set $X$.
We first show that
\begin{itemize}
\item $B(S)$ is a Boolean algebra,
\item $D(S)$ is a distributive lattice with a greatest element, whence $F(D(S))$ is a bounded distributive lattice, and
\item $\varphi(S)$ is a bounded lattice homomorphism.
\end{itemize}
Next, from a triple $T = (B,D,\varphi)$ such that $B$ is a Boolean algebra, $D$ is a distributive lattice with a greatest element and $\varphi : B \to F(D)$ is a bounded lattice homomorphism, we construct a Stone algebra $S(T)$.
The elements of $S(T)$ are pairs taken from $B \times F(D)$ following the construction of \cite{Katrinak1973}.
We need to represent $S(T)$ as a type to be able to instantiate the Stone algebra class.
Because the pairs must satisfy a condition depending on $\varphi$, this would require dependent types.
Since Isabelle/HOL does not have dependent types, we use a function lifting instead.
The lifted pairs form a Stone algebra.

Next, we specialise the construction to start with the triple associated with a Stone algebra $S$, that is, we construct $S(B(S),D(S),\varphi(S))$.
In this case, we can instantiate the lifted pairs to obtain a type of pairs (that no longer implements a dependent type).
To achieve this, we construct an embedding of the type of pairs into the lifted pairs, so that we inherit the Stone algebra axioms (using a technique of universal algebra that works for universally quantified equations and equational implications).

Next, we show that the Stone algebras $S(B(S),D(S),\varphi(S))$ and $S$ are isomorphic.
We give explicit mappings in both directions.
This implies the uniqueness theorem for the triple representation of Stone algebras.

Finally, we show that the triples $(B(S(T)),D(S(T)),\varphi(S(T)))$ and $T$ are isomorphic.
This requires an isomorphism of the Boolean algebras $B$ and $B(S(T))$, an isomorphism of the distributive lattices $D$ and $D(S(T))$, and a proof that they preserve the structure maps.
We give explicit mappings of the Boolean algebra isomorphism and the distributive lattice isomorphism in both directions.
This implies the construction theorem of Stone algebras.
Because $S(T)$ is implemented by lifted pairs, so are $B(S(T))$ and $D(S(T))$; we therefore also lift $B$ and $D$ to establish the isomorphisms.
\<close>

theory Stone_Construction

imports P_Algebras Filters

begin

subsection \<open>Triples\<close>

text \<open>
This section gives definitions of lattice homomorphisms and isomorphisms and basic properties.
It concludes with a locale that represents triples as discussed above.
\<close>

class sup_inf_top_bot_uminus = sup + inf + top + bot + uminus
class sup_inf_top_bot_uminus_ord = sup_inf_top_bot_uminus + ord

context p_algebra
begin

subclass sup_inf_top_bot_uminus_ord .

end

abbreviation sup_homomorphism :: "('a::sup \<Rightarrow> 'b::sup) \<Rightarrow> bool"
  where "sup_homomorphism f \<equiv> \<forall>x y . f (x \<squnion> y) = f x \<squnion> f y"

abbreviation inf_homomorphism :: "('a::inf \<Rightarrow> 'b::inf) \<Rightarrow> bool"
  where "inf_homomorphism f \<equiv> \<forall>x y . f (x \<sqinter> y) = f x \<sqinter> f y"

abbreviation sup_inf_homomorphism :: "('a::{sup,inf} \<Rightarrow> 'b::{sup,inf}) \<Rightarrow> bool"
  where "sup_inf_homomorphism f \<equiv> sup_homomorphism f \<and> inf_homomorphism f"

abbreviation sup_inf_top_homomorphism :: "('a::{sup,inf,top} \<Rightarrow> 'b::{sup,inf,top}) \<Rightarrow> bool"
  where "sup_inf_top_homomorphism f \<equiv> sup_inf_homomorphism f \<and> f top = top"

abbreviation sup_inf_top_bot_homomorphism :: "('a::{sup,inf,top,bot} \<Rightarrow> 'b::{sup,inf,top,bot}) \<Rightarrow> bool"
  where "sup_inf_top_bot_homomorphism f \<equiv> sup_inf_top_homomorphism f \<and> f bot = bot"

abbreviation bounded_lattice_homomorphism :: "('a::bounded_lattice \<Rightarrow> 'b::bounded_lattice) \<Rightarrow> bool"
  where "bounded_lattice_homomorphism f \<equiv> sup_inf_top_bot_homomorphism f"

abbreviation sup_inf_top_bot_uminus_homomorphism :: "('a::sup_inf_top_bot_uminus \<Rightarrow> 'b::sup_inf_top_bot_uminus) \<Rightarrow> bool"
  where "sup_inf_top_bot_uminus_homomorphism f \<equiv> sup_inf_top_bot_homomorphism f \<and> (\<forall>x . f (-x) = -f x)"

abbreviation sup_inf_top_bot_uminus_ord_homomorphism :: "('a::sup_inf_top_bot_uminus_ord \<Rightarrow> 'b::sup_inf_top_bot_uminus_ord) \<Rightarrow> bool"
  where "sup_inf_top_bot_uminus_ord_homomorphism f \<equiv> sup_inf_top_bot_uminus_homomorphism f \<and> (\<forall>x y . x \<le> y \<longrightarrow> f x \<le> f y)"

abbreviation sup_inf_top_isomorphism :: "('a::{sup,inf,top} \<Rightarrow> 'b::{sup,inf,top}) \<Rightarrow> bool"
  where "sup_inf_top_isomorphism f \<equiv> sup_inf_top_homomorphism f \<and> bij f"

abbreviation bounded_lattice_top_isomorphism :: "('a::bounded_lattice_top \<Rightarrow> 'b::bounded_lattice_top) \<Rightarrow> bool"
  where "bounded_lattice_top_isomorphism f \<equiv> sup_inf_top_isomorphism f"

abbreviation sup_inf_top_bot_uminus_isomorphism :: "('a::sup_inf_top_bot_uminus \<Rightarrow> 'b::sup_inf_top_bot_uminus) \<Rightarrow> bool"
  where "sup_inf_top_bot_uminus_isomorphism f \<equiv> sup_inf_top_bot_uminus_homomorphism f \<and> bij f"

abbreviation stone_algebra_isomorphism :: "('a::stone_algebra \<Rightarrow> 'b::stone_algebra) \<Rightarrow> bool"
  where "stone_algebra_isomorphism f \<equiv> sup_inf_top_bot_uminus_isomorphism f"

abbreviation boolean_algebra_isomorphism :: "('a::boolean_algebra \<Rightarrow> 'b::boolean_algebra) \<Rightarrow> bool"
  where "boolean_algebra_isomorphism f \<equiv> sup_inf_top_bot_uminus_isomorphism f"

lemma sup_homomorphism_mono:
  "sup_homomorphism (f::'a::semilattice_sup \<Rightarrow> 'b::semilattice_sup) \<Longrightarrow> mono f"
  by (metis le_iff_sup monoI)

lemma sup_isomorphism_ord_isomorphism:
  assumes "sup_homomorphism (f::'a::semilattice_sup \<Rightarrow> 'b::semilattice_sup)"
      and "bij f"
    shows "x \<le> y \<longleftrightarrow> f x \<le> f y"
proof
  assume "x \<le> y"
  thus "f x \<le> f y"
    by (metis assms(1) le_iff_sup)
next
  assume "f x \<le> f y"
  hence "f (x \<squnion> y) = f y"
    by (simp add: assms(1) le_iff_sup)
  hence "x \<squnion> y = y"
    by (metis injD bij_is_inj assms(2))
  thus "x \<le> y"
    by (simp add: le_iff_sup)
qed

text \<open>
A triple consists of a Boolean algebra, a distributive lattice with a greatest element, and a structure map.
The Boolean algebra and the distributive lattice are represented as HOL types.
Because both occur in the type of the structure map, the triple is determined simply by the structure map and its HOL type.
The structure map needs to be a bounded lattice homomorphism.
\<close>

locale triple =
  fixes phi :: "'a::boolean_algebra \<Rightarrow> 'b::distrib_lattice_top filter"
  assumes hom: "bounded_lattice_homomorphism phi"

subsection \<open>The Triple of a Stone Algebra\<close>

text \<open>
In this section we construct the triple associated to a Stone algebra.
\<close>

subsubsection \<open>Regular Elements\<close>

text \<open>
The regular elements of a Stone algebra form a Boolean subalgebra.
\<close>

typedef (overloaded) 'a regular = "regular_elements::'a::stone_algebra set"
  by auto

lemma simp_regular [simp]:
  "\<exists>y . Rep_regular x = -y"
  using Rep_regular by simp

setup_lifting type_definition_regular

instantiation regular :: (stone_algebra) boolean_algebra
begin

lift_definition sup_regular :: "'a regular \<Rightarrow> 'a regular \<Rightarrow> 'a regular" is sup
  by (meson regular_in_p_image_iff regular_closed_sup)

lift_definition inf_regular :: "'a regular \<Rightarrow> 'a regular \<Rightarrow> 'a regular" is inf
  by (meson regular_in_p_image_iff regular_closed_inf)

lift_definition minus_regular :: "'a regular \<Rightarrow> 'a regular \<Rightarrow> 'a regular" is "\<lambda>x y . x \<sqinter> -y"
  by (meson regular_in_p_image_iff regular_closed_inf)

lift_definition uminus_regular :: "'a regular \<Rightarrow> 'a regular" is uminus
  by auto

lift_definition bot_regular :: "'a regular" is bot
  by (meson regular_in_p_image_iff regular_closed_bot)

lift_definition top_regular :: "'a regular" is top
  by (meson regular_in_p_image_iff regular_closed_top)

lift_definition less_eq_regular :: "'a regular \<Rightarrow> 'a regular \<Rightarrow> bool" is less_eq .

lift_definition less_regular :: "'a regular \<Rightarrow> 'a regular \<Rightarrow> bool" is less .

instance
  apply intro_classes
  apply (simp add: less_eq_regular.rep_eq less_regular.rep_eq inf.less_le_not_le)
  apply (simp add: less_eq_regular.rep_eq)
  apply (simp add: less_eq_regular.rep_eq)
  apply (simp add: Rep_regular_inject less_eq_regular.rep_eq)
  apply (simp add: inf_regular.rep_eq less_eq_regular.rep_eq)
  apply (simp add: inf_regular.rep_eq less_eq_regular.rep_eq)
  apply (simp add: inf_regular.rep_eq less_eq_regular.rep_eq)
  apply (simp add: sup_regular.rep_eq less_eq_regular.rep_eq)
  apply (simp add: sup_regular.rep_eq less_eq_regular.rep_eq)
  apply (simp add: sup_regular.rep_eq less_eq_regular.rep_eq)
  apply (simp add: bot_regular.rep_eq less_eq_regular.rep_eq)
  apply (simp add: top_regular.rep_eq less_eq_regular.rep_eq)
  apply (metis (mono_tags) Rep_regular_inject inf_regular.rep_eq sup_inf_distrib1 sup_regular.rep_eq)
  apply (metis (mono_tags) Rep_regular_inverse bot_regular.abs_eq inf_regular.rep_eq inf_p uminus_regular.rep_eq)
  apply (metis (mono_tags) top_regular.abs_eq Rep_regular_inverse simp_regular stone sup_regular.rep_eq uminus_regular.rep_eq)
  by (metis (mono_tags) Rep_regular_inject inf_regular.rep_eq minus_regular.rep_eq uminus_regular.rep_eq)

end

instantiation regular :: (non_trivial_stone_algebra) non_trivial_boolean_algebra
begin

instance
proof (intro_classes, rule ccontr)
  assume "\<not>(\<exists>x y::'a regular . x \<noteq> y)"
  hence "(bot::'a regular) = top"
    by simp
  hence "(bot::'a) = top"
    by (metis bot_regular.rep_eq top_regular.rep_eq)
  thus False
    by (simp add: bot_not_top)
qed

end

subsubsection \<open>Dense Elements\<close>

text \<open>
The dense elements of a Stone algebra form a distributive lattice with a greatest element.
\<close>

typedef (overloaded) 'a dense = "dense_elements::'a::stone_algebra set"
  using dense_closed_top by blast

lemma simp_dense [simp]:
  "-Rep_dense x = bot"
  using Rep_dense by simp

setup_lifting type_definition_dense

instantiation dense :: (stone_algebra) distrib_lattice_top
begin

lift_definition sup_dense :: "'a dense \<Rightarrow> 'a dense \<Rightarrow> 'a dense" is sup
  by simp

lift_definition inf_dense :: "'a dense \<Rightarrow> 'a dense \<Rightarrow> 'a dense" is inf
  by simp

lift_definition top_dense :: "'a dense" is top
  by simp

lift_definition less_eq_dense :: "'a dense \<Rightarrow> 'a dense \<Rightarrow> bool" is less_eq .

lift_definition less_dense :: "'a dense \<Rightarrow> 'a dense \<Rightarrow> bool" is less .

instance
  apply intro_classes
  apply (simp add: less_eq_dense.rep_eq less_dense.rep_eq inf.less_le_not_le)
  apply (simp add: less_eq_dense.rep_eq)
  apply (simp add: less_eq_dense.rep_eq)
  apply (simp add: Rep_dense_inject less_eq_dense.rep_eq)
  apply (simp add: inf_dense.rep_eq less_eq_dense.rep_eq)
  apply (simp add: inf_dense.rep_eq less_eq_dense.rep_eq)
  apply (simp add: inf_dense.rep_eq less_eq_dense.rep_eq)
  apply (simp add: sup_dense.rep_eq less_eq_dense.rep_eq)
  apply (simp add: sup_dense.rep_eq less_eq_dense.rep_eq)
  apply (simp add: sup_dense.rep_eq less_eq_dense.rep_eq)
  apply (simp add: top_dense.rep_eq less_eq_dense.rep_eq)
  by (metis (mono_tags, lifting) Rep_dense_inject sup_inf_distrib1 inf_dense.rep_eq sup_dense.rep_eq)

end

lemma up_filter_dense_antitone_dense:
  "dense (x \<squnion> -x \<squnion> y) \<and> dense (x \<squnion> -x \<squnion> y \<squnion> z)"
  by simp

lemma up_filter_dense_antitone:
  "up_filter (Abs_dense (x \<squnion> -x \<squnion> y \<squnion> z)) \<le> up_filter (Abs_dense (x \<squnion> -x \<squnion> y))"
  by (unfold up_filter_antitone[THEN sym]) (simp add: Abs_dense_inverse less_eq_dense.rep_eq)

text \<open>
The filters of dense elements of a Stone algebra form a bounded distributive lattice.
\<close>

type_synonym 'a dense_filter = "'a dense filter"

typedef (overloaded) 'a dense_filter_type = "{ x::'a dense_filter . True }"
  using filter_top by blast

setup_lifting type_definition_dense_filter_type

instantiation dense_filter_type :: (stone_algebra) bounded_distrib_lattice
begin

lift_definition sup_dense_filter_type :: "'a dense_filter_type \<Rightarrow> 'a dense_filter_type \<Rightarrow> 'a dense_filter_type" is sup .

lift_definition inf_dense_filter_type :: "'a dense_filter_type \<Rightarrow> 'a dense_filter_type \<Rightarrow> 'a dense_filter_type" is inf .

lift_definition bot_dense_filter_type :: "'a dense_filter_type" is bot ..

lift_definition top_dense_filter_type :: "'a dense_filter_type" is top ..

lift_definition less_eq_dense_filter_type :: "'a dense_filter_type \<Rightarrow> 'a dense_filter_type \<Rightarrow> bool" is less_eq .

lift_definition less_dense_filter_type :: "'a dense_filter_type \<Rightarrow> 'a dense_filter_type \<Rightarrow> bool" is less .

instance
  apply intro_classes
  apply (simp add: less_eq_dense_filter_type.rep_eq less_dense_filter_type.rep_eq inf.less_le_not_le)
  apply (simp add: less_eq_dense_filter_type.rep_eq)
  apply (simp add: less_eq_dense_filter_type.rep_eq inf.order_lesseq_imp)
  apply (simp add: Rep_dense_filter_type_inject less_eq_dense_filter_type.rep_eq)
  apply (simp add: inf_dense_filter_type.rep_eq less_eq_dense_filter_type.rep_eq)
  apply (simp add: inf_dense_filter_type.rep_eq less_eq_dense_filter_type.rep_eq)
  apply (simp add: inf_dense_filter_type.rep_eq less_eq_dense_filter_type.rep_eq)
  apply (simp add: less_eq_dense_filter_type.rep_eq sup_dense_filter_type.rep_eq)
  apply (simp add: less_eq_dense_filter_type.rep_eq sup_dense_filter_type.rep_eq)
  apply (simp add: less_eq_dense_filter_type.rep_eq sup_dense_filter_type.rep_eq)
  apply (simp add: less_eq_dense_filter_type.rep_eq bot_dense_filter_type.rep_eq)
  apply (simp add: top_dense_filter_type.rep_eq less_eq_dense_filter_type.rep_eq)
  by (metis (mono_tags, lifting) Rep_dense_filter_type_inject sup_inf_distrib1 inf_dense_filter_type.rep_eq sup_dense_filter_type.rep_eq)

end

subsubsection \<open>The Structure Map\<close>

text \<open>
The structure map of a Stone algebra is a bounded lattice homomorphism.
It maps a regular element \<open>x\<close> to the set of all dense elements above \<open>-x\<close>.
This set is a filter.
\<close>

abbreviation stone_phi_set :: "'a::stone_algebra regular \<Rightarrow> 'a dense set"
  where "stone_phi_set x \<equiv> { y . -Rep_regular x \<le> Rep_dense y }"

lemma stone_phi_set_filter:
  "filter (stone_phi_set x)"
  apply (unfold filter_def, intro conjI)
  apply (metis Collect_empty_eq top_dense.rep_eq top_greatest)
  apply (metis inf_dense.rep_eq inf_le2 le_inf_iff mem_Collect_eq)
  using order_trans less_eq_dense.rep_eq by blast

definition stone_phi :: "'a::stone_algebra regular \<Rightarrow> 'a dense_filter"
  where "stone_phi x = Abs_filter (stone_phi_set x)"

text \<open>
To show that we obtain a triple, we only need to prove that \<open>stone_phi\<close> is a bounded lattice homomorphism.
The Boolean algebra and the distributive lattice requirements are taken care of by the type system.
\<close>

interpretation stone_phi: triple "stone_phi"
proof (unfold_locales, intro conjI)
  have 1: "Rep_regular (Abs_regular bot) = bot"
    by (metis bot_regular.rep_eq bot_regular_def)
  show "stone_phi bot = bot"
    apply (unfold stone_phi_def bot_regular_def 1 p_bot bot_filter_def)
    by (metis (mono_tags, lifting) Collect_cong Rep_dense_inject order_refl singleton_conv top.extremum_uniqueI top_dense.rep_eq)
next
  show "stone_phi top = top"
    by (metis Collect_cong stone_phi_def UNIV_I bot.extremum dense_closed_top top_empty_eq top_filter.abs_eq top_regular.rep_eq top_set_def)
next
  show "\<forall>x y::'a regular . stone_phi (x \<squnion> y) = stone_phi x \<squnion> stone_phi y"
  proof (intro allI)
    fix x y :: "'a regular"
    have "stone_phi_set (x \<squnion> y) = filter_sup (stone_phi_set x) (stone_phi_set y)"
    proof (rule set_eqI, rule iffI)
      fix z
      assume 2: "z \<in> stone_phi_set (x \<squnion> y)"
      let ?t = "-Rep_regular x \<squnion> Rep_dense z"
      let ?u = "-Rep_regular y \<squnion> Rep_dense z"
      let ?v = "Abs_dense ?t"
      let ?w = "Abs_dense ?u"
      have 3: "?v \<in> stone_phi_set x \<and> ?w \<in> stone_phi_set y"
        by (simp add: Abs_dense_inverse)
      have "?v \<sqinter> ?w = Abs_dense (?t \<sqinter> ?u)"
        by (simp add: eq_onp_def inf_dense.abs_eq)
      also have "... = Abs_dense (-Rep_regular (x \<squnion> y) \<squnion> Rep_dense z)"
        by (simp add: distrib(1) sup_commute sup_regular.rep_eq)
      also have "... = Abs_dense (Rep_dense z)"
        using 2 by (simp add: le_iff_sup)
      also have "... = z"
        by (simp add: Rep_dense_inverse)
      finally show "z \<in> filter_sup (stone_phi_set x) (stone_phi_set y)"
        using 3 mem_Collect_eq order_refl by fastforce
    next
      fix z
      assume "z \<in> filter_sup (stone_phi_set x) (stone_phi_set y)"
      then obtain v w where 4: "v \<in> stone_phi_set x \<and> w \<in> stone_phi_set y \<and> v \<sqinter> w \<le> z"
        by auto
      have "-Rep_regular (x \<squnion> y) = Rep_regular (-(x \<squnion> y))"
        by (metis uminus_regular.rep_eq)
      also have "... = -Rep_regular x \<sqinter> -Rep_regular y"
        by (simp add: inf_regular.rep_eq uminus_regular.rep_eq)
      also have "... \<le> Rep_dense v \<sqinter> Rep_dense w"
        using 4 inf_mono mem_Collect_eq by blast
      also have "... = Rep_dense (v \<sqinter> w)"
        by (simp add: inf_dense.rep_eq)
      also have "... \<le> Rep_dense z"
        using 4 by (simp add: less_eq_dense.rep_eq)
      finally show "z \<in> stone_phi_set (x \<squnion> y)"
        by simp
    qed
    thus "stone_phi (x \<squnion> y) = stone_phi x \<squnion> stone_phi y"
      by (simp add: stone_phi_def eq_onp_same_args stone_phi_set_filter sup_filter.abs_eq)
  qed
next
  show "\<forall>x y::'a regular . stone_phi (x \<sqinter> y) = stone_phi x \<sqinter> stone_phi y"
  proof (intro allI)
    fix x y :: "'a regular"
    have "\<forall>z . -Rep_regular (x \<sqinter> y) \<le> Rep_dense z \<longleftrightarrow> -Rep_regular x \<le> Rep_dense z \<and> -Rep_regular y \<le> Rep_dense z"
      by (simp add: inf_regular.rep_eq)
    hence "stone_phi_set (x \<sqinter> y) = (stone_phi_set x) \<inter> (stone_phi_set y)"
      by auto
    thus "stone_phi (x \<sqinter> y) = stone_phi x \<sqinter> stone_phi y"
      by (simp add: stone_phi_def eq_onp_same_args stone_phi_set_filter inf_filter.abs_eq)
  qed
qed

subsection \<open>Properties of Triples\<close>

text \<open>
In this section we construct a certain set of pairs from a triple, introduce operations on these pairs and develop their properties.
The given set and operations will form a Stone algebra.
\<close>

context triple
begin

lemma phi_bot:
  "phi bot = Abs_filter {top}"
  by (metis hom bot_filter_def)

lemma phi_top:
  "phi top = Abs_filter UNIV"
  by (metis hom top_filter_def)

text \<open>
The occurrence of \<open>phi\<close> in the following definition of the pairs creates a need for dependent types.
\<close>

definition pairs :: "('a \<times> 'b filter) set"
  where "pairs = { (x,y) . \<exists>z . y = phi (-x) \<squnion> up_filter z }"

text \<open>
Operations on pairs are defined in the following.
They will be used to establish that the pairs form a Stone algebra.
\<close>

fun pairs_less_eq :: "('a \<times> 'b filter) \<Rightarrow> ('a \<times> 'b filter) \<Rightarrow> bool"
  where "pairs_less_eq (x,y) (z,w) = (x \<le> z \<and> w \<le> y)"

fun pairs_less :: "('a \<times> 'b filter) \<Rightarrow> ('a \<times> 'b filter) \<Rightarrow> bool"
  where "pairs_less (x,y) (z,w) = (pairs_less_eq (x,y) (z,w) \<and> \<not> pairs_less_eq (z,w) (x,y))"

fun pairs_sup :: "('a \<times> 'b filter) \<Rightarrow> ('a \<times> 'b filter) \<Rightarrow> ('a \<times> 'b filter)"
  where "pairs_sup (x,y) (z,w) = (x \<squnion> z,y \<sqinter> w)"

fun pairs_inf :: "('a \<times> 'b filter) \<Rightarrow> ('a \<times> 'b filter) \<Rightarrow> ('a \<times> 'b filter)"
  where "pairs_inf (x,y) (z,w) = (x \<sqinter> z,y \<squnion> w)"

fun pairs_uminus :: "('a \<times> 'b filter) \<Rightarrow> ('a \<times> 'b filter)"
  where "pairs_uminus (x,y) = (-x,phi x)"

abbreviation pairs_bot :: "('a \<times> 'b filter)"
  where "pairs_bot \<equiv> (bot,Abs_filter UNIV)"

abbreviation pairs_top :: "('a \<times> 'b filter)"
  where "pairs_top \<equiv> (top,Abs_filter {top})"

lemma pairs_top_in_set:
  "(x,y) \<in> pairs \<Longrightarrow> top \<in> Rep_filter y"
  by simp

lemma phi_complemented:
  "complement (phi x) (phi (-x))"
  by (metis hom inf_compl_bot sup_compl_top)

lemma phi_inf_principal:
  "\<exists>z . up_filter z = phi x \<sqinter> up_filter y"
proof -
  let ?F = "Rep_filter (phi x)"
  let ?G = "Rep_filter (phi (-x))"
  have 1: "eq_onp filter ?F ?F \<and> eq_onp filter (\<up>y) (\<up>y)"
    by (simp add: eq_onp_def)
  have "filter_complements ?F ?G"
    apply (intro conjI)
    apply simp
    apply simp
    apply (metis (no_types) phi_complemented sup_filter.rep_eq top_filter.rep_eq)
    by (metis (no_types) phi_complemented inf_filter.rep_eq bot_filter.rep_eq)
  hence "is_principal_up (?F \<inter> \<up>y)"
    using complemented_filter_inf_principal by blast
  then obtain z where "\<up>z = ?F \<inter> \<up>y"
    by auto
  hence "up_filter z = Abs_filter (?F \<inter> \<up>y)"
    by simp
  also have "... = Abs_filter ?F \<sqinter> up_filter y"
    using 1 inf_filter.abs_eq by force
  also have "... = phi x \<sqinter> up_filter y"
    by (simp add: Rep_filter_inverse)
  finally show ?thesis
    by auto
qed

text \<open>
Quite a bit of filter theory is involved in showing that the intersection of \<open>phi x\<close> with a principal filter is a principal filter, so the following function can extract its least element.
\<close>

fun rho :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  where "rho x y = (SOME z . up_filter z = phi x \<sqinter> up_filter y)"

lemma rho_char:
  "up_filter (rho x y) = phi x \<sqinter> up_filter y"
  by (metis (mono_tags) someI_ex rho.simps phi_inf_principal)

text \<open>
The following results show that the pairs are closed under the given operations.
\<close>

lemma pairs_sup_closed:
  assumes "(x,y) \<in> pairs"
      and "(z,w) \<in> pairs"
    shows "pairs_sup (x,y) (z,w) \<in> pairs"
proof -
  from assms obtain u v where "y = phi (-x) \<squnion> up_filter u \<and> w = phi (-z) \<squnion> up_filter v"
    using pairs_def by auto
  hence "pairs_sup (x,y) (z,w) = (x \<squnion> z,(phi (-x) \<squnion> up_filter u) \<sqinter> (phi (-z) \<squnion> up_filter v))"
    by simp
  also have "... = (x \<squnion> z,(phi (-x) \<sqinter> phi (-z)) \<squnion> (phi (-x) \<sqinter> up_filter v) \<squnion> (up_filter u \<sqinter> phi (-z)) \<squnion> (up_filter u \<sqinter> up_filter v))"
    by (simp add: inf.sup_commute inf_sup_distrib1 sup_commute sup_left_commute)
  also have "... = (x \<squnion> z,phi (-(x \<squnion> z)) \<squnion> (phi (-x) \<sqinter> up_filter v) \<squnion> (up_filter u \<sqinter> phi (-z)) \<squnion> (up_filter u \<sqinter> up_filter v))"
    using hom by simp
  also have "... = (x \<squnion> z,phi (-(x \<squnion> z)) \<squnion> up_filter (rho (-x) v) \<squnion> up_filter (rho (-z) u) \<squnion> (up_filter u \<sqinter> up_filter v))"
    by (metis inf.sup_commute rho_char)
  also have "... = (x \<squnion> z,phi (-(x \<squnion> z)) \<squnion> up_filter (rho (-x) v) \<squnion> up_filter (rho (-z) u) \<squnion> up_filter (u \<squnion> v))"
    by (metis up_filter_dist_sup)
  also have "... = (x \<squnion> z,phi (-(x \<squnion> z)) \<squnion> up_filter (rho (-x) v \<sqinter> rho (-z) u \<sqinter> (u \<squnion> v)))"
    by (simp add: sup_commute sup_left_commute up_filter_dist_inf)
  finally show ?thesis
    using pairs_def by auto
qed

lemma pairs_inf_closed:
  assumes "(x,y) \<in> pairs"
      and "(z,w) \<in> pairs"
    shows "pairs_inf (x,y) (z,w) \<in> pairs"
proof -
  from assms obtain u v where "y = phi (-x) \<squnion> up_filter u \<and> w = phi (-z) \<squnion> up_filter v"
    using pairs_def by auto
  hence "pairs_inf (x,y) (z,w) = (x \<sqinter> z,(phi (-x) \<squnion> up_filter u) \<squnion> (phi (-z) \<squnion> up_filter v))"
    by simp
  also have "... = (x \<sqinter> z,(phi (-x) \<squnion> phi (-z)) \<squnion> (up_filter u \<squnion> up_filter v))"
    by (simp add: sup_commute sup_left_commute)
  also have "... = (x \<sqinter> z,phi (-(x \<sqinter> z)) \<squnion> (up_filter u \<squnion> up_filter v))"
    using hom by simp
  also have "... = (x \<sqinter> z,phi (-(x \<sqinter> z)) \<squnion> up_filter (u \<sqinter> v))"
    by (simp add: up_filter_dist_inf)
  finally show ?thesis
    using pairs_def by auto
qed

lemma pairs_uminus_closed:
  "pairs_uminus (x,y) \<in> pairs"
proof -
  have "pairs_uminus (x,y) = (-x,phi (--x) \<squnion> bot)"
    by simp
  also have "... = (-x,phi (--x) \<squnion> up_filter top)"
    by (simp add: bot_filter.abs_eq)
  finally show ?thesis
    by (metis (mono_tags, lifting) mem_Collect_eq old.prod.case pairs_def)
qed

lemma pairs_bot_closed:
  "pairs_bot \<in> pairs"
  using pairs_def phi_top triple.hom triple_axioms by fastforce

lemma pairs_top_closed:
  "pairs_top \<in> pairs"
  by (metis p_bot pairs_uminus.simps pairs_uminus_closed phi_bot)

text \<open>
We prove enough properties of the pair operations so that we can later show they form a Stone algebra.
\<close>

lemma pairs_sup_dist_inf:
  "(x,y) \<in> pairs \<Longrightarrow> (z,w) \<in> pairs \<Longrightarrow> (u,v) \<in> pairs \<Longrightarrow> pairs_sup (x,y) (pairs_inf (z,w) (u,v)) = pairs_inf (pairs_sup (x,y) (z,w)) (pairs_sup (x,y) (u,v))"
  using sup_inf_distrib1 inf_sup_distrib1 by auto

lemma pairs_phi_less_eq:
  "(x,y) \<in> pairs \<Longrightarrow> phi (-x) \<le> y"
  using pairs_def by auto

lemma pairs_uminus_galois:
  assumes "(x,y) \<in> pairs"
      and "(z,w) \<in> pairs"
    shows "pairs_inf (x,y) (z,w) = pairs_bot \<longleftrightarrow> pairs_less_eq (x,y) (pairs_uminus (z,w))"
proof -
  have 1: "x \<sqinter> z = bot \<and> y \<squnion> w = Abs_filter UNIV \<longrightarrow> phi z \<le> y"
    by (metis (no_types, lifting) assms(1) heyting.implies_inf_absorb hom le_supE pairs_phi_less_eq sup_bot_right)
  have 2: "x \<le> -z \<and> phi z \<le> y \<longrightarrow> y \<squnion> w = Abs_filter UNIV"
  proof
    assume 3: "x \<le> -z \<and> phi z \<le> y"
    have "Abs_filter UNIV = phi z \<squnion> phi (-z)"
      using hom phi_complemented phi_top by auto
    also have "... \<le> y \<squnion> w"
      using 3 assms(2) sup_mono pairs_phi_less_eq by auto
    finally show "y \<squnion> w = Abs_filter UNIV"
      using hom phi_top top.extremum_uniqueI by auto
  qed
  have "x \<sqinter> z = bot \<longleftrightarrow> x \<le> -z"
    by (simp add: shunting_1)
  thus ?thesis
    using 1 2 Pair_inject pairs_inf.simps pairs_less_eq.simps pairs_uminus.simps by auto
qed

lemma pairs_stone:
  "(x,y) \<in> pairs \<Longrightarrow> pairs_sup (pairs_uminus (x,y)) (pairs_uminus (pairs_uminus (x,y))) = pairs_top"
  by (metis hom pairs_sup.simps pairs_uminus.simps phi_bot phi_complemented stone)

text \<open>
The following results show how the regular elements and the dense elements among the pairs look like.
\<close>

abbreviation "dense_pairs \<equiv> { (x,y) . (x,y) \<in> pairs \<and> pairs_uminus (x,y) = pairs_bot }"
abbreviation "regular_pairs \<equiv> { (x,y) . (x,y) \<in> pairs \<and> pairs_uminus (pairs_uminus (x,y)) = (x,y) }"
abbreviation "is_principal_up_filter x \<equiv> \<exists>y . x = up_filter y"

lemma dense_pairs:
  "dense_pairs = { (x,y) . x = top \<and> is_principal_up_filter y }"
proof -
  have "dense_pairs = { (x,y) . (x,y) \<in> pairs \<and> x = top }"
    by (metis Pair_inject compl_bot_eq double_compl pairs_uminus.simps phi_top)
  also have "... = { (x,y) . (\<exists>z . y = up_filter z) \<and> x = top }"
    using hom pairs_def by auto
  finally show ?thesis
    by auto
qed

lemma regular_pairs:
  "regular_pairs = { (x,y) . y = phi (-x) }"
  using pairs_def pairs_uminus_closed by fastforce

text \<open>
The following extraction function will be used in defining one direction of the Stone algebra isomorphism.
\<close>

fun rho_pair :: "'a \<times> 'b filter \<Rightarrow> 'b"
  where "rho_pair (x,y) = (SOME z . up_filter z = phi x \<sqinter> y)"

lemma get_rho_pair_char:
  assumes "(x,y) \<in> pairs"
    shows "up_filter (rho_pair (x,y)) = phi x \<sqinter> y"
proof -
  from assms obtain w where "y = phi (-x) \<squnion> up_filter w"
    using pairs_def by auto
  hence "phi x \<sqinter> y = phi x \<sqinter> up_filter w"
    by (simp add: inf_sup_distrib1 phi_complemented)
  thus ?thesis
    using rho_char by auto
qed

lemma sa_iso_pair:
  "(--x,phi (-x) \<squnion> up_filter y) \<in> pairs"
  using pairs_def by auto

end

subsection \<open>The Stone Algebra of a Triple\<close>

text \<open>
In this section we prove that the set of pairs constructed in a triple forms a Stone Algebra.
The following type captures the parameter \<open>phi\<close> on which the type of triples depends.
This parameter is the structure map that occurs in the definition of the set of pairs.
The set of all structure maps is the set of all bounded lattice homomorphisms (of appropriate type).
In order to make it a HOL type, we need to show that at least one such structure map exists.
To this end we use the ultrafilter lemma: the required bounded lattice homomorphism is essentially the characteristic map of an ultrafilter, but the latter must exist.
In particular, the underlying Boolean algebra must contain at least two elements.
\<close>

typedef (overloaded) ('a,'b) phi = "{ f::'a::non_trivial_boolean_algebra \<Rightarrow> 'b::distrib_lattice_top filter . bounded_lattice_homomorphism f }"
proof -
  from ultra_filter_exists obtain F :: "'a set" where 1: "ultra_filter F"
    by auto
  hence 2: "prime_filter F"
    using ultra_filter_prime by auto
  let ?f = "\<lambda>x . if x\<in>F then top else bot::'b filter"
  have "bounded_lattice_homomorphism ?f"
  proof (intro conjI)
    show "?f bot = bot"
      using 1 by (meson bot.extremum filter_def subset_eq top.extremum_unique)
  next
    show "?f top = top"
      using 1 by simp
  next
    show "\<forall>x y . ?f (x \<squnion> y) = ?f x \<squnion> ?f y"
    proof (intro allI)
      fix x y
      show "?f (x \<squnion> y) = ?f x \<squnion> ?f y"
        apply (cases "x \<in> F"; cases "y \<in> F")
        using 1 filter_def apply fastforce
        using 1 filter_def apply fastforce
        using 1 filter_def apply fastforce
        using 2 sup_bot_left by auto
   qed
  next
    show "\<forall>x y . ?f (x \<sqinter> y) = ?f x \<sqinter> ?f y"
    proof (intro allI)
      fix x y
      show "?f (x \<sqinter> y) = ?f x \<sqinter> ?f y"
        apply (cases "x \<in> F"; cases "y \<in> F")
        using 1 apply (simp add: filter_inf_closed)
        using 1 apply (metis (mono_tags, lifting) brouwer.inf_sup_ord(4) inf_top_left filter_def)
        using 1 apply (metis (mono_tags, lifting) brouwer.inf_sup_ord(3) inf_top_right filter_def)
        using 1 filter_def by force
    qed
  qed
  hence "?f \<in> {f . bounded_lattice_homomorphism f}"
    by simp
  thus ?thesis
    by meson
qed

lemma simp_phi [simp]:
  "bounded_lattice_homomorphism (Rep_phi x)"
  using Rep_phi by simp

setup_lifting type_definition_phi

text \<open>
The following implements the dependent type of pairs depending on structure maps.
It uses functions from structure maps to pairs with the requirement that, for each structure map, the corresponding pair is contained in the set of pairs constructed for a triple with that structure map.

If this type could be defined in the locale \<open>triple\<close> and instantiated to Stone algebras there, there would be no need for the lifting and we could work with triples directly.
\<close>

typedef (overloaded) ('a,'b) lifted_pair = "{ pf::('a::non_trivial_boolean_algebra,'b::distrib_lattice_top) phi \<Rightarrow> 'a \<times> 'b filter . \<forall>f . pf f \<in> triple.pairs (Rep_phi f) }"
proof -
  have "\<forall>f::('a,'b) phi . triple.pairs_bot \<in> triple.pairs (Rep_phi f)"
  proof
    fix f :: "('a,'b) phi"
    have "triple (Rep_phi f)"
      by (simp add: triple_def)
    thus "triple.pairs_bot \<in> triple.pairs (Rep_phi f)"
      using triple.regular_pairs triple.phi_top by fastforce
  qed
  thus ?thesis
    by auto
qed

lemma simp_lifted_pair [simp]:
  "\<forall>f . Rep_lifted_pair pf f \<in> triple.pairs (Rep_phi f)"
  using Rep_lifted_pair by simp

setup_lifting type_definition_lifted_pair

text \<open>
The lifted pairs form a Stone algebra.
\<close>

instantiation lifted_pair :: (non_trivial_boolean_algebra,distrib_lattice_top) stone_algebra
begin

text \<open>
All operations are lifted point-wise.
\<close>

lift_definition sup_lifted_pair :: "('a,'b) lifted_pair \<Rightarrow> ('a,'b) lifted_pair \<Rightarrow> ('a,'b) lifted_pair" is "\<lambda>xf yf f . triple.pairs_sup (xf f) (yf f)"
  by (metis (no_types, hide_lams) simp_phi triple_def triple.pairs_sup_closed prod.collapse)

lift_definition inf_lifted_pair :: "('a,'b) lifted_pair \<Rightarrow> ('a,'b) lifted_pair \<Rightarrow> ('a,'b) lifted_pair" is "\<lambda>xf yf f . triple.pairs_inf (xf f) (yf f)"
  by (metis (no_types, hide_lams) simp_phi triple_def triple.pairs_inf_closed prod.collapse)

lift_definition uminus_lifted_pair :: "('a,'b) lifted_pair \<Rightarrow> ('a,'b) lifted_pair" is "\<lambda>xf f . triple.pairs_uminus (Rep_phi f) (xf f)"
  by (metis (no_types, hide_lams) simp_phi triple_def triple.pairs_uminus_closed prod.collapse)

lift_definition bot_lifted_pair :: "('a,'b) lifted_pair" is "\<lambda>f . triple.pairs_bot"
  by (metis (no_types, hide_lams) simp_phi triple_def triple.pairs_bot_closed)

lift_definition top_lifted_pair :: "('a,'b) lifted_pair" is "\<lambda>f . triple.pairs_top"
  by (metis (no_types, hide_lams) simp_phi triple_def triple.pairs_top_closed)

lift_definition less_eq_lifted_pair :: "('a,'b) lifted_pair \<Rightarrow> ('a,'b) lifted_pair \<Rightarrow> bool" is "\<lambda>xf yf . \<forall>f . triple.pairs_less_eq (xf f) (yf f)" .

lift_definition less_lifted_pair :: "('a,'b) lifted_pair \<Rightarrow> ('a,'b) lifted_pair \<Rightarrow> bool" is "\<lambda>xf yf . (\<forall>f . triple.pairs_less_eq (xf f) (yf f)) \<and> \<not> (\<forall>f . triple.pairs_less_eq (yf f) (xf f))" .

instance
proof intro_classes
  fix xf yf :: "('a,'b) lifted_pair"
  show "xf < yf \<longleftrightarrow> xf \<le> yf \<and> \<not> yf \<le> xf"
    by (simp add: less_lifted_pair.rep_eq less_eq_lifted_pair.rep_eq)
next
  fix xf :: "('a,'b) lifted_pair"
  {
    fix f :: "('a,'b) phi"
    have 1: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    obtain x1 x2 where "(x1,x2) = ?x"
      using prod.collapse by blast
    hence "triple.pairs_less_eq ?x ?x"
      using 1 by (metis triple.pairs_less_eq.simps order_refl)
  }
  thus "xf \<le> xf"
    by (simp add: less_eq_lifted_pair.rep_eq)
next
  fix xf yf zf :: "('a,'b) lifted_pair"
  assume 1: "xf \<le> yf" and 2: "yf \<le> zf"
  {
    fix f :: "('a,'b) phi"
    have 3: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    let ?y = "Rep_lifted_pair yf f"
    let ?z = "Rep_lifted_pair zf f"
    obtain x1 x2 y1 y2 z1 z2 where 4: "(x1,x2) = ?x \<and> (y1,y2) = ?y \<and> (z1,z2) = ?z"
      using prod.collapse by blast
    have "triple.pairs_less_eq ?x ?y \<and> triple.pairs_less_eq ?y ?z"
      using 1 2 3 less_eq_lifted_pair.rep_eq by simp
    hence "triple.pairs_less_eq ?x ?z"
      using 3 4 by (metis (mono_tags, lifting) triple.pairs_less_eq.simps order_trans)
  }
  thus "xf \<le> zf"
    by (simp add: less_eq_lifted_pair.rep_eq)
next
  fix xf yf :: "('a,'b) lifted_pair"
  assume 1: "xf \<le> yf" and 2: "yf \<le> xf"
  {
    fix f :: "('a,'b) phi"
    have 3: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    let ?y = "Rep_lifted_pair yf f"
    obtain x1 x2 y1 y2 where 4: "(x1,x2) = ?x \<and> (y1,y2) = ?y"
      using prod.collapse by blast
    have "triple.pairs_less_eq ?x ?y \<and> triple.pairs_less_eq ?y ?x"
      using 1 2 3 less_eq_lifted_pair.rep_eq by simp
    hence "?x = ?y"
      using 3 4 by (metis (mono_tags, lifting) triple.pairs_less_eq.simps antisym)
  }
  thus "xf = yf"
    by (metis Rep_lifted_pair_inverse ext)
next
  fix xf yf :: "('a,'b) lifted_pair"
  {
    fix f :: "('a,'b) phi"
    have 1: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    let ?y = "Rep_lifted_pair yf f"
    obtain x1 x2 y1 y2 where "(x1,x2) = ?x \<and> (y1,y2) = ?y"
      using prod.collapse by blast
    hence "triple.pairs_less_eq (triple.pairs_inf ?x ?y) ?y"
      using 1 by (metis (mono_tags, lifting) inf_sup_ord(2) sup.cobounded2 triple.pairs_inf.simps triple.pairs_less_eq.simps inf_lifted_pair.rep_eq)
  }
  thus "xf \<sqinter> yf \<le> yf"
    by (simp add: less_eq_lifted_pair.rep_eq inf_lifted_pair.rep_eq)
next
  fix xf yf :: "('a,'b) lifted_pair"
  {
    fix f :: "('a,'b) phi"
    have 1: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    let ?y = "Rep_lifted_pair yf f"
    obtain x1 x2 y1 y2 where "(x1,x2) = ?x \<and> (y1,y2) = ?y"
      using prod.collapse by blast
    hence "triple.pairs_less_eq (triple.pairs_inf ?x ?y) ?x"
      using 1 by (metis (mono_tags, lifting) inf_sup_ord(1) sup.cobounded1 triple.pairs_inf.simps triple.pairs_less_eq.simps inf_lifted_pair.rep_eq)
  }
  thus "xf \<sqinter> yf \<le> xf"
    by (simp add: less_eq_lifted_pair.rep_eq inf_lifted_pair.rep_eq)
next
  fix xf yf zf :: "('a,'b) lifted_pair"
  assume 1: "xf \<le> yf" and 2: "xf \<le> zf"
  {
    fix f :: "('a,'b) phi"
    have 3: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    let ?y = "Rep_lifted_pair yf f"
    let ?z = "Rep_lifted_pair zf f"
    obtain x1 x2 y1 y2 z1 z2 where 4: "(x1,x2) = ?x \<and> (y1,y2) = ?y \<and> (z1,z2) = ?z"
      using prod.collapse by blast
    have "triple.pairs_less_eq ?x ?y \<and> triple.pairs_less_eq ?x ?z"
      using 1 2 3 less_eq_lifted_pair.rep_eq by simp
    hence "triple.pairs_less_eq ?x (triple.pairs_inf ?y ?z)"
      using 3 4 by (metis (mono_tags, lifting) le_inf_iff sup.bounded_iff triple.pairs_inf.simps triple.pairs_less_eq.simps)
  }
  thus "xf \<le> yf \<sqinter> zf"
    by (simp add: less_eq_lifted_pair.rep_eq inf_lifted_pair.rep_eq)
next
  fix xf yf :: "('a,'b) lifted_pair"
  {
    fix f :: "('a,'b) phi"
    have 1: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    let ?y = "Rep_lifted_pair yf f"
    obtain x1 x2 y1 y2 where "(x1,x2) = ?x \<and> (y1,y2) = ?y"
      using prod.collapse by blast
    hence "triple.pairs_less_eq ?x (triple.pairs_sup ?x ?y)"
      using 1 by (metis (no_types, lifting) inf_commute sup.cobounded1 inf.cobounded2 triple.pairs_sup.simps triple.pairs_less_eq.simps sup_lifted_pair.rep_eq)
  }
  thus "xf \<le> xf \<squnion> yf"
    by (simp add: less_eq_lifted_pair.rep_eq sup_lifted_pair.rep_eq)
next
  fix xf yf :: "('a,'b) lifted_pair"
  {
    fix f :: "('a,'b) phi"
    have 1: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    let ?y = "Rep_lifted_pair yf f"
    obtain x1 x2 y1 y2 where "(x1,x2) = ?x \<and> (y1,y2) = ?y"
      using prod.collapse by blast
    hence "triple.pairs_less_eq ?y (triple.pairs_sup ?x ?y)"
      using 1 by (metis (no_types, lifting) sup.cobounded2 inf.cobounded2 triple.pairs_sup.simps triple.pairs_less_eq.simps sup_lifted_pair.rep_eq)
  }
  thus "yf \<le> xf \<squnion> yf"
    by (simp add: less_eq_lifted_pair.rep_eq sup_lifted_pair.rep_eq)
next
  fix xf yf zf :: "('a,'b) lifted_pair"
  assume 1: "yf \<le> xf" and 2: "zf \<le> xf"
  {
    fix f :: "('a,'b) phi"
    have 3: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    let ?y = "Rep_lifted_pair yf f"
    let ?z = "Rep_lifted_pair zf f"
    obtain x1 x2 y1 y2 z1 z2 where 4: "(x1,x2) = ?x \<and> (y1,y2) = ?y \<and> (z1,z2) = ?z"
      using prod.collapse by blast
    have "triple.pairs_less_eq ?y ?x \<and> triple.pairs_less_eq ?z ?x"
      using 1 2 3 less_eq_lifted_pair.rep_eq by simp
    hence "triple.pairs_less_eq (triple.pairs_sup ?y ?z) ?x"
      using 3 4 by (metis (mono_tags, lifting) le_inf_iff sup.bounded_iff triple.pairs_sup.simps triple.pairs_less_eq.simps)
  }
  thus "yf \<squnion> zf \<le> xf"
    by (simp add: less_eq_lifted_pair.rep_eq sup_lifted_pair.rep_eq)
next
  fix xf :: "('a,'b) lifted_pair"
  {
    fix f :: "('a,'b) phi"
    have 1: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    obtain x1 x2 where "(x1,x2) = ?x"
      using prod.collapse by blast
    hence "triple.pairs_less_eq triple.pairs_bot ?x"
      using 1 by (metis bot.extremum top_greatest top_filter.abs_eq triple.pairs_less_eq.simps)
  }
  thus "bot \<le> xf"
    by (simp add: less_eq_lifted_pair.rep_eq bot_lifted_pair.rep_eq)
next
  fix xf :: "('a,'b) lifted_pair"
  {
    fix f :: "('a,'b) phi"
    have 1: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    obtain x1 x2 where "(x1,x2) = ?x"
      using prod.collapse by blast
    hence "triple.pairs_less_eq ?x triple.pairs_top"
      using 1 by (metis top.extremum bot_least bot_filter.abs_eq triple.pairs_less_eq.simps)
  }
  thus "xf \<le> top"
    by (simp add: less_eq_lifted_pair.rep_eq top_lifted_pair.rep_eq)
next
  fix xf yf zf :: "('a,'b) lifted_pair"
  {
    fix f :: "('a,'b) phi"
    have 1: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    let ?y = "Rep_lifted_pair yf f"
    let ?z = "Rep_lifted_pair zf f"
    obtain x1 x2 y1 y2 z1 z2 where "(x1,x2) = ?x \<and> (y1,y2) = ?y \<and> (z1,z2) = ?z"
      using prod.collapse by blast
    hence "triple.pairs_sup ?x (triple.pairs_inf ?y ?z) = triple.pairs_inf (triple.pairs_sup ?x ?y) (triple.pairs_sup ?x ?z)"
      using 1 by (metis (no_types) sup_inf_distrib1 inf_sup_distrib1 triple.pairs_sup.simps triple.pairs_inf.simps)
  }
  thus "xf \<squnion> (yf \<sqinter> zf) = (xf \<squnion> yf) \<sqinter> (xf \<squnion> zf)"
    by (metis Rep_lifted_pair_inverse ext sup_lifted_pair.rep_eq inf_lifted_pair.rep_eq)
next
  fix xf yf :: "('a,'b) lifted_pair"
  {
    fix f :: "('a,'b) phi"
    have 1: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    let ?y = "Rep_lifted_pair yf f"
    obtain x1 x2 y1 y2 where 2: "(x1,x2) = ?x \<and> (y1,y2) = ?y"
      using prod.collapse by blast
    have "?x \<in> triple.pairs (Rep_phi f) \<and> ?y \<in> triple.pairs (Rep_phi f)"
      by simp
    hence "(triple.pairs_inf ?x ?y = triple.pairs_bot) \<longleftrightarrow> triple.pairs_less_eq ?x (triple.pairs_uminus (Rep_phi f) ?y)"
      using 1 2 by (metis triple.pairs_uminus_galois)
  }
  hence "\<forall>f . (Rep_lifted_pair (xf \<sqinter> yf) f = Rep_lifted_pair bot f) \<longleftrightarrow> triple.pairs_less_eq (Rep_lifted_pair xf f) (Rep_lifted_pair (-yf) f)"
    using bot_lifted_pair.rep_eq inf_lifted_pair.rep_eq uminus_lifted_pair.rep_eq by simp
  hence "(Rep_lifted_pair (xf \<sqinter> yf) = Rep_lifted_pair bot) \<longleftrightarrow> xf \<le> -yf"
    using less_eq_lifted_pair.rep_eq by auto
  thus "(xf \<sqinter> yf = bot) \<longleftrightarrow> (xf \<le> -yf)"
    by (simp add: Rep_lifted_pair_inject)
next
  fix xf :: "('a,'b) lifted_pair"
  {
    fix f :: "('a,'b) phi"
    have 1: "triple (Rep_phi f)"
      by (simp add: triple_def)
    let ?x = "Rep_lifted_pair xf f"
    obtain x1 x2 where "(x1,x2) = ?x"
      using prod.collapse by blast
    hence "triple.pairs_sup (triple.pairs_uminus (Rep_phi f) ?x) (triple.pairs_uminus (Rep_phi f) (triple.pairs_uminus (Rep_phi f) ?x)) = triple.pairs_top"
      using 1 by (metis simp_lifted_pair triple.pairs_stone)
  }
  hence "Rep_lifted_pair (-xf \<squnion> --xf) = Rep_lifted_pair top"
    using sup_lifted_pair.rep_eq uminus_lifted_pair.rep_eq top_lifted_pair.rep_eq by simp
  thus "-xf \<squnion> --xf = top"
    by (simp add: Rep_lifted_pair_inject)
qed

end

subsection \<open>The Stone Algebra of the Triple of a Stone Algebra\<close>

text \<open>
In this section we specialise the above construction to a particular structure map, namely the one obtained in the triple of a Stone algebra.
For this particular structure map (as well as for any other particular structure map) the resulting type is no longer a dependent type.
It is just the set of pairs obtained for the given structure map.
\<close>

typedef (overloaded) 'a stone_phi_pair = "triple.pairs (stone_phi::'a::stone_algebra regular \<Rightarrow> 'a dense_filter)"
  using stone_phi.pairs_bot_closed by auto

setup_lifting type_definition_stone_phi_pair

instantiation stone_phi_pair :: (stone_algebra) sup_inf_top_bot_uminus_ord
begin

lift_definition sup_stone_phi_pair :: "'a stone_phi_pair \<Rightarrow> 'a stone_phi_pair \<Rightarrow> 'a stone_phi_pair" is triple.pairs_sup
  using stone_phi.pairs_sup_closed by auto

lift_definition inf_stone_phi_pair :: "'a stone_phi_pair \<Rightarrow> 'a stone_phi_pair \<Rightarrow> 'a stone_phi_pair" is triple.pairs_inf
  using stone_phi.pairs_inf_closed by auto

lift_definition uminus_stone_phi_pair :: "'a stone_phi_pair \<Rightarrow> 'a stone_phi_pair" is "triple.pairs_uminus stone_phi"
  using stone_phi.pairs_uminus_closed by auto

lift_definition bot_stone_phi_pair :: "'a stone_phi_pair" is "triple.pairs_bot"
  by (rule stone_phi.pairs_bot_closed)

lift_definition top_stone_phi_pair :: "'a stone_phi_pair" is "triple.pairs_top"
  by (rule stone_phi.pairs_top_closed)

lift_definition less_eq_stone_phi_pair :: "'a stone_phi_pair \<Rightarrow> 'a stone_phi_pair \<Rightarrow> bool" is triple.pairs_less_eq .

lift_definition less_stone_phi_pair :: "'a stone_phi_pair \<Rightarrow> 'a stone_phi_pair \<Rightarrow> bool" is "\<lambda>xf yf . triple.pairs_less_eq xf yf \<and> \<not> triple.pairs_less_eq yf xf" .

instance ..

end

text \<open>
The result is a Stone algebra and could be proved so by repeating and specialising the above proof for lifted pairs.
We choose a different approach, namely by embedding the type of pairs into the lifted type.
The embedding injects a pair \<open>x\<close> into a function as the value at the given structure map; this makes the embedding injective.
The value of the function at any other structure map needs to be carefully chosen so that the resulting function is a Stone algebra homomorphism.
We use \<open>--x\<close>, which is essentially a projection to the regular element component of \<open>x\<close>, whence the image has the structure of a Boolean algebra.
\<close>

fun stone_phi_embed :: "'a::non_trivial_stone_algebra stone_phi_pair \<Rightarrow> ('a regular,'a dense) lifted_pair"
  where "stone_phi_embed x = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair x else triple.pairs_uminus (Rep_phi f) (triple.pairs_uminus (Rep_phi f) (Rep_stone_phi_pair x)))"

text \<open>
The following lemma shows that in both cases the value of the function is a valid pair for the given structure map.
\<close>

lemma stone_phi_embed_triple_pair:
  "(if Rep_phi f = stone_phi then Rep_stone_phi_pair x else triple.pairs_uminus (Rep_phi f) (triple.pairs_uminus (Rep_phi f) (Rep_stone_phi_pair x))) \<in> triple.pairs (Rep_phi f)"
  by (metis (no_types, hide_lams) Rep_stone_phi_pair simp_phi surj_pair triple.pairs_uminus_closed triple_def)

text \<open>
The following result shows that the embedding preserves the operations of Stone algebras.
Of course, it is not (yet) a Stone algebra homomorphism as we do not know (yet) that the domain of the embedding is a Stone algebra.
To establish the latter is the purpose of the embedding.
\<close>

lemma stone_phi_embed_homomorphism:
  "sup_inf_top_bot_uminus_ord_homomorphism stone_phi_embed"
proof (intro conjI)
  let ?p = "\<lambda>f . triple.pairs_uminus (Rep_phi f)"
  let ?pp = "\<lambda>f x . ?p f (?p f x)"
  let ?q = "\<lambda>f x . ?pp f (Rep_stone_phi_pair x)"
  show "\<forall>x y::'a stone_phi_pair . stone_phi_embed (x \<squnion> y) = stone_phi_embed x \<squnion> stone_phi_embed y"
  proof (intro allI)
    fix x y :: "'a stone_phi_pair"
    have 1: "\<forall>f . triple.pairs_sup (?q f x) (?q f y) = ?q f (x \<squnion> y)"
    proof
      fix f :: "('a regular,'a dense) phi"
      let ?r = "Rep_phi f"
      obtain x1 x2 y1 y2 where 2: "(x1,x2) = Rep_stone_phi_pair x \<and> (y1,y2) = Rep_stone_phi_pair y"
        using prod.collapse by blast
      hence "triple.pairs_sup (?q f x) (?q f y) = triple.pairs_sup (?pp f (x1,x2)) (?pp f (y1,y2))"
        by simp
      also have "... = triple.pairs_sup (--x1,?r (-x1)) (--y1,?r (-y1))"
        by (simp add: triple.pairs_uminus.simps triple_def)
      also have "... = (--x1 \<squnion> --y1,?r (-x1) \<sqinter> ?r (-y1))"
        by simp
      also have "... = (--(x1 \<squnion> y1),?r (-(x1 \<squnion> y1)))"
        by simp
      also have "... = ?pp f (x1 \<squnion> y1,x2 \<sqinter> y2)"
        by (simp add: triple.pairs_uminus.simps triple_def)
      also have "... = ?pp f (triple.pairs_sup (x1,x2) (y1,y2))"
        by simp
      also have "... = ?q f (x \<squnion> y)"
        using 2 by (simp add: sup_stone_phi_pair.rep_eq)
      finally show "triple.pairs_sup (?q f x) (?q f y) = ?q f (x \<squnion> y)"
        .
    qed
    have "stone_phi_embed x \<squnion> stone_phi_embed y = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair x else ?q f x) \<squnion> Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair y else ?q f y)"
      by simp
    also have "... = Abs_lifted_pair (\<lambda>f . triple.pairs_sup (if Rep_phi f = stone_phi then Rep_stone_phi_pair x else ?q f x) (if Rep_phi f = stone_phi then Rep_stone_phi_pair y else ?q f y))"
      by (rule sup_lifted_pair.abs_eq) (simp_all add: eq_onp_same_args stone_phi_embed_triple_pair)
    also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then triple.pairs_sup (Rep_stone_phi_pair x) (Rep_stone_phi_pair y) else triple.pairs_sup (?q f x) (?q f y))"
      by (simp add: if_distrib_2)
    also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then triple.pairs_sup (Rep_stone_phi_pair x) (Rep_stone_phi_pair y) else ?q f (x \<squnion> y))"
      using 1 by meson
    also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair (x \<squnion> y) else ?q f (x \<squnion> y))"
      by (metis sup_stone_phi_pair.rep_eq)
    also have "... = stone_phi_embed (x \<squnion> y)"
      by simp
    finally show "stone_phi_embed (x \<squnion> y) = stone_phi_embed x \<squnion> stone_phi_embed y"
      by simp
  qed
next
  let ?p = "\<lambda>f . triple.pairs_uminus (Rep_phi f)"
  let ?pp = "\<lambda>f x . ?p f (?p f x)"
  let ?q = "\<lambda>f x . ?pp f (Rep_stone_phi_pair x)"
  show "\<forall>x y::'a stone_phi_pair . stone_phi_embed (x \<sqinter> y) = stone_phi_embed x \<sqinter> stone_phi_embed y"
  proof (intro allI)
    fix x y :: "'a stone_phi_pair"
    have 1: "\<forall>f . triple.pairs_inf (?q f x) (?q f y) = ?q f (x \<sqinter> y)"
    proof
      fix f :: "('a regular,'a dense) phi"
      let ?r = "Rep_phi f"
      obtain x1 x2 y1 y2 where 2: "(x1,x2) = Rep_stone_phi_pair x \<and> (y1,y2) = Rep_stone_phi_pair y"
        using prod.collapse by blast
      hence "triple.pairs_inf (?q f x) (?q f y) = triple.pairs_inf (?pp f (x1,x2)) (?pp f (y1,y2))"
        by simp
      also have "... = triple.pairs_inf (--x1,?r (-x1)) (--y1,?r (-y1))"
        by (simp add: triple.pairs_uminus.simps triple_def)
      also have "... = (--x1 \<sqinter> --y1,?r (-x1) \<squnion> ?r (-y1))"
        by simp
      also have "... = (--(x1 \<sqinter> y1),?r (-(x1 \<sqinter> y1)))"
        by simp
      also have "... = ?pp f (x1 \<sqinter> y1,x2 \<squnion> y2)"
        by (simp add: triple.pairs_uminus.simps triple_def)
      also have "... = ?pp f (triple.pairs_inf (x1,x2) (y1,y2))"
        by simp
      also have "... = ?q f (x \<sqinter> y)"
        using 2 by (simp add: inf_stone_phi_pair.rep_eq)
      finally show "triple.pairs_inf (?q f x) (?q f y) = ?q f (x \<sqinter> y)"
        .
    qed
    have "stone_phi_embed x \<sqinter> stone_phi_embed y = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair x else ?q f x) \<sqinter> Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair y else ?q f y)"
      by simp
    also have "... = Abs_lifted_pair (\<lambda>f . triple.pairs_inf (if Rep_phi f = stone_phi then Rep_stone_phi_pair x else ?q f x) (if Rep_phi f = stone_phi then Rep_stone_phi_pair y else ?q f y))"
      by (rule inf_lifted_pair.abs_eq) (simp_all add: eq_onp_same_args stone_phi_embed_triple_pair)
    also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then triple.pairs_inf (Rep_stone_phi_pair x) (Rep_stone_phi_pair y) else triple.pairs_inf (?q f x) (?q f y))"
      by (simp add: if_distrib_2)
    also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then triple.pairs_inf (Rep_stone_phi_pair x) (Rep_stone_phi_pair y) else ?q f (x \<sqinter> y))"
      using 1 by meson
    also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair (x \<sqinter> y) else ?q f (x \<sqinter> y))"
      by (metis inf_stone_phi_pair.rep_eq)
    also have "... = stone_phi_embed (x \<sqinter> y)"
      by simp
    finally show "stone_phi_embed (x \<sqinter> y) = stone_phi_embed x \<sqinter> stone_phi_embed y"
      by simp
  qed
next
  have "stone_phi_embed (top::'a stone_phi_pair) = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair top else triple.pairs_uminus (Rep_phi f) (triple.pairs_uminus (Rep_phi f) (Rep_stone_phi_pair top)))"
    by simp
  also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then (top,bot) else triple.pairs_uminus (Rep_phi f) (triple.pairs_uminus (Rep_phi f) (top,bot)))"
    by (metis (no_types, hide_lams) bot_filter.abs_eq top_stone_phi_pair.rep_eq)
  also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then (top,bot) else triple.pairs_uminus (Rep_phi f) (bot,top))"
    by (metis (no_types, hide_lams) dense_closed_top simp_phi triple.pairs_uminus.simps triple_def)
  also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then (top,bot) else (top,bot))"
    by (metis (no_types, hide_lams) p_bot simp_phi triple.pairs_uminus.simps triple_def)
  also have "... = Abs_lifted_pair (\<lambda>f . (top,Abs_filter {top}))"
    by (simp add: bot_filter.abs_eq)
  also have "... = top"
    by (rule top_lifted_pair.abs_eq[THEN sym])
  finally show "stone_phi_embed (top::'a stone_phi_pair) = top"
    .
next
  have "stone_phi_embed (bot::'a stone_phi_pair) = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair bot else triple.pairs_uminus (Rep_phi f) (triple.pairs_uminus (Rep_phi f) (Rep_stone_phi_pair bot)))"
    by simp
  also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then (bot,top) else triple.pairs_uminus (Rep_phi f) (triple.pairs_uminus (Rep_phi f) (bot,top)))"
    by (metis (no_types, hide_lams) top_filter.abs_eq bot_stone_phi_pair.rep_eq)
  also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then (bot,top) else triple.pairs_uminus (Rep_phi f) (top,bot))"
    by (metis (no_types, hide_lams) p_bot simp_phi triple.pairs_uminus.simps triple_def)
  also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then (bot,top) else (bot,top))"
    by (metis (no_types, hide_lams) p_top simp_phi triple.pairs_uminus.simps triple_def)
  also have "... = Abs_lifted_pair (\<lambda>f . (bot,Abs_filter UNIV))"
    by (simp add: top_filter.abs_eq)
  also have "... = bot"
    by (rule bot_lifted_pair.abs_eq[THEN sym])
  finally show "stone_phi_embed (bot::'a stone_phi_pair) = bot"
    .
next
  let ?p = "\<lambda>f . triple.pairs_uminus (Rep_phi f)"
  let ?pp = "\<lambda>f x . ?p f (?p f x)"
  let ?q = "\<lambda>f x . ?pp f (Rep_stone_phi_pair x)"
  show "\<forall>x::'a stone_phi_pair . stone_phi_embed (-x) = -stone_phi_embed x"
  proof (intro allI)
    fix x :: "'a stone_phi_pair"
    have 1: "\<forall>f . triple.pairs_uminus (Rep_phi f) (?q f x) = ?q f (-x)"
    proof
      fix f :: "('a regular,'a dense) phi"
      let ?r = "Rep_phi f"
      obtain x1 x2 where 2: "(x1,x2) = Rep_stone_phi_pair x"
        using prod.collapse by blast
      hence "triple.pairs_uminus (Rep_phi f) (?q f x) = triple.pairs_uminus (Rep_phi f) (?pp f (x1,x2))"
        by simp
      also have "... = triple.pairs_uminus (Rep_phi f) (--x1,?r (-x1))"
        by (simp add: triple.pairs_uminus.simps triple_def)
      also have "... = (---x1,?r (--x1))"
        by (simp add: triple.pairs_uminus.simps triple_def)
      also have "... = ?pp f (-x1,stone_phi x1)"
        by (simp add: triple.pairs_uminus.simps triple_def)
      also have "... = ?pp f (triple.pairs_uminus stone_phi (x1,x2))"
        by simp
      also have "... = ?q f (-x)"
        using 2 by (simp add: uminus_stone_phi_pair.rep_eq)
      finally show "triple.pairs_uminus (Rep_phi f) (?q f x) = ?q f (-x)"
        .
    qed
    have "-stone_phi_embed x = -Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair x else ?q f x)"
      by simp
    also have "... = Abs_lifted_pair (\<lambda>f . triple.pairs_uminus (Rep_phi f) (if Rep_phi f = stone_phi then Rep_stone_phi_pair x else ?q f x))"
      by (rule uminus_lifted_pair.abs_eq) (simp_all add: eq_onp_same_args stone_phi_embed_triple_pair)
    also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then triple.pairs_uminus (Rep_phi f) (Rep_stone_phi_pair x) else triple.pairs_uminus (Rep_phi f) (?q f x))"
      by (simp add: if_distrib)
    also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then triple.pairs_uminus (Rep_phi f) (Rep_stone_phi_pair x) else ?q f (-x))"
      using 1 by meson
    also have "... = Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair (-x) else ?q f (-x))"
      by (metis uminus_stone_phi_pair.rep_eq)
    also have "... = stone_phi_embed (-x)"
      by simp
    finally show "stone_phi_embed (-x) = -stone_phi_embed x"
      by simp
  qed
next
  let ?p = "\<lambda>f . triple.pairs_uminus (Rep_phi f)"
  let ?pp = "\<lambda>f x . ?p f (?p f x)"
  let ?q = "\<lambda>f x . ?pp f (Rep_stone_phi_pair x)"
  show "\<forall>x y::'a stone_phi_pair . x \<le> y \<longrightarrow> stone_phi_embed x \<le> stone_phi_embed y"
  proof (intro allI, rule impI)
    fix x y :: "'a stone_phi_pair"
    assume 1: "x \<le> y"
    have "\<forall>f . triple.pairs_less_eq (if Rep_phi f = stone_phi then Rep_stone_phi_pair x else ?q f x) (if Rep_phi f = stone_phi then Rep_stone_phi_pair y else ?q f y)"
    proof
      fix f :: "('a regular,'a dense) phi"
      let ?r = "Rep_phi f"
      obtain x1 x2 y1 y2 where 2: "(x1,x2) = Rep_stone_phi_pair x \<and> (y1,y2) = Rep_stone_phi_pair y"
        using prod.collapse by blast
      have "x1 \<le> y1"
        using 1 2 by (metis less_eq_stone_phi_pair.rep_eq stone_phi.pairs_less_eq.simps)
      hence "--x1 \<le> --y1 \<and> ?r (-y1) \<le> ?r (-x1)"
        by (metis compl_le_compl_iff le_iff_sup simp_phi)
      hence "triple.pairs_less_eq (--x1,?r (-x1)) (--y1,?r (-y1))"
        by simp
      hence "triple.pairs_less_eq (?pp f (x1,x2)) (?pp f (y1,y2))"
        by (simp add: triple.pairs_uminus.simps triple_def)
      hence "triple.pairs_less_eq (?q f x) (?q f y)"
        using 2 by simp
      hence "if ?r = stone_phi then triple.pairs_less_eq (Rep_stone_phi_pair x) (Rep_stone_phi_pair y) else triple.pairs_less_eq (?q f x) (?q f y)"
        using 1 by (simp add: less_eq_stone_phi_pair.rep_eq)
      thus "triple.pairs_less_eq (if ?r = stone_phi then Rep_stone_phi_pair x else ?q f x) (if ?r = stone_phi then Rep_stone_phi_pair y else ?q f y)"
        by (simp add: if_distrib_2)
    qed
    hence "Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair x else ?q f x) \<le> Abs_lifted_pair (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair y else ?q f y)"
      by (subst less_eq_lifted_pair.abs_eq) (simp_all add: eq_onp_same_args stone_phi_embed_triple_pair)
    thus "stone_phi_embed x \<le> stone_phi_embed y"
      by simp
  qed
qed

text \<open>
The following lemmas show that the embedding is injective and reflects the order.
The latter allows us to easily inherit properties involving inequalities from the target of the embedding, without transforming them to equations.
\<close>

lemma stone_phi_embed_injective:
  "inj stone_phi_embed"
proof (rule injI)
  fix x y :: "'a stone_phi_pair"
  have 1: "Rep_phi (Abs_phi stone_phi) = stone_phi"
    by (simp add: Abs_phi_inverse stone_phi.hom)
  assume 2: "stone_phi_embed x = stone_phi_embed y"
  have "\<forall>x::'a stone_phi_pair . Rep_lifted_pair (stone_phi_embed x) = (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair x else triple.pairs_uminus (Rep_phi f) (triple.pairs_uminus (Rep_phi f) (Rep_stone_phi_pair x)))"
    by (simp add: Abs_lifted_pair_inverse stone_phi_embed_triple_pair)
  hence "(\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair x else triple.pairs_uminus (Rep_phi f) (triple.pairs_uminus (Rep_phi f) (Rep_stone_phi_pair x))) = (\<lambda>f . if Rep_phi f = stone_phi then Rep_stone_phi_pair y else triple.pairs_uminus (Rep_phi f) (triple.pairs_uminus (Rep_phi f) (Rep_stone_phi_pair y)))"
    using 2 by metis
  hence "Rep_stone_phi_pair x = Rep_stone_phi_pair y"
    using 1 by metis
  thus "x = y"
    by (simp add: Rep_stone_phi_pair_inject)
qed

lemma stone_phi_embed_order_injective:
  assumes "stone_phi_embed x \<le> stone_phi_embed y"
    shows "x \<le> y"
proof -
  let ?f = "Abs_phi stone_phi"
  have "\<forall>f . triple.pairs_less_eq (if Rep_phi f = stone_phi then Rep_stone_phi_pair x else triple.pairs_uminus (Rep_phi f) (triple.pairs_uminus (Rep_phi f) (Rep_stone_phi_pair x))) (if Rep_phi f = stone_phi then Rep_stone_phi_pair y else triple.pairs_uminus (Rep_phi f) (triple.pairs_uminus (Rep_phi f) (Rep_stone_phi_pair y)))"
    using assms by (subst less_eq_lifted_pair.abs_eq[THEN sym]) (simp_all add: eq_onp_same_args stone_phi_embed_triple_pair)
  hence "triple.pairs_less_eq (if Rep_phi ?f = (stone_phi::'a regular \<Rightarrow> 'a dense_filter) then Rep_stone_phi_pair x else triple.pairs_uminus (Rep_phi ?f) (triple.pairs_uminus (Rep_phi ?f) (Rep_stone_phi_pair x))) (if Rep_phi ?f = (stone_phi::'a regular \<Rightarrow> 'a dense_filter) then Rep_stone_phi_pair y else triple.pairs_uminus (Rep_phi ?f) (triple.pairs_uminus (Rep_phi ?f) (Rep_stone_phi_pair y)))"
    by simp
  hence "triple.pairs_less_eq (Rep_stone_phi_pair x) (Rep_stone_phi_pair y)"
    by (simp add: Abs_phi_inverse stone_phi.hom)
  thus "x \<le> y"
    by (simp add: less_eq_stone_phi_pair.rep_eq)
qed

text \<open>
Now all Stone algebra axioms can be inherited using the embedding.
This is due to the fact that the axioms are universally quantified equations or conditional equations (or inequalities); this is called a quasivariety in universal algebra.
It would be useful to have this construction available for arbitrary quasivarieties.
\<close>

instantiation stone_phi_pair :: (non_trivial_stone_algebra) stone_algebra
begin

instance
  apply intro_classes
  apply (simp add: less_stone_phi_pair.rep_eq less_eq_stone_phi_pair.rep_eq)
  apply (simp add: stone_phi_embed_order_injective)
  apply (meson order.trans stone_phi_embed_homomorphism stone_phi_embed_order_injective)
  apply (meson stone_phi_embed_homomorphism antisym stone_phi_embed_injective injD)
  apply (metis inf.sup_ge1 stone_phi_embed_homomorphism stone_phi_embed_order_injective)
  apply (metis inf.sup_ge2 stone_phi_embed_homomorphism stone_phi_embed_order_injective)
  apply (metis inf_greatest stone_phi_embed_homomorphism stone_phi_embed_order_injective)
  apply (metis stone_phi_embed_homomorphism stone_phi_embed_order_injective sup_ge1)
  apply (metis stone_phi_embed_homomorphism stone_phi_embed_order_injective sup.cobounded2)
  apply (metis stone_phi_embed_homomorphism stone_phi_embed_order_injective sup_least)
  apply (metis bot.extremum stone_phi_embed_homomorphism stone_phi_embed_order_injective)
  apply (metis stone_phi_embed_homomorphism stone_phi_embed_order_injective top_greatest)
  apply (metis (mono_tags, lifting) stone_phi_embed_homomorphism sup_inf_distrib1 stone_phi_embed_injective injD)
  apply (metis stone_phi_embed_homomorphism stone_phi_embed_injective injD stone_phi_embed_order_injective pseudo_complement)
  by (metis injD stone_phi_embed_homomorphism stone_phi_embed_injective stone)

end

subsection \<open>Stone Algebra Isomorphism\<close>

text \<open>
In this section we prove that the Stone algebra of the triple of a Stone algebra is isomorphic to the original Stone algebra.
The following two definitions give the isomorphism.
\<close>

abbreviation sa_iso_inv :: "'a::non_trivial_stone_algebra stone_phi_pair \<Rightarrow> 'a"
  where "sa_iso_inv \<equiv> \<lambda>p . Rep_regular (fst (Rep_stone_phi_pair p)) \<sqinter> Rep_dense (triple.rho_pair stone_phi (Rep_stone_phi_pair p))"

abbreviation sa_iso :: "'a::non_trivial_stone_algebra \<Rightarrow> 'a stone_phi_pair"
  where "sa_iso \<equiv> \<lambda>x . Abs_stone_phi_pair (Abs_regular (--x),stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x)))"

lemma sa_iso_triple_pair:
  "(Abs_regular (--x),stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) \<in> triple.pairs stone_phi"
  by (metis (mono_tags, lifting) double_compl eq_onp_same_args stone_phi.sa_iso_pair uminus_regular.abs_eq)

lemma stone_phi_inf_dense:
  "stone_phi (Abs_regular (-x)) \<sqinter> up_filter (Abs_dense (y \<squnion> -y)) \<le> up_filter (Abs_dense (y \<squnion> -y \<squnion> x))"
proof -
  have "Rep_filter (stone_phi (Abs_regular (-x)) \<sqinter> up_filter (Abs_dense (y \<squnion> -y))) \<le> \<up>(Abs_dense (y \<squnion> -y \<squnion> x))"
  proof
    fix z :: "'a dense"
    let ?r = "Rep_dense z"
    assume "z \<in> Rep_filter (stone_phi (Abs_regular (-x)) \<sqinter> up_filter (Abs_dense (y \<squnion> -y)))"
    also have "... = Rep_filter (stone_phi (Abs_regular (-x))) \<inter> Rep_filter (up_filter (Abs_dense (y \<squnion> -y)))"
      by (simp add: inf_filter.rep_eq)
    also have "... = stone_phi_set (Abs_regular (-x)) \<inter> \<up>(Abs_dense (y \<squnion> -y))"
      by (metis Abs_filter_inverse mem_Collect_eq up_filter stone_phi_set_filter stone_phi_def)
    finally have "--x \<le> ?r \<and> Abs_dense (y \<squnion> -y) \<le> z"
      by (metis (mono_tags, lifting) Abs_regular_inverse Int_Collect mem_Collect_eq)
    hence "--x \<le> ?r \<and> y \<squnion> -y \<le> ?r"
      by (simp add: Abs_dense_inverse less_eq_dense.rep_eq)
    hence "y \<squnion> -y \<squnion> x \<le> ?r"
      using order_trans pp_increasing by auto
    hence "Abs_dense (y \<squnion> -y \<squnion> x) \<le> Abs_dense ?r"
      by (subst less_eq_dense.abs_eq) (simp_all add: eq_onp_same_args)
    thus "z \<in> \<up>(Abs_dense (y \<squnion> -y \<squnion> x))"
      by (simp add: Rep_dense_inverse)
  qed
  hence "Abs_filter (Rep_filter (stone_phi (Abs_regular (-x)) \<sqinter> up_filter (Abs_dense (y \<squnion> -y)))) \<le> up_filter (Abs_dense (y \<squnion> -y \<squnion> x))"
    by (simp add: eq_onp_same_args less_eq_filter.abs_eq)
  thus ?thesis
    by (simp add: Rep_filter_inverse)
qed

lemma stone_phi_complement:
  "complement (stone_phi (Abs_regular (-x))) (stone_phi (Abs_regular (--x)))"
  by (metis (mono_tags, lifting) eq_onp_same_args stone_phi.phi_complemented uminus_regular.abs_eq)

lemma up_dense_stone_phi:
  "up_filter (Abs_dense (x \<squnion> -x)) \<le> stone_phi (Abs_regular (--x))"
proof -
  have "\<up>(Abs_dense (x \<squnion> -x)) \<le> stone_phi_set (Abs_regular (--x))"
  proof
    fix z :: "'a dense"
    let ?r = "Rep_dense z"
    assume "z \<in> \<up>(Abs_dense (x \<squnion> -x))"
    hence "---x \<le> ?r"
      by (simp add: Abs_dense_inverse less_eq_dense.rep_eq)
    hence "-Rep_regular (Abs_regular (--x)) \<le> ?r"
      by (metis (mono_tags, lifting) Abs_regular_inverse mem_Collect_eq)
    thus "z \<in> stone_phi_set (Abs_regular (--x))"
      by simp
  qed
  thus ?thesis
    by (unfold stone_phi_def, subst less_eq_filter.abs_eq, simp_all add: eq_onp_same_args stone_phi_set_filter)
qed

text \<open>
The following two results prove that the isomorphisms are mutually inverse.
\<close>

lemma sa_iso_left_invertible:
  "sa_iso_inv (sa_iso x) = x"
proof -
  have "up_filter (triple.rho_pair stone_phi (Abs_regular (--x),stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x)))) = stone_phi (Abs_regular (--x)) \<sqinter> (stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x)))"
    using sa_iso_triple_pair stone_phi.get_rho_pair_char by blast
  also have "... = stone_phi (Abs_regular (--x)) \<sqinter> up_filter (Abs_dense (x \<squnion> -x))"
    by (simp add: inf.sup_commute inf_sup_distrib1 stone_phi_complement)
  also have "... = up_filter (Abs_dense (x \<squnion> -x))"
    using up_dense_stone_phi inf.absorb2 by auto
  finally have 1: "triple.rho_pair stone_phi (Abs_regular (--x),stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) = Abs_dense (x \<squnion> -x)"
    using up_filter_injective by auto
  have "sa_iso_inv (sa_iso x) = (\<lambda>p . Rep_regular (fst p) \<sqinter> Rep_dense (triple.rho_pair stone_phi p)) (Abs_regular (--x),stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x)))"
    by (simp add: Abs_stone_phi_pair_inverse sa_iso_triple_pair)
  also have "... = Rep_regular (Abs_regular (--x)) \<sqinter> Rep_dense (triple.rho_pair stone_phi (Abs_regular (--x),stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))))"
    by simp
  also have "... = --x \<sqinter> Rep_dense (Abs_dense (x \<squnion> -x))"
    using 1 by (subst Abs_regular_inverse) auto
  also have "... = --x \<sqinter> (x \<squnion> -x)"
    by (subst Abs_dense_inverse) simp_all
  also have "... = x"
    by simp
  finally show ?thesis
    by auto
qed

lemma sa_iso_right_invertible:
  "sa_iso (sa_iso_inv p) = p"
proof -
  obtain x y where 1: "(x,y) = Rep_stone_phi_pair p"
    using prod.collapse by blast
  hence 2: "(x,y) \<in> triple.pairs stone_phi"
    by (simp add: Rep_stone_phi_pair)
  hence 3: "stone_phi (-x) \<le> y"
    by (simp add: stone_phi.pairs_phi_less_eq)
  have 4: "\<forall>z . z \<in> Rep_filter (stone_phi x \<sqinter> y) \<longrightarrow> -Rep_regular x \<le> Rep_dense z"
  proof (rule allI, rule impI)
    fix z :: "'a dense"
    let ?r = "Rep_dense z"
    assume "z \<in> Rep_filter (stone_phi x \<sqinter> y)"
    hence "z \<in> Rep_filter (stone_phi x)"
      by (simp add: inf_filter.rep_eq)
    also have "... = stone_phi_set x"
      by (simp add: stone_phi_def Abs_filter_inverse stone_phi_set_filter)
    finally show "-Rep_regular x \<le> ?r"
      by simp
  qed
  have "triple.rho_pair stone_phi (x,y) \<in> \<up>(triple.rho_pair stone_phi (x,y))"
    by simp
  also have "... = Rep_filter (Abs_filter (\<up>(triple.rho_pair stone_phi (x,y))))"
    by (simp add: Abs_filter_inverse)
  also have "... = Rep_filter (stone_phi x \<sqinter> y)"
    using 2 stone_phi.get_rho_pair_char by fastforce
  finally have "triple.rho_pair stone_phi (x,y) \<in> Rep_filter (stone_phi x \<sqinter> y)"
    by simp
  hence 5: "-Rep_regular x \<le> Rep_dense (triple.rho_pair stone_phi (x,y))"
    using 4 by simp
  have 6: "sa_iso_inv p = Rep_regular x \<sqinter> Rep_dense (triple.rho_pair stone_phi (x,y))"
    using 1 by (metis fstI)
  hence "-sa_iso_inv p = -Rep_regular x"
    by simp
  hence "sa_iso (sa_iso_inv p) = Abs_stone_phi_pair (Abs_regular (--Rep_regular x),stone_phi (Abs_regular (-Rep_regular x)) \<squnion> up_filter (Abs_dense ((Rep_regular x \<sqinter> Rep_dense (triple.rho_pair stone_phi (x,y))) \<squnion> -Rep_regular x)))"
    using 6 by simp
  also have "... = Abs_stone_phi_pair (x,stone_phi (-x) \<squnion> up_filter (Abs_dense ((Rep_regular x \<sqinter> Rep_dense (triple.rho_pair stone_phi (x,y))) \<squnion> -Rep_regular x)))"
    by (metis (mono_tags, lifting) Rep_regular_inverse double_compl uminus_regular.rep_eq)
  also have "... = Abs_stone_phi_pair (x,stone_phi (-x) \<squnion> up_filter (Abs_dense (Rep_dense (triple.rho_pair stone_phi (x,y)) \<squnion> -Rep_regular x)))"
    by (metis inf_sup_aci(5) maddux_3_21_pp simp_regular)
  also have "... = Abs_stone_phi_pair (x,stone_phi (-x) \<squnion> up_filter (Abs_dense (Rep_dense (triple.rho_pair stone_phi (x,y)))))"
    using 5 by (simp add: sup.absorb1)
  also have "... = Abs_stone_phi_pair (x,stone_phi (-x) \<squnion> up_filter (triple.rho_pair stone_phi (x,y)))"
    by (simp add: Rep_dense_inverse)
  also have "... = Abs_stone_phi_pair (x,stone_phi (-x) \<squnion> (stone_phi x \<sqinter> y))"
    using 2 stone_phi.get_rho_pair_char by fastforce
  also have "... = Abs_stone_phi_pair (x,stone_phi (-x) \<squnion> y)"
    by (simp add: stone_phi.phi_complemented sup.commute sup_inf_distrib1)
  also have "... = Abs_stone_phi_pair (x,y)"
    using 3 by (simp add: le_iff_sup)
  also have "... = p"
    using 1 by (simp add: Rep_stone_phi_pair_inverse)
  finally show ?thesis
    .
qed

text \<open>
It remains to show the homomorphism properties, which is done in the following result.
\<close>

lemma sa_iso:
  "stone_algebra_isomorphism sa_iso"
proof (intro conjI)
  have "Abs_stone_phi_pair (Abs_regular (--bot),stone_phi (Abs_regular (-bot)) \<squnion> up_filter (Abs_dense (bot \<squnion> -bot))) = Abs_stone_phi_pair (bot,stone_phi top \<squnion> up_filter top)"
    by (simp add: bot_regular.abs_eq top_regular.abs_eq top_dense.abs_eq)
  also have "... = Abs_stone_phi_pair (bot,stone_phi top)"
    by (simp add: stone_phi.hom)
  also have "... = bot"
    by (simp add: bot_stone_phi_pair_def stone_phi.phi_top)
  finally show "sa_iso bot = bot"
    .
next
  have "Abs_stone_phi_pair (Abs_regular (--top),stone_phi (Abs_regular (-top)) \<squnion> up_filter (Abs_dense (top \<squnion> -top))) = Abs_stone_phi_pair (top,stone_phi bot \<squnion> up_filter top)"
    by (simp add: bot_regular.abs_eq top_regular.abs_eq top_dense.abs_eq)
  also have "... = top"
    by (simp add: stone_phi.phi_bot top_stone_phi_pair_def)
  finally show "sa_iso top = top"
    .
next
  have 1: "\<forall>x y::'a . dense (x \<squnion> -x \<squnion> y)"
    by simp
  have 2: "\<forall>x y::'a . up_filter (Abs_dense (x \<squnion> -x \<squnion> y)) \<le> (stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) \<sqinter> (stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y)))"
  proof (intro allI)
    fix x y :: 'a
    let ?u = "Abs_dense (x \<squnion> -x \<squnion> --y)"
    let ?v = "Abs_dense (y \<squnion> -y)"
    have "\<up>(Abs_dense (x \<squnion> -x \<squnion> y)) \<le> Rep_filter (stone_phi (Abs_regular (-y)) \<squnion> up_filter ?v)"
    proof
      fix z
      assume "z \<in> \<up>(Abs_dense (x \<squnion> -x \<squnion> y))"
      hence "Abs_dense (x \<squnion> -x \<squnion> y) \<le> z"
        by simp
      hence 3: "x \<squnion> -x \<squnion> y \<le> Rep_dense z"
        by (simp add: Abs_dense_inverse less_eq_dense.rep_eq)
      have "y \<le> x \<squnion> -x \<squnion> --y"
        by (simp add: le_supI2 pp_increasing)
      hence "(x \<squnion> -x \<squnion> --y) \<sqinter> (y \<squnion> -y) = y \<squnion> ((x \<squnion> -x \<squnion> --y) \<sqinter> -y)"
        by (simp add: le_iff_sup sup_inf_distrib1)
      also have "... = y \<squnion> ((x \<squnion> -x) \<sqinter> -y)"
        by (simp add: inf_commute inf_sup_distrib1)
      also have "... \<le> Rep_dense z"
        using 3 by (meson le_infI1 sup.bounded_iff)
      finally have "Abs_dense ((x \<squnion> -x \<squnion> --y) \<sqinter> (y \<squnion> -y)) \<le> z"
        by (simp add: Abs_dense_inverse less_eq_dense.rep_eq)
      hence 4: "?u \<sqinter> ?v \<le> z"
        by (simp add: eq_onp_same_args inf_dense.abs_eq)
      have "-Rep_regular (Abs_regular (-y)) = --y"
        by (metis (mono_tags, lifting) mem_Collect_eq Abs_regular_inverse)
      also have "... \<le> Rep_dense ?u"
        by (simp add: Abs_dense_inverse)
      finally have "?u \<in> stone_phi_set (Abs_regular (-y))"
        by simp
      hence 5: "?u \<in> Rep_filter (stone_phi (Abs_regular (-y)))"
        by (metis mem_Collect_eq stone_phi_def stone_phi_set_filter Abs_filter_inverse)
      have "?v \<in> \<up>?v"
        by simp
      hence "?v \<in> Rep_filter (up_filter ?v)"
        by (metis Abs_filter_inverse mem_Collect_eq up_filter)
      thus "z \<in> Rep_filter (stone_phi (Abs_regular (-y)) \<squnion> up_filter ?v)"
        using 4 5 sup_filter.rep_eq by blast
    qed
    hence "up_filter (Abs_dense (x \<squnion> -x \<squnion> y)) \<le> Abs_filter (Rep_filter (stone_phi (Abs_regular (-y)) \<squnion> up_filter ?v))"
      by (simp add: eq_onp_same_args less_eq_filter.abs_eq)
    also have "... = stone_phi (Abs_regular (-y)) \<squnion> up_filter ?v"
      by (simp add: Rep_filter_inverse)
    finally show "up_filter (Abs_dense (x \<squnion> -x \<squnion> y)) \<le> (stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) \<sqinter> (stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y)))"
      by (metis le_infI le_supI2 sup_bot.right_neutral up_filter_dense_antitone)
  qed
  have 6: "\<forall>x::'a . in_p_image (-x)"
    by auto
  show "\<forall>x y::'a . sa_iso (x \<squnion> y) = sa_iso x \<squnion> sa_iso y"
  proof (intro allI)
    fix x y :: 'a
    have 7: "up_filter (Abs_dense (x \<squnion> -x)) \<sqinter> up_filter (Abs_dense (y \<squnion> -y)) \<le> up_filter (Abs_dense (y \<squnion> -y \<squnion> x))"
    proof -
      have "up_filter (Abs_dense (x \<squnion> -x)) \<sqinter> up_filter (Abs_dense (y \<squnion> -y)) = up_filter (Abs_dense (x \<squnion> -x) \<squnion> Abs_dense (y \<squnion> -y))"
        by (metis up_filter_dist_sup)
      also have "... = up_filter (Abs_dense (x \<squnion> -x \<squnion> (y \<squnion> -y)))"
        by (subst sup_dense.abs_eq) (simp_all add: eq_onp_same_args)
      also have "... = up_filter (Abs_dense (y \<squnion> -y \<squnion> x \<squnion> -x))"
        by (simp add: sup_commute sup_left_commute)
      also have "... \<le> up_filter (Abs_dense (y \<squnion> -y \<squnion> x))"
        using up_filter_dense_antitone by auto
      finally show ?thesis
        .
    qed
    have "Abs_dense (x \<squnion> y \<squnion> -(x \<squnion> y)) = Abs_dense ((x \<squnion> -x \<squnion> y) \<sqinter> (y \<squnion> -y \<squnion> x))"
      by (simp add: sup_commute sup_inf_distrib1 sup_left_commute)
    also have "... = Abs_dense (x \<squnion> -x \<squnion> y) \<sqinter> Abs_dense (y \<squnion> -y \<squnion> x)"
      using 1 by (metis (mono_tags, lifting) Abs_dense_inverse Rep_dense_inverse inf_dense.rep_eq mem_Collect_eq)
    finally have 8: "up_filter (Abs_dense (x \<squnion> y \<squnion> -(x \<squnion> y))) = up_filter (Abs_dense (x \<squnion> -x \<squnion> y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y \<squnion> x))"
      by (simp add: up_filter_dist_inf)
    also have "... \<le> (stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) \<sqinter> (stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y)))"
      using 2 by (simp add: inf.sup_commute le_sup_iff)
    finally have 9: "(stone_phi (Abs_regular (-x)) \<sqinter> stone_phi (Abs_regular (-y))) \<squnion> up_filter (Abs_dense (x \<squnion> y \<squnion> -(x \<squnion> y))) \<le> ..."
      by (simp add: le_supI1)
    have "... = (stone_phi (Abs_regular (-x)) \<sqinter> stone_phi (Abs_regular (-y))) \<squnion> (stone_phi (Abs_regular (-x)) \<sqinter> up_filter (Abs_dense (y \<squnion> -y))) \<squnion> ((up_filter (Abs_dense (x \<squnion> -x)) \<sqinter> stone_phi (Abs_regular (-y))) \<squnion> (up_filter (Abs_dense (x \<squnion> -x)) \<sqinter> up_filter (Abs_dense (y \<squnion> -y))))"
      by (metis (no_types) inf_sup_distrib1 inf_sup_distrib2)
    also have "... \<le> (stone_phi (Abs_regular (-x)) \<sqinter> stone_phi (Abs_regular (-y))) \<squnion> up_filter (Abs_dense (y \<squnion> -y \<squnion> x)) \<squnion> ((up_filter (Abs_dense (x \<squnion> -x)) \<sqinter> stone_phi (Abs_regular (-y))) \<squnion> (up_filter (Abs_dense (x \<squnion> -x)) \<sqinter> up_filter (Abs_dense (y \<squnion> -y))))"
      by (meson sup_left_isotone sup_right_isotone stone_phi_inf_dense)
    also have "... \<le> (stone_phi (Abs_regular (-x)) \<sqinter> stone_phi (Abs_regular (-y))) \<squnion> up_filter (Abs_dense (y \<squnion> -y \<squnion> x)) \<squnion> (up_filter (Abs_dense (x \<squnion> -x \<squnion> y)) \<squnion> (up_filter (Abs_dense (x \<squnion> -x)) \<sqinter> up_filter (Abs_dense (y \<squnion> -y))))"
      by (metis inf.commute sup_left_isotone sup_right_isotone stone_phi_inf_dense)
    also have "... \<le> (stone_phi (Abs_regular (-x)) \<sqinter> stone_phi (Abs_regular (-y))) \<squnion> up_filter (Abs_dense (y \<squnion> -y \<squnion> x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x \<squnion> y))"
      using 7 by (simp add: sup.absorb1 sup_commute sup_left_commute)
    also have "... = (stone_phi (Abs_regular (-x)) \<sqinter> stone_phi (Abs_regular (-y))) \<squnion> up_filter (Abs_dense (x \<squnion> y \<squnion> -(x \<squnion> y)))"
      using 8 by (simp add: sup.commute sup.left_commute)
    finally have "(stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) \<sqinter> (stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y))) = ..."
      using 9 using antisym by blast
    also have "... = stone_phi (Abs_regular (-x) \<sqinter> Abs_regular (-y)) \<squnion> up_filter (Abs_dense (x \<squnion> y \<squnion> -(x \<squnion> y)))"
      by (simp add: stone_phi.hom)
    also have "... = stone_phi (Abs_regular (-(x \<squnion> y))) \<squnion> up_filter (Abs_dense (x \<squnion> y \<squnion> -(x \<squnion> y)))"
      using 6 by (subst inf_regular.abs_eq) (simp_all add: eq_onp_same_args)
    finally have 10: "stone_phi (Abs_regular (-(x \<squnion> y))) \<squnion> up_filter (Abs_dense (x \<squnion> y \<squnion> -(x \<squnion> y))) = (stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) \<sqinter> (stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y)))"
      by simp
    have "Abs_regular (--(x \<squnion> y)) = Abs_regular (--x) \<squnion> Abs_regular (--y)"
      using 6 by (subst sup_regular.abs_eq) (simp_all add: eq_onp_same_args)
    hence "Abs_stone_phi_pair (Abs_regular (--(x \<squnion> y)),stone_phi (Abs_regular (-(x \<squnion> y))) \<squnion> up_filter (Abs_dense (x \<squnion> y \<squnion> -(x \<squnion> y)))) = Abs_stone_phi_pair (triple.pairs_sup (Abs_regular (--x),stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) (Abs_regular (--y),stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y))))"
      using 10 by auto
    also have "... = Abs_stone_phi_pair (Abs_regular (--x),stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) \<squnion> Abs_stone_phi_pair (Abs_regular (--y),stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y)))"
      by (rule sup_stone_phi_pair.abs_eq[THEN sym]) (simp_all add: eq_onp_same_args sa_iso_triple_pair)
    finally show "sa_iso (x \<squnion> y) = sa_iso x \<squnion> sa_iso y"
      .
  qed
next
  have 1: "\<forall>x y::'a . dense (x \<squnion> -x \<squnion> y)"
    by simp
  have 2: "\<forall>x::'a . in_p_image (-x)"
    by auto
  have 3: "\<forall>x y::'a . stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (x \<squnion> -x)) = stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (x \<squnion> -x \<squnion> -y))"
  proof (intro allI)
    fix x y :: 'a
    have 4: "up_filter (Abs_dense (x \<squnion> -x)) \<le> stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (x \<squnion> -x \<squnion> -y))"
      by (metis (no_types, lifting) complement_shunting stone_phi_inf_dense stone_phi_complement complement_symmetric)
    have "up_filter (Abs_dense (x \<squnion> -x \<squnion> -y)) \<le> up_filter (Abs_dense (x \<squnion> -x))"
      by (metis sup_idem up_filter_dense_antitone)
    thus "stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (x \<squnion> -x)) = stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (x \<squnion> -x \<squnion> -y))"
      using 4 by (simp add: le_iff_sup sup_commute sup_left_commute)
  qed
  show "\<forall>x y::'a . sa_iso (x \<sqinter> y) = sa_iso x \<sqinter> sa_iso y"
  proof (intro allI)
    fix x y :: 'a
    have "Abs_dense ((x \<sqinter> y) \<squnion> -(x \<sqinter> y)) = Abs_dense ((x \<squnion> -x \<squnion> -y) \<sqinter> (y \<squnion> -y \<squnion> -x))"
      by (simp add: sup_commute sup_inf_distrib1 sup_left_commute)
    also have "... = Abs_dense (x \<squnion> -x \<squnion> -y) \<sqinter> Abs_dense (y \<squnion> -y \<squnion> -x)"
      using 1 by (metis (mono_tags, lifting) Abs_dense_inverse Rep_dense_inverse inf_dense.rep_eq mem_Collect_eq)
    finally have 5: "up_filter (Abs_dense ((x \<sqinter> y) \<squnion> -(x \<sqinter> y))) = up_filter (Abs_dense (x \<squnion> -x \<squnion> -y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y \<squnion> -x))"
      by (simp add: up_filter_dist_inf)
    have "(stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) \<squnion> (stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y))) = (stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) \<squnion> (stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (y \<squnion> -y)))"
      by (simp add: inf_sup_aci(6) sup_left_commute)
    also have "... = (stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (x \<squnion> -x \<squnion> -y))) \<squnion> (stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (y \<squnion> -y \<squnion> -x)))"
      using 3 by simp
    also have "... = (stone_phi (Abs_regular (-x)) \<squnion> stone_phi (Abs_regular (-y))) \<squnion> (up_filter (Abs_dense (x \<squnion> -x \<squnion> -y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y \<squnion> -x)))"
      by (simp add: inf_sup_aci(6) sup_left_commute)
    also have "... = (stone_phi (Abs_regular (-x)) \<squnion> stone_phi (Abs_regular (-y))) \<squnion> up_filter (Abs_dense ((x \<sqinter> y) \<squnion> -(x \<sqinter> y)))"
      using 5 by (simp add: sup.commute sup.left_commute)
    finally have "(stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) \<squnion> (stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y))) = ..."
      by simp
    also have "... = stone_phi (Abs_regular (-x) \<squnion> Abs_regular (-y)) \<squnion> up_filter (Abs_dense ((x \<sqinter> y) \<squnion> -(x \<sqinter> y)))"
      by (simp add: stone_phi.hom)
    also have "... = stone_phi (Abs_regular (-(x \<sqinter> y))) \<squnion> up_filter (Abs_dense ((x \<sqinter> y) \<squnion> -(x \<sqinter> y)))"
      using 2 by (subst sup_regular.abs_eq) (simp_all add: eq_onp_same_args)
    finally have 6: "stone_phi (Abs_regular (-(x \<sqinter> y))) \<squnion> up_filter (Abs_dense ((x \<sqinter> y) \<squnion> -(x \<sqinter> y))) = (stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) \<squnion> (stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y)))"
      by simp
    have "Abs_regular (--(x \<sqinter> y)) = Abs_regular (--x) \<sqinter> Abs_regular (--y)"
      using 2 by (subst inf_regular.abs_eq) (simp_all add: eq_onp_same_args)
    hence "Abs_stone_phi_pair (Abs_regular (--(x \<sqinter> y)),stone_phi (Abs_regular (-(x \<sqinter> y))) \<squnion> up_filter (Abs_dense ((x \<sqinter> y) \<squnion> -(x \<sqinter> y)))) = Abs_stone_phi_pair (triple.pairs_inf (Abs_regular (--x),stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) (Abs_regular (--y),stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y))))"
      using 6 by auto
    also have "... = Abs_stone_phi_pair (Abs_regular (--x),stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))) \<sqinter> Abs_stone_phi_pair (Abs_regular (--y),stone_phi (Abs_regular (-y)) \<squnion> up_filter (Abs_dense (y \<squnion> -y)))"
      by (rule inf_stone_phi_pair.abs_eq[THEN sym]) (simp_all add: eq_onp_same_args sa_iso_triple_pair)
    finally show "sa_iso (x \<sqinter> y) = sa_iso x \<sqinter> sa_iso y"
      .
  qed
next
  show "\<forall>x::'a . sa_iso (-x) = -sa_iso x"
  proof
    fix x :: 'a
    have "sa_iso (-x) = Abs_stone_phi_pair (Abs_regular (---x),stone_phi (Abs_regular (--x)) \<squnion> up_filter top)"
      by (simp add: top_dense_def)
    also have "... = Abs_stone_phi_pair (Abs_regular (---x),stone_phi (Abs_regular (--x)))"
      by (metis bot_filter.abs_eq sup_bot.right_neutral up_top)
    also have "... = Abs_stone_phi_pair (triple.pairs_uminus stone_phi (Abs_regular (--x),stone_phi (Abs_regular (-x)) \<squnion> up_filter (Abs_dense (x \<squnion> -x))))"
      by (subst uminus_regular.abs_eq[THEN sym], unfold eq_onp_same_args) auto
    also have "... = -sa_iso x"
      by (simp add: eq_onp_def sa_iso_triple_pair uminus_stone_phi_pair.abs_eq)
    finally show "sa_iso (-x) = -sa_iso x"
      by simp
  qed
next
  show "bij sa_iso"
    by (metis (mono_tags, lifting) sa_iso_left_invertible sa_iso_right_invertible invertible_bij[where g=sa_iso_inv])
qed

subsection \<open>Triple Isomorphism\<close>

text \<open>
In this section we prove that the triple of the Stone algebra of a triple is isomorphic to the original triple.
The notion of isomorphism for triples is described in \cite{ChenGraetzer1969}.
It amounts to an isomorphism of Boolean algebras, an isomorphism of distributive lattices with a greatest element, and a commuting diagram involving the structure maps.
\<close>

subsubsection \<open>Boolean Algebra Isomorphism\<close>

text \<open>
We first define and prove the isomorphism of Boolean algebras.
Because the Stone algebra of a triple is implemented as a lifted pair, we also lift the Boolean algebra.
\<close>

typedef (overloaded) ('a,'b) lifted_boolean_algebra = "{ xf::('a::non_trivial_boolean_algebra,'b::distrib_lattice_top) phi \<Rightarrow> 'a . True }"
  by simp

setup_lifting type_definition_lifted_boolean_algebra

instantiation lifted_boolean_algebra :: (non_trivial_boolean_algebra,distrib_lattice_top) boolean_algebra
begin

lift_definition sup_lifted_boolean_algebra :: "('a,'b) lifted_boolean_algebra \<Rightarrow> ('a,'b) lifted_boolean_algebra \<Rightarrow> ('a,'b) lifted_boolean_algebra" is "\<lambda>xf yf f . sup (xf f) (yf f)" .

lift_definition inf_lifted_boolean_algebra :: "('a,'b) lifted_boolean_algebra \<Rightarrow> ('a,'b) lifted_boolean_algebra \<Rightarrow> ('a,'b) lifted_boolean_algebra" is "\<lambda>xf yf f . inf (xf f) (yf f)" .

lift_definition minus_lifted_boolean_algebra :: "('a,'b) lifted_boolean_algebra \<Rightarrow> ('a,'b) lifted_boolean_algebra \<Rightarrow> ('a,'b) lifted_boolean_algebra" is "\<lambda>xf yf f . minus (xf f) (yf f)" .

lift_definition uminus_lifted_boolean_algebra :: "('a,'b) lifted_boolean_algebra \<Rightarrow> ('a,'b) lifted_boolean_algebra" is "\<lambda>xf f . uminus (xf f)" .

lift_definition bot_lifted_boolean_algebra :: "('a,'b) lifted_boolean_algebra" is "\<lambda>f . bot" ..

lift_definition top_lifted_boolean_algebra :: "('a,'b) lifted_boolean_algebra" is "\<lambda>f . top" ..

lift_definition less_eq_lifted_boolean_algebra :: "('a,'b) lifted_boolean_algebra \<Rightarrow> ('a,'b) lifted_boolean_algebra \<Rightarrow> bool" is "\<lambda>xf yf . \<forall>f . less_eq (xf f) (yf f)" .

lift_definition less_lifted_boolean_algebra :: "('a,'b) lifted_boolean_algebra \<Rightarrow> ('a,'b) lifted_boolean_algebra \<Rightarrow> bool" is "\<lambda>xf yf . (\<forall>f . less_eq (xf f) (yf f)) \<and> \<not> (\<forall>f . less_eq (yf f) (xf f))" .

instance
  apply intro_classes
  apply (simp add: less_eq_lifted_boolean_algebra.rep_eq less_lifted_boolean_algebra.rep_eq)
  apply (simp add: less_eq_lifted_boolean_algebra.rep_eq)
  using less_eq_lifted_boolean_algebra.rep_eq order_trans apply fastforce
  apply (metis less_eq_lifted_boolean_algebra.rep_eq antisym ext Rep_lifted_boolean_algebra_inject)
  apply (simp add: inf_lifted_boolean_algebra.rep_eq less_eq_lifted_boolean_algebra.rep_eq)
  apply (simp add: inf_lifted_boolean_algebra.rep_eq less_eq_lifted_boolean_algebra.rep_eq)
  apply (simp add: inf_lifted_boolean_algebra.rep_eq less_eq_lifted_boolean_algebra.rep_eq)
  apply (simp add: sup_lifted_boolean_algebra.rep_eq less_eq_lifted_boolean_algebra.rep_eq)
  apply (simp add: less_eq_lifted_boolean_algebra.rep_eq sup_lifted_boolean_algebra.rep_eq)
  apply (simp add: less_eq_lifted_boolean_algebra.rep_eq sup_lifted_boolean_algebra.rep_eq)
  apply (simp add: bot_lifted_boolean_algebra.rep_eq less_eq_lifted_boolean_algebra.rep_eq)
  apply (simp add: less_eq_lifted_boolean_algebra.rep_eq top_lifted_boolean_algebra.rep_eq)
  apply (unfold Rep_lifted_boolean_algebra_inject[THEN sym] sup_lifted_boolean_algebra.rep_eq inf_lifted_boolean_algebra.rep_eq, simp add: sup_inf_distrib1)
  apply (unfold Rep_lifted_boolean_algebra_inject[THEN sym] inf_lifted_boolean_algebra.rep_eq uminus_lifted_boolean_algebra.rep_eq bot_lifted_boolean_algebra.rep_eq, simp)
  apply (unfold Rep_lifted_boolean_algebra_inject[THEN sym] sup_lifted_boolean_algebra.rep_eq uminus_lifted_boolean_algebra.rep_eq top_lifted_boolean_algebra.rep_eq, simp)
  by (unfold Rep_lifted_boolean_algebra_inject[THEN sym] inf_lifted_boolean_algebra.rep_eq uminus_lifted_boolean_algebra.rep_eq minus_lifted_boolean_algebra.rep_eq, simp add: diff_eq)

end

text \<open>
The following two definitions give the Boolean algebra isomorphism.
\<close>

abbreviation ba_iso_inv :: "('a::non_trivial_boolean_algebra,'b::distrib_lattice_top) lifted_boolean_algebra \<Rightarrow> ('a,'b) lifted_pair regular"
  where "ba_iso_inv \<equiv> \<lambda>xf . Abs_regular (Abs_lifted_pair (\<lambda>f . (Rep_lifted_boolean_algebra xf f,Rep_phi f (-Rep_lifted_boolean_algebra xf f))))"

abbreviation ba_iso :: "('a::non_trivial_boolean_algebra,'b::distrib_lattice_top) lifted_pair regular \<Rightarrow> ('a,'b) lifted_boolean_algebra"
  where "ba_iso \<equiv> \<lambda>pf . Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular pf) f))"

lemma ba_iso_inv_lifted_pair:
  "(Rep_lifted_boolean_algebra xf f,Rep_phi f (-Rep_lifted_boolean_algebra xf f)) \<in> triple.pairs (Rep_phi f)"
  by (metis (no_types, hide_lams) double_compl simp_phi triple.pairs_uminus.simps triple_def triple.pairs_uminus_closed)

lemma ba_iso_inv_regular:
  "regular (Abs_lifted_pair (\<lambda>f . (Rep_lifted_boolean_algebra xf f,Rep_phi f (-Rep_lifted_boolean_algebra xf f))))"
proof -
  have "\<forall>f . (Rep_lifted_boolean_algebra xf f,Rep_phi f (-Rep_lifted_boolean_algebra xf f)) = triple.pairs_uminus (Rep_phi f) (triple.pairs_uminus (Rep_phi f) (Rep_lifted_boolean_algebra xf f,Rep_phi f (-Rep_lifted_boolean_algebra xf f)))"
    by (simp add: triple.pairs_uminus.simps triple_def)
  hence "Abs_lifted_pair (\<lambda>f . (Rep_lifted_boolean_algebra xf f,Rep_phi f (-Rep_lifted_boolean_algebra xf f))) = --Abs_lifted_pair (\<lambda>f . (Rep_lifted_boolean_algebra xf f,Rep_phi f (-Rep_lifted_boolean_algebra xf f)))"
    by (simp add: triple.pairs_uminus_closed triple_def eq_onp_def uminus_lifted_pair.abs_eq ba_iso_inv_lifted_pair)
  thus ?thesis
    by simp
qed

text \<open>
The following two results prove that the isomorphisms are mutually inverse.
\<close>

lemma ba_iso_left_invertible:
  "ba_iso_inv (ba_iso pf) = pf"
proof -
  have 1: "\<forall>f . snd (Rep_lifted_pair (Rep_regular pf) f) = Rep_phi f (-fst (Rep_lifted_pair (Rep_regular pf) f))"
  proof
    fix f :: "('a,'b) phi"
    let ?r = "Rep_phi f"
    have "triple ?r"
      by (simp add: triple_def)
    hence 2: "\<forall>p . triple.pairs_uminus ?r p = (-fst p,?r (fst p))"
      by (metis prod.collapse triple.pairs_uminus.simps)
    have 3: "Rep_regular pf = --Rep_regular pf"
      by (simp add: regular_in_p_image_iff)
    show "snd (Rep_lifted_pair (Rep_regular pf) f) = ?r (-fst (Rep_lifted_pair (Rep_regular pf) f))"
      using 2 3 by (metis fstI sndI uminus_lifted_pair.rep_eq)
  qed
  have "ba_iso_inv (ba_iso pf) = Abs_regular (Abs_lifted_pair (\<lambda>f . (fst (Rep_lifted_pair (Rep_regular pf) f),Rep_phi f (-fst (Rep_lifted_pair (Rep_regular pf) f)))))"
    by (simp add: Abs_lifted_boolean_algebra_inverse)
  also have "... = Abs_regular (Abs_lifted_pair (Rep_lifted_pair (Rep_regular pf)))"
    using 1 by (metis prod.collapse)
  also have "... = pf"
    by (simp add: Rep_regular_inverse Rep_lifted_pair_inverse)
  finally show ?thesis
    .
qed

lemma ba_iso_right_invertible:
  "ba_iso (ba_iso_inv xf) = xf"
proof -
  let ?rf = "Rep_lifted_boolean_algebra xf"
  have 1: "\<forall>f . (-?rf f,Rep_phi f (?rf f)) \<in> triple.pairs (Rep_phi f) \<and> (?rf f,Rep_phi f (-?rf f)) \<in> triple.pairs (Rep_phi f)"
  proof
    fix f
    have "up_filter top = bot"
      by (simp add: bot_filter.abs_eq)
    hence "(\<exists>z . Rep_phi f (?rf f) = Rep_phi f (?rf f) \<squnion> up_filter z) \<and> (\<exists>z . Rep_phi f (-?rf f) = Rep_phi f (-?rf f) \<squnion> up_filter z)"
      by (metis sup_bot_right)
    thus "(-?rf f,Rep_phi f (?rf f)) \<in> triple.pairs (Rep_phi f) \<and> (?rf f,Rep_phi f (-?rf f)) \<in> triple.pairs (Rep_phi f)"
      by (simp add: triple_def triple.pairs_def)
  qed
  have "regular (Abs_lifted_pair (\<lambda>f . (?rf f,Rep_phi f (-?rf f))))"
  proof -
    have "--Abs_lifted_pair (\<lambda>f . (?rf f,Rep_phi f (-?rf f))) = -Abs_lifted_pair (\<lambda>f . triple.pairs_uminus (Rep_phi f) (?rf f,Rep_phi f (-?rf f)))"
      using 1 by (simp add: eq_onp_same_args uminus_lifted_pair.abs_eq)
    also have "... = -Abs_lifted_pair (\<lambda>f . (-?rf f,Rep_phi f (?rf f)))"
      by (metis (no_types, lifting) simp_phi triple_def triple.pairs_uminus.simps)
    also have "... = Abs_lifted_pair (\<lambda>f . triple.pairs_uminus (Rep_phi f) (-?rf f,Rep_phi f (?rf f)))"
      using 1 by (simp add: eq_onp_same_args uminus_lifted_pair.abs_eq)
    also have "... = Abs_lifted_pair (\<lambda>f . (?rf f,Rep_phi f (-?rf f)))"
      by (metis (no_types, lifting) simp_phi triple_def triple.pairs_uminus.simps double_compl)
    finally show ?thesis
      by simp
  qed
  hence "in_p_image (Abs_lifted_pair (\<lambda>f . (?rf f,Rep_phi f (-?rf f))))"
    by blast
  thus ?thesis
    using 1 by (simp add: Rep_lifted_boolean_algebra_inverse Abs_lifted_pair_inverse Abs_regular_inverse)
qed

text \<open>
The isomorphism is established by proving the remaining Boolean algebra homomorphism properties.
\<close>

lemma ba_iso:
  "boolean_algebra_isomorphism ba_iso"
proof (intro conjI)
  show "Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular bot) f)) = bot"
    by (simp add: bot_lifted_boolean_algebra_def bot_regular.rep_eq bot_lifted_pair.rep_eq)
next
  show "Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular top) f)) = top"
    by (simp add: top_lifted_boolean_algebra_def top_regular.rep_eq top_lifted_pair.rep_eq)
next
  show "\<forall>pf qf . Abs_lifted_boolean_algebra (\<lambda>f::('a,'b) phi . fst (Rep_lifted_pair (Rep_regular (pf \<squnion> qf)) f)) = Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular pf) f)) \<squnion> Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular qf) f))"
  proof (intro allI)
    fix pf qf :: "('a,'b) lifted_pair regular"
    {
      fix f
      obtain x y z w where 1: "(x,y) = Rep_lifted_pair (Rep_regular pf) f \<and> (z,w) = Rep_lifted_pair (Rep_regular qf) f"
        using prod.collapse by blast
      have "triple (Rep_phi f)"
        by (simp add: triple_def)
      hence "fst (triple.pairs_sup (x,y) (z,w)) = fst (x,y) \<squnion> fst (z,w)"
        using triple.pairs_sup.simps by force
      hence "fst (triple.pairs_sup (Rep_lifted_pair (Rep_regular pf) f) (Rep_lifted_pair (Rep_regular qf) f)) = fst (Rep_lifted_pair (Rep_regular pf) f) \<squnion> fst (Rep_lifted_pair (Rep_regular qf) f)"
        using 1 by simp
      hence "fst (Rep_lifted_pair (Rep_regular (pf \<squnion> qf)) f) = fst (Rep_lifted_pair (Rep_regular pf) f) \<squnion> fst (Rep_lifted_pair (Rep_regular qf) f)"
        by (unfold sup_regular.rep_eq sup_lifted_pair.rep_eq) simp
    }
    thus "Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular (pf \<squnion> qf)) f)) = Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular pf) f)) \<squnion> Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular qf) f))"
      by (simp add: eq_onp_same_args sup_lifted_boolean_algebra.abs_eq sup_regular.rep_eq sup_lifted_boolean_algebra.rep_eq)
  qed
next
  show "\<forall>pf qf . Abs_lifted_boolean_algebra (\<lambda>f::('a,'b) phi . fst (Rep_lifted_pair (Rep_regular (pf \<sqinter> qf)) f)) = Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular pf) f)) \<sqinter> Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular qf) f))"
  proof (intro allI)
    fix pf qf :: "('a,'b) lifted_pair regular"
    {
      fix f
      obtain x y z w where 1: "(x,y) = Rep_lifted_pair (Rep_regular pf) f \<and> (z,w) = Rep_lifted_pair (Rep_regular qf) f"
        using prod.collapse by blast
      have "triple (Rep_phi f)"
        by (simp add: triple_def)
      hence "fst (triple.pairs_inf (x,y) (z,w)) = fst (x,y) \<sqinter> fst (z,w)"
        using triple.pairs_inf.simps by force
      hence "fst (triple.pairs_inf (Rep_lifted_pair (Rep_regular pf) f) (Rep_lifted_pair (Rep_regular qf) f)) = fst (Rep_lifted_pair (Rep_regular pf) f) \<sqinter> fst (Rep_lifted_pair (Rep_regular qf) f)"
        using 1 by simp
      hence "fst (Rep_lifted_pair (Rep_regular (pf \<sqinter> qf)) f) = fst (Rep_lifted_pair (Rep_regular pf) f) \<sqinter> fst (Rep_lifted_pair (Rep_regular qf) f)"
        by (unfold inf_regular.rep_eq inf_lifted_pair.rep_eq) simp
    }
    thus "Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular (pf \<sqinter> qf)) f)) = Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular pf) f)) \<sqinter> Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular qf) f))"
      by (simp add: eq_onp_same_args inf_lifted_boolean_algebra.abs_eq inf_regular.rep_eq inf_lifted_boolean_algebra.rep_eq)
  qed
next
  show "\<forall>pf . Abs_lifted_boolean_algebra (\<lambda>f::('a,'b) phi . fst (Rep_lifted_pair (Rep_regular (-pf)) f)) = -Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular pf) f))"
  proof
    fix pf :: "('a,'b) lifted_pair regular"
    {
      fix f
      obtain x y where 1: "(x,y) = Rep_lifted_pair (Rep_regular pf) f"
        using prod.collapse by blast
      have "triple (Rep_phi f)"
        by (simp add: triple_def)
      hence "fst (triple.pairs_uminus (Rep_phi f) (x,y)) = -fst (x,y)"
        using triple.pairs_uminus.simps by force
      hence "fst (triple.pairs_uminus (Rep_phi f) (Rep_lifted_pair (Rep_regular pf) f)) = -fst (Rep_lifted_pair (Rep_regular pf) f)"
        using 1 by simp
      hence "fst (Rep_lifted_pair (Rep_regular (-pf)) f) = -fst (Rep_lifted_pair (Rep_regular pf) f)"
        by (unfold uminus_regular.rep_eq uminus_lifted_pair.rep_eq) simp
    }
    thus "Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular (-pf)) f)) = -Abs_lifted_boolean_algebra (\<lambda>f . fst (Rep_lifted_pair (Rep_regular pf) f))"
      by (simp add: eq_onp_same_args uminus_lifted_boolean_algebra.abs_eq uminus_regular.rep_eq uminus_lifted_boolean_algebra.rep_eq)
  qed
next
  show "bij ba_iso"
    by (rule invertible_bij[where g=ba_iso_inv]) (simp_all add: ba_iso_left_invertible ba_iso_right_invertible)
qed

subsubsection \<open>Distributive Lattice Isomorphism\<close>

text \<open>
We carry out a similar development for the isomorphism of distributive lattices.
Again, the original distributive lattice with a greatest element needs to be lifted to match the lifted pairs.
\<close>

typedef (overloaded) ('a,'b) lifted_distrib_lattice_top = "{ xf::('a::non_trivial_boolean_algebra,'b::distrib_lattice_top) phi \<Rightarrow> 'b . True }"
  by simp

setup_lifting type_definition_lifted_distrib_lattice_top

instantiation lifted_distrib_lattice_top :: (non_trivial_boolean_algebra,distrib_lattice_top) distrib_lattice_top
begin

lift_definition sup_lifted_distrib_lattice_top :: "('a,'b) lifted_distrib_lattice_top \<Rightarrow> ('a,'b) lifted_distrib_lattice_top \<Rightarrow> ('a,'b) lifted_distrib_lattice_top" is "\<lambda>xf yf f . sup (xf f) (yf f)" .

lift_definition inf_lifted_distrib_lattice_top :: "('a,'b) lifted_distrib_lattice_top \<Rightarrow> ('a,'b) lifted_distrib_lattice_top \<Rightarrow> ('a,'b) lifted_distrib_lattice_top" is "\<lambda>xf yf f . inf (xf f) (yf f)" .

lift_definition top_lifted_distrib_lattice_top :: "('a,'b) lifted_distrib_lattice_top" is "\<lambda>f . top" ..

lift_definition less_eq_lifted_distrib_lattice_top :: "('a,'b) lifted_distrib_lattice_top \<Rightarrow> ('a,'b) lifted_distrib_lattice_top \<Rightarrow> bool" is "\<lambda>xf yf . \<forall>f . less_eq (xf f) (yf f)" .

lift_definition less_lifted_distrib_lattice_top :: "('a,'b) lifted_distrib_lattice_top \<Rightarrow> ('a,'b) lifted_distrib_lattice_top \<Rightarrow> bool" is "\<lambda>xf yf . (\<forall>f . less_eq (xf f) (yf f)) \<and> \<not> (\<forall>f . less_eq (yf f) (xf f))" .

instance
  apply intro_classes
  apply (simp add: less_eq_lifted_distrib_lattice_top.rep_eq less_lifted_distrib_lattice_top.rep_eq)
  apply (simp add: less_eq_lifted_distrib_lattice_top.rep_eq)
  using less_eq_lifted_distrib_lattice_top.rep_eq order_trans apply fastforce
  apply (metis less_eq_lifted_distrib_lattice_top.rep_eq antisym ext Rep_lifted_distrib_lattice_top_inject)
  apply (simp add: inf_lifted_distrib_lattice_top.rep_eq less_eq_lifted_distrib_lattice_top.rep_eq)
  apply (simp add: inf_lifted_distrib_lattice_top.rep_eq less_eq_lifted_distrib_lattice_top.rep_eq)
  apply (simp add: inf_lifted_distrib_lattice_top.rep_eq less_eq_lifted_distrib_lattice_top.rep_eq)
  apply (simp add: sup_lifted_distrib_lattice_top.rep_eq less_eq_lifted_distrib_lattice_top.rep_eq)
  apply (simp add: less_eq_lifted_distrib_lattice_top.rep_eq sup_lifted_distrib_lattice_top.rep_eq)
  apply (simp add: less_eq_lifted_distrib_lattice_top.rep_eq sup_lifted_distrib_lattice_top.rep_eq)
  apply (simp add: less_eq_lifted_distrib_lattice_top.rep_eq top_lifted_distrib_lattice_top.rep_eq)
  by (unfold Rep_lifted_distrib_lattice_top_inject[THEN sym] sup_lifted_distrib_lattice_top.rep_eq inf_lifted_distrib_lattice_top.rep_eq, simp add: sup_inf_distrib1)

end

text \<open>
The following function extracts the least element of the filter of a dense pair, which turns out to be a principal filter.
It is used to define one of the isomorphisms below.
\<close>

fun get_dense :: "('a::non_trivial_boolean_algebra,'b::distrib_lattice_top) lifted_pair dense \<Rightarrow> ('a,'b) phi \<Rightarrow> 'b"
  where "get_dense pf f = (SOME z . Rep_lifted_pair (Rep_dense pf) f = (top,up_filter z))"

lemma get_dense_char:
  "Rep_lifted_pair (Rep_dense pf) f = (top,up_filter (get_dense pf f))"
proof -
  obtain x y where 1: "(x,y) = Rep_lifted_pair (Rep_dense pf) f \<and> (x,y) \<in> triple.pairs (Rep_phi f) \<and> triple.pairs_uminus (Rep_phi f) (x,y) = triple.pairs_bot"
    by (metis bot_lifted_pair.rep_eq prod.collapse simp_dense simp_lifted_pair uminus_lifted_pair.rep_eq)
  hence 2: "x = top"
    by (simp add: triple.intro triple.pairs_uminus.simps dense_pp)
  have "triple (Rep_phi f)"
    by (simp add: triple_def)
  hence "\<exists>z. y = Rep_phi f (-x) \<squnion> up_filter z"
    using 1 triple.pairs_def by blast
  then obtain z where "y = up_filter z"
    using 2 by auto
  hence "Rep_lifted_pair (Rep_dense pf) f = (top,up_filter z)"
    using 1 2 by simp
  thus ?thesis
    by (metis (mono_tags, lifting) tfl_some get_dense.simps)
qed

text \<open>
The following two definitions give the distributive lattice isomorphism.
\<close>

abbreviation dl_iso_inv :: "('a::non_trivial_boolean_algebra,'b::distrib_lattice_top) lifted_distrib_lattice_top \<Rightarrow> ('a,'b) lifted_pair dense"
  where "dl_iso_inv \<equiv> \<lambda>xf . Abs_dense (Abs_lifted_pair (\<lambda>f . (top,up_filter (Rep_lifted_distrib_lattice_top xf f))))"

abbreviation dl_iso :: "('a::non_trivial_boolean_algebra,'b::distrib_lattice_top) lifted_pair dense \<Rightarrow> ('a,'b) lifted_distrib_lattice_top"
  where "dl_iso \<equiv> \<lambda>pf . Abs_lifted_distrib_lattice_top (get_dense pf)"

lemma dl_iso_inv_lifted_pair:
  "(top,up_filter (Rep_lifted_distrib_lattice_top xf f)) \<in> triple.pairs (Rep_phi f)"
  by (metis (no_types, hide_lams) compl_bot_eq double_compl simp_phi sup_bot.left_neutral triple.sa_iso_pair triple_def)

lemma dl_iso_inv_dense:
  "dense (Abs_lifted_pair (\<lambda>f . (top,up_filter (Rep_lifted_distrib_lattice_top xf f))))"
proof -
  have "\<forall>f . triple.pairs_uminus (Rep_phi f) (top,up_filter (Rep_lifted_distrib_lattice_top xf f)) = triple.pairs_bot"
    by (simp add: top_filter.abs_eq triple.pairs_uminus.simps triple_def)
  hence "bot = -Abs_lifted_pair (\<lambda>f . (top,up_filter (Rep_lifted_distrib_lattice_top xf f)))"
    by (simp add: eq_onp_def uminus_lifted_pair.abs_eq dl_iso_inv_lifted_pair bot_lifted_pair_def)
  thus ?thesis
    by simp
qed

text \<open>
The following two results prove that the isomorphisms are mutually inverse.
\<close>

lemma dl_iso_left_invertible:
  "dl_iso_inv (dl_iso pf) = pf"
proof -
  have "dl_iso_inv (dl_iso pf) = Abs_dense (Abs_lifted_pair (\<lambda>f . (top,up_filter (get_dense pf f))))"
    by (metis Abs_lifted_distrib_lattice_top_inverse UNIV_I UNIV_def)
  also have "... = Abs_dense (Abs_lifted_pair (Rep_lifted_pair (Rep_dense pf)))"
    by (metis get_dense_char)
  also have "... = pf"
    by (simp add: Rep_dense_inverse Rep_lifted_pair_inverse)
  finally show ?thesis
    .
qed

lemma dl_iso_right_invertible:
  "dl_iso (dl_iso_inv xf) = xf"
proof -
  let ?rf = "Rep_lifted_distrib_lattice_top xf"
  let ?pf = "Abs_dense (Abs_lifted_pair (\<lambda>f . (top,up_filter (?rf f))))"
  have 1: "\<forall>f . (top,up_filter (?rf f)) \<in> triple.pairs (Rep_phi f)"
  proof
    fix f :: "('a,'b) phi"
    have "triple (Rep_phi f)"
      by (simp add: triple_def)
    thus "(top,up_filter (?rf f)) \<in> triple.pairs (Rep_phi f)"
      using triple.pairs_def by force
  qed
  have 2: "dense (Abs_lifted_pair (\<lambda>f . (top,up_filter (?rf f))))"
  proof -
    have "-Abs_lifted_pair (\<lambda>f . (top,up_filter (?rf f))) = Abs_lifted_pair (\<lambda>f . triple.pairs_uminus (Rep_phi f) (top,up_filter (?rf f)))"
      using 1 by (simp add: eq_onp_same_args uminus_lifted_pair.abs_eq)
    also have "... = Abs_lifted_pair (\<lambda>f . (bot,Rep_phi f top))"
      by (simp add: triple.pairs_uminus.simps triple_def)
    also have "... = Abs_lifted_pair (\<lambda>f . triple.pairs_bot)"
      by (metis (no_types, hide_lams) simp_phi triple.phi_top triple_def)
    also have "... = bot"
      by (simp add: bot_lifted_pair_def)
    finally show ?thesis
      by simp
  qed
  have "get_dense ?pf = ?rf"
  proof
    fix f
    have "(top,up_filter (get_dense ?pf f)) = Rep_lifted_pair (Rep_dense ?pf) f"
      by (metis get_dense_char)
    also have "... = Rep_lifted_pair (Abs_lifted_pair (\<lambda>f . (top,up_filter (?rf f)))) f"
      using Abs_dense_inverse 2 by force
    also have "... = (top,up_filter (?rf f))"
      using 1 by (simp add: Abs_lifted_pair_inverse)
    finally show "get_dense ?pf f = ?rf f"
      using up_filter_injective by auto
  qed
  thus ?thesis
    by (simp add: Rep_lifted_distrib_lattice_top_inverse)
qed

text \<open>
To obtain the isomorphism, it remains to show the homomorphism properties of lattices with a greatest element.
\<close>

lemma dl_iso:
  "bounded_lattice_top_isomorphism dl_iso"
proof (intro conjI)
  have "get_dense top = (\<lambda>f::('a,'b) phi . top)"
  proof
    fix f :: "('a,'b) phi"
    have "Rep_lifted_pair (Rep_dense top) f = (top,Abs_filter {top})"
      by (simp add: top_dense.rep_eq top_lifted_pair.rep_eq)
    hence "up_filter (get_dense top f) = Abs_filter {top}"
      by (metis prod.inject get_dense_char)
    hence "Rep_filter (up_filter (get_dense top f)) = {top}"
      by (metis bot_filter.abs_eq bot_filter.rep_eq)
    thus "get_dense top f = top"
      by (metis self_in_upset singletonD Abs_filter_inverse mem_Collect_eq up_filter)
  qed
  thus "Abs_lifted_distrib_lattice_top (get_dense top::('a,'b) phi \<Rightarrow> 'b) = top"
    by (metis top_lifted_distrib_lattice_top_def)
next
  show "\<forall>pf qf :: ('a,'b) lifted_pair dense . Abs_lifted_distrib_lattice_top (get_dense (pf \<squnion> qf)) = Abs_lifted_distrib_lattice_top (get_dense pf) \<squnion> Abs_lifted_distrib_lattice_top (get_dense qf)"
  proof (intro allI)
    fix pf qf :: "('a,'b) lifted_pair dense"
    have 1: "Abs_lifted_distrib_lattice_top (get_dense pf) \<squnion> Abs_lifted_distrib_lattice_top (get_dense qf) = Abs_lifted_distrib_lattice_top (\<lambda>f . get_dense pf f \<squnion> get_dense qf f)"
      by (simp add: eq_onp_same_args sup_lifted_distrib_lattice_top.abs_eq)
    have "(\<lambda>f . get_dense (pf \<squnion> qf) f) = (\<lambda>f . get_dense pf f \<squnion> get_dense qf f)"
    proof
      fix f
      have "(top,up_filter (get_dense (pf \<squnion> qf) f)) = Rep_lifted_pair (Rep_dense (pf \<squnion> qf)) f"
        by (metis get_dense_char)
      also have "... = triple.pairs_sup (Rep_lifted_pair (Rep_dense pf) f) (Rep_lifted_pair (Rep_dense qf) f)"
        by (simp add: sup_lifted_pair.rep_eq sup_dense.rep_eq)
      also have "... = triple.pairs_sup (top,up_filter (get_dense pf f)) (top,up_filter (get_dense qf f))"
        by (metis get_dense_char)
      also have "... = (top,up_filter (get_dense pf f) \<sqinter> up_filter (get_dense qf f))"
        by (metis (no_types, lifting) calculation prod.simps(1) simp_phi triple.pairs_sup.simps triple_def)
      also have "... = (top,up_filter (get_dense pf f \<squnion> get_dense qf f))"
        by (metis up_filter_dist_sup)
      finally show "get_dense (pf \<squnion> qf) f = get_dense pf f \<squnion> get_dense qf f"
        using up_filter_injective by blast
    qed
    thus "Abs_lifted_distrib_lattice_top (get_dense (pf \<squnion> qf)) = Abs_lifted_distrib_lattice_top (get_dense pf) \<squnion> Abs_lifted_distrib_lattice_top (get_dense qf)"
      using 1 by metis
  qed
next
  show "\<forall>pf qf :: ('a,'b) lifted_pair dense . Abs_lifted_distrib_lattice_top (get_dense (pf \<sqinter> qf)) = Abs_lifted_distrib_lattice_top (get_dense pf) \<sqinter> Abs_lifted_distrib_lattice_top (get_dense qf)"
  proof (intro allI)
    fix pf qf :: "('a,'b) lifted_pair dense"
    have 1: "Abs_lifted_distrib_lattice_top (get_dense pf) \<sqinter> Abs_lifted_distrib_lattice_top (get_dense qf) = Abs_lifted_distrib_lattice_top (\<lambda>f . get_dense pf f \<sqinter> get_dense qf f)"
      by (simp add: eq_onp_same_args inf_lifted_distrib_lattice_top.abs_eq)
    have "(\<lambda>f . get_dense (pf \<sqinter> qf) f) = (\<lambda>f . get_dense pf f \<sqinter> get_dense qf f)"
    proof
      fix f
      have "(top,up_filter (get_dense (pf \<sqinter> qf) f)) = Rep_lifted_pair (Rep_dense (pf \<sqinter> qf)) f"
        by (metis get_dense_char)
      also have "... = triple.pairs_inf (Rep_lifted_pair (Rep_dense pf) f) (Rep_lifted_pair (Rep_dense qf) f)"
        by (simp add: inf_lifted_pair.rep_eq inf_dense.rep_eq)
      also have "... = triple.pairs_inf (top,up_filter (get_dense pf f)) (top,up_filter (get_dense qf f))"
        by (metis get_dense_char)
      also have "... = (top,up_filter (get_dense pf f) \<squnion> up_filter (get_dense qf f))"
        by (metis (no_types, lifting) calculation prod.simps(1) simp_phi triple.pairs_inf.simps triple_def)
      also have "... = (top,up_filter (get_dense pf f \<sqinter> get_dense qf f))"
        by (metis up_filter_dist_inf)
      finally show "get_dense (pf \<sqinter> qf) f = get_dense pf f \<sqinter> get_dense qf f"
        using up_filter_injective by blast
    qed
    thus "Abs_lifted_distrib_lattice_top (get_dense (pf \<sqinter> qf)) = Abs_lifted_distrib_lattice_top (get_dense pf) \<sqinter> Abs_lifted_distrib_lattice_top (get_dense qf)"
      using 1 by metis
  qed
next
  show "bij dl_iso"
    by (rule invertible_bij[where g=dl_iso_inv]) (simp_all add: dl_iso_left_invertible dl_iso_right_invertible)
qed

subsubsection \<open>Structure Map Preservation\<close>

text \<open>
We finally show that the isomorphisms are compatible with the structure maps.
This involves lifting the distributive lattice isomorphism to filters of distributive lattices (as these are the targets of the structure maps).
To this end, we first show that the lifted isomorphism preserves filters.
\<close>

lemma phi_iso_filter:
  "filter ((\<lambda>qf::('a::non_trivial_boolean_algebra,'b::distrib_lattice_top) lifted_pair dense . Rep_lifted_distrib_lattice_top (dl_iso qf) f) ` Rep_filter (stone_phi pf))"
proof (rule filter_map_filter)
  show "mono (\<lambda>qf::('a::non_trivial_boolean_algebra,'b::distrib_lattice_top) lifted_pair dense . Rep_lifted_distrib_lattice_top (dl_iso qf) f)"
    by (metis (no_types, lifting) mono_def dl_iso le_iff_sup sup_lifted_distrib_lattice_top.rep_eq)
next
  show "\<forall>qf y . Rep_lifted_distrib_lattice_top (dl_iso qf) f \<le> y \<longrightarrow> (\<exists>rf . qf \<le> rf \<and> y = Rep_lifted_distrib_lattice_top (dl_iso rf) f)"
  proof (intro allI, rule impI)
    fix qf :: "('a,'b) lifted_pair dense"
    fix y :: 'b
    assume 1: "Rep_lifted_distrib_lattice_top (dl_iso qf) f \<le> y"
    let ?rf = "Abs_dense (Abs_lifted_pair (\<lambda>g . if g = f then (top,up_filter y) else Rep_lifted_pair (Rep_dense qf) g))"
    have 2: "\<forall>g . (if g = f then (top,up_filter y) else Rep_lifted_pair (Rep_dense qf) g) \<in> triple.pairs (Rep_phi g)"
      by (metis Abs_lifted_distrib_lattice_top_inverse dl_iso_inv_lifted_pair mem_Collect_eq simp_lifted_pair)
    hence "-Abs_lifted_pair (\<lambda>g . if g = f then (top,up_filter y) else Rep_lifted_pair (Rep_dense qf) g) = Abs_lifted_pair (\<lambda>g . triple.pairs_uminus (Rep_phi g) (if g = f then (top,up_filter y) else Rep_lifted_pair (Rep_dense qf) g))"
      by (simp add: eq_onp_def uminus_lifted_pair.abs_eq)
    also have "... = Abs_lifted_pair (\<lambda>g . if g = f then triple.pairs_uminus (Rep_phi g) (top,up_filter y) else triple.pairs_uminus (Rep_phi g) (Rep_lifted_pair (Rep_dense qf) g))"
      by (simp add: if_distrib)
    also have "... = Abs_lifted_pair (\<lambda>g . if g = f then (bot,top) else triple.pairs_uminus (Rep_phi g) (Rep_lifted_pair (Rep_dense qf) g))"
      by (subst triple.pairs_uminus.simps, simp add: triple_def, metis compl_top_eq simp_phi)
    also have "... = Abs_lifted_pair (\<lambda>g . if g = f then (bot,top) else (bot,top))"
      by (metis bot_lifted_pair.rep_eq simp_dense top_filter.abs_eq uminus_lifted_pair.rep_eq)
    also have "... = bot"
      by (simp add: bot_lifted_pair.abs_eq top_filter.abs_eq)
    finally have 3: "Abs_lifted_pair (\<lambda>g . if g = f then (top,up_filter y) else Rep_lifted_pair (Rep_dense qf) g) \<in> dense_elements"
      by blast
    hence "(top,up_filter (get_dense (Abs_dense (Abs_lifted_pair (\<lambda>g . if g = f then (top,up_filter y) else Rep_lifted_pair (Rep_dense qf) g))) f)) = Rep_lifted_pair (Rep_dense (Abs_dense (Abs_lifted_pair (\<lambda>g . if g = f then (top,up_filter y) else Rep_lifted_pair (Rep_dense qf) g)))) f"
      by (metis (mono_tags, lifting) get_dense_char)
    also have "... = Rep_lifted_pair (Abs_lifted_pair (\<lambda>g . if g = f then (top,up_filter y) else Rep_lifted_pair (Rep_dense qf) g)) f"
      using 3 by (simp add: Abs_dense_inverse)
    also have "... = (top,up_filter y)"
      using 2 by (simp add: Abs_lifted_pair_inverse)
    finally have "get_dense (Abs_dense (Abs_lifted_pair (\<lambda>g . if g = f then (top,up_filter y) else Rep_lifted_pair (Rep_dense qf) g))) f = y"
      using up_filter_injective by blast
    hence 4: "Rep_lifted_distrib_lattice_top (dl_iso ?rf) f = y"
      by (simp add: Abs_lifted_distrib_lattice_top_inverse)
    {
      fix g
      have "Rep_lifted_distrib_lattice_top (dl_iso qf) g \<le> Rep_lifted_distrib_lattice_top (dl_iso ?rf) g"
      proof (cases "g = f")
        assume "g = f"
        thus ?thesis
          using 1 4 by simp
      next
        assume 5: "g \<noteq> f"
        have "(top,up_filter (get_dense ?rf g)) = Rep_lifted_pair (Rep_dense (Abs_dense (Abs_lifted_pair (\<lambda>g . if g = f then (top,up_filter y) else Rep_lifted_pair (Rep_dense qf) g)))) g"
          by (metis (mono_tags, lifting) get_dense_char)
        also have "... = Rep_lifted_pair (Abs_lifted_pair (\<lambda>g . if g = f then (top,up_filter y) else Rep_lifted_pair (Rep_dense qf) g)) g"
          using 3 by (simp add: Abs_dense_inverse)
        also have "... = Rep_lifted_pair (Rep_dense qf) g"
          using 2 5 by (simp add: Abs_lifted_pair_inverse)
        also have "... = (top,up_filter (get_dense qf g))"
          using get_dense_char by auto
        finally have "get_dense ?rf g = get_dense qf g"
          using up_filter_injective by blast
        thus "Rep_lifted_distrib_lattice_top (dl_iso qf) g \<le> Rep_lifted_distrib_lattice_top (dl_iso ?rf) g"
          by (simp add: Abs_lifted_distrib_lattice_top_inverse)
      qed
    }
    hence "Rep_lifted_distrib_lattice_top (dl_iso qf) \<le> Rep_lifted_distrib_lattice_top (dl_iso ?rf)"
      by (simp add: le_funI)
    hence 6: "dl_iso qf \<le> dl_iso ?rf"
      by (simp add: le_funD less_eq_lifted_distrib_lattice_top.rep_eq)
    hence "qf \<le> ?rf"
      by (metis (no_types, lifting) dl_iso sup_isomorphism_ord_isomorphism)
    thus "\<exists>rf . qf \<le> rf \<and> y = Rep_lifted_distrib_lattice_top (dl_iso rf) f"
      using 4 by auto
  qed
qed

text \<open>
The commutativity property states that the same result is obtained in two ways by starting with a regular lifted pair \<open>pf\<close>:
\begin{itemize}
\item apply the Boolean algebra isomorphism to the pair; then apply a structure map \<open>f\<close> to obtain a filter of dense elements; or,
\item apply the structure map \<open>stone_phi\<close> to the pair; then apply the distributive lattice isomorphism lifted to the resulting filter.
\end{itemize}
\<close>

lemma phi_iso:
  "Rep_phi f (Rep_lifted_boolean_algebra (ba_iso pf) f) = filter_map (\<lambda>qf::('a::non_trivial_boolean_algebra,'b::distrib_lattice_top) lifted_pair dense . Rep_lifted_distrib_lattice_top (dl_iso qf) f) (stone_phi pf)"
proof -
  let ?r = "Rep_phi f"
  let ?ppf = "\<lambda>g . triple.pairs_uminus (Rep_phi g) (Rep_lifted_pair (Rep_regular pf) g)"
  have 1: "triple ?r"
    by (simp add: triple_def)
  have 2: "Rep_filter (?r (fst (Rep_lifted_pair (Rep_regular pf) f))) \<subseteq> { z . \<exists>qf . -Rep_regular pf \<le> Rep_dense qf \<and> z = get_dense qf f }"
  proof
    fix z
    obtain x where 3: "x = fst (Rep_lifted_pair (Rep_regular pf) f)"
      by simp
    assume "z \<in> Rep_filter (?r (fst (Rep_lifted_pair (Rep_regular pf) f)))"
    hence "\<up>z \<subseteq> Rep_filter (?r x)"
      using 3 filter_def by fastforce
    hence 4: "up_filter z \<le> ?r x"
      by (metis Rep_filter_cases Rep_filter_inverse less_eq_filter.rep_eq mem_Collect_eq up_filter)
    have 5: "\<forall>g . ?ppf g \<in> triple.pairs (Rep_phi g)"
      by (metis (no_types) simp_lifted_pair uminus_lifted_pair.rep_eq)
    let ?zf = "\<lambda>g . if g = f then (top,up_filter z) else triple.pairs_top"
    have 6: "\<forall>g . ?zf g \<in> triple.pairs (Rep_phi g)"
    proof
      fix g :: "('a,'b) phi"
      have "triple (Rep_phi g)"
        by (simp add: triple_def)
      hence "(top,up_filter z) \<in> triple.pairs (Rep_phi g)"
        using triple.pairs_def by force
      thus "?zf g \<in> triple.pairs (Rep_phi g)"
        by (metis simp_lifted_pair top_lifted_pair.rep_eq)
    qed
    hence "-Abs_lifted_pair ?zf = Abs_lifted_pair (\<lambda>g . triple.pairs_uminus (Rep_phi g) (?zf g))"
      by (subst uminus_lifted_pair.abs_eq) (simp_all add: eq_onp_same_args)
    also have "... = Abs_lifted_pair (\<lambda>g . if g = f then triple.pairs_uminus (Rep_phi g) (top,up_filter z) else triple.pairs_uminus (Rep_phi g) triple.pairs_top)"
      by (rule arg_cong[where f=Abs_lifted_pair]) auto
    also have "... = Abs_lifted_pair (\<lambda>g . triple.pairs_bot)"
      using 1 by (metis bot_lifted_pair.rep_eq dense_closed_top top_lifted_pair.rep_eq triple.pairs_uminus.simps uminus_lifted_pair.rep_eq)
    finally have 7: "Abs_lifted_pair ?zf \<in> dense_elements"
      by (simp add: bot_lifted_pair.abs_eq)
    let ?qf = "Abs_dense (Abs_lifted_pair ?zf)"
    have "\<forall>g . triple.pairs_less_eq (?ppf g) (?zf g)"
    proof
      fix g
      show "triple.pairs_less_eq (?ppf g) (?zf g)"
      proof (cases "g = f")
        assume 8: "g = f"
        hence 9: "?ppf g = (-x,?r x)"
          using 1 3 by (metis prod.collapse triple.pairs_uminus.simps)
        have "triple.pairs_less_eq (-x,?r x) (top,up_filter z)"
          using 1 4 by (meson inf.bot_least triple.pairs_less_eq.simps)
        thus ?thesis
          using 8 9 by simp
      next
        assume 10: "g \<noteq> f"
        have "triple.pairs_less_eq (?ppf g) triple.pairs_top"
          using 1 by (metis (no_types, hide_lams) bot.extremum top_greatest prod.collapse triple_def triple.pairs_less_eq.simps triple.phi_bot)
        thus ?thesis
          using 10 by simp
      qed
    qed
    hence "Abs_lifted_pair ?ppf \<le> Abs_lifted_pair ?zf"
      using 5 6 by (subst less_eq_lifted_pair.abs_eq) (simp_all add: eq_onp_same_args)
    hence 11: "-Rep_regular pf \<le> Rep_dense ?qf"
      using 7 by (simp add: uminus_lifted_pair_def Abs_dense_inverse)
    have "(top,up_filter (get_dense ?qf f)) = Rep_lifted_pair (Rep_dense ?qf) f"
      by (metis get_dense_char)
    also have "... = (top,up_filter z)"
      using 6 7 Abs_dense_inverse Abs_lifted_pair_inverse by force
    finally have "z = get_dense ?qf f"
      using up_filter_injective by force
    thus "z \<in> { z . \<exists>qf . -Rep_regular pf \<le> Rep_dense qf \<and> z = get_dense qf f }"
      using 11 by auto
  qed
  have 12: "Rep_filter (?r (fst (Rep_lifted_pair (Rep_regular pf) f))) \<supseteq> { z . \<exists>qf . -Rep_regular pf \<le> Rep_dense qf \<and> z = get_dense qf f }"
  proof
    fix z
    assume "z \<in> { z . \<exists>qf . -Rep_regular pf \<le> Rep_dense qf \<and> z = get_dense qf f }"
    hence "\<exists>qf . -Rep_regular pf \<le> Rep_dense qf \<and> z = get_dense qf f"
      by auto
    hence "triple.pairs_less_eq (Rep_lifted_pair (-Rep_regular pf) f) (top,up_filter z)"
      by (metis less_eq_lifted_pair.rep_eq get_dense_char)
    hence "up_filter z \<le> snd (Rep_lifted_pair (-Rep_regular pf) f)"
      using 1 by (metis (no_types, hide_lams) prod.collapse triple.pairs_less_eq.simps)
    also have "... = snd (?ppf f)"
      by (metis uminus_lifted_pair.rep_eq)
    also have "... = ?r (fst (Rep_lifted_pair (Rep_regular pf) f))"
      using 1 by (metis (no_types) prod.collapse prod.inject triple.pairs_uminus.simps)
    finally have "Rep_filter (up_filter z) \<subseteq> Rep_filter (?r (fst (Rep_lifted_pair (Rep_regular pf) f)))"
      by (simp add: less_eq_filter.rep_eq)
    hence "\<up>z \<subseteq> Rep_filter (?r (fst (Rep_lifted_pair (Rep_regular pf) f)))"
      by (metis Abs_filter_inverse mem_Collect_eq up_filter)
    thus "z \<in> Rep_filter (?r (fst (Rep_lifted_pair (Rep_regular pf) f)))"
      by blast
  qed
  have 13: "\<forall>qf\<in>Rep_filter (stone_phi pf) . Rep_lifted_distrib_lattice_top (Abs_lifted_distrib_lattice_top (get_dense qf)) f = get_dense qf f"
    by (metis Abs_lifted_distrib_lattice_top_inverse UNIV_I UNIV_def)
  have "Rep_filter (?r (fst (Rep_lifted_pair (Rep_regular pf) f))) = { z . \<exists>qf\<in>stone_phi_set pf . z = get_dense qf f }"
    using 2 12 by simp
  hence "?r (fst (Rep_lifted_pair (Rep_regular pf) f)) = Abs_filter { z . \<exists>qf\<in>stone_phi_set pf . z = get_dense qf f }"
    by (metis Rep_filter_inverse)
  hence "?r (Rep_lifted_boolean_algebra (ba_iso pf) f) = Abs_filter { z . \<exists>qf\<in>Rep_filter (stone_phi pf) . z = Rep_lifted_distrib_lattice_top (dl_iso qf) f }"
    using 13 by (simp add: Abs_filter_inverse stone_phi_set_filter stone_phi_def Abs_lifted_boolean_algebra_inverse)
  thus ?thesis
    by (simp add: image_def)
qed

end

