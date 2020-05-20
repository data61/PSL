(* Title:      Lattice Basics
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Lattice Basics\<close>

text \<open>
This theory provides notations, basic definitions and facts of lattice-related structures used throughout the subsequent development.
\<close>

theory Lattice_Basics

imports Main

begin

subsection \<open>General Facts and Notations\<close>

text \<open>
The following results extend basic Isabelle/HOL facts.
\<close>

lemma imp_as_conj:
  assumes "P x \<Longrightarrow> Q x"
  shows "P x \<and> Q x \<longleftrightarrow> P x"
  using assms by auto

lemma if_distrib_2:
  "f (if c then x else y) (if c then z else w) = (if c then f x z else f y w)"
  by simp

lemma left_invertible_inj:
  "(\<forall>x . g (f x) = x) \<Longrightarrow> inj f"
  by (metis injI)

lemma invertible_bij:
  assumes "\<forall>x . g (f x) = x"
      and "\<forall>y . f (g y) = y"
    shows "bij f"
  by (metis assms bijI')

lemma finite_ne_subset_induct [consumes 3, case_names singleton insert]:
  assumes "finite F"
      and "F \<noteq> {}"
      and "F \<subseteq> S"
      and singleton: "\<And>x . P {x}"
      and insert: "\<And>x F . finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> F \<subseteq> S \<Longrightarrow> x \<in> S \<Longrightarrow> x \<notin> F \<Longrightarrow> P F \<Longrightarrow> P (insert x F)"
    shows "P F"
  using assms(1-3)
  apply (induct rule: finite_ne_induct)
  apply (simp add: singleton)
  by (simp add: insert)

lemma finite_set_of_finite_funs_pred:
  assumes "finite { x::'a . True }"
      and "finite { y::'b . P y }"
    shows "finite { f . (\<forall>x::'a . P (f x)) }"
  using assms finite_set_of_finite_funs by force

text \<open>
We use the following notations for the join, meet and complement operations.
Changing the precedence of the unary complement allows us to write terms like \<open>--x\<close> instead of \<open>-(-x)\<close>.
\<close>

context sup
begin

notation sup (infixl "\<squnion>" 65)

definition additive :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "additive f \<equiv> \<forall>x y . f (x \<squnion> y) = f x \<squnion> f y"

end

context inf
begin

notation inf (infixl "\<sqinter>" 67)

end

context uminus
begin

no_notation uminus ("- _" [81] 80)

notation uminus ("- _" [80] 80)

end

subsection \<open>Orders\<close>

text \<open>
We use the following definition of monotonicity for operations defined in classes.
The standard \<open>mono\<close> places a sort constraint on the target type.
We also give basic properties of Galois connections and lift orders to functions.
\<close>

context ord
begin

definition isotone :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "isotone f \<equiv> \<forall>x y . x \<le> y \<longrightarrow> f x \<le> f y"

definition galois :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "galois l u \<equiv> \<forall>x y . l x \<le> y \<longleftrightarrow> x \<le> u y"

definition lifted_less_eq :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" ("(_ \<le>\<le> _)" [51, 51] 50)
  where "f \<le>\<le> g \<equiv> \<forall>x . f x \<le> g x"

end

context order
begin

lemma order_lesseq_imp:
  "(\<forall>z . x \<le> z \<longrightarrow> y \<le> z) \<longleftrightarrow> y \<le> x"
  using order_trans by blast

lemma galois_char:
  "galois l u \<longleftrightarrow> (\<forall>x . x \<le> u (l x)) \<and> (\<forall>x . l (u x) \<le> x) \<and> isotone l \<and> isotone u"
  apply (rule iffI)
  apply (metis (full_types) galois_def isotone_def order_refl order_trans)
  using galois_def isotone_def order_trans by blast

lemma galois_closure:
  "galois l u \<Longrightarrow> l x = l (u (l x)) \<and> u x = u (l (u x))"
  by (simp add: galois_char isotone_def antisym)

lemma lifted_reflexive:
  "f = g \<Longrightarrow> f \<le>\<le> g"
  by (simp add: lifted_less_eq_def)

lemma lifted_transitive:
  "f \<le>\<le> g \<Longrightarrow> g \<le>\<le> h \<Longrightarrow> f \<le>\<le> h"
  using lifted_less_eq_def order_trans by blast

lemma lifted_antisymmetric:
  "f \<le>\<le> g \<Longrightarrow> g \<le>\<le> f \<Longrightarrow> f = g"
  by (metis (full_types) antisym ext lifted_less_eq_def)

text \<open>
If the image of a finite non-empty set under \<open>f\<close> is a totally ordered, there is an element that minimises the value of \<open>f\<close>.
\<close>

lemma finite_set_minimal:
  assumes "finite s"
      and "s \<noteq> {}"
      and "\<forall>x\<in>s . \<forall>y\<in>s . f x \<le> f y \<or> f y \<le> f x"
    shows "\<exists>m\<in>s . \<forall>z\<in>s . f m \<le> f z"
  apply (rule finite_ne_subset_induct[where S=s])
  apply (rule assms(1))
  apply (rule assms(2))
  apply simp
  apply simp
  by (metis assms(3) insert_iff order_trans subsetD)

end

subsection \<open>Semilattices\<close>

text \<open>
The following are basic facts in semilattices.
\<close>

context semilattice_sup
begin

lemma sup_left_isotone:
  "x \<le> y \<Longrightarrow> x \<squnion> z \<le> y \<squnion> z"
  using sup.mono by blast

lemma sup_right_isotone:
  "x \<le> y \<Longrightarrow> z \<squnion> x \<le> z \<squnion> y"
  using sup.mono by blast

lemma sup_left_divisibility:
  "x \<le> y \<longleftrightarrow> (\<exists>z . x \<squnion> z = y)"
  using sup.absorb2 sup.cobounded1 by blast

lemma sup_right_divisibility:
  "x \<le> y \<longleftrightarrow> (\<exists>z . z \<squnion> x = y)"
  by (metis sup.cobounded2 sup.orderE)

lemma sup_same_context:
  "x \<le> y \<squnion> z \<Longrightarrow> y \<le> x \<squnion> z \<Longrightarrow> x \<squnion> z = y \<squnion> z"
  by (simp add: le_iff_sup sup_left_commute)

lemma sup_relative_same_increasing:
  "x \<le> y \<Longrightarrow> x \<squnion> z = x \<squnion> w \<Longrightarrow> y \<squnion> z = y \<squnion> w"
  using sup.assoc sup_right_divisibility by auto

end

text \<open>
Every bounded semilattice is a commutative monoid.
Finite sums defined in commutative monoids are available via the following sublocale.
\<close>

context bounded_semilattice_sup_bot
begin

sublocale sup_monoid: comm_monoid_add where plus = sup and zero = bot
  apply unfold_locales
  apply (simp add: sup_assoc)
  apply (simp add: sup_commute)
  by simp

end

context semilattice_inf
begin

lemma inf_same_context:
  "x \<le> y \<sqinter> z \<Longrightarrow> y \<le> x \<sqinter> z \<Longrightarrow> x \<sqinter> z = y \<sqinter> z"
  using antisym by auto

end

text \<open>
The following class requires only the existence of upper bounds, which is a property common to bounded semilattices and (not necessarily bounded) lattices.
We use it in our development of filters.
\<close>

class directed_semilattice_inf = semilattice_inf +
  assumes ub: "\<exists>z . x \<le> z \<and> y \<le> z"

text \<open>
We extend the \<open>inf\<close> sublocale, which dualises the order in semilattices, to bounded semilattices.
\<close>

context bounded_semilattice_inf_top
begin

subclass directed_semilattice_inf
  apply unfold_locales
  using top_greatest by blast

sublocale inf: bounded_semilattice_sup_bot where sup = inf and less_eq = greater_eq and less = greater and bot = top
  by unfold_locales (simp_all add: less_le_not_le)

end

subsection \<open>Lattices\<close>

context lattice
begin

subclass directed_semilattice_inf
  apply unfold_locales
  using sup_ge1 sup_ge2 by blast

definition dual_additive :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "dual_additive f \<equiv> \<forall>x y . f (x \<squnion> y) = f x \<sqinter> f y"

end

text \<open>
Not every bounded lattice has complements, but two elements might still be complements of each other as captured in the following definition.
In this situation we can apply, for example, the shunting property shown below.
We introduce most definitions using the \<open>abbreviation\<close> command.
\<close>

context bounded_lattice
begin

abbreviation "complement x y \<equiv> x \<squnion> y = top \<and> x \<sqinter> y = bot"

lemma complement_symmetric:
  "complement x y \<Longrightarrow> complement y x"
  by (simp add: inf.commute sup.commute)

definition conjugate :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "conjugate f g \<equiv> \<forall>x y . f x \<sqinter> y = bot \<longleftrightarrow> x \<sqinter> g y = bot"

end

class dense_lattice = bounded_lattice +
  assumes bot_meet_irreducible: "x \<sqinter> y = bot \<longrightarrow> x = bot \<or> y = bot"

context distrib_lattice
begin

lemma relative_equality:
  "x \<squnion> z = y \<squnion> z \<Longrightarrow> x \<sqinter> z = y \<sqinter> z \<Longrightarrow> x = y"
  by (metis inf.commute inf_sup_absorb inf_sup_distrib2)

end

text \<open>
Distributive lattices with a greatest element are widely used in the construction theorem for Stone algebras.
\<close>

class distrib_lattice_bot = bounded_lattice_bot + distrib_lattice

class distrib_lattice_top = bounded_lattice_top + distrib_lattice

class bounded_distrib_lattice = bounded_lattice + distrib_lattice
begin

subclass distrib_lattice_bot ..

subclass distrib_lattice_top ..

lemma complement_shunting:
  assumes "complement z w"
    shows "z \<sqinter> x \<le> y \<longleftrightarrow> x \<le> w \<squnion> y"
proof
  assume 1: "z \<sqinter> x \<le> y"
  have "x = (z \<squnion> w) \<sqinter> x"
    by (simp add: assms)
  also have "... \<le> y \<squnion> (w \<sqinter> x)"
    using 1 sup.commute sup.left_commute inf_sup_distrib2 sup_right_divisibility by fastforce
  also have "... \<le> w \<squnion> y"
    by (simp add: inf.coboundedI1)
  finally show "x \<le> w \<squnion> y"
    .
next
  assume "x \<le> w \<squnion> y"
  hence "z \<sqinter> x \<le> z \<sqinter> (w \<squnion> y)"
    using inf.sup_right_isotone by auto
  also have "... = z \<sqinter> y"
    by (simp add: assms inf_sup_distrib1)
  also have "... \<le> y"
    by simp
  finally show "z \<sqinter> x \<le> y"
    .
qed

end

subsection \<open>Linear Orders\<close>

text \<open>
We next consider lattices with a linear order structure.
In such lattices, join and meet are selective operations, which give the maximum and the minimum of two elements, respectively.
Moreover, the lattice is automatically distributive.
\<close>

class bounded_linorder = linorder + order_bot + order_top

class linear_lattice = lattice + linorder
begin

lemma max_sup:
  "max x y = x \<squnion> y"
  by (metis max.boundedI max.cobounded1 max.cobounded2 sup_unique)

lemma min_inf:
  "min x y = x \<sqinter> y"
  by (simp add: inf.absorb1 inf.absorb2 min_def)

lemma sup_inf_selective:
  "(x \<squnion> y = x \<and> x \<sqinter> y = y) \<or> (x \<squnion> y = y \<and> x \<sqinter> y = x)"
  by (meson inf.absorb1 inf.absorb2 le_cases sup.absorb1 sup.absorb2)

lemma sup_selective:
  "x \<squnion> y = x \<or> x \<squnion> y = y"
  using sup_inf_selective by blast

lemma inf_selective:
  "x \<sqinter> y = x \<or> x \<sqinter> y = y"
  using sup_inf_selective by blast

subclass distrib_lattice
  apply unfold_locales
  by (metis inf_selective antisym distrib_sup_le inf.commute inf_le2)

lemma sup_less_eq:
  "x \<le> y \<squnion> z \<longleftrightarrow> x \<le> y \<or> x \<le> z"
  by (metis le_supI1 le_supI2 sup_selective)

lemma inf_less_eq:
  "x \<sqinter> y \<le> z \<longleftrightarrow> x \<le> z \<or> y \<le> z"
  by (metis inf.coboundedI1 inf.coboundedI2 inf_selective)

lemma sup_inf_sup:
  "x \<squnion> y = (x \<squnion> y) \<squnion> (x \<sqinter> y)"
  by (metis sup_commute sup_inf_absorb sup_left_commute)

end

text \<open>
The following class derives additional properties if the linear order of the lattice has a least and a greatest element.
\<close>

class linear_bounded_lattice = bounded_lattice + linorder
begin

subclass linear_lattice ..

subclass bounded_linorder ..

subclass bounded_distrib_lattice ..

lemma sup_dense:
  "x \<noteq> top \<Longrightarrow> y \<noteq> top \<Longrightarrow> x \<squnion> y \<noteq> top"
  by (metis sup_selective)

lemma inf_dense:
  "x \<noteq> bot \<Longrightarrow> y \<noteq> bot \<Longrightarrow> x \<sqinter> y \<noteq> bot"
  by (metis inf_selective)

lemma sup_not_bot:
  "x \<noteq> bot \<Longrightarrow> x \<squnion> y \<noteq> bot"
  by simp

lemma inf_not_top:
  "x \<noteq> top \<Longrightarrow> x \<sqinter> y \<noteq> top"
  by simp

subclass dense_lattice
  apply unfold_locales
  using inf_dense by blast

end

text \<open>
Every bounded linear order can be expanded to a bounded lattice.
Join and meet are maximum and minimum, respectively.
\<close>

class linorder_lattice_expansion = bounded_linorder + sup + inf +
  assumes sup_def [simp]: "x \<squnion> y = max x y"
  assumes inf_def [simp]: "x \<sqinter> y = min x y"
begin

subclass linear_bounded_lattice
  apply unfold_locales
  by auto

end

subsection \<open>Non-trivial Algebras\<close>

text \<open>
Some results, such as the existence of certain filters, require that the algebras are not trivial.
This is not an assumption of the order and lattice classes that come with Isabelle/HOL; for example, \<open>bot = top\<close> may hold in bounded lattices.
\<close>

class non_trivial =
  assumes consistent: "\<exists>x y . x \<noteq> y"

class non_trivial_order = non_trivial + order

class non_trivial_order_bot = non_trivial_order + order_bot

class non_trivial_bounded_order = non_trivial_order_bot + order_top
begin

lemma bot_not_top:
  "bot \<noteq> top"
proof -
  from consistent obtain x y :: 'a where "x \<noteq> y"
    by auto
  thus ?thesis
    by (metis bot_less top.extremum_strict)
qed

end

subsection \<open>Homomorphisms\<close>

text \<open>
This section gives definitions of lattice homomorphisms and isomorphisms and basic properties.
\<close>

class sup_inf_top_bot_uminus = sup + inf + top + bot + uminus
class sup_inf_top_bot_uminus_ord = sup_inf_top_bot_uminus + ord

context boolean_algebra
begin

subclass sup_inf_top_bot_uminus_ord .

end

abbreviation sup_homomorphism :: "('a::sup \<Rightarrow> 'b::sup) \<Rightarrow> bool"
  where "sup_homomorphism f \<equiv> \<forall>x y . f (x \<squnion> y) = f x \<squnion> f y"

abbreviation inf_homomorphism :: "('a::inf \<Rightarrow> 'b::inf) \<Rightarrow> bool"
  where "inf_homomorphism f \<equiv> \<forall>x y . f (x \<sqinter> y) = f x \<sqinter> f y"

abbreviation bot_homomorphism :: "('a::bot \<Rightarrow> 'b::bot) \<Rightarrow> bool"
  where "bot_homomorphism f \<equiv> f bot = bot"

abbreviation top_homomorphism :: "('a::top \<Rightarrow> 'b::top) \<Rightarrow> bool"
  where "top_homomorphism f \<equiv> f top = top"

abbreviation minus_homomorphism :: "('a::minus \<Rightarrow> 'b::minus) \<Rightarrow> bool"
  where "minus_homomorphism f \<equiv> \<forall>x y . f (x - y) = f x - f y"

abbreviation uminus_homomorphism :: "('a::uminus \<Rightarrow> 'b::uminus) \<Rightarrow> bool"
  where "uminus_homomorphism f \<equiv> \<forall>x . f (-x) = -f x"

abbreviation sup_inf_homomorphism :: "('a::{sup,inf} \<Rightarrow> 'b::{sup,inf}) \<Rightarrow> bool"
  where "sup_inf_homomorphism f \<equiv> sup_homomorphism f \<and> inf_homomorphism f"

abbreviation sup_inf_top_homomorphism :: "('a::{sup,inf,top} \<Rightarrow> 'b::{sup,inf,top}) \<Rightarrow> bool"
  where "sup_inf_top_homomorphism f \<equiv> sup_inf_homomorphism f \<and> top_homomorphism f"

abbreviation sup_inf_top_bot_homomorphism :: "('a::{sup,inf,top,bot} \<Rightarrow> 'b::{sup,inf,top,bot}) \<Rightarrow> bool"
  where "sup_inf_top_bot_homomorphism f \<equiv> sup_inf_top_homomorphism f \<and> bot_homomorphism f"

abbreviation bounded_lattice_homomorphism :: "('a::bounded_lattice \<Rightarrow> 'b::bounded_lattice) \<Rightarrow> bool"
  where "bounded_lattice_homomorphism f \<equiv> sup_inf_top_bot_homomorphism f"

abbreviation sup_inf_top_bot_uminus_homomorphism :: "('a::sup_inf_top_bot_uminus \<Rightarrow> 'b::sup_inf_top_bot_uminus) \<Rightarrow> bool"
  where "sup_inf_top_bot_uminus_homomorphism f \<equiv> sup_inf_top_bot_homomorphism f \<and> uminus_homomorphism f"

abbreviation sup_inf_top_bot_uminus_ord_homomorphism :: "('a::sup_inf_top_bot_uminus_ord \<Rightarrow> 'b::sup_inf_top_bot_uminus_ord) \<Rightarrow> bool"
  where "sup_inf_top_bot_uminus_ord_homomorphism f \<equiv> sup_inf_top_bot_uminus_homomorphism f \<and> (\<forall>x y . x \<le> y \<longrightarrow> f x \<le> f y)"

abbreviation sup_inf_top_isomorphism :: "('a::{sup,inf,top} \<Rightarrow> 'b::{sup,inf,top}) \<Rightarrow> bool"
  where "sup_inf_top_isomorphism f \<equiv> sup_inf_top_homomorphism f \<and> bij f"

abbreviation bounded_lattice_top_isomorphism :: "('a::bounded_lattice_top \<Rightarrow> 'b::bounded_lattice_top) \<Rightarrow> bool"
  where "bounded_lattice_top_isomorphism f \<equiv> sup_inf_top_isomorphism f"

abbreviation sup_inf_top_bot_uminus_isomorphism :: "('a::sup_inf_top_bot_uminus \<Rightarrow> 'b::sup_inf_top_bot_uminus) \<Rightarrow> bool"
  where "sup_inf_top_bot_uminus_isomorphism f \<equiv> sup_inf_top_bot_uminus_homomorphism f \<and> bij f"

abbreviation boolean_algebra_isomorphism :: "('a::boolean_algebra \<Rightarrow> 'b::boolean_algebra) \<Rightarrow> bool"
  where "boolean_algebra_isomorphism f \<equiv> sup_inf_top_bot_uminus_isomorphism f \<and> minus_homomorphism f"

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

lemma minus_homomorphism_default:
  assumes "\<forall>x y::'a::{inf,minus,uminus} . x - y = x \<sqinter> -y"
      and "\<forall>x y::'b::{inf,minus,uminus} . x - y = x \<sqinter> -y"
      and "inf_homomorphism (f::'a \<Rightarrow> 'b)"
      and "uminus_homomorphism f"
    shows "minus_homomorphism f"
  by (simp add: assms)

end

