(* Title:      Relation Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Relation Algebras\<close>

text \<open>
The main structures introduced in this theory are Stone relation algebras.
They generalise Tarski's relation algebras \cite{Tarski1941} by weakening the Boolean algebra lattice structure to a Stone algebra.
Our motivation is to generalise relation-algebraic methods from unweighted graphs to weighted graphs.
Unlike unweighted graphs, weighted graphs do not form a Boolean algebra because there is no complement operation on the edge weights.
However, edge weights form a Stone algebra, and matrices over edge weights (that is, weighted graphs) form a Stone relation algebra.

The development in this theory is described in our papers \cite{Guttmann2016c,Guttmann2017b}.
Our main application there is the verification of Prim's minimum spanning tree algorithm.
Related work about fuzzy relations \cite{Goguen1967,Winter2001b}, Dedekind categories \cite{KawaharaFurusawa2001} and rough relations \cite{Comer1993,Pawlak1996} is also discussed in these papers.
In particular, Stone relation algebras do not assume that the underlying lattice is complete or a Heyting algebra, and they do not assume that composition has residuals.

We proceed in two steps.
First, we study the positive fragment in the form of single-object bounded distributive allegories \cite{FreydScedrov1990}.
Second, we extend these structures by a pseudocomplement operation with additional axioms to obtain Stone relation algebras.

Tarski's relation algebras are then obtained by a simple extension that imposes a Boolean algebra.
See, for example, \cite{BirdMoor1997,HirschHodkinson2002,Maddux1996,Maddux2006,Schmidt2011,SchmidtStroehlein1993} for further details about relations and relation algebras, and \cite{AndrekaMikulas2011,BredihinSchein1978} for algebras of relations with a smaller signature.
\<close>

theory Relation_Algebras

imports Stone_Algebras.P_Algebras Semirings

begin

subsection \<open>Single-Object Bounded Distributive Allegories\<close>

text \<open>
We start with developing bounded distributive allegories.
The following definitions concern properties of relations that require converse in addition to lattice and semiring operations.
\<close>

class conv =
  fixes conv :: "'a \<Rightarrow> 'a" ("_\<^sup>T" [100] 100)

class bounded_distrib_allegory_signature = inf + sup + times + conv + bot + top + one + ord
begin

subclass times_one_ord .
subclass times_top .

abbreviation total_var      :: "'a \<Rightarrow> bool" where "total_var x      \<equiv> 1 \<le> x * x\<^sup>T"
abbreviation surjective_var :: "'a \<Rightarrow> bool" where "surjective_var x \<equiv> 1 \<le> x\<^sup>T * x"
abbreviation univalent      :: "'a \<Rightarrow> bool" where "univalent x      \<equiv> x\<^sup>T * x \<le> 1"
abbreviation injective      :: "'a \<Rightarrow> bool" where "injective x      \<equiv> x * x\<^sup>T \<le> 1"

abbreviation mapping        :: "'a \<Rightarrow> bool" where "mapping x        \<equiv> univalent x \<and> total x"
abbreviation bijective      :: "'a \<Rightarrow> bool" where "bijective x      \<equiv> injective x \<and> surjective x"

abbreviation point          :: "'a \<Rightarrow> bool" where "point x          \<equiv> vector x \<and> bijective x"
abbreviation arc            :: "'a \<Rightarrow> bool" where "arc x            \<equiv> bijective (x * top) \<and> bijective (x\<^sup>T * top)" (* earlier name: atom *)

abbreviation symmetric      :: "'a \<Rightarrow> bool" where "symmetric x      \<equiv> x\<^sup>T = x"
abbreviation antisymmetric  :: "'a \<Rightarrow> bool" where "antisymmetric x  \<equiv> x \<sqinter> x\<^sup>T \<le> 1"
abbreviation asymmetric     :: "'a \<Rightarrow> bool" where "asymmetric x     \<equiv> x \<sqinter> x\<^sup>T = bot"
abbreviation linear         :: "'a \<Rightarrow> bool" where "linear x         \<equiv> x \<squnion> x\<^sup>T = top"

abbreviation equivalence    :: "'a \<Rightarrow> bool" where "equivalence x    \<equiv> preorder x \<and> symmetric x"
abbreviation order          :: "'a \<Rightarrow> bool" where "order x          \<equiv> preorder x \<and> antisymmetric x"
abbreviation linear_order   :: "'a \<Rightarrow> bool" where "linear_order x   \<equiv> order x \<and> linear x"

end

text \<open>
We reuse the relation algebra axioms given in \cite{Maddux1996} except for one -- see lemma \<open>conv_complement_sub\<close> below -- which we replace with the Dedekind rule (or modular law) \<open>dedekind_1\<close>.
The Dedekind rule or variants of it are known from \cite{BirdMoor1997,FreydScedrov1990,KawaharaFurusawaMori1999,SchmidtStroehlein1993}.
We add \<open>comp_left_zero\<close>, which follows in relation algebras but not in the present setting.
The main change is that only a bounded distributive lattice is required, not a Boolean algebra.
\<close>

class bounded_distrib_allegory = bounded_distrib_lattice + times + one + conv +
  assumes comp_associative      : "(x * y) * z = x * (y * z)"
  assumes comp_right_dist_sup   : "(x \<squnion> y) * z = (x * z) \<squnion> (y * z)"
  assumes comp_left_zero  [simp]: "bot * x = bot"
  assumes comp_left_one   [simp]: "1 * x = x"
  assumes conv_involutive [simp]: "x\<^sup>T\<^sup>T = x"
  assumes conv_dist_sup         : "(x \<squnion> y)\<^sup>T = x\<^sup>T \<squnion> y\<^sup>T"
  assumes conv_dist_comp        : "(x * y)\<^sup>T = y\<^sup>T * x\<^sup>T"
  assumes dedekind_1            : "x * y \<sqinter> z \<le> x * (y \<sqinter> (x\<^sup>T * z))"
begin

subclass bounded_distrib_allegory_signature .

text \<open>
Many properties of relation algebras already follow in bounded distributive allegories.
\<close>

lemma conv_isotone:
  "x \<le> y \<Longrightarrow> x\<^sup>T \<le> y\<^sup>T"
  by (metis conv_dist_sup le_iff_sup)

lemma conv_order:
  "x \<le> y \<longleftrightarrow> x\<^sup>T \<le> y\<^sup>T"
  using conv_isotone by fastforce

lemma conv_bot [simp]:
  "bot\<^sup>T = bot"
  using conv_order bot_unique by force

lemma conv_top [simp]:
  "top\<^sup>T = top"
  by (metis conv_involutive conv_order eq_iff top_greatest)

lemma conv_dist_inf:
  "(x \<sqinter> y)\<^sup>T = x\<^sup>T \<sqinter> y\<^sup>T"
  apply (rule antisym)
  using conv_order apply simp
  by (metis conv_order conv_involutive inf.boundedI inf.cobounded1 inf.cobounded2)

lemma conv_inf_bot_iff:
  "bot = x\<^sup>T \<sqinter> y \<longleftrightarrow> bot = x \<sqinter> y\<^sup>T"
  using conv_dist_inf conv_bot by fastforce

lemma conv_one [simp]:
  "1\<^sup>T = 1"
  by (metis comp_left_one conv_dist_comp conv_involutive)

lemma comp_left_dist_sup:
  "(x * y) \<squnion> (x * z) = x * (y \<squnion> z)"
  by (metis comp_right_dist_sup conv_involutive conv_dist_sup conv_dist_comp)

lemma comp_right_isotone:
  "x \<le> y \<Longrightarrow> z * x \<le> z * y"
  by (simp add: comp_left_dist_sup sup.absorb_iff1)

lemma comp_left_isotone:
  "x \<le> y \<Longrightarrow> x * z \<le> y * z"
  by (metis comp_right_dist_sup le_iff_sup)

lemma comp_isotone:
  "x \<le> y \<Longrightarrow> w \<le> z \<Longrightarrow> x * w \<le> y * z"
  using comp_left_isotone comp_right_isotone order.trans by blast

lemma comp_left_subdist_inf:
  "(x \<sqinter> y) * z \<le> x * z \<sqinter> y * z"
  by (simp add: comp_left_isotone)

lemma comp_left_increasing_sup:
  "x * y \<le> (x \<squnion> z) * y"
  by (simp add: comp_left_isotone)

lemma comp_right_subdist_inf:
  "x * (y \<sqinter> z) \<le> x * y \<sqinter> x * z"
  by (simp add: comp_right_isotone)

lemma comp_right_increasing_sup:
  "x * y \<le> x * (y \<squnion> z)"
  by (simp add: comp_right_isotone)

lemma comp_right_zero [simp]:
  "x * bot = bot"
  by (metis comp_left_zero conv_dist_comp conv_involutive)

lemma comp_right_one [simp]:
  "x * 1 = x"
  by (metis comp_left_one conv_dist_comp conv_involutive)

lemma comp_left_conjugate:
  "conjugate (\<lambda>y . x * y) (\<lambda>y . x\<^sup>T * y)"
  apply (unfold conjugate_def, intro allI)
  by (metis comp_right_zero bot.extremum_unique conv_involutive dedekind_1 inf.commute)

lemma comp_right_conjugate:
  "conjugate (\<lambda>y . y * x) (\<lambda>y . y * x\<^sup>T)"
  apply (unfold conjugate_def, intro allI)
  by (metis comp_left_conjugate[unfolded conjugate_def] conv_inf_bot_iff conv_dist_comp conv_involutive)

text \<open>
We still obtain a semiring structure.
\<close>

subclass bounded_idempotent_semiring
  by (unfold_locales)
  (auto simp: comp_right_isotone comp_right_dist_sup comp_associative comp_left_dist_sup)

sublocale inf: semiring_0 sup bot inf
  by (unfold_locales, auto simp: inf_sup_distrib2 inf_sup_distrib1 inf_assoc)

lemma schroeder_1:
  "x * y \<sqinter> z = bot \<longleftrightarrow> x\<^sup>T * z \<sqinter> y = bot"
  using abel_semigroup.commute comp_left_conjugate conjugate_def inf.abel_semigroup_axioms by fastforce

lemma schroeder_2:
  "x * y \<sqinter> z = bot \<longleftrightarrow> z * y\<^sup>T \<sqinter> x = bot"
  by (metis comp_right_conjugate conjugate_def inf_commute)

lemma comp_additive:
  "additive (\<lambda>y . x * y) \<and> additive (\<lambda>y . x\<^sup>T * y) \<and> additive (\<lambda>y . y * x) \<and> additive (\<lambda>y . y * x\<^sup>T)"
  by (simp add: comp_left_dist_sup additive_def comp_right_dist_sup)

lemma dedekind_2:
  "y * x \<sqinter> z \<le> (y \<sqinter> (z * x\<^sup>T)) * x"
  by (metis conv_dist_inf conv_order conv_dist_comp dedekind_1)

text \<open>
The intersection with a vector can still be exported from the first argument of a composition, and many other properties of vectors and covectors continue to hold.
\<close>

lemma vector_inf_comp:
  "vector x \<Longrightarrow> (x \<sqinter> y) * z = x \<sqinter> (y * z)"
  apply (rule antisym)
  apply (metis comp_left_subdist_inf comp_right_isotone inf.sup_left_isotone order_lesseq_imp top_greatest)
  by (metis comp_left_isotone comp_right_isotone dedekind_2 inf_commute inf_mono order_refl order_trans top_greatest)

lemma vector_inf_closed:
  "vector x \<Longrightarrow> vector y \<Longrightarrow> vector (x \<sqinter> y)"
  by (simp add: vector_inf_comp)

lemma vector_inf_one_comp:
  "vector x \<Longrightarrow> (x \<sqinter> 1) * y = x \<sqinter> y"
  by (simp add: vector_inf_comp)

lemma covector_inf_comp_1:
  assumes "vector x"
    shows "(y \<sqinter> x\<^sup>T) * z = (y \<sqinter> x\<^sup>T) * (x \<sqinter> z)"
proof -
  have "(y \<sqinter> x\<^sup>T) * z \<le> (y \<sqinter> x\<^sup>T) * (z \<sqinter> ((y\<^sup>T \<sqinter> x) * top))"
    by (metis inf_top_right dedekind_1 conv_dist_inf conv_involutive)
  also have "... \<le> (y \<sqinter> x\<^sup>T) * (x \<sqinter> z)"
    by (metis assms comp_left_isotone comp_right_isotone inf_le2 inf_mono order_refl inf_commute)
  finally show ?thesis
    by (simp add: comp_right_isotone antisym)
qed

lemma covector_inf_comp_2:
  assumes "vector x"
    shows "y * (x \<sqinter> z) = (y \<sqinter> x\<^sup>T) * (x \<sqinter> z)"
proof -
  have "y * (x \<sqinter> z) \<le> (y \<sqinter> (top * (x \<sqinter> z)\<^sup>T)) * (x \<sqinter> z)"
    by (metis dedekind_2 inf_top_right)
  also have "... \<le> (y \<sqinter> x\<^sup>T) * (x \<sqinter> z)"
    by (metis assms comp_left_isotone conv_dist_comp conv_order conv_top eq_refl inf_le1 inf_mono)
  finally show ?thesis
    using comp_left_subdist_inf antisym by auto
qed

lemma covector_inf_comp_3:
  "vector x \<Longrightarrow> (y \<sqinter> x\<^sup>T) * z = y * (x \<sqinter> z)"
  by (metis covector_inf_comp_1 covector_inf_comp_2)

lemma covector_inf_closed:
  "covector x \<Longrightarrow> covector y \<Longrightarrow> covector (x \<sqinter> y)"
  by (metis comp_right_subdist_inf inf.antisym top_left_mult_increasing)

lemma vector_conv_covector:
  "vector v \<longleftrightarrow> covector (v\<^sup>T)"
  by (metis conv_dist_comp conv_involutive conv_top)

lemma covector_conv_vector:
  "covector v \<longleftrightarrow> vector (v\<^sup>T)"
  by (simp add: vector_conv_covector)

lemma covector_comp_inf:
  "covector z \<Longrightarrow> x * (y \<sqinter> z) = x * y \<sqinter> z"
  apply (rule antisym)
  apply (metis comp_isotone comp_right_subdist_inf inf.boundedE inf.boundedI inf.cobounded2 top.extremum)
  by (metis comp_left_isotone comp_right_isotone dedekind_1 inf_commute inf_mono order_refl order_trans top_greatest)

lemma vector_restrict_comp_conv:
  "vector x \<Longrightarrow> x \<sqinter> y \<le> x\<^sup>T * y"
  by (metis covector_inf_comp_3 eq_refl inf.sup_monoid.add_commute inf_top_right le_supE sup.orderE top_left_mult_increasing)

lemma covector_restrict_comp_conv:
  "covector x \<Longrightarrow> y \<sqinter> x \<le> y * x\<^sup>T"
  by (metis conv_dist_comp conv_dist_inf conv_order conv_top inf.sup_monoid.add_commute vector_restrict_comp_conv)

lemma covector_comp_inf_1:
  "covector x \<Longrightarrow> (y \<sqinter> x) * z = y * (x\<^sup>T \<sqinter> z)"
  using covector_conv_vector covector_inf_comp_3 by fastforce

text \<open>
We still have two ways to represent surjectivity and totality.
\<close>

lemma surjective_var:
  "surjective x \<longleftrightarrow> surjective_var x"
proof
  assume "surjective x"
  thus "surjective_var x"
    by (metis dedekind_2 comp_left_one inf_absorb2 top_greatest)
next
  assume "surjective_var x"
  hence "x\<^sup>T * (x * top) = top"
    by (metis comp_left_isotone comp_associative comp_left_one top_le)
  thus "surjective x"
    by (metis comp_right_isotone conv_top conv_dist_comp conv_involutive top_greatest top_le)
qed

lemma total_var:
  "total x \<longleftrightarrow> total_var x"
  by (metis conv_top conv_dist_comp conv_involutive surjective_var)

lemma surjective_conv_total:
  "surjective x \<longleftrightarrow> total (x\<^sup>T)"
  by (metis conv_top conv_dist_comp conv_involutive)

lemma total_conv_surjective:
  "total x \<longleftrightarrow> surjective (x\<^sup>T)"
  by (simp add: surjective_conv_total)

lemma injective_conv_univalent:
  "injective x \<longleftrightarrow> univalent (x\<^sup>T)"
  by simp

lemma univalent_conv_injective:
  "univalent x \<longleftrightarrow> injective (x\<^sup>T)"
  by simp

text \<open>
We continue with studying further closure properties.
\<close>

lemma univalent_bot_closed:
  "univalent bot"
  by simp

lemma univalent_one_closed:
  "univalent 1"
  by simp

lemma univalent_inf_closed:
  "univalent x \<Longrightarrow> univalent (x \<sqinter> y)"
  by (metis comp_left_subdist_inf comp_right_subdist_inf conv_dist_inf inf.cobounded1 order_lesseq_imp)

lemma univalent_mult_closed:
  assumes "univalent x"
      and "univalent y"
    shows "univalent (x * y)"
proof -
  have "(x * y)\<^sup>T * x \<le> y\<^sup>T"
    by (metis assms(1) comp_left_isotone comp_right_one conv_one conv_order comp_associative conv_dist_comp conv_involutive)
  thus ?thesis
    by (metis assms(2) comp_left_isotone comp_associative dual_order.trans)
qed

lemma injective_bot_closed:
  "injective bot"
  by simp

lemma injective_one_closed:
  "injective 1"
  by simp

lemma injective_inf_closed:
  "injective x \<Longrightarrow> injective (x \<sqinter> y)"
  by (metis conv_dist_inf injective_conv_univalent univalent_inf_closed)

lemma injective_mult_closed:
  "injective x \<Longrightarrow> injective y \<Longrightarrow> injective (x * y)"
  by (metis injective_conv_univalent conv_dist_comp univalent_mult_closed)

lemma mapping_one_closed:
  "mapping 1"
  by simp

lemma mapping_mult_closed:
  "mapping x \<Longrightarrow> mapping y \<Longrightarrow> mapping (x * y)"
  by (simp add: comp_associative univalent_mult_closed)

lemma bijective_one_closed:
  "bijective 1"
  by simp

lemma bijective_mult_closed:
  "bijective x \<Longrightarrow> bijective y \<Longrightarrow> bijective (x * y)"
  by (metis injective_mult_closed comp_associative)

lemma bijective_conv_mapping:
  "bijective x \<longleftrightarrow> mapping (x\<^sup>T)"
  by (simp add: surjective_conv_total)

lemma mapping_conv_bijective:
  "mapping x \<longleftrightarrow> bijective (x\<^sup>T)"
  by (simp add: total_conv_surjective)

lemma reflexive_inf_closed:
  "reflexive x \<Longrightarrow> reflexive y \<Longrightarrow> reflexive (x \<sqinter> y)"
  by simp

lemma reflexive_conv_closed:
  "reflexive x \<Longrightarrow> reflexive (x\<^sup>T)"
  using conv_isotone by force

lemma coreflexive_inf_closed:
  "coreflexive x \<Longrightarrow> coreflexive (x \<sqinter> y)"
  by (simp add: le_infI1)

lemma coreflexive_conv_closed:
  "coreflexive x \<Longrightarrow> coreflexive (x\<^sup>T)"
  using conv_order by force

lemma coreflexive_symmetric:
  "coreflexive x \<Longrightarrow> symmetric x"
  by (metis comp_right_one comp_right_subdist_inf conv_dist_inf conv_dist_comp conv_involutive dedekind_1 inf.absorb1 inf_absorb2)

lemma transitive_inf_closed:
  "transitive x \<Longrightarrow> transitive y \<Longrightarrow> transitive (x \<sqinter> y)"
  by (meson comp_left_subdist_inf inf.cobounded1 inf.sup_mono inf_le2 mult_right_isotone order.trans)

lemma transitive_conv_closed:
  "transitive x \<Longrightarrow> transitive (x\<^sup>T)"
  using conv_order conv_dist_comp by fastforce

lemma dense_conv_closed:
  "dense_rel x \<Longrightarrow> dense_rel (x\<^sup>T)"
  using conv_order conv_dist_comp by fastforce

lemma idempotent_conv_closed:
  "idempotent x \<Longrightarrow> idempotent (x\<^sup>T)"
  by (metis conv_dist_comp)

lemma preorder_inf_closed:
  "preorder x \<Longrightarrow> preorder y \<Longrightarrow> preorder (x \<sqinter> y)"
  using transitive_inf_closed by auto

lemma preorder_conv_closed:
  "preorder x \<Longrightarrow> preorder (x\<^sup>T)"
  by (simp add: reflexive_conv_closed transitive_conv_closed)

lemma symmetric_bot_closed:
  "symmetric bot"
  by simp

lemma symmetric_one_closed:
  "symmetric 1"
  by simp

lemma symmetric_top_closed:
  "symmetric top"
  by simp

lemma symmetric_inf_closed:
  "symmetric x \<Longrightarrow> symmetric y \<Longrightarrow> symmetric (x \<sqinter> y)"
  by (simp add: conv_dist_inf)

lemma symmetric_sup_closed:
  "symmetric x \<Longrightarrow> symmetric y \<Longrightarrow> symmetric (x \<squnion> y)"
  by (simp add: conv_dist_sup)

lemma symmetric_conv_closed:
  "symmetric x \<Longrightarrow> symmetric (x\<^sup>T)"
  by simp

lemma one_inf_conv:
  "1 \<sqinter> x = 1 \<sqinter> x\<^sup>T"
  by (metis conv_dist_inf coreflexive_symmetric inf.cobounded1 symmetric_one_closed)

lemma antisymmetric_bot_closed:
  "antisymmetric bot"
  by simp

lemma antisymmetric_one_closed:
  "antisymmetric 1"
  by simp

lemma antisymmetric_inf_closed:
  "antisymmetric x \<Longrightarrow> antisymmetric (x \<sqinter> y)"
  by (rule order_trans[where y="x \<sqinter> x\<^sup>T"]) (simp_all add: conv_isotone inf.coboundedI2 inf.sup_assoc)

lemma antisymmetric_conv_closed:
  "antisymmetric x \<Longrightarrow> antisymmetric (x\<^sup>T)"
  by (simp add: inf_commute)

lemma asymmetric_bot_closed:
  "asymmetric bot"
  by simp

lemma asymmetric_inf_closed:
  "asymmetric x \<Longrightarrow> asymmetric (x \<sqinter> y)"
  by (metis conv_dist_inf inf.mult_zero_left inf.left_commute inf_assoc)

lemma asymmetric_conv_closed:
  "asymmetric x \<Longrightarrow> asymmetric (x\<^sup>T)"
  by (simp add: inf_commute)

lemma linear_top_closed:
  "linear top"
  by simp

lemma linear_sup_closed:
  "linear x \<Longrightarrow> linear (x \<squnion> y)"
  by (metis conv_dist_sup sup_assoc sup_commute sup_top_right)

lemma linear_reflexive:
  "linear x \<Longrightarrow> reflexive x"
  by (metis one_inf_conv inf.distrib_left inf.cobounded2 inf.orderE reflexive_top_closed sup.idem)

lemma linear_conv_closed:
  "linear x \<Longrightarrow> linear (x\<^sup>T)"
  by (simp add: sup_commute)

lemma linear_comp_closed:
  assumes "linear x"
      and "linear y"
    shows "linear (x * y)"
proof -
  have "reflexive y"
    by (simp add: assms(2) linear_reflexive)
  hence "x \<squnion> x\<^sup>T \<le> x * y \<squnion> y\<^sup>T * x\<^sup>T"
    by (metis case_split_left case_split_right le_supI sup.cobounded1 sup.cobounded2 sup.idem reflexive_conv_closed)
  thus ?thesis
    by (simp add: assms(1) conv_dist_comp top_le)
qed

lemma equivalence_one_closed:
  "equivalence 1"
  by simp

lemma equivalence_top_closed:
  "equivalence top"
  by simp

lemma equivalence_inf_closed:
  "equivalence x \<Longrightarrow> equivalence y \<Longrightarrow> equivalence (x \<sqinter> y)"
  using conv_dist_inf preorder_inf_closed by auto

lemma equivalence_conv_closed:
  "equivalence x \<Longrightarrow> equivalence (x\<^sup>T)"
  by simp

lemma order_one_closed:
  "order 1"
  by simp

lemma order_inf_closed:
  "order x \<Longrightarrow> order y \<Longrightarrow> order (x \<sqinter> y)"
  using antisymmetric_inf_closed transitive_inf_closed by auto

lemma order_conv_closed:
  "order x \<Longrightarrow> order (x\<^sup>T)"
  by (simp add: inf_commute reflexive_conv_closed transitive_conv_closed)

lemma linear_order_conv_closed:
  "linear_order x \<Longrightarrow> linear_order (x\<^sup>T)"
  using equivalence_top_closed conv_dist_sup inf_commute reflexive_conv_closed transitive_conv_closed by force

text \<open>
We show a fact about equivalences.
\<close>

lemma equivalence_comp_dist_inf:
  "equivalence x \<Longrightarrow> x * y \<sqinter> x * z = x * (y \<sqinter> x * z)"
  by (metis antisym comp_right_subdist_inf dedekind_1 eq_iff inf.absorb1 inf.absorb2 mult_1_right mult_assoc)

text \<open>
The following result generalises the fact that composition with a test amounts to intersection with the corresponding vector.
Both tests and vectors can be used to represent sets as relations.
\<close>

lemma coreflexive_comp_top_inf:
  "coreflexive x \<Longrightarrow> x * top \<sqinter> y = x * y"
  apply (rule antisym)
  apply (metis comp_left_isotone comp_left_one coreflexive_symmetric dedekind_1 inf_top_left order_trans)
  using comp_left_isotone comp_right_isotone by fastforce

lemma coreflexive_comp_top_inf_one:
  "coreflexive x \<Longrightarrow> x * top \<sqinter> 1 = x"
  by (simp add: coreflexive_comp_top_inf)

lemma coreflexive_comp_inf:
  "coreflexive x \<Longrightarrow> coreflexive y \<Longrightarrow> x * y = x \<sqinter> y"
  by (metis (full_types) coreflexive_comp_top_inf coreflexive_comp_top_inf_one inf.mult_assoc inf.absorb2)

lemma coreflexive_comp_inf_comp:
  assumes "coreflexive x"
      and "coreflexive y"
    shows "(x * z) \<sqinter> (y * z) = (x \<sqinter> y) * z"
proof -
  have "(x * z) \<sqinter> (y * z) = x * top \<sqinter> z \<sqinter> y * top \<sqinter> z"
    using assms coreflexive_comp_top_inf inf_assoc by auto
  also have "... = x * top \<sqinter> y * top \<sqinter> z"
    by (simp add: inf.commute inf.left_commute)
  also have "... = (x \<sqinter> y) * top \<sqinter> z"
    by (metis assms coreflexive_comp_inf coreflexive_comp_top_inf mult_assoc)
  also have "... = (x \<sqinter> y) * z"
    by (simp add: assms(1) coreflexive_comp_top_inf coreflexive_inf_closed)
  finally show ?thesis
    .
qed

lemma coreflexive_idempotent:
  "coreflexive x \<Longrightarrow> idempotent x"
  by (simp add: coreflexive_comp_inf)

lemma coreflexive_univalent:
  "coreflexive x \<Longrightarrow> univalent x"
  by (simp add: coreflexive_idempotent coreflexive_symmetric)

lemma coreflexive_injective:
  "coreflexive x \<Longrightarrow> injective x"
  by (simp add: coreflexive_idempotent coreflexive_symmetric)

lemma coreflexive_commutative:
  "coreflexive x \<Longrightarrow> coreflexive y \<Longrightarrow> x * y = y * x"
  by (simp add: coreflexive_comp_inf inf.commute)

lemma coreflexive_dedekind:
  "coreflexive x \<Longrightarrow> coreflexive y \<Longrightarrow> coreflexive z \<Longrightarrow> x * y \<sqinter> z \<le> x * (y \<sqinter> x * z)"
  by (simp add: coreflexive_comp_inf inf.coboundedI1 inf.left_commute)

text \<open>
Also the equational version of the Dedekind rule continues to hold.
\<close>

lemma dedekind_eq:
  "x * y \<sqinter> z = (x \<sqinter> (z * y\<^sup>T)) * (y \<sqinter> (x\<^sup>T * z)) \<sqinter> z"
proof (rule antisym)
  have "x * y \<sqinter> z \<le> x * (y \<sqinter> (x\<^sup>T * z)) \<sqinter> z"
    by (simp add: dedekind_1)
  also have "... \<le> (x \<sqinter> (z * (y \<sqinter> (x\<^sup>T * z))\<^sup>T)) * (y \<sqinter> (x\<^sup>T * z)) \<sqinter> z"
    by (simp add: dedekind_2)
  also have "... \<le> (x \<sqinter> (z * y\<^sup>T)) * (y \<sqinter> (x\<^sup>T * z)) \<sqinter> z"
    by (metis comp_left_isotone comp_right_isotone inf_mono conv_order inf.cobounded1 order_refl)
  finally show "x * y \<sqinter> z \<le> (x \<sqinter> (z * y\<^sup>T)) * (y \<sqinter> (x\<^sup>T * z)) \<sqinter> z"
    .
next
  show "(x \<sqinter> (z * y\<^sup>T)) * (y \<sqinter> (x\<^sup>T * z)) \<sqinter> z \<le> x * y \<sqinter> z"
    using comp_isotone inf.sup_left_isotone by auto
qed

lemma dedekind:
  "x * y \<sqinter> z \<le> (x \<sqinter> (z * y\<^sup>T)) * (y \<sqinter> (x\<^sup>T * z))"
  by (metis dedekind_eq inf.cobounded1)

lemma vector_export_comp:
  "(x * top \<sqinter> y) * z = x * top \<sqinter> y * z"
proof -
  have "vector (x * top)"
    by (simp add: comp_associative)
  thus ?thesis
    by (simp add: vector_inf_comp)
qed

lemma vector_export_comp_unit:
  "(x * top \<sqinter> 1) * y = x * top \<sqinter> y"
  by (simp add: vector_export_comp)

text \<open>
We solve a few exercises from \cite{SchmidtStroehlein1993}.
\<close>

lemma ex231a [simp]:
  "(1 \<sqinter> x * x\<^sup>T) * x = x"
  by (metis inf.cobounded1 inf.idem inf_right_idem comp_left_one conv_one coreflexive_comp_top_inf dedekind_eq)

lemma ex231b [simp]:
  "x * (1 \<sqinter> x\<^sup>T * x) = x"
  by (metis conv_dist_comp conv_dist_inf conv_involutive conv_one ex231a)

lemma ex231c:
  "x \<le> x * x\<^sup>T * x"
  by (metis comp_left_isotone ex231a inf_le2)

lemma ex231d:
  "x \<le> x * top * x"
  by (metis comp_left_isotone comp_right_isotone top_greatest order_trans ex231c)

lemma ex231e [simp]:
  "x * top * x * top = x * top"
  by (metis ex231d antisym comp_associative mult_right_isotone top.extremum)

lemma arc_injective:
  "arc x \<Longrightarrow> injective x"
  by (metis conv_dist_inf conv_involutive inf.absorb2 top_right_mult_increasing univalent_inf_closed)

lemma arc_conv_closed:
  "arc x \<Longrightarrow> arc (x\<^sup>T)"
  by simp

lemma arc_univalent:
  "arc x \<Longrightarrow> univalent x"
  using arc_conv_closed arc_injective univalent_conv_injective by blast

text \<open>
The following result generalises \cite[Exercise 2]{Oliveira2009}.
It is used to show that the while-loop preserves injectivity of the constructed tree.
\<close>

lemma injective_sup:
  assumes "injective t"
      and "e * t\<^sup>T \<le> 1"
      and "injective e"
    shows "injective (t \<squnion> e)"
proof -
  have "(t \<squnion> e) * (t \<squnion> e)\<^sup>T = t * t\<^sup>T \<squnion> t * e\<^sup>T \<squnion> e * t\<^sup>T \<squnion> e * e\<^sup>T"
    by (simp add: comp_left_dist_sup conv_dist_sup semiring.distrib_right sup.assoc)
  thus ?thesis
    using assms coreflexive_symmetric conv_dist_comp by fastforce
qed

lemma injective_inv:
  "injective t \<Longrightarrow> e * t\<^sup>T = bot \<Longrightarrow> arc e \<Longrightarrow> injective (t \<squnion> e)"
  using arc_injective injective_sup bot_least by blast

lemma univalent_sup:
  "univalent t \<Longrightarrow> e\<^sup>T * t \<le> 1 \<Longrightarrow> univalent e \<Longrightarrow> univalent (t \<squnion> e)"
  by (metis injective_sup conv_dist_sup conv_involutive)

lemma point_injective:
  "arc x \<Longrightarrow> x\<^sup>T * top * x \<le> 1"
  by (metis conv_top comp_associative conv_dist_comp conv_involutive vector_top_closed)

lemma vv_transitive:
  "vector v \<Longrightarrow> (v * v\<^sup>T) * (v * v\<^sup>T) \<le> v * v\<^sup>T"
  by (metis comp_associative comp_left_isotone comp_right_isotone top_greatest)

lemma epm_3:
  assumes "e \<le> w"
      and "injective w"
    shows "e = w \<sqinter> top * e"
proof -
  have "w \<sqinter> top * e \<le> w * e\<^sup>T * e"
    by (metis (no_types, lifting) inf.absorb2 top.extremum dedekind_2 inf.commute)
  also have "... \<le> w * w\<^sup>T * e"
    by (simp add: assms(1) conv_isotone mult_left_isotone mult_right_isotone)
  also have "... \<le> e"
    using assms(2) coreflexive_comp_top_inf inf.sup_right_divisibility by blast
  finally show ?thesis
    by (simp add: assms(1) top_left_mult_increasing antisym)
qed

lemma comp_inf_vector:
  "x * (y \<sqinter> z * top) = (x \<sqinter> top * z\<^sup>T) * y"
  by (metis conv_top covector_inf_comp_3 comp_associative conv_dist_comp inf.commute vector_top_closed)

lemma inf_vector_comp:
  "(x \<sqinter> y * top) * z = y * top \<sqinter> x * z"
  using inf.commute vector_export_comp by auto

lemma comp_inf_covector:
  "x * (y \<sqinter> top * z) = x * y \<sqinter> top * z"
  by (simp add: covector_comp_inf covector_mult_closed)

text \<open>
Well-known distributivity properties of univalent and injective relations over meet continue to hold.
\<close>

lemma univalent_comp_left_dist_inf:
  assumes "univalent x"
    shows "x * (y \<sqinter> z) = x * y \<sqinter> x * z"
proof (rule antisym)
  show "x * (y \<sqinter> z) \<le> x * y \<sqinter> x * z"
    by (simp add: comp_right_isotone)
next
  have "x * y \<sqinter> x * z \<le> (x \<sqinter> x * z * y\<^sup>T) * (y \<sqinter> x\<^sup>T * x * z)"
    by (metis comp_associative dedekind)
  also have "... \<le> x * (y \<sqinter> x\<^sup>T * x * z)"
    by (simp add: comp_left_isotone)
  also have "... \<le> x * (y \<sqinter> 1 * z)"
    using assms comp_left_isotone comp_right_isotone inf.sup_right_isotone by blast
  finally show "x * y \<sqinter> x * z \<le> x * (y \<sqinter> z)"
    by simp
qed

lemma injective_comp_right_dist_inf:
  "injective z \<Longrightarrow> (x \<sqinter> y) * z = x * z \<sqinter> y * z"
  by (metis univalent_comp_left_dist_inf conv_dist_comp conv_involutive conv_dist_inf)

lemma vector_covector:
  "vector v \<Longrightarrow> vector w \<Longrightarrow> v \<sqinter> w\<^sup>T = v * w\<^sup>T"
  by (metis covector_comp_inf inf_top_left vector_conv_covector)

lemma comp_inf_vector_1:
  "(x \<sqinter> top * y) * z = x * (z \<sqinter> (top * y)\<^sup>T)"
  by (simp add: comp_inf_vector conv_dist_comp)

text \<open>
The shunting properties for bijective relations and mappings continue to hold.
\<close>

lemma shunt_bijective:
  assumes "bijective z"
    shows "x \<le> y * z \<longleftrightarrow> x * z\<^sup>T \<le> y"
proof
  assume "x \<le> y * z"
  hence "x * z\<^sup>T \<le> y * z * z\<^sup>T"
    by (simp add: mult_left_isotone)
  also have "... \<le> y"
    using assms comp_associative mult_right_isotone by fastforce
  finally show "x * z\<^sup>T \<le> y"
    .
next
  assume 1: "x * z\<^sup>T \<le> y"
  have "x = x \<sqinter> top * z"
    by (simp add: assms)
  also have "... \<le> x * z\<^sup>T * z"
    by (metis dedekind_2 inf_commute inf_top.right_neutral)
  also have "... \<le> y * z"
    using 1 by (simp add: mult_left_isotone)
  finally show "x \<le> y * z"
    .
qed

lemma shunt_mapping:
  "mapping z \<Longrightarrow> x \<le> z * y \<longleftrightarrow> z\<^sup>T * x \<le> y"
  by (metis shunt_bijective mapping_conv_bijective conv_order conv_dist_comp conv_involutive)

lemma bijective_reverse:
  assumes "bijective p"
      and "bijective q"
    shows "p \<le> r * q \<longleftrightarrow> q \<le> r\<^sup>T * p"
proof -
  have "p \<le> r * q \<longleftrightarrow> p * q\<^sup>T \<le> r"
    by (simp add: assms(2) shunt_bijective)
  also have "... \<longleftrightarrow> q\<^sup>T \<le> p\<^sup>T * r"
    by (metis assms(1) conv_dist_comp conv_involutive conv_order shunt_bijective)
  also have "... \<longleftrightarrow> q \<le> r\<^sup>T * p"
    using conv_dist_comp conv_isotone by fastforce
  finally show ?thesis
    by simp
qed

lemma arc_expanded:
  "arc x \<longleftrightarrow> x * top * x\<^sup>T \<le> 1 \<and> x\<^sup>T * top * x \<le> 1 \<and> top * x * top = top"
  by (metis conv_top comp_associative conv_dist_comp conv_involutive vector_top_closed)

lemma arc_top_arc:
  assumes "arc x"
    shows "x * top * x = x"
  by (metis assms epm_3 top_right_mult_increasing vector_inf_comp vector_mult_closed vector_top_closed)

lemma arc_top_edge:
  assumes "arc x"
    shows "x\<^sup>T * top * x = x\<^sup>T * x"
proof -
  have "x\<^sup>T = x\<^sup>T * top \<sqinter> top * x\<^sup>T"
    using assms epm_3 top_right_mult_increasing by simp
  thus ?thesis
    by (metis comp_inf_vector_1 conv_dist_comp conv_involutive conv_top inf.absorb1 top_right_mult_increasing)
qed

end

subsection \<open>Single-Object Pseudocomplemented Distributive Allegories\<close>

text \<open>
We extend single-object bounded distributive allegories by a pseudocomplement operation.
The following definitions concern properties of relations that require a pseudocomplement.
\<close>

class relation_algebra_signature = bounded_distrib_allegory_signature + uminus
begin

abbreviation irreflexive         :: "'a \<Rightarrow> bool" where "irreflexive x         \<equiv> x \<le> -1"
abbreviation strict_linear       :: "'a \<Rightarrow> bool" where "strict_linear x       \<equiv> x \<squnion> x\<^sup>T = -1"

abbreviation strict_order        :: "'a \<Rightarrow> bool" where "strict_order x        \<equiv> irreflexive x \<and> transitive x"
abbreviation linear_strict_order :: "'a \<Rightarrow> bool" where "linear_strict_order x \<equiv> strict_order x \<and> strict_linear x"

text \<open>
The following variants are useful for the graph model.
\<close>

abbreviation pp_mapping          :: "'a \<Rightarrow> bool" where "pp_mapping x          \<equiv> univalent x \<and> total (--x)"
abbreviation pp_bijective        :: "'a \<Rightarrow> bool" where "pp_bijective x        \<equiv> injective x \<and> surjective (--x)"

abbreviation pp_point            :: "'a \<Rightarrow> bool" where "pp_point x            \<equiv> vector x \<and> pp_bijective x"
abbreviation pp_arc              :: "'a \<Rightarrow> bool" where "pp_arc x              \<equiv> pp_bijective (x * top) \<and> pp_bijective (x\<^sup>T * top)"

end

class pd_allegory = bounded_distrib_allegory + p_algebra
begin

subclass relation_algebra_signature .

subclass pd_algebra ..

lemma conv_complement_1:
  "-(x\<^sup>T) \<squnion> (-x)\<^sup>T = (-x)\<^sup>T"
  by (metis conv_dist_inf conv_order bot_least conv_involutive pseudo_complement sup.absorb2 sup.cobounded2)

lemma conv_complement:
  "(-x)\<^sup>T = -(x\<^sup>T)"
  by (metis conv_complement_1 conv_dist_sup conv_involutive sup_commute)

lemma conv_complement_sub_inf [simp]:
  "x\<^sup>T * -(x * y) \<sqinter> y = bot"
  by (metis comp_left_zero conv_dist_comp conv_involutive dedekind_1 inf_import_p inf_p inf_right_idem ppp pseudo_complement regular_closed_bot)

lemma conv_complement_sub_leq:
  "x\<^sup>T * -(x * y) \<le> -y"
  using pseudo_complement conv_complement_sub_inf by blast

lemma conv_complement_sub [simp]:
  "x\<^sup>T * -(x * y) \<squnion> -y = -y"
  by (simp add: conv_complement_sub_leq sup.absorb2)

lemma complement_conv_sub:
  "-(y * x) * x\<^sup>T \<le> -y"
  by (metis conv_complement conv_complement_sub_leq conv_order conv_dist_comp)

text \<open>
The following so-called Schr\"oder equivalences, or De Morgan's Theorem K, hold only with a pseudocomplemented element on both right-hand sides.
\<close>

lemma schroeder_3_p:
  "x * y \<le> -z \<longleftrightarrow> x\<^sup>T * z \<le> -y"
  using pseudo_complement schroeder_1 by auto

lemma schroeder_4_p:
  "x * y \<le> -z \<longleftrightarrow> z * y\<^sup>T \<le> -x"
  using pseudo_complement schroeder_2 by auto

lemma comp_pp_semi_commute:
  "x * --y \<le> --(x * y)"
  using conv_complement_sub_leq schroeder_3_p by fastforce

text \<open>
The following result looks similar to a property of (anti)domain.
\<close>

lemma p_comp_pp [simp]:
  "-(x * --y) = -(x * y)"
  using comp_pp_semi_commute comp_right_isotone inf.eq_iff p_antitone pp_increasing by fastforce

lemma pp_comp_semi_commute:
  "--x * y \<le> --(x * y)"
  using complement_conv_sub schroeder_4_p by fastforce

lemma p_pp_comp [simp]:
  "-(--x * y) = -(x * y)"
  using pp_comp_semi_commute comp_left_isotone inf.eq_iff p_antitone pp_increasing by fastforce

lemma pp_comp_subdist:
  "--x * --y \<le> --(x * y)"
  by (simp add: p_antitone_iff)

lemma theorem24xxiii:
  "x * y \<sqinter> -(x * z) = x * (y \<sqinter> -z) \<sqinter> -(x * z)"
proof -
  have "x * y \<sqinter> -(x * z) \<le> x * (y \<sqinter> (x\<^sup>T * -(x * z)))"
    by (simp add: dedekind_1)
  also have "... \<le> x * (y \<sqinter> -z)"
    using comp_right_isotone conv_complement_sub_leq inf.sup_right_isotone by auto
  finally show ?thesis
    using comp_right_subdist_inf antisym inf.coboundedI2 inf.commute by auto
qed

text \<open>
Even in Stone relation algebras, we do not obtain the backward implication in the following result.
\<close>

lemma vector_complement_closed:
  "vector x \<Longrightarrow> vector (-x)"
  by (metis complement_conv_sub conv_top eq_iff top_right_mult_increasing)

lemma covector_complement_closed:
  "covector x \<Longrightarrow> covector (-x)"
  by (metis conv_complement_sub_leq conv_top eq_iff top_left_mult_increasing)

lemma covector_vector_comp:
  "vector v \<Longrightarrow> -v\<^sup>T * v = bot"
  by (metis conv_bot conv_complement conv_complement_sub_inf conv_dist_comp conv_involutive inf_top.right_neutral)

lemma irreflexive_bot_closed:
  "irreflexive bot"
  by simp

lemma irreflexive_inf_closed:
  "irreflexive x \<Longrightarrow> irreflexive (x \<sqinter> y)"
  by (simp add: le_infI1)

lemma irreflexive_sup_closed:
  "irreflexive x \<Longrightarrow> irreflexive y \<Longrightarrow> irreflexive (x \<squnion> y)"
  by simp

lemma irreflexive_conv_closed:
  "irreflexive x \<Longrightarrow> irreflexive (x\<^sup>T)"
  using conv_complement conv_isotone by fastforce

lemma reflexive_complement_irreflexive:
  "reflexive x \<Longrightarrow> irreflexive (-x)"
  by (simp add: p_antitone)

lemma irreflexive_complement_reflexive:
  "irreflexive x \<longleftrightarrow> reflexive (-x)"
  by (simp add: p_antitone_iff)

lemma symmetric_complement_closed:
  "symmetric x \<Longrightarrow> symmetric (-x)"
  by (simp add: conv_complement)

lemma asymmetric_irreflexive:
  "asymmetric x \<Longrightarrow> irreflexive x"
  by (metis inf.mult_not_zero inf.left_commute inf.right_idem inf.sup_monoid.add_commute pseudo_complement one_inf_conv)

lemma linear_asymmetric:
  "linear x \<Longrightarrow> asymmetric (-x)"
  using conv_complement p_top by force

lemma strict_linear_sup_closed:
  "strict_linear x \<Longrightarrow> strict_linear y \<Longrightarrow> strict_linear (x \<squnion> y)"
  by (metis (mono_tags, hide_lams) conv_dist_sup sup.right_idem sup_assoc sup_commute)

lemma strict_linear_irreflexive:
  "strict_linear x \<Longrightarrow> irreflexive x"
  using sup_left_divisibility by blast

lemma strict_linear_conv_closed:
  "strict_linear x \<Longrightarrow> strict_linear (x\<^sup>T)"
  by (simp add: sup_commute)

lemma strict_order_var:
  "strict_order x \<longleftrightarrow> asymmetric x \<and> transitive x"
  by (metis asymmetric_irreflexive comp_right_one irreflexive_conv_closed conv_dist_comp dual_order.trans pseudo_complement schroeder_3_p)

lemma strict_order_bot_closed:
  "strict_order bot"
  by simp

lemma strict_order_inf_closed:
  "strict_order x \<Longrightarrow> strict_order y \<Longrightarrow> strict_order (x \<sqinter> y)"
  using inf.coboundedI1 transitive_inf_closed by auto

lemma strict_order_conv_closed:
  "strict_order x \<Longrightarrow> strict_order (x\<^sup>T)"
  using irreflexive_conv_closed transitive_conv_closed by blast

lemma order_strict_order:
  assumes "order x"
  shows "strict_order (x \<sqinter> -1)"
proof (rule conjI)
  show 1: "irreflexive (x \<sqinter> -1)"
    by simp
  have "antisymmetric (x \<sqinter> -1)"
    using antisymmetric_inf_closed assms by blast
  hence "(x \<sqinter> -1) * (x \<sqinter> -1) \<sqinter> 1 \<le> (x \<sqinter> -1 \<sqinter> (x \<sqinter> -1)\<^sup>T) * (x \<sqinter> -1 \<sqinter> (x \<sqinter> -1)\<^sup>T)"
    using 1 by (metis (no_types) coreflexive_symmetric irreflexive_inf_closed coreflexive_transitive dedekind_1 inf_idem mult_1_right semiring.mult_not_zero strict_order_var)
  also have "... = (x \<sqinter> x\<^sup>T \<sqinter> -1) * (x \<sqinter> x\<^sup>T \<sqinter> -1)"
    by (simp add: conv_complement conv_dist_inf inf.absorb2 inf.sup_monoid.add_assoc)
  also have "... = bot"
    using assms inf.antisym reflexive_conv_closed by fastforce
  finally have "(x \<sqinter> -1) * (x \<sqinter> -1) \<le> -1"
    using le_bot pseudo_complement by blast
  thus "transitive (x \<sqinter> -1)"
    by (meson assms comp_isotone inf.boundedI inf.cobounded1 inf.order_lesseq_imp)
qed

lemma strict_order_order:
  "strict_order x \<Longrightarrow> order (x \<squnion> 1)"
  apply (unfold strict_order_var, intro conjI)
  apply simp
  apply (simp add: mult_left_dist_sup mult_right_dist_sup sup.absorb2)
  using conv_dist_sup coreflexive_bot_closed sup.absorb2 sup_inf_distrib2 by fastforce

lemma linear_strict_order_conv_closed:
  "linear_strict_order x \<Longrightarrow> linear_strict_order (x\<^sup>T)"
  by (simp add: irreflexive_conv_closed sup_monoid.add_commute transitive_conv_closed)

lemma linear_order_strict_order:
  "linear_order x \<Longrightarrow> linear_strict_order (x \<sqinter> -1)"
  apply (rule conjI)
  using order_strict_order apply simp
  by (metis conv_complement conv_dist_inf coreflexive_symmetric eq_iff inf.absorb2 inf.distrib_left inf.sup_monoid.add_commute top.extremum)

lemma regular_conv_closed:
  "regular x \<Longrightarrow> regular (x\<^sup>T)"
  by (metis conv_complement)

text \<open>
We show a number of facts about equivalences.
\<close>

lemma equivalence_comp_left_complement:
  "equivalence x \<Longrightarrow> x * -x = -x"
  apply (rule antisym)
  apply (metis conv_complement_sub_leq preorder_idempotent)
  using mult_left_isotone by fastforce

lemma equivalence_comp_right_complement:
  "equivalence x \<Longrightarrow> -x * x = -x"
  by (metis equivalence_comp_left_complement conv_complement conv_dist_comp)

text \<open>
The pseudocomplement of tests is given by the following operation.
\<close>

abbreviation coreflexive_complement :: "'a \<Rightarrow> 'a" ("_ '" [80] 80)
  where "x ' \<equiv> -x \<sqinter> 1"

lemma coreflexive_comp_top_coreflexive_complement:
  "coreflexive x \<Longrightarrow> (x * top)' = x '"
  by (metis coreflexive_comp_top_inf_one inf.commute inf_import_p)

lemma coreflexive_comp_inf_complement:
  "coreflexive x \<Longrightarrow> (x * y) \<sqinter> -z = (x * y) \<sqinter> -(x * z)"
  by (metis coreflexive_comp_top_inf inf.sup_relative_same_increasing inf_import_p inf_le1)

lemma double_coreflexive_complement:
  "x '' = (-x)'"
  using inf.sup_monoid.add_commute inf_import_p by auto

lemma coreflexive_pp_dist_comp:
  assumes "coreflexive x"
      and "coreflexive y"
    shows "(x * y)'' = x '' * y ''"
proof -
  have "(x * y)'' = --(x * y) \<sqinter> 1"
    by (simp add: double_coreflexive_complement)
  also have "... = --x \<sqinter> --y \<sqinter> 1"
    by (simp add: assms coreflexive_comp_inf)
  also have "... = (--x \<sqinter> 1) * (--y \<sqinter> 1)"
    by (simp add: coreflexive_comp_inf inf.left_commute inf.sup_monoid.add_assoc)
  also have "... = x '' * y ''"
    by (simp add: double_coreflexive_complement)
  finally show ?thesis
    .
qed

lemma coreflexive_pseudo_complement:
  "coreflexive x \<Longrightarrow> x \<sqinter> y = bot \<longleftrightarrow> x \<le> y '"
  by (simp add: pseudo_complement)

lemma pp_bijective_conv_mapping:
  "pp_bijective x \<longleftrightarrow> pp_mapping (x\<^sup>T)"
  by (simp add: conv_complement surjective_conv_total)

lemma pp_arc_expanded:
  "pp_arc x \<longleftrightarrow> x * top * x\<^sup>T \<le> 1 \<and> x\<^sup>T * top * x \<le> 1 \<and> top * --x * top = top"
proof
  assume 1: "pp_arc x"
  have 2: "x * top * x\<^sup>T \<le> 1"
    using 1 by (metis comp_associative conv_dist_comp equivalence_top_closed vector_top_closed)
  have 3: "x\<^sup>T * top * x \<le> 1"
    using 1 by (metis conv_dist_comp conv_involutive equivalence_top_closed vector_top_closed mult_assoc)
  have 4: "x\<^sup>T \<le> x\<^sup>T * x * x\<^sup>T"
    by (metis conv_involutive ex231c)
  have "top = --(top * x) * top"
    using 1 by (metis conv_complement conv_dist_comp conv_involutive equivalence_top_closed)
  also have "... \<le> --(top * x\<^sup>T * top * x) * top"
    using 1 by (metis eq_refl mult_assoc p_comp_pp p_pp_comp)
  also have "... = (top * --(x * top) \<sqinter> --(top * x\<^sup>T * top * x)) * top"
    using 1 by simp
  also have "... = top * (--(x * top) \<sqinter> --(top * x\<^sup>T * top * x)) * top"
    by (simp add: covector_complement_closed covector_comp_inf covector_mult_closed)
  also have "... = top * --(x * top \<sqinter> top * x\<^sup>T * top * x) * top"
    by simp
  also have "... = top * --(x * top * x\<^sup>T * top * x) * top"
    by (metis comp_associative comp_inf_covector inf_top.left_neutral)
  also have "... \<le> top * --(x * top * x\<^sup>T * x * x\<^sup>T * top * x) * top"
    using 4 by (metis comp_associative comp_left_isotone comp_right_isotone pp_isotone)
  also have "... \<le> top * --(x * x\<^sup>T * top * x) * top"
    using 2 by (metis comp_associative comp_left_isotone comp_right_isotone pp_isotone comp_left_one)
  also have "... \<le> top * --x * top"
    using 3 by (metis comp_associative comp_left_isotone comp_right_isotone pp_isotone comp_right_one)
  finally show "x * top * x\<^sup>T \<le> 1 \<and> x\<^sup>T * top * x \<le> 1 \<and> top * --x * top = top"
    using 2 3 top_le by blast
next
  assume "x * top * x\<^sup>T \<le> 1 \<and> x\<^sup>T * top * x \<le> 1 \<and> top * --x * top = top"
  thus "pp_arc x"
    apply (intro conjI)
    apply (metis comp_associative conv_dist_comp equivalence_top_closed vector_top_closed)
    apply (metis comp_associative mult_right_isotone top_le pp_comp_semi_commute)
    apply (metis conv_dist_comp coreflexive_symmetric vector_conv_covector vector_top_closed mult_assoc)
    by (metis conv_complement conv_dist_comp equivalence_top_closed inf.orderE inf_top.left_neutral mult_right_isotone pp_comp_semi_commute)
qed

text \<open>
The following operation represents states with infinite executions of non-strict computations.
\<close>

abbreviation N :: "'a \<Rightarrow> 'a"
  where "N x \<equiv> -(-x * top) \<sqinter> 1"

lemma N_comp:
  "N x * y = -(-x * top) \<sqinter> y"
  by (simp add: vector_mult_closed vector_complement_closed vector_inf_one_comp)

lemma N_comp_top [simp]:
  "N x * top = -(-x * top)"
  by (simp add: N_comp)

lemma vector_N_pp:
  "vector x \<Longrightarrow> N x = --x \<sqinter> 1"
  by (simp add: vector_complement_closed)

lemma N_vector_pp [simp]:
  "N (x * top) = --(x * top) \<sqinter> 1"
  by (simp add: comp_associative vector_complement_closed)

lemma N_vector_top_pp [simp]:
  "N (x * top) * top = --(x * top)"
  by (metis N_comp_top comp_associative vector_top_closed vector_complement_closed)

lemma N_below_inf_one_pp:
  "N x \<le> --x \<sqinter> 1"
  using inf.sup_left_isotone p_antitone top_right_mult_increasing by auto

lemma N_below_pp:
  "N x \<le> --x"
  using N_below_inf_one_pp by auto

lemma N_comp_N:
  "N x * N y = -(-x * top) \<sqinter> -(-y * top) \<sqinter> 1"
  by (simp add: N_comp inf.mult_assoc)

lemma N_bot [simp]:
  "N bot = bot"
  by simp

lemma N_top [simp]:
  "N top = 1"
  by simp

lemma n_split_omega_mult_pp:
  "xs * --xo = xo \<Longrightarrow> vector xo \<Longrightarrow> N top * xo = xs * N xo * top"
  by (metis N_top N_vector_top_pp comp_associative comp_left_one)

text \<open>
Many of the following results have been derived for verifying Prim's minimum spanning tree algorithm.
\<close>

lemma ee:
  assumes "vector v"
      and "e \<le> v * -v\<^sup>T"
    shows "e * e = bot"
proof -
  have "e * v \<le> bot"
    by (metis assms covector_vector_comp comp_associative mult_left_isotone mult_right_zero)
  thus ?thesis
    by (metis assms(2) bot_unique comp_associative mult_right_isotone semiring.mult_not_zero)
qed

lemma et:
  assumes "vector v"
      and "e \<le> v * -v\<^sup>T"
      and "t \<le> v * v\<^sup>T"
    shows "e * t = bot"
      and "e * t\<^sup>T = bot"
proof -
  have "e * t \<le> v * -v\<^sup>T * v * v\<^sup>T"
    using assms(2-3) comp_isotone mult_assoc by fastforce
  thus "e * t = bot"
    by (simp add: assms(1) covector_vector_comp le_bot mult_assoc)
next
  have "t\<^sup>T \<le> v * v\<^sup>T"
    using assms(3) conv_order conv_dist_comp by fastforce
  hence "e * t\<^sup>T \<le> v * -v\<^sup>T * v * v\<^sup>T"
    by (metis assms(2) comp_associative comp_isotone)
  thus "e * t\<^sup>T = bot"
    by (simp add: assms(1) covector_vector_comp le_bot mult_assoc)
qed

lemma ve_dist:
  assumes "e \<le> v * -v\<^sup>T"
      and "vector v"
      and "arc e"
    shows "(v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T = v * v\<^sup>T \<squnion> v * v\<^sup>T * e \<squnion> e\<^sup>T * v * v\<^sup>T \<squnion> e\<^sup>T * e"
proof -
  have "e \<le> v * top"
    using assms(1) comp_right_isotone dual_order.trans top_greatest by blast
  hence "v * top * e = v * top * (v * top \<sqinter> e)"
    by (simp add: inf.absorb2)
  also have "... = (v * top \<sqinter> top * v\<^sup>T) * e"
    using assms(2) covector_inf_comp_3 vector_conv_covector by force
  also have "... = v * top * v\<^sup>T * e"
    by (metis assms(2) inf_top_right vector_inf_comp)
  also have "... = v * v\<^sup>T * e"
    by (simp add: assms(2))
  finally have 1: "v * top * e = v * v\<^sup>T * e"
    .
  have "e\<^sup>T * top * e \<le> e\<^sup>T * top * e * e\<^sup>T * e"
    using ex231c comp_associative mult_right_isotone by auto
  also have "... \<le> e\<^sup>T * e"
    by (metis assms(3) coreflexive_comp_top_inf le_infE mult_semi_associative point_injective)
  finally have 2: "e\<^sup>T * top * e = e\<^sup>T * e"
    by (simp add: inf.antisym mult_left_isotone top_right_mult_increasing)
  have "(v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T = (v \<squnion> e\<^sup>T * top) * (v\<^sup>T \<squnion> top * e)"
    by (simp add: conv_dist_comp conv_dist_sup)
  also have "... = v * v\<^sup>T \<squnion> v * top * e \<squnion> e\<^sup>T * top * v\<^sup>T \<squnion> e\<^sup>T * top * top * e"
    by (metis semiring.distrib_left semiring.distrib_right sup_assoc mult_assoc)
  also have "... = v * v\<^sup>T \<squnion> v * top * e \<squnion> (v * top * e)\<^sup>T \<squnion> e\<^sup>T * top * e"
    by (simp add: comp_associative conv_dist_comp)
  also have "... = v * v\<^sup>T \<squnion> v * v\<^sup>T * e \<squnion> (v * v\<^sup>T * e)\<^sup>T \<squnion> e\<^sup>T * e"
    using 1 2 by simp
  finally show ?thesis
    by (simp add: comp_associative conv_dist_comp)
qed

lemma ev:
  "vector v \<Longrightarrow> e \<le> v * -v\<^sup>T \<Longrightarrow> e * v = bot"
  by (metis covector_vector_comp antisym bot_least comp_associative mult_left_isotone mult_right_zero)

lemma vTeT:
  "vector v \<Longrightarrow> e \<le> v * -v\<^sup>T \<Longrightarrow> v\<^sup>T * e\<^sup>T = bot"
  using conv_bot ev conv_dist_comp by fastforce

text \<open>
The following result is used to show that the while-loop of Prim's algorithm preserves that the constructed tree is a subgraph of g.
\<close>

lemma prim_subgraph_inv:
  assumes "e \<le> v * -v\<^sup>T \<sqinter> g"
      and "t \<le> v * v\<^sup>T \<sqinter> g"
    shows "t \<squnion> e \<le> ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T) \<sqinter> g"
proof (rule sup_least)
  have "t \<le> ((v \<squnion> e\<^sup>T * top) * v\<^sup>T) \<sqinter> g"
    using assms(2) le_supI1 mult_right_dist_sup by auto
  also have "... \<le> ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T) \<sqinter> g"
    using comp_right_isotone conv_dist_sup inf.sup_left_isotone by auto
  finally show "t \<le> ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T) \<sqinter> g"
    .
next
  have "e \<le> v * top"
    by (meson assms(1) inf.boundedE mult_right_isotone order.trans top.extremum)
  hence "e \<le> v * top \<sqinter> top * e"
    by (simp add: top_left_mult_increasing)
  also have "... = v * top * e"
    by (metis inf_top_right vector_export_comp)
  finally have "e \<le> v * top * e \<sqinter> g"
    using assms(1) by auto
  also have "... = v * (e\<^sup>T * top)\<^sup>T \<sqinter> g"
    by (simp add: comp_associative conv_dist_comp)
  also have "... \<le> v * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g"
    by (simp add: conv_dist_sup mult_left_dist_sup sup.assoc sup.orderI)
  also have "... \<le> (v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T \<sqinter> g"
    using inf.sup_left_isotone mult_right_sub_dist_sup_left by auto
  finally show "e \<le> ((v \<squnion> e\<^sup>T * top) * (v \<squnion> e\<^sup>T * top)\<^sup>T) \<sqinter> g"
    .
qed

text \<open>
The following result shows how to apply the Schr\"oder equivalence to the middle factor in a composition of three relations.
Again the elements on the right-hand side need to be pseudocomplemented.
\<close>

lemma triple_schroeder_p:
  "x * y * z \<le> -w \<longleftrightarrow> x\<^sup>T * w * z\<^sup>T \<le> -y"
  using mult_assoc p_antitone_iff schroeder_3_p schroeder_4_p by auto

text \<open>
The rotation versions of the Schr\"oder equivalences continue to hold, again with pseudocomplemented elements on the right-hand side.
\<close>

lemma schroeder_5_p:
  "x * y \<le> -z \<longleftrightarrow> y * z\<^sup>T \<le> -x\<^sup>T"
  using schroeder_3_p schroeder_4_p by auto

lemma schroeder_6_p:
  "x * y \<le> -z \<longleftrightarrow> z\<^sup>T * x \<le> -y\<^sup>T"
  using schroeder_3_p schroeder_4_p by auto

lemma vector_conv_compl:
  "vector v \<Longrightarrow> top * -v\<^sup>T = -v\<^sup>T"
  by (simp add: covector_complement_closed vector_conv_covector)

text \<open>
Composition commutes, relative to the diversity relation.
\<close>

lemma comp_commute_below_diversity:
  "x * y \<le> -1 \<longleftrightarrow> y * x \<le> -1"
  by (metis comp_right_one conv_dist_comp conv_one schroeder_3_p schroeder_4_p)

lemma comp_injective_below_complement:
  "injective y \<Longrightarrow> -x * y \<le> -(x * y)"
  by (metis p_antitone_iff comp_associative comp_right_isotone comp_right_one schroeder_4_p)

lemma comp_univalent_below_complement:
  "univalent x \<Longrightarrow> x * -y \<le> -(x * y)"
  by (metis p_inf pseudo_complement semiring.mult_zero_right univalent_comp_left_dist_inf)

text \<open>
Bijective relations and mappings can be exported from a pseudocomplement.
\<close>

lemma comp_bijective_complement:
  "bijective y \<Longrightarrow> -x * y = -(x * y)"
  using comp_injective_below_complement complement_conv_sub antisym shunt_bijective by blast

lemma comp_mapping_complement:
  "mapping x \<Longrightarrow> x * -y = -(x * y)"
  by (metis (full_types) comp_bijective_complement conv_complement conv_dist_comp conv_involutive total_conv_surjective)

text \<open>
The following facts are used in the correctness proof of Kruskal's minimum spanning tree algorithm.
\<close>

lemma kruskal_injective_inv:
  assumes "injective f"
      and "covector q"
      and "q * f\<^sup>T \<le> q"
      and "e \<le> q"
      and "q * f\<^sup>T \<le> -e"
      and "injective e"
      and "q\<^sup>T * q \<sqinter> f\<^sup>T * f \<le> 1"
    shows "injective ((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T \<squnion> e)"
proof -
  have 1: "(f \<sqinter> -q) * (f \<sqinter> -q)\<^sup>T \<le> 1"
    by (simp add: assms(1) injective_inf_closed)
  have 2: "(f \<sqinter> -q) * (f \<sqinter> q) \<le> 1"
  proof -
    have 21: "bot = q * f\<^sup>T \<sqinter> - q"
      by (metis assms(3) inf.sup_monoid.add_assoc inf.sup_right_divisibility inf_import_p inf_p)
    have "(f \<sqinter> -q) * (f \<sqinter> q) \<le> -q * f \<sqinter> q"
      by (metis assms(2) comp_inf_covector comp_isotone inf.cobounded2 inf.left_idem)
    also have "... = bot"
      using 21 schroeder_2 by auto
    finally show ?thesis
      by (simp add: bot_unique)
  qed
  have 3: "(f \<sqinter> -q) * e\<^sup>T \<le> 1"
  proof -
    have "(f \<sqinter> -q) * e\<^sup>T \<le> -q * e\<^sup>T"
      by (simp add: mult_left_isotone)
    also have "... = bot"
      by (metis assms(2,4) bot_unique conv_bot conv_complement covector_complement_closed p_antitone p_bot regular_closed_bot schroeder_5_p)
    finally show ?thesis
      by (simp add: bot_unique)
  qed
  have 4: "(f \<sqinter> q)\<^sup>T * (f \<sqinter> -q)\<^sup>T \<le> 1"
    using 2 conv_dist_comp conv_isotone by force
  have 5: "(f \<sqinter> q)\<^sup>T * (f \<sqinter> q) \<le> 1"
  proof -
    have "(f \<sqinter> q)\<^sup>T * (f \<sqinter> q) \<le> q\<^sup>T * q \<sqinter> f\<^sup>T * f"
      by (simp add: conv_isotone mult_isotone)
    also have "... \<le> 1"
      by (simp add: assms(7))
    finally show ?thesis
      by simp
  qed
  have 6: "(f \<sqinter> q)\<^sup>T * e\<^sup>T \<le> 1"
  proof -
    have "f\<^sup>T * e\<^sup>T \<le> -q\<^sup>T"
      using assms(5) schroeder_5_p by simp
    hence "(f \<sqinter> q)\<^sup>T * e\<^sup>T = bot"
      by (metis assms(2,5) conv_bot conv_dist_comp covector_comp_inf inf.absorb1 inf.cobounded2 inf.sup_monoid.add_commute inf_left_commute inf_p schroeder_4_p)
    thus ?thesis
      by (simp add: bot_unique)
  qed
  have 7: "e * (f \<sqinter> -q)\<^sup>T \<le> 1"
    using 3 conv_dist_comp coreflexive_symmetric by fastforce
  have 8: "e * (f \<sqinter> q) \<le> 1"
    using 6 conv_dist_comp coreflexive_symmetric by fastforce
  have 9: "e * e\<^sup>T \<le> 1"
    by (simp add: assms(6))
  have "((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T \<squnion> e) * ((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T \<squnion> e)\<^sup>T = (f \<sqinter> -q) * (f \<sqinter> -q)\<^sup>T \<squnion> (f \<sqinter> -q) * (f \<sqinter> q) \<squnion> (f \<sqinter> -q) * e\<^sup>T \<squnion> (f \<sqinter> q)\<^sup>T * (f \<sqinter> -q)\<^sup>T \<squnion> (f \<sqinter> q)\<^sup>T * (f \<sqinter> q) \<squnion> (f \<sqinter> q)\<^sup>T * e\<^sup>T \<squnion> e * (f \<sqinter> -q)\<^sup>T \<squnion> e * (f \<sqinter> q) \<squnion> e * e\<^sup>T"
    using comp_left_dist_sup comp_right_dist_sup conv_dist_sup sup.assoc by simp
  also have "... \<le> 1"
    using 1 2 3 4 5 6 7 8 9 by simp
  finally show ?thesis
    by simp
qed

lemma kruskal_exchange_injective_inv_1:
  assumes "injective f"
      and "covector q"
      and "q * f\<^sup>T \<le> q"
      and "q\<^sup>T * q \<sqinter> f\<^sup>T * f \<le> 1"
    shows "injective ((f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T)"
  using kruskal_injective_inv[where e=bot] by (simp add: assms)

lemma kruskal_exchange_acyclic_inv_3:
  assumes "injective w"
      and "d \<le> w"
    shows "(w \<sqinter> -d) * d\<^sup>T * top = bot"
proof -
  have "(w \<sqinter> -d) * d\<^sup>T * top = (w \<sqinter> -d \<sqinter> (d\<^sup>T * top)\<^sup>T) * top"
    by (simp add: comp_associative comp_inf_vector_1 conv_dist_comp)
  also have "... = (w \<sqinter> top * d \<sqinter> -d) * top"
    by (simp add: conv_dist_comp inf_commute inf_left_commute)
  finally show ?thesis
    using assms epm_3 by simp
qed

lemma kruskal_subgraph_inv:
  assumes "f \<le> --(-h \<sqinter> g)"
      and "e \<le> --g"
      and "symmetric h"
      and "symmetric g"
    shows "(f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T \<squnion> e \<le> --(-(h \<sqinter> -e \<sqinter> -e\<^sup>T) \<sqinter> g)"
proof -
  let ?f = "(f \<sqinter> -q) \<squnion> (f \<sqinter> q)\<^sup>T \<squnion> e"
  let ?h = "h \<sqinter> -e \<sqinter> -e\<^sup>T"
  have 1: "f \<sqinter> -q \<le> -h \<sqinter> --g"
    using assms(1) inf.coboundedI1 by simp
  have "(f \<sqinter> q)\<^sup>T \<le> (-h \<sqinter> --g)\<^sup>T"
    using assms(1) inf.coboundedI1 conv_isotone by simp
  also have "... = -h \<sqinter> --g"
    using assms(3,4) conv_complement conv_dist_inf by simp
  finally have "?f \<le> (-h \<sqinter> --g) \<squnion> (e \<sqinter> --g)"
    using 1 assms(2) inf.absorb1 semiring.add_right_mono by simp
  also have "... \<le> (-h \<squnion> --e) \<sqinter> --g"
    by (simp add: inf.coboundedI1 le_supI2 pp_increasing)
  also have "... \<le> -?h \<sqinter> --g"
    using inf.sup_left_isotone order_trans p_antitone_inf p_supdist_inf by blast
  finally show "?f \<le> --(-?h \<sqinter> g)"
    using inf_pp_semi_commute order_lesseq_imp by blast
qed

end

subsection \<open>Stone Relation Algebras\<close>

text \<open>
We add \<open>pp_dist_comp\<close> and \<open>pp_one\<close>, which follow in relation algebras but not in the present setting.
The main change is that only a Stone algebra is required, not a Boolean algebra.
\<close>

class stone_relation_algebra = pd_allegory + stone_algebra +
  assumes pp_dist_comp : "--(x * y) = --x * --y"
  assumes pp_one [simp]: "--1 = 1"
begin

text \<open>
The following property is a simple consequence of the Stone axiom.
We cannot hope to remove the double complement in it.
\<close>

lemma conv_complement_0_p [simp]:
  "(-x)\<^sup>T \<squnion> (--x)\<^sup>T = top"
  by (metis conv_top conv_dist_sup stone)

lemma theorem24xxiv_pp:
  "-(x * y) \<squnion> --(x * z) = -(x * (y \<sqinter> -z)) \<squnion> --(x * z)"
  by (metis p_dist_inf theorem24xxiii)

lemma asymmetric_linear:
  "asymmetric x \<longleftrightarrow> linear (-x)"
  by (metis conv_complement inf.distrib_left inf_p maddux_3_11_pp p_bot p_dist_inf)

lemma strict_linear_asymmetric:
  "strict_linear x \<Longrightarrow> antisymmetric (-x)"
  by (metis conv_complement eq_refl p_dist_sup pp_one)

lemma regular_complement_top:
  "regular x \<Longrightarrow> x \<squnion> -x = top"
  by (metis stone)

lemma regular_mult_closed:
  "regular x \<Longrightarrow> regular y \<Longrightarrow> regular (x * y)"
  by (simp add: pp_dist_comp)

lemma regular_one_closed:
  "regular 1"
  by simp

text \<open>
The following variants of total and surjective are useful for graphs.
\<close>

lemma pp_total:
  "total (--x) \<longleftrightarrow> -(x*top) = bot"
  by (simp add: dense_pp pp_dist_comp)

lemma pp_surjective:
  "surjective (--x) \<longleftrightarrow> -(top*x) = bot"
  by (metis p_bot p_comp_pp p_top pp_dist_comp)

text \<open>
Bijective elements and mappings are necessarily regular, that is, invariant under double-complement.
This implies that points are regular.
Moreover, also arcs are regular.
\<close>

lemma bijective_regular:
  "bijective x \<Longrightarrow> regular x"
  by (metis comp_bijective_complement mult_left_one regular_one_closed)

lemma mapping_regular:
  "mapping x \<Longrightarrow> regular x"
  by (metis bijective_regular conv_complement conv_involutive total_conv_surjective)

lemma arc_regular:
  assumes "arc x"
    shows "regular x"
proof -
  have "--x \<le> --(x * top \<sqinter> top * x)"
    by (simp add: pp_isotone top_left_mult_increasing top_right_mult_increasing)
  also have "... = --(x * top) \<sqinter> --(top * x)"
    by simp
  also have "... = x * top \<sqinter> top * x"
    by (metis assms bijective_regular conv_top conv_dist_comp conv_involutive mapping_regular)
  also have "... \<le> x * x\<^sup>T * top * x"
    by (metis comp_associative dedekind_1 inf.commute inf_top.right_neutral)
  also have "... \<le> x"
    by (metis assms comp_right_one conv_top comp_associative conv_dist_comp conv_involutive mult_right_isotone vector_top_closed)
  finally show ?thesis
    by (simp add: antisym pp_increasing)
qed

(*
lemma conv_complement_0 [simp]: "x\<^sup>T \<squnion> (-x)\<^sup>T = top" nitpick [expect=genuine] oops
lemma schroeder_3: "x * y \<le> z \<longleftrightarrow> x\<^sup>T * -z \<le> -y" nitpick [expect=genuine] oops
lemma schroeder_4: "x * y \<le> z \<longleftrightarrow> -z * y\<^sup>T \<le> -x" nitpick [expect=genuine] oops
lemma theorem24xxiv: "-(x * y) \<squnion> (x * z) = -(x * (y \<sqinter> -z)) \<squnion> (x * z)" nitpick [expect=genuine] oops
lemma vector_N: "x = x * top \<longrightarrow> N(x) = x \<sqinter> 1" nitpick [expect=genuine] oops
lemma N_vector [simp]: "N(x * top) = x * top \<sqinter> 1" nitpick [expect=genuine] oops
lemma N_vector_top [simp]: "N(x * top) * top = x * top" nitpick [expect=genuine] oops
lemma N_below_inf_one: "N(x) \<le> x \<sqinter> 1" nitpick [expect=genuine] oops
lemma N_below: "N(x) \<le> x" nitpick [expect=genuine] oops
lemma n_split_omega_mult: "xs * xo = xo \<and> xo * top = xo \<longrightarrow> N(top) * xo = xs * N(xo) * top" nitpick [expect=genuine] oops
lemma complement_vector: "vector v \<longleftrightarrow> vector (-v)" nitpick [expect=genuine] oops
lemma complement_covector: "covector v \<longleftrightarrow> covector (-v)" nitpick [expect=genuine] oops
lemma triple_schroeder: "x * y * z \<le> w \<longleftrightarrow> x\<^sup>T * -w * z\<^sup>T \<le> -y" nitpick [expect=genuine] oops
lemma schroeder_5: "x * y \<le> z \<longleftrightarrow> y * -z\<^sup>T \<le> -x\<^sup>T" nitpick [expect=genuine] oops
lemma schroeder_6: "x * y \<le> z \<longleftrightarrow> -z\<^sup>T * x \<le> -y\<^sup>T" nitpick [expect=genuine] oops
*)

end

text \<open>
Every Stone algebra can be expanded to a Stone relation algebra by identifying the semiring and lattice structures and taking identity as converse.
\<close>

sublocale stone_algebra < comp_inf: stone_relation_algebra where one = top and times = inf and conv = id
proof (unfold_locales, goal_cases)
  case 7
  show ?case by (simp add: inf_commute)
qed (auto simp: inf.assoc inf_sup_distrib2 inf_left_commute)

text \<open>
Every bounded linear order can be expanded to a Stone algebra, which can be expanded to a Stone relation algebra by reusing some of the operations.
In particular, composition is meet, its identity is \<open>top\<close> and converse is the identity function.
\<close>

class linorder_stone_relation_algebra_expansion = linorder_stone_algebra_expansion + times + conv + one +
  assumes times_def [simp]: "x * y = min x y"
  assumes conv_def [simp]: "x\<^sup>T = x"
  assumes one_def [simp]: "1 = top"
begin

lemma times_inf [simp]:
  "x * y = x \<sqinter> y"
  by simp

subclass stone_relation_algebra
  apply unfold_locales
  using comp_inf.mult_right_dist_sup inf_commute inf_assoc inf_left_commute pp_dist_inf min_def by simp_all

lemma times_dense:
  "x \<noteq> bot \<Longrightarrow> y \<noteq> bot \<Longrightarrow> x * y \<noteq> bot"
  using inf_dense min_inf times_def by presburger

end

subsection \<open>Relation Algebras\<close>

text \<open>
For a relation algebra, we only require that the underlying lattice is a Boolean algebra.
In fact, the only missing axiom is that double-complement is the identity.
\<close>

class relation_algebra = boolean_algebra + stone_relation_algebra
begin

lemma conv_complement_0 [simp]:
  "x\<^sup>T \<squnion> (-x)\<^sup>T = top"
  by (simp add: conv_complement)

text \<open>
We now obtain the original formulations of the Schr\"oder equivalences.
\<close>

lemma schroeder_3:
  "x * y \<le> z \<longleftrightarrow> x\<^sup>T * -z \<le> -y"
  by (simp add: schroeder_3_p)

lemma schroeder_4:
  "x * y \<le> z \<longleftrightarrow> -z * y\<^sup>T \<le> -x"
  by (simp add: schroeder_4_p)

lemma theorem24xxiv:
  "-(x * y) \<squnion> (x * z) = -(x * (y \<sqinter> -z)) \<squnion> (x * z)"
  using theorem24xxiv_pp by auto

lemma vector_N:
  "vector x \<Longrightarrow> N(x) = x \<sqinter> 1"
  by (simp add: vector_N_pp)

lemma N_vector [simp]:
  "N(x * top) = x * top \<sqinter> 1"
  by simp

lemma N_vector_top [simp]:
  "N(x * top) * top = x * top"
  using N_vector_top_pp by simp

lemma N_below_inf_one:
  "N(x) \<le> x \<sqinter> 1"
  using N_below_inf_one_pp by simp

lemma N_below:
  "N(x) \<le> x"
  using N_below_pp by simp

lemma n_split_omega_mult:
  "xs * xo = xo \<Longrightarrow> xo * top = xo \<Longrightarrow> N(top) * xo = xs * N(xo) * top"
  using n_split_omega_mult_pp by simp

lemma complement_vector:
  "vector v \<longleftrightarrow> vector (-v)"
  using vector_complement_closed by fastforce

lemma complement_covector:
  "covector v \<longleftrightarrow> covector (-v)"
  using covector_complement_closed by force

lemma triple_schroeder:
  "x * y * z \<le> w \<longleftrightarrow> x\<^sup>T * -w * z\<^sup>T \<le> -y"
  by (simp add: triple_schroeder_p)

lemma schroeder_5:
  "x * y \<le> z \<longleftrightarrow> y * -z\<^sup>T \<le> -x\<^sup>T"
  by (simp add: conv_complement schroeder_5_p)

lemma schroeder_6:
  "x * y \<le> z \<longleftrightarrow> -z\<^sup>T * x \<le> -y\<^sup>T"
  by (simp add: conv_complement schroeder_5_p)

end

text \<open>
We briefly look at the so-called Tarski rule.
In some models of Stone relation algebras it only holds for regular elements, so we add this as an assumption.
\<close>

class stone_relation_algebra_tarski = stone_relation_algebra +
  assumes tarski: "regular x \<Longrightarrow> x \<noteq> bot \<Longrightarrow> top * x * top = top"
begin

text \<open>
We can then show, for example, that every arc is contained in a pseudocomplemented relation or its pseudocomplement.
\<close>

lemma arc_in_partition:
  assumes "arc x"
    shows "x \<le> -y \<or> x \<le> --y"
proof -
  have 1: "x * top * x\<^sup>T \<le> 1 \<and> x\<^sup>T * top * x \<le> 1"
    using assms arc_expanded by auto
  have "\<not> x \<le> --y \<longrightarrow> x \<le> -y"
  proof
    assume "\<not> x \<le> --y"
    hence "x \<sqinter> -y \<noteq> bot"
      using pseudo_complement by simp
    hence "top * (x \<sqinter> -y) * top = top"
      using assms arc_regular tarski by auto
    hence "x = x \<sqinter> top * (x \<sqinter> -y) * top"
      by simp
    also have "... \<le> x \<sqinter> x * ((x \<sqinter> -y) * top)\<^sup>T * (x \<sqinter> -y) * top"
      by (metis dedekind_2 inf.cobounded1 inf.boundedI inf_commute mult_assoc inf.absorb2 top.extremum)
    also have "... = x \<sqinter> x * top * (x\<^sup>T \<sqinter> -y\<^sup>T) * (x \<sqinter> -y) * top"
      by (simp add: comp_associative conv_complement conv_dist_comp conv_dist_inf)
    also have "... \<le> x \<sqinter> x * top * x\<^sup>T * (x \<sqinter> -y) * top"
      using inf.sup_right_isotone mult_left_isotone mult_right_isotone by auto
    also have "... \<le> x \<sqinter> 1 * (x \<sqinter> -y) * top"
      using 1 by (metis comp_associative comp_isotone inf.sup_right_isotone mult_1_left mult_semi_associative)
    also have "... = x \<sqinter> (x \<sqinter> -y) * top"
      by simp
    also have "... \<le> (x \<sqinter> -y) * ((x \<sqinter> -y)\<^sup>T * x)"
      by (metis dedekind_1 inf_commute inf_top_right)
    also have "... \<le> (x \<sqinter> -y) * (x\<^sup>T * x)"
      by (simp add: conv_dist_inf mult_left_isotone mult_right_isotone)
    also have "... \<le> (x \<sqinter> -y) * (x\<^sup>T * top * x)"
      by (simp add: mult_assoc mult_right_isotone top_left_mult_increasing)
    also have "... \<le> x \<sqinter> -y"
      using 1 by (metis mult_right_isotone mult_1_right)
    finally show "x \<le> -y"
      by simp
  qed
  thus ?thesis
    by auto
qed

lemma non_bot_arc_in_partition_xor:
  assumes "arc x"
      and "x \<noteq> bot"
    shows "(x \<le> -y \<and> \<not> x \<le> --y) \<or> (\<not> x \<le> -y \<and> x \<le> --y)"
proof -
  have "x \<le> -y \<and> x \<le> --y \<longrightarrow> False"
    by (simp add: assms(2) inf_absorb1 shunting_1_pp)
  thus ?thesis
    using assms(1) arc_in_partition by auto
qed

end

class relation_algebra_tarski = relation_algebra + stone_relation_algebra_tarski

text \<open>
Finally, the above axioms of relation algebras do not imply that they contain at least two elements.
This is necessary, for example, to show that arcs are not empty.
\<close>

class stone_relation_algebra_consistent = stone_relation_algebra +
  assumes consistent: "bot \<noteq> top"
begin

lemma arc_not_bot:
  "arc x \<Longrightarrow> x \<noteq> bot"
  using consistent mult_right_zero by auto

end

class relation_algebra_consistent = relation_algebra + stone_relation_algebra_consistent

class stone_relation_algebra_tarski_consistent = stone_relation_algebra_tarski + stone_relation_algebra_consistent
begin

lemma arc_in_partition_xor:
  "arc x \<Longrightarrow> (x \<le> -y \<and> \<not> x \<le> --y) \<or> (\<not> x \<le> -y \<and> x \<le> --y)"
  by (simp add: non_bot_arc_in_partition_xor arc_not_bot)

end

end

