(*  Title:      Dual_Lattice.thy
    Author:     Peter Gammie, borrowing from Makarius's Lattice theory
                More modifications by Brian Huffman
*)

section {* Lattice operations on dually-ordered types *}

theory Dual_Lattice
imports Main
begin

text {*
  The \emph{dual} of an ordered structure is an isomorphic copy of the
  underlying type, with the @{text \<le>} relation defined as the inverse
  of the original one.
*}

datatype 'a dual = dual 'a

primrec undual :: "'a dual \<Rightarrow> 'a" where
  undual_dual: "undual (dual x) = x"

lemma dual_undual [simp]: "dual (undual x') = x'"
  by (cases x') simp

lemma undual_comp_dual [simp]:
  "undual \<circ> dual = id"
  by (simp add: fun_eq_iff)

lemma dual_comp_undual [simp]:
  "dual \<circ> undual = id"
  by (simp add: fun_eq_iff)

lemma dual_eq_iff: "x = y \<longleftrightarrow> undual x = undual y"
  by (induct x, induct y, simp)

subsection {* Pointwise ordering *}

instantiation dual :: (ord) ord
begin

definition
  "x \<le> y \<longleftrightarrow> undual y \<le> undual x"

definition
  "(x::'a dual) < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance ..

end

lemma undual_leq [iff?]: "(undual x' \<le> undual y') = (y' \<le> x')"
  by (simp add: less_eq_dual_def)

lemma dual_leq [intro?, simp]: "(dual x \<le> dual y) = (y \<le> x)"
  by (simp add: less_eq_dual_def)

(* FIXME maybe this isn't so useful. *)

text {*
  \medskip Functions @{term dual} and @{term undual} are inverse to
  each other; this entails the following fundamental properties.
*}

text {*
  \medskip Since @{term dual} (and @{term undual}) are both injective
  and surjective, the basic logical connectives (equality,
  quantification etc.) are transferred as follows.
*}

lemma undual_equality [iff?]: "(undual x' = undual y') = (x' = y')"
  by (cases x', cases y') simp

lemma dual_equality [iff?]: "(dual x = dual y) = (x = y)"
  by simp

(* BH: a generalization of dual_ball[symmetric] is already in ball_simps *)
(* BH: This proof can be replaced with "by simp" *)
lemma dual_ball [iff?]: "(\<forall>x \<in> A. P (dual x)) = (\<forall>x' \<in> dual ` A. P x')"
  by simp

lemma range_dual [simp]: "surj dual"
proof -
  have "\<And>x'. dual (undual x') = x'" by simp
  thus "surj dual" by (rule surjI)
qed

lemma dual_all [iff?]: "(\<forall>x. P (dual x)) = (\<forall>x'. P x')"
proof -
  have "(\<forall>x \<in> UNIV. P (dual x)) = (\<forall>x' \<in> dual ` UNIV. P x')"
    by (rule dual_ball)
  thus ?thesis by simp
qed

lemma dual_ex: "(\<exists>x. P (dual x)) = (\<exists>x'. P x')"
proof -
  have "(\<forall>x. \<not> P (dual x)) = (\<forall>x'. \<not> P x')"
    by (rule dual_all)
  thus ?thesis by blast
qed

lemma dual_Collect: "{dual x| x. P (dual x)} = {x'. P x'}"
proof -
  have "{dual x| x. P (dual x)} = {x'. \<exists>x''. x' = x'' \<and> P x''}"
    by (simp only: dual_ex [symmetric])
  thus ?thesis by blast
qed

instance dual :: (preorder) preorder
proof
  fix x y z :: "'a dual"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (rule less_dual_def)
  show "x \<le> x"
    unfolding less_eq_dual_def
    by fast
  assume "x \<le> y" and "y \<le> z" thus "x \<le> z"
    unfolding less_eq_dual_def
    by (fast elim: order_trans)
qed

instance dual :: (order) order
  by standard (auto simp: less_eq_dual_def undual_equality)


subsection {* Binary infimum and supremum *}

text {*
  The class of lattices is closed under formation of dual structures.
  This means that for any theorem of lattice theory, the dualized
  statement holds as well; this important fact simplifies many proofs
  of lattice theory.
*}

instantiation dual :: (semilattice_sup) semilattice_inf
begin

definition
  "inf f g = dual (sup (undual f) (undual g))"

instance
  by standard (auto simp: inf_dual_def less_eq_dual_def)

end

instantiation dual :: (semilattice_inf) semilattice_sup
begin

definition
  "sup f g = dual (inf (undual f) (undual g))"

instance
  by standard (auto simp: sup_dual_def less_eq_dual_def)

end

instance dual :: (lattice) lattice ..

text {*
  Apparently, the @{text \<sqinter>} and @{text \<squnion>} operations are dual to each
  other.
*}

theorem dual_inf [intro?]: "dual (inf x y) = sup (dual x) (dual y)"
  unfolding sup_dual_def by simp
(* BH: Why the "intro?" attribute? Why not just "simp"? *)

theorem dual_sup [intro?]: "dual (sup x y) = inf (dual x) (dual y)"
  unfolding inf_dual_def by simp

lemma undual_inf [simp]: "undual (inf x y) = sup (undual x) (undual y)"
  unfolding inf_dual_def by (rule undual_dual)

lemma undual_sup [simp]: "undual (sup x y) = inf (undual x) (undual y)"
  unfolding sup_dual_def by (rule undual_dual)

text {*
  Infimum and supremum are dual to each other.
*}

theorem dual_inf' [iff?]:
    "(inf (dual x) (dual y) = s) = (sup x y = undual s)"
  by (cases s) (simp add: inf_dual_def)
(* BH: This rule seems very contrived. When is it ever useful? *)

theorem dual_sup' [iff?]:
    "(sup (dual x) (dual y) = s) = (inf x y = undual s)"
  by (cases s) (simp add: sup_dual_def)

instance dual :: (distrib_lattice) distrib_lattice
  by standard (simp add: inf_dual_def sup_dual_def inf_sup_distrib1)


subsection {* Top and bottom elements *}

instantiation dual :: (order_top) order_bot
begin

definition
  "bot = dual top"

instance
  by standard (simp add: bot_dual_def less_eq_dual_def)

end

instantiation dual :: (order_bot) order_top
begin

definition
  "top = dual bot"

instance
  by standard (simp add: top_dual_def less_eq_dual_def)

end

instance dual :: (bounded_lattice_top) bounded_lattice_bot ..

instance dual :: (bounded_lattice_bot) bounded_lattice_top ..

instance dual :: (bounded_lattice) bounded_lattice ..

text {*
  Likewise are @{text \<bottom>} and @{text \<top>} duals of each other.
*}

theorem dual_bot [intro?, simp]: "dual bot = top"
  unfolding bot_dual_def top_dual_def by simp
(* BH: What is the "intro?" attribute for? *)

theorem dual_top [intro?, simp]: "dual top = bot"
  unfolding bot_dual_def top_dual_def by simp

theorem undual_bot [simp]: "undual bot = top"
  unfolding bot_dual_def by (rule undual_dual)

theorem undual_top [simp]: "undual top = bot"
  unfolding top_dual_def by (rule undual_dual)

instantiation dual :: (uminus) uminus
begin

definition
  "- x = dual (- undual x)"

instance ..

end

lemma undual_minus [simp]: "undual (- x) = - undual x"
  unfolding uminus_dual_def by (rule undual_dual)

instantiation dual :: (boolean_algebra) boolean_algebra
begin

definition
  "(x::'a dual) - y = inf x (- y)"

instance
  by standard
    (auto simp: dual_eq_iff sup_compl_top inf_compl_bot minus_dual_def)

end

subsection {* Complete lattice operations *}

text {*
  The class of complete lattices is closed under formation of dual
  structures.
*}

instantiation dual :: (complete_lattice) complete_lattice
begin

definition
  "Sup A = dual (INFIMUM A undual)"

definition
  "Inf A = dual (SUPREMUM A undual)"

instance
  by standard (auto simp: less_eq_dual_def less_dual_def Sup_dual_def Inf_dual_def
    INF_lower SUP_upper intro: INF_greatest SUP_least)

end

lemma SUP_dual_unfold:
  "SUPREMUM A f = dual (INFIMUM A (undual \<circ> f))"
  by (simp add: Sup_dual_def)

lemma INF_dual_unfold:
  "INFIMUM A f = dual (SUPREMUM A (undual \<circ> f))"
  by (simp add: Inf_dual_def)

text {*
  Apparently, the @{text \<Sqinter>} and @{text \<Squnion>} operations are dual to each
  other.
*}

theorem dual_Inf [intro?]: "dual (Inf A) = SUPREMUM A dual"
  by (simp add: Inf_dual_def Sup_dual_def)
(* BH: Why not [simp]? *)

theorem dual_Sup [intro?]: "dual (Sup A) = INFIMUM A dual"
  by (simp add: Inf_dual_def Sup_dual_def)
(* BH: Why not [simp]? *)

lemma undual_Inf: "undual (Inf A) = SUPREMUM A undual"
  by (simp add: Inf_dual_def)

lemma undual_Sup: "undual (Sup A) = INFIMUM A undual"
  by (simp add: Sup_dual_def)

theorem dual_Inf' [iff?]:
    "(Inf (dual ` A) = dual s) = (Sup A = s)"
  unfolding Inf_dual_def Sup_dual_def by (simp add: image_image)
(* BH: When would this lemma ever be useful? *)

theorem dual_Sup' [iff?]:
    "(Sup (dual ` A) = dual i) = (Inf A = i)"
  unfolding Inf_dual_def Sup_dual_def by (simp add: image_image)

end
