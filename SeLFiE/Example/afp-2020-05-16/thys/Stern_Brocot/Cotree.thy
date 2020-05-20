(* Author: Andreas Lochbihler, ETH Zurich
   Author: Peter Gammie *)

section \<open>A codatatype of infinite binary trees\<close>

theory Cotree imports 
  Main
  Applicative_Lifting.Applicative
  "HOL-Library.BNF_Corec"
  "HOL-Library.Adhoc_Overloading"
begin

context notes [[bnf_internals]]
begin
  codatatype 'a tree = Node (root: 'a) (left: "'a tree") (right: "'a tree")
end

lemma rel_treeD:
  assumes "rel_tree A x y"
  shows rel_tree_rootD: "A (root x) (root y)"
  and rel_tree_leftD: "rel_tree A (left x) (left y)"
  and rel_tree_rightD: "rel_tree A (right x) (right y)"
using assms
by(cases x y rule: tree.exhaust[case_product tree.exhaust], simp_all)+

lemmas [simp] = tree.map_sel tree.map_comp

lemma set_tree_induct[consumes 1, case_names root left right]:
  assumes x: "x \<in> set_tree t"
  and root: "\<And>t. P (root t) t"
  and left: "\<And>x t. \<lbrakk> x \<in> set_tree (left t); P x (left t) \<rbrakk> \<Longrightarrow> P x t"
  and right: "\<And>x t. \<lbrakk> x \<in> set_tree (right t); P x (right t) \<rbrakk> \<Longrightarrow> P x t"
  shows "P x t"
using x
proof(rule tree.set_induct)
  fix l x r
  from root[of "Node x l r"] show "P x (Node x l r)" by simp
qed(auto intro: left right)

lemma corec_tree_cong:
  assumes "\<And>x. stopL x \<Longrightarrow> STOPL x = STOPL' x"
  and "\<And>x. ~ stopL x \<Longrightarrow> LEFT x = LEFT' x"
  and "\<And>x. stopR x \<Longrightarrow> STOPR x = STOPR' x"
  and "\<And>x. \<not> stopR x \<Longrightarrow> RIGHT x = RIGHT' x"
  shows "corec_tree ROOT stopL STOPL LEFT stopR STOPR RIGHT = 
         corec_tree ROOT stopL STOPL' LEFT' stopR STOPR' RIGHT'"
  (is "?lhs = ?rhs")
proof
  fix x
  show "?lhs x = ?rhs x"
    by(coinduction arbitrary: x rule: tree.coinduct_strong)(auto simp add: assms)
qed

context 
  fixes g1 :: "'a \<Rightarrow> 'b"
  and g22 :: "'a \<Rightarrow> 'a"
  and g32 :: "'a \<Rightarrow> 'a"
begin

corec unfold_tree :: "'a \<Rightarrow> 'b tree"
where "unfold_tree a = Node (g1 a) (unfold_tree (g22 a)) (unfold_tree (g32 a))"

lemma unfold_tree_simps [simp]:
  "root (unfold_tree a) = g1 a"
  "left (unfold_tree a) = unfold_tree (g22 a)"
  "right (unfold_tree a) = unfold_tree (g32 a)"
by(subst unfold_tree.code; simp; fail)+

end

lemma unfold_tree_unique:
  assumes "\<And>s. root (f s) = ROOT s"
  and "\<And>s. left (f s) = f (LEFT s)"
  and "\<And>s. right (f s) = f (RIGHT s)"
  shows "f s = unfold_tree ROOT LEFT RIGHT s"
by(rule unfold_tree.unique[THEN fun_cong])(auto simp add: fun_eq_iff assms intro: tree.expand)

subsection \<open>Applicative functor for @{typ "'a tree"}\<close>

context fixes x :: "'a" begin
corec pure_tree :: "'a tree"
where "pure_tree = Node x pure_tree pure_tree"
end

lemmas pure_tree_unfold = pure_tree.code

lemma pure_tree_simps [simp]: 
  "root (pure_tree x) = x"
  "left (pure_tree x) = pure_tree x"
  "right (pure_tree x) = pure_tree x"
by(subst pure_tree_unfold; simp; fail)+

adhoc_overloading pure pure_tree

lemma pure_tree_parametric [transfer_rule]: "(rel_fun A (rel_tree A)) pure pure"
by(rule rel_funI)(coinduction, auto)

lemma map_pure_tree [simp]: "map_tree f (pure x) = pure (f x)"
by(coinduction arbitrary: x) auto

lemmas pure_tree_unique = pure_tree.unique

primcorec (transfer) ap_tree :: "('a \<Rightarrow> 'b) tree \<Rightarrow> 'a tree \<Rightarrow> 'b tree"
where
  "root (ap_tree f x) = root f (root x)"
| "left (ap_tree f x) = ap_tree (left f) (left x)"
| "right (ap_tree f x) = ap_tree (right f) (right x)"

adhoc_overloading Applicative.ap ap_tree

unbundle applicative_syntax

lemma ap_tree_pure_Node [simp]:
  "pure f \<diamondop> Node x l r = Node (f x) (pure f \<diamondop> l) (pure f \<diamondop> r)"
by(rule tree.expand) auto

lemma ap_tree_Node_Node [simp]:
  "Node f fl fr \<diamondop> Node x l r = Node (f x) (fl \<diamondop> l) (fr \<diamondop> r)"
by(rule tree.expand) auto

text \<open>Applicative functor laws\<close>

lemma map_tree_ap_tree_pure_tree:
  "pure f \<diamondop> u = map_tree f u"
by(coinduction arbitrary: u) auto

lemma ap_tree_identity: "pure id \<diamondop> t = t"
by(simp add: map_tree_ap_tree_pure_tree tree.map_id)

lemma ap_tree_composition:
  "pure (\<circ>) \<diamondop> r1 \<diamondop> r2 \<diamondop> r3 = r1 \<diamondop> (r2 \<diamondop> r3)"
by(coinduction arbitrary: r1 r2 r3) auto

lemma ap_tree_homomorphism:
  "pure f \<diamondop> pure x = pure (f x)"
by(simp add: map_tree_ap_tree_pure_tree)

lemma ap_tree_interchange:
  "t \<diamondop> pure x = pure (\<lambda>f. f x) \<diamondop> t"
by(coinduction arbitrary: t) auto

lemma ap_tree_K_tree: "pure (\<lambda>x y. x) \<diamondop> u \<diamondop> v = u"
by(coinduction arbitrary: u v)(auto)

lemma ap_tree_C_tree: "pure (\<lambda>f x y. f y x) \<diamondop> u \<diamondop> v \<diamondop> w = u \<diamondop> w \<diamondop> v"
by(coinduction arbitrary: u v w)(auto)

lemma ap_tree_W_tree: "pure (\<lambda>f x. f x x) \<diamondop> f \<diamondop> x = f \<diamondop> x \<diamondop> x"
by(coinduction arbitrary: f x)(auto)

applicative tree (K, W) for
  pure: pure_tree
  ap: ap_tree
  rel: rel_tree
  set: set_tree
proof -
  fix R :: "'b \<Rightarrow> 'c \<Rightarrow> bool" and f :: "('a \<Rightarrow> 'b) tree" and g x
  assume [transfer_rule]: "rel_tree (rel_fun (eq_on (set_tree x)) R) f g"
  have [transfer_rule]: "rel_tree (eq_on (set_tree x)) x x" by(rule tree.rel_refl_strong) simp
  show "rel_tree R (f \<diamondop> x) (g \<diamondop> x)" by transfer_prover
qed(rule ap_tree_homomorphism ap_tree_composition[unfolded o_def[abs_def]] ap_tree_K_tree ap_tree_W_tree ap_tree_interchange pure_tree_parametric)+

declare map_tree_ap_tree_pure_tree[symmetric, applicative_unfold]

lemma ap_tree_strong_extensional:
  "(\<And>x. f \<diamondop> pure x = g \<diamondop> pure x) \<Longrightarrow> f = g"
proof(coinduction arbitrary: f g)
  case [rule_format]: (Eq_tree f g)
  have "root f = root g"
  proof
    fix x
    show "root f x = root g x"
      using Eq_tree[of x] by(subst (asm) (1 2) ap_tree.ctr) simp
  qed
  moreover {
    fix x
    have "left f \<diamondop> pure x = left g \<diamondop> pure x"
      using Eq_tree[of x] by(subst (asm) (1 2) ap_tree.ctr) simp
  } moreover {
    fix x
    have "right f \<diamondop> pure x = right g \<diamondop> pure x"
      using Eq_tree[of x] by(subst (asm) (1 2) ap_tree.ctr) simp
  } ultimately show ?case by simp
qed

lemma ap_tree_extensional:
  "(\<And>x. f \<diamondop> x = g \<diamondop> x) \<Longrightarrow> f = g"
by(rule ap_tree_strong_extensional) simp

subsection \<open>Standard tree combinators\<close>

subsubsection \<open>Recurse combinator\<close>

text \<open>
  This will be the main combinator to define trees recursively

  Uniqueness for this gives us the unique fixed-point theorem for guarded recursive definitions.
\<close>
lemma map_unfold_tree [simp]: fixes l r x
 defines "unf \<equiv> unfold_tree (\<lambda>f. f x) (\<lambda>f. f \<circ> l) (\<lambda>f. f \<circ> r)"
 shows "map_tree G (unf F) = unf (G \<circ> F)"
by(coinduction arbitrary: F G)(auto 4 3 simp add: unf_def o_assoc)

friend_of_corec map_tree :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "map_tree f t = Node (f (root t)) (map_tree f (left t)) (map_tree f (right t))"
subgoal by (rule tree.expand; simp)
subgoal by (fold relator_eq; transfer_prover)
done

context fixes l :: "'a \<Rightarrow> 'a" and r :: "'a \<Rightarrow> 'a" and x :: "'a" begin
corec tree_recurse :: "'a tree"
where "tree_recurse = Node x (map_tree l tree_recurse) (map_tree r tree_recurse)"
end

lemma tree_recurse_simps [simp]:
  "root (tree_recurse l r x) = x"
  "left (tree_recurse l r x) = map_tree l (tree_recurse l r x)"
  "right (tree_recurse l r x) = map_tree r (tree_recurse l r x)"
by(subst tree_recurse.code; simp; fail)+

lemma tree_recurse_unfold:
  "tree_recurse l r x = Node x (map_tree l (tree_recurse l r x)) (map_tree r (tree_recurse l r x))"
by(fact tree_recurse.code)

lemma tree_recurse_fusion:
  assumes "h \<circ> l = l' \<circ> h" and "h \<circ> r = r' \<circ> h"
  shows "map_tree h (tree_recurse l r x) = tree_recurse l' r' (h x)"
by(rule tree_recurse.unique)(simp add: tree.expand assms)

subsubsection \<open>Tree iteration\<close>

context fixes l :: "'a \<Rightarrow> 'a" and r :: "'a \<Rightarrow> 'a" begin
primcorec tree_iterate :: " 'a \<Rightarrow> 'a tree"
where "tree_iterate s = Node s (tree_iterate (l s)) (tree_iterate (r s))"
end

lemma unfold_tree_tree_iterate:
  "unfold_tree out l r = map_tree out \<circ> tree_iterate l r"
by(rule ext)(rule unfold_tree_unique[symmetric]; simp)

lemma tree_iterate_fusion:
  assumes "h \<circ> l = l' \<circ> h"
  assumes "h \<circ> r = r' \<circ> h"
  shows "map_tree h (tree_iterate l r x) = tree_iterate l' r' (h x)"
apply(coinduction arbitrary: x)
using assms by(auto simp add: fun_eq_iff)

subsubsection \<open>Tree traversal\<close>

datatype dir = L | R
type_synonym path = "dir list"

definition traverse_tree :: "path \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
where "traverse_tree path \<equiv> foldr (\<lambda>d f. f \<circ> case_dir left right d) path id"

lemma traverse_tree_simps[simp]:
  "traverse_tree [] = id"
  "traverse_tree (d # path) = traverse_tree path \<circ> (case d of L \<Rightarrow> left | R \<Rightarrow> right)"
by (simp_all add: traverse_tree_def)

lemma traverse_tree_map_tree [simp]:
  "traverse_tree path (map_tree f t) = map_tree f (traverse_tree path t)"
by (induct path arbitrary: t) (simp_all split: dir.splits)

lemma traverse_tree_append [simp]:
  "traverse_tree (path @ ext) t = traverse_tree ext (traverse_tree path t)"
by (induct path arbitrary: t) simp_all

text\<open>@{const "traverse_tree"} is an applicative-functor homomorphism.\<close>

lemma traverse_tree_pure_tree [simp]:
  "traverse_tree path (pure x) = pure x"
by (induct path arbitrary: x) (simp_all split: dir.splits)

lemma traverse_tree_ap [simp]:
  "traverse_tree path (f \<diamondop> x) = traverse_tree path f \<diamondop> traverse_tree path x"
by (induct path arbitrary: f x) (simp_all split: dir.splits)

context fixes l r :: "'a \<Rightarrow> 'a" begin

primrec traverse_dir :: "dir \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "traverse_dir L = l"
| "traverse_dir R = r"

abbreviation traverse_path :: "path \<Rightarrow> 'a \<Rightarrow> 'a"
where "traverse_path \<equiv> fold traverse_dir"

end

lemma traverse_tree_tree_iterate:
  "traverse_tree path (tree_iterate l r s) =
   tree_iterate l r (traverse_path l r path s)"
by (induct path arbitrary: s) (simp_all split: dir.splits)

text\<open>

\citeauthor{DBLP:journals/jfp/Hinze09} shows that if the tree
construction function is suitably monoidal then recursion and
iteration define the same tree.

\<close>

lemma tree_recurse_iterate:
  assumes monoid:
    "\<And>x y z. f (f x y) z = f x (f y z)"
    "\<And>x. f x \<epsilon> = x"
    "\<And>x. f \<epsilon> x = x"
  shows "tree_recurse (f l) (f r) \<epsilon> = tree_iterate (\<lambda>x. f x l) (\<lambda>x. f x r) \<epsilon>"
apply(rule tree_recurse.unique[symmetric])
apply(rule tree.expand)
apply(simp add: tree_iterate_fusion[where r'="\<lambda>x. f x r" and l'="\<lambda>x. f x l"] fun_eq_iff monoid)
done

subsubsection \<open>Mirroring\<close>

primcorec mirror :: "'a tree \<Rightarrow> 'a tree"
where
  "root (mirror t) = root t"
| "left (mirror t) = mirror (right t)"
| "right (mirror t) = mirror (left t)"

lemma mirror_unfold: "mirror (Node x l r) = Node x (mirror r) (mirror l)"
by(rule tree.expand) simp

lemma mirror_pure: "mirror (pure x) = pure x"
by(coinduction rule: tree.coinduct) simp

lemma mirror_ap_tree: "mirror (f \<diamondop> x) = mirror f \<diamondop> mirror x"
by(coinduction arbitrary: f x) auto

end
