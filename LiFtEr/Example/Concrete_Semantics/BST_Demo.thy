(*
 * This file "BST_Demo.thy" was originally developed by Tobias Nipkow and Gerwin Klein
 * as Isabelle theory files accompanying their book "Concrete Semantics".
 * 
 * The PDF file of the book and the original Isabelle theory files are available 
 * at the following website:
 *   http://concrete-semantics.org/index.html
 *
 *)
theory BST_Demo
imports "~~/src/HOL/Library/Tree"
begin

(* useful most of the time: *)
declare Let_def [simp]

section "Basic BST Functions"

fun isin :: "('a::linorder) tree \<Rightarrow> 'a \<Rightarrow> bool" where
"isin Leaf x = False" |
"isin (Node l a r) x =
  (if x < a then isin l x else
   if x > a then isin r x
   else True)"

fun ins :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"ins x Leaf = Node Leaf x Leaf" |
"ins x (Node l a r) =
  (if x < a then Node (ins x l) a r else
   if x > a then Node l a (ins x r)
   else Node l a r)"

subsection "Functional Correctness"

lemma "bst t \<Longrightarrow> isin t x = (x \<in> set_tree t)"
apply(induction t)
apply auto
done

lemma set_tree_ins: "set_tree (ins x t) = {x} \<union> set_tree t"
apply(induction t)
apply auto
done

subsection "Preservation of Invariant"

lemma bst_ins: "bst t \<Longrightarrow> bst (ins x t)"
apply(induction t)
apply (auto simp: set_tree_ins)
done


section "Reducing the Number of Comparisons"

text\<open>Idea: never test for \<open>=\<close> but remember the last value where you
should have tested for \<open>=\<close> but did not. Compare with that value when
you reach a leaf.\<close>

fun isin2 :: "('a::linorder) tree \<Rightarrow> 'a option \<Rightarrow> 'a \<Rightarrow> bool" where
"isin2 Leaf z x = (case z of None \<Rightarrow> False | Some y \<Rightarrow> x = y) " |
"isin2 (Node l a r) z x =
  (if x < a then isin2 l z x else isin2 r (Some a) x)"

lemma isin2_Some:
  "\<lbrakk> bst t;  \<forall>x \<in> set_tree t. y < x \<rbrakk>
  \<Longrightarrow> isin2 t (Some y) x = (isin t x \<or> x=y)"
apply(induction t arbitrary: y)
apply auto
done

lemma isin2_None:
  "bst t \<Longrightarrow> isin2 t None x = isin t x"
apply(induction t)
apply (auto simp: isin2_Some)
done


section "Trees with Size Info"

type_synonym 'a tree_sz = "('a * nat) tree"

fun inv_sz :: "('a::linorder) tree_sz \<Rightarrow> bool" where
"inv_sz \<langle>\<rangle> = True" |
"inv_sz \<langle>l, (a,s), r\<rangle> = (inv_sz l \<and> inv_sz r \<and> s = size l + size r + 1)"

fun sz :: "'a tree_sz \<Rightarrow> nat" where
"sz Leaf = 0" |
"sz (Node _ (_,s) _) = s"

abbreviation un_sz :: "'a tree_sz \<Rightarrow> 'a tree" where
"un_sz t == map_tree fst t"

fun ins_sz :: "'a::linorder \<Rightarrow> 'a tree_sz \<Rightarrow> 'a tree_sz" where
"ins_sz x Leaf = Node Leaf (x,1) Leaf" |
"ins_sz x (Node l (a,s) r) =
  (if x < a then let l' = ins_sz x l in Node l' (a, sz l' + sz r + 1) r else
   if x > a then let r' = ins_sz x r in Node l (a, sz l + sz r' + 1) r'
   else Node l (a,s) r)"

subsection "Functional Correctness"

lemma un_sz_ins_sz: "un_sz (ins_sz x t) = ins x (un_sz t)"
apply(induction t)
apply auto
done

subsection "Preservation of Invariants"

lemma "bst(un_sz t) \<Longrightarrow> bst(un_sz (ins_sz x t))"
by(simp add: un_sz_ins_sz bst_ins)

lemma sz_size[simp]: "inv_sz t \<Longrightarrow> sz t = size t"
apply(induction t)
apply auto
done

lemma "inv_sz t \<Longrightarrow> inv_sz (ins_sz x t)"
apply(induction t)
apply (auto)
done

(* nth smallest element: *)
fun nth_min :: "('a::linorder) tree_sz \<Rightarrow> nat \<Rightarrow> 'a" where
"nth_min \<langle>l, (a,s), r\<rangle> n =
   (let sl = sz l in
    if n = sl then a else
    if n < sl then nth_min l n else nth_min r (n-sl-1))"

lemma "\<lbrakk> bst(un_sz t);  inv_sz t;  n < size t \<rbrakk>
 \<Longrightarrow> nth_min t n = nth (inorder(un_sz t)) n"
apply(induction t arbitrary: n)
apply (auto simp: nth_append)
done


section "Compressing the Height of BSTs"

fun compress :: "'a tree \<Rightarrow> 'a tree" where
"compress (Node Leaf a t) =
  (case compress t of
     Node Leaf b u \<Rightarrow> Node (Node Leaf a Leaf) b u |
     u \<Rightarrow> Node Leaf a u)" |
"compress (Node l a r) = Node (compress l) a (compress r)" |
"compress Leaf = Leaf"

(* Another way of saying that \<open>bst\<close> and \<open>set_tree\<close> are preserved: *)
lemma "inorder(compress t) = inorder t"
apply(induction t rule: compress.induct)
apply (auto split: tree.split)
done

lemma "height (compress t) \<le> height t"
apply(induction t rule: compress.induct)
apply (auto split: tree.split)
done

(* What is the correct relationship? *)
lemma "height t \<le> height (compress t)"
oops


section "BST Implementation of Maps"

fun lookup :: "('a::linorder * 'b) tree \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup Leaf x = None" |
"lookup (Node l (a,b) r) x =
  (if x < a then lookup l x else
   if x > a then lookup r x
   else Some b)"

fun update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a::linorder * 'b) tree \<Rightarrow> ('a * 'b) tree" where
"update x y Leaf = Node Leaf (x,y) Leaf" |
"update x y (Node l (a,b) r) =
  (if x < a then Node (update x y l) (a,b) r else
   if x > a then Node l (a,b) (update x y r)
   else Node l (x,y) r)"

subsection "Functional Correctness"

lemma "lookup (update x y t) a = (if x=a then Some y else lookup t a)"
apply(induction t)
apply auto
done

subsection "Preservation of Invariant"

definition "bst1 t = bst (map_tree fst t)"

lemma map_tree_update: "map_tree fst (update x y t) = ins x (map_tree fst t)"
apply(induction t)
apply auto
done

lemma "bst1 t \<Longrightarrow> bst1(update x y t)"
apply(induction t)
apply (auto simp: bst1_def map_tree_update set_tree_ins)
done

end
