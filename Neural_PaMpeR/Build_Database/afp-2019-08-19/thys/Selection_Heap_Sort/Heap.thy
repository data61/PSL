(*  Title:      Sort.thy
    Author:     Danijela Petrovi\'c, Facylty of Mathematics, University of Belgrade *)

section \<open>Verification of Heap Sort\<close>

theory Heap
imports RemoveMax
begin

subsection \<open>Defining tree and properties of heap\<close>

datatype 'a Tree = "E" | "T" 'a "'a Tree" "'a Tree"

text\<open>With {\em E} is represented empty tree and with {\em T\ \ \ 'a\ \ \ 'a
  Tree\ \ \ 'a Tree} is represented a node whose root element is of
type {\em 'a} and its left and right branch is also a tree of
type {\em 'a}.\<close>

primrec size :: "'a Tree \<Rightarrow> nat" where
  "size E = 0"
| "size (T v l r) = 1 + size l + size r"

text\<open>Definition of the function that makes a multiset from the given tree:\<close>

primrec multiset where
  "multiset E = {#}"
| "multiset (T v l r) = multiset l + {#v#} + multiset r"

primrec val where
 "val (T v _ _) = v"

text\<open>Definition of the function that has the value {\em True} if the tree is
heap, otherwise it is {\em False}:\<close>

fun is_heap :: "'a::linorder Tree \<Rightarrow> bool" where
  "is_heap E = True"
| "is_heap (T v E E) = True"
| "is_heap (T v E r) = (v \<ge> val r \<and> is_heap r)"
| "is_heap (T v l E) = (v \<ge> val l \<and> is_heap l)"
| "is_heap (T v l r) = (v \<ge> val r \<and> is_heap r \<and> v \<ge> val l \<and> is_heap l)"

lemma heap_top_geq:
  assumes "a \<in># multiset t" "is_heap t"
  shows "val t \<ge> a"
using assms
by (induct t rule: is_heap.induct)  (auto split: if_split_asm)

lemma heap_top_max:
  assumes "t \<noteq> E" "is_heap t"
  shows "val t = Max_mset (multiset t)"
proof (rule Max_eqI[symmetric])
  fix y
  assume "y \<in> set_mset (multiset t)"
  thus "y \<le> val t"
    using heap_top_geq [of y t] \<open>is_heap t\<close>
    by simp
next
  show "val t \<in> set_mset (multiset t)"
    using \<open>t \<noteq> E\<close>
    by (cases t) auto
qed simp

text\<open>The next step is to define function {\em remove\_max}, but the
question is weather implementation of {\em remove\_max} depends on
implementation of the functions {\em is\_heap} and {\em multiset}. The
answer is negative. This suggests that another step of refinement
could be added before definition of function {\em
  remove\_max}. Additionally, there are other reasons why this should
be done, for example, function {\em remove\_max} could be implemented
in functional or in imperative manner.
\<close>

locale Heap =  Collection empty is_empty of_list  multiset for 
  empty :: "'b" and 
  is_empty :: "'b \<Rightarrow> bool" and 
  of_list :: "'a::linorder list \<Rightarrow> 'b" and 
  multiset :: "'b \<Rightarrow> 'a::linorder multiset" + 
  fixes as_tree :: "'b \<Rightarrow> 'a::linorder Tree"
  \<comment> \<open>This function is not very important, but it is needed in order to avoide problems with types and to detect that observed object is a tree.\<close>
  fixes remove_max :: "'b \<Rightarrow> 'a \<times> 'b"
  assumes multiset: "multiset l = Heap.multiset (as_tree l)"
  assumes is_heap_of_list: "is_heap (as_tree (of_list i))"
  assumes as_tree_empty: "as_tree t = E \<longleftrightarrow> is_empty t"
  assumes remove_max_multiset': 
  "\<lbrakk>\<not> is_empty l; (m, l') = remove_max l\<rbrakk> \<Longrightarrow> add_mset m (multiset l') = multiset l"
  assumes remove_max_is_heap: 
  "\<lbrakk>\<not> is_empty l; is_heap (as_tree l); (m, l') = remove_max l\<rbrakk> \<Longrightarrow> 
  is_heap (as_tree l')"
  assumes remove_max_val: 
  "\<lbrakk> \<not> is_empty t; (m, t') = remove_max t\<rbrakk> \<Longrightarrow> m = val (as_tree t)"

text\<open>It is very easy to prove that locale {\em Heap} is sublocale of locale {\em RemoveMax}\<close>

sublocale Heap < 
  RemoveMax empty is_empty of_list multiset remove_max "\<lambda> t. is_heap (as_tree t)"
proof
  fix x
  show "is_heap (as_tree (of_list x))"
    by (rule is_heap_of_list)
next
  fix l m l'
  assume "\<not> is_empty l" "(m, l') = remove_max l" 
  thus "add_mset m (multiset l') = multiset l"
    by (rule remove_max_multiset')
next
  fix l m l'
  assume "\<not> is_empty l" "is_heap (as_tree l)" "(m, l') = remove_max l" 
  thus "is_heap (as_tree l')"
    by (rule remove_max_is_heap)
next
  fix l m l'
  assume "\<not> is_empty l" "is_heap (as_tree l)" "(m, l') = remove_max l" 
  thus "m = Max (set l)"
    unfolding set_def
    using heap_top_max[of "as_tree l"] remove_max_val[of l m l'] 
    using multiset is_empty_inj as_tree_empty
    by auto
qed

primrec in_tree where
  "in_tree v E = False"
| "in_tree v (T v' l r) \<longleftrightarrow> v = v' \<or> in_tree v l \<or> in_tree v r"

lemma is_heap_max:
  assumes "in_tree v t" "is_heap t"
  shows "val t \<ge> v"
using assms
apply (induct t rule:is_heap.induct)
by auto

end
