section "Splay Tree"

theory Splay_Tree
imports
  "HOL-Library.Tree"
  "HOL-Data_Structures.Set_Specs"
  "HOL-Data_Structures.Cmp"
begin

declare sorted_wrt.simps(2)[simp del]

text\<open>Splay trees were invented by Sleator and Tarjan~\cite{SleatorT-JACM85}.\<close>

subsection "Function \<open>splay\<close>"

function splay :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"splay x Leaf = Leaf" |
"splay x (Node A x B) = Node A x B" |
"x<b \<Longrightarrow> splay x (Node (Node A x B) b C) = Node A x (Node B b C)" |
"x<b \<Longrightarrow> splay x (Node Leaf b A) = Node Leaf b A" |
"x<a \<Longrightarrow> x<b \<Longrightarrow> splay x (Node (Node Leaf a A) b B) = Node Leaf a (Node A b B)" |
"x<b \<Longrightarrow> x<c \<Longrightarrow> AB \<noteq> Leaf \<Longrightarrow>
 splay x (Node (Node AB b C) c D) =
 (case splay x AB of Node A a B \<Rightarrow> Node A a (Node B b (Node C c D)))" |
"a<x \<Longrightarrow> x<b \<Longrightarrow> splay x (Node (Node A a Leaf) b B) = Node A a (Node Leaf b B)" |
"a<x \<Longrightarrow> x<c \<Longrightarrow> BC \<noteq> Leaf \<Longrightarrow>
 splay x (Node (Node A a BC) c D) =
 (case splay x BC of Node B b C \<Rightarrow> Node (Node A a B) b (Node C c D))" |
"a<x \<Longrightarrow> splay x (Node A a (Node B x C)) = Node (Node A a B) x C" |
"a<x \<Longrightarrow> splay x (Node A a Leaf) = Node A a Leaf" |
"a<x \<Longrightarrow> x<c \<Longrightarrow> BC \<noteq> Leaf \<Longrightarrow>
 splay x (Node A a (Node BC c D)) =
 (case splay x BC of Node B b C \<Rightarrow> Node (Node A a B) b (Node C c D))" |
"a<x \<Longrightarrow> x<b \<Longrightarrow> splay x (Node A a (Node Leaf b C)) = Node (Node A a Leaf) b C" |
"a<x \<Longrightarrow> b<x \<Longrightarrow> splay x (Node A a (Node B b Leaf)) = Node (Node A a B) b Leaf" |
"a<x \<Longrightarrow> b<x \<Longrightarrow> CD \<noteq> Leaf \<Longrightarrow>
 splay x (Node A a (Node B b CD)) =
 (case splay x CD of Node C c D \<Rightarrow> Node (Node (Node A a B) b C) c D)"
apply(atomize_elim)
apply(auto)
(* 1 subgoal *)
apply (subst (asm) neq_Leaf_iff)
apply(auto)
apply (metis tree.exhaust le_less_linear less_linear)+
done

termination splay
by lexicographic_order

lemma splay_code: "splay x (Node AB b CD) =
  (if x=b
   then Node AB b CD
   else if x < b
        then case AB of
          Leaf \<Rightarrow> Node AB b CD |
          Node A a B \<Rightarrow>
            (if x=a then Node A a (Node B b CD)
             else if x < a
                  then if A = Leaf then Node A a (Node B b CD)
                       else case splay x A of
                         Node A\<^sub>1 a' A\<^sub>2 \<Rightarrow> Node A\<^sub>1 a' (Node A\<^sub>2 a (Node B b CD))
                  else if B = Leaf then Node A a (Node B b CD)
                       else case splay x B of
                         Node B\<^sub>1 b' B\<^sub>2 \<Rightarrow> Node (Node A a B\<^sub>1) b' (Node B\<^sub>2 b CD))
        else case CD of
          Leaf \<Rightarrow> Node AB b CD |
          Node C c D \<Rightarrow>
            (if x=c then Node (Node AB b C) c D
             else if x < c
                  then if C = Leaf then Node (Node AB b C) c D
                       else case splay x C of
                         Node C\<^sub>1 c' C\<^sub>2 \<Rightarrow> Node (Node AB b C\<^sub>1) c' (Node C\<^sub>2 c D)
                  else if D=Leaf then Node (Node AB b C) c D
                       else case splay x D of
                         Node D\<^sub>1 d D\<^sub>2 \<Rightarrow> Node (Node (Node AB b C) c D\<^sub>1) d D\<^sub>2))"
by(auto split!: tree.split)

definition is_root :: "'a \<Rightarrow> 'a tree \<Rightarrow> bool" where
"is_root x t = (case t of Leaf \<Rightarrow> False | Node l a r \<Rightarrow> x = a)"

definition "isin t x = is_root x (splay x t)"

definition empty :: "'a tree" where
"empty = Leaf"

hide_const (open) insert

fun insert :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert x t =
  (if t = Leaf then Node Leaf x Leaf
   else case splay x t of
     Node l a r \<Rightarrow>
      case cmp x a of
        EQ \<Rightarrow> Node l a r |
        LT \<Rightarrow> Node l x (Node Leaf a r) |
        GT \<Rightarrow> Node (Node l a Leaf) x r)"


fun splay_max :: "'a tree \<Rightarrow> 'a tree" where
"splay_max Leaf = Leaf" |
"splay_max (Node A a Leaf) = Node A a Leaf" |
"splay_max (Node A a (Node B b CD)) =
  (if CD = Leaf then Node (Node A a B) b Leaf
   else case splay_max CD of
     Node C c D \<Rightarrow> Node (Node (Node A a B) b C) c D)"

lemma splay_max_code: "splay_max t = (case t of
  Leaf \<Rightarrow> t |
  Node la a ra \<Rightarrow> (case ra of
    Leaf \<Rightarrow> t |
    Node lb b rb \<Rightarrow>
      (if rb=Leaf then Node (Node la a lb) b rb
       else case splay_max rb of
              Node lc c rc \<Rightarrow> Node (Node (Node la a lb) b lc) c rc)))"
by(auto simp: neq_Leaf_iff split: tree.split)

definition delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"delete x t =
  (if t = Leaf then Leaf
   else case splay x t of Node l a r \<Rightarrow>
     if x = a
     then if l = Leaf then r else case splay_max l of Node l' m r' \<Rightarrow> Node l' m r
     else Node l a r)"



subsection "Functional Correctness Proofs I"

text \<open>This subsection follows the automated method by Nipkow \cite{Nipkow-ITP16}.\<close>

lemma splay_Leaf_iff[simp]: "(splay a t = Leaf) = (t = Leaf)"
by(induction a t rule: splay.induct) (auto split: tree.splits)

lemma splay_max_Leaf_iff[simp]: "(splay_max t = Leaf) = (t = Leaf)"
by(induction t rule: splay_max.induct)(auto split: tree.splits)


subsubsection "Verification of @{const isin}"

lemma splay_elemsD:
  "splay x t = Node l a r \<Longrightarrow> sorted(inorder t) \<Longrightarrow>
  x \<in> set (inorder t) \<longleftrightarrow> x=a"
by(induction x t arbitrary: l a r rule: splay.induct)
  (auto simp: isin_simps ball_Un split: tree.splits)

lemma isin_set: "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> set (inorder t))"
by (auto simp: isin_def is_root_def dest: splay_elemsD split: tree.splits)


subsubsection "Verification of @{const insert}"

lemma inorder_splay: "inorder(splay x t) = inorder t"
by(induction x t rule: splay.induct)
  (auto simp: neq_Leaf_iff split: tree.split)

lemma sorted_splay:
  "sorted(inorder t) \<Longrightarrow> splay x t = Node l a r \<Longrightarrow>
  sorted(inorder l @ x # inorder r)"
unfolding inorder_splay[of x t, symmetric]
by(induction x t arbitrary: l a r rule: splay.induct)
  (auto simp: sorted_lems sorted_Cons_le sorted_snoc_le split: tree.splits)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
using inorder_splay[of x t, symmetric] sorted_splay[of t x]
by(auto simp: ins_list_simps ins_list_Cons ins_list_snoc neq_Leaf_iff split: tree.split)


subsubsection "Verification of @{const delete}"

lemma inorder_splay_maxD:
  "splay_max t = Node l a r \<Longrightarrow> sorted(inorder t) \<Longrightarrow>
  inorder l @ [a] = inorder t \<and> r = Leaf"
by(induction t arbitrary: l a r rule: splay_max.induct)
  (auto simp: sorted_lems split: tree.splits if_splits)

lemma inorder_delete:
  "sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
using inorder_splay[of x t, symmetric] sorted_splay[of t x]
by (auto simp: del_list_simps del_list_sorted_app delete_def
  del_list_notin_Cons inorder_splay_maxD split: tree.splits)


subsubsection "Overall Correctness"

interpretation splay: Set_by_Ordered
where empty = empty and isin = isin and insert = insert
and delete = delete and inorder = inorder and inv = "\<lambda>_. True"
proof (standard, goal_cases)
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert del: insert.simps)
next
  case 4 thus ?case by(simp add: inorder_delete)
qed (auto simp: empty_def)


subsection "Functional Correctness Proofs II"

text \<open>This subsection follows the traditional approach, is less automated
and is retained more for historic reasons.\<close>

lemma size_splay[simp]: "size (splay a t) = size t"
apply(induction a t rule: splay.induct)
apply auto
 apply(force split: tree.split)+
done

lemma size_if_splay: "splay a t = Node l u r \<Longrightarrow> size t = size l + size r + 1"
by (metis One_nat_def size_splay tree.size(4))

lemma splay_not_Leaf: "t \<noteq> Leaf \<Longrightarrow> \<exists>l x r. splay a t = Node l x r"
by (metis neq_Leaf_iff splay_Leaf_iff)

lemma set_splay: "set_tree(splay a t) = set_tree t"
proof(induction a t rule: splay.induct)
  case (6 a)
  with splay_not_Leaf[OF 6(3), of a] show ?case by(fastforce)
next
  case (8 _ a)
  with splay_not_Leaf[OF 8(3), of a] show ?case by(fastforce)
next
  case (11 _ a)
  with splay_not_Leaf[OF 11(3), of a] show ?case by(fastforce)
next
  case (14 _ a)
  with splay_not_Leaf[OF 14(3), of a] show ?case by(fastforce)
qed auto

lemma splay_bstL: "bst t \<Longrightarrow> splay a t = Node l e r \<Longrightarrow> x \<in> set_tree l \<Longrightarrow> x < a"
apply(induction a t arbitrary: l x r rule: splay.induct)
apply (auto split: tree.splits)
apply auto
done

lemma splay_bstR: "bst t \<Longrightarrow> splay a t = Node l e r \<Longrightarrow> x \<in> set_tree r \<Longrightarrow> a < x"
apply(induction a t arbitrary: l e x r rule: splay.induct)
apply auto
apply (fastforce split!: tree.splits)+
done

lemma bst_splay: "bst t \<Longrightarrow> bst(splay a t)"
proof(induction a t rule: splay.induct)
  case (6 a _ _ ll)
  with splay_not_Leaf[OF 6(3), of a] set_splay[of a ll,symmetric]
  show ?case by (fastforce)
next
  case (8 _ a _ t)
  with splay_not_Leaf[OF 8(3), of a] set_splay[of a t,symmetric]
  show ?case by fastforce
next
  case (11 _ a _ t)
  with splay_not_Leaf[OF 11(3), of a] set_splay[of a t,symmetric]
  show ?case by fastforce
next
  case (14 _ a _ t)
  with splay_not_Leaf[OF 14(3), of a] set_splay[of a t,symmetric]
  show ?case by fastforce
qed auto

lemma splay_to_root: "\<lbrakk> bst t;  splay a t = t' \<rbrakk> \<Longrightarrow>
  a \<in> set_tree t \<longleftrightarrow> (\<exists>l r. t' = Node l a r)"
proof(induction a t arbitrary: t' rule: splay.induct)
  case (6 a)
  with splay_not_Leaf[OF 6(3), of a] show ?case by auto
next
  case (8 _ a)
  with splay_not_Leaf[OF 8(3), of a] show ?case by auto
next
  case (11 _ a)
  with splay_not_Leaf[OF 11(3), of a] show ?case by auto
next
  case (14 _ a)
  with splay_not_Leaf[OF 14(3), of a] show ?case by auto
qed fastforce+


subsubsection "Verification of Is-in Test"

text\<open>To test if an element \<open>a\<close> is in \<open>t\<close>, first perform
@{term"splay a t"}, then check if the root is \<open>a\<close>. One could
put this into one function that returns both a new tree and the test result.\<close>

lemma is_root_splay: "bst t \<Longrightarrow> is_root a (splay a t) \<longleftrightarrow> a \<in> set_tree t"
by(auto simp add: is_root_def splay_to_root split: tree.split)


subsubsection "Verification of @{const insert}"

lemma set_insert: "set_tree(insert a t) = Set.insert a (set_tree t)"
apply(cases t)
 apply simp
using set_splay[of a t]
by(simp split: tree.split) fastforce

lemma bst_insert: "bst t \<Longrightarrow> bst(insert a t)"
apply(cases t)
 apply simp
using bst_splay[of t a] splay_bstL[of t a] splay_bstR[of t a]
by(auto simp: ball_Un split: tree.split)


subsubsection "Verification of \<open>splay_max\<close>"

lemma size_splay_max: "size(splay_max t) = size t"
apply(induction t rule: splay_max.induct)
  apply(simp)
 apply(simp)
apply(clarsimp split: tree.split)
done

lemma size_if_splay_max: "splay_max t = Node l u r \<Longrightarrow> size t = size l + size r + 1"
by (metis One_nat_def size_splay_max tree.size(4))

lemma set_splay_max: "set_tree(splay_max t) = set_tree t"
apply(induction t rule: splay_max.induct)
   apply(simp)
  apply(simp)
apply(force split: tree.split)
done

lemma bst_splay_max: "bst t \<Longrightarrow> bst (splay_max t)"
proof(induction t rule: splay_max.induct)
  case (3 l b rl c rr)
  { fix rrl' d' rrr'
    have "splay_max rr = Node rrl' d' rrr'
       \<Longrightarrow> \<forall>x \<in> set_tree(Node rrl' d' rrr'). c < x" 
      using "3.prems" set_splay_max[of rr]
      by (clarsimp split: tree.split simp: ball_Un)
  }
  with 3 show ?case by (fastforce split: tree.split simp: ball_Un)
qed auto

lemma splay_max_Leaf: "splay_max t = Node l a r \<Longrightarrow> r = Leaf"
by(induction t arbitrary: l rule: splay_max.induct)
  (auto split: tree.splits if_splits)

text\<open>For sanity purposes only:\<close>

lemma splay_max_eq_splay:
  "bst t \<Longrightarrow> \<forall>x \<in> set_tree t. x \<le> a \<Longrightarrow> splay_max t = splay a t"
proof(induction a t rule: splay.induct)
  case (2 a l r)
  show ?case
  proof (cases r)
    case Leaf with 2 show ?thesis by simp
  next
    case Node with 2 show ?thesis by(auto)
  qed
qed (auto simp: neq_Leaf_iff)

lemma splay_max_eq_splay_ex: assumes "bst t" shows "\<exists>a. splay_max t = splay a t"
proof(cases t)
  case Leaf thus ?thesis by simp
next
  case Node
  hence "splay_max t = splay (Max(set_tree t)) t"
    using assms by (auto simp: splay_max_eq_splay)
  thus ?thesis by auto
qed


subsubsection "Verification of @{const delete}"

lemma set_delete: assumes "bst t"
shows "set_tree (delete a t) = set_tree t - {a}"
proof(cases t)
  case Leaf thus ?thesis by(simp add: delete_def)
next
  case (Node l x r)
  obtain l' x' r' where sp[simp]: "splay a (Node l x r) = Node l' x' r'"
    by (metis neq_Leaf_iff splay_Leaf_iff)
  show ?thesis
  proof cases
    assume [simp]: "x' = a"
    show ?thesis
    proof cases
      assume "l' = Leaf"
      thus ?thesis
        using Node assms set_splay[of a "Node l x r"] bst_splay[of "Node l x r" a]
        by(simp add: delete_def split: tree.split prod.split)(fastforce)
    next
      assume "l' \<noteq> Leaf"
      moreover then obtain l'' m r'' where "splay_max l' = Node l'' m r''"
        using splay_max_Leaf_iff tree.exhaust by blast
      moreover have "a \<notin> set_tree l'"
        by (metis (no_types) Node assms less_irrefl sp splay_bstL)
      ultimately show ?thesis
        using Node assms set_splay[of a "Node l x r"] bst_splay[of "Node l x r" a]
          splay_max_Leaf[of l' l'' m r''] set_splay_max[of l']
        by(clarsimp simp: delete_def split: tree.split) auto
    qed
  next
    assume "x' \<noteq> a"
    thus ?thesis using Node assms set_splay[of a "Node l x r"] splay_to_root[OF _ sp]
      by (simp add: delete_def)
  qed
qed

lemma bst_delete: assumes "bst t" shows "bst (delete a t)"
proof(cases t)
  case Leaf thus ?thesis by(simp add: delete_def)
next
  case (Node l x r)
  obtain l' x' r' where sp[simp]: "splay a (Node l x r) = Node l' x' r'"
    by (metis neq_Leaf_iff splay_Leaf_iff)
  show ?thesis
  proof cases
    assume [simp]: "x' = a"
    show ?thesis
    proof cases
      assume "l' = Leaf"
      thus ?thesis using Node assms bst_splay[of "Node l x r" a]
        by(simp add: delete_def split: tree.split prod.split)
    next
      assume "l' \<noteq> Leaf"
      thus ?thesis
        using Node assms set_splay[of a "Node l x r"] bst_splay[of "Node l x r" a]
          bst_splay_max[of l'] set_splay_max[of l']
        by(clarsimp simp: delete_def split: tree.split)
          (metis (no_types) insertI1 less_trans)
    qed
  next
    assume "x' \<noteq> a"
    thus ?thesis using Node assms bst_splay[of "Node l x r" a]
      by(auto simp: delete_def split: tree.split prod.split)
  qed
qed

end
