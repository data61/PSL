(*  Title:      AVL Trees
    Author:     Tobias Nipkow and Cornelia Pusch,
                converted to Isar by Gerwin Klein
                contributions by Achim Brucker, Burkhart Wolff and Jan Smaus
                delete formalization and a transformation to Isar by Ondrej Kuncar
    Maintainer: Gerwin Klein <gerwin.klein at nicta.com.au>

    see the file Changelog for a list of changes
*)

section "AVL Trees"

theory AVL
imports Main
begin

text \<open>
  This is a monolithic formalization of AVL trees.
\<close>

subsection \<open>AVL tree type definition\<close>

datatype (set_of: 'a) tree = ET |  MKT 'a "'a tree" "'a tree" nat

subsection \<open>Invariants and auxiliary functions\<close>

primrec height :: "'a tree \<Rightarrow> nat" where
"height ET = 0" |
"height (MKT x l r h) = max (height l) (height r) + 1"

primrec avl :: "'a tree \<Rightarrow> bool" where
"avl ET = True" |
"avl (MKT x l r h) =
 ((height l = height r \<or> height l = height r + 1 \<or> height r = height l + 1) \<and> 
  h = max (height l) (height r) + 1 \<and> avl l \<and> avl r)"

primrec is_ord :: "('a::order) tree \<Rightarrow> bool" where
"is_ord ET = True" |
"is_ord (MKT n l r h) =
 ((\<forall>n' \<in> set_of l. n' < n) \<and> (\<forall>n' \<in> set_of r. n < n') \<and> is_ord l \<and> is_ord r)"


subsection \<open>AVL interface and implementation\<close>

primrec is_in :: "('a::order) \<Rightarrow> 'a tree \<Rightarrow> bool" where
 "is_in k ET = False" |
 "is_in k (MKT n l r h) = (if k = n then True else
                           if k < n then (is_in k l)
                           else (is_in k r))"

primrec ht :: "'a tree \<Rightarrow> nat" where
"ht ET = 0" |
"ht (MKT x l r h) = h"

definition
 mkt :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"mkt x l r = MKT x l r (max (ht l) (ht r) + 1)"

fun mkt_bal_l where
"mkt_bal_l n l r = (
  if ht l = ht r + 2 then (case l of 
    MKT ln ll lr _ \<Rightarrow> (if ht ll < ht lr
    then case lr of
      MKT lrn lrl lrr _ \<Rightarrow> mkt lrn (mkt ln ll lrl) (mkt n lrr r)
    else mkt ln ll (mkt n lr r)))
  else mkt n l r
)"

fun mkt_bal_r where
"mkt_bal_r n l r = (
  if ht r = ht l + 2 then (case r of
    MKT rn rl rr _ \<Rightarrow> (if ht rl > ht rr
    then case rl of
      MKT rln rll rlr _ \<Rightarrow> mkt rln (mkt n l rll) (mkt rn rlr rr)
    else mkt rn (mkt n l rl) rr))
  else mkt n l r
)"

primrec insert :: "'a::order \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert x ET = MKT x ET ET 1" |
"insert x (MKT n l r h) = 
   (if x=n
    then MKT n l r h
    else if x<n
      then mkt_bal_l n (insert x l) r
      else mkt_bal_r n l (insert x r))"

fun delete_max where
"delete_max (MKT n l ET h) = (n,l)" |
"delete_max (MKT n l r h) = (
  let (n',r') = delete_max r in
  (n',mkt_bal_l n l r'))"

lemmas delete_max_induct = delete_max.induct[case_names ET MKT]

fun delete_root where
"delete_root (MKT n ET r h) = r" |
"delete_root (MKT n l ET h) = l" |
"delete_root (MKT n l r h) =  
  (let (new_n, l') = delete_max l in
      mkt_bal_r new_n l' r
  )"

lemmas delete_root_cases = delete_root.cases[case_names ET_t MKT_ET MKT_MKT]

primrec delete :: "'a::order \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"delete _ ET = ET" |
"delete x (MKT n l r h) = (
   if x = n then delete_root (MKT n l r h)
   else if x < n then 
        let l' = delete x l in
        mkt_bal_r n l' r
   else 
        let r' = delete x r in
        mkt_bal_l n l r'
   )"

subsection \<open>Correctness proof\<close>

subsubsection \<open>Insertion maintains AVL balance\<close>

declare Let_def [simp]

lemma [simp]: "avl t \<Longrightarrow> ht t = height t"
by (induct t) simp_all

lemma height_mkt_bal_l:
  "\<lbrakk> height l = height r + 2; avl l; avl r \<rbrakk> \<Longrightarrow>
   height (mkt_bal_l n l r) = height r + 2 \<or>
   height (mkt_bal_l n l r) = height r + 3"
by (cases l) (auto simp:mkt_def split:tree.split)
       
lemma height_mkt_bal_r:
  "\<lbrakk> height r = height l + 2; avl l; avl r \<rbrakk> \<Longrightarrow>
   height (mkt_bal_r n l r) = height l + 2 \<or>
   height (mkt_bal_r n l r) = height l + 3"
by (cases r) (auto simp add:mkt_def split:tree.split)

lemma [simp]: "height(mkt x l r) = max (height l) (height r) + 1"
by (simp add: mkt_def)

lemma avl_mkt:
  "\<lbrakk> avl l; avl r;
     height l = height r \<or> height l = height r + 1 \<or> height r = height l + 1
   \<rbrakk> \<Longrightarrow> avl(mkt x l r)"
by (auto simp add:max_def mkt_def)

lemma height_mkt_bal_l2:
  "\<lbrakk> avl l; avl r; height l \<noteq> height r + 2 \<rbrakk> \<Longrightarrow>
   height (mkt_bal_l n l r) = (1 + max (height l) (height r))"
by (cases l, cases r) simp_all

lemma height_mkt_bal_r2:
  "\<lbrakk> avl l;  avl r;  height r \<noteq> height l + 2 \<rbrakk> \<Longrightarrow>
   height (mkt_bal_r n l r) = (1 + max (height l) (height r))"
by (cases l, cases r) simp_all

lemma avl_mkt_bal_l: 
  assumes "avl l" "avl r" and "height l = height r \<or> height l = height r + 1
    \<or> height r = height l + 1 \<or> height l = height r + 2" 
  shows "avl(mkt_bal_l n l r)"
proof(cases l)
  case ET
  with assms show ?thesis by (simp add: mkt_def)
next
  case (MKT ln ll lr lh)
  with assms show ?thesis
  proof(cases "height l = height r + 2")
    case True
      from True MKT assms show ?thesis by (auto intro!: avl_mkt split: tree.split) arith+
  next
    case False
      with assms show ?thesis by (simp add: avl_mkt)
  qed
qed

lemma avl_mkt_bal_r: 
  assumes "avl l" and "avl r" and "height l = height r \<or> height l = height r + 1
    \<or> height r = height l + 1 \<or> height r = height l + 2" 
  shows "avl(mkt_bal_r n l r)"
proof(cases r)
  case ET
  with assms show ?thesis by (simp add: mkt_def)
next
  case (MKT rn rl rr rh)
  with assms show ?thesis
  proof(cases "height r = height l + 2")
    case True
      from True MKT assms show ?thesis by (auto intro!: avl_mkt split: tree.split) arith+
  next
    case False
      with assms show ?thesis by (simp add: avl_mkt)
  qed
qed

(* It apppears that these two properties need to be proved simultaneously: *)

text\<open>Insertion maintains the AVL property:\<close>

theorem avl_insert_aux:
  assumes "avl t"
  shows "avl(insert x t)"
        "(height (insert x t) = height t \<or> height (insert x t) = height t + 1)"
using assms
proof (induction t)
  case (MKT n l r h)
  case 1
  with MKT show ?case
  proof(cases "x = n")
    case True
    with MKT 1 show ?thesis by simp
  next
    case False
    with MKT 1 show ?thesis 
    proof(cases "x<n")
      case True
      with MKT 1 show ?thesis by (auto simp add:avl_mkt_bal_l simp del:mkt_bal_l.simps)
    next
      case False
      with MKT 1 \<open>x\<noteq>n\<close> show ?thesis by (auto simp add:avl_mkt_bal_r simp del:mkt_bal_r.simps)
    qed
  qed
  case 2
  from 2 MKT show ?case
  proof(cases "x = n")
    case True
    with MKT 1 show ?thesis by simp
  next
    case False
    with MKT 1 show ?thesis 
     proof(cases "x<n")
      case True
      with MKT 2 show ?thesis
      proof(cases "height (AVL.insert x l) = height r + 2")
        case False with MKT 2 \<open>x < n\<close> show ?thesis by (auto simp del: mkt_bal_l.simps simp: height_mkt_bal_l2)
      next
        case True 
        then consider (a) "height (mkt_bal_l n (AVL.insert x l) r) = height r + 2"
          | (b) "height (mkt_bal_l n (AVL.insert x l) r) = height r + 3" 
          using MKT 2 by (atomize_elim, intro height_mkt_bal_l) simp_all
        then show ?thesis
        proof cases
          case a
          with 2 \<open>x < n\<close> show ?thesis by (auto simp del: mkt_bal_l.simps)
        next
          case b
          with True 1 MKT(2) \<open>x < n\<close> show ?thesis by (simp del: mkt_bal_l.simps) arith
        qed
      qed
    next
      case False
      with MKT 2 show ?thesis 
      proof(cases "height (AVL.insert x r) = height l + 2")
        case False with MKT 2 \<open>\<not>x < n\<close> show ?thesis by (auto simp del: mkt_bal_r.simps simp: height_mkt_bal_r2)
      next
        case True 
        then consider (a) "height (mkt_bal_r n l (AVL.insert x r)) = height l + 2"
          | (b) "height (mkt_bal_r n l (AVL.insert x r)) = height l + 3" 
          using MKT 2 by (atomize_elim, intro height_mkt_bal_r) simp_all
        then show ?thesis 
        proof cases
          case a
          with 2 \<open>\<not>x < n\<close> show ?thesis by (auto simp del: mkt_bal_r.simps)
        next
          case b
          with True 1 MKT(4) \<open>\<not>x < n\<close> show ?thesis by (simp del: mkt_bal_r.simps) arith
        qed
      qed
    qed
  qed
qed simp_all

lemmas avl_insert = avl_insert_aux(1)

subsubsection \<open>Deletion maintains AVL balance\<close>

lemma avl_delete_max:
  assumes "avl x" and "x \<noteq> ET"
  shows "avl (snd (delete_max x))" "height x = height(snd (delete_max x)) \<or>
         height x = height(snd (delete_max x)) + 1"
using assms
proof (induct x rule: delete_max_induct)
  case (MKT n l rn rl rr rh h)
  case 1
  with MKT have "avl l" "avl (snd (delete_max (MKT rn rl rr rh)))" by auto
  with 1 MKT have "avl (mkt_bal_l n l (snd (delete_max (MKT rn rl rr rh))))"
    by (intro avl_mkt_bal_l) fastforce+
  then show ?case 
    by (auto simp: height_mkt_bal_l height_mkt_bal_l2
      linorder_class.max.absorb1 linorder_class.max.absorb2
      split:prod.split simp del:mkt_bal_l.simps)
next
  case (MKT n l rn rl rr rh h)
  case 2
  let ?r = "MKT rn rl rr rh"
  let ?r' = "snd (delete_max ?r)"
  from \<open>avl x\<close> MKT 2 have "avl l" and "avl ?r" by simp_all
  then show ?case using MKT 2 height_mkt_bal_l[of l ?r' n] height_mkt_bal_l2[of l ?r' n]
    apply (auto split:prod.splits simp del:avl.simps mkt_bal_l.simps) by arith+
qed auto

lemma avl_delete_root:
  assumes "avl t" and "t \<noteq> ET"
  shows "avl(delete_root t)" 
using assms
proof (cases t rule:delete_root_cases)
  case (MKT_MKT n ln ll lr lh rn rl rr rh h) 
  let ?l = "MKT ln ll lr lh"
  let ?r = "MKT rn rl rr rh"
  let ?l' = "snd (delete_max ?l)"
  from \<open>avl t\<close> and MKT_MKT have "avl ?r" by simp
  from \<open>avl t\<close> and MKT_MKT have "avl ?l" by simp
  then have "avl(?l')" "height ?l = height(?l') \<or>
         height ?l = height(?l') + 1" by (rule avl_delete_max,simp)+
  with \<open>avl t\<close> MKT_MKT have "height ?l' = height ?r \<or> height ?l' = height ?r + 1
            \<or> height ?r = height ?l' + 1 \<or> height ?r = height ?l' + 2" by fastforce
  with \<open>avl ?l'\<close> \<open>avl ?r\<close> have "avl(mkt_bal_r (fst(delete_max ?l)) ?l' ?r)"
    by (rule avl_mkt_bal_r)
  with MKT_MKT show ?thesis by (auto split:prod.splits simp del:mkt_bal_r.simps)
qed simp_all

lemma height_delete_root:
  assumes "avl t" and "t \<noteq> ET" 
  shows "height t = height(delete_root t) \<or> height t = height(delete_root t) + 1"
using assms
proof (cases t rule: delete_root_cases)
  case (MKT_MKT n ln ll lr lh rn rl rr rh h) 
  let ?l = "MKT ln ll lr lh"
  let ?r = "MKT rn rl rr rh"
  let ?l' = "snd (delete_max ?l)"
  let ?t' = "mkt_bal_r (fst(delete_max ?l)) ?l' ?r"
  from \<open>avl t\<close> and MKT_MKT have "avl ?r" by simp
  from \<open>avl t\<close> and MKT_MKT have "avl ?l" by simp
  then have "avl(?l')"  by (rule avl_delete_max,simp)
  have l'_height: "height ?l = height ?l' \<or> height ?l = height ?l' + 1" using \<open>avl ?l\<close> by (intro avl_delete_max) auto
  have t_height: "height t = 1 + max (height ?l) (height ?r)" using \<open>avl t\<close> MKT_MKT by simp
  have "height t = height ?t' \<or> height t = height ?t' + 1" using  \<open>avl t\<close> MKT_MKT
  proof(cases "height ?r = height ?l' + 2")
    case False
    show ?thesis using l'_height t_height False by (subst  height_mkt_bal_r2[OF \<open>avl ?l'\<close> \<open>avl ?r\<close> False])+ arith
  next
    case True
    show ?thesis
    proof(cases rule: disjE[OF height_mkt_bal_r[OF True \<open>avl ?l'\<close> \<open>avl ?r\<close>, of "fst (delete_max ?l)"]])
      case 1
      then show ?thesis using l'_height t_height True by arith
    next
      case 2
      then show ?thesis using l'_height t_height True by arith
    qed
  qed
  thus ?thesis using MKT_MKT by (auto split:prod.splits simp del:mkt_bal_r.simps)
qed simp_all

text\<open>Deletion maintains the AVL property:\<close>

theorem avl_delete_aux:
  assumes "avl t" 
  shows "avl(delete x t)" and "height t = (height (delete x t)) \<or> height t = height (delete x t) + 1"
using assms
proof (induct t)
  case (MKT n l r h)
  case 1
  with MKT show ?case
  proof(cases "x = n")
    case True
    with MKT 1 show ?thesis by (auto simp:avl_delete_root)
  next
    case False
    with MKT 1 show ?thesis 
    proof(cases "x<n")
      case True
      with MKT 1 show ?thesis by (auto simp add:avl_mkt_bal_r simp del:mkt_bal_r.simps)
    next
      case False
      with MKT 1 \<open>x\<noteq>n\<close> show ?thesis by (auto simp add:avl_mkt_bal_l simp del:mkt_bal_l.simps)
    qed
  qed
  case 2
  with MKT show ?case
  proof(cases "x = n")
    case True
    with 1 have "height (MKT n l r h) = height(delete_root (MKT n l r h))
      \<or> height (MKT n l r h) = height(delete_root (MKT n l r h)) + 1"
      by (subst height_delete_root,simp_all)
    with True show ?thesis by simp
  next
    case False
    with MKT 1 show ?thesis 
     proof(cases "x<n")
      case True
      show ?thesis
      proof(cases "height r = height (delete x l) + 2")
        case False with MKT 1 \<open>x < n\<close> show ?thesis by auto
      next
        case True 
        then consider (a) "height (mkt_bal_r n (delete x l) r) = height (delete x l) + 2"
          | (b) "height (mkt_bal_r n (delete x l) r) = height (delete x l) + 3"
          using MKT 2 by (atomize_elim, intro height_mkt_bal_r) auto
        then show ?thesis 
        proof cases
          case a
          with \<open>x < n\<close> MKT 2 show ?thesis by auto
        next
          case b
          with \<open>x < n\<close> MKT 2 show ?thesis by auto
        qed
      qed
    next
      case False
      show ?thesis
      proof(cases "height l = height (delete x r) + 2")
        case False with MKT 1 \<open>\<not>x < n\<close> \<open>x \<noteq> n\<close> show ?thesis by auto
      next
        case True 
        then consider (a) "height (mkt_bal_l n l (delete x r)) = height (delete x r) + 2"
          | (b) "height (mkt_bal_l n l (delete x r)) = height (delete x r) + 3" 
          using MKT 2 by (atomize_elim, intro height_mkt_bal_l) auto
        then show ?thesis 
        proof cases
          case a
          with \<open>\<not>x < n\<close> \<open>x \<noteq> n\<close> MKT 2 show ?thesis by auto
        next
          case b
          with \<open>\<not>x < n\<close> \<open>x \<noteq> n\<close> MKT 2 show ?thesis by auto
        qed
      qed
    qed
  qed
qed simp_all

lemmas avl_delete = avl_delete_aux(1)


subsubsection \<open>Correctness of insertion\<close>

lemma set_of_mkt_bal_l:
  "\<lbrakk> avl l; avl r \<rbrakk> \<Longrightarrow>
  set_of (mkt_bal_l n l r) = Set.insert n (set_of l \<union> set_of r)"
by (auto simp: mkt_def split:tree.splits)

lemma set_of_mkt_bal_r:
  "\<lbrakk> avl l; avl r \<rbrakk> \<Longrightarrow>
  set_of (mkt_bal_r n l r) = Set.insert n (set_of l \<union> set_of r)"
by (auto simp: mkt_def split:tree.splits)

text\<open>Correctness of @{const insert}:\<close>

theorem set_of_insert:
  "avl t \<Longrightarrow> set_of(insert x t) = Set.insert x (set_of t)"
by (induct t) 
   (auto simp: avl_insert set_of_mkt_bal_l set_of_mkt_bal_r simp del:mkt_bal_l.simps mkt_bal_r.simps)

subsubsection \<open>Correctness of deletion\<close>

fun rightmost_item :: "'a tree \<Rightarrow> 'a" where
"rightmost_item (MKT n l ET h) = n" |
"rightmost_item (MKT n l r h) = rightmost_item r"

lemma avl_dist:
  "\<lbrakk> avl(MKT n l r h); is_ord(MKT n l r h); x \<in> set_of l \<rbrakk> \<Longrightarrow>
  x \<notin> set_of r"
by fastforce

lemma avl_dist2:
  "\<lbrakk> avl(MKT n l r h); is_ord(MKT n l r h); x \<in> set_of l \<or> x \<in> set_of r \<rbrakk> \<Longrightarrow>
  x \<noteq> n"
by auto

lemma ritem_in_rset: "r \<noteq> ET \<Longrightarrow> rightmost_item r \<in> set_of r"
by(induct r rule:rightmost_item.induct) auto

lemma ritem_greatest_in_rset:
  "\<lbrakk> r \<noteq> ET; is_ord r \<rbrakk> \<Longrightarrow>
  \<forall>x.  x \<in> set_of r \<longrightarrow> x \<noteq> rightmost_item r \<longrightarrow> x < rightmost_item r" 
proof(induct r rule:rightmost_item.induct)
  case (2 n l rn rl rr rh h)
  show ?case (is "\<forall>x. ?P x") 
  proof
    fix x
    from 2 have "is_ord (MKT rn rl rr rh)" by auto
    moreover from 2 have "n < rightmost_item (MKT rn rl rr rh)" 
      by (metis is_ord.simps(2) ritem_in_rset tree.simps(2))
    moreover from 2 have "x \<in> set_of l \<longrightarrow> x < rightmost_item (MKT rn rl rr rh)"
      by (metis calculation(2) is_ord.simps(2) xt1(10))
    ultimately show "?P x" using 2 by simp
  qed
qed auto

lemma ritem_not_in_ltree:
  "\<lbrakk> avl(MKT n l r h); is_ord(MKT n l r h); r \<noteq> ET \<rbrakk> \<Longrightarrow>
  rightmost_item r \<notin> set_of l"
by (metis avl_dist ritem_in_rset)

lemma set_of_delete_max:
  "\<lbrakk> avl t; is_ord t; t\<noteq>ET \<rbrakk> \<Longrightarrow>
   set_of (snd(delete_max t)) = (set_of t) - {rightmost_item t}"
proof (induct t rule: delete_max_induct)
  case (MKT n l rn rl rr rh h)
  let ?r = "MKT rn rl rr rh"
  from MKT have "avl l" and "avl ?r" by simp_all
  let ?t' = "mkt_bal_l n l (snd (delete_max ?r))"
  from MKT have "avl (snd(delete_max ?r))" by (auto simp add: avl_delete_max)
  with MKT ritem_not_in_ltree[of n l ?r h]
  have "set_of ?t' = (set_of l) \<union> (set_of ?r) - {rightmost_item ?r} \<union> {n}" 
    by (auto simp add:set_of_mkt_bal_l simp del: mkt_bal_l.simps)
  moreover have "n \<notin> {rightmost_item ?r}" 
    by (metis MKT(2) MKT(3) avl_dist2 ritem_in_rset singletonE tree.simps(3))
  ultimately show ?case
    by (auto simp add:insert_Diff_if split:prod.splits simp del: mkt_bal_l.simps) 
qed auto

lemma fst_delete_max_eq_ritem:
  "t\<noteq>ET \<Longrightarrow> fst(delete_max t) = rightmost_item t"
by (induct t rule:rightmost_item.induct) (auto split:prod.splits)

lemma set_of_delete_root:
  assumes "t = MKT n l r h" and "avl t" and "is_ord t"
  shows "set_of (delete_root t) = (set_of t) - {n}"
using assms
proof(cases t rule:delete_root_cases)
  case(MKT_MKT n ln ll lr lh rn rl rr rh h)
  let ?t' = "mkt_bal_r (fst (delete_max l)) (snd (delete_max l)) r"
  from assms MKT_MKT have "avl l" and "avl r" and "is_ord l" and "l\<noteq>ET" by auto
  moreover from MKT_MKT assms have "avl (snd(delete_max l))" 
    by (auto simp add: avl_delete_max)
  ultimately have "set_of ?t' = (set_of l) \<union> (set_of r)"
    by (fastforce simp add: Set.insert_Diff ritem_in_rset fst_delete_max_eq_ritem  
       set_of_delete_max set_of_mkt_bal_r  simp del: mkt_bal_r.simps)
  moreover from MKT_MKT assms(1) have "set_of (delete_root t) = set_of ?t'" 
    by (simp split:prod.split del:mkt_bal_r.simps)
  moreover from MKT_MKT assms have "(set_of t) - {n} = set_of l \<union> set_of r" 
    by (metis Diff_insert_absorb UnE avl_dist2 tree.set(2) tree.inject)
  ultimately show ?thesis using MKT_MKT assms(1)
    by (simp del: delete_root.simps)
qed auto

text\<open>Correctness of @{const delete}:\<close>

theorem set_of_delete:
  "\<lbrakk> avl t; is_ord t \<rbrakk> \<Longrightarrow> set_of (delete x t) = (set_of t) - {x}"
proof (induct t)
  case (MKT n l r h)
  then show ?case
  proof(cases "x = n")
    case True
    with MKT set_of_delete_root[of "MKT n l r h"] show ?thesis by simp
  next
    case False
    with MKT show ?thesis 
    proof(cases "x<n")
      case True
      with True MKT  show ?thesis 
        by (force simp: avl_delete set_of_mkt_bal_r[of "(delete x l)" r n] simp del:mkt_bal_r.simps)
    next
      case False
      with False MKT \<open>x\<noteq>n\<close> show ?thesis 
        by (force simp: avl_delete set_of_mkt_bal_l[of l "(delete x r)" n] simp del:mkt_bal_l.simps)
    qed
 qed
qed simp

subsubsection \<open>Correctness of lookup\<close>

theorem is_in_correct: "is_ord t \<Longrightarrow> is_in k t = (k : set_of t)"
by (induct t) auto

subsubsection \<open>Insertion maintains order\<close>

lemma is_ord_mkt_bal_l:
  "is_ord(MKT n l r h) \<Longrightarrow> is_ord (mkt_bal_l n l r)"
by (cases l) (auto simp: mkt_def split:tree.splits intro: order_less_trans)

lemma is_ord_mkt_bal_r: "is_ord(MKT n l r h) \<Longrightarrow> is_ord (mkt_bal_r n l r)"
by (cases r) (auto simp: mkt_def split:tree.splits intro: order_less_trans)

text\<open>If the order is linear, @{const insert} maintains the order:\<close>

theorem is_ord_insert:
  "\<lbrakk> avl t; is_ord t \<rbrakk> \<Longrightarrow> is_ord(insert (x::'a::linorder) t)"
by (induct t) (simp_all add:is_ord_mkt_bal_l is_ord_mkt_bal_r avl_insert set_of_insert
                linorder_not_less order_neq_le_trans del:mkt_bal_l.simps mkt_bal_r.simps)

subsubsection \<open>Deletion maintains order\<close>

lemma is_ord_delete_max:
  "\<lbrakk> avl t; is_ord t; t\<noteq>ET \<rbrakk> \<Longrightarrow> is_ord(snd(delete_max t))"
proof(induct t rule:delete_max_induct)
  case(MKT n l rn rl rr rh h)
  let ?r = "MKT rn rl rr rh"
  let ?r' = "snd(delete_max ?r)"
  from MKT have "\<forall>h. is_ord(MKT n l ?r' h)" by (auto simp: set_of_delete_max)
  moreover from MKT have "avl(?r')" by (auto simp: avl_delete_max)
  moreover note MKT is_ord_mkt_bal_l[of n l ?r']
  ultimately show ?case by (auto split:prod.splits simp del:is_ord.simps mkt_bal_l.simps)
qed auto

lemma is_ord_delete_root:
  assumes "avl t" and "is_ord t" and "t \<noteq> ET"
  shows "is_ord (delete_root t)"
using assms
proof(cases t rule:delete_root_cases)
  case(MKT_MKT n ln ll lr lh rn rl rr rh h)
  let ?l = "MKT ln ll lr lh"
  let ?r = "MKT rn rl rr rh"
  let ?l' = "snd (delete_max ?l)"
  let ?n' = "fst (delete_max ?l)"
  from assms MKT_MKT have "\<forall>h. is_ord(MKT ?n' ?l' ?r h)" 
  proof -
    from assms MKT_MKT have "is_ord ?l'" by (auto simp add: is_ord_delete_max)
    moreover from assms MKT_MKT have "is_ord ?r" by auto
    moreover from assms MKT_MKT have "\<forall>x. x \<in> set_of ?r \<longrightarrow> ?n' < x" 
      by (metis fst_delete_max_eq_ritem is_ord.simps(2) order_less_trans ritem_in_rset 
          tree.simps(3))
    moreover from assms MKT_MKT ritem_greatest_in_rset have "\<forall>x. x \<in> set_of ?l' \<longrightarrow> x < ?n'" 
      by (metis Diff_iff avl.simps(2) fst_delete_max_eq_ritem is_ord.simps(2) 
          set_of_delete_max singleton_iff tree.simps(3))
    ultimately show ?thesis by auto
  qed
  moreover from assms MKT_MKT have "avl ?r" by simp
  moreover from assms MKT_MKT have "avl ?l'"  by (simp add: avl_delete_max)
  moreover note MKT_MKT is_ord_mkt_bal_r[of  ?n' ?l' ?r]
  ultimately show ?thesis by (auto simp del:mkt_bal_r.simps is_ord.simps split:prod.splits)
qed simp_all

text\<open>If the order is linear, @{const delete} maintains the order:\<close>

theorem is_ord_delete:
  "\<lbrakk> avl t; is_ord t \<rbrakk> \<Longrightarrow> is_ord (delete x t)"
proof (induct t)
  case (MKT n l r h)
  then show ?case
  proof(cases "x = n")
    case True
    with MKT is_ord_delete_root[of "MKT n l r h"] show ?thesis by simp
  next
    case False
    with MKT show ?thesis 
    proof(cases "x<n")
      case True
      with True MKT have "\<forall>h. is_ord (MKT n (delete x l) r h)" by (auto simp:set_of_delete)
      with True MKT is_ord_mkt_bal_r[of n "(delete x l)" r]  show ?thesis 
        by (auto simp add: avl_delete)
    next
      case False
      with False MKT have "\<forall>h. is_ord (MKT n l (delete x r) h)" by (auto simp:set_of_delete)
      with False MKT is_ord_mkt_bal_l[of n l "(delete x r)"] \<open>x\<noteq>n\<close> show ?thesis by (simp add: avl_delete)
    qed
  qed
qed simp

end
