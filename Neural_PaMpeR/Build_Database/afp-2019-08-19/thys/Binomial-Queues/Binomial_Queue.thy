(* Authors:  René Neumann and Florian Haftmann, TU Muenchen *)

section \<open>Functional Binomial Queues\<close>

theory Binomial_Queue
imports PQ
begin

subsection \<open>Type definition and projections\<close>

datatype ('a, 'b) bintree = Node "'a" "'b" "('a, 'b) bintree list"

primrec priority :: "('a, 'b) bintree \<Rightarrow> 'a" where
  "priority (Node a _ _) = a"

primrec val :: "('a, 'b) bintree \<Rightarrow> 'b" where
  "val (Node _ v _) = v"

primrec children :: "('a, 'b) bintree \<Rightarrow> ('a, 'b) bintree list" where
  "children (Node _ _ ts) = ts"

type_synonym ('a, 'b) binqueue = "('a, 'b) bintree option list"

lemma binqueue_induct [case_names Empty None Some, induct type: binqueue]:
  assumes "P []"
    and "\<And>xs. P xs \<Longrightarrow> P (None # xs)"
    and "\<And>x xs. P xs \<Longrightarrow> P (Some x # xs)"
  shows "P xs"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases x) simp_all
qed

text \<open>
  \noindent Terminology:

  \begin{itemize}

    \item values \<open>v, w\<close> or \<open>v1, v2\<close>

    \item priorities \<open>a, b\<close> or \<open>a1, a2\<close>

    \item bintrees \<open>t, r\<close> or \<open>t1, t2\<close>

    \item bintree lists \<open>ts, rs\<close> or \<open>ts1, ts2\<close>

    \item binqueue element \<open>x, y\<close> or \<open>x1, x2\<close>

    \item binqueues = binqueue element lists \<open>xs, ys\<close> or \<open>xs1, xs2\<close>

    \item abstract priority queues \<open>q, p\<close> or \<open>q1, q2\<close>

  \end{itemize}
\<close>


subsection \<open>Binomial queue properties\<close>

subsubsection \<open>Binomial tree property\<close>

inductive is_bintree_list :: "nat \<Rightarrow> ('a, 'b) bintree list \<Rightarrow> bool" where
  is_bintree_list_Nil [simp]: "is_bintree_list 0 []"
| is_bintree_list_Cons: "is_bintree_list l ts \<Longrightarrow> is_bintree_list l (children t)
    \<Longrightarrow> is_bintree_list (Suc l) (t # ts)"

abbreviation (input) "is_bintree k t \<equiv> is_bintree_list k (children t)"

lemma is_bintree_list_triv [simp]:
  "is_bintree_list 0 ts \<longleftrightarrow> ts = []"
  "is_bintree_list l [] \<longleftrightarrow> l = 0"
  by (auto intro: is_bintree_list.intros elim: is_bintree_list.cases)

lemma is_bintree_list_simp [simp]:
  "is_bintree_list (Suc l) (t # ts) \<longleftrightarrow>
    is_bintree_list l (children t) \<and> is_bintree_list l ts"
  by (auto intro: is_bintree_list.intros elim: is_bintree_list.cases)

lemma is_bintree_list_length [simp]:
  "is_bintree_list l ts \<Longrightarrow> length ts = l"
  by (erule is_bintree_list.induct) simp_all

lemma is_bintree_list_children_last:
  assumes "is_bintree_list l ts" and "ts \<noteq> []"
  shows "children (last ts) = []"
  using assms by induct auto

lemma is_bintree_children_length_desc:
  assumes "is_bintree_list l ts"
  shows "map (length \<circ> children) ts = rev [0..<l]"
  using assms by (induct ts) simp_all


subsubsection \<open>Heap property\<close>

inductive is_heap_list :: "'a::linorder \<Rightarrow> ('a, 'b) bintree list \<Rightarrow> bool" where
  is_heap_list_Nil: "is_heap_list h []"
| is_heap_list_Cons: "is_heap_list h ts \<Longrightarrow> is_heap_list (priority t) (children t)
    \<Longrightarrow> (priority t) \<ge> h \<Longrightarrow> is_heap_list h (t # ts)"

abbreviation (input) "is_heap t \<equiv> is_heap_list (priority t) (children t)"

lemma is_heap_list_simps [simp]:
  "is_heap_list h [] \<longleftrightarrow> True"
  "is_heap_list h (t # ts) \<longleftrightarrow>
    is_heap_list h ts \<and> is_heap_list (priority t) (children t) \<and> priority t \<ge> h"
  by (auto intro: is_heap_list.intros elim: is_heap_list.cases)

lemma is_heap_list_append_dest [dest]:
  "is_heap_list l (ts@rs) \<Longrightarrow> is_heap_list l ts"
  "is_heap_list l (ts@rs) \<Longrightarrow> is_heap_list l rs"
  by (induct ts) (auto intro: is_heap_list.intros elim: is_heap_list.cases)

lemma is_heap_list_rev:
  "is_heap_list l ts \<Longrightarrow> is_heap_list l (rev ts)"
  by (induct ts rule: rev_induct) auto

lemma is_heap_children_larger:
  "is_heap t \<Longrightarrow> \<forall> x \<in> set (children t). priority x \<ge> priority t"
  by (erule is_heap_list.induct) simp_all

lemma is_heap_Min_children_larger:
  "is_heap t \<Longrightarrow> children t \<noteq> [] \<Longrightarrow> 
   priority t \<le> Min (priority ` set (children t))"
  by (simp add: is_heap_children_larger)


subsubsection \<open>Combination of both: binqueue property\<close>

inductive is_binqueue :: "nat \<Rightarrow> ('a::linorder, 'b) binqueue \<Rightarrow> bool" where
  Empty: "is_binqueue l []"
| None: "is_binqueue (Suc l) xs \<Longrightarrow> is_binqueue l (None # xs)"
| Some: "is_binqueue (Suc l) xs \<Longrightarrow> is_bintree l t
    \<Longrightarrow> is_heap t \<Longrightarrow> is_binqueue l (Some t # xs)"

lemma is_binqueue_simp [simp]:
  "is_binqueue l [] \<longleftrightarrow> True"
  "is_binqueue l (Some t # xs) \<longleftrightarrow>
    is_bintree l t \<and> is_heap t \<and> is_binqueue (Suc l) xs"
  "is_binqueue l (None # xs) \<longleftrightarrow> is_binqueue (Suc l) xs"
  by (auto intro: is_binqueue.intros elim: is_binqueue.cases)

lemma is_binqueue_trans:
  "is_binqueue l (x#xs) \<Longrightarrow> is_binqueue (Suc l) xs"
  by (cases x) simp_all

lemma is_binqueue_head:
  "is_binqueue l (x#xs) \<Longrightarrow> is_binqueue l [x]"
  by (cases x) simp_all

lemma is_binqueue_append:
  "is_binqueue l xs \<Longrightarrow> is_binqueue (length xs + l) ys \<Longrightarrow> is_binqueue l (xs @ ys)"
  by (induct xs arbitrary: l) (auto intro: is_binqueue.intros elim: is_binqueue.cases)

lemma is_binqueue_append_dest [dest]:
  "is_binqueue l (xs @ ys) \<Longrightarrow> is_binqueue l xs"
  by (induct xs arbitrary: l) (auto intro: is_binqueue.intros elim: is_binqueue.cases)

lemma is_binqueue_children:
  assumes "is_bintree_list l ts"
  and "is_heap_list t ts"
  shows "is_binqueue 0 (map Some (rev ts))"
  using assms by (induct ts) (auto simp add: is_binqueue_append)

lemma is_binqueue_select:
  "is_binqueue l xs \<Longrightarrow> Some t \<in> set xs \<Longrightarrow> \<exists>k. is_bintree k t \<and> is_heap t"
  by (induct xs arbitrary: l) (auto intro: is_binqueue.intros elim: is_binqueue.cases)


subsubsection \<open>Normalized representation\<close>

inductive normalized :: "('a, 'b) binqueue \<Rightarrow> bool" where
  normalized_Nil: "normalized []"
| normalized_single: "normalized [Some t]"
| normalized_append: "xs \<noteq> [] \<Longrightarrow> normalized xs \<Longrightarrow> normalized (ys @ xs)"

lemma normalized_last_not_None:
  \<comment> \<open>\ sometimes the inductive definition might work better\<close>
  "normalized xs \<longleftrightarrow> xs = [] \<or> last xs \<noteq> None"
proof
  assume "normalized xs"
  then show "xs = [] \<or> last xs \<noteq> None"
    by (rule normalized.induct) simp_all
next
  assume *: "xs = [] \<or> last xs \<noteq> None"
  show "normalized xs" proof (cases xs rule: rev_cases)
    case Nil then show ?thesis by (simp add: normalized.intros)
  next
    case (snoc ys x) with * obtain t where "last xs = Some t" by auto
    with snoc have "xs = ys @ [Some t]" by simp
    then show ?thesis by (simp add: normalized.intros)
  qed
qed

lemma normalized_simps [simp]:
  "normalized [] \<longleftrightarrow> True"
  "normalized (Some t # xs) \<longleftrightarrow> normalized xs"
  "normalized (None # xs) \<longleftrightarrow> xs \<noteq> [] \<and> normalized xs"
  by (simp_all add: normalized_last_not_None)

lemma normalized_map_Some [simp]:
  "normalized (map Some xs)"
  by (induct xs) simp_all

lemma normalized_Cons:
  "normalized (x#xs) \<Longrightarrow> normalized xs"
  by (auto simp add: normalized_last_not_None)

lemma normalized_append:
  "normalized xs \<Longrightarrow> normalized ys \<Longrightarrow> normalized (xs@ys)"
  by (cases ys) (simp_all add: normalized_last_not_None)

lemma normalized_not_None:
  "normalized xs \<Longrightarrow> set xs \<noteq> {None}"
  by (induct xs) (auto simp add: normalized_Cons [of _ ts] dest: subset_singletonD) 

primrec normalize' :: "('a, 'b) binqueue \<Rightarrow> ('a, 'b) binqueue" where
  "normalize' [] = []"
| "normalize' (x # xs) =
    (case x of None \<Rightarrow> normalize' xs | Some t \<Rightarrow> (x # xs))"

definition normalize :: "('a, 'b) binqueue \<Rightarrow> ('a, 'b) binqueue" where
  "normalize xs = rev (normalize' (rev xs))"

lemma normalized_normalize:
  "normalized (normalize xs)"
proof (induct xs rule: rev_induct)
  case (snoc y ys) then show ?case 
    by (cases y) (simp_all add: normalized_last_not_None normalize_def)
qed (simp add: normalize_def)

lemma is_binqueue_normalize:
  "is_binqueue l xs \<Longrightarrow> is_binqueue l (normalize xs)"
  unfolding normalize_def
    by (induct xs arbitrary: l rule: rev_induct) (auto split: option.split)


subsection \<open>Operations\<close>

subsubsection \<open>Adding data\<close>

definition merge :: "('a::linorder, 'b) bintree \<Rightarrow> ('a, 'b) bintree \<Rightarrow> ('a, 'b) bintree" where
  "merge t1 t2 = (if priority t1 < priority t2
    then Node (priority t1) (val t1) (t2 # children t1) 
    else Node (priority t2) (val t2) (t1 # children t2))"

lemma is_bintree_list_merge:
  assumes "is_bintree l t1" "is_bintree l t2"
  shows "is_bintree (Suc l) (merge t1 t2)"
  using assms by (simp add: merge_def)

lemma is_heap_merge:
  assumes "is_heap t1" "is_heap t2"
  shows "is_heap (merge t1 t2)"
  using assms by (auto simp add: merge_def)

fun
  add :: "('a::linorder, 'b) bintree option \<Rightarrow> ('a, 'b) binqueue \<Rightarrow> ('a, 'b) binqueue"
where
  "add None xs = xs"
| "add (Some t) [] = [Some t]"
| "add (Some t) (None # xs) = Some t # xs"
| "add (Some t) (Some r # xs) = None # add (Some (merge t r)) xs"

lemma add_Some_not_Nil [simp]:
  "add (Some t) xs \<noteq> []"
  by (induct "Some t" xs rule: add.induct) simp_all

lemma normalized_add:
  assumes "normalized xs"
  shows "normalized (add x xs)"
  using assms by (induct xs rule: add.induct) simp_all

lemma is_binqueue_add_None:
  assumes "is_binqueue l xs"
  shows "is_binqueue l (add None xs)"
  using assms by simp

lemma is_binqueue_add_Some:
  assumes "is_binqueue l xs"
  and     "is_bintree l t"
  and     "is_heap t"
  shows "is_binqueue l (add (Some t) xs)"
  using assms by (induct xs arbitrary: t) (simp_all add: is_bintree_list_merge is_heap_merge)

function
  meld :: "('a::linorder, 'b) binqueue \<Rightarrow> ('a, 'b) binqueue \<Rightarrow> ('a, 'b) binqueue"
where
  "meld [] ys = ys"
| "meld xs [] = xs"
| "meld (None # xs) (y # ys) = y # meld xs ys"
| "meld (x # xs) (None # ys) = x # meld xs ys"
| "meld (Some t # xs) (Some r # ys) =
    None # add (Some (merge t r)) (meld xs ys)"
  by pat_completeness auto termination by lexicographic_order

lemma meld_singleton_add [simp]:
  "meld [Some t] xs = add (Some t) xs"
  by (induct "Some t" xs rule: add.induct) simp_all

lemma nonempty_meld [simp]:
  "xs \<noteq> [] \<Longrightarrow> meld xs ys \<noteq> []"
  "ys \<noteq> [] \<Longrightarrow> meld xs ys \<noteq> []"
  by (induct xs ys rule: meld.induct) auto

lemma nonempty_meld_commute:
  "meld xs ys \<noteq> [] \<Longrightarrow> meld xs ys \<noteq> []"
  by (induct xs ys rule: meld.induct) auto

lemma is_binqueue_meld:
  assumes "is_binqueue l xs"
  and     "is_binqueue l ys"
  shows "is_binqueue l (meld xs ys)"
using assms
proof (induct xs ys arbitrary: l rule: meld.induct)
  fix xs ys :: "('a, 'b) binqueue"
  fix y :: "('a, 'b) bintree option"
  fix l :: nat
  assume "\<And> l. is_binqueue l xs \<Longrightarrow> is_binqueue l ys
      \<Longrightarrow> is_binqueue l (meld xs ys)"
    and "is_binqueue l (None # xs)"
    and "is_binqueue l (y # ys)"
  then show "is_binqueue l (meld (None # xs) (y # ys))" by (cases y) simp_all
next
  fix xs ys :: "('a, 'b) binqueue"
  fix x :: "('a, 'b) bintree option"
  fix l :: nat
  assume "\<And> l. is_binqueue l xs \<Longrightarrow> is_binqueue l ys
      \<Longrightarrow> is_binqueue l (meld xs ys)"
    and "is_binqueue l (x # xs)"
    and "is_binqueue l (None # ys)"
  then show "is_binqueue l (meld (x # xs) (None # ys))" by (cases x) simp_all
qed (simp_all add: is_bintree_list_merge is_heap_merge is_binqueue_add_Some)

lemma normalized_meld:
  assumes "normalized xs"
  and     "normalized ys"
  shows   "normalized (meld xs ys)"
using assms
proof (induct xs ys rule: meld.induct)
  fix xs ys :: "('a, 'b) binqueue"
  fix y :: "('a, 'b) bintree option"
  assume "normalized xs \<Longrightarrow> normalized ys \<Longrightarrow> normalized (meld xs ys)"
    and  "normalized (None # xs)"
    and  "normalized (y # ys)"
  then show "normalized (meld (None # xs) (y # ys))" by (cases y) simp_all
next
  fix xs ys :: "('a, 'b) binqueue"
  fix x :: "('a, 'b) bintree option"
  assume "normalized xs \<Longrightarrow> normalized ys \<Longrightarrow> normalized (meld xs ys)"
    and  "normalized (x # xs)"
    and  "normalized (None # ys)"
  then show "normalized (meld (x # xs) (None # ys))" by (cases x) simp_all
qed (simp_all add: normalized_add)

lemma normalized_meld_weak:
  assumes "normalized xs"
  and "length ys \<le> length xs"
  shows "normalized (meld xs ys)"
using assms
proof (induct xs ys rule: meld.induct)
  fix xs ys :: "('a, 'b) binqueue"
  fix y :: "('a, 'b) bintree option"
  assume "normalized xs \<Longrightarrow> length ys \<le> length xs \<Longrightarrow> normalized (meld xs ys)"
    and  "normalized (None # xs)"
    and  "length (y # ys) \<le> length (None # xs)"
  then show "normalized (meld (None # xs) (y # ys))" by (cases y) simp_all
next
  fix xs ys :: "('a, 'b) binqueue"
  fix x :: "('a, 'b) bintree option"
  assume "normalized xs \<Longrightarrow> length ys \<le> length xs \<Longrightarrow> normalized (meld xs ys)"
    and  "normalized (x # xs)"
    and  "length (None # ys) \<le> length (x # xs)"
  then show "normalized (meld (x # xs) (None # ys))" by (cases x) simp_all
qed (simp_all add: normalized_add)

definition least :: "'a::linorder option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "least x y = (case x of
      None \<Rightarrow> y
    | Some x' \<Rightarrow> (case y of
           None \<Rightarrow> x
         | Some y' \<Rightarrow> if x' \<le> y' then x else y))"

lemma least_simps [simp, code]:
  "least None x = x"
  "least x None = x"
  "least (Some x') (Some y') = (if x' \<le> y' then Some x' else Some y')"
  unfolding least_def by (simp_all) (cases x, simp_all)

lemma least_split:
  assumes "least x y = Some z"
  shows "x = Some z \<or> y = Some z"
using assms proof (cases x)
  case (Some x') with assms show ?thesis by (cases y) (simp_all add: eq_commute)
qed simp

interpretation least: semilattice least proof
qed (auto simp add: least_def split: option.split)

definition min :: "('a::linorder, 'b) binqueue \<Rightarrow> 'a option" where
  "min xs = fold least (map (map_option priority) xs) None"

lemma min_simps [simp]:
  "min [] = None"
  "min (None # xs) = min xs"
  "min (Some t # xs) = least (Some (priority t)) (min xs)"
  by (simp_all add: min_def fold_commute_apply [symmetric]
    fun_eq_iff least.left_commute del: least_simps)

lemma [code]:
  "min xs = fold (\<lambda> x. least (map_option priority x)) xs None"
  by (simp add: min_def fold_map o_def)

lemma min_single:
  "min [x] = Some a \<Longrightarrow> priority (the x) = a"
  "min [x] = None \<Longrightarrow> x = None"
  by (auto simp add: min_def)

lemma min_Some_not_None:
  "min (Some t # xs) \<noteq> None"
  by (cases "min xs") simp_all

lemma min_None_trans:
  assumes "min (x#xs) = None"
  shows "min xs = None"
using assms proof (cases x)
  case None with assms show ?thesis by simp
next
  case (Some t) with assms show ?thesis by (simp only: min_Some_not_None)
qed

lemma min_None_None:
  "min xs = None \<longleftrightarrow> xs = [] \<or> set xs = {None}"
proof (rule iffI)
  have splitQ: "\<And> xs. xs \<subseteq> {None} \<Longrightarrow> xs = {} \<or> xs = {None}" by auto

  assume "min xs = None"
  then have "set xs \<subseteq> {None}"
  proof (induct xs)
    case (None ys) thus ?case using min_None_trans[of _ ys] by simp_all
  next
    case (Some t ys) thus ?case using min_Some_not_None[of t ys] by simp 
  qed simp
 
  with splitQ show "xs = [] \<or> set xs = {None}" by auto
next
  show "xs = [] \<or> set xs = {None} \<Longrightarrow> min xs = None"
    by (induct xs) (auto dest: subset_singletonD)
qed

lemma normalized_min_not_None:
  "normalized xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> min xs \<noteq> None"
  by (simp add: min_None_None normalized_not_None)

lemma min_is_min:
  assumes "normalized xs"
  and "xs \<noteq> []"
  and "min xs = Some a"
  shows "\<forall>x \<in> set xs. x = None \<or> a \<le> priority (the x)"
using assms proof (induct xs arbitrary: a rule: binqueue_induct)
  case (Some t ys) thus ?case
  proof (cases "ys = []")
    case False
    with Some have N: "normalized ys" using normalized_Cons[of _ ys] by simp
    with \<open>ys \<noteq> []\<close> have "min ys \<noteq> None"
      by (simp add: normalized_min_not_None)
    then obtain a' where oa': "min ys = Some a'" by auto
    with Some N False
      have "\<forall>y \<in> set ys. y = None \<or> a' \<le> priority (the y)" by simp

    with Some oa' show ?thesis
      by (cases "a' \<le> priority t") (auto simp add: least.commute)
  qed simp
qed simp_all

lemma min_exists:
  assumes "min xs = Some a"
  shows "Some a \<in> map_option priority ` set xs"
proof (rule ccontr)
  assume "Some a \<notin> map_option priority ` set xs"
  then have "\<forall>x \<in> set xs. x = None \<or> priority (the x) \<noteq> a" by (induct xs) auto
  then have "min xs \<noteq> Some a"  
  proof (induct xs arbitrary: a)
    case (Some t ys) 
    hence "priority t \<noteq> a" and "min ys \<noteq> Some a" by simp_all
    show ?case
    proof (rule ccontr, simp)
      assume "least (Some (priority t)) (min ys) = Some a"
      hence "Some (priority t) = Some a \<or> min ys = Some a" by (rule least_split)
      with \<open>min ys \<noteq> Some a\<close> have "priority t = a" by simp
      with \<open>priority t \<noteq> a\<close> show False by simp
    qed
  qed simp_all
  with assms show False by simp
qed

primrec find :: "'a::linorder \<Rightarrow> ('a, 'b) binqueue \<Rightarrow> ('a, 'b) bintree option" where
  "find a [] = None"
| "find a (x#xs) = (case x of None \<Rightarrow> find a xs
    | Some t \<Rightarrow> if priority t = a then Some t else find a xs)"

declare find.simps [simp del]

lemma find_simps [simp, code]:
  "find a [] = None"
  "find a (None # xs) = find a xs"
  "find a (Some t # xs) = (if priority t = a then Some t else find a xs)"
  by (simp_all add: find_def)

lemma find_works:
  assumes "Some a \<in> set (map (map_option priority) xs)"
  shows "\<exists>t. find a xs = Some t \<and> priority t = a"
  using assms by (induct xs) auto

lemma find_works_not_None:
  "Some a \<in> set (map (map_option priority) xs) \<Longrightarrow> find a xs \<noteq> None"
  by (drule find_works) auto

lemma find_None:
  "find a xs = None \<Longrightarrow> Some a \<notin> set (map (map_option priority) xs)"
  by (auto simp add: find_works_not_None)

lemma find_exist:
  "find a xs = Some t \<Longrightarrow> Some t \<in> set xs"
  by (induct xs) (simp_all add: eq_commute)

definition find_min :: "('a::linorder, 'b) binqueue \<Rightarrow> ('a, 'b) bintree option" where
  "find_min xs = (case min xs of None \<Rightarrow> None | Some a \<Rightarrow> find a xs)"

lemma find_min_simps [simp]:
  "find_min [] = None"
  "find_min (None # xs) = find_min xs"
  by (auto simp add: find_min_def split: option.split)

lemma find_min_single:
  "find_min [x] = x"
  by (cases x) (auto simp add: find_min_def)

lemma min_eq_find_min_None:
  "min xs = None \<longleftrightarrow> find_min xs = None"
proof (rule iffI)
  show "min xs = None \<Longrightarrow> find_min xs = None"
    by (simp add: find_min_def)
next
  assume *: "find_min xs = None"
  show "min xs = None"
  proof (rule ccontr)
    assume "min xs \<noteq> None"
    
    then obtain a where "min xs = Some a" by auto
    hence "find_min xs \<noteq> None"
      by (simp add: find_min_def min_exists find_works_not_None)
    with * show False by simp
  qed
qed

lemma min_eq_find_min_Some:
  "min xs = Some a \<longleftrightarrow> (\<exists> t. find_min xs = Some t \<and> priority t = a)"
proof (rule iffI)
  show D1: "\<And>a. min xs = Some a
    \<Longrightarrow> (\<exists> t. find_min xs = Some t \<and> priority t = a)"
    by (simp add: find_min_def find_works min_exists)
  (* no 'next' here to keep D1 in scope as it is needed in the other part *)
  assume *: "\<exists> t. find_min xs = Some t \<and> priority t = a"
  show "min xs = Some a"
  proof (rule ccontr)
    assume "min xs \<noteq> Some a" thus False
    proof (cases "min xs")
      case None 
      hence "find_min xs = None" by (simp only: min_eq_find_min_None)
      with * show False by simp
    next
      case (Some b) 
      with \<open>min xs \<noteq> Some a\<close> have "a \<noteq> b" by simp
      with * Some show False using D1 by auto
    qed
  qed
qed

lemma find_min_exist:
  assumes "find_min xs = Some t"
  shows "Some t \<in> set xs"
proof -
  from assms have "min xs \<noteq> None" by (simp add: min_eq_find_min_None)
  with assms show ?thesis by (auto simp add: find_min_def find_exist)
qed

lemma find_min_is_min:
  assumes "normalized xs"
  and "xs \<noteq> []"
  and "find_min xs = Some t"
  shows "\<forall>x \<in> set xs. x = None \<or> (priority t) \<le> priority (the x)"
  using assms by (simp add: min_eq_find_min_Some min_is_min)

lemma normalized_find_min_exists:
  "normalized xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> \<exists>t. find_min xs = Some t"
by (drule normalized_min_not_None) (simp_all add: min_eq_find_min_None)

primrec
  match :: "'a::linorder \<Rightarrow> ('a, 'b) bintree option \<Rightarrow> ('a, 'b) bintree option"
where
  "match a None = None"
| "match a (Some t) = (if priority t = a then None else Some t)"

definition delete_min :: "('a::linorder, 'b) binqueue \<Rightarrow> ('a, 'b) binqueue" where
  "delete_min xs = (case find_min xs
    of Some (Node a v ts) \<Rightarrow>
         normalize (meld (map Some (rev ts)) (map (match a) xs)) 
     | None \<Rightarrow> [])"

lemma delete_min_empty [simp]:
  "delete_min [] = []"
  by (simp add: delete_min_def)

lemma delete_min_nonempty [simp]:
  "normalized xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> find_min xs = Some t
    \<Longrightarrow> delete_min xs = normalize
      (meld (map Some (rev (children t))) (map (match (priority t)) xs))"
  unfolding delete_min_def by (cases t) simp

lemma is_binqueue_delete_min:
  assumes "is_binqueue 0 xs"
  shows "is_binqueue 0 (delete_min xs)"
proof (cases "find_min xs")
  case (Some t)
  from assms have "is_binqueue 0 (map (match (priority t)) xs)"
    by (induct xs) simp_all

  moreover
  from Some have "Some t \<in> set xs" by (rule find_min_exist)
  with assms have "\<exists>l. is_bintree l t" and "is_heap t"
    using is_binqueue_select[of 0 xs t] by auto
  with assms have "is_binqueue 0 (map Some (rev (children t)))"
    by (auto simp add: is_binqueue_children)
  
  ultimately show ?thesis using Some
    by (auto simp add: is_binqueue_meld delete_min_def is_binqueue_normalize
      split: bintree.split)
qed (simp add: delete_min_def)

lemma normalized_delete_min:
  "normalized (delete_min xs)"
  by (cases "find_min xs")
    (auto simp add: delete_min_def normalized_normalize split: bintree.split)


subsubsection \<open>Dedicated grand unified operation for generated program\<close>

definition
  meld' :: "('a, 'b) bintree option \<Rightarrow> ('a::linorder, 'b) binqueue
    \<Rightarrow> ('a, 'b) binqueue \<Rightarrow> ('a, 'b) binqueue"
where
  "meld' z xs ys = add z (meld xs ys)"

lemma [code]:
  "add z xs = meld' z [] xs"
  "meld xs ys = meld' None xs ys"
  by (simp_all add: meld'_def)

lemma [code]:
  "meld' z (Some t # xs) (Some r # ys) =
    z # (meld' (Some (merge t r)) xs ys)"
  "meld' (Some t) (Some r # xs) (None # ys) =
    None # (meld' (Some (merge t r)) xs ys)"
  "meld' (Some t) (None # xs) (Some r # ys) =
    None # (meld' (Some (merge t r)) xs ys)"
  "meld' None (x # xs) (None # ys) = x # (meld' None xs ys)"
  "meld' None (None # xs) (y # ys) = y # (meld' None xs ys)"
  "meld' z (None # xs) (None # ys) = z # (meld' None xs ys)"
  "meld' z xs [] = meld' z [] xs"
  "meld' z [] (y # ys) = meld' None [z] (y # ys)"
  "meld' (Some t) [] ys = meld' None [Some t] ys"
  "meld' None [] ys = ys"
  by (simp add: meld'_def | cases z)+


subsubsection \<open>Interface operations\<close>

abbreviation (input) empty :: "('a,'b) binqueue" where
  "empty \<equiv> []"

definition
  insert :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a, 'b) binqueue \<Rightarrow> ('a, 'b) binqueue"
where
  "insert a v xs = add (Some (Node a v [])) xs"

lemma insert_simps [simp]:
  "insert a v [] = [Some (Node a v [])]"
  "insert a v (None # xs) = Some (Node a v []) # xs"
  "insert a v (Some t # xs) = None # add (Some (merge (Node a v []) t)) xs"
  by (simp_all add: insert_def)

lemma is_binqueue_insert:
  "is_binqueue 0 xs \<Longrightarrow> is_binqueue 0 (insert a v xs)"
  by (simp add: is_binqueue_add_Some insert_def)

lemma normalized_insert:
  "normalized xs \<Longrightarrow> normalized (insert a v xs)"
  by (simp add: normalized_add insert_def)

definition
  pop :: "('a::linorder, 'b) binqueue \<Rightarrow> (('b \<times> 'a) option \<times> ('a, 'b) binqueue)"
where
  "pop xs = (case find_min xs of 
      None \<Rightarrow> (None, xs) 
    | Some t  \<Rightarrow> (Some (val t, priority t), delete_min xs))"

lemma pop_empty [simp]:
  "pop empty = (None, empty)"
  by (simp add: pop_def empty_def)

lemma pop_nonempty [simp]:
  "normalized xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> find_min xs = Some t
    \<Longrightarrow> pop xs = (Some (val t, priority t), normalize
      (meld (map Some (rev (children t))) (map (match (priority t)) xs)))"
  by (simp add: pop_def)

lemma pop_code [code]:
  "pop xs = (case find_min xs of 
      None \<Rightarrow> (None, xs) 
    | Some t  \<Rightarrow> (Some (val t, priority t), normalize
       (meld (map Some (rev (children t))) (map (match (priority t)) xs))))"
  by (cases "find_min xs") (simp_all add: pop_def delete_min_def split: bintree.split)

end
