section "Priority Queues Based on Braun Trees"

theory Priority_Queue_Braun
imports
  "HOL-Library.Tree_Multiset"
  "HOL-Library.Pattern_Aliases"
  "HOL-Data_Structures.Priority_Queue_Specs"
  "HOL-Data_Structures.Braun_Tree"
begin

subsection "Introduction"

text\<open>Braun, Rem and Hoogerwoord \cite{BraunRem,Hoogerwoord} used
specific balanced binary trees, often called Braun trees (where in
each node with subtrees $l$ and $r$, $size(r) \le size(l) \le
size(r)+1$), to implement flexible arrays. Paulson \cite{Paulson}
(based on code supplied by Okasaki)
implemented priority queues via Braun trees. This theory verifies
Paulsons's implementation, with small simplifications.\<close>

text \<open>Direct proof of logarithmic height. Also follows from the fact that Braun
trees are balanced (proved in the base theory).\<close>

lemma height_size_braun: "braun t \<Longrightarrow> 2 ^ (height t) \<le> 2 * size t + 1"
proof(induction t)
  case (Node t1)
  show ?case
  proof (cases "height t1")
    case 0 thus ?thesis using Node by simp
  next
    case (Suc n)
    hence "2 ^ n \<le> size t1" using Node by simp
    thus ?thesis using Suc Node by(auto simp: max_def)
  qed
qed simp


subsection "Get Minimum"

lemma get_min: "\<lbrakk> heap h;  h \<noteq> Leaf \<rbrakk> \<Longrightarrow> value h = Min_mset (mset_tree h)"
by (auto simp add: eq_Min_iff neq_Leaf_iff)

subsection \<open>Insertion\<close>

hide_const (open) insert

fun insert :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert a Leaf = Node Leaf a Leaf" |
"insert a (Node l x r) =
 (if a < x then Node (insert x r) a l else Node (insert a r) x l)"

value "fold insert [0::int,1,2,3,-55,-5] Leaf"

lemma size_insert[simp]: "size(insert x t) = size t + 1"
by(induction t arbitrary: x) auto

lemma mset_insert: "mset_tree(insert x t) = {#x#} + mset_tree t"
by(induction t arbitrary: x) (auto simp: ac_simps)

lemma set_insert[simp]: "set_tree(insert x t) = {x} \<union> (set_tree t)"
by(induction t arbitrary: x) auto

lemma braun_insert: "braun t \<Longrightarrow> braun(insert x t)"
by(induction t arbitrary: x) auto

lemma heap_insert: "heap t \<Longrightarrow> heap(insert x t)"
by(induction t arbitrary: x) (auto  simp add: ball_Un)


subsection \<open>Deletion\<close>

text \<open>Slightly simpler definition of @{text del_left}
which avoids the need to appeal to the Braun invariant.\<close>

fun del_left :: "'a tree \<Rightarrow> 'a * 'a tree" where
"del_left (Node Leaf x r) = (x,r)" |
"del_left (Node l x r) = (let (y,l') = del_left l in (y,Node r x l'))"

lemma del_left_mset_plus:
  "del_left t = (x,t') \<Longrightarrow> t \<noteq> Leaf
  \<Longrightarrow> mset_tree t = {#x#} + mset_tree t'"
  by (induction t arbitrary: x t' rule: del_left.induct;
    auto split: prod.splits)

lemma del_left_mset:
  "del_left t = (x,t') \<Longrightarrow> t \<noteq> Leaf
  \<Longrightarrow> x \<in># mset_tree t \<and> mset_tree t' = mset_tree t - {#x#}"
by (simp add: del_left_mset_plus)

lemma del_left_set:
  "del_left t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> set_tree t = {x} \<union> set_tree t'"
by(simp add: del_left_mset_plus flip: set_mset_tree)

lemma del_left_heap:
  "del_left t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> heap t \<Longrightarrow> heap t'"
  by (induction t arbitrary: x t' rule: del_left.induct;
    fastforce split: prod.splits dest: del_left_set[THEN equalityD2])

lemma del_left_size:
  "del_left t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> size t = size t' + 1"
  by(induction t arbitrary: x t' rule: del_left.induct;
    auto split: prod.splits)

lemma del_left_braun:
  "del_left t = (x,t') \<Longrightarrow> braun t \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> braun t'"
  by(induction t arbitrary: x t' rule: del_left.induct;
    auto split: prod.splits dest: del_left_size)

context includes pattern_aliases
begin

text \<open>Slightly simpler definition: \<open>_\<close> instead of @{const Leaf} because of Braun invariant.\<close>

function (sequential) sift_down :: "'a::linorder tree \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"sift_down Leaf a _ = Node Leaf a Leaf" |
"sift_down (Node Leaf x _) a Leaf =
  (if a \<le> x then Node (Node Leaf x Leaf) a Leaf
   else Node (Node Leaf a Leaf) x Leaf)" |
"sift_down (Node l1 x1 r1 =: t1) a (Node l2 x2 r2 =: t2) =
  (if a \<le> x1 \<and> a \<le> x2
   then Node t1 a t2
   else if x1 \<le> x2 then Node (sift_down l1 a r1) x1 t2
        else Node t1 x2 (sift_down l2 a r2))"
by pat_completeness auto
termination
by (relation "measure (%(l,a,r). size l + size r)") auto

end

lemma size_sift_down:
  "braun(Node l a r) \<Longrightarrow> size(sift_down l a r) = size l + size r + 1"
by(induction l a r rule: sift_down.induct) (auto simp: Let_def)

lemma braun_sift_down:
  "braun(Node l a r) \<Longrightarrow> braun(sift_down l a r)"
by(induction l a r rule: sift_down.induct) (auto simp: size_sift_down Let_def)

lemma mset_sift_down:
  "braun(Node l a r) \<Longrightarrow> mset_tree(sift_down l a r) = {#a#} + (mset_tree l + mset_tree r)"
by(induction l a r rule: sift_down.induct) (auto simp: ac_simps Let_def)

lemma set_sift_down: "braun(Node l a r)
  \<Longrightarrow> set_tree(sift_down l a r) = {a} \<union> (set_tree l \<union> set_tree r)"
by(drule arg_cong[where f=set_mset, OF mset_sift_down]) (simp)

lemma heap_sift_down:
  "braun(Node l a r) \<Longrightarrow> heap l \<Longrightarrow> heap r \<Longrightarrow> heap(sift_down l a r)"
by (induction l a r rule: sift_down.induct) (auto simp: set_sift_down ball_Un Let_def)

fun del_min :: "'a::linorder tree \<Rightarrow> 'a tree" where
"del_min Leaf = Leaf" |
"del_min (Node Leaf x r) = Leaf" |
"del_min (Node l x r) = (let (y,l') = del_left l in sift_down r y l')"

lemma braun_del_min: "braun t \<Longrightarrow> braun(del_min t)"
apply(cases t rule: del_min.cases)
  apply simp
 apply simp
apply (fastforce split: prod.split intro!: braun_sift_down
  dest: del_left_size del_left_braun)
done

lemma heap_del_min: "heap t \<Longrightarrow> braun t \<Longrightarrow> heap(del_min t)"
apply(cases t rule: del_min.cases)
  apply simp
 apply simp
apply (fastforce split: prod.split intro!: heap_sift_down
  dest: del_left_size del_left_braun del_left_heap)
done

lemma size_del_min: assumes "braun t" shows "size(del_min t) = size t - 1"
proof(cases t rule: del_min.cases)
  case [simp]: (3 ll b lr a r)
  { fix y l' assume "del_left (Node ll b lr) = (y,l')"
    hence "size(sift_down r y l') = size t - 1" using assms
    by(subst size_sift_down) (auto dest: del_left_size del_left_braun) }
  thus ?thesis by(auto split: prod.split)
qed (insert assms, auto)

lemma mset_del_min: assumes "braun t" "t \<noteq> Leaf"
shows "mset_tree(del_min t) = mset_tree t - {#value t#}"
proof(cases t rule: del_min.cases)
  case 1 with assms show ?thesis by simp
next
  case 2 with assms show ?thesis by (simp)
next
  case [simp]: (3 ll b lr a r)
  have "mset_tree(sift_down r y l') = mset_tree t - {#a#}"
    if del: "del_left (Node ll b lr) = (y,l')" for y l'
    using assms del_left_mset[OF del] del_left_size[OF del]
      del_left_braun[OF del] del_left_mset_plus[OF del]
    apply (subst mset_sift_down)
    apply (auto simp: ac_simps del_left_mset_plus[OF del])
    done
  thus ?thesis by(auto split: prod.split)
qed


text \<open>Last step: prove all axioms of the priority queue specification:\<close>

interpretation braun: Priority_Queue
where empty = Leaf and is_empty = "\<lambda>h. h = Leaf"
and insert = insert and del_min = del_min
and get_min = "value" and invar = "\<lambda>h. braun h \<and> heap h"
and mset = mset_tree
proof(standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 show ?case by simp
next
  case 3 show ?case by(simp add: mset_insert)
next
  case 4 thus ?case by(simp add: mset_del_min)
next
  case 5 thus ?case using get_min mset_tree.simps(1) by blast
next
  case 6 thus ?case by(simp)
next
  case 7 thus ?case by(simp add: heap_insert braun_insert)
next
  case 8 thus ?case by(simp add: heap_del_min braun_del_min)
qed

end
