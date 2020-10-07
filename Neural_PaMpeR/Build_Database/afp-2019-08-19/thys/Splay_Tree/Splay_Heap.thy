section "Splay Heap"

theory Splay_Heap
imports
  "HOL-Library.Tree_Multiset"
begin

text\<open>Splay heaps were invented by Okasaki~\cite{Okasaki}. They represent
priority queues by splay trees, not by heaps!\<close>

fun get_min :: "('a::linorder) tree \<Rightarrow> 'a" where
"get_min(Node l m r) = (if l = Leaf then m else get_min l)"

fun partition :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree * 'a tree" where
"partition p Leaf = (Leaf,Leaf)" |
"partition p (Node al a ar) =
  (if a \<le> p then
     case ar of
       Leaf \<Rightarrow> (Node al a ar, Leaf) |
       Node bl b br \<Rightarrow>
         if b \<le> p
         then let (pl,pr) = partition p br in (Node (Node al a bl) b pl, pr)
         else let (pl,pr) = partition p bl in (Node al a pl, Node pr b br)
   else case al of
       Leaf \<Rightarrow> (Leaf, Node al a ar) |
       Node bl b br \<Rightarrow>
         if b \<le> p
         then let (pl,pr) = partition p br in (Node bl b pl, Node pr a ar)
         else let (pl,pr) = partition p bl in (pl, Node pr b (Node br a ar)))" 

definition insert :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert x h = (let (l,r) = partition x h in Node l x r)"

fun del_min :: "'a::linorder tree \<Rightarrow> 'a tree" where
"del_min Leaf = Leaf" |
"del_min (Node Leaf _ r) = r" |
"del_min (Node (Node ll a lr) b r) =
  (if ll = Leaf then Node lr b r else Node (del_min ll) a (Node lr b r))"


lemma get_min_in:
  "h \<noteq> Leaf \<Longrightarrow> get_min h \<in> set_tree h"
by(induction h) auto

lemma get_min_min:
  "\<lbrakk> bst_wrt (\<le>) h; h \<noteq> Leaf \<rbrakk> \<Longrightarrow> \<forall>x \<in> set_tree h. get_min h \<le> x"
proof(induction h)
  case (Node l x r) thus ?case using get_min_in[of l] get_min_in[of r]
    by auto (blast intro: order_trans)
qed simp

lemma size_partition: "partition p t = (l',r') \<Longrightarrow> size t = size l' + size r'"
by (induction p t arbitrary: l' r' rule: partition.induct)
   (auto split: if_splits tree.splits prod.splits)

lemma mset_partition: "\<lbrakk> bst_wrt (\<le>) t; partition p t = (l',r') \<rbrakk>
 \<Longrightarrow> mset_tree t = mset_tree l' + mset_tree r'"
proof(induction p t arbitrary: l' r' rule: partition.induct)
  case 1 thus ?case by simp
next
  case (2 p l a r)
  show ?case
  proof cases
    assume "a \<le> p"
    show ?thesis
    proof (cases r)
      case Leaf thus ?thesis using \<open>a \<le> p\<close> "2.prems" by auto
    next
      case (Node rl b rr)
      show ?thesis
      proof cases
        assume "b \<le> p"
        thus ?thesis using Node \<open>a \<le> p\<close> "2.prems" "2.IH"(1)[OF _ Node]
          by (auto simp: ac_simps split: prod.splits)
      next
        assume "\<not> b \<le> p"
        thus ?thesis using Node \<open>a \<le> p\<close> "2.prems" "2.IH"(2)[OF _ Node]
          by (auto simp: ac_simps split: prod.splits)
      qed
    qed
  next
    assume "\<not> a \<le> p"
    show ?thesis
    proof (cases l)
      case Leaf thus ?thesis using \<open>\<not> a \<le> p\<close> "2.prems" by auto
    next
      case (Node ll b lr)
      show ?thesis
      proof cases
        assume "b \<le> p"
        thus ?thesis using Node \<open>\<not> a \<le> p\<close> "2.prems" "2.IH"(3)[OF _ Node]
          by (auto simp: ac_simps split: prod.splits)
      next
        assume "\<not> b \<le> p"
        thus ?thesis using Node \<open>\<not> a \<le> p\<close> "2.prems" "2.IH"(4)[OF _ Node]
          by (auto simp: ac_simps split: prod.splits)
      qed
    qed
  qed
qed

lemma set_partition: "\<lbrakk> bst_wrt (\<le>) t; partition p t = (l',r') \<rbrakk>
 \<Longrightarrow> set_tree t = set_tree l' \<union> set_tree r'"
by (metis mset_partition set_mset_tree set_mset_union)

lemma bst_partition:
  "partition p t = (l',r') \<Longrightarrow> bst_wrt (\<le>) t \<Longrightarrow> bst_wrt (\<le>) (Node l' p r')"
proof(induction p t arbitrary: l' r' rule: partition.induct)
  case 1 thus ?case by simp
next
  case (2 p l a r)
  show ?case
  proof cases
    assume "a \<le> p"
    show ?thesis
    proof (cases r)
      case Leaf thus ?thesis using \<open>a \<le> p\<close> "2.prems" by fastforce
    next
      case (Node rl b rr)
      show ?thesis
      proof cases
        assume "b \<le> p"
        thus ?thesis
          using Node \<open>a \<le> p\<close> "2.prems" "2.IH"(1)[OF _ Node] set_partition[of rr]
          by (fastforce split: prod.splits)
      next
        assume "\<not> b \<le> p"
        thus ?thesis
          using Node \<open>a \<le> p\<close> "2.prems" "2.IH"(2)[OF _ Node] set_partition[of rl]
          by (fastforce split: prod.splits)
      qed
    qed
  next
    assume "\<not> a \<le> p"
    show ?thesis
    proof (cases l)
      case Leaf thus ?thesis using \<open>\<not> a \<le> p\<close> "2.prems" by fastforce
    next
      case (Node ll b lr)
      show ?thesis
      proof cases
        assume "b \<le> p"
        thus ?thesis
          using Node \<open>\<not> a \<le> p\<close> "2.prems" "2.IH"(3)[OF _ Node] set_partition[of lr]
          by (fastforce split: prod.splits)
      next
        assume "\<not> b \<le> p"
        thus ?thesis
          using Node \<open>\<not> a \<le> p\<close> "2.prems" "2.IH"(4)[OF _ Node] set_partition[of ll]
          by (fastforce split: prod.splits)
      qed
    qed
  qed
qed

lemma size_del_min[simp]: "size(del_min t) = size t - 1"
by(induction t rule: del_min.induct) (auto simp: neq_Leaf_iff)

lemma mset_del_min: "mset_tree (del_min h) = mset_tree h - {# get_min h #}"
proof(induction h rule: del_min.induct)
  case (3 ll)
  show ?case
  proof cases
    assume "ll = Leaf" thus ?thesis using 3 by (simp add: ac_simps)
  next
    assume "ll \<noteq> Leaf"
    hence "get_min ll \<in># mset_tree ll"
      by (simp add: get_min_in)
    then obtain A where "mset_tree ll = add_mset (get_min ll) A"
      by (blast dest: multi_member_split)
    then show ?thesis using 3 by auto
  qed
qed auto

lemma bst_del_min: "bst_wrt (\<le>) t \<Longrightarrow> bst_wrt (\<le>) (del_min t)"
apply(induction t rule: del_min.induct)
  apply simp
 apply simp
apply auto
by (metis Multiset.diff_subset_eq_self subsetD set_mset_mono set_mset_tree mset_del_min)

end
