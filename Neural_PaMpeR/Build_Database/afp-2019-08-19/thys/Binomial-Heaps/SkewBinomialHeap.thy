section "Skew Binomial Heaps"

theory SkewBinomialHeap
imports Main "HOL-Library.Multiset"
begin

text \<open>Skew Binomial Queues as specified by Brodal and Okasaki \cite{BrOk96}
  are a data structure for priority queues with worst case O(1) {\em findMin}, 
  {\em insert}, and {\em meld} operations, and worst-case logarithmic 
  {\em deleteMin} operation.
  They are derived from priority queues in three steps:
    \begin{enumerate}
      \item Skew binomial trees are used to eliminate the possibility of 
            cascading links during insert operations. This reduces the complexity
            of an insert operation to $O(1)$.
      \item The current minimal element is cached. This approach, known as 
            {\em global root}, reduces the cost of a {\em findMin}-operation to
            O(1).
      \item By allowing skew binomial queues to contain skew binomial queues,
            the cost for meld-operations is reduced to $O(1)$. This approach
            is known as {\em data-structural bootstrapping}.
    \end{enumerate}

  In this theory, we combine Steps~2 and 3, i.e. we first implement skew binomial
  queues, and then bootstrap them. The bootstrapping implicitly introduces a 
  global root, such that we also get a constant time findMin operation.
\<close>

locale SkewBinomialHeapStruc_loc
begin

subsection "Datatype"

datatype ('e, 'a) SkewBinomialTree = 
  Node (val: 'e) (prio: "'a::linorder") (rank: nat) (children: "('e , 'a) SkewBinomialTree list")

type_synonym ('e, 'a) SkewBinomialQueue = "('e, 'a::linorder) SkewBinomialTree list"

subsubsection "Abstraction to Multisets"
text \<open>Returns a multiset with all (element, priority) pairs from a queue\<close>
fun tree_to_multiset 
  :: "('e, 'a::linorder) SkewBinomialTree \<Rightarrow> ('e \<times> 'a) multiset" 
and queue_to_multiset 
  :: "('e, 'a::linorder) SkewBinomialQueue \<Rightarrow> ('e \<times> 'a) multiset" where
  "tree_to_multiset (Node e a r ts) = {#(e,a)#} + queue_to_multiset ts" |
  "queue_to_multiset [] = {#}" |
  "queue_to_multiset (t#q) = tree_to_multiset t + queue_to_multiset q"

lemma ttm_children: "tree_to_multiset t = 
  {#(val t,prio t)#} + queue_to_multiset (children t)"
  by (cases t) auto

(*lemma qtm_cons[simp]: "queue_to_multiset (t#q)
  = queue_to_multiset q + tree_to_multiset t"
  apply(induct q arbitrary: t)
  apply simp
  apply(auto simp add: union_ac)
done*)

lemma qtm_conc[simp]: "queue_to_multiset (q@q') 
  = queue_to_multiset q + queue_to_multiset q'"
  by (induct q) (auto simp add: union_ac)

subsubsection "Invariant"

text \<open>Link two trees of rank $r$ to a new tree of rank $r+1$\<close>
fun  link :: "('e, 'a::linorder) SkewBinomialTree \<Rightarrow> ('e, 'a) SkewBinomialTree \<Rightarrow> 
  ('e, 'a) SkewBinomialTree" where
  "link (Node e1 a1 r1 ts1) (Node e2 a2 r2 ts2) = 
   (if  a1\<le>a2 
     then (Node e1 a1 (Suc r1) ((Node e2 a2 r2 ts2)#ts1))
     else (Node e2 a2 (Suc r2) ((Node e1 a1 r1 ts1)#ts2)))"

text \<open>Link two trees of rank $r$ and a new element to a new tree of 
  rank $r+1$\<close>
fun skewlink :: "'e \<Rightarrow> 'a::linorder \<Rightarrow> ('e, 'a) SkewBinomialTree \<Rightarrow> 
  ('e, 'a) SkewBinomialTree \<Rightarrow> ('e, 'a) SkewBinomialTree" where
  "skewlink e a t t' = (if a \<le> (prio t) \<and> a \<le> (prio t')
  then (Node e a (Suc (rank t)) [t,t'])
  else (if (prio t) \<le> (prio t') 
   then 
    Node (val t)  (prio t)  (Suc (rank t))  (Node e a 0 [] # t' # children t)
   else 
    Node (val t') (prio t') (Suc (rank t')) (Node e a 0 [] # t # children t')))"

text \<open>
  The invariant for trees claims that a tree labeled rank $0$ has no children, 
  and a tree labeled rank $r + 1$ is the result of an ordinary link or 
  a skew link of two trees with rank $r$.\<close>
function tree_invar :: "('e, 'a::linorder) SkewBinomialTree \<Rightarrow> bool" where
  "tree_invar (Node e a 0 ts) = (ts = [])" |
  "tree_invar (Node e a (Suc r) ts) = (\<exists> e1 a1 ts1 e2 a2 ts2 e' a'. 
  tree_invar (Node e1 a1 r ts1) \<and> tree_invar (Node e2 a2 r ts2) \<and> 
  ((Node e a (Suc r) ts) = link (Node e1 a1 r ts1) (Node e2 a2 r ts2) \<or> 
   (Node e a (Suc r) ts) = skewlink e' a' (Node e1 a1 r ts1) (Node e2 a2 r ts2)))"
by pat_completeness auto
termination
  apply(relation "measure rank")
  apply auto
done

text \<open>A heap satisfies the invariant, if all contained trees satisfy the 
  invariant, the ranks of the trees in the heap are distinct, except that the
  first two trees may have same rank, and the ranks are ordered in ascending 
  order.\<close>

text \<open>First part: All trees inside the queue satisfy the invariant.\<close>
definition queue_invar :: "('e, 'a::linorder) SkewBinomialQueue \<Rightarrow> bool" where
  "queue_invar q \<equiv> (\<forall>t \<in> set q. tree_invar t)"

lemma queue_invar_simps[simp]:
  "queue_invar []"
  "queue_invar (t#q) \<longleftrightarrow> tree_invar t \<and> queue_invar q"
  "queue_invar (q@q') \<longleftrightarrow> queue_invar q \<and> queue_invar q'"
  "queue_invar q \<Longrightarrow> t\<in>set q \<Longrightarrow> tree_invar t"
  unfolding queue_invar_def by auto


text \<open>Second part: The ranks of the trees in the heap are distinct, 
  except that the first two trees may have same rank, and the ranks are 
  ordered in ascending order.\<close>

text \<open>For tail of queue\<close>
fun rank_invar :: "('e, 'a::linorder) SkewBinomialQueue \<Rightarrow> bool" where
  "rank_invar [] = True" |
  "rank_invar [t] = True" |
  "rank_invar (t # t' # bq) = (rank t < rank t' \<and> rank_invar (t' # bq))"

text \<open>For whole queue: First two elements may have same rank\<close>
fun rank_skew_invar :: "('e, 'a::linorder) SkewBinomialQueue \<Rightarrow> bool" where
  "rank_skew_invar [] = True" |
  "rank_skew_invar [t] = True" |
  "rank_skew_invar (t # t' # bq) = ((rank t \<le> rank t') \<and> rank_invar (t' # bq))"

definition tail_invar :: "('e, 'a::linorder) SkewBinomialQueue \<Rightarrow> bool" where
  "tail_invar bq = (queue_invar bq \<and> rank_invar bq)"

definition invar :: "('e, 'a::linorder) SkewBinomialQueue \<Rightarrow> bool" where
  "invar bq = (queue_invar bq \<and> rank_skew_invar bq)"

lemma invar_empty[simp]:
  "invar []"
  "tail_invar []"
  unfolding invar_def tail_invar_def by auto

lemma invar_tail_invar: 
  "invar (t # bq) \<Longrightarrow> tail_invar bq" 
  unfolding invar_def tail_invar_def
  by (cases bq) simp_all

lemma link_mset[simp]: "tree_to_multiset (link t1 t2) 
                  = tree_to_multiset t1 +tree_to_multiset t2"
  by (cases t1, cases t2, auto simp add:union_ac)

lemma link_tree_invar: "\<lbrakk>tree_invar t1; tree_invar t2; rank t1 = rank t2\<rbrakk> \<Longrightarrow>
  tree_invar (link t1 t2)"
  by (cases t1, cases t2, simp, blast)

lemma skewlink_mset[simp]: "tree_to_multiset (skewlink e a t1 t2) 
  = {# (e,a) #} +  tree_to_multiset t1 + tree_to_multiset t2"
  by (cases t1, cases t2, auto simp add:union_ac)

lemma skewlink_tree_invar: "\<lbrakk>tree_invar t1; tree_invar t2; rank t1 = rank t2\<rbrakk> \<Longrightarrow> 
  tree_invar (skewlink e a t1 t2)"
  by (cases t1, cases t2, simp, blast)


lemma rank_link: "rank t = rank t' \<Longrightarrow> rank (link t t') = rank t + 1"
  apply (cases t)
  apply (cases t')
  apply(auto)
  done

lemma rank_skew_rank_invar: "rank_skew_invar (t # bq) \<Longrightarrow> rank_invar bq" 
  by (cases bq) simp_all

lemma rank_invar_rank_skew:
  assumes "rank_invar q"
  shows "rank_skew_invar q" 
proof (cases q)
  case Nil
  then show ?thesis by simp
next
  case (Cons _ list)
  with assms show ?thesis
    by (cases list) simp_all
qed

lemma rank_invar_cons_up: 
  "\<lbrakk>rank_invar (t # bq); rank t' < rank t\<rbrakk> \<Longrightarrow> rank_invar (t' # t # bq)" 
  by simp  

lemma rank_skew_cons_up: 
  "\<lbrakk>rank_invar (t # bq); rank t' \<le> rank t\<rbrakk> \<Longrightarrow> rank_skew_invar (t' # t # bq)" 
  by simp

lemma rank_invar_cons_down: "rank_invar (t # bq) \<Longrightarrow> rank_invar bq" 
  by (cases bq) simp_all

lemma rank_invar_hd_cons: 
  "\<lbrakk>rank_invar bq; rank t < rank (hd bq)\<rbrakk> \<Longrightarrow> rank_invar (t # bq)"
  apply(cases bq)
  apply(auto)
  done


lemma tail_invar_cons_up: 
  "\<lbrakk>tail_invar (t # bq); rank t' < rank t; tree_invar t'\<rbrakk> 
  \<Longrightarrow> tail_invar (t' # t # bq)" 
  unfolding tail_invar_def
  apply (cases bq) 
  apply simp_all
  done

lemma tail_invar_cons_up_invar: 
  "\<lbrakk>tail_invar (t # bq); rank t' \<le> rank t; tree_invar t'\<rbrakk> \<Longrightarrow> invar (t' # t # bq)"
  by (cases bq) (simp_all add: invar_def tail_invar_def)

lemma tail_invar_cons_down: 
  "tail_invar (t # bq) \<Longrightarrow> tail_invar bq" 
  unfolding tail_invar_def
  by (cases bq) simp_all

lemma tail_invar_app_single: 
  "\<lbrakk>tail_invar bq; \<forall>t \<in> set bq. rank t < rank t'; tree_invar t'\<rbrakk> 
    \<Longrightarrow> tail_invar (bq @ [t'])" 
proof (induct bq)
  case Nil
  then show ?case by (simp add: tail_invar_def)
next
  case (Cons a bq)
  from \<open>tail_invar (a # bq)\<close> have "tail_invar bq" 
    by (rule tail_invar_cons_down)
  with Cons have "tail_invar (bq @ [t'])" by simp
  with Cons show ?case 
    by (cases bq) (simp_all add: tail_invar_cons_up tail_invar_def)
qed

lemma invar_app_single: 
  "\<lbrakk>invar bq; \<forall>t \<in> set bq. rank t < rank t'; tree_invar t'\<rbrakk> 
   \<Longrightarrow> invar (bq @ [t'])"
proof (induct bq)
  case Nil
  then show ?case by (simp add: invar_def)
next
  case (Cons a bq)
  show ?case
  proof (cases bq)
    case Nil
    with Cons show ?thesis by (simp add: invar_def)
  next
    case Cons': (Cons ta qa)
    from Cons(2) have a1: "tail_invar bq" by (rule invar_tail_invar)
    from Cons(3) have a2: "\<forall>t\<in>set bq. rank t < rank t'" by simp
    from a1 a2 Cons(4) tail_invar_app_single[of "bq" "t'"] 
    have "tail_invar (bq @ [t'])" by simp
    with Cons Cons' show ?thesis
      by (simp_all add: tail_invar_cons_up_invar invar_def tail_invar_def)
  qed 
qed

lemma invar_children: 
  assumes "tree_invar ((Node e a r ts)::(('e, 'a::linorder) SkewBinomialTree))"
  shows "queue_invar ts" using assms
proof (induct r arbitrary: e a ts)
  case 0
  then show ?case by simp
next
  case (Suc r)
  from Suc(2) obtain e1 a1 ts1 e2 a2 ts2 e' a' where  
    inv_t1: "tree_invar (Node e1 a1 r ts1)" and
    inv_t2: "tree_invar (Node e2 a2 r ts2)" and
    link_or_skew: 
    "((Node e a (Suc r) ts) = link (Node e1 a1 r ts1) (Node e2 a2 r ts2)
    \<or> (Node e a (Suc r) ts) 
       = skewlink e' a' (Node e1 a1 r ts1) (Node e2 a2 r ts2))"
    by (simp only: tree_invar.simps) blast
  from Suc(1)[OF inv_t1] inv_t2 
  have case1: "queue_invar ((Node e2 a2 r ts2) # ts1)" by simp
  from Suc(1)[OF inv_t2] inv_t1 
  have case2: "queue_invar ((Node e1 a1 r ts1) # ts2)" by simp
  show ?case
  proof (cases "(Node e a (Suc r) ts) = link (Node e1 a1 r ts1) (Node e2 a2 r ts2)")
    case True
    hence "ts =
     (if a1 \<le> a2 
      then (Node e2 a2 r ts2) # ts1 
      else (Node e1 a1 r ts1) # ts2)" by auto
    with case1 case2 show ?thesis by simp
  next
    case False
    with link_or_skew 
    have "Node e a (Suc r) ts = 
      skewlink e' a' (Node e1 a1 r ts1) (Node e2 a2 r ts2)" by simp
    hence "ts =
     (if a' \<le> a1 \<and> a' \<le> a2
      then [(Node e1 a1 r ts1),(Node e2 a2 r ts2)]
      else (if a1 \<le> a2 
        then (Node e' a' 0 []) # (Node e2 a2 r ts2) # ts1
        else (Node e' a' 0 []) # (Node e1 a1 r ts1) # ts2))" by auto
    with case1 case2 show ?thesis by simp
  qed
qed

subsubsection "Heap Order"

fun heap_ordered :: "('e, 'a::linorder) SkewBinomialTree \<Rightarrow> bool" where
  "heap_ordered (Node e a r ts) 
   = (\<forall>x \<in> set_mset (queue_to_multiset ts). a \<le> snd x)"


text \<open>The invariant for trees implies heap order.\<close>
lemma tree_invar_heap_ordered: 
  fixes t :: "('e, 'a::linorder) SkewBinomialTree"
  assumes "tree_invar t"
  shows "heap_ordered t"
proof (cases t)
  case (Node e a nat list)
  with assms show ?thesis
  proof (induct nat arbitrary: t e a list)
    case 0
    then show ?case by simp
  next
    case (Suc nat)
    from Suc(2,3) obtain t1 e1 a1 ts1 t2 e2 a2 ts2 e' a' where 
      inv_t1: "tree_invar t1" and
      inv_t2: "tree_invar t2" and 
      link_or_skew: "t = link t1 t2 \<or> t = skewlink e' a' t1 t2" and 
      eq_t1[simp]: "t1 = (Node e1 a1 nat ts1)" and 
      eq_t2[simp]: "t2 = (Node e2 a2 nat ts2)" 
      by (simp only: tree_invar.simps) blast
    note heap_t1 = Suc(1)[OF inv_t1 eq_t1]
    note heap_t2 = Suc(1)[OF inv_t2 eq_t2]
    from link_or_skew heap_t1 heap_t2 show ?case
      by (cases "t = link t1 t2") auto
  qed
qed

(***********************************************************)



(***********************************************************)


subsubsection "Height and Length"
text \<open>
  Although complexity of HOL-functions cannot be expressed within 
  HOL, we can express the height and length of a binomial heap.
  By showing that both, height and length, are logarithmic in the number 
  of contained elements, we give strong evidence that our functions have
  logarithmic complexity in the number of elements.
\<close>

text \<open>Height of a tree and queue\<close>
fun height_tree :: "('e, ('a::linorder)) SkewBinomialTree \<Rightarrow> nat" and
    height_queue :: "('e, ('a::linorder)) SkewBinomialQueue \<Rightarrow> nat" 
  where
  "height_tree (Node e a r ts) = height_queue ts" |
  "height_queue [] = 0" |
  "height_queue (t # ts) = max (Suc (height_tree t)) (height_queue ts)"

lemma link_length: "size (tree_to_multiset (link t1 t2)) = 
  size (tree_to_multiset t1) + size (tree_to_multiset t2)"
  apply(cases t1)
  apply(cases t2)
  apply simp
done

lemma tree_rank_estimate_upper: 
  "tree_invar (Node e a r ts) \<Longrightarrow> 
   size (tree_to_multiset (Node e a r ts)) \<le> (2::nat)^(Suc r) - 1"
proof (induct r arbitrary: e a ts)
  case 0
  then show ?case by simp
next
  case (Suc r)
  from Suc(2) obtain e1 a1 ts1 e2 a2 ts2 e' a' where
    link:
      "(Node e a (Suc r) ts) = link (Node e1 a1 r ts1) (Node e2 a2 r ts2) \<or>
       (Node e a (Suc r) ts) = skewlink e' a' (Node e1 a1 r ts1) (Node e2 a2 r ts2)"
    and inv1: "tree_invar (Node e1 a1 r ts1)"
    and inv2: "tree_invar (Node e2 a2 r ts2)"
    by simp blast
  note iv1 = Suc(1)[OF inv1]
  note iv2 = Suc(1)[OF inv2]
  have "(2::nat)^r - 1 + (2::nat)^r - 1 \<le> (2::nat)^(Suc r) - 1" by simp
  with link Suc show ?case
    apply (cases "Node e a (Suc r) ts = link (Node e1 a1 r ts1) (Node e2 a2 r ts2)")
    using iv1 iv2 apply (simp del: link.simps)
    using iv1 iv2 apply (simp del: skewlink.simps)
    done
qed

lemma tree_rank_estimate_lower: 
  "tree_invar (Node e a r ts) \<Longrightarrow> 
   size (tree_to_multiset (Node e a r ts)) \<ge> (2::nat)^r"
proof (induct r arbitrary: e a ts)
  case 0
  then show ?case by simp
next
  case (Suc r)
  from Suc(2) obtain e1 a1 ts1 e2 a2 ts2 e' a' where
    link:
      "(Node e a (Suc r) ts) = link (Node e1 a1 r ts1) (Node e2 a2 r ts2) \<or>
       (Node e a (Suc r) ts) = skewlink e' a' (Node e1 a1 r ts1) (Node e2 a2 r ts2)"
    and inv1: "tree_invar (Node e1 a1 r ts1)"
    and inv2: "tree_invar (Node e2 a2 r ts2)"
    by simp blast
  note iv1 = Suc(1)[OF inv1]
  note iv2 = Suc(1)[OF inv2]
  have "(2::nat)^r - 1 + (2::nat)^r - 1 \<le> (2::nat)^(Suc r) - 1" by simp
  with link Suc show ?case
    apply (cases "Node e a (Suc r) ts = link (Node e1 a1 r ts1) (Node e2 a2 r ts2)")
    using iv1 iv2 apply (simp del: link.simps)
    using iv1 iv2 apply (simp del: skewlink.simps)
    done
qed



lemma tree_rank_height:
  "tree_invar (Node e a r ts) \<Longrightarrow> height_tree (Node e a r ts) = r"
proof (induct r arbitrary: e a ts)
  case 0
  then show ?case by simp
next
  case (Suc r)
  from Suc(2) obtain e1 a1 ts1 e2 a2 ts2 e' a' where
    link:
      "(Node e a (Suc r) ts) = link (Node e1 a1 r ts1) (Node e2 a2 r ts2) \<or>
       (Node e a (Suc r) ts) = skewlink e' a' (Node e1 a1 r ts1) (Node e2 a2 r ts2)"
    and inv1: "tree_invar (Node e1 a1 r ts1)"
    and inv2: "tree_invar (Node e2 a2 r ts2)"
    by simp blast
  note iv1 = Suc(1)[OF inv1]
  note iv2 = Suc(1)[OF inv2]
  from Suc(2) link show ?case
    apply (cases "Node e a (Suc r) ts = link (Node e1 a1 r ts1) (Node e2 a2 r ts2)")
    apply (cases "a1 \<le> a2")
    using iv1 iv2 apply simp 
    using iv1 iv2 apply simp
    apply (cases "a' \<le> a1 \<and> a' \<le> a2")
    apply (simp only: height_tree.simps)
    using iv1 iv2 apply simp 
    apply (cases "a1 \<le> a2") 
    using iv1 iv2 
    apply (simp del: tree_invar.simps link.simps) 
    using iv1 iv2 
    apply (simp del: tree_invar.simps link.simps) 
    done
qed

text \<open>A skew binomial tree of height $h$ contains at most  $2^{h+1} - 1$
  elements\<close>
theorem tree_height_estimate_upper:
  "tree_invar t \<Longrightarrow> 
  size (tree_to_multiset t) \<le> (2::nat)^(Suc (height_tree t)) - 1"
  apply (cases t, simp only:)
  apply (frule tree_rank_estimate_upper)
  apply (frule tree_rank_height)
  apply (simp only: )
  done

text \<open>A skew binomial tree of height $h$ contains at least  $2^{h}$ elements\<close>
theorem tree_height_estimate_lower:
  "tree_invar t \<Longrightarrow> size (tree_to_multiset t) \<ge> (2::nat)^(height_tree t)"
  apply (cases t, simp only:)
  apply (frule tree_rank_estimate_lower)
  apply (frule tree_rank_height)
  apply (simp only: )
  done


lemma size_mset_tree_upper: "tree_invar t \<Longrightarrow> 
  size (tree_to_multiset t) \<le> (2::nat)^(Suc (rank t)) - (1::nat)"
  apply (cases t)
  by (simp only: tree_rank_estimate_upper SkewBinomialTree.sel(3)) 

lemma size_mset_tree_lower: "tree_invar t \<Longrightarrow> 
  size (tree_to_multiset t) \<ge> (2::nat)^(rank t)"
  apply (cases t) 
  by (simp only: tree_rank_estimate_lower SkewBinomialTree.sel(3)) 


lemma invar_butlast: "invar (bq @ [t]) \<Longrightarrow> invar bq"
  unfolding invar_def
  apply (induct bq) 
  apply simp 
  apply (case_tac bq) 
  apply simp
  apply (case_tac list) 
  by simp_all

lemma invar_last_max: 
  "invar ((b#b'#bq) @ [m]) \<Longrightarrow> \<forall> t \<in> set (b'#bq). rank t < rank m"
  unfolding invar_def
  apply (induct bq) apply simp apply (case_tac bq) apply simp by simp

lemma invar_last_max': "invar ((b#b'#bq) @ [m]) \<Longrightarrow> rank b \<le> rank b'" 
  unfolding invar_def by simp

lemma invar_length: "invar bq \<Longrightarrow> length bq \<le> Suc (Suc (rank (last bq)))"
proof (induct bq rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x xs)
  show ?case proof (cases xs)
    case Nil thus ?thesis by simp
  next
    case [simp]: (Cons xxs xx) 
    note Cons' = Cons
    thus ?thesis
    proof (cases xx)
      case Nil with snoc.prems Cons show ?thesis by simp
    next
      case (Cons xxxs xxx)
      from snoc.hyps[OF invar_butlast[OF snoc.prems]] have
        IH: "length xs \<le> Suc (Suc (rank (last xs)))" .
      also from invar_last_max[OF snoc.prems[unfolded Cons' Cons]] 
                invar_last_max'[OF snoc.prems[unfolded Cons' Cons]] 
                last_in_set[of xs] Cons have
        "Suc (rank (last xs)) \<le> rank (last (xs @ [x]))" by auto
      finally show ?thesis by simp
    qed
  qed
qed

lemma size_queue_sum_list: 
  "size (queue_to_multiset bq) = sum_list (map (size \<circ> tree_to_multiset) bq)"
  by (induct bq) simp_all

text \<open>
  A skew binomial heap of length $l$ contains at least $2^{l-1} - 1$ elements. 
\<close>
theorem queue_length_estimate_lower: 
  "invar bq \<Longrightarrow> (size (queue_to_multiset bq)) \<ge> 2^(length bq - 1) - 1"
proof (induct bq rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x xs) thus ?case
  proof (cases xs)
    case Nil thus ?thesis by simp
  next
    case [simp]: (Cons xx xxs)
    from snoc.hyps[OF invar_butlast[OF snoc.prems]]
    have IH: "2 ^ (length xs - 1) \<le> Suc (size (queue_to_multiset xs))" by simp
    have size_q: 
      "size (queue_to_multiset (xs @ [x])) = 
      size (queue_to_multiset xs) + size (tree_to_multiset x)" 
      by (simp add: size_queue_sum_list)
    moreover
    from snoc.prems have inv_x: "tree_invar x" by (simp add: invar_def)
    from size_mset_tree_lower[OF this] 
    have "2 ^ (rank x) \<le> size (tree_to_multiset x)" .
    ultimately have 
      eq: "size (queue_to_multiset xs) + (2::nat)^(rank x) \<le> 
      size (queue_to_multiset (xs @ [x]))" by simp
    from invar_length[OF snoc.prems] have "length xs \<le> (rank x + 1)" by simp
    hence snd: "(2::nat) ^ (length xs - 1) \<le> (2::nat) ^ ((rank x))" 
      by (simp del: power.simps)
    have
      "(2::nat) ^ (length (xs @ [x]) - 1) = 
      (2::nat) ^ (length xs - 1) + (2::nat) ^ (length xs - 1)"
      by auto
    with IH have 
      "2 ^ (length (xs @ [x]) - 1) \<le> 
      Suc (size (queue_to_multiset xs)) + 2 ^ (length xs - 1)" 
      by simp
    with snd have "2 ^ (length (xs @ [x]) - 1) \<le> 
      Suc (size (queue_to_multiset xs)) + 2 ^ rank x" 
      by arith
    with eq show ?thesis by simp
  qed
qed


subsection "Operations"
subsubsection "Empty Tree"
lemma empty_correct: "q=Nil \<longleftrightarrow> queue_to_multiset q = {#}"
  apply (cases q)
  apply simp
  apply (case_tac a)
  apply auto
  done

subsubsection "Insert"
text \<open>Inserts a tree into the queue, such that two trees of same rank get 
  linked and are recursively inserted. This is the same definition as for 
  binomial queues and is used for melding.\<close>
fun ins :: "('e, 'a::linorder) SkewBinomialTree \<Rightarrow> ('e, 'a) SkewBinomialQueue \<Rightarrow> 
  ('e, 'a) SkewBinomialQueue" where
  "ins t [] = [t]" |
  "ins t' (t # bq) =
    (if (rank t') < (rank t) 
      then t' # t # bq 
      else (if (rank t) < (rank t')
        then t # (ins t' bq) 
        else ins (link t' t) bq))"

text \<open>Insert an element with priority into a queue using skewlinks.\<close>
fun insert :: "'e \<Rightarrow> 'a::linorder \<Rightarrow> ('e, 'a) SkewBinomialQueue \<Rightarrow> 
  ('e, 'a) SkewBinomialQueue" where
  "insert e a [] = [Node e a 0 []]" |
  "insert e a [t] = [Node e a 0 [],t]" |
  "insert e a (t # t' # bq) =
    (if rank t \<noteq> rank t' 
      then (Node e a 0 []) # t # t' # bq
      else (skewlink e a t t') # bq)"

lemma ins_mset: 
  "\<lbrakk>tree_invar t; queue_invar q\<rbrakk> \<Longrightarrow>
   queue_to_multiset (ins t q) = tree_to_multiset t + queue_to_multiset q"
by (induct q arbitrary: t) (auto simp: union_ac link_tree_invar)

lemma insert_mset: "queue_invar q \<Longrightarrow> 
  queue_to_multiset (insert e a q) = 
  queue_to_multiset q + {# (e,a) #}"
by (induct q rule: insert.induct) (auto simp add: union_ac ttm_children)

lemma ins_queue_invar: "\<lbrakk>tree_invar t; queue_invar q\<rbrakk> \<Longrightarrow> queue_invar (ins t q)"
proof (induct q arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons a q) 
  note iv = Cons(1)
  from Cons(2,3) show ?case
    apply (cases "rank t < rank a")
    apply simp
    apply (cases "rank t = rank a")
    defer
    using iv[of "t"] apply simp
  proof goal_cases
    case prems: 1
    from prems(2) have inv_a: "tree_invar a" by simp
    from prems(2) have inv_q: "queue_invar q" by simp
    note inv_link = link_tree_invar[OF prems(1) inv_a prems(4)]
    from iv[OF inv_link inv_q] prems(4) show ?case by simp
  qed
qed

lemma insert_queue_invar: "queue_invar q \<Longrightarrow> queue_invar (insert e a q)"
proof (induct q rule: insert.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 e a t t' bq)
  show ?case
  proof (cases "rank t = rank t'")
    case False
    with 3 show ?thesis by simp
  next
    case True
    from 3 have inv_t: "tree_invar t" by simp
    from 3 have inv_t': "tree_invar t'" by simp
    from 3 skewlink_tree_invar[OF inv_t inv_t' True, of e a] True
    show ?thesis by simp
  qed
qed

lemma rank_ins2: 
  "rank_invar bq \<Longrightarrow> 
    rank t \<le> rank (hd (ins t bq)) 
    \<or> (rank (hd (ins t bq)) = rank (hd bq) \<and> bq \<noteq> [])"
  apply (induct bq arbitrary: t)
  apply auto
proof goal_cases
  case prems: (1 a bq t)
  hence r: "rank (link t a) = rank a + 1" by (simp add: rank_link)
  with prems and prems(1)[of "(link t a)"] show ?case
    apply (cases bq)
    apply auto
    done
qed

lemma insert_rank_invar: "rank_skew_invar q \<Longrightarrow> rank_skew_invar (insert e a q)"
proof (cases q, simp)
  fix t q'
  assume "rank_skew_invar q" "q = t # q'"
  thus "rank_skew_invar (insert e a q)"
  proof (cases "q'", (auto intro: gr0I)[1])
    fix t' q''
    assume "rank_skew_invar q" "q = t # q'" "q' = t' # q''"
    thus "rank_skew_invar (insert e a q)"
      apply(cases "rank t = rank t'") defer 
      apply (auto intro: gr0I)[1]
      apply (simp del: skewlink.simps)
    proof goal_cases
      case prems: 1
      with rank_invar_cons_down[of "t'" "q'"] have "rank_invar q'" by simp
      show ?case
      proof (cases q'')
        case Nil
        then show ?thesis by simp
      next
        case (Cons t'' q''')
        with prems have "rank t' < rank t''" by simp
        with prems have "rank (skewlink e a t t') \<le> rank t''" by simp
        with prems Cons rank_skew_cons_up[of "t''" "q'''" "skewlink e a t t'"] 
        show ?thesis by simp
      qed 
    qed 
  qed 
qed

lemma insert_invar: "invar q \<Longrightarrow> invar (insert e a q)"
  unfolding invar_def
  using insert_queue_invar[of q] insert_rank_invar[of q]
  by simp

theorem insert_correct:
  assumes I: "invar q"
  shows 
  "invar (insert e a q)"
  "queue_to_multiset (insert e a q) = queue_to_multiset q + {# (e,a) #}"
  using insert_mset[of q] insert_invar[of q] I
  unfolding invar_def by simp_all

subsubsection "meld"
text \<open>Remove duplicate tree ranks by inserting the first tree of the 
  queue into the rest of the queue.\<close>
fun uniqify 
  :: "('e, 'a::linorder) SkewBinomialQueue \<Rightarrow> ('e, 'a) SkewBinomialQueue" 
  where
  "uniqify [] = []" |
  "uniqify (t#bq) = ins t bq"

text \<open>Meld two uniquified queues using the same definition as for 
  binomial queues.\<close>
fun meldUniq 
  :: "('e, 'a::linorder) SkewBinomialQueue \<Rightarrow> ('e,'a) SkewBinomialQueue \<Rightarrow>
  ('e, 'a) SkewBinomialQueue" where
  "meldUniq [] bq = bq" |
  "meldUniq bq [] = bq" |
  "meldUniq (t1#bq1) (t2#bq2) = (if rank t1 < rank t2 
       then t1 # (meldUniq bq1 (t2#bq2))
       else (if rank t2 < rank t1
              then t2 # (meldUniq (t1#bq1) bq2)
              else ins (link t1 t2) (meldUniq bq1 bq2)))"

text \<open>Meld two queues using above functions.\<close>
definition meld 
  :: "('e, 'a::linorder) SkewBinomialQueue \<Rightarrow> ('e, 'a) SkewBinomialQueue \<Rightarrow> 
      ('e, 'a) SkewBinomialQueue" where
  "meld bq1 bq2 = meldUniq (uniqify bq1) (uniqify bq2)"

lemma invar_uniqify: "queue_invar q \<Longrightarrow> queue_invar (uniqify q)"
  apply(cases q, simp)
  apply(auto simp add: ins_queue_invar)
done

lemma invar_meldUniq: "\<lbrakk>queue_invar q; queue_invar q'\<rbrakk> \<Longrightarrow> queue_invar (meldUniq q q')"
proof (induct q q' rule: meldUniq.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 t1 bq1 t2 bq2)
  consider (lt) "rank t1 < rank t2" | (gt) "rank t1 > rank t2" | (eq) "rank t1 = rank t2"
    by atomize_elim auto
  then show ?case
  proof cases
    case t1t2: lt
    from 3(4) have inv_bq1: "queue_invar bq1" by simp
    from 3(4) have inv_t1: "tree_invar t1" by simp
    from 3(1)[OF t1t2 inv_bq1 3(5)] inv_t1 t1t2
    show ?thesis by simp
  next
    case t1t2: gt
    from 3(5) have inv_bq2: "queue_invar bq2" by simp
    from 3(5) have inv_t2: "tree_invar t2" by simp
    from t1t2 have "\<not> rank t1 < rank t2" by simp
    from 3(2) [OF this t1t2 3(4) inv_bq2] inv_t2 t1t2
    show ?thesis by simp
  next
    case t1t2: eq
    from 3(4) have inv_bq1: "queue_invar bq1" by simp
    from 3(4) have inv_t1: "tree_invar t1" by simp
    from 3(5) have inv_bq2: "queue_invar bq2" by simp
    from 3(5) have inv_t2: "tree_invar t2" by simp
    note inv_link = link_tree_invar[OF inv_t1 inv_t2 t1t2]
    from t1t2 have "\<not> rank t1 < rank t2" "\<not> rank t2 < rank t1" by auto
    note inv_meld = 3(3)[OF this inv_bq1 inv_bq2]
    from ins_queue_invar[OF inv_link inv_meld] t1t2
    show ?thesis by simp
  qed
qed


lemma meld_queue_invar:
  assumes "queue_invar q"
    and "queue_invar q'"
  shows "queue_invar (meld q q')"
proof -
  note inv_uniq_q = invar_uniqify[OF assms(1)] 
  note inv_uniq_q' = invar_uniqify[OF assms(2)]
  note inv_meldUniq = invar_meldUniq[OF inv_uniq_q inv_uniq_q']
  thus ?thesis by (simp add: meld_def)
qed

lemma uniqify_mset: "queue_invar q \<Longrightarrow> queue_to_multiset q = queue_to_multiset (uniqify q)"
  apply (cases q) 
  apply simp
  apply (simp add: ins_mset)
  done

lemma meldUniq_mset: "\<lbrakk>queue_invar q; queue_invar q'\<rbrakk> \<Longrightarrow> 
  queue_to_multiset (meldUniq q q') = 
  queue_to_multiset q + queue_to_multiset q'"
by(induct q q' rule: meldUniq.induct)
  (auto simp: ins_mset link_tree_invar invar_meldUniq union_ac)

lemma meld_mset:
  "\<lbrakk> queue_invar q; queue_invar q' \<rbrakk> \<Longrightarrow>
  queue_to_multiset (meld q q') = queue_to_multiset q + queue_to_multiset q'"
by (simp add: meld_def meldUniq_mset invar_uniqify uniqify_mset[symmetric])

text \<open>Ins operation satisfies rank invariant, see binomial queues\<close>
lemma rank_ins: "rank_invar bq \<Longrightarrow> rank_invar (ins t bq)"
proof (induct bq arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons a bq)
  then show ?case
    apply auto
  proof goal_cases
    case prems: 1
    hence inv: "rank_invar (ins t bq)" by (cases bq) simp_all
    from prems have hd: "bq \<noteq> [] \<Longrightarrow> rank a < rank (hd bq)"  by (cases bq) auto
    from prems have "rank t \<le> rank (hd (ins t bq)) 
                     \<or> (rank (hd (ins t bq)) = rank (hd bq) \<and> bq \<noteq> [])"
      by (metis rank_ins2 rank_invar_cons_down)
    with prems have "rank a < rank (hd (ins t bq)) 
      \<or> (rank (hd (ins t bq)) = rank (hd bq) \<and> bq \<noteq> [])" by auto
    with prems and inv and hd show ?case
      by (auto simp add: rank_invar_hd_cons)
  next
    case prems: 2
    hence inv: "rank_invar bq" by (cases bq) simp_all
    with prems and prems(1)[of "(link t a)"] show ?case by simp
  qed
qed
     
lemma rank_uniqify:
  assumes "rank_skew_invar q"
  shows "rank_invar (uniqify q)"
proof (cases q)
  case Nil
  then show ?thesis by simp
next
  case (Cons a list)
  with rank_skew_rank_invar[of "a" "list"] rank_ins[of "list" "a"] assms
  show ?thesis by simp 
qed

lemma rank_ins_min: "rank_invar bq \<Longrightarrow> rank (hd (ins t bq)) \<ge> min (rank t) (rank (hd bq))"
proof (induct bq arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons a bq)
  then show ?case
    apply auto
  proof goal_cases
    case prems: 1
    hence inv: "rank_invar bq" by (cases bq) simp_all
    from prems have r: "rank (link t a) = rank a + 1" by (simp add: rank_link)
    with prems and inv and prems(1)[of "(link t a)"] show ?case
      by (cases bq) auto
  qed
qed

lemma rank_invar_not_empty_hd: "\<lbrakk>rank_invar (t # bq); bq \<noteq> []\<rbrakk> \<Longrightarrow> rank t < rank (hd bq)"
  by (induct bq arbitrary: t) auto

lemma rank_invar_meldUniq_strong: 
  "\<lbrakk>rank_invar bq1; rank_invar bq2\<rbrakk> \<Longrightarrow> 
    rank_invar (meldUniq bq1 bq2) 
    \<and> rank (hd (meldUniq bq1 bq2)) \<ge> min (rank (hd bq1)) (rank (hd bq2))"
proof (induct bq1 bq2 rule: meldUniq.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 t1 bq1 t2 bq2)
  from 3 have inv1: "rank_invar bq1" by (cases bq1) simp_all
  from 3 have inv2: "rank_invar bq2" by (cases bq2) simp_all
  
  from inv1 and inv2 and 3 show ?case
    apply auto
  proof goal_cases
    let ?t = "t2"
    let ?bq = "bq2"
    let ?meldUniq = "rank t2 < rank (hd (meldUniq (t1 # bq1) bq2))"
    case prems: 1
    hence "?bq \<noteq> [] \<Longrightarrow> rank ?t < rank (hd ?bq)" 
      by (simp add: rank_invar_not_empty_hd)
    with prems have ne: "?bq \<noteq> [] \<Longrightarrow> ?meldUniq" by simp
    from prems have "?bq = [] \<Longrightarrow> ?meldUniq" by simp
    with ne have "?meldUniq" by (cases "?bq = []")
    with prems show ?case by (simp add: rank_invar_hd_cons)
  next \<comment> \<open>analog\<close>
    let ?t = "t1"
    let ?bq = "bq1"
    let ?meldUniq = "rank t1 < rank (hd (meldUniq bq1 (t2 # bq2)))"
    case prems: 2
    hence "?bq \<noteq> [] \<Longrightarrow> rank ?t < rank (hd ?bq)" 
      by (simp add: rank_invar_not_empty_hd)
    with prems have ne: "?bq \<noteq> [] \<Longrightarrow> ?meldUniq" by simp
    from prems have "?bq = [] \<Longrightarrow> ?meldUniq" by simp
    with ne have "?meldUniq" by (cases "?bq = []")
    with prems show ?case by (simp add: rank_invar_hd_cons)
  next
    case 3
    thus ?case by (simp add: rank_ins)
  next
    case prems: 4 (* Ab hier wirds hässlich *)
    then have r: "rank (link t1 t2) = rank t2 + 1" by (simp add: rank_link)
    have m: "meldUniq bq1 [] = bq1" by (cases bq1) auto
    
    from inv1 and inv2 and prems have 
      mm: "min (rank (hd bq1)) (rank (hd bq2)) \<le> rank (hd (meldUniq bq1 bq2))" 
      by simp
    from \<open>rank_invar (t1 # bq1)\<close> have "bq1 \<noteq> [] \<Longrightarrow> rank t1 < rank (hd bq1)" 
      by (simp add: rank_invar_not_empty_hd)
    with prems have r1: "bq1 \<noteq> [] \<Longrightarrow> rank t2 < rank (hd bq1)" by simp
    from \<open>rank_invar (t2 # bq2)\<close> have r2: "bq2 \<noteq> [] \<Longrightarrow> rank t2 < rank (hd bq2)"
      by (simp add: rank_invar_not_empty_hd)
    
    from inv1 r r1 rank_ins_min[of bq1 "(link t1 t2)"] have 
      abc1: "bq1 \<noteq> [] \<Longrightarrow> rank t2 \<le> rank (hd (ins (link t1 t2) bq1))" by simp
    from inv2 r r2 rank_ins_min[of bq2 "(link t1 t2)"] have 
      abc2: "bq2 \<noteq> [] \<Longrightarrow> rank t2 \<le> rank (hd (ins (link t1 t2) bq2))" by simp
    
    from r1 r2 mm have 
      "\<lbrakk>bq1 \<noteq> []; bq2 \<noteq> []\<rbrakk> \<Longrightarrow> rank t2 < rank (hd (meldUniq bq1 bq2))" 
      by (simp)
    with \<open>rank_invar (meldUniq bq1 bq2)\<close> r 
      rank_ins_min[of "meldUniq bq1 bq2" "link t1 t2"] 
    have "\<lbrakk>bq1 \<noteq> []; bq2 \<noteq> []\<rbrakk> \<Longrightarrow> 
      rank t2 < rank (hd (ins (link t1 t2) (meldUniq bq1 bq2)))" 
      by simp
    with inv1 and inv2 and r m r1 show ?case
      apply(cases "bq2 = []")
      apply(cases "bq1 = []")
      apply(simp)
      apply(auto simp add: abc1)
      apply(cases "bq1 = []")
      apply(simp)
      apply(auto simp add: abc2)
      done
  qed
qed

lemma rank_meldUniq: 
  "\<lbrakk>rank_invar bq1; rank_invar bq2\<rbrakk> \<Longrightarrow> rank_invar (meldUniq bq1 bq2)" 
  by (simp only: rank_invar_meldUniq_strong)


lemma rank_meld: 
  "\<lbrakk>rank_skew_invar q1; rank_skew_invar q2\<rbrakk> \<Longrightarrow> rank_skew_invar (meld q1 q2)"
  by (simp only: meld_def rank_meldUniq rank_uniqify rank_invar_rank_skew)

theorem meld_invar: 
  "\<lbrakk>invar bq1; invar bq2\<rbrakk> 
  \<Longrightarrow> invar (meld bq1 bq2)"
  by (metis meld_queue_invar rank_meld invar_def)


theorem meld_correct:
  assumes I: "invar q" "invar q'"
  shows 
  "invar (meld q q')"
  "queue_to_multiset (meld q q') = queue_to_multiset q + queue_to_multiset q'"
  using meld_invar[of q q'] meld_mset[of q q'] I
  unfolding invar_def by simp_all


subsubsection "Find Minimal Element"
text \<open>Find the tree containing the minimal element.\<close>
fun getMinTree :: "('e, 'a::linorder) SkewBinomialQueue \<Rightarrow> 
  ('e, 'a) SkewBinomialTree" where
  "getMinTree [t] = t" |
  "getMinTree (t#bq) =
    (if prio t \<le> prio (getMinTree bq)
      then t
      else (getMinTree bq))"

text \<open>Find the minimal Element in the queue.\<close>
definition findMin :: "('e, 'a::linorder) SkewBinomialQueue \<Rightarrow> ('e \<times> 'a)" where
  "findMin bq = (let min = getMinTree bq in (val min, prio min))"

lemma mintree_exists: "(bq \<noteq> []) = (getMinTree bq \<in> set bq)"
proof (induct bq)
  case Nil
  then show ?case by simp
next
  case (Cons _ bq)
  then show ?case by (cases bq) simp_all
qed

lemma treehead_in_multiset: 
  "t \<in> set bq \<Longrightarrow> (val t, prio t) \<in># (queue_to_multiset bq)"
  by (induct bq, simp, cases t, auto)

lemma heap_ordered_single: 
  "heap_ordered t = (\<forall>x \<in> set_mset (tree_to_multiset t). prio t \<le> snd x)"
  by (cases t) auto

lemma getMinTree_cons: 
  "prio (getMinTree (y # x # xs)) \<le> prio (getMinTree (x # xs))" 
  by (induct xs rule: getMinTree.induct) simp_all 

lemma getMinTree_min_tree: "t \<in> set bq  \<Longrightarrow> prio (getMinTree bq) \<le> prio t"
  by (induct bq arbitrary: t rule: getMinTree.induct) (simp, fastforce, simp)

lemma getMinTree_min_prio:
  assumes "queue_invar bq"
    and "y \<in> set_mset (queue_to_multiset bq)"
  shows "prio (getMinTree bq) \<le> snd y"
proof -
  from assms have "bq \<noteq> []" by (cases bq) simp_all
  with assms have "\<exists>t \<in> set bq. (y \<in> set_mset (tree_to_multiset t))"
  proof (induct bq)
    case Nil
    then show ?case by simp
  next
    case (Cons a bq)
    then show ?case
    apply (cases "y \<in> set_mset (tree_to_multiset a)") 
    apply simp
    apply (cases bq)
    apply simp_all
    done
  qed
  from this obtain t where O: 
    "t \<in> set bq"
    "y \<in> set_mset ((tree_to_multiset t))" by blast
  obtain e a r ts where [simp]: "t = (Node e a r ts)" by (cases t) blast
  from O assms(1) have inv: "tree_invar t" by simp
  from tree_invar_heap_ordered[OF inv] heap_ordered.simps[of e a r ts] O
  have "prio t \<le> snd y" by auto
  with getMinTree_min_tree[OF O(1)] show ?thesis by simp
qed

lemma findMin_mset:
  assumes I: "queue_invar q"
  assumes NE: "q\<noteq>Nil"
  shows "findMin q \<in># queue_to_multiset q"
  "\<forall>y\<in>set_mset (queue_to_multiset q). snd (findMin q) \<le> snd y"
proof -
  from NE have "getMinTree q \<in> set q" by (simp only: mintree_exists)
  thus "findMin q \<in># queue_to_multiset q" 
    by (simp add: treehead_in_multiset findMin_def Let_def)
  show "\<forall>y\<in>set_mset (queue_to_multiset q). snd (findMin q) \<le> snd y"
    by (simp add: getMinTree_min_prio findMin_def Let_def NE I)
qed  

theorem findMin_correct:
  assumes I: "invar q"
  assumes NE: "q\<noteq>Nil"
  shows "findMin q \<in># queue_to_multiset q"
  "\<forall>y\<in>set_mset (queue_to_multiset q). snd (findMin q) \<le> snd y"
  using I NE findMin_mset
  unfolding invar_def by auto

subsubsection "Delete Minimal Element"

text \<open>Insert the roots of a given queue into an other queue.\<close>
fun insertList :: 
  "('e, 'a::linorder) SkewBinomialQueue \<Rightarrow> ('e, 'a) SkewBinomialQueue \<Rightarrow> 
   ('e, 'a) SkewBinomialQueue" where
  "insertList [] tbq = tbq" |
  "insertList (t#bq) tbq = insertList bq (insert (val t) (prio t) tbq)"

text \<open>Remove the first tree, which has the priority $a$ within his root.\<close>
fun remove1Prio :: "'a \<Rightarrow> ('e, 'a::linorder) SkewBinomialQueue \<Rightarrow>
  ('e, 'a) SkewBinomialQueue" where
  "remove1Prio a [] = []" |
  "remove1Prio a (t#bq) = 
  (if (prio t) = a then bq else t # (remove1Prio a bq))"

lemma remove1Prio_remove1[simp]: 
  "remove1Prio (prio (getMinTree bq)) bq = remove1 (getMinTree bq) bq"
proof (induct bq)
  case Nil thus ?case by simp
next
  case (Cons t bq) 
  note iv = Cons
  thus ?case
  proof (cases "t = getMinTree (t # bq)")
    case True
    with iv show ?thesis by simp
  next
    case False
    hence ne: "bq \<noteq> []" by auto
    with False have down: "getMinTree (t # bq) = getMinTree bq" 
      by (induct bq rule: getMinTree.induct) auto
    from ne False have "prio t \<noteq> prio (getMinTree bq)" 
      by (induct bq rule: getMinTree.induct) auto
    with down iv False ne show ?thesis by simp 
  qed
qed

text \<open>Return the queue without the minimal element found by findMin\<close>
definition deleteMin :: "('e, 'a::linorder) SkewBinomialQueue \<Rightarrow> 
  ('e, 'a) SkewBinomialQueue" where
  "deleteMin bq = (let min = getMinTree bq in insertList
    (filter (\<lambda> t. rank t = 0) (children min))
    (meld (rev (filter (\<lambda> t. rank t > 0) (children min))) 
     (remove1Prio (prio min) bq)))"

lemma invar_rev[simp]: "queue_invar (rev q) \<longleftrightarrow> queue_invar q"
  by (unfold queue_invar_def) simp

lemma invar_remove1: "queue_invar q \<Longrightarrow> queue_invar (remove1 t q)" 
  by (unfold queue_invar_def) (auto)

lemma mset_rev: "queue_to_multiset (rev q) = queue_to_multiset q"
  by (induct q) (auto simp add: union_ac)

lemma in_set_subset: "t \<in> set q \<Longrightarrow> tree_to_multiset t \<subseteq># queue_to_multiset q"
proof (induct q)
  case Nil
  then show ?case by simp
next
  case (Cons a q)
  show ?case
  proof (cases "t = a")
    case True
    then show ?thesis by simp
  next
    case False
    with Cons have t_in_q: "t \<in> set q" by simp
    have "queue_to_multiset q \<subseteq># queue_to_multiset (a # q)"
      by simp
    from subset_mset.order_trans[OF Cons(1)[OF t_in_q] this] show ?thesis .
  qed
qed

lemma mset_remove1: "t \<in> set q \<Longrightarrow> 
  queue_to_multiset (remove1 t q) = 
  queue_to_multiset q - tree_to_multiset t"
by (induct q) (auto simp: in_set_subset)

lemma invar_children':
  assumes "tree_invar t"
  shows "queue_invar (children t)"
proof (cases t)
  case (Node e a nat list)
  with assms have inv: "tree_invar (Node e a nat list)" by simp
  from Node invar_children[OF inv] show ?thesis by simp
qed

lemma invar_filter: "queue_invar q \<Longrightarrow> queue_invar (filter f q)" 
  by (unfold queue_invar_def) simp
  
lemma insertList_queue_invar: "queue_invar q \<Longrightarrow> queue_invar (insertList ts q)"
proof (induct ts arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons a q)
  note inv_insert = insert_queue_invar[OF Cons(2), of "val a" "prio a"]
  from Cons(1)[OF inv_insert] show ?case by simp
qed

lemma deleteMin_queue_invar: 
  "\<lbrakk>queue_invar q; queue_to_multiset q \<noteq> {#}\<rbrakk> \<Longrightarrow> 
  queue_invar (deleteMin q)"
  unfolding deleteMin_def Let_def
proof goal_cases
  case prems: 1
  from prems(2) have q_ne: "q \<noteq> []" by auto
  with prems(1) mintree_exists[of q]
  have inv_min: "tree_invar (getMinTree q)" by simp
  note inv_rem = invar_remove1[OF prems(1), of "getMinTree q"]
  note inv_children = invar_children'[OF inv_min]
  note inv_filter = invar_filter[OF inv_children, of "\<lambda>t. 0 < rank t"]
  note inv_rev = iffD2[OF invar_rev inv_filter]
  note inv_meld = meld_queue_invar[OF inv_rev inv_rem]
  note inv_ins = 
    insertList_queue_invar[OF inv_meld, 
      of "[t\<leftarrow>children (getMinTree q). rank t = 0]"]
  then show ?case by simp
qed

lemma mset_children: "queue_to_multiset (children t) = 
  tree_to_multiset t - {# (val t, prio t) #}"
  by(cases t, auto)

lemma mset_insertList: 
  "\<lbrakk>\<forall>t \<in> set ts. rank t = 0 \<and> children t = [] ; queue_invar q\<rbrakk> \<Longrightarrow> 
  queue_to_multiset (insertList ts q) = 
  queue_to_multiset ts + queue_to_multiset q"
proof (induct ts arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  from Cons(2) have ball_ts: "\<forall>t\<in>set ts. rank t = 0 \<and> children t = []" by simp
  note inv_insert = insert_queue_invar[OF Cons(3), of "val a" "prio a"]
  note iv = Cons(1)[OF ball_ts inv_insert]
  from Cons(2) have mset_a: "tree_to_multiset a = {# (val a, prio a)#}"
    by (cases a) simp
  note insert_mset[OF Cons(3), of "val a" "prio a"]
  with mset_a iv show ?case by (simp add: union_ac)
qed
        
lemma mset_filter: "(queue_to_multiset [t\<leftarrow>q . rank t = 0]) +
  queue_to_multiset [t\<leftarrow>q . 0 < rank t] =
  queue_to_multiset q"
  by (induct q) (auto simp add: union_ac)

lemma deleteMin_mset:
  assumes "queue_invar q"
    and "queue_to_multiset q \<noteq> {#}"
  shows "queue_to_multiset (deleteMin q) = queue_to_multiset q - {# (findMin q) #}"
proof -
  from assms(2) have q_ne: "q \<noteq> []" by auto
  with mintree_exists[of q]
  have min_in_q: "getMinTree q \<in> set q" by simp
  with assms(1) have inv_min: "tree_invar (getMinTree q)" by simp
  note inv_rem = invar_remove1[OF assms(1), of "getMinTree q"]
  note inv_children = invar_children'[OF inv_min]
  note inv_filter = invar_filter[OF inv_children, of "\<lambda>t. 0 < rank t"]
  note inv_rev = iffD2[OF invar_rev inv_filter]
  note inv_meld = meld_queue_invar[OF inv_rev inv_rem]
  note mset_rem = mset_remove1[OF min_in_q]
  note mset_rev = mset_rev[of "[t\<leftarrow>children (getMinTree q). 0 < rank t]"]
  note mset_meld = meld_mset[OF inv_rev inv_rem]
  note mset_children = mset_children[of "getMinTree q"]
  thm mset_insertList[of "[t\<leftarrow>children (getMinTree q) .
             rank t = 0]"]
  have "\<lbrakk>tree_invar t; rank t = 0\<rbrakk> \<Longrightarrow> children t = []" for t
    by (cases t) simp
  with inv_children 
  have ball_min: "\<forall>t\<in>set [t\<leftarrow>children (getMinTree q). rank t = 0]. 
    rank t = 0 \<and> children t = []" by (unfold queue_invar_def) auto
  note mset_insertList = mset_insertList[OF ball_min inv_meld]
  note mset_filter = mset_filter[of "children (getMinTree q)"]
  let ?Q = "queue_to_multiset q"
  let ?MT = "tree_to_multiset (getMinTree q)"
  from q_ne have head_subset_min: 
    "{# (val (getMinTree q), prio (getMinTree q)) #} \<subseteq># ?MT"
    by(cases "getMinTree q") simp
  note min_subset_q = in_set_subset[OF min_in_q]
  from mset_insertList mset_meld mset_rev mset_rem mset_filter mset_children
    multiset_diff_union_assoc[OF head_subset_min, of "?Q - ?MT"]
    mset_subset_eq_multiset_union_diff_commute[OF min_subset_q, of "?MT"]
  show ?thesis 
    by (auto simp add: deleteMin_def Let_def union_ac findMin_def)
qed

lemma rank_insertList: "rank_skew_invar q \<Longrightarrow> rank_skew_invar (insertList ts q)"
  by (induct ts arbitrary: q) (simp_all add: insert_rank_invar) 

lemma insertList_invar: "invar q \<Longrightarrow> invar (insertList ts q)"
proof (induct ts arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons a q)
  show ?case
    apply (unfold insertList.simps)
  proof goal_cases
    case 1
    from Cons(2) insert_rank_invar[of "q" "val a" "prio a"]
    have a1: "rank_skew_invar (insert (val a) (prio a) q)" 
      by (simp add: invar_def)
    from Cons(2) insert_queue_invar[of "q" "val a" "prio a"]
    have a2: "queue_invar (insert (val a) (prio a) q)" by (simp add: invar_def)
    from a1 a2 have "invar (insert (val a) (prio a) q)" by (simp add: invar_def)
    with Cons(1)[of "(insert (val a) (prio a) q)"] show ?case .
  qed
qed

lemma children_rank_less:
  assumes "tree_invar t"
  shows "\<forall>t' \<in> set (children t). rank t' < rank t"
proof (cases t)
  case (Node e a nat list)
  with assms show ?thesis
  proof (induct nat arbitrary: t e a list) 
    case 0
    then show ?case by simp
  next
    case (Suc nat)
    then obtain e1 a1 ts1 e2 a2 ts2 e' a' where 
      O: "tree_invar (Node e1 a1 nat ts1)"  "tree_invar (Node e2 a2 nat ts2)"
      "t = link (Node e1 a1 nat ts1) (Node e2 a2 nat ts2) 
       \<or> t = skewlink e' a' (Node e1 a1 nat ts1) (Node e2 a2 nat ts2)" 
      by (simp only: tree_invar.simps) blast
    hence ch_id:
      "children t = (if a1 \<le> a2 then (Node e2 a2 nat ts2)#ts1 
                     else (Node e1 a1 nat ts1)#ts2) \<or>
      children t = 
        (if a' \<le> a1 \<and> a' \<le> a2 then [(Node e1 a1 nat ts1), (Node e2 a2 nat ts2)]
         else (if a1 \<le> a2 then (Node e' a' 0 []) # (Node e2 a2 nat ts2) # ts1
         else (Node e' a' 0 []) # (Node e1 a1 nat ts1) # ts2))" 
      by auto
    from O Suc(1)[of "Node e1 a1 nat ts1" "e1" "a1" "ts1"] 
    have  p1: "\<forall>t'\<in>set ((Node e2 a2 nat ts2) # ts1). rank t' < Suc nat" by auto
    from O Suc(1)[of "Node e2 a2 nat ts2" "e2" "a2" "ts2"] 
    have p2: "\<forall>t'\<in>set ((Node e1 a1 nat ts1) # ts2). rank t' < Suc nat" by auto
    from O have 
      p3: "\<forall>t' \<in> set [(Node e1 a1 nat ts1), (Node e2 a2 nat ts2)]. 
                 rank t' < Suc nat" by simp
    from O Suc(1)[of "Node e1 a1 nat ts1" "e1" "a1" "ts1"] 
    have 
      p4: "\<forall>t' \<in> set ((Node e' a' 0 []) # (Node e2 a2 nat ts2) # ts1). 
                 rank t' < Suc nat" by auto
    from O Suc(1)[of "Node e2 a2 nat ts2" "e2" "a2" "ts2"] 
    have p5: 
      "\<forall>t' \<in> set ((Node e' a' 0 []) # (Node e1 a1 nat ts1) # ts2). 
                 rank t' < Suc nat" by auto
    from Suc(3) p1 p2 p3 p4 p5 ch_id show ?case 
      by(cases "children t = (if a1 \<le> a2 then Node e2 a2 nat ts2 # ts1 
                              else Node e1 a1 nat ts1 # ts2)") simp_all
  qed
qed

lemma strong_rev_children:
  assumes "tree_invar t"
  shows "invar (rev [t \<leftarrow> children t. 0 < rank t])"
proof (cases t)
  case (Node e a nat list)
  with assms show ?thesis
  proof (induct "nat" arbitrary: t e a list)
    case 0
    then show ?case by (simp add: invar_def)
  next
    case (Suc nat)
    show ?case
    proof (cases "nat")
      case 0
      with Suc obtain e1 a1 e2 a2 e' a' where 
        O: "tree_invar (Node e1 a1 0 [])" "tree_invar (Node e2 a2 0 [])"
        "t = link (Node e1 a1 0 []) (Node e2 a2 0 []) 
        \<or> t = skewlink e' a' (Node e1 a1 0 []) (Node e2 a2 0 [])" 
        by (simp only: tree_invar.simps) blast
      hence "[t \<leftarrow> children t. 0 < rank t] = []" by auto
      then show ?thesis by (simp add: invar_def)
    next
      case Suc': (Suc n)
      from Suc obtain e1 a1 ts1 e2 a2 ts2 e' a' where 
        O: "tree_invar (Node e1 a1 nat ts1)" "tree_invar (Node e2 a2 nat ts2)"
        "t = link (Node e1 a1 nat ts1) (Node e2 a2 nat ts2) 
        \<or> t = skewlink e' a' (Node e1 a1 nat ts1) (Node e2 a2 nat ts2)" 
        by (simp only: tree_invar.simps) blast
      hence ch_id: 
        "children t = (if a1 \<le> a2 then 
          (Node e2 a2 nat ts2)#ts1 
        else (Node e1 a1 nat ts1)#ts2) 
        \<or> 
        children t = (if a' \<le> a1 \<and> a' \<le> a2 then 
          [(Node e1 a1 nat ts1), (Node e2 a2 nat ts2)]
        else (if a1 \<le> a2 then 
          (Node e' a' 0 []) # (Node e2 a2 nat ts2) # ts1
        else (Node e' a' 0 []) # (Node e1 a1 nat ts1) # ts2))" 
        by auto 
      from O Suc(1)[of "Node e1 a1 nat ts1" "e1" "a1" "ts1"] have 
        rev_ts1: "invar (rev [t \<leftarrow> ts1. 0 < rank t])" by simp
      from O children_rank_less[of "Node e1 a1 nat ts1"] have
        "\<forall>t\<in>set (rev [t \<leftarrow> ts1. 0 < rank t]). rank t < rank (Node e2 a2 nat ts2)"
        by simp
      with O rev_ts1 
        invar_app_single[of "rev [t \<leftarrow> ts1. 0 < rank t]" 
                                  "Node e2 a2 nat ts2"]  
      have 
        "invar (rev ((Node e2 a2 nat ts2) # [t \<leftarrow> ts1. 0 < rank t]))" 
        by simp
      with Suc' have p1: "invar (rev [t \<leftarrow> ((Node e2 a2 nat ts2) # ts1). 0 < rank t])"
        by simp
      from O Suc(1)[of "Node e2 a2 nat ts2" "e2" "a2" "ts2"]
      have rev_ts2: "invar (rev [t \<leftarrow> ts2. 0 < rank t])" by simp
      from O children_rank_less[of "Node e2 a2 nat ts2"]
      have "\<forall>t\<in>set (rev [t \<leftarrow> ts2. 0 < rank t]). 
        rank t < rank (Node e1 a1 nat ts1)" by simp
      with O rev_ts2 invar_app_single[of "rev [t \<leftarrow> ts2. 0 < rank t]" 
                                         "Node e1 a1 nat ts1"] 
      have "invar (rev [t \<leftarrow> ts2. 0 < rank t] @ [Node e1 a1 nat ts1])"
        by simp
      with Suc' have p2: "invar (rev [t \<leftarrow> ((Node e1 a1 nat ts1) # ts2). 0 < rank t])" 
        by simp
      from O(1-2)
      have p3: "invar (rev (filter (\<lambda> t. 0 < rank t)
                                 [(Node e1 a1 nat ts1), (Node e2 a2 nat ts2)]))" 
        by (simp add: invar_def)
      from p1 have p4: "invar (rev 
           [t \<leftarrow> ((Node e' a' 0 []) # (Node e2 a2 nat ts2) # ts1). 0 < rank t])"
        by simp
      from p2 have p5: "invar (rev 
           [t \<leftarrow> ((Node e' a' 0 []) # (Node e1 a1 nat ts1) # ts2). 0 < rank t])"
        by simp
      from p1 p2 p3 p4 p5 ch_id show 
        "invar (rev [t\<leftarrow>children t . 0 < rank t])"
        by (cases "children t = (if a1 \<le> a2 then (Node e2 a2 nat ts2)#ts1 
                                else (Node e1 a1 nat ts1)#ts2)") metis+
    qed
  qed
qed

lemma first_less: "rank_invar (t # bq) \<Longrightarrow> \<forall>t' \<in> set bq. rank t < rank t'" 
  apply(induct bq arbitrary: t) 
  apply (simp)
  apply (metis List.set_simps(2) insert_iff not_le_imp_less 
    not_less_iff_gr_or_eq order_less_le_trans rank_invar.simps(3) 
    rank_invar_cons_down)
  done

lemma first_less_eq: 
  "rank_skew_invar (t # bq) \<Longrightarrow> \<forall>t' \<in> set bq. rank t \<le> rank t'" 
  apply(induct bq arbitrary: t) 
  apply (simp)
  apply (metis List.set_simps(2) insert_iff le_trans
    rank_invar_rank_skew rank_skew_invar.simps(3) rank_skew_rank_invar)
  done

lemma remove1_tail_invar: "tail_invar bq \<Longrightarrow> tail_invar (remove1 t bq)" 
proof (induct bq arbitrary: t) 
  case Nil
  then show ?case by simp
next
  case (Cons a bq)
  show ?case 
  proof (cases "t = a")
    case True
    from Cons(2) have "tail_invar bq" by (rule tail_invar_cons_down)
    with True show ?thesis by simp
  next
    case False
    from Cons(2) have "tail_invar bq" by (rule tail_invar_cons_down)
    with Cons(1)[of "t"] have si1: "tail_invar (remove1 t bq)" .
    from False have "tail_invar (remove1 t (a # bq)) = tail_invar (a # (remove1 t bq))" 
      by simp
    show ?thesis
    proof (cases "remove1 t bq")
      case Nil
      with si1 Cons(2) False show ?thesis by (simp add: tail_invar_def)
    next
      case Cons': (Cons aa list)
      from Cons(2) have "tree_invar a" by (simp add: tail_invar_def)
      from Cons(2) first_less[of "a" "bq"]
      have "\<forall>t \<in> set (remove1 t bq). rank a < rank t"
        by (metis notin_set_remove1 tail_invar_def) 
      with Cons' have "rank a < rank aa" by simp
      with si1 Cons(2) False Cons' tail_invar_cons_up[of "aa" "list" "a"] show ?thesis
        by (simp add: tail_invar_def)
    qed
  qed
qed

lemma invar_cons_down: "invar (t # bq) \<Longrightarrow> invar bq"
  by (metis rank_invar_rank_skew tail_invar_def 
    invar_def invar_tail_invar) 

lemma remove1_invar: "invar bq \<Longrightarrow> invar (remove1 t bq)" 
proof (induct bq arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons a bq)
  show ?case
  proof (cases "t = a")
    case True
    from Cons(2) have "invar bq" by (rule invar_cons_down)
    with True show ?thesis by simp
  next
    case False
    from Cons(2) have "invar bq" by (rule invar_cons_down)
    with Cons(1)[of "t"] have si1: "invar (remove1 t bq)" .
    from False have "invar (remove1 t (a # bq)) = invar (a # (remove1 t bq))"
      by simp
    show ?thesis
    proof (cases "remove1 t bq")
      case Nil
      with si1 Cons(2) False show ?thesis by (simp add: invar_def)
    next
      case Cons': (Cons aa list)
      from Cons(2) have ti: "tree_invar a" by (simp add: invar_def)
      from Cons(2) have sbq: "tail_invar bq" by (metis invar_tail_invar)
      hence srm: "tail_invar (remove1 t bq)" by (metis remove1_tail_invar)
      from Cons(2) first_less_eq[of "a" "bq"]
      have "\<forall>t \<in> set (remove1 t bq). rank a \<le> rank t"
        by (metis notin_set_remove1 invar_def) 
      with Cons' have "rank a \<le> rank aa" by simp
      with si1 Cons(2) False Cons' ti srm tail_invar_cons_up_invar[of "aa" "list" "a"] 
      show ?thesis by simp 
    qed
  qed
qed

lemma deleteMin_invar:
  assumes "invar bq"
    and "bq \<noteq> []"
  shows "invar (deleteMin bq)"
proof -
  have eq: "invar (deleteMin bq) = 
    invar (insertList
    (filter (\<lambda> t. rank t = 0) (children (getMinTree bq)))
    (meld (rev (filter (\<lambda> t. rank t > 0) (children (getMinTree bq)))) 
          (remove1 (getMinTree bq) bq)))" 
    by (simp add: deleteMin_def Let_def)
  from assms mintree_exists[of "bq"] have ti: "tree_invar (getMinTree bq)" 
    by (simp add: invar_def queue_invar_def del: queue_invar_simps)
  with strong_rev_children[of "getMinTree bq"] have 
    m1: "invar (rev [t \<leftarrow> children (getMinTree bq). 0 < rank t])" .
  from remove1_invar[of "bq" "getMinTree bq"] assms(1)
  have m2: "invar (remove1 (getMinTree bq) bq)" .
  from meld_invar[of "rev [t \<leftarrow> children (getMinTree bq). 0 < rank t]" 
                     "remove1 (getMinTree bq) bq"] m1 m2
  have "invar (meld (rev [t \<leftarrow> children (getMinTree bq). 0 < rank t]) 
                    (remove1 (getMinTree bq) bq))" .
  with insertList_invar[of 
    "(meld (rev [t\<leftarrow>children (getMinTree bq) . 0 < rank t]) 
           (remove1 (getMinTree bq) bq))" 
    "[t\<leftarrow>children (getMinTree bq) . rank t = 0]"] 
  have "invar
   (insertList
     [t\<leftarrow>children (getMinTree bq) . rank t = 0]
     (meld (rev [t\<leftarrow>children (getMinTree bq) . 0 < rank t])
       (remove1 (getMinTree bq) bq)))" . 
  with eq show ?thesis ..
qed

theorem deleteMin_correct:
  assumes I: "invar q"
    and NE: "q \<noteq> Nil"
  shows "invar (deleteMin q)"
    and "queue_to_multiset (deleteMin q) = queue_to_multiset q - {#findMin q#}"
  apply (rule deleteMin_invar[OF I NE])
  using deleteMin_mset[of q] I NE
  unfolding invar_def
  apply (auto simp add: empty_correct)
  done


(*
fun foldt and foldq where
  "foldt f z (Node e a _ q) = f (foldq f z q) e a" |
  "foldq f z [] = z" |
  "foldq f z (t#q) = foldq f (foldt f z t) q"

lemma fold_plus:
  "foldt ((\<lambda>m e a. m+{#(e,a)#})) zz t + z = foldt ((\<lambda>m e a. m+{#(e,a)#})) (zz+z) t"
  "foldq ((\<lambda>m e a. m+{#(e,a)#})) zz q + z = foldq ((\<lambda>m e a. m+{#(e,a)#})) (zz+z) q"
  apply (induct t and q arbitrary: zz and zz 
    rule: tree_to_multiset_queue_to_multiset.induct)
  apply (auto simp add: union_ac)
  apply (subst union_ac, simp)
  done


lemma to_mset_fold:
  fixes t::"('e,'a::linorder) SkewBinomialTree" and
        q::"('e,'a) SkewBinomialQueue"
  shows
  "tree_to_multiset t = foldt (\<lambda>m e a. m+{#(e,a)#}) {#} t"
  "queue_to_multiset q = foldq (\<lambda>m e a. m+{#(e,a)#}) {#} q"
  apply (induct t and q rule: tree_to_multiset_queue_to_multiset.induct)
  apply (auto simp add: union_ac fold_plus)
  done
*)

lemmas [simp del] = insert.simps 

end

interpretation SkewBinomialHeapStruc: SkewBinomialHeapStruc_loc .


subsection "Bootstrapping"
text \<open>
  In this section, we implement datastructural bootstrapping, to
  reduce the complexity of meld-operations to $O(1)$.
  The bootstrapping also contains a {\em global root}, caching the
  minimal element of the queue, and thus also reducing the complexity of
  findMin-operations to $O(1)$.

  Bootstrapping adds one more level of recursion:
  An {\em element} is an entry and a priority queues of elements.

  In the original paper on skew binomial queues \cite{BrOk96}, higher order 
  functors and recursive structures are used to elegantly implement bootstrapped
  heaps on top of ordinary heaps. However, such concepts are not supported in
  Isabelle/HOL, nor in Standard ML. Hence we have to use the 
  ,,much less clean'' \cite{BrOk96} alternative:  
  We manually specialize the heap datastructure, and re-implement the functions
  on the specialized data structure.

  The correctness proofs are done by defining a mapping from teh specialized to 
  the original data structure, and reusing the correctness statements of the 
  original data structure.
\<close>

subsubsection "Auxiliary"
text \<open>
  We first have to state some auxiliary lemmas and functions, mainly
  about multisets.
\<close>
(* TODO: Some of these should be moved into the multiset library, they are
  marked by *MOVE* *)

text \<open>Finding the preimage of an element\<close>
(*MOVE*)
lemma in_image_msetE:
  assumes "x\<in>#image_mset f M"
  obtains y where "y\<in>#M" "x=f y"
  using assms
  apply (induct M)
  apply simp
  apply (force split: if_split_asm)
  done

text \<open>Very special lemma for images multisets of pairs, where the second
  component is a function of the first component\<close>
lemma mset_image_fst_dep_pair_diff_split:
  "(\<forall>e a. (e,a)\<in>#M \<longrightarrow> a=f e) \<Longrightarrow>
  image_mset fst (M - {#(e, f e)#}) = image_mset fst M - {#e#}"
proof (induct M)
  case empty thus ?case by auto
next
  case (add x M)
  then obtain e' where [simp]: "x=(e',f e')"
    apply (cases x)
    apply (force)
    done

  from add.prems have "\<forall>e a. (e, a) \<in># M \<longrightarrow> a = f e" by simp
  with add.hyps have 
    IH: "image_mset fst (M - {#(e, f e)#}) = image_mset fst M - {#e#}"
    by auto

  show ?case proof (cases "e=e'")
    case True
    thus ?thesis by (simp)
  next
    case False
    thus ?thesis
      by (simp add: IH)
  qed
qed




locale Bootstrapped
begin

subsubsection "Datatype"
text \<open>We manually specialize the binomial tree to contain elements, that, in, 
  turn, may contain trees.
  Note that we specify nodes without explicit priority,
  as the priority is contained in the elements stored in the nodes.
\<close>


datatype ('e, 'a) BsSkewBinomialTree = 
  BsNode (val: "('e, 'a::linorder) BsSkewElem")
        (rank: nat) (children: "('e , 'a) BsSkewBinomialTree list")
and
('e,'a) BsSkewElem =
  Element 'e (eprio: 'a) "('e,'a) BsSkewBinomialTree list"

type_synonym ('e,'a) BsSkewHeap = "unit + ('e,'a) BsSkewElem"
type_synonym ('e,'a) BsSkewBinomialQueue = "('e,'a) BsSkewBinomialTree list"

subsubsection "Specialization Boilerplate"
text \<open>
  In this section, we re-define the functions
  on the specialized priority queues, and show there correctness.
  This is done by defining a mapping to original priority queues,
  and re-using the correctness lemmas proven there.
\<close>

text \<open>Mapping to original binomial trees and queues\<close>
fun bsmapt where
  "bsmapt (BsNode e r q) = SkewBinomialHeapStruc.Node e (eprio e) r (map bsmapt q)"

abbreviation bsmap where
  "bsmap q == map bsmapt q"

text \<open>Invariant and mapping to multiset are defined via the mapping\<close>
abbreviation "invar q == SkewBinomialHeapStruc.invar (bsmap q)"
abbreviation "queue_to_multiset q 
  == image_mset fst (SkewBinomialHeapStruc.queue_to_multiset (bsmap q))"
abbreviation "tree_to_multiset t
  == image_mset fst (SkewBinomialHeapStruc.tree_to_multiset (bsmapt t))"

abbreviation "queue_to_multiset_aux q 
  == (SkewBinomialHeapStruc.queue_to_multiset (bsmap q))"


text \<open>Now starts the re-implementation of the functions\<close>
primrec prio :: "('e, 'a::linorder) BsSkewBinomialTree \<Rightarrow> 'a" where
  "prio (BsNode e r ts) = eprio e"

lemma proj_xlate:
  "val t = SkewBinomialHeapStruc.val (bsmapt t)"
  "prio t = SkewBinomialHeapStruc.prio (bsmapt t)"
  "rank t = SkewBinomialHeapStruc.rank (bsmapt t)"
  "bsmap (children t) = SkewBinomialHeapStruc.children (bsmapt t)"
  "eprio (SkewBinomialHeapStruc.val (bsmapt t)) 
   = SkewBinomialHeapStruc.prio (bsmapt t)"
  apply (case_tac [!] t)
  apply auto
  done

fun  link :: "('e, 'a::linorder) BsSkewBinomialTree 
  \<Rightarrow> ('e, 'a) BsSkewBinomialTree \<Rightarrow> 
  ('e, 'a) BsSkewBinomialTree" where
  "link (BsNode e1 r1 ts1) (BsNode e2 r2 ts2) = 
   (if  eprio e1\<le>eprio e2 
     then (BsNode e1 (Suc r1) ((BsNode e2 r2 ts2)#ts1))
     else (BsNode e2 (Suc r2) ((BsNode e1 r1 ts1)#ts2)))"

text \<open>Link two trees of rank $r$ and a new element to a new tree of 
  rank $r+1$\<close>
fun skewlink :: "('e,'a::linorder) BsSkewElem \<Rightarrow> ('e, 'a) BsSkewBinomialTree \<Rightarrow> 
  ('e, 'a) BsSkewBinomialTree \<Rightarrow> ('e, 'a) BsSkewBinomialTree" where
  "skewlink e t t' = (if eprio e \<le> (prio t) \<and> eprio e \<le> (prio t')
  then (BsNode e (Suc (rank t)) [t,t'])
  else (if (prio t) \<le> (prio t') 
   then 
    BsNode (val t) (Suc (rank t))  (BsNode e 0 [] # t' # children t)
   else 
    BsNode (val t') (Suc (rank t')) (BsNode e 0 [] # t # children t')))"

lemma link_xlate:
  "bsmapt (link t t') = SkewBinomialHeapStruc.link (bsmapt t) (bsmapt t')"
  "bsmapt (skewlink e t t') = 
     SkewBinomialHeapStruc.skewlink e (eprio e) (bsmapt t) (bsmapt t')"
  by (case_tac [!] t, case_tac [!] t') auto


fun ins :: "('e, 'a::linorder) BsSkewBinomialTree \<Rightarrow> 
  ('e, 'a) BsSkewBinomialQueue \<Rightarrow> 
  ('e, 'a) BsSkewBinomialQueue" where
  "ins t [] = [t]" |
  "ins t' (t # bq) =
    (if (rank t') < (rank t) 
      then t' # t # bq 
      else (if (rank t) < (rank t')
        then t # (ins t' bq) 
        else ins (link t' t) bq))"

lemma ins_xlate:
  "bsmap (ins t q) = SkewBinomialHeapStruc.ins (bsmapt t) (bsmap q)"
  by (induct q arbitrary: t) (auto simp add: proj_xlate link_xlate)


text \<open>Insert an element with priority into a queue using skewlinks.\<close>
fun insert :: "('e,'a::linorder) BsSkewElem \<Rightarrow>
  ('e, 'a) BsSkewBinomialQueue \<Rightarrow> 
  ('e, 'a) BsSkewBinomialQueue" where
  "insert e [] = [BsNode e 0 []]" |
  "insert e [t] = [BsNode e 0 [],t]" |
  "insert e (t # t' # bq) =
    (if rank t \<noteq> rank t' 
      then (BsNode e 0 []) # t # t' # bq
      else (skewlink e t t') # bq)"

lemma insert_xlate:
  "bsmap (insert e q) = SkewBinomialHeapStruc.insert e (eprio e) (bsmap q)"
  apply (cases "(e,q)" rule: insert.cases) 
  apply (auto simp add: proj_xlate link_xlate SkewBinomialHeapStruc.insert.simps)
  done

lemma insert_correct:
  assumes I: "invar q"
  shows 
  "invar (insert e q)"
  "queue_to_multiset (insert e q) = queue_to_multiset q + {#(e)#}"
  by (simp_all add: I SkewBinomialHeapStruc.insert_correct insert_xlate)

fun uniqify 
  :: "('e, 'a::linorder) BsSkewBinomialQueue \<Rightarrow> ('e, 'a) BsSkewBinomialQueue" 
  where
  "uniqify [] = []" |
  "uniqify (t#bq) = ins t bq"

fun meldUniq 
  :: "('e, 'a::linorder) BsSkewBinomialQueue \<Rightarrow> ('e,'a) BsSkewBinomialQueue \<Rightarrow>
  ('e, 'a) BsSkewBinomialQueue" where
  "meldUniq [] bq = bq" |
  "meldUniq bq [] = bq" |
  "meldUniq (t1#bq1) (t2#bq2) = (if rank t1 < rank t2 
       then t1 # (meldUniq bq1 (t2#bq2))
       else (if rank t2 < rank t1
              then t2 # (meldUniq (t1#bq1) bq2)
              else ins (link t1 t2) (meldUniq bq1 bq2)))"

definition meld 
  :: "('e, 'a::linorder) BsSkewBinomialQueue \<Rightarrow> ('e, 'a) BsSkewBinomialQueue \<Rightarrow> 
      ('e, 'a) BsSkewBinomialQueue" where
  "meld bq1 bq2 = meldUniq (uniqify bq1) (uniqify bq2)"

lemma uniqify_xlate:
  "bsmap (uniqify q) = SkewBinomialHeapStruc.uniqify (bsmap q)"
  by (cases q) (simp_all add: ins_xlate)

lemma meldUniq_xlate:
  "bsmap (meldUniq q q') = SkewBinomialHeapStruc.meldUniq (bsmap q) (bsmap q')"
  apply (induct q q' rule: meldUniq.induct)
  apply (auto simp add: link_xlate proj_xlate uniqify_xlate ins_xlate)
  done

lemma meld_xlate: 
  "bsmap (meld q q') = SkewBinomialHeapStruc.meld (bsmap q) (bsmap q')"
  by (simp add: meld_def meldUniq_xlate uniqify_xlate 
           SkewBinomialHeapStruc.meld_def)

lemma meld_correct:
  assumes I: "invar q" "invar q'"
  shows 
  "invar (meld q q')"
  "queue_to_multiset (meld q q') = queue_to_multiset q + queue_to_multiset q'"
  by (simp_all add: I SkewBinomialHeapStruc.meld_correct meld_xlate)

fun insertList :: 
  "('e, 'a::linorder) BsSkewBinomialQueue \<Rightarrow> ('e, 'a) BsSkewBinomialQueue \<Rightarrow> 
   ('e, 'a) BsSkewBinomialQueue" where
  "insertList [] tbq = tbq" |
  "insertList (t#bq) tbq = insertList bq (insert (val t) tbq)"

fun remove1Prio :: "'a \<Rightarrow> ('e, 'a::linorder) BsSkewBinomialQueue \<Rightarrow>
  ('e, 'a) BsSkewBinomialQueue" where
  "remove1Prio a [] = []" |
  "remove1Prio a (t#bq) = 
  (if (prio t) = a then bq else t # (remove1Prio a bq))"

fun getMinTree :: "('e, 'a::linorder) BsSkewBinomialQueue \<Rightarrow> 
  ('e, 'a) BsSkewBinomialTree" where
  "getMinTree [t] = t" |
  "getMinTree (t#bq) =
    (if prio t \<le> prio (getMinTree bq)
      then t
      else (getMinTree bq))"

definition findMin 
  :: "('e, 'a::linorder) BsSkewBinomialQueue \<Rightarrow> ('e,'a) BsSkewElem" where
  "findMin bq = val (getMinTree bq)"

definition deleteMin :: "('e, 'a::linorder) BsSkewBinomialQueue \<Rightarrow> 
  ('e, 'a) BsSkewBinomialQueue" where
  "deleteMin bq = (let min = getMinTree bq in insertList
    (filter (\<lambda> t. rank t = 0) (children min))
    (meld (rev (filter (\<lambda> t. rank t > 0) (children min))) 
     (remove1Prio (prio min) bq)))"

lemma insertList_xlate:
  "bsmap (insertList q q') 
  = SkewBinomialHeapStruc.insertList (bsmap q) (bsmap q')"
  apply (induct q arbitrary: q')
  apply (auto simp add: insert_xlate proj_xlate)
  done

lemma remove1Prio_xlate:
  "bsmap (remove1Prio a q) = SkewBinomialHeapStruc.remove1Prio a (bsmap q)"
  by (induct q) (auto simp add: proj_xlate)

lemma getMinTree_xlate:
  "q\<noteq>[] \<Longrightarrow> bsmapt (getMinTree q) = SkewBinomialHeapStruc.getMinTree (bsmap q)"
  apply (induct q)
  apply simp
  apply (case_tac q)
  apply (auto simp add: proj_xlate)
  done

lemma findMin_xlate: 
  "q\<noteq>[] \<Longrightarrow> findMin q = fst (SkewBinomialHeapStruc.findMin (bsmap q))"
  apply (unfold findMin_def SkewBinomialHeapStruc.findMin_def)
  apply (simp add: proj_xlate Let_def getMinTree_xlate)
  done

lemma findMin_xlate_aux: 
  "q\<noteq>[] \<Longrightarrow> (findMin q, eprio (findMin q)) = 
  (SkewBinomialHeapStruc.findMin (bsmap q))"
  apply (unfold findMin_def SkewBinomialHeapStruc.findMin_def)
  apply (simp add: proj_xlate Let_def getMinTree_xlate)
  apply (induct q)
  apply simp
  apply (case_tac q)
  apply (auto simp add: proj_xlate)
  done
  
(* TODO: Also possible in generic formulation. Then a candidate for Misc.thy *)
lemma bsmap_filter_xlate:
  "bsmap [ x\<leftarrow>l . P (bsmapt x) ] = [ x \<leftarrow> bsmap l. P x ]"
  by (induct l) auto

lemma bsmap_rev_xlate:
  "bsmap (rev q) = rev (bsmap q)"
  by (induct q) auto

lemma deleteMin_xlate:
  "q\<noteq>[] \<Longrightarrow> bsmap (deleteMin q) = SkewBinomialHeapStruc.deleteMin (bsmap q)"
  apply (simp add: 
    deleteMin_def SkewBinomialHeapStruc.deleteMin_def
    proj_xlate getMinTree_xlate insertList_xlate meld_xlate remove1Prio_xlate
    Let_def bsmap_rev_xlate, (subst bsmap_filter_xlate)?)+
  done


lemma deleteMin_correct_aux:
  assumes I: "invar q"
  assumes NE: "q\<noteq>[]"
  shows 
  "invar (deleteMin q)"
  "queue_to_multiset_aux (deleteMin q) = queue_to_multiset_aux q - 
  {# (findMin q, eprio (findMin q)) #}"
  apply (simp_all add:
    I NE deleteMin_xlate findMin_xlate_aux 
    SkewBinomialHeapStruc.deleteMin_correct)
  done


lemma bsmap_fs_dep:
  "(e,a)\<in>#SkewBinomialHeapStruc.tree_to_multiset (bsmapt t) \<Longrightarrow> a=eprio e"
  "(e,a)\<in>#SkewBinomialHeapStruc.queue_to_multiset (bsmap q) \<Longrightarrow> a=eprio e"
  thm SkewBinomialHeapStruc.tree_to_multiset_queue_to_multiset.induct
  apply (induct "bsmapt t" and "bsmap q" arbitrary: t and q
    rule: SkewBinomialHeapStruc.tree_to_multiset_queue_to_multiset.induct)
  apply auto
  apply (case_tac t)
  apply (auto split: if_split_asm)
  done


lemma bsmap_fs_depD:
  "(e,a)\<in>#SkewBinomialHeapStruc.tree_to_multiset (bsmapt t) 
  \<Longrightarrow> e \<in># tree_to_multiset t \<and> a=eprio e"
  "(e,a)\<in>#SkewBinomialHeapStruc.queue_to_multiset (bsmap q) 
  \<Longrightarrow> e \<in># queue_to_multiset q \<and> a=eprio e"
  by (auto dest: bsmap_fs_dep intro!: image_eqI)

lemma findMin_correct_aux:
  assumes I: "invar q"
  assumes NE: "q\<noteq>[]"
  shows "(findMin q, eprio (findMin q)) \<in># queue_to_multiset_aux q"
  "\<forall>y\<in>set_mset (queue_to_multiset_aux q). snd (findMin q,eprio (findMin q)) \<le> snd y"
  apply (simp_all add:
    I NE findMin_xlate_aux 
    SkewBinomialHeapStruc.findMin_correct)
  done

lemma findMin_correct:
  assumes I: "invar q"
    and NE: "q\<noteq>[]"
  shows "findMin q \<in># queue_to_multiset q"
    and "\<forall>y\<in>set_mset (queue_to_multiset q). eprio (findMin q) \<le> eprio y"
  using findMin_correct_aux[OF I NE]
  apply simp_all
  apply (force dest: bsmap_fs_depD)
  apply auto
proof goal_cases
  case prems: (1 a b)
  from prems(3) have "(a, eprio a) \<in># queue_to_multiset_aux q"
    apply -
    apply (frule bsmap_fs_dep)
    apply simp
    done
  with prems(2)[rule_format, simplified]
  show ?case by auto
qed

lemma deleteMin_correct:
  assumes I: "invar q"
  assumes NE: "q\<noteq>[]"
  shows 
  "invar (deleteMin q)"
  "queue_to_multiset (deleteMin q) = queue_to_multiset q - 
  {# findMin q #}"
  using deleteMin_correct_aux[OF I NE]
  apply simp_all
  apply (rule mset_image_fst_dep_pair_diff_split)
  apply (auto dest: bsmap_fs_dep)
  done


declare insert.simps[simp del]


subsubsection "Bootstrapping: Phase 1"
text \<open>
  In this section, we define the ticked versions
  of the functions, as defined in \cite{BrOk96}.
  These functions work on elements, i.e. only on 
  heaps that contain at least one entry.
  Additionally, we define an invariant for elements, and
  a mapping to multisets of entries, and prove correct
  the ticked functions.
\<close>

primrec findMin' where "findMin' (Element e a q) = (e,a)"
fun meld':: "('e,'a::linorder) BsSkewElem \<Rightarrow> 
  ('e,'a) BsSkewElem \<Rightarrow> ('e,'a) BsSkewElem"
  where "meld' (Element e1 a1 q1) (Element e2 a2 q2) =
  (if a1\<le>a2 then
    Element e1 a1 (insert (Element e2 a2 q2) q1)
   else
    Element e2 a2 (insert (Element e1 a1 q1) q2)
  )"
fun insert' where
  "insert' e a q = meld' (Element e a []) q"
fun deleteMin' where
  "deleteMin' (Element e a q) = (
    case (findMin q) of
      Element ey ay q1 \<Rightarrow>
        Element ey ay (meld q1 (deleteMin q))
  )"

text \<open>
  Size-function for termination proofs
\<close>
fun tree_level and queue_level where
  "tree_level (BsNode (Element _ _ qd) _ q) = 
  max (Suc (queue_level qd)) (queue_level q)" |
  "queue_level [] = (0::nat)" |
  "queue_level (t#q) = max (tree_level t) (queue_level q)"

fun level where
  "level (Element _ _ q) = Suc (queue_level q)"

lemma level_m:
  "x\<in>#tree_to_multiset t \<Longrightarrow> level x < Suc (tree_level t)"
  "x\<in>#queue_to_multiset q \<Longrightarrow> level x < Suc (queue_level q)"
  apply (induct t and q rule: tree_level_queue_level.induct)
  apply (case_tac [!] x)
  apply (auto simp add: less_max_iff_disj)
  done

lemma level_measure:
  "x \<in> set_mset (queue_to_multiset q) \<Longrightarrow> (x,(Element e a q))\<in>measure level"
  "x \<in># (queue_to_multiset q) \<Longrightarrow> (x,(Element e a q))\<in>measure level"
  apply (case_tac [!] x)
  apply (auto dest: level_m simp del: set_image_mset)
  done

text \<open>
  Invariant for elements
\<close>
function elem_invar where
  "elem_invar (Element e a q) \<longleftrightarrow>
  (\<forall>x. x\<in># (queue_to_multiset q) \<longrightarrow> a \<le> eprio x \<and> elem_invar x) \<and> 
  invar q"
  by pat_completeness auto
termination
proof
  show "wf (measure level)" by auto
qed (rule level_measure)


text \<open>
  Abstraction to multisets
\<close>
function elem_to_mset where
  "elem_to_mset (Element e a q) = {# (e,a) #} 
  + Union_mset (image_mset elem_to_mset (queue_to_multiset q))"
by pat_completeness auto
termination
proof
  show "wf (measure level)" by auto
qed (rule level_measure)

lemma insert_correct':
  assumes I: "elem_invar x"
  shows 
  "elem_invar (insert' e a x)"
  "elem_to_mset (insert' e a x) = elem_to_mset x + {#(e,a)#}"
  using I
  apply (case_tac [!] x)
  apply (auto simp add: insert_correct union_ac)
  done

lemma meld_correct':
  assumes I: "elem_invar x" "elem_invar x'"
  shows 
  "elem_invar (meld' x x')"
  "elem_to_mset (meld' x x') = elem_to_mset x + elem_to_mset x'"
  using I
  apply (case_tac [!] x)
  apply (case_tac [!] x')
  apply (auto simp add: insert_correct union_ac)
  done
  
lemma findMin'_min: 
  "\<lbrakk>elem_invar x; y\<in>#elem_to_mset x\<rbrakk> \<Longrightarrow> snd (findMin' x) \<le> snd y"
proof (induct n\<equiv>"level x" arbitrary: x rule: full_nat_induct)
  case 1
  note IH="1.hyps"[rule_format, OF _ refl]
  note PREMS="1.prems"
  obtain e a q where [simp]: "x=Element e a q" by (cases x) auto

  from PREMS(2) have "y=(e,a) \<or> 
    y\<in>#Union_mset (image_mset elem_to_mset (queue_to_multiset q))"
    (is "?C1 \<or> ?C2")
    by (auto split: if_split_asm)
  moreover {
    assume "y=(e,a)"
    with PREMS have ?case by simp
  } moreover {
    assume ?C2
    then obtain yx where 
      A: "yx \<in># queue_to_multiset q"  and
      B: "y \<in># elem_to_mset yx"
      apply (auto elim!: in_image_msetE)
      done
    
    from A PREMS have IYX: "elem_invar yx" by auto

    from PREMS(1) A have "a \<le> eprio yx" by auto
    hence "snd (findMin' x) \<le> snd (findMin' yx)"
      by (cases yx) auto
    also
    from IH[OF _ IYX B] level_m(2)[OF A]
    have "snd (findMin' yx) \<le> snd y" by simp
    finally have ?case .
  } ultimately show ?case by blast
qed
  
lemma findMin_correct':
  assumes I: "elem_invar x"
  shows
  "findMin' x \<in># elem_to_mset x"
  "\<forall>y\<in>set_mset (elem_to_mset x). snd (findMin' x) \<le> snd y"
  using I
  apply (cases x)
  apply simp
  apply (simp add: findMin'_min[OF I])
  done

lemma deleteMin_correct':
  assumes I: "elem_invar (Element e a q)"
  assumes NE[simp]: "q\<noteq>[]"
  shows 
    "elem_invar (deleteMin' (Element e a q))"
    "elem_to_mset (deleteMin' (Element e a q)) = 
       elem_to_mset (Element e a q) - {# findMin' (Element e a q) #}"

proof -
  from I have IQ[simp]: "invar q" by simp
  from findMin_correct[OF IQ NE] have
    FMIQ: "findMin q \<in># queue_to_multiset q" and
    FMIN: "!!y. y\<in>#(queue_to_multiset q) \<Longrightarrow> eprio (findMin q) \<le> eprio y"
    by (auto simp del: set_image_mset)
  from FMIQ I have FMEI: "elem_invar (findMin q)" by auto
  from I have FEI: "!!y. y\<in>#(queue_to_multiset q) \<Longrightarrow> elem_invar y" by auto
  
  obtain ey ay qy where [simp]: "findMin q = Element ey ay qy" 
    by (cases "findMin q") auto
  from FMEI have 
    IQY[simp]: "invar qy" and
    AYMIN: "!!x. x \<in># queue_to_multiset qy \<Longrightarrow> ay \<le> eprio x" and 
    QEI: "!!x. x \<in># queue_to_multiset qy \<Longrightarrow> elem_invar x" 
    by auto

  show "elem_invar (deleteMin' (Element e a q))"
    using AYMIN QEI FMIN FEI
    by (auto simp add: deleteMin_correct meld_correct in_diff_count)

  from FMIQ have 
    S: "(queue_to_multiset q - {#Element ey ay qy#}) + {#Element ey ay qy#} 
    = queue_to_multiset q" by simp

  show "elem_to_mset (deleteMin' (Element e a q)) = 
    elem_to_mset (Element e a q) - {# findMin' (Element e a q) #}"
    apply (simp add: deleteMin_correct meld_correct)
    by (subst S[symmetric], simp add: union_ac)

qed

subsubsection "Bootstrapping: Phase 2"
text \<open>
  In this phase, we extend the ticked versions to also work with
  empty priority queues.
\<close>

definition bs_empty where "bs_empty \<equiv> Inl ()"

primrec bs_findMin where
  "bs_findMin (Inr x) = findMin' x"

fun bs_meld 
  :: "('e,'a::linorder) BsSkewHeap \<Rightarrow> ('e,'a) BsSkewHeap \<Rightarrow> ('e,'a) BsSkewHeap"
  where
  "bs_meld (Inl _) x = x" |
  "bs_meld x (Inl _) = x" |
  "bs_meld (Inr x) (Inr x') = Inr (meld' x x')"
lemma [simp]: "bs_meld x (Inl u) = x" 
  by (cases x) auto

primrec bs_insert 
  :: "'e \<Rightarrow> ('a::linorder) \<Rightarrow> ('e,'a) BsSkewHeap \<Rightarrow> ('e,'a) BsSkewHeap"
  where
  "bs_insert e a (Inl _) = Inr (Element e a [])" |
  "bs_insert e a (Inr x) = Inr (insert' e a x)"

fun bs_deleteMin 
  :: "('e,'a::linorder) BsSkewHeap \<Rightarrow> ('e,'a) BsSkewHeap"
  where
  "bs_deleteMin (Inr (Element e a [])) = Inl ()" |
  "bs_deleteMin (Inr (Element e a q)) = Inr (deleteMin' (Element e a q))"

primrec bs_invar :: "('e,'a::linorder) BsSkewHeap \<Rightarrow> bool"
where
  "bs_invar (Inl _) \<longleftrightarrow> True" |
  "bs_invar (Inr x) \<longleftrightarrow> elem_invar x"

lemma [simp]: "bs_invar bs_empty" by (simp add: bs_empty_def)

primrec bs_to_mset :: "('e,'a::linorder) BsSkewHeap \<Rightarrow> ('e\<times>'a) multiset"
where
  "bs_to_mset (Inl _) = {#}" |
  "bs_to_mset (Inr x) = elem_to_mset x"

theorem bs_empty_correct: "h=bs_empty \<longleftrightarrow> bs_to_mset h = {#}"
  apply (unfold bs_empty_def)
  apply (cases h)
  apply simp
  apply (case_tac b)
  apply simp
  done

lemma bs_mset_of_empty[simp]:
  "bs_to_mset bs_empty = {#}"
  by (simp add: bs_empty_def)

theorem bs_findMin_correct:
  assumes I: "bs_invar h"
  assumes NE: "h\<noteq>bs_empty"
  shows "bs_findMin h \<in># bs_to_mset h"
        "\<forall>y\<in>set_mset (bs_to_mset h). snd (bs_findMin h) \<le> snd y"
  using I NE
  apply (case_tac [!] h)
  apply (auto simp add: bs_empty_def findMin_correct')
  done

theorem bs_insert_correct:
  assumes I: "bs_invar h"
  shows 
  "bs_invar (bs_insert e a h)"
  "bs_to_mset (bs_insert e a h) = {#(e,a)#} + bs_to_mset h"
  using I
  apply (case_tac [!] h)
  apply (simp_all)
  apply (auto simp add: meld_correct')
  done

theorem bs_meld_correct:
  assumes I: "bs_invar h" "bs_invar h'"
  shows 
  "bs_invar (bs_meld h h')"
  "bs_to_mset (bs_meld h h') = bs_to_mset h + bs_to_mset h'"
  using I
  apply (case_tac [!] h, case_tac [!] h')
  apply (auto simp add: meld_correct')
  done

theorem bs_deleteMin_correct:
  assumes I: "bs_invar h"
  assumes NE: "h \<noteq> bs_empty"
  shows 
  "bs_invar (bs_deleteMin h)"
  "bs_to_mset (bs_deleteMin h) = bs_to_mset h - {#bs_findMin h#}"
  using I NE
  apply (case_tac [!] h)
  apply (simp_all add: bs_empty_def)
  apply (case_tac [!] b)
  apply (rename_tac [!] list)
  apply (case_tac [!] list)
  apply (simp_all del: elem_invar.simps deleteMin'.simps add: deleteMin_correct')
  done

end


interpretation BsSkewBinomialHeapStruc: Bootstrapped .


subsection "Hiding the Invariant"

subsubsection "Datatype"
typedef (overloaded) ('e, 'a) SkewBinomialHeap =
  "{q :: ('e,'a::linorder) BsSkewBinomialHeapStruc.BsSkewHeap. BsSkewBinomialHeapStruc.bs_invar q }"
  apply (rule_tac x="BsSkewBinomialHeapStruc.bs_empty" in exI)
  apply (auto)
  done

lemma Rep_SkewBinomialHeap_invar[simp]: 
  "BsSkewBinomialHeapStruc.bs_invar (Rep_SkewBinomialHeap x)"
  using Rep_SkewBinomialHeap
  by (auto)

lemma [simp]: 
  "BsSkewBinomialHeapStruc.bs_invar q 
  \<Longrightarrow> Rep_SkewBinomialHeap (Abs_SkewBinomialHeap q) = q"
  using Abs_SkewBinomialHeap_inverse by auto

lemma [simp, code abstype]: "Abs_SkewBinomialHeap (Rep_SkewBinomialHeap q) = q"
  by (rule Rep_SkewBinomialHeap_inverse)

locale SkewBinomialHeap_loc
begin
  subsubsection "Operations"

  definition [code]: 
    "to_mset t 
    == BsSkewBinomialHeapStruc.bs_to_mset (Rep_SkewBinomialHeap t)"

  definition empty where 
    "empty == Abs_SkewBinomialHeap BsSkewBinomialHeapStruc.bs_empty" 
  lemma [code abstract, simp]: 
    "Rep_SkewBinomialHeap empty = BsSkewBinomialHeapStruc.bs_empty"
    by (unfold empty_def) simp

  definition [code]: 
    "isEmpty q == Rep_SkewBinomialHeap q = BsSkewBinomialHeapStruc.bs_empty"
  lemma empty_rep: 
    "q=empty \<longleftrightarrow> Rep_SkewBinomialHeap q = BsSkewBinomialHeapStruc.bs_empty"
    apply (auto simp add: empty_def)
    apply (metis Rep_SkewBinomialHeap_inverse)
    done

  lemma isEmpty_correct: "isEmpty q \<longleftrightarrow> q=empty"
    by (simp add: empty_rep isEmpty_def)
  
  definition 
    insert 
    :: "'e  \<Rightarrow> ('a::linorder) \<Rightarrow> ('e,'a) SkewBinomialHeap 
        \<Rightarrow> ('e,'a) SkewBinomialHeap"
    where "insert e a q == 
            Abs_SkewBinomialHeap (
              BsSkewBinomialHeapStruc.bs_insert e a (Rep_SkewBinomialHeap q))"
  lemma [code abstract]: 
    "Rep_SkewBinomialHeap (insert e a q) 
    = BsSkewBinomialHeapStruc.bs_insert e a (Rep_SkewBinomialHeap q)"
    by (simp add: insert_def BsSkewBinomialHeapStruc.bs_insert_correct)

  definition [code]: "findMin q 
    == BsSkewBinomialHeapStruc.bs_findMin (Rep_SkewBinomialHeap q)"
  
  definition "deleteMin q == 
    if q=empty then empty 
    else Abs_SkewBinomialHeap (
            BsSkewBinomialHeapStruc.bs_deleteMin (Rep_SkewBinomialHeap q))"

  text \<open>
    We don't use equality here, to prevent the code-generator
    from introducing equality-class parameter for type \<open>'a\<close>.
    Instead we use a case-distinction to check for emptiness.
\<close>
  lemma [code abstract]: "Rep_SkewBinomialHeap (deleteMin q) =
    (case (Rep_SkewBinomialHeap q) of Inl _ \<Rightarrow> BsSkewBinomialHeapStruc.bs_empty |
     _ \<Rightarrow> BsSkewBinomialHeapStruc.bs_deleteMin (Rep_SkewBinomialHeap q))"
  proof (cases "(Rep_SkewBinomialHeap q)")
    case [simp]: (Inl a)
    hence "(Rep_SkewBinomialHeap q) = BsSkewBinomialHeapStruc.bs_empty"
      apply (cases q) 
      apply (auto simp add: BsSkewBinomialHeapStruc.bs_empty_def)
      done
    thus ?thesis
      apply (auto simp add: deleteMin_def 
        BsSkewBinomialHeapStruc.bs_deleteMin_correct 
        BsSkewBinomialHeapStruc.bs_empty_correct empty_rep )
      done
  next
    case (Inr x)
    hence "(Rep_SkewBinomialHeap q) \<noteq> BsSkewBinomialHeapStruc.bs_empty"
      apply (cases q) 
      apply (auto simp add: BsSkewBinomialHeapStruc.bs_empty_def)
      done
    thus ?thesis
      apply (simp add: Inr)
      apply (fold Inr)
      apply (auto simp add: deleteMin_def 
        BsSkewBinomialHeapStruc.bs_deleteMin_correct 
        BsSkewBinomialHeapStruc.bs_empty_correct empty_rep )
      done
  qed

(*
  lemma [code abstract]: "Rep_SkewBinomialHeap (deleteMin q) =
    (if (Rep_SkewBinomialHeap q = BsSkewBinomialHeapStruc.bs_empty) then BsSkewBinomialHeapStruc.bs_empty 
     else BsSkewBinomialHeapStruc.bs_deleteMin (Rep_SkewBinomialHeap q))"
    by (auto simp add: deleteMin_def BsSkewBinomialHeapStruc.bs_deleteMin_correct 
      BsSkewBinomialHeapStruc.bs_empty_correct empty_rep)
*)

  definition "meld q1 q2 == 
    Abs_SkewBinomialHeap (BsSkewBinomialHeapStruc.bs_meld 
    (Rep_SkewBinomialHeap q1) (Rep_SkewBinomialHeap q2))"
  lemma [code abstract]:
    "Rep_SkewBinomialHeap (meld q1 q2) 
    = BsSkewBinomialHeapStruc.bs_meld (Rep_SkewBinomialHeap q1) 
                                 (Rep_SkewBinomialHeap q2)"
    by (simp add: meld_def BsSkewBinomialHeapStruc.bs_meld_correct)

  subsubsection "Correctness"

  lemma empty_correct: "to_mset q = {#} \<longleftrightarrow> q=empty"
    by (simp add: to_mset_def BsSkewBinomialHeapStruc.bs_empty_correct empty_rep)

  lemma to_mset_of_empty[simp]: "to_mset empty = {#}"
    by (simp add: empty_correct)

  lemma insert_correct: "to_mset (insert e a q) =  to_mset q + {#(e,a)#}"
    apply (unfold insert_def to_mset_def)
    apply (simp add: BsSkewBinomialHeapStruc.bs_insert_correct union_ac)
    done

  lemma findMin_correct: 
    assumes "q\<noteq>empty"
    shows 
    "findMin q \<in># to_mset q"
    "\<forall>y\<in>set_mset (to_mset q). snd (findMin q) \<le> snd y"
    using assms
    apply (unfold findMin_def to_mset_def)
    apply (simp_all add: empty_rep BsSkewBinomialHeapStruc.bs_findMin_correct)
    done

  lemma deleteMin_correct:
    assumes "q\<noteq>empty"
    shows "to_mset (deleteMin q) = to_mset q - {# findMin q #}"
    using assms
    apply (unfold findMin_def deleteMin_def to_mset_def)
    apply (simp_all add: empty_rep BsSkewBinomialHeapStruc.bs_deleteMin_correct)
    done

  lemma meld_correct:
    shows "to_mset (meld q q') = to_mset q + to_mset q'"
    apply (unfold to_mset_def meld_def)
    apply (simp_all add: BsSkewBinomialHeapStruc.bs_meld_correct)
    done

  text \<open>Correctness lemmas to be used with simplifier\<close>
  lemmas correct = empty_correct deleteMin_correct meld_correct

  end

  interpretation SkewBinomialHeap: SkewBinomialHeap_loc .


subsection "Documentation"

(*#DOC
  fun [no_spec] SkewBinomialHeap.to_mset
    Abstraction to multiset.

  fun SkewBinomialHeap.empty
    The empty heap. ($O(1)$)

  fun SkewBinomialHeap.isEmpty
    Checks whether heap is empty. Mainly used to work around 
    code-generation issues. ($O(1)$)

  fun [long_type] SkewBinomialHeap.insert
    Inserts element ($O(1)$)

  fun SkewBinomialHeap.findMin
    Returns a minimal element ($O(1)$)

  fun [long_type] SkewBinomialHeap.deleteMin
    Deletes {\em the} element that is returned by {\em find\_min}. $O(\log(n))$

  fun [long_type] SkewBinomialHeap.meld
    Melds two heaps ($O(1)$)

*)


text \<open>
   \underline{@{term_type "SkewBinomialHeap.to_mset"}}\\
        Abstraction to multiset.\\


    \underline{@{term_type "SkewBinomialHeap.empty"}}\\
        The empty heap. ($O(1)$)\\
    {\bf Spec} \<open>SkewBinomialHeap.empty_correct\<close>:
    @{thm [display] SkewBinomialHeap.empty_correct[no_vars]}


    \underline{@{term_type "SkewBinomialHeap.isEmpty"}}\\
        Checks whether heap is empty. Mainly used to work around
    code-generation issues. ($O(1)$)\\
    {\bf Spec} \<open>SkewBinomialHeap.isEmpty_correct\<close>:
    @{thm [display] SkewBinomialHeap.isEmpty_correct[no_vars]}


    \underline{@{term "SkewBinomialHeap.insert"}}
    @{term_type [display] "SkewBinomialHeap.insert"}
        Inserts element ($O(1)$)\\
    {\bf Spec} \<open>SkewBinomialHeap.insert_correct\<close>:
    @{thm [display] SkewBinomialHeap.insert_correct[no_vars]}


    \underline{@{term_type "SkewBinomialHeap.findMin"}}\\
        Returns a minimal element ($O(1)$)\\
    {\bf Spec} \<open>SkewBinomialHeap.findMin_correct\<close>:
    @{thm [display] SkewBinomialHeap.findMin_correct[no_vars]}


    \underline{@{term "SkewBinomialHeap.deleteMin"}}
    @{term_type [display] "SkewBinomialHeap.deleteMin"}
        Deletes {\em the} element that is returned by {\em find\_min}. $O(\log(n))$\\
    {\bf Spec} \<open>SkewBinomialHeap.deleteMin_correct\<close>:
    @{thm [display] SkewBinomialHeap.deleteMin_correct[no_vars]}


    \underline{@{term "SkewBinomialHeap.meld"}}
    @{term_type [display] "SkewBinomialHeap.meld"}
        Melds two heaps ($O(1)$)\\
    {\bf Spec} \<open>SkewBinomialHeap.meld_correct\<close>:
    @{thm [display] SkewBinomialHeap.meld_correct[no_vars]}

\<close>


end
