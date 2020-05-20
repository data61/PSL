section "Binomial Heaps"

theory BinomialHeap
imports Main "HOL-Library.Multiset"
begin

locale BinomialHeapStruc_loc
begin

subsection \<open>Datatype Definition\<close>

text \<open>Binomial heaps are lists of binomial trees.\<close>
datatype ('e, 'a) BinomialTree = 
  Node (val: 'e) (prio: "'a::linorder") (rank: nat) (children: "('e , 'a) BinomialTree list")
type_synonym ('e, 'a) BinomialQueue_inv = "('e, 'a::linorder) BinomialTree list"

text \<open>Combine two binomial trees (of rank $r$) to one (of rank $r+1$).\<close>
fun  link :: "('e, 'a::linorder) BinomialTree \<Rightarrow> ('e, 'a) BinomialTree \<Rightarrow> 
  ('e, 'a) BinomialTree" where
  "link (Node e1 a1 r1 ts1) (Node e2 a2 r2 ts2) = 
   (if  a1\<le>a2 
     then (Node e1 a1 (Suc r1) ((Node e2 a2 r2 ts2)#ts1))
     else (Node e2 a2 (Suc r2) ((Node e1 a1 r1 ts1)#ts2)))"


subsubsection "Abstraction to Multiset"
text \<open>Return a multiset with all (element, priority) pairs from a queue.\<close>
fun tree_to_multiset 
  :: "('e, 'a::linorder) BinomialTree \<Rightarrow> ('e \<times> 'a) multiset" 
and queue_to_multiset 
  :: "('e, 'a::linorder) BinomialQueue_inv \<Rightarrow> ('e \<times> 'a) multiset" where
  "tree_to_multiset (Node e a r ts) = {#(e,a)#} + queue_to_multiset ts" |
  "queue_to_multiset [] = {#}" |
  "queue_to_multiset (t#q) = tree_to_multiset t + queue_to_multiset q" 


lemma qtmset_append_union[simp]: "queue_to_multiset (q @ q') = 
  queue_to_multiset q + queue_to_multiset q'"
  apply(induct q)
  apply(simp)
  apply(simp add: union_ac)
done

lemma qtmset_rev[simp]: "queue_to_multiset (rev q) = queue_to_multiset q"
  apply(induct q)
  apply(simp)
  apply(simp add: union_ac)
done

subsubsection "Invariant"

text \<open>We first formulate the invariant for single binomial trees,
  and then extend the invariant to binomial heaps (lists of binomial trees).
  The invariant for trees claims that a tree labeled rank $0$ has no children,
  and a tree labeled rank $r+1$ is the result of a link operation of
  two rank $r$ trees.
\<close>
function tree_invar :: "('e, 'a::linorder) BinomialTree \<Rightarrow> bool" where
  "tree_invar (Node e a 0 ts) = (ts = [])" |
  "tree_invar (Node e a (Suc r) ts) = 
  (\<exists> e1 a1 ts1 e2 a2 ts2. 
    tree_invar (Node e1 a1 r ts1) \<and> 
    tree_invar (Node e2 a2 r ts2) \<and> 
    (Node e a (Suc r) ts) = link (Node e1 a1 r ts1) (Node e2 a2 r ts2))"
by pat_completeness auto
termination
  apply(relation "measure (\<lambda>t. rank t)")
  apply auto
done

text \<open>A queue satisfies the invariant, iff all trees inside the queue satisfy 
  the invariant, and the queue contains only trees of distinct rank and 
  is ordered by rank\<close>

text \<open>First part: All trees of the queue satisfy the tree invariant:\<close>
definition queue_invar :: "('e, 'a::linorder) BinomialQueue_inv \<Rightarrow> bool" where
  "queue_invar q \<equiv> (\<forall>t \<in> set q. tree_invar t)"

text \<open>Second part: Trees have distinct rank, and are ordered by 
  ascending rank:\<close>
fun rank_invar :: "('e, 'a::linorder) BinomialQueue_inv \<Rightarrow> bool" where
  "rank_invar [] = True" |
  "rank_invar [t] = True" |
  "rank_invar (t # t' # bq) = (rank t < rank t' \<and> rank_invar (t' # bq))"

lemma queue_invar_simps[simp]:
  "queue_invar []"
  "queue_invar (t#q) \<longleftrightarrow> tree_invar t \<and> queue_invar q"
  "queue_invar (q@q') \<longleftrightarrow> queue_invar q \<and> queue_invar q'"
  unfolding queue_invar_def by auto

text \<open>Invariant for binomial queues:\<close>
definition "invar q == queue_invar q \<and> rank_invar q"

lemma mset_link[simp]: "(tree_to_multiset (link t1 t2)) 
  = (tree_to_multiset t1) + (tree_to_multiset t2)"
  by(cases t1, cases t2, auto simp add: union_ac)

lemma link_tree_invar: 
  "\<lbrakk>tree_invar t1; tree_invar t2; rank t1 = rank t2\<rbrakk> \<Longrightarrow> tree_invar (link t1 t2)"
  by (cases t1, cases t2, simp, blast)

lemma invar_children: 
  assumes "tree_invar ((Node e a r ts)::(('e, 'a::linorder) BinomialTree))" 
  shows "queue_invar ts" using assms
  unfolding queue_invar_def
proof(induct r arbitrary: e a ts)
  case 0
  then show ?case by simp
next
  case (Suc r)
  from Suc(2) obtain e1 a1 ts1 e2 a2 ts2 where 
    O: "tree_invar (Node e1 a1 r ts1)"  "tree_invar (Node e2 a2 r ts2)" 
    "(Node e a (Suc r) ts) = link (Node e1 a1 r ts1) (Node e2 a2 r ts2)" 
    by (simp only: tree_invar.simps) blast
  from Suc(1)[OF O(1)] O(2)
  have case1: "queue_invar ((Node e2 a2 r ts2) # ts1)" 
    unfolding queue_invar_def by simp
  from Suc(1)[OF O(2)] O(1)
  have case2: "queue_invar ((Node e1 a1 r ts1) # ts2)" 
    unfolding queue_invar_def by simp
  from O(3) have "ts = (if a1\<le>a2 
    then (Node e2 a2 r ts2) # ts1 
    else (Node e1 a1 r ts1) # ts2)" by auto
  with case1 case2 show ?case unfolding queue_invar_def by simp
qed

lemma invar_children': "tree_invar t \<Longrightarrow> queue_invar (children t)"
  by (cases t) (auto simp add: invar_children)


lemma rank_link: "rank t = rank t' \<Longrightarrow> rank (link t t') = rank t + 1"
apply (cases t)
apply (cases t')
apply(auto)
done

lemma rank_invar_not_empty_hd: "\<lbrakk>rank_invar (t # bq); bq \<noteq> []\<rbrakk> \<Longrightarrow> 
  rank t < rank (hd bq)"
apply(induct bq arbitrary: t)
apply(auto)
done

lemma rank_invar_to_set: "rank_invar (t # bq) \<Longrightarrow> 
  \<forall> t' \<in> set bq. rank t < rank t'"
apply(induct bq arbitrary: t)
apply(simp)
apply (metis nat_less_le rank_invar.simps(3) set_ConsD xt1(7))
done

lemma set_to_rank_invar: "\<lbrakk>\<forall> t' \<in> set bq. rank t < rank t'; rank_invar bq\<rbrakk> 
  \<Longrightarrow>  rank_invar (t # bq)"
apply(induct bq arbitrary: t)
apply(simp)
by (metis list.sel(1) hd_in_set list.distinct(1) rank_invar.simps(3))

lemma rank_invar_hd_cons: 
  "\<lbrakk>rank_invar bq; rank t < rank (hd bq)\<rbrakk> \<Longrightarrow> rank_invar (t # bq)"
apply(cases bq)
apply(auto)
done

lemma rank_invar_cons: "rank_invar (t # bq) \<Longrightarrow> rank_invar bq"
apply(cases bq)
apply(auto)
done


lemma invar_cons_up: 
  "\<lbrakk>invar (t # bq); rank t' < rank t; tree_invar t'\<rbrakk> \<Longrightarrow> invar (t' # t # bq)" 
  unfolding invar_def
  by (cases bq) simp_all 

lemma invar_cons_down: "invar (t # bq) \<Longrightarrow> invar bq" 
  unfolding invar_def
  by (cases bq) simp_all

lemma invar_app_single: 
  "\<lbrakk>invar bq; \<forall>t \<in> set bq. rank t < rank t'; tree_invar t'\<rbrakk> 
   \<Longrightarrow> invar (bq @ [t'])" 
proof (induct bq)
  case Nil
  then show ?case by (simp add: invar_def)
next
  case (Cons a bq)
  from \<open>invar (a # bq)\<close> have "invar bq" by (rule invar_cons_down)
  with Cons have "invar (bq @ [t'])" by simp
  with Cons show ?case by (cases bq) (simp_all add: invar_def)
qed

subsubsection "Heap Ordering"
fun heap_ordered :: "('e, 'a::linorder) BinomialTree \<Rightarrow> bool" where
  "heap_ordered (Node e a r ts) = (\<forall>x \<in> set_mset(queue_to_multiset ts). a \<le> snd x)"

text \<open>The invariant for trees implies heap order.\<close>
lemma tree_invar_heap_ordered:
  assumes "tree_invar t"
  shows "heap_ordered t"
proof (cases t)
  case (Node e a nat list)
  with assms show ?thesis
  proof (induct nat arbitrary: t e a list)
    case 0
    then show ?case by simp
  next
    case (Suc nat t)
    then obtain t1 e1 a1 ts1 t2 e2 a2 ts2 where 
      O: "tree_invar t1"  "tree_invar t2" "t = link t1 t2" 
      and t1[simp]: "t1 = (Node e1 a1 nat ts1)" 
      and t2[simp]: "t2 = (Node e2 a2 nat ts2)" 
      by (simp only: tree_invar.simps) blast
    from O(3) have "t = (if  a1\<le>a2 
      then (Node e1 a1 (Suc nat) (t2 # ts1))
      else (Node e2 a2 (Suc nat) (t1 # ts2)))" by simp
    with Suc(1)[OF O(1) t1] Suc(1)[OF O(2) t2]
    show ?case by (cases "a1 \<le> a2") auto
  qed
qed

subsubsection "Height and Length"
text \<open>
  Although complexity of HOL-functions cannot be expressed within 
  HOL, we can express the height and length of a binomial heap.
  By showing that both, height and length, are logarithmic in the number 
  of contained elements, we give strong evidence that our functions have
  logarithmic complexity in the number of elements.
\<close>

text \<open>Height of a tree and queue\<close>
fun height_tree :: "('e, ('a::linorder)) BinomialTree \<Rightarrow> nat" and
    height_queue :: "('e, ('a::linorder)) BinomialQueue_inv \<Rightarrow> nat" 
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

lemma tree_rank_estimate:
  "tree_invar (Node e a r ts) \<Longrightarrow> 
    size (tree_to_multiset (Node e a r ts)) = (2::nat)^r"
proof (induct r arbitrary: e a ts)
  case 0
  then show ?case by simp
next
  case (Suc r)
  from Suc(2) obtain e1 a1 ts1 e2 a2 ts2 where link:
    "(Node e a (Suc r) ts) = link (Node e1 a1 r ts1) (Node e2 a2 r ts2)"
    and inv1: "tree_invar (Node e1 a1 r ts1) "
    and inv2: "tree_invar (Node e2 a2 r ts2)" by simp blast
  from link_length[of "(Node e1 a1 r ts1)" "(Node e2 a2 r ts2)"]
    Suc(1)[OF inv1] Suc(1)[OF inv2] link
  show ?case by simp
qed

lemma tree_rank_height:
  "tree_invar (Node e a r ts) \<Longrightarrow> height_tree (Node e a r ts) = r"
proof (induct r arbitrary: e a ts)
  case 0
  then show ?case by simp
next
  case (Suc r)
  from Suc(2) obtain e1 a1 ts1 e2 a2 ts2 where link:
    "(Node e a (Suc r) ts) = link (Node e1 a1 r ts1) (Node e2 a2 r ts2)"
    and inv1: "tree_invar (Node e1 a1 r ts1) "
    and inv2: "tree_invar (Node e2 a2 r ts2)" by simp blast
  with link Suc(1)[OF inv1] Suc(1)[OF inv2] Suc(2) show ?case
    by (cases "a1 \<le> a2") simp_all
qed

text \<open>A binomial tree of height $h$ contains exactly $2^{h}$ elements\<close>
theorem tree_height_estimate:
  "tree_invar t \<Longrightarrow> size (tree_to_multiset t) = (2::nat)^(height_tree t)"
  apply (cases t, simp only:)
  apply (frule tree_rank_estimate)
  apply (frule tree_rank_height)
  apply (simp only: )
  done

(*lemma size_mset_tree_Node: "tree_invar (Node e a r ts) \<Longrightarrow> 
  size (tree_to_multiset (Node e a r ts)) = (2::nat)^r"
  apply(induct r arbitrary: e a ts, simp)
proof -
  case goal1
  from goal1(2) obtain e1 a1 ts1 e2 a2 ts2 where link:
    "(Node e a (Suc r) ts) = link (Node e1 a1 r ts1) (Node e2 a2 r ts2)"
    and inv1: "tree_invar (Node e1 a1 r ts1) "
    and inv2: "tree_invar (Node e2 a2 r ts2)" by simp blast
  from link_length[of "(Node e1 a1 r ts1)" "(Node e2 a2 r ts2)"]
    goal1(1)[OF inv1] goal1(1)[OF inv2] link
  show ?case by simp
qed*)

lemma size_mset_tree: "tree_invar t \<Longrightarrow> 
  size (tree_to_multiset t) = (2::nat)^(rank t)"
  by (cases t) (simp only: tree_rank_estimate BinomialTree.sel(3)) 


lemma invar_butlast: "invar (bq @ [t]) \<Longrightarrow> invar bq"
  unfolding invar_def
  apply (induct bq) apply simp apply (case_tac bq) 
  by (simp_all)

lemma invar_last_max: "invar (bq @ [m]) \<Longrightarrow> \<forall> t \<in> set bq. rank t < rank m"
  unfolding invar_def
  apply (induct bq) apply simp apply (case_tac bq) apply simp by simp

lemma invar_length: "invar bq \<Longrightarrow> length bq \<le> Suc (rank (last bq))"
proof (induct bq rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x xs)
  show ?case proof (cases xs)
    case Nil thus ?thesis by simp
  next
    case [simp]: (Cons xxs xx)
    from snoc.hyps[OF invar_butlast[OF snoc.prems]] have
      IH: "length xs \<le> Suc (rank (last xs))" .
    also from invar_last_max[OF snoc.prems] last_in_set[of xs] have
      "Suc (rank (last xs)) \<le> rank (last (xs @ [x]))"
      by auto
    finally show ?thesis by simp
  qed
qed

lemma size_queue_sum_list: 
  "size (queue_to_multiset bq) = sum_list (map (size \<circ> tree_to_multiset) bq)"
  by (induct bq) simp_all

text \<open>
  A binomial heap of length $l$ contains at least $2^l - 1$ elements. 
\<close>
theorem queue_length_estimate_lower: 
  "invar bq \<Longrightarrow> (size (queue_to_multiset bq)) \<ge> 2^(length bq) - 1"
proof (induct bq rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x xs)
  from snoc.hyps[OF invar_butlast[OF snoc.prems]]
  have IH: "2 ^ length xs \<le> Suc (size (queue_to_multiset xs))" by simp
  have size_q: 
    "size (queue_to_multiset (xs @ [x])) = 
    size (queue_to_multiset xs) + size (tree_to_multiset x)" 
    by (simp add: size_queue_sum_list)
  also 
  from snoc.prems have inv_x: "tree_invar x" by (simp add: invar_def)
  hence "size (tree_to_multiset x) = 2 ^ rank x" by (simp add: size_mset_tree)
  finally have 
    eq: "size (queue_to_multiset (xs @ [x])) = 
         size (queue_to_multiset xs) + (2::nat)^(rank x)" .
  from invar_length[OF snoc.prems] have "length xs \<le> rank x" by simp
  hence snd: "(2::nat) ^ length xs \<le> (2::nat) ^ rank x" by simp
  have
    "(2::nat) ^ length (xs @ [x]) = (2::nat) ^ (length xs) + (2::nat) ^ (length xs)"
    by simp
  with IH have 
    "2 ^ length (xs @ [x]) \<le> Suc (size (queue_to_multiset xs)) + 2 ^ length xs" 
    by simp
  with snd have "2 ^ length (xs @ [x]) \<le> 
    Suc (size (queue_to_multiset xs)) + 2 ^ rank x" 
    by arith
  with eq show ?case by simp
qed

subsection \<open>Operations\<close>

subsubsection "Empty"
lemma empty_correct[simp]: 
  "invar Nil"
  "queue_to_multiset Nil = {#}"
  by (simp_all add: invar_def)
  
text \<open>The empty multiset is represented by exactly the empty queue\<close>
lemma empty_iff: "t=Nil \<longleftrightarrow> queue_to_multiset t = {#}"
  apply (cases t)
  apply auto
  apply (case_tac a)
  apply auto
  done

subsubsection "Insert"
text \<open>Inserts a binomial tree into a binomial queue, such that the queue 
  does not contain two trees of same rank.\<close>
fun  ins :: "('e, 'a::linorder) BinomialTree \<Rightarrow> ('e, 'a) BinomialQueue_inv \<Rightarrow> 
  ('e, 'a) BinomialQueue_inv" where
  "ins t [] = [t]" |
  "ins t' (t # bq) = (if (rank t') < (rank t) 
    then t' # t # bq 
    else (if (rank t) < (rank t') 
            then t # (ins t' bq)       
            else ins (link t' t) bq))" 
  
text \<open>Inserts an element with priority into the queue.\<close>
definition insert :: "'e \<Rightarrow> 'a::linorder \<Rightarrow> ('e, 'a) BinomialQueue_inv \<Rightarrow> 
  ('e, 'a) BinomialQueue_inv" where
  "insert e a bq = ins (Node e a 0 []) bq"

lemma ins_mset:
  "\<lbrakk>tree_invar t; queue_invar q\<rbrakk> \<Longrightarrow> queue_to_multiset (ins t q) 
   = tree_to_multiset t + queue_to_multiset q"
by (induct q arbitrary: t) (auto simp: union_ac link_tree_invar)

lemma insert_mset: "queue_invar q \<Longrightarrow>
  queue_to_multiset (insert e a q) = queue_to_multiset q + {# (e,a) #}"
by(simp add: ins_mset union_ac insert_def)

lemma ins_queue_invar: "\<lbrakk>tree_invar t; queue_invar q\<rbrakk> \<Longrightarrow> queue_invar (ins t q)"
proof (induct q arbitrary: t)
  case (Cons a q)
  note iv = Cons.hyps
  show ?case
  proof (cases "rank t = rank a")
    case [simp]: True
    from Cons.prems have 
      inv_a: "tree_invar a" and inv_q: "queue_invar q" 
      by (simp_all)
    note inv_link = link_tree_invar[OF \<open>tree_invar t\<close> inv_a True]
    from iv[OF inv_link inv_q] show ?thesis by simp
  next
    case False
    with Cons show ?thesis by auto
  qed
qed simp

lemma insert_queue_invar: 
  assumes "queue_invar q" 
  shows "queue_invar (insert e a q)"
proof -
  have inv: "tree_invar (Node e a 0 [])" by simp
  from ins_queue_invar[OF inv assms] show ?thesis by (simp add: insert_def)
qed

lemma  rank_ins: "(rank_invar (t # bq) \<Longrightarrow> 
  (rank (hd (ins t' (t # bq))) \<ge> rank t) \<or> 
  (rank (hd (ins t' (t # bq))) \<ge> rank t'))"
  apply(auto)
  apply(induct bq arbitrary: t t')
  apply(simp add: rank_link)
proof goal_cases
  case prems: (1 a bq t t')
  thus ?case
    apply(cases "rank (link t' t) = rank a")
    apply(auto simp add: rank_link)
  proof goal_cases
    case 1
    note * = this and \<open>\<And>t' t. \<lbrakk>rank_invar (t # bq); rank t' = rank t\<rbrakk>
      \<Longrightarrow> rank t \<le> rank (hd (ins (link t' t) bq))\<close>[of a "(link t' t)"] 
    show ?case
    proof (cases "rank (hd (ins (link (link t' t) a) bq)) = rank a")
      case True
      with * show ?thesis by simp
    next
      case False
      with * have "rank a \<le> rank (hd (ins (link (link t' t) a) bq))" 
        by (simp add: rank_link)
      with * show ?thesis by simp
    qed
  qed
qed

lemma rank_ins2: "rank_invar bq \<Longrightarrow> 
  rank t \<le> rank (hd (ins t bq)) \<or> 
  (rank (hd (ins t bq)) = rank (hd bq) \<and> bq \<noteq> [])"
  apply(induct bq arbitrary: t)
  apply(auto)
proof goal_cases
  case prems: (1 a bq t)
  hence r: "rank (link t a) = rank a + 1" by (simp add: rank_link)
  from prems r and prems(1)[of "(link t a)"] show ?case by (cases bq) auto
qed

lemma rank_invar_ins: "rank_invar bq \<Longrightarrow> rank_invar (ins t bq)"
  apply(induct bq arbitrary: t)
  apply(simp)
  apply(auto)
proof goal_cases
  case prems: (1 a bq t)
  hence inv: "rank_invar (ins t bq)" by (cases bq) simp_all
  from prems have hd: "bq \<noteq> [] \<Longrightarrow> rank a < rank (hd bq)"  
    by (cases bq) auto
  from prems have "rank t \<le> rank (hd (ins t bq)) \<or>
    (rank (hd (ins t bq)) = rank (hd bq) \<and> bq \<noteq> [])"
    by (simp add: rank_ins2 rank_invar_cons)
  with prems have "rank a < rank (hd (ins t bq)) \<or>
    (rank (hd (ins t bq)) = rank (hd bq) \<and> bq \<noteq> [])" by auto
  with prems and inv and hd show ?case by (auto simp add: rank_invar_hd_cons)
next
  case prems: (2 a bq t)
  hence inv: "rank_invar bq" by (cases bq) simp_all
  with prems and prems(1)[of "(link t a)"] show ?case by simp
qed

lemma rank_invar_insert: "rank_invar bq \<Longrightarrow> rank_invar (insert e a bq)"
  by (simp add: rank_invar_ins insert_def)

lemma insert_correct: 
  assumes I: "invar q"
  shows 
  "invar (insert e a q)"
  "queue_to_multiset (insert e a q) = queue_to_multiset q + {# (e,a) #}"
  using insert_queue_invar[of q] rank_invar_insert[of q] insert_mset[of q] I
  unfolding invar_def by auto

subsubsection "Meld"
text \<open>Melds two queues.\<close>
fun meld :: "('e, 'a::linorder) BinomialQueue_inv \<Rightarrow> ('e, 'a) BinomialQueue_inv
  \<Rightarrow> ('e, 'a) BinomialQueue_inv" 
  where
  "meld [] bq = bq" |
  "meld bq [] = bq" |
  "meld (t1#bq1) (t2#bq2) =
   (if (rank t1) < (rank t2) 
       then t1 # (meld bq1 (t2 # bq2))
       else (
         if (rank t2 < rank t1)
            then t2 # (meld (t1 # bq1) bq2)
            else ins (link t1 t2) (meld bq1 bq2)
       )
    )"

lemma meld_queue_invar: 
  "\<lbrakk>queue_invar q; queue_invar q'\<rbrakk> \<Longrightarrow> queue_invar (meld q q')"
proof (induct q q' rule: meld.induct)
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
    case lt
    from 3(4) have inv_bq1: "queue_invar bq1" by simp
    from 3(4) have inv_t1: "tree_invar t1" by simp
    from 3(1)[OF lt inv_bq1 3(5)] inv_t1 lt
    show ?thesis by simp
  next
    case gt
    from 3(5) have inv_bq2: "queue_invar bq2" by simp
    from 3(5) have inv_t2: "tree_invar t2" by simp
    from gt have "\<not> rank t1 < rank t2" by simp
    from 3(2)[OF this gt 3(4) inv_bq2] inv_t2 gt
    show ?thesis by simp
  next
    case eq
    from 3(4) have inv_bq1: "queue_invar bq1" by simp
    from 3(4) have inv_t1: "tree_invar t1" by simp
    from 3(5) have inv_bq2: "queue_invar bq2" by simp
    from 3(5) have inv_t2: "tree_invar t2" by simp
    note inv_link = link_tree_invar[OF inv_t1 inv_t2 eq]
    from eq have *: "\<not> rank t1 < rank t2" "\<not> rank t2 < rank t1" by simp_all
    note inv_meld = 3(3)[OF * inv_bq1 inv_bq2]
    from ins_queue_invar[OF inv_link inv_meld] *
    show ?thesis by simp
  qed
qed

lemma rank_ins_min: "rank_invar bq \<Longrightarrow> 
  rank (hd (ins t bq)) \<ge> min (rank t) (rank (hd bq))"
  apply(induct bq arbitrary: t)
  apply(auto)
proof goal_cases
  case prems: (1 a bq t)
  hence inv: "rank_invar bq" by (cases bq) simp_all
  from prems have r: "rank (link t a) = rank a + 1" by (simp add: rank_link)
  with prems and inv and prems(1)[of "(link t a)"] show ?case by (cases bq) auto
qed

lemma rank_invar_meld_strong: 
  "\<lbrakk>rank_invar bq1; rank_invar bq2\<rbrakk> \<Longrightarrow> rank_invar (meld bq1 bq2) \<and> 
  rank (hd (meld bq1 bq2)) \<ge> min (rank (hd bq1)) (rank (hd bq2))"
proof (induct bq1 bq2 rule: meld.induct)
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
  proof (auto, goal_cases)
    let ?t = "t2"
    let ?bq = "bq2"
    let ?meld = "rank t2 < rank (hd (meld (t1 # bq1) bq2))"
    case prems: 1
    hence "?bq \<noteq> [] \<Longrightarrow> rank ?t < rank (hd ?bq)" 
      by (simp add: rank_invar_not_empty_hd)
    with prems have ne: "?bq \<noteq> [] \<Longrightarrow> ?meld" by simp
    from prems have "?bq = [] \<Longrightarrow> ?meld" by simp
    with ne have "?meld" by (cases "?bq = []")
    with prems show ?case by (simp add: rank_invar_hd_cons)
  next \<comment> \<open>analog\<close>
    let ?t = "t1"
    let ?bq = "bq1"
    let ?meld = "rank t1 < rank (hd (meld bq1 (t2 # bq2)))"
    case prems: 2
    hence "?bq \<noteq> [] \<Longrightarrow> rank ?t < rank (hd ?bq)" 
      by (simp add: rank_invar_not_empty_hd)
    with prems have ne: "?bq \<noteq> [] \<Longrightarrow> ?meld" by simp
    from prems have "?bq = [] \<Longrightarrow> ?meld" by simp
    with ne have "?meld" by (cases "?bq = []")
    with prems show ?case by (simp add: rank_invar_hd_cons)
  next
    case 3
    thus ?case by (simp add: rank_invar_ins)
  next
    case prems: 4 (* Ab hier wirds hässlich *)
    then have r: "rank (link t1 t2) = rank t2 + 1" 
      by (simp add: rank_link)
    have m: "meld bq1 [] = bq1" by (cases bq1, auto)
    
    from inv1 and inv2 and prems
    have mm: "min (rank (hd bq1)) (rank (hd bq2)) \<le> rank (hd (meld bq1 bq2))"
      by simp
    from \<open>rank_invar (t1 # bq1)\<close> have "bq1 \<noteq> [] \<Longrightarrow> rank t1 < rank (hd bq1)" 
      by (simp add: rank_invar_not_empty_hd)
    with prems have r1: "bq1 \<noteq> [] \<Longrightarrow> rank t2 < rank (hd bq1)" by simp
    from \<open>rank_invar (t2 # bq2)\<close> 
    have r2: "bq2 \<noteq> [] \<Longrightarrow> rank t2 < rank (hd bq2)" 
      by (simp add: rank_invar_not_empty_hd)
    
    from inv1 r r1 rank_ins_min[of bq1 "(link t1 t2)"] 
    have abc1: "bq1 \<noteq> [] \<Longrightarrow> rank t2 \<le> rank (hd (ins (link t1 t2) bq1))" 
      by simp
    from inv2 r r2 rank_ins_min[of bq2 "(link t1 t2)"] 
    have abc2: "bq2 \<noteq> [] \<Longrightarrow> rank t2 \<le> rank (hd (ins (link t1 t2) bq2))" 
      by simp
    from r1 r2 mm have 
      "\<lbrakk>bq1 \<noteq> []; bq2 \<noteq> []\<rbrakk> \<Longrightarrow> rank t2 < rank (hd (meld bq1 bq2))" by simp
    with \<open>rank_invar (meld bq1 bq2)\<close> 
      r rank_ins_min[of "meld bq1 bq2" "link t1 t2"] 
    have "\<lbrakk>bq1 \<noteq> []; bq2 \<noteq> []\<rbrakk> \<Longrightarrow> 
      rank t2 < rank (hd (ins (link t1 t2) (meld bq1 bq2)))" by simp
    thm rank_ins_min[of "meld bq1 bq2" "link t1 t2"]
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

lemma rank_invar_meld: 
  "\<lbrakk>rank_invar bq1; rank_invar bq2\<rbrakk> \<Longrightarrow> rank_invar (meld bq1 bq2)" 
  by (simp only: rank_invar_meld_strong)

lemma meld_mset: "\<lbrakk>queue_invar q; queue_invar q'\<rbrakk> \<Longrightarrow> 
  queue_to_multiset (meld q q') = 
  queue_to_multiset q + queue_to_multiset q'"
by(induct q q' rule: meld.induct)
  (auto simp add: link_tree_invar meld_queue_invar ins_mset union_ac)

lemma meld_correct:
  assumes "invar q" "invar q'" 
  shows 
  "invar (meld q q')"
  "queue_to_multiset (meld q q') = queue_to_multiset q + queue_to_multiset q'"
  using assms
  unfolding invar_def
  by (simp_all add: meld_queue_invar rank_invar_meld meld_mset)

subsubsection "Find Minimal Element"
text \<open>Finds the tree containing the minimal element.\<close>
fun getMinTree :: "('e, 'a::linorder) BinomialQueue_inv \<Rightarrow> 
  ('e, 'a) BinomialTree" where
  "getMinTree [t] = t" |
  "getMinTree (t#bq) = (if prio t \<le> prio (getMinTree bq) 
     then t else (getMinTree bq))" 

lemma mintree_exists: "(bq \<noteq> []) = (getMinTree bq \<in> set bq)"
proof (induct bq)
  case Nil
  then show ?case by simp
next
  case (Cons _ bq)
  then show ?case by (cases bq) simp_all
qed

lemma treehead_in_multiset: 
  "t \<in> set bq \<Longrightarrow> (val t, prio t) \<in># queue_to_multiset bq"
  by (induct bq, simp, cases t, auto) 

lemma heap_ordered_single: 
"heap_ordered t = (\<forall>x \<in> set_mset (tree_to_multiset t). prio t \<le> snd x)"
  by (cases t) auto

lemma getMinTree_cons: 
  "prio (getMinTree (y # x # xs)) \<le> prio (getMinTree (x # xs))" 
  by (induct xs rule: getMinTree.induct) simp_all 

lemma getMinTree_min_tree:
  "t \<in> set bq  \<Longrightarrow> prio (getMinTree bq) \<le> prio t"
  apply(induct bq arbitrary: t rule: getMinTree.induct) 
  apply simp   
  defer
  apply simp
proof goal_cases
  case prems: (1 t v va ta)
  thus ?case
    apply (cases "ta = t")
    apply auto[1] 
    apply (metis getMinTree_cons prems(1) prems(3) set_ConsD xt1(6))
    done
qed

lemma getMinTree_min_prio:
  assumes "queue_invar bq"
    and "y \<in> set_mset (queue_to_multiset bq)"
  shows "prio (getMinTree bq) \<le> snd y"
proof -
  from assms have "bq \<noteq> []" by (cases bq) simp_all
  with assms have "\<exists> t \<in> set bq. (y \<in> set_mset ((tree_to_multiset t)))"
  proof (induct bq)
    case Nil
    then show ?case by simp
  next
    case (Cons a bq)
    thus ?case
      apply(cases "y \<in> set_mset (tree_to_multiset a)") 
      apply simp
      apply(cases bq)
      apply simp_all
      done
  qed
  from this obtain t where O: 
    "t \<in> set bq"
    "y \<in> set_mset (tree_to_multiset t)" by blast
  obtain e a r ts where [simp]: "t = (Node e a r ts)" by (cases t) blast
  from O assms(1) have inv: "tree_invar t" by (simp add: queue_invar_def)
  from tree_invar_heap_ordered[OF inv] heap_ordered.simps[of e a r ts] O
  have "prio t \<le> snd y" by auto
  with getMinTree_min_tree[OF O(1)] show ?thesis by simp
qed

text \<open>Finds the minimal Element in the queue.\<close>
definition findMin :: "('e, 'a::linorder) BinomialQueue_inv \<Rightarrow> ('e \<times> 'a)" where
  "findMin bq = (let min = getMinTree bq in (val min, prio min))"

lemma findMin_correct:
  assumes I: "invar q"
  assumes NE: "q \<noteq> Nil"
  shows 
  "findMin q \<in># queue_to_multiset q"
  "\<forall>y\<in>set_mset (queue_to_multiset q). snd (findMin q) \<le> snd y"
proof -
  from NE have "getMinTree q \<in> set q" by (simp only: mintree_exists)
  thus "findMin q \<in># queue_to_multiset q" 
    by (simp add: treehead_in_multiset Let_def findMin_def)
  show "\<forall>y\<in>set_mset (queue_to_multiset q). snd (findMin q) \<le> snd y"
    using I[unfolded invar_def]
    by (auto simp add: getMinTree_min_prio Let_def findMin_def)
qed  

subsubsection "Delete Minimal Element"

text \<open>Removes the first tree, which has the priority $a$ within his root.\<close>
fun remove1Prio :: "'a \<Rightarrow> ('e, 'a::linorder) BinomialQueue_inv \<Rightarrow>
  ('e, 'a) BinomialQueue_inv" where
  "remove1Prio a [] = []" |
  "remove1Prio a (t#bq) = 
  (if (prio t) = a then bq else t # (remove1Prio a bq))"

text \<open>Returns the queue without the minimal element.\<close>
definition deleteMin :: "('e, 'a::linorder) BinomialQueue_inv \<Rightarrow> 
  ('e, 'a) BinomialQueue_inv" where
  "deleteMin bq \<equiv> (let min = getMinTree bq in 
                    meld (rev (children min)) 
                         (remove1Prio (prio min) bq))"

lemma queue_invar_rev: "queue_invar q \<Longrightarrow> queue_invar (rev q)"
  by (simp add: queue_invar_def)

lemma queue_invar_remove1: "queue_invar q \<Longrightarrow> queue_invar (remove1 t q)" 
  by (auto simp add: queue_invar_def)

lemma qtm_in_set_subset: "t \<in> set q \<Longrightarrow> 
  tree_to_multiset t \<subseteq># queue_to_multiset q"
proof(induct q)
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
  
lemma remove1_mset: "t \<in> set q \<Longrightarrow> 
  queue_to_multiset (remove1 t q) = 
  queue_to_multiset q - tree_to_multiset t"
by (induct q) (auto simp: qtm_in_set_subset)

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
    
lemma deleteMin_queue_invar: 
  assumes INV: "queue_invar q" 
  assumes NE: "q \<noteq> Nil"
  shows "queue_invar (deleteMin q)"
proof (cases q)
  case Nil
  with assms show ?thesis by simp
next
  case Cons
  from NE and mintree_exists[of q] INV 
  have inv_min: "tree_invar (getMinTree q)" by (simp add: queue_invar_def)
  note inv_children = invar_children'[OF inv_min]
  note inv_rev = queue_invar_rev[OF inv_children]
  note inv_rem = queue_invar_remove1[OF INV, of "getMinTree q"]
  from meld_queue_invar[OF inv_rev inv_rem] show ?thesis
    by (simp add: deleteMin_def Let_def)
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
    then obtain e1 a1 ts1 e2 a2 ts2 where 
      O: "tree_invar (Node e1 a1 nat ts1)" "tree_invar (Node e2 a2 nat ts2)"
        "t = link (Node e1 a1 nat ts1) (Node e2 a2 nat ts2)"
      by (simp only: tree_invar.simps) blast
    hence ch_id: "children t = 
      (if a1 \<le> a2 then (Node e2 a2 nat ts2)#ts1 
       else (Node e1 a1 nat ts1)#ts2)" by simp 
    from O Suc(1)[of "Node e1 a1 nat ts1" "e1" "a1" "ts1"] 
    have  p1: "\<forall>t'\<in>set ((Node e2 a2 nat ts2) # ts1). rank t' < Suc nat" by auto
    from O Suc(1)[of "Node e2 a2 nat ts2" "e2" "a2" "ts2"] 
    have p2: "\<forall>t'\<in>set ((Node e1 a1 nat ts1) # ts2). rank t' < Suc nat" by auto
    from Suc(3) p1 p2 ch_id show ?case by simp
  qed
qed

lemma strong_rev_children:
  assumes "tree_invar t"
  shows "invar (rev (children t))"
  unfolding invar_def
proof (cases t)
  case (Node e a nat list)
  with assms show "queue_invar (rev (children t)) \<and> rank_invar (rev (children t))"
  proof (induct "nat" arbitrary: t e a list)
    case 0
    then show ?case by simp
  next
    case (Suc nat)
    then obtain e1 a1 ts1 e2 a2 ts2 where 
      O: "tree_invar (Node e1 a1 nat ts1)" "tree_invar (Node e2 a2 nat ts2)"
        "t = link (Node e1 a1 nat ts1) (Node e2 a2 nat ts2)"
      by (simp only: tree_invar.simps) blast
    hence ch_id: "children t = 
      (if a1 \<le> a2 then (Node e2 a2 nat ts2)#ts1 
       else (Node e1 a1 nat ts1)#ts2)" by simp 
    from O Suc(1)[of "Node e1 a1 nat ts1" "e1" "a1" "ts1"]
    have rev_ts1: "invar (rev ts1)" by (simp add: invar_def)
    from O children_rank_less[of "Node e1 a1 nat ts1"]
    have  "\<forall>t\<in>set (rev ts1). rank t < rank (Node e2 a2 nat ts2)" by simp
    with O rev_ts1 invar_app_single[of "rev ts1" "Node e2 a2 nat ts2"] 
    have p1: "invar (rev ((Node e2 a2 nat ts2) # ts1))" by simp 
    from O Suc(1)[of "Node e2 a2 nat ts2" "e2" "a2" "ts2"]
    have rev_ts2: "invar (rev ts2)" by (simp add: invar_def)
    from O children_rank_less[of "Node e2 a2 nat ts2"]
    have "\<forall>t\<in>set (rev ts2). rank t < rank (Node e1 a1 nat ts1)" by simp
    with O rev_ts2 invar_app_single[of "rev ts2" "Node e1 a1 nat ts1"] 
    have p2: "invar (rev ((Node e1 a1 nat ts1) # ts2))" by simp 
    from p1 p2 ch_id show ?case by (simp add: invar_def)
  qed
qed

lemma first_less: "rank_invar (t # bq) \<Longrightarrow> \<forall>t' \<in> set bq. rank t < rank t'" 
  apply(induct bq arbitrary: t) 
  apply (simp)
  apply (metis order_le_less rank_invar.simps(3) set_ConsD xt1(7)) 
  done

lemma strong_remove1: "invar bq \<Longrightarrow> invar (remove1 t bq)" 
proof (induct bq arbitrary: t) 
  case Nil
  then show ?case by simp
next
  case (Cons a bq) 
  show ?case 
  proof (cases "t=a")
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
      from Cons have "tree_invar a" by (simp add: invar_def)
      from Cons first_less[of "a" "bq"] have "\<forall>t \<in> set (remove1 t bq). rank a < rank t"
        by (metis notin_set_remove1 invar_def) 
      with Cons' have "rank a < rank aa" by simp
      with si1 Cons(2) False Cons' invar_cons_up[of "aa" "list" "a"] show ?thesis
        by (simp add: invar_def)
    qed
  qed
qed  

theorem deleteMin_invar:
  assumes "invar bq"
    and "bq \<noteq> []"
  shows "invar (deleteMin bq)"
proof -
  have eq: "invar (deleteMin bq) = 
    invar (meld (rev (children (getMinTree bq))) (remove1 (getMinTree bq) bq))"
    by (simp add: deleteMin_def Let_def)
  from assms mintree_exists[of "bq"] have ti: "tree_invar (getMinTree bq)" 
    by (simp add: invar_def Let_def queue_invar_def)
  with strong_rev_children[of "getMinTree bq"]
  have m1: "invar (rev (children (getMinTree bq)))" .
  from strong_remove1[of "bq" "getMinTree bq"] assms(1)
  have m2: "invar (remove1 (getMinTree bq) bq)" .
  from meld_correct(1)[of "rev (children (getMinTree bq))" 
    "remove1 (getMinTree bq) bq"] m1 m2
  have "invar (meld (rev (children (getMinTree bq))) (remove1 (getMinTree bq) bq))" .
  with eq show ?thesis ..
qed

lemma children_mset: "queue_to_multiset (children t) = 
  tree_to_multiset t - {# (val t, prio t) #}"
proof (cases t)
  case (Node e a nat list)
  thus ?thesis by (induct list) simp_all
qed

lemma deleteMin_mset:
  assumes "queue_invar q"
    and "q \<noteq> Nil"
  shows "queue_to_multiset (deleteMin q) = queue_to_multiset q - {# (findMin q) #}"
proof -
  from assms mintree_exists[of "q"] have min_in_q: "getMinTree q \<in> set q" by auto
  with assms(1) have inv_min: "tree_invar (getMinTree q)" 
    by (simp add: queue_invar_def)
  from assms(2) have q_ne: "q \<noteq> []" .
  note inv_children = invar_children'[OF inv_min]
  note inv_rev = queue_invar_rev[OF inv_children]
  note inv_rem = queue_invar_remove1[OF assms(1), of "getMinTree q"]
  note m_meld = meld_mset[OF inv_rev inv_rem]
  note m_rem = remove1_mset[OF min_in_q]
  note m_rev = qtmset_rev[of "children (getMinTree q)"]
  note m_children = children_mset[of "getMinTree q"]
  note min_subset_q = qtm_in_set_subset[OF min_in_q]
  let ?Q = "queue_to_multiset q"
  let ?MT = "tree_to_multiset (getMinTree q)"
  from q_ne have head_subset_min: 
    "{# (val (getMinTree q), prio (getMinTree q)) #} \<subseteq># ?MT"
    by(cases "getMinTree q") simp
  let ?Q = "queue_to_multiset q"
  let ?MT = "tree_to_multiset (getMinTree q)"
  from m_meld m_rem m_rev m_children 
    multiset_diff_union_assoc[OF head_subset_min, of "?Q - ?MT"]
    mset_subset_eq_multiset_union_diff_commute[OF min_subset_q, of "?MT"]
  show ?thesis by (simp add: deleteMin_def union_ac Let_def findMin_def)
qed

lemma deleteMin_correct:
  assumes INV: "invar q" 
  assumes NE: "q \<noteq> Nil"
  shows 
  "invar (deleteMin q)"
  "queue_to_multiset (deleteMin q) = queue_to_multiset q - {# (findMin q) #}"
  using deleteMin_invar deleteMin_mset INV NE
  unfolding invar_def
  by auto

end

interpretation BinomialHeapStruc: BinomialHeapStruc_loc .


subsection "Hiding the Invariant"
subsubsection "Datatype"
typedef (overloaded) ('e, 'a) BinomialHeap =
  "{q :: ('e,'a::linorder) BinomialHeapStruc.BinomialQueue_inv. BinomialHeapStruc.invar q }"
  apply (rule_tac x="Nil" in exI)
  apply auto
  done

lemma Rep_BinomialHeap_invar[simp]: 
  "BinomialHeapStruc.invar (Rep_BinomialHeap x)"
  using Rep_BinomialHeap
  by (auto)

lemma [simp]: 
  "BinomialHeapStruc.invar q \<Longrightarrow> Rep_BinomialHeap (Abs_BinomialHeap q) = q"
  using Abs_BinomialHeap_inverse by auto

lemma [simp, code abstype]: "Abs_BinomialHeap (Rep_BinomialHeap q) = q"
  by (rule Rep_BinomialHeap_inverse)

locale BinomialHeap_loc
begin
  subsubsection "Operations"

  definition [code]: 
    "to_mset t == BinomialHeapStruc.queue_to_multiset (Rep_BinomialHeap t)"

  definition empty where "empty == Abs_BinomialHeap Nil" 
  lemma [code abstract, simp]: "Rep_BinomialHeap empty = []"
    by (unfold empty_def) simp


  definition [code]: "isEmpty q == Rep_BinomialHeap q = Nil"
  lemma empty_rep: "q=empty \<longleftrightarrow> Rep_BinomialHeap q = Nil"
    apply (auto simp add: empty_def)
    apply (metis Rep_BinomialHeap_inverse)
    done

  lemma isEmpty_correct: "isEmpty q \<longleftrightarrow> q=empty"
    by (simp add: empty_rep isEmpty_def)
  
  definition 
    insert 
    :: "'e  \<Rightarrow> ('a::linorder) \<Rightarrow> ('e,'a) BinomialHeap \<Rightarrow> ('e,'a) BinomialHeap"
    where "insert e a q == 
            Abs_BinomialHeap (BinomialHeapStruc.insert e a (Rep_BinomialHeap q))"
  lemma [code abstract]: 
    "Rep_BinomialHeap (insert e a q) 
    = BinomialHeapStruc.insert e a (Rep_BinomialHeap q)"
    by (simp add: insert_def BinomialHeapStruc.insert_correct)

  definition [code]: "findMin q == BinomialHeapStruc.findMin (Rep_BinomialHeap q)"
  
  definition "deleteMin q == 
    if q=empty then empty 
    else Abs_BinomialHeap (BinomialHeapStruc.deleteMin (Rep_BinomialHeap q))"

  text \<open>
    In this lemma, we do not use equality, but case-distinction for checking 
    non-emptyness. That prevents the code generator from introducing
    an equality-class parameter for the entry type \<open>'a\<close>.
\<close>
  lemma [code abstract]: "Rep_BinomialHeap (deleteMin q) =
    (case (Rep_BinomialHeap q) of [] \<Rightarrow> [] |
     _ \<Rightarrow> BinomialHeapStruc.deleteMin (Rep_BinomialHeap q))"
  proof (cases "Rep_BinomialHeap q")
    case Nil 
    show ?thesis
      apply (simp add: Nil)
      apply (auto simp add: deleteMin_def BinomialHeapStruc.deleteMin_correct 
      BinomialHeapStruc.empty_iff empty_rep Nil)
      done
  next
    case (Cons a b)
    hence NE: "Rep_BinomialHeap q \<noteq> []" by auto
    show ?thesis
      apply (simp add: Cons)
      apply (fold Cons)
      using NE
      by (auto simp add: deleteMin_def BinomialHeapStruc.deleteMin_correct 
        BinomialHeapStruc.empty_iff empty_rep)
  qed

  (*
  lemma [code abstract]: "Rep_BinomialHeap (deleteMin q) =
    (if (Rep_BinomialHeap q = []) then [] 
     else BinomialHeapStruc.deleteMin (Rep_BinomialHeap q))"
    by (auto simp add: deleteMin_def BinomialHeapStruc.deleteMin_correct 
      BinomialHeapStruc.empty_iff empty_rep)
      *)

  definition "meld q1 q2 == 
    Abs_BinomialHeap (BinomialHeapStruc.meld (Rep_BinomialHeap q1) 
                                             (Rep_BinomialHeap q2))"
  lemma [code abstract]:
    "Rep_BinomialHeap (meld q1 q2) 
    = BinomialHeapStruc.meld (Rep_BinomialHeap q1) (Rep_BinomialHeap q2)"
    by (simp add: meld_def BinomialHeapStruc.meld_correct)


  subsubsection "Correctness"

  lemma empty_correct: "to_mset q = {#} \<longleftrightarrow> q=empty"
    by (simp add: to_mset_def BinomialHeapStruc.empty_iff empty_rep)

  lemma to_mset_of_empty[simp]: "to_mset empty = {#}"
    by (simp add: empty_correct)

  lemma insert_correct: "to_mset (insert e a q) = to_mset q + {#(e,a)#}"
    apply (unfold insert_def to_mset_def)
    apply (simp add: BinomialHeapStruc.insert_correct)
    done

  lemma findMin_correct: 
    assumes "q\<noteq>empty"
    shows 
    "findMin q \<in># to_mset q"
    "\<forall>y\<in>set_mset (to_mset q). snd (findMin q) \<le> snd y"
    using assms
    apply (unfold findMin_def to_mset_def)
    apply (simp_all add: empty_rep BinomialHeapStruc.findMin_correct)
    done

  lemma deleteMin_correct:
    assumes "q\<noteq>empty"
    shows "to_mset (deleteMin q) = to_mset q - {# findMin q #}"
    using assms
    apply (unfold findMin_def deleteMin_def to_mset_def)
    apply (simp_all add: empty_rep BinomialHeapStruc.deleteMin_correct)
    done

  lemma meld_correct:
    shows "to_mset (meld q q') = to_mset q + to_mset q'"
    apply (unfold to_mset_def meld_def)
    apply (simp_all add: BinomialHeapStruc.meld_correct)
    done

  text \<open>Correctness lemmas to be used with simplifier\<close>
  lemmas correct = empty_correct deleteMin_correct meld_correct

  end
  interpretation BinomialHeap: BinomialHeap_loc .
  

  
subsection "Documentation"

(*#DOC
  fun [no_spec] BinomialHeap.to_mset
    Abstraction to multiset.

  fun BinomialHeap.empty
    The empty heap. ($O(1)$)

  fun BinomialHeap.isEmpty
    Checks whether heap is empty. Mainly used to work around 
    code-generation issues. ($O(1)$)

  fun BinomialHeap.insert
    Inserts element ($O(\log(n))$)

  fun BinomialHeap.findMin
    Returns a minimal element ($O(\log(n))$)

  fun BinomialHeap.deleteMin
    Deletes {\em the} element that is returned by {\em find\_min}

  fun [long_type] BinomialHeap.meld
    Melds two heaps ($O(\log(n+m))$)

*)


text \<open>
    \underline{@{term_type "BinomialHeap.to_mset"}}\\
        Abstraction to multiset.\\


    \underline{@{term_type "BinomialHeap.empty"}}\\
        The empty heap. ($O(1)$)\\
    {\bf Spec} \<open>BinomialHeap.empty_correct\<close>:
    @{thm [display] BinomialHeap.empty_correct[no_vars]}


    \underline{@{term_type "BinomialHeap.isEmpty"}}\\
        Checks whether heap is empty. Mainly used to work around
    code-generation issues. ($O(1)$)\\
    {\bf Spec} \<open>BinomialHeap.isEmpty_correct\<close>:
    @{thm [display] BinomialHeap.isEmpty_correct[no_vars]}


    \underline{@{term_type "BinomialHeap.insert"}}\\
        Inserts element ($O(\log(n))$)\\
    {\bf Spec} \<open>BinomialHeap.insert_correct\<close>:
    @{thm [display] BinomialHeap.insert_correct[no_vars]}


    \underline{@{term_type "BinomialHeap.findMin"}}\\
        Returns a minimal element ($O(\log(n))$)\\
    {\bf Spec} \<open>BinomialHeap.findMin_correct\<close>:
    @{thm [display] BinomialHeap.findMin_correct[no_vars]}


    \underline{@{term_type "BinomialHeap.deleteMin"}}\\
        Deletes {\em the} element that is returned by {\em find\_min}\\
    {\bf Spec} \<open>BinomialHeap.deleteMin_correct\<close>:
    @{thm [display] BinomialHeap.deleteMin_correct[no_vars]}


    \underline{@{term "BinomialHeap.meld"}}
    @{term_type [display] "BinomialHeap.meld"}
        Melds two heaps ($O(\log(n+m))$)\\
    {\bf Spec} \<open>BinomialHeap.meld_correct\<close>:
    @{thm [display] BinomialHeap.meld_correct[no_vars]}

\<close>


end
