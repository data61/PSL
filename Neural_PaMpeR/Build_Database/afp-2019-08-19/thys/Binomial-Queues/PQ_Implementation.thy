(* Authors:  René Neumann and Florian Haftmann, TU Muenchen *)

section \<open>Relating Functional Binomial Queues To The Abstract Priority Queues\<close>

theory PQ_Implementation
imports PQ Binomial_Queue 
begin

notation
  "PQ.values" ("|(_)|")
  and "PQ.priorities" ("\<parallel>(_)\<parallel>")

text \<open>
  \noindent Naming convention: prefix \<open>bt_\<close> for bintrees, \<open>bts_\<close> for bintree lists,
  no prefix for binqueues.
\<close>

primrec bt_dfs :: "(('a::linorder, 'b) bintree \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) bintree \<Rightarrow> 'c list"
  and bts_dfs :: "(('a::linorder, 'b) bintree \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) bintree list  \<Rightarrow> 'c list" where
  "bt_dfs f (Node a v ts) = f (Node a v ts) # bts_dfs f ts"
| "bts_dfs f [] = []"
| "bts_dfs f (t # ts) = bt_dfs f t @ bts_dfs f ts"

lemma bt_dfs_simp:
  "bt_dfs f t = f t # bts_dfs f (children t)"
  by (cases t) simp_all

lemma bts_dfs_append [simp]:
  "bts_dfs f (ts @ rs) = bts_dfs f ts @ bts_dfs f rs"
  by (induct ts) simp_all

lemma set_bts_dfs_rev:
  "set (bts_dfs f (rev ts)) = set (bts_dfs f ts)"
  by (induct ts) auto

lemma bts_dfs_rev_distinct:
  "distinct (bts_dfs f ts) \<Longrightarrow> distinct (bts_dfs f (rev ts))"
  by (induct ts) (auto simp add: set_bts_dfs_rev)

lemma bt_dfs_comp:
  "bt_dfs (f \<circ> g) t = map f (bt_dfs g t)"
  "bts_dfs (f \<circ> g) ts = map f (bts_dfs g ts)"
  by (induct t and ts rule: bt_dfs.induct bts_dfs.induct) simp_all

lemma bt_dfs_comp_distinct:
  "distinct (bt_dfs (f \<circ> g) t) \<Longrightarrow> distinct (bt_dfs g t)"
  "distinct (bts_dfs (f \<circ> g) ts) \<Longrightarrow> distinct (bts_dfs g ts)"
  by (simp_all add: bt_dfs_comp distinct_map [of f])

lemma bt_dfs_distinct_children:
  "distinct (bt_dfs f x) \<Longrightarrow> distinct (bts_dfs f (children x))"
  by (cases x) simp

fun dfs :: "(('a::linorder, 'b) bintree \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) binqueue \<Rightarrow> 'c list" where
  "dfs f [] = []"
| "dfs f (None # xs) = dfs f xs"
| "dfs f (Some t # xs) = bt_dfs f t @ dfs f xs"

lemma dfs_append:
  "dfs f (xs @ ys) = (dfs f xs) @ (dfs f ys)"
  by (induct xs) simp_all

lemma set_dfs_rev:
  "set (dfs f (rev xs)) = set (dfs f xs)"
  by (induct xs) (auto simp add: dfs_append)

lemma set_dfs_Cons:
  "set (dfs f (x # xs)) = set (dfs f xs) \<union> set (dfs f [x])"
proof -
  have "set (dfs f (x # xs)) = set (dfs f (rev xs @ [x]))"
    using set_dfs_rev[of f "rev xs @ [x]"] by simp
  thus ?thesis by (simp add: dfs_append set_dfs_rev)
qed

lemma dfs_comp:
  "dfs (f \<circ> g) xs = map f (dfs g xs)"
  by (induct xs) (simp_all add: bt_dfs_comp del: o_apply)

lemma dfs_comp_distinct:
  "distinct (dfs (f \<circ> g) xs) \<Longrightarrow> distinct (dfs g xs)"
  by (simp add: dfs_comp distinct_map[of f])

lemma dfs_distinct_member:
  "distinct (dfs f xs) \<Longrightarrow> 
   Some x \<in> set xs \<Longrightarrow> 
   distinct (bt_dfs f x)"
proof (induct xs arbitrary: x)
  case (Some r xs t) then show ?case by (cases "t = r") simp_all
qed simp_all

lemma dfs_map_Some_idem:
  "dfs f (map Some xs) = bts_dfs f xs"
  by (induct xs) simp_all

primrec alist :: "('a, 'b) bintree \<Rightarrow> ('b \<times> 'a)" where
  "alist (Node a v _) = (v, a)"

lemma alist_split_pre:
  "val t = (fst \<circ> alist) t"
  "priority t = (snd \<circ> alist) t"
  by (cases t, simp)+

lemma alist_split:
  "val = fst \<circ> alist"
  "priority = snd \<circ> alist"
  by (auto intro!: ext simp add: alist_split_pre)

lemma alist_split_set:
  "set (dfs val xs) = fst ` set (dfs alist xs)"
  "set (dfs priority xs) = snd ` set (dfs alist xs)"
  by (auto simp add: dfs_comp alist_split)

lemma in_set_in_alist:
  assumes "Some t \<in> set xs"
  shows "(val t, priority t) \<in> set (dfs alist xs)"
using assms
proof (induct xs)
  case (Some x xs) then show ?case
  proof (cases "Some t \<in> set xs")
    case False with Some show ?thesis by (cases t) (auto simp add: bt_dfs_simp)
  qed simp
qed simp_all

abbreviation vals where "vals \<equiv> dfs val"
abbreviation prios where "prios \<equiv> dfs priority"
abbreviation elements where "elements \<equiv> dfs alist"

primrec
  bt_augment :: "('a::linorder, 'b) bintree \<Rightarrow> ('b, 'a) PQ.pq \<Rightarrow> ('b, 'a) PQ.pq"
and
  bts_augment :: "('a::linorder, 'b) bintree list \<Rightarrow> ('b, 'a) PQ.pq \<Rightarrow> ('b, 'a) PQ.pq"
where
  "bt_augment (Node a v ts) q = PQ.push v a (bts_augment ts q)"
| "bts_augment [] q = q"
| "bts_augment (t # ts) q = bts_augment ts (bt_augment t q)"

lemma bts_augment [simp]:
  "bts_augment = fold bt_augment"
proof (rule ext)
  fix ts :: "('a, 'b) bintree list"
  show "bts_augment ts = fold bt_augment ts"
    by (induct ts) simp_all
qed

lemma bt_augment_Node [simp]:
  "bt_augment (Node a v ts) q = PQ.push v a (fold bt_augment ts q)"
  by (simp add: bts_augment)

lemma bt_augment_simp:
  "bt_augment t q = PQ.push (val t) (priority t) (fold bt_augment (children t) q)"
  by (cases t) (simp_all add: bts_augment)

declare bt_augment.simps [simp del] bts_augment.simps [simp del]

fun pqueue :: "('a::linorder, 'b) binqueue \<Rightarrow> ('b, 'a) PQ.pq" where
  Empty: "pqueue [] = PQ.empty"
| None: "pqueue (None # xs) = pqueue xs"
| Some: "pqueue (Some t # xs) = bt_augment t (pqueue xs)"

lemma bt_augment_v_subset:
  "set |q| \<subseteq> set |bt_augment t q|"
  "set |q| \<subseteq> set |bts_augment ts q|"
  by (induct t and ts arbitrary: q and q rule: bt_augment.induct bts_augment.induct) auto

lemma bt_augment_v_in:
  "v \<in> set |q| \<Longrightarrow> v \<in> set |bt_augment t q|"
  "v \<in> set |q| \<Longrightarrow> v \<in> set |bts_augment ts q|"
  using bt_augment_v_subset[of q] by auto

lemma bt_augment_v_union:
  "set |bt_augment t (bt_augment r q)| =
    set |bt_augment t q| \<union> set |bt_augment r q|"
  "set |bts_augment ts (bt_augment r q)| =
    set |bts_augment ts q| \<union> set |bt_augment r q|"
proof (induct t and ts arbitrary: q r and q r rule: bt_augment.induct bts_augment.induct)
  case Nil_bintree
    from bt_augment_v_subset[of q] show ?case by auto
qed auto

lemma bt_val_augment:
  shows "set (bt_dfs val t) \<union> set |q| = set |bt_augment t q|"
  and   "set (bts_dfs val ts) \<union> set |q| = set |bts_augment ts q|"
proof (induct t and ts rule: bt_augment.induct bts_augment.induct)
  case (Cons_bintree r rs)
  have "set |bts_augment rs (bt_augment r q)| =
    set |bts_augment rs q| \<union> set |bt_augment r q|" 
    by (simp only: bt_augment_v_union)
  
  with bt_augment_v_subset[of q]
    have "set |bts_augment rs (bt_augment r q)| =
      set |bts_augment rs q| \<union> set |bt_augment r q| \<union> set |q|" 
    by auto
  with Cons_bintree show ?case by auto
qed auto

lemma vals_pqueue:
  "set (vals xs) = set |pqueue xs|"
  by (induct xs) (simp_all add: bt_val_augment)

lemma bt_augment_v_push:
  "set |bt_augment t (PQ.push v a q)| = set |bt_augment t q| \<union> {v}"
  "set |bts_augment ts (PQ.push v a q)| = set |bts_augment ts q| \<union> {v}"
  using bt_val_augment[where q = "PQ.push v a q"] by (simp_all add: bt_val_augment)

lemma bt_augment_v_push_commute:
  "set |bt_augment t (PQ.push v a q)| = set |PQ.push v a (bt_augment t q)|"
  "set |bts_augment ts (PQ.push v a q)| = set |PQ.push v a (bts_augment ts q)|"
  by (simp_all add: bt_augment_v_push del: bts_augment)

lemma bts_augment_v_union:
  "set |bt_augment t (bts_augment rs q)| =
    set |bt_augment t q| \<union> set |bts_augment rs q|"
  "set |bts_augment ts (bts_augment rs q)| =
    set |bts_augment ts q| \<union> set |bts_augment rs q|"
proof (induct t and ts arbitrary: q rs and q rs rule: bt_augment.induct bts_augment.induct)
  case Nil_bintree
  from bt_augment_v_subset[of q] show ?case by auto
  
next 
  case (Cons_bintree x xs)
  let ?L = "set |bts_augment xs (bt_augment x (bts_augment rs q))|"
  
  from bt_augment_v_union
    have *: "\<And> q. set |bts_augment xs (bt_augment x q)| =
      set |bts_augment xs q| \<union> set |bt_augment x q|" by simp
  
  with Cons_bintree
    have "?L =
      set |bts_augment xs q| \<union> set |bts_augment rs q| \<union> set |bt_augment x q|"
      by auto
  with * show ?case by auto
qed simp

lemma bt_augment_v_commute:
  "set |bt_augment t (bt_augment r q)| = set |bt_augment r (bt_augment t q)|"
  "set |bt_augment t (bts_augment rs q)| = set |bts_augment rs (bt_augment t q)|"
  "set |bts_augment ts (bts_augment rs q)| =
    set |bts_augment rs (bts_augment ts q)|"
  unfolding bts_augment_v_union bt_augment_v_union by auto
  
lemma bt_augment_v_merge:
  "set |bt_augment (merge t r) q| = set |bt_augment t (bt_augment r q)|"
  by (simp add: bt_augment_simp [symmetric] bt_augment_v_push
    bt_augment_v_commute merge_def)

lemma vals_merge [simp]:
  "set (bt_dfs val (merge t r)) = set (bt_dfs val t) \<union> set (bt_dfs val r)"
  by (auto simp add: bt_dfs_simp merge_def)

lemma vals_merge_distinct:
  "distinct (bt_dfs val t) \<Longrightarrow> distinct (bt_dfs val r) \<Longrightarrow>
   set (bt_dfs val t) \<inter> set (bt_dfs val r) = {} \<Longrightarrow> 
   distinct (bt_dfs val (merge t r))"
  by (auto simp add: bt_dfs_simp merge_def)

lemma vals_add_Cons:
  "set (vals (add x xs)) = set (vals (x # xs))"
proof (cases x)
  case (Some t) then show ?thesis
    by (induct xs arbitrary: x t) auto
qed simp

lemma vals_add_distinct:
  assumes "distinct (vals xs)"
  and "distinct (dfs val [x])"
  and "set (vals xs) \<inter> set (dfs val [x]) = {}"
  shows "distinct (vals (add x xs))"
using assms
proof (cases x)
  case (Some t) with assms show ?thesis
  proof (induct xs arbitrary: x t)
    case (Some r xs)
    then have "set (bt_dfs val t) \<inter> set (bt_dfs val r) = {}" by auto
    with Some have "distinct (bt_dfs val (merge t r))" by (simp add: vals_merge_distinct)
    moreover
    with Some have "set (vals xs) \<inter> set (bt_dfs val (merge t r)) = {}" by auto

    moreover note Some
    ultimately show ?case by simp
  qed auto
qed simp
    
lemma vals_insert [simp]:
  "set (vals (insert a v xs)) = set (vals xs) \<union> {v}"
  by (simp add: insert_def vals_add_Cons)

lemma insert_v_push:
  "set (vals (insert a v xs)) = set |PQ.push v a (pqueue xs)|"
  by (simp add: vals_pqueue[symmetric])

lemma vals_meld:
  "set (dfs val (meld xs ys)) = set (dfs val xs) \<union> set (dfs val ys)"
proof (induct xs ys rule: meld.induct)
  case (3 xs y ys) then show ?case
  using set_dfs_Cons[of val y "meld xs ys"] using set_dfs_Cons[of val y ys] by auto
next
  case (4 x xs ys) then show ?case
  using set_dfs_Cons[of val x "meld xs ys"] using set_dfs_Cons[of val x xs] by auto
next
  case (5 x xs y ys) then show ?case by (auto simp add: vals_add_Cons)
qed simp_all

lemma vals_meld_distinct:
  "distinct (dfs val xs) \<Longrightarrow> distinct (dfs val ys) \<Longrightarrow>
   set (dfs val xs) \<inter> set (dfs val ys) = {} \<Longrightarrow>
   distinct (dfs val (meld xs ys))"
proof (induct xs ys rule: meld.induct)
  case (3 xs y ys) then show ?case
  proof (cases y)
    case None with "3" show ?thesis by simp
  next
    case (Some t)
    from "3" have A: "set (vals xs) \<inter> set (vals ys) = {}"
      using set_dfs_Cons[of val y ys] by auto
 
    moreover
    from Some "3" have "set (bt_dfs val t) \<inter> set (vals xs) = {}" by auto

    moreover
    from Some "3" have "set (bt_dfs val t) \<inter> set (vals ys) = {}" by simp

    ultimately have "set (bt_dfs val t) \<inter> set (vals (meld xs ys)) = {}"
      by (auto simp add: vals_meld)
    with "3" Some show ?thesis by auto
  qed
next
  case (4 x xs ys) then show ?case
  proof (cases x)
    case None with "4" show ?thesis by simp
  next
    case (Some t)
    from "4" have "set (vals xs) \<inter> set (vals ys) = {}"
      using set_dfs_Cons[of val x xs] by auto
 
    moreover
    from Some "4" have "set (bt_dfs val t) \<inter> set (vals xs) = {}" by simp

    moreover
    from Some "4" have "set (bt_dfs val t) \<inter> set (vals ys) = {}" by auto

    ultimately have "set (bt_dfs val t) \<inter> set (vals (meld xs ys)) = {}"
      by (auto simp add: vals_meld)
    with "4" Some show ?thesis by auto
  qed
next
  case (5 x xs y ys) then
  have "set (vals xs) \<inter> set (vals ys) = {}" by (auto simp add: set_dfs_Cons)
  with "5" have "distinct (vals (meld xs ys))" by simp

  moreover
  from "5" have "set (bt_dfs val x) \<inter> set (bt_dfs val y) = {}" by auto
  with "5" have "distinct (bt_dfs val (merge x y))"
    by (simp add: vals_merge_distinct)

  moreover
  from "5" have "set (vals (meld xs ys)) \<inter> set (bt_dfs val (merge x y)) = {}"
    by (auto simp add: vals_meld)

  ultimately show ?case by (simp add: vals_add_distinct)
qed simp_all

lemma bt_augment_alist_subset:
  "set (PQ.alist_of q) \<subseteq> set (PQ.alist_of (bt_augment t q))"
  "set (PQ.alist_of q) \<subseteq> set (PQ.alist_of (bts_augment ts q))"
proof (induct t and ts arbitrary: q and q rule: bt_augment.induct bts_augment.induct)
  case (Node a v rs)
  show ?case using Node[of q] by (auto simp add: bt_augment_simp set_insort_key)
qed auto

lemma bt_augment_alist_in:
  "(v,a) \<in> set (PQ.alist_of q) \<Longrightarrow> (v,a) \<in> set (PQ.alist_of (bt_augment t q))"
  "(v,a) \<in> set (PQ.alist_of q) \<Longrightarrow> (v,a) \<in> set (PQ.alist_of (bts_augment ts q))"
  using bt_augment_alist_subset[of q] by auto

lemma bt_augment_alist_union:
  "distinct (bts_dfs val (r # [t])) \<Longrightarrow> 
   set (bts_dfs val (r # [t])) \<inter> set |q| = {} \<Longrightarrow> 
   set (PQ.alist_of (bt_augment t (bt_augment r q))) =
     set (PQ.alist_of (bt_augment t q)) \<union> set (PQ.alist_of (bt_augment r q))"
  
  "distinct (bts_dfs val (r # ts)) \<Longrightarrow> 
   set (bts_dfs val (r # ts)) \<inter> set |q| = {} \<Longrightarrow> 
   set (PQ.alist_of (bts_augment ts (bt_augment r q))) =
     set (PQ.alist_of (bts_augment ts q)) \<union> set (PQ.alist_of (bt_augment r q))"
proof (induct t and ts arbitrary: q r and q r rule: bt_augment.induct bts_augment.induct)
  case Nil_bintree 
  from bt_augment_alist_subset[of q] show ?case by auto
next
  case (Node a v rs) then
  have
    "set (PQ.alist_of (bts_augment rs (bt_augment r q))) =
     set (PQ.alist_of (bts_augment rs q)) \<union> set (PQ.alist_of (bt_augment r q))" 
    by simp

  moreover
  from Node.prems have *: "v \<notin> set |bts_augment rs q| \<union> set |bt_augment r q|" unfolding bt_val_augment[symmetric] by simp
  hence "v \<notin> set |bts_augment rs (bt_augment r q)|" by (unfold bt_augment_v_union)

  moreover
  from * have "v \<notin> set |bts_augment rs q|" by simp

  ultimately show ?case by (simp add: set_insort_key)
next
  case (Cons_bintree x xs) then
  have \<comment> \<open>FIXME: ugly... and slow\<close>
    "distinct (bts_dfs val (x # xs))" and
    "distinct (bts_dfs val (r # xs))" and
    "distinct (bts_dfs val [r,x])" and
    "set (bts_dfs val (x # xs)) \<inter> set |bt_augment r q| = {}" and
    "set (bts_dfs val (x # xs)) \<inter> set |q| = {}" and
    "set (bts_dfs val [r, x]) \<inter> set |q| = {}" and
    "set (bts_dfs val (r # xs)) \<inter> set |q| = {}"
    unfolding bt_val_augment[symmetric] by auto
  with Cons_bintree.hyps show ?case by auto
qed

lemma bt_alist_augment:
  "distinct (bt_dfs val t) \<Longrightarrow> 
   set (bt_dfs val t) \<inter> set |q| = {} \<Longrightarrow> 
   set (bt_dfs alist t) \<union> set (PQ.alist_of q) = set (PQ.alist_of (bt_augment t q))"
  
  "distinct (bts_dfs val ts) \<Longrightarrow> 
   set (bts_dfs val ts) \<inter> set |q| = {} \<Longrightarrow> 
   set (bts_dfs alist ts) \<union> set (PQ.alist_of q) =
     set (PQ.alist_of (bts_augment ts q))"
proof (induct t and ts rule: bt_augment.induct bts_augment.induct)
  case Nil_bintree then show ?case by simp
next
  case (Node a v rs)
  hence "v \<notin> set |bts_augment rs q|"
    unfolding bt_val_augment[symmetric] by simp
  with Node show ?case by (simp add: set_insort_key)
next
  case (Cons_bintree r rs) then
  have "set (PQ.alist_of (bts_augment (r # rs) q)) =
    set (PQ.alist_of (bts_augment rs q)) \<union> set (PQ.alist_of (bt_augment r q))"
    using bt_augment_alist_union by simp
  with Cons_bintree bt_augment_alist_subset show ?case by auto
qed

lemma alist_pqueue:
  "distinct (vals xs) \<Longrightarrow> set (dfs alist xs) = set (PQ.alist_of (pqueue xs))"
  by (induct xs) (simp_all add: vals_pqueue bt_alist_augment)

lemma alist_pqueue_priority:
  "distinct (vals xs) \<Longrightarrow> (v, a) \<in> set (dfs alist xs)
    \<Longrightarrow> PQ.priority (pqueue xs) v = Some a"
  by (simp add: alist_pqueue PQ.priority_def)

lemma prios_pqueue:
  "distinct (vals xs) \<Longrightarrow> set (prios xs) = set \<parallel>pqueue xs\<parallel>"
  by (auto simp add: alist_pqueue priorities_set alist_split_set)

lemma alist_merge [simp]:
  "distinct (bt_dfs val t) \<Longrightarrow> distinct (bt_dfs val r) \<Longrightarrow>
   set (bt_dfs val t) \<inter> set (bt_dfs val r) = {} \<Longrightarrow> 
   set (bt_dfs alist (merge t r)) = set (bt_dfs alist t) \<union> set (bt_dfs alist r)"
  by (auto simp add: bt_dfs_simp merge_def alist_split)

lemma alist_add_Cons:
  assumes "distinct (vals (x#xs))"
  shows "set (dfs alist (add x xs)) = set (dfs alist (x # xs))"
using assms proof (induct xs arbitrary: x)
  case Empty then show ?case by (cases x) simp_all
next
  case None then show ?case by (cases x) simp_all
next
  case (Some y ys) then
  show ?case 
  proof (cases x)
    case (Some t)
    note prem = Some.prems Some
    
    from prem have "distinct (bt_dfs val (merge t y))"
      by (auto simp add: bt_dfs_simp merge_def)
    with prem have "distinct (vals (Some (merge t y) # ys))" by auto
    with prem Some.hyps
      have "set (dfs alist (add (Some (merge t y)) ys)) =
        set (dfs alist (Some (merge t y) # ys))" by simp

    moreover
    from prem have "set (bt_dfs val t) \<inter> set (bt_dfs val y) = {}" by auto
    with prem
      have "set (bt_dfs alist (merge t y)) =
        set (bt_dfs alist t) \<union> set (bt_dfs alist y)"
      by simp

    moreover note prem and Un_assoc
      
    ultimately
    show ?thesis by simp
  qed simp
qed

lemma alist_insert [simp]:
  "distinct (vals xs) \<Longrightarrow> 
   v \<notin> set (vals xs) \<Longrightarrow>
   set (dfs alist (insert a v xs)) = set (dfs alist xs) \<union> {(v,a)}"
  by (simp add: insert_def alist_add_Cons)

lemma insert_push:
  "distinct (vals xs) \<Longrightarrow>
   v \<notin> set (vals xs) \<Longrightarrow>
   set (dfs alist (insert a v xs)) = set (PQ.alist_of (PQ.push v a (pqueue xs)))"
  by (simp add: alist_pqueue vals_pqueue set_insort_key)

lemma insert_p_push:
  assumes "distinct (vals xs)"
  and "v \<notin> set (vals xs)"
  shows "set (prios (insert a v xs)) = set \<parallel>PQ.push v a (pqueue xs)\<parallel>"
proof -
  from assms
    have "set (dfs alist (insert a v xs)) =
      set (PQ.alist_of (PQ.push v a (pqueue xs)))"
    by (rule insert_push)
  thus ?thesis by (simp add: alist_split_set priorities_set)
qed

lemma empty_empty:
  "normalized xs \<Longrightarrow> xs = empty \<longleftrightarrow> PQ.is_empty (pqueue xs)"
proof (rule iffI)
  assume "xs = []" then show "PQ.is_empty (pqueue xs)" by simp
next
  assume N: "normalized xs" and E: "PQ.is_empty (pqueue xs)"
  show "xs = []"
  proof (rule ccontr)
    assume "xs \<noteq> []"
    with N have "set (vals xs) \<noteq> {}"
      by (induct xs) (simp_all add: bt_dfs_simp dfs_append)
    hence "set |pqueue xs| \<noteq> {}" by (simp add: vals_pqueue)

    moreover
    from E have "set |pqueue xs| = {}" by (simp add: is_empty_empty)
    
    ultimately show False by simp
  qed
qed
  
lemma bt_dfs_Min_priority:
  assumes "is_heap t"
  shows "priority t = Min (set (bt_dfs priority t))"
using assms
proof (induct "priority t" "children t" arbitrary: t)
  case is_heap_list_Nil then show ?case by (simp add: bt_dfs_simp)
next
  case (is_heap_list_Cons rs r t) note cons = this
  let ?M = "Min (set (bt_dfs priority t))"
  
  obtain t' where "t' = Node (priority t) (val t) rs" by auto
  hence ot: "rs = children t'" "priority t' = priority t" by simp_all
  with is_heap_list_Cons have "priority t = Min (set (bt_dfs priority t'))"
    by simp
  with ot
    have "priority t = Min (Set.insert (priority t) (set (bts_dfs priority rs)))"
    by (simp add: bt_dfs_simp)

  moreover
  from cons have "priority r = Min (set (bt_dfs priority r))" by simp

  moreover
  from cons have "children t = r # rs" by simp
  then have "bts_dfs priority (children t) =
    (bt_dfs priority r) @ (bts_dfs priority rs)" by simp
  hence "bt_dfs priority t =
    priority t # (bt_dfs priority r @ bts_dfs priority rs)"
    by (simp add: bt_dfs_simp)
  hence A: "?M = Min
    (Set.insert (priority t) (set (bt_dfs priority r) \<union> set (bts_dfs priority rs)))"
    by simp
  
  have "Set.insert (priority t) (set (bt_dfs priority r)
    \<union> set (bts_dfs priority rs)) =
    Set.insert (priority t) (set (bts_dfs priority rs)) \<union> set (bt_dfs priority r)"
    by auto
  with A have "?M = Min
    (Set.insert (priority t) (set (bts_dfs priority rs)) \<union> set (bt_dfs priority r))"
    by simp
  
  with Min_Un
    [of "Set.insert (priority t) (set (bts_dfs priority rs))" "set (bt_dfs priority r)"] 
  have "?M =
    ord_class.min (Min (Set.insert (priority t) (set (bts_dfs priority rs))))
      (Min (set (bt_dfs priority r)))" 
    by (auto simp add: bt_dfs_simp)

  ultimately 
  have "?M = ord_class.min (priority t) (priority r)" by simp

  with \<open>priority t \<le> priority r\<close> show ?case by (auto simp add: ord_class.min_def)
qed

lemma is_binqueue_min_Min_prios:
  assumes "is_binqueue l xs"
  and "normalized xs"
  and "xs \<noteq> []"
  shows "min xs = Some (Min (set (prios xs)))"
using assms
proof (induct xs)
  case (Some l xs x) then show ?case
  proof (cases "xs \<noteq> []")
    case False with Some show ?thesis
      using bt_dfs_Min_priority[of x] by (simp add: min_single)
  next
    case True note T = this Some
    
    from T have "normalized xs" by simp
    with \<open>xs \<noteq> []\<close> have "prios xs \<noteq> []" by (induct xs) (simp_all add: bt_dfs_simp)
    with T show ?thesis
      using Min_Un[of "set (bt_dfs priority x)" "set (prios xs)"]
      using bt_dfs_Min_priority[of x]
      by (auto simp add: bt_dfs_simp ord_class.min_def)
  qed
qed simp_all
  
lemma min_p_min:
  assumes "is_binqueue l xs"
  and "xs \<noteq> []"
  and "normalized xs"
  and "distinct (vals xs)"
  and "distinct (prios xs)"
  shows "min xs = PQ.priority (pqueue xs) (PQ.min (pqueue xs))"
proof -
  from \<open>xs \<noteq> []\<close> \<open>normalized xs\<close> have "\<not> PQ.is_empty (pqueue xs)"
    by (simp add: empty_empty)

  moreover
  from assms have "min xs = Some (Min (set (prios xs)))"
    by (simp add: is_binqueue_min_Min_prios)
  with \<open>distinct (vals xs)\<close> have "min xs = Some (Min (set \<parallel>pqueue xs\<parallel> ))"
    by (simp add: prios_pqueue)

  ultimately show ?thesis
   by (simp add: priority_Min_priorities [where q = "pqueue xs"] )
qed

lemma find_min_p_min:
  assumes "is_binqueue l xs"
  and "xs \<noteq> []"
  and "normalized xs"
  and "distinct (vals xs)"
  and "distinct (prios xs)"
  shows "priority (the (find_min xs)) =
    the (PQ.priority (pqueue xs) (PQ.min (pqueue xs)))"
proof -
  from assms have "min xs \<noteq> None" by (simp add: normalized_min_not_None)
  from assms have "min xs = PQ.priority (pqueue xs) (PQ.min (pqueue xs))"
    by (simp add: min_p_min)
  with \<open>min xs \<noteq> None\<close> show ?thesis by (auto simp add: min_eq_find_min_Some)
qed

lemma find_min_v_min:
  assumes "is_binqueue l xs"
  and "xs \<noteq> []"
  and "normalized xs"
  and "distinct (vals xs)"
  and "distinct (prios xs)"
  shows "val (the (find_min xs)) = PQ.min (pqueue xs)"
proof -
  from assms have "min xs \<noteq> None" by (simp add: normalized_min_not_None)
  then obtain a where oa: "Some a = min xs" by auto
  then obtain t where ot: "find_min xs = Some t" "priority t = a"
    using min_eq_find_min_Some [of xs a] by auto
    
  hence *: "(val t, a) \<in> set (dfs alist xs)"
    by (auto simp add: find_min_exist in_set_in_alist)

  have "PQ.min (pqueue xs) = val t"
  proof (rule ccontr)    
    assume A: "PQ.min (pqueue xs) \<noteq> val t"
    then obtain t' where ot':"PQ.min (pqueue xs) = t'" by simp
    with A have NE: "val t \<noteq> t'" by simp
    
    from ot' oa assms have "(t', a) \<in> set (dfs alist xs)"
      by (simp add: alist_pqueue PQ.priority_def min_p_min)

    with * NE have "\<not> distinct (prios xs)" 
      unfolding alist_split(2) 
      unfolding dfs_comp 
      by (induct ("dfs alist xs")) (auto simp add: rev_image_eqI)
    with \<open>distinct (prios xs)\<close> show False by simp
  qed
  with ot show ?thesis by auto
qed

lemma alist_normalize_idem:
  "dfs alist (normalize xs) = dfs alist xs"
unfolding normalize_def
proof (induct xs rule: rev_induct)
  case (snoc x xs) then show ?case by (cases x) (simp_all add: dfs_append)
qed simp

lemma dfs_match_not_in:
  "(\<forall> t. Some t \<in> set xs \<longrightarrow> priority t \<noteq> a) \<Longrightarrow>
    set (dfs f (map (match a) xs)) = set (dfs f xs)"
by (induct xs) simp_all

lemma dfs_match_subset:
  "set (dfs f (map (match a) xs)) \<subseteq> set (dfs f xs)"
proof (induct xs rule: list.induct)
  case (Cons x xs) then show ?case by (cases x) auto
qed simp

lemma dfs_match_distinct:
  "distinct (dfs f xs) \<Longrightarrow> distinct (dfs f (map (match a) xs))"
proof (induct xs rule: list.induct)
  case (Cons x xs) then show ?case
    using dfs_match_subset[of f a xs]
    by (cases x, auto)
qed simp

lemma dfs_match:
  "distinct (prios xs) \<Longrightarrow> 
   distinct (dfs f xs) \<Longrightarrow>
   Some t \<in> set xs \<Longrightarrow> 
   priority t = a \<Longrightarrow> 
   set (dfs f (map (match a) xs)) = set (dfs f xs) - set (bt_dfs f t)"
proof (induct xs arbitrary: t)
  case (Some r xs t) then show ?case 
  proof (cases "t = r")
    case True 
    from Some have "priority r \<notin> set (prios xs)" by (auto simp add: bt_dfs_simp)
    with Some True have "a \<notin> set (prios xs)" by simp
    hence "\<forall> s. Some s \<in> set xs \<longrightarrow> priority s \<noteq> a"
      by (induct xs) (auto simp add: bt_dfs_simp)
    hence "set (dfs f (map (match a) xs)) = set (dfs f xs)"
      by (simp add: dfs_match_not_in)
    with True Some show ?thesis by auto
  next
    case False
    with Some.prems have "Some t \<in> set xs" by simp
    with \<open>priority t = a\<close> have "a \<in> set (prios xs)"
    proof (induct xs)
      case (Some x xs) then show ?case
        by (cases "t = x") (simp_all add: bt_dfs_simp)
    qed simp_all
    with False Some have "priority r \<noteq> a" by (auto simp add: bt_dfs_simp)

    moreover 
    from Some False
      have "set (dfs f (map (match a) xs)) = set (dfs f xs) - set (bt_dfs f t)"
      by simp

    moreover
    from Some.prems False have "set (bt_dfs f t) \<inter> set (bt_dfs f r) = {}"
      by (induct xs) auto
    hence "set (bt_dfs f r) - set (bt_dfs f t) = set (bt_dfs f r)" by auto
    
    ultimately show ?thesis by auto
  qed
qed simp_all

lemma alist_meld:
  "distinct (dfs val xs) \<Longrightarrow> distinct (dfs val ys) \<Longrightarrow>
   set (dfs val xs) \<inter> set (dfs val ys) = {} \<Longrightarrow>
   set (dfs alist (meld xs ys)) = set (dfs alist xs) \<union> set (dfs alist ys)"
proof (induct xs ys rule: meld.induct)
  case (3 xs y ys)
  have "set (dfs alist (y # meld xs ys)) =
    set (dfs alist xs) \<union> set (dfs alist (y # ys))"
  proof -
    note assms = "3"
    from assms have "set (vals xs) \<inter> set (vals ys) = {}"
      using set_dfs_Cons[of val y ys] by auto

    moreover
    from assms have "distinct (vals ys)" by (cases y) simp_all

    moreover
    from assms have "distinct (vals xs)" by simp

    moreover note assms
    ultimately have "set (dfs alist (meld xs ys)) =
      set (dfs alist xs) \<union> set (dfs alist ys)" by simp
    
    hence "set (dfs alist (y # meld xs ys)) =
      set (dfs alist [y]) \<union> set (dfs alist xs) \<union> set (dfs alist ys)"
      using set_dfs_Cons[of alist y "meld xs ys"] by auto

    then show ?thesis using set_dfs_Cons[of alist y ys] by auto
  qed
  thus ?case by simp
next
  case (4 x xs ys)
  have "set (dfs alist (x # meld xs ys)) =
    set (dfs alist (x # xs)) \<union> set (dfs alist ys)"
  proof - (* this is the same as for 3 minus some renaming *)
    note assms = "4"
    from assms have "set (vals xs) \<inter> set (vals ys) = {}"
      using set_dfs_Cons[of val x xs] by auto

    moreover
    from assms have "distinct (vals xs)" by (cases x) simp_all

    moreover
    from assms have "distinct (vals ys)" by simp

    moreover note assms
    ultimately have "set (dfs alist (meld xs ys)) =
      set (dfs alist xs) \<union> set (dfs alist ys)" by simp
    
    hence "set (dfs alist (x # meld xs ys)) =
      set (dfs alist [x]) \<union> set (dfs alist xs) \<union> set (dfs alist ys)"
      using set_dfs_Cons[of alist x "meld xs ys"] by auto

    then show ?thesis using set_dfs_Cons[of alist x xs] by auto
  qed
  thus ?case by simp
next
  case (5 x xs y ys)
  have "set (dfs alist (add (Some (merge x y)) (meld xs ys))) =
    set (bt_dfs alist x) \<union> set (dfs alist xs)
    \<union> set (bt_dfs alist y) \<union> set (dfs alist ys)"
  proof -
    note assms = "5"
    
    from assms have "distinct (bt_dfs val x)" "distinct (bt_dfs val y)" by simp_all
    moreover from assms have xyint:
      "set (bt_dfs val x) \<inter> set (bt_dfs val y) = {}" by (auto simp add: set_dfs_Cons)
    ultimately have *: "set (dfs alist [Some (merge x y)]) =
      set (bt_dfs alist x) \<union> set (bt_dfs alist y)" by auto

    moreover
    from assms
      have **: "set (dfs alist (meld xs ys)) = set (dfs alist xs) \<union> set (dfs alist ys)"
      by (auto simp add: set_dfs_Cons)

    moreover
    from assms have "distinct (vals (Some (merge x y) # meld xs ys))"
    proof -
      from assms xyint have "distinct (bt_dfs val (merge x y))"
        by (simp add: vals_merge_distinct)

      moreover
      from assms have 
        "distinct (vals xs)" 
        and "distinct (vals ys)" 
        and "set (vals xs) \<inter> set (vals ys) = {}"
        by (auto simp add: set_dfs_Cons)
      hence "distinct (vals (meld xs ys))" by (rule vals_meld_distinct)

      moreover
      from assms
        have "set (bt_dfs val (merge x y)) \<inter> set (vals (meld xs ys)) = {}"
        by (auto simp add: vals_meld)

      ultimately show ?thesis by simp
    qed
   
    ultimately show ?thesis by (auto simp add: alist_add_Cons)
  qed
  thus ?case by auto
qed simp_all

lemma alist_delete_min:
  assumes "distinct (vals xs)"
  and "distinct (prios xs)"
  and "find_min xs = Some (Node a v ts)"
  shows "set (dfs alist (delete_min xs)) = set (dfs alist xs) - {(v, a)}"
proof -
  from \<open>distinct (vals xs)\<close> have d: "distinct (dfs alist xs)"
    using dfs_comp_distinct[of fst alist "xs"]
    by (simp only: alist_split)

  from assms have IN: "Some (Node a v ts) \<in> set xs"
    by (simp add: find_min_exist)
  hence sub: "set (bts_dfs alist ts) \<subseteq> set (dfs alist xs)"
    by (induct xs) (auto simp add: bt_dfs_simp)

  from d IN have "(v,a) \<notin> set (bts_dfs alist ts)"
    using dfs_distinct_member[of alist xs "Node a v ts"] by simp
  with sub have "set (bts_dfs alist ts) \<subseteq> set (dfs alist xs) - {(v,a)}" by blast
  hence nu: "set (bts_dfs alist ts) \<union> (set (dfs alist xs) - {(v,a)}) =
    set (dfs alist xs) - {(v,a)}" by auto

  from assms have "distinct (vals (map (match a) xs))"
    by (simp add: dfs_match_distinct)
 
  moreover  
  from IN assms have "distinct (bts_dfs val ts)"
    using dfs_distinct_member[of val xs "Node a v ts"]
    by (simp add: bt_dfs_distinct_children)
  hence "distinct (vals (map Some (rev ts)))"
    by (simp add: bts_dfs_rev_distinct dfs_map_Some_idem)

  moreover
  from assms IN have "set (dfs val (map (match a) xs)) =
    set (dfs val xs) - set (bt_dfs val (Node a v ts))"
    by (simp add: dfs_match)
  hence "set (vals (map (match a) xs)) \<inter> set (vals (map Some (rev ts))) = {}"
    by (auto simp add: dfs_map_Some_idem set_bts_dfs_rev)

  ultimately
  have "set (dfs alist (meld (map Some (rev ts)) (map (match a) xs))) =
    set (dfs alist (map Some (rev ts))) \<union> set (dfs alist (map (match a) xs))"
    using alist_meld by auto

  with assms d IN nu show ?thesis
    by (simp add: delete_min_def alist_normalize_idem set_bts_dfs_rev dfs_map_Some_idem
     dfs_match Diff_insert2 [of "set (dfs alist xs)" "(v,a)" "set (bts_dfs alist ts)"])
qed

lemma alist_remove_min:
  assumes "is_binqueue l xs"
  and "distinct (vals xs)"
  and "distinct (prios xs)"
  and "normalized xs"
  and "xs \<noteq> []"
  shows "set (dfs alist (delete_min xs)) =
  set (PQ.alist_of (PQ.remove_min (pqueue xs)))"
proof -
  from assms obtain t where ot: "find_min xs = Some t"
    using normalized_find_min_exists by auto
  with assms show ?thesis
  proof (cases t)
    case (Node a v ys)
    from assms have "\<not> PQ.is_empty (pqueue xs)" by (simp add: empty_empty)
    hence "set (PQ.alist_of (PQ.remove_min (pqueue xs))) =
      set (PQ.alist_of (pqueue xs)) - {(PQ.min (pqueue xs),
        the (PQ.priority (pqueue xs) (PQ.min (pqueue xs))))}"
      by (simp add: set_alist_of_remove_min[of "pqueue xs"] del: alist_of_remove_min)
    
    moreover
    from assms ot Node
    have "set (dfs alist (delete_min xs)) = set (dfs alist xs) - {(v, a)}"
      using alist_delete_min[of xs] by simp

    moreover
    from Node ot have "priority (the (find_min xs)) = a" by simp
    with assms have "a = the (PQ.priority (pqueue xs) (PQ.min (pqueue xs)))"
      by (simp add: find_min_p_min)

    moreover
    from Node ot have "val (the (find_min xs)) = v" by simp
    with assms have "v = PQ.min (pqueue xs)" by (simp add: find_min_v_min)
    
    moreover note \<open>distinct (vals xs)\<close>
    ultimately show ?thesis by (simp add: alist_pqueue)
  qed
qed

no_notation
  "PQ.values" ("|(_)|")
  and "PQ.priorities" ("\<parallel>(_)\<parallel>")

end
