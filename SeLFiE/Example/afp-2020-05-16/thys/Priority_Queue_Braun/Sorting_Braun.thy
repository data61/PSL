(* Authors: Tobias Nipkow and Thomas Sewell *)

section "Sorting via Priority Queues Based on Braun Trees"

theory Sorting_Braun
imports Priority_Queue_Braun
begin

text \<open>This theory is about sorting algorithms based on heaps.
Algorithm A can be found here
\<^url>\<open>http://www.csse.canterbury.ac.nz/walter.guttmann/publications/0005.pdf\<close> on p. 54.
(published here \<^url>\<open>http://www.jucs.org/doi?doi=10.3217/jucs-009-02-0173\<close>)
Not really the classic heap sort but a mixture of heap sort and merge sort.
The algorithm (B) in Larry's book comes closer to the classic heap sort:
\<^url>\<open>https://www.cl.cam.ac.uk/~lp15/MLbook/programs/sample7.sml\<close>.

Both algorithms have two phases:
build a heap from a list, then extract the elements of the heap into a sorted list.
\<close>

abbreviation(input)
  "nlog2 n == nat(ceiling(log 2 n))"

section \<open>Phase 1: List to Tree\<close>

text \<open>Algorithm A does this naively, in $O(n lg n)$ fashion and generates a Braun tree:\<close>

fun heap_of_A :: "('a::linorder) list \<Rightarrow> 'a tree" where
"heap_of_A [] = Leaf" |
"heap_of_A (a#as) = insert a (heap_of_A as)"

(* just for testing
definition
  shuffle100 :: "nat list"
  where
  "shuffle100 = [50 :: nat, 7, 77, 15, 42, 82, 87, 68, 69, 29, 43, 24, 84, 12, 35, 30, 95, 45, 14, 47, 54, 66, 96, 71, 98, 4, 22, 0, 92, 86, 34, 33, 57, 91, 20, 13, 64, 73, 70, 8, 85, 40, 16, 18, 81, 99, 63, 41, 56, 72, 79, 48, 78, 52, 25, 49, 65, 90, 26, 76, 3, 59, 74, 58, 46, 38, 61, 94, 75, 11, 88, 31, 53, 17, 44, 89, 39, 93, 62, 5, 1, 21, 6, 55, 83, 28, 37, 60, 19, 67, 23, 97, 51, 10, 27, 32, 2, 36, 9, 80]"

value "heap_of_A shuffle100"
*)

lemma heap_heap_of_A: "heap (heap_of_A xs)"
by(induction xs)(simp_all add: heap_insert)

lemma braun_heap_of_A: "braun (heap_of_A xs)"
by(induction xs)(simp_all add: braun_insert)

lemma mset_tree_heap_of_A: "mset_tree (heap_of_A xs) = mset xs"
by(induction xs)(simp_all add: mset_insert)

text \<open>Running time is n*log n, which we can approximate with height.\<close>

fun t_insert :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
"t_insert a Leaf = 1" |
"t_insert a (Node l x r) =
 (if a < x then 1 + t_insert x r else 1 + t_insert a r)"

fun t_heap_of_A :: "('a::linorder) list \<Rightarrow> nat" where
"t_heap_of_A [] = 0" |
"t_heap_of_A (a#as) = t_insert a (heap_of_A as) + t_heap_of_A as"

lemma t_insert_height:
  "t_insert x t \<le> height t + 1"
  apply (induct t arbitrary: x; simp)
  apply (simp only: max_Suc_Suc[symmetric] le_max_iff_disj, simp)
  done

lemma height_insert_ge:
  "height t \<le> height (insert x t)"
  apply (induct t arbitrary: x; simp add: le_max_iff_disj)
  apply (metis less_imp_le_nat less_le_trans not_le_imp_less)
  done

lemma t_heap_of_A_bound:
  "t_heap_of_A xs \<le> length xs * (height (heap_of_A xs) + 1)"
proof (induct xs)
  case (Cons x xs)

  let ?lhs = "t_insert x (heap_of_A xs) + t_heap_of_A xs"

  have "?lhs \<le> ?lhs"
    by simp
  also note Cons
  also note height_insert_ge[of "heap_of_A xs" x]
  also note t_insert_height[of x "heap_of_A xs"]

  finally show ?case
    apply simp
    apply (erule order_trans)
    apply (simp add: height_insert_ge)
    done
qed simp_all

lemma size_heap_of_A:
  "size (heap_of_A xs) = length xs"
  using arg_cong[OF mset_tree_heap_of_A, of size xs]
  by simp

lemma t_heap_of_A_log_bound:
  "t_heap_of_A xs \<le> length xs * (nlog2 (length xs + 1) + 1)"
  using t_heap_of_A_bound[of xs]
    balanced_if_braun[OF braun_heap_of_A, of xs]
  by (simp add: height_balanced size1_size size_heap_of_A)

text \<open>Algorithm B mimics heap sort more closely by building heaps bottom up in a balanced way:\<close>

fun heapify :: "nat \<Rightarrow> ('a::linorder) list \<Rightarrow> 'a tree * 'a list" where
"heapify 0 xs = (Leaf, xs)" |
"heapify (Suc n) (x#xs) =
	 (let (l, ys) = heapify (Suc n div 2) xs;
		    (r, zs) = heapify (n div 2) ys
	  in (sift_down l x r, zs))"

text \<open>The result should be a Braun tree:\<close>

lemma heapify_snd:
  "n \<le> length xs \<Longrightarrow> snd (heapify n xs) = drop n xs"
  apply (induct xs arbitrary: n rule: measure_induct[where f=length])
  apply (case_tac n; simp)
  apply (clarsimp simp: Suc_le_length_iff case_prod_beta)
  apply (rule arg_cong[where f="\<lambda>n. drop n xs" for xs])
  apply simp
  done

lemma heapify_snd_tup:
  "heapify n xs = (t, ys) \<Longrightarrow> n \<le> length xs \<Longrightarrow> ys = drop n xs"
  by (drule heapify_snd, simp)

lemma heapify_correct:
  "n \<le> length xs \<Longrightarrow> heapify n xs = (t, ys) \<Longrightarrow>
    size t = n \<and> heap t \<and> braun t \<and> mset_tree t = mset (take n xs)"
proof (induct n xs arbitrary: t ys rule: heapify.induct)
  case (2 n x xs)

  note len = "2.prems"(1)

  obtain t1 ys1 where h1: "heapify (Suc n div 2) xs = (t1, ys1)"
    by (simp add: prod_eq_iff)
  obtain t2 ys2 where h2: "heapify (n div 2) ys1 = (t2, ys2)"
    by (simp add: prod_eq_iff)

  from len have le1: "Suc n div 2 \<le> length xs"
    by simp
  note ys1 = heapify_snd_tup[OF h1 le1]
  from len have le2: "n div 2 \<le> length ys1"
    by (simp add: ys1)

  note app_hyps = "2.hyps"(1)[OF le1 h1]
    "2.hyps"(2)[OF refl h1[symmetric], simplified, OF le2 h2]

  hence braun: "braun (Node t1 x t2)"
    by (simp, linarith)

  have eq:
    "n div 2 + Suc n div 2 = n"
    by simp

  have msets:
    "mset (take (Suc n div 2) xs) + mset (take (n div 2) ys1) = mset (take n xs)"
    apply (subst append_take_drop_id[symmetric, where n="Suc n div 2" and t="take n xs"],
        subst mset_append)
    apply (simp add: take_drop min_absorb1 le1 eq ys1)
    done

  from "2.prems" app_hyps msets show ?case
    apply (clarsimp simp: h1 h2 le2)
    apply (clarsimp simp: size_sift_down[OF braun]
                       braun_sift_down[OF braun]
                       mset_sift_down[OF braun])
    apply (simp add: heap_sift_down[OF braun])
    done
qed simp_all

lemma braun_heapify:
  "n \<le> length xs \<Longrightarrow> braun (fst (heapify n xs))"
  by (cases "heapify n xs", drule(1) heapify_correct, simp)

lemma heap_heapify:
  "n \<le> length xs \<Longrightarrow> heap (fst (heapify n xs))"
  by (cases "heapify n xs", drule(1) heapify_correct, simp)

lemma mset_heapify:
  "n \<le> length xs \<Longrightarrow> mset_tree (fst (heapify n xs)) = mset (take n xs)"
  by (cases "heapify n xs", drule(1) heapify_correct, simp)

text \<open>The running time of heapify is linear.
  (similar to \<^url>\<open>https://en.wikipedia.org/wiki/Binary_heap#Building_a_heap\<close>)

This is an interesting result, so we embark on this exercise
to prove it the hard way.
\<close>

context includes pattern_aliases
begin

function (sequential) t_sift_down :: "'a::linorder tree \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> nat" where
"t_sift_down Leaf a Leaf = 1" |
"t_sift_down (Node Leaf x Leaf) a Leaf = 2" |
"t_sift_down (Node l1 x1 r1 =: t1) a (Node l2 x2 r2 =: t2) =
  (if a \<le> x1 \<and> a \<le> x2
   then 1
   else if x1 \<le> x2 then 1 + t_sift_down l1 a r1
        else 1 + t_sift_down l2 a r2)"
by pat_completeness auto

termination
by (relation "measure (%(l,a,r). size l + size r)") auto

end

fun t_heapify :: "nat \<Rightarrow> ('a::linorder) list \<Rightarrow> nat" where
"t_heapify 0 xs = 1" |
"t_heapify (Suc n) (x#xs) =
	 (let (l, ys) = heapify (Suc n div 2) xs;
        t1 = t_heapify (Suc n div 2) xs;
        (r, zs) = heapify (n div 2) ys;
		    t2 = t_heapify (n div 2) ys
	  in 1 + t1 + t2 + t_sift_down l x r)"

lemma t_sift_down_height:
  "braun (Node l x r) \<Longrightarrow> t_sift_down l x r \<le> height (Node l x r)"
  by (induct l x r rule: t_sift_down.induct; auto)

lemma sift_down_height:
  "braun (Node l x r) \<Longrightarrow> height (sift_down l x r) \<le> height (Node l x r)"
  by (induct l x r rule: sift_down.induct; auto simp: Let_def)

lemma braun_height_r_le:
  "braun (Node l x r) \<Longrightarrow> height r \<le> height l"
  by (rule balanced_optimal, auto intro: balanced_if_braun)

lemma braun_height_l_le:
  assumes b: "braun (Node l x r)"
  shows "height l \<le> Suc (height r)"
  using b balanced_if_braun[OF b] min_height_le_height[of r]
  by (simp add: balanced_def)

lemma braun_height_node_eq:
  assumes b: "braun (Node l x r)"
  shows "height (Node l x r) = Suc (height l)"
  using b braun_height_r_le[OF b]
  by (auto simp add: max_def)

lemma t_heapify_induct:
  "i \<le> length xs \<Longrightarrow> t_heapify i xs + height (fst (heapify i xs)) \<le> 5 * i + 1"
proof (induct i xs rule: t_heapify.induct)
  case (1 vs)
  thus ?case
    by simp
next
  case (2 i x xs)

  obtain l ys where h1: "heapify (Suc i div 2) xs = (l, ys)"
    by (simp add: prod_eq_iff)
  note hyps1 = "2.hyps"[OF h1[symmetric] refl, simplified]
  obtain r zs where h2: "heapify (i div 2) ys = (r, zs)"
    by (simp add: prod_eq_iff)

  from "2.prems" heapify_snd_tup[OF h1]
  have le1: "Suc i div 2 \<le> length xs"
    and le2: "i div 2 \<le> length xs"
    and le4: "i div 2 \<le> length ys"
    by simp_all

  note hyps2 = hyps1(1)[OF le1] hyps1(2)[OF refl h2[symmetric] refl le4]

  note prem = add_le_mono[OF add_le_mono[OF hyps2] order_refl[where x=3]]

  from heapify_correct[OF le1 h1] heapify_correct[OF le4 h2]
  have braun: "braun \<langle>l, x, r\<rangle>"
    by auto

  have t_sift_l:
    "t_sift_down l x r \<le> height l + 1"
    using t_sift_down_height[OF braun] braun_height_r_le[OF braun]
    by simp

  from t_sift_down_height[OF braun]
  have height_sift_r:
    "height (sift_down l x r) \<le> height r + 2"
    using sift_down_height[OF braun] braun_height_l_le[OF braun]
    by simp

  from h1 h2 t_sift_l height_sift_r "2.prems"
  show ?case
    apply simp
    apply (rule order_trans, rule order_trans[rotated], rule prem)
     apply simp_all
    apply (simp only: mult_le_cancel1 add_mult_distrib2[symmetric])
    apply simp
    done

qed simp_all

lemma t_heapify_bound:
  "i \<le> length xs \<Longrightarrow> t_heapify i xs \<le> 5 * i + 1"
  using t_heapify_induct[of i xs]
  by simp

section \<open>Phase 2: Heap to List\<close>

text\<open>Algorithm A extracts (\<open>list_of_A\<close>) the list by removing the root and merging the children:\<close>


(* For termination of \<open>merge\<close> only: *)
lemma size_prod_measure[measure_function]:
  "is_measure f \<Longrightarrow> is_measure g \<Longrightarrow> is_measure (size_prod f g)"
by (rule is_measure_trivial)

fun merge :: "('a::linorder) tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"merge Leaf t2 = t2" |
"merge t1 Leaf = t1" |
"merge (Node l1 a1 r1) (Node l2 a2 r2) =
   (if a1 \<le> a2 then Node (merge l1 r1) a1 (Node l2 a2 r2)
    else Node (Node l1 a1 r1) a2 (merge l2 r2))"

(* Merging does not preserve braun: *)
value "merge \<langle>\<langle>\<rangle>, 0::int, \<langle>\<rangle>\<rangle> \<langle>\<langle>\<rangle>, 0, \<langle>\<rangle>\<rangle> = \<langle>\<langle>\<rangle>, 0, \<langle>\<langle>\<rangle>, 0, \<langle>\<rangle>\<rangle>\<rangle>"

lemma merge_size[termination_simp]:
  "size (merge l r) = size l + size r"
  by (induct rule: merge.induct; simp)

fun list_of_A :: "('a::linorder) tree \<Rightarrow> 'a list" where
"list_of_A Leaf = []" |
"list_of_A (Node l a r) = a # list_of_A (merge l r)"

value "list_of_A (heap_of_A shuffle100)"

lemma set_tree_merge[simp]:
  "set_tree (merge l r) = set_tree l \<union> set_tree r"
  by (induct l r rule: merge.induct; simp)

lemma mset_tree_merge[simp]:
  "mset_tree (merge l r) = mset_tree l + mset_tree r"
  by (induct l r rule: merge.induct; simp)

lemma merge_heap:
  "heap l \<Longrightarrow> heap r \<Longrightarrow> heap (merge l r)"
  by (induct l r rule: merge.induct; auto simp: ball_Un)

lemma set_list_of_A[simp]:
  "set (list_of_A t) = set_tree t"
  by (induct t rule: list_of_A.induct; simp)

lemma mset_list_of_A[simp]:
  "mset (list_of_A t) = mset_tree t"
  by (induct t rule: list_of_A.induct; simp)

lemma sorted_list_of_A:
  "heap t \<Longrightarrow> sorted (list_of_A t)"
  by (induct t rule: list_of_A.induct; simp add: merge_heap)

lemma sortedA: "sorted (list_of_A (heap_of_A xs))"
by (simp add: heap_heap_of_A sorted_list_of_A)

lemma msetA: "mset (list_of_A (heap_of_A xs)) = mset xs"
  by (simp add: mset_tree_heap_of_A)

text\<open>Does \<open>list_of_A\<close> take time $O(n lg n)$? Although \<open>merge\<close> does not preserve \<open>braun\<close>,
it cannot increase the height of the heap.\<close>

lemma merge_height:
  "height (merge l r) \<le>  Suc (max (height l) (height r))"
  by (induct rule: merge.induct, auto)

corollary merge_height_display:
  "height (merge l r) \<le> height (Node l x r)"
  using merge_height by simp

fun t_merge :: "('a::linorder) tree \<Rightarrow> 'a tree \<Rightarrow> nat" where
"t_merge Leaf t2 = 0" |
"t_merge t1 Leaf = 0" |
"t_merge (Node l1 a1 r1) (Node l2 a2 r2) =
   (if a1 \<le> a2 then 1 + t_merge l1 r1
    else 1 + t_merge l2 r2)"

fun t_list_of_A :: "('a::linorder) tree \<Rightarrow> nat" where
"t_list_of_A Leaf = 0" |
"t_list_of_A (Node l a r) = 1 + t_merge l r + t_list_of_A (merge l r)"

lemma t_merge_height:
  "t_merge l r \<le> max (height l) (height r)"
  by (induct rule: t_merge.induct, auto)

lemma t_list_of_A_induct:
  "height t \<le> n \<Longrightarrow> t_list_of_A t \<le> 2 * n * size t"
  apply (induct rule: t_list_of_A.induct)
   apply simp
  apply simp
  apply (drule meta_mp)
   apply (rule order_trans, rule merge_height)
   apply simp
  apply (simp add: merge_size)
  apply (cut_tac l=l and r=r in t_merge_height)
  apply linarith
  done

lemma t_list_of_A_bound:
  "t_list_of_A t \<le> 2 * height t * size t"
  by (rule t_list_of_A_induct, simp)

lemma t_list_of_A_log_bound:
  "braun t \<Longrightarrow> t_list_of_A t \<le> 2 * nlog2 (size t + 1) * size t"
  using t_list_of_A_bound[of t]
  by (simp add: height_balanced balanced_if_braun size1_size)

value "t_list_of_A (heap_of_A shuffle100)"

theorem t_sortA:
  "t_heap_of_A xs + t_list_of_A (heap_of_A xs) \<le> 3 * length xs * (nlog2 (length xs + 1) + 1)"
  (is "?lhs \<le> _")
proof -
  have "?lhs \<le> ?lhs" by simp
  also note t_heap_of_A_log_bound[of xs]
  also note t_list_of_A_log_bound[of "heap_of_A xs", OF braun_heap_of_A]
  finally show ?thesis
    by (simp add: size_heap_of_A)
qed

text \<open>Running time of algorithm B:\<close>

(* Unfortunately this can only be proven to terminate conditionally.
   To make it unconditional would require a total specification of
   sift_down, which would be complex and differ substantially from
   Paulson's presentation.  *)
function list_of_B :: "('a::linorder) tree \<Rightarrow> 'a list" where
"list_of_B Leaf = []" |
"list_of_B (Node l a r) = a # list_of_B (del_min (Node l a r))"
  by pat_completeness auto

lemma list_of_B_braun_ptermination:
  "braun t \<Longrightarrow> list_of_B_dom t"
  apply (induct t rule: measure_induct[where f=size])
  apply (rule accpI, erule list_of_B_rel.cases)
  apply (clarsimp simp: size_del_min braun_del_min)
  done

lemmas list_of_B_braun_simps
    = list_of_B.psimps[OF list_of_B_braun_ptermination]

lemma mset_list_of_B:
  "braun t \<Longrightarrow> mset (list_of_B t) = mset_tree t"
  apply (induct t rule: measure_induct[where f=size])
  apply (case_tac x; simp add: list_of_B_braun_simps)
  apply (simp add: size_del_min braun_del_min mset_del_min)
  done

lemma set_list_of_B:
  "braun t \<Longrightarrow> set (list_of_B t) = set_tree t"
  by (simp only: set_mset_mset[symmetric] mset_list_of_B, simp)

lemma sorted_list_of_B:
  "braun t \<Longrightarrow> heap t \<Longrightarrow> sorted (list_of_B t)"
  apply (induct t rule: measure_induct[where f=size])
  apply (case_tac x; simp add: list_of_B_braun_simps)
  apply (clarsimp simp: set_list_of_B braun_del_min size_del_min heap_del_min)
  apply (simp add: set_mset_tree[symmetric] mset_del_min del: set_mset_tree)
  done

definition
  "heap_of_B xs = fst (heapify (length xs) xs)"

lemma sortedB: "sorted (list_of_B (heap_of_B xs))"
by (simp add: heap_of_B_def braun_heapify heap_heapify sorted_list_of_B)

lemma msetB: "mset (list_of_B (heap_of_B xs)) = mset xs"
by (simp add: heap_of_B_def braun_heapify mset_heapify mset_list_of_B)

fun t_del_left :: "'a tree \<Rightarrow> nat" where
"t_del_left (Node Leaf x r) = 1" |
"t_del_left (Node l x r) = (let (y,l') = del_left l in 2 + t_del_left l)"

fun t_del_min :: "'a::linorder tree \<Rightarrow> nat" where
"t_del_min Leaf = 0" |
"t_del_min (Node Leaf x r) = 0" |
"t_del_min (Node l x r) = (let (y,l') = del_left l in t_del_left l + t_sift_down r y l')"

function t_list_of_B :: "('a::linorder) tree \<Rightarrow> nat" where
"t_list_of_B Leaf = 0" |
"t_list_of_B (Node l a r) = 1 + t_del_min (Node l a r) + t_list_of_B (del_min (Node l a r))"
  by pat_completeness auto

lemma t_del_left_bound:
  "t \<noteq> Leaf \<Longrightarrow> t_del_left t \<le> 2 * height t"
  apply (induct rule: t_del_left.induct; clarsimp)
  apply (atomize(full); clarsimp simp: prod_eq_iff)
  apply (simp add: nat_mult_max_right le_max_iff_disj)
  done

lemma del_left_height:
  "del_left t = (v, t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> height t' \<le> height t"
  apply (induct t arbitrary: v t' rule: del_left.induct; simp)
  apply (atomize(full), clarsimp split: prod.splits)
  apply simp
  done

lemma t_del_min_bound:
  "braun t \<Longrightarrow> t_del_min t \<le> 3 * height t"
  apply (cases t rule: t_del_min.cases; simp)
  apply (clarsimp split: prod.split)
  apply (frule del_left_braun, simp+)
  apply (frule del_left_size, simp+)
  apply (frule del_left_height, simp)
  apply (rule order_trans)
   apply ((rule add_le_mono t_del_left_bound t_sift_down_height | simp)+)[1]
   apply auto[1]
  apply (simp add: max_def)
  done

lemma t_list_of_B_braun_ptermination:
  "braun t \<Longrightarrow> t_list_of_B_dom t"
  apply (induct t rule: measure_induct[where f=size])
  apply (rule accpI, erule t_list_of_B_rel.cases)
  apply (clarsimp simp: size_del_min braun_del_min)
  done

lemmas t_list_of_B_braun_simps
    = t_list_of_B.psimps[OF t_list_of_B_braun_ptermination]

lemma del_min_height:
  "braun t \<Longrightarrow> height (del_min t) \<le> height t"
  apply (cases t rule: del_min.cases; simp)
  apply (clarsimp split: prod.split)
  apply (frule del_left_braun, simp+)
  apply (frule del_left_size, simp+)
  apply (drule del_left_height)
   apply simp
  apply (rule order_trans, rule sift_down_height, auto)
  done

lemma t_list_of_B_induct:
  "braun t \<Longrightarrow> height t \<le> n \<Longrightarrow> t_list_of_B t \<le> 3 * (n + 1) * size t"
  apply (induct t rule: measure_induct[where f=size])
  apply (drule_tac x="del_min x" in spec)
  apply (frule del_min_height)
  apply (case_tac x; simp add: t_list_of_B_braun_simps)
  apply (rename_tac l x' r)
  apply (clarsimp simp: braun_del_min size_del_min)
  apply (rule order_trans)
   apply ((rule add_le_mono t_del_min_bound | assumption | simp)+)[1]
  apply simp
  done

lemma t_list_of_B_bound:
  "braun t \<Longrightarrow> t_list_of_B t \<le> 3 * (height t + 1) * size t"
  by (erule t_list_of_B_induct, simp)

lemma t_list_of_B_log_bound:
  "braun t \<Longrightarrow> t_list_of_B t \<le> 3 * (nlog2 (size t + 1) + 1) * size t"
  apply (frule t_list_of_B_bound)
  apply (simp add: height_balanced balanced_if_braun size1_size)
  done

definition
  "t_heap_of_B xs = length xs + t_heapify (length xs) xs"

lemma t_heap_of_B_bound:
  "t_heap_of_B xs \<le> 6 * length xs + 1"
  by (simp add: t_heap_of_B_def order_trans[OF t_heapify_bound])

lemmas size_heapify = arg_cong[OF mset_heapify, where f=size, simplified]

theorem t_sortB:
  "t_heap_of_B xs + t_list_of_B (heap_of_B xs)
    \<le> 3 * length xs * (nlog2 (length xs + 1) + 3) + 1"
  (is "?lhs \<le> _")
proof -
  have "?lhs \<le> ?lhs" by simp
  also note t_heap_of_B_bound[of xs]
  also note t_list_of_B_log_bound[of "heap_of_B xs"]
  finally show ?thesis
    apply (simp add: size_heapify braun_heapify heap_of_B_def)
    apply (simp add: field_simps)
    done
qed

(* One suspects that algorithm A is actually faster, despite being
algorithmically slower on the construction of the heap. The operation
merge needs to allocate one constructor per level of the heap,
as opposed to del_min, which needs three, so the extraction is probably
much faster. Not sure how to validate that.

value "t_list_of_B (heap_of
  [50 :: nat, 7, 77, 15, 42, 82, 87, 68, 69, 29, 43, 24, 84, 12, 35, 30, 95, 45, 14, 47, 54, 66, 96, 71, 98, 4, 22, 0, 92, 86, 34, 33, 57, 91, 20, 13, 64, 73, 70, 8, 85, 40, 16, 18, 81, 99, 63, 41, 56, 72, 79, 48, 78, 52, 25, 49, 65, 90, 26, 76, 3, 59, 74, 58, 46, 38, 61, 94, 75, 11, 88, 31, 53, 17, 44, 89, 39, 93, 62, 5, 1, 21, 6, 55, 83, 28, 37, 60, 19, 67, 23, 97, 51, 10, 27, 32, 2, 36, 9, 80]
)"
 *)

end
