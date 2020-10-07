(*  Title:      Sort.thy
    Author:     Danijela Petrovi\'c, Facylty of Mathematics, University of Belgrade *)

section \<open>Verification of Functional Heap Sort\<close>

theory HeapFunctional
imports Heap
begin

text\<open>As we
said before, maximum element of the heap is its root. So, finding
maximum element is not difficulty. But, this element should also be
removed and remainder after deleting this element is two trees, left
and right branch of original heap. Those branches are also heaps by
the definition of the heap. To maintain consistency, branches should
be combined into one tree that satisfies heap condition:\<close>

function merge :: "'a::linorder Tree \<Rightarrow> 'a Tree \<Rightarrow> 'a Tree" where
  "merge t1 E = t1"
| "merge E t2 = t2"
| "merge (T v1 l1 r1) (T v2 l2 r2) = 
     (if v1 \<ge> v2 then T v1 (merge l1 (T v2 l2 r2)) r1
      else T v2 (merge l2 (T v1 l1 r1)) r2)"
by (pat_completeness) auto
termination
proof (relation "measure (\<lambda> (t1, t2). size t1 + size t2)")
  fix v1 l1 r1 v2 l2 r2
  assume "v2 \<le> v1"
  thus "((l1, T v2 l2 r2), T v1 l1 r1, T v2 l2 r2) \<in> 
        measure (\<lambda>(t1, t2). Heap.size t1 + Heap.size t2)"
    by auto
next
  fix v1 l1 r1 v2 l2 r2
  assume "\<not> v2 \<le> v1"
  thus "((l2, T v1 l1 r1), T v1 l1 r1, T v2 l2 r2) \<in> 
        measure (\<lambda>(t1, t2). Heap.size t1 + Heap.size t2)"
    by auto  
qed simp

lemma merge_val:
  "val(merge l r) = val l \<or> val(merge l r) = val r"
proof(induct l r rule:merge.induct)
  case (1 l)
  thus ?case 
    by auto
next
  case (2 r)
  thus ?case 
    by auto
next
  case (3 v1 l1 r1 v2 l2 r2)
  thus ?case
  proof(cases "v2 \<le> v1")
    case True
    hence "val (merge (T v1 l1 r1) (T v2 l2 r2)) = val (T v1 l1 r1)"
      by auto
    thus ?thesis
      by auto
  next
    case False
    hence "val (merge (T v1 l1 r1) (T v2 l2 r2)) = val (T v2 l2 r2)"
      by auto
    thus ?thesis
      by auto
  qed
qed

text\<open>Function {\em merge} merges two heaps into one:\<close>

lemma merge_heap_is_heap:
  assumes "is_heap l" "is_heap r"
  shows "is_heap (merge l r)"
using assms
proof(induct l r rule:merge.induct)
  case (1 l)
  thus ?case
    by auto
next
  case (2 r)
  thus ?case 
    by auto
next
  case (3 v1 l1 r1 v2 l2 r2)
  thus ?case
  proof(cases "v2 \<le> v1")
    case True
    have "is_heap l1"
      using \<open>is_heap (T v1 l1 r1)\<close>
      by (metis Tree.exhaust is_heap.simps(1) is_heap.simps(4) is_heap.simps(5))
    hence "is_heap (merge l1 (T v2 l2 r2))"
      using True \<open>is_heap (T v2 l2 r2)\<close>  3
      by auto 
    have "val (merge l1 (T v2 l2 r2)) = val l1 \<or> val(merge l1 (T v2 l2 r2)) = v2"
      using merge_val[of l1 "T v2 l2 r2"]
      by auto
    show ?thesis
    proof(cases "r1 = E")
      case True
      show ?thesis
      proof(cases "l1 = E")
        case True
        hence "merge (T v1 l1 r1) (T v2 l2 r2) = T v1 (T v2 l2 r2) E"
          using \<open>r1 = E\<close> \<open>v2 \<le> v1\<close>
          by auto
        thus ?thesis
          using 3
          using \<open>v2 \<le> v1\<close>
          by auto
      next
        case False
        hence "v1 \<ge> val l1"
          using 3(3)
          by (metis Tree.exhaust in_tree.simps(2) is_heap_max val.simps)
        thus ?thesis
          using \<open>r1 = E\<close> \<open>v1 \<ge> v2\<close> 
          using \<open>val (merge l1 (T v2 l2 r2)) = val l1 
                     \<or> val(merge l1 (T v2 l2 r2)) = v2\<close>
          using \<open>is_heap (merge l1 (T v2 l2 r2))\<close>
          by (metis False Tree.exhaust is_heap.simps(2) 
              is_heap.simps(4) merge.simps(3) val.simps)
      qed
    next
      case False
      hence "v1 \<ge> val r1"
        using 3(3)
        by (metis Tree.exhaust in_tree.simps(2) is_heap_max val.simps)
      show ?thesis
      proof(cases "l1 = E")
        case True
        hence "merge (T v1 l1 r1) (T v2 l2 r2) = T v1 (T v2 l2 r2) r1"
          using \<open>v2 \<le> v1\<close>
          by auto
        thus ?thesis
          using 3 \<open>v1 \<ge> val r1\<close>
          using \<open>v2 \<le> v1\<close>
          by (metis False Tree.exhaust Tree.inject Tree.simps(3) 
              True is_heap.simps(3) is_heap.simps(6) merge.simps(2) 
              merge.simps(3) order_eq_iff val.simps)
      next
        case False
        hence "v1 \<ge> val l1"
          using 3(3)
          by (metis Tree.exhaust in_tree.simps(2) is_heap_max val.simps)
        have "merge l1 (T v2 l2 r2) \<noteq> E"
          using False
          by (metis Tree.exhaust Tree.simps(2) merge.simps(3))    
        have "is_heap r1"
          using 3(3)
          by (metis False Tree.exhaust \<open>r1 \<noteq> E\<close> is_heap.simps(5))
        obtain ll1 lr1 lv1 where "r1 = T lv1 ll1 lr1"
          using \<open>r1 \<noteq> E\<close>
          by (metis Tree.exhaust)
        obtain rl1 rr1 rv1 where "merge l1 (T v2 l2 r2) = T rv1 rl1 rr1"
          using \<open>merge l1 (T v2 l2 r2) \<noteq> E\<close>
          by (metis Tree.exhaust)
        have "val (merge l1 (T v2 l2 r2)) \<le> v1"
          using \<open>val (merge l1 (T v2 l2 r2)) = val l1 \<or> 
                 val(merge l1 (T v2 l2 r2)) = v2\<close>
          using \<open>v1 \<ge> v2\<close> \<open>v1 \<ge> val l1\<close>
          by auto
        hence "is_heap (T v1 (merge l1 (T v2 l2 r2)) r1)"
          using is_heap.simps(5)[of v1 lv1 ll1 lr1 rv1 rl1  rr1]
          using \<open>r1 = T lv1 ll1 lr1\<close> \<open>merge l1 (T v2 l2 r2) = T rv1 rl1 rr1\<close>
          using \<open>is_heap r1\<close> \<open>is_heap (merge l1 (T v2 l2 r2))\<close> \<open>v1 \<ge> val r1\<close>
          by auto
        thus ?thesis
          using \<open>v2 \<le> v1\<close>
          by auto
      qed
    qed
  next
    case False
    have "is_heap l2"
      using 3(4)
      by (metis Tree.exhaust is_heap.simps(1) 
          is_heap.simps(4) is_heap.simps(5))
    hence "is_heap (merge l2 (T v1 l1 r1))"
      using False \<open>is_heap (T v1 l1 r1)\<close>  3
      by auto 
    have "val (merge l2 (T v1 l1 r1)) = val l2 \<or> 
          val(merge l2 (T v1 l1 r1)) = v1"
      using merge_val[of l2 "T v1 l1 r1"]
      by auto
    show ?thesis
    proof(cases "r2 = E")
      case True
      show ?thesis
      proof(cases "l2 = E")
        case True
        hence "merge (T v1 l1 r1) (T v2 l2 r2) = T v2 (T v1 l1 r1) E"
          using \<open>r2 = E\<close> \<open>\<not> v2 \<le> v1\<close>
          by auto
        thus ?thesis
          using 3
          using \<open>\<not> v2 \<le> v1\<close>
          by auto
      next
        case False
        hence "v2 \<ge> val l2"
          using 3(4)
          by (metis Tree.exhaust in_tree.simps(2) is_heap_max val.simps)
        thus ?thesis
          using \<open>r2 = E\<close> \<open>\<not> v1 \<ge> v2\<close> 
          using \<open>is_heap (merge l2 (T v1 l1 r1))\<close> 
          using \<open>val (merge l2 (T v1 l1 r1)) = val l2 \<or> 
                 val(merge l2 (T v1 l1 r1)) = v1\<close>
          by (metis False Tree.exhaust is_heap.simps(2) 
              is_heap.simps(4) linorder_linear merge.simps(3) val.simps)
      qed
    next
      case False
      hence "v2 \<ge> val r2"
        using 3(4)
        by (metis Tree.exhaust in_tree.simps(2) is_heap_max val.simps)
      show ?thesis
      proof(cases "l2 = E") 
        case True
        hence "merge (T v1 l1 r1) (T v2 l2 r2) = T v2 (T v1 l1 r1) r2" 
          using \<open>\<not> v2 \<le> v1\<close>
          by auto
        thus ?thesis
          using 3 \<open>v2 \<ge> val r2\<close>
          using \<open>\<not> v2 \<le> v1\<close>
          by (metis False Tree.exhaust Tree.simps(3) is_heap.simps(3) 
              is_heap.simps(5) linorder_linear val.simps)
      next
        case False
        hence "v2 \<ge> val l2"
          using 3(4)
          by (metis Tree.exhaust in_tree.simps(2) is_heap_max val.simps)
        have "merge l2 (T v1 l1 r1) \<noteq> E"
          using False
          by (metis Tree.exhaust Tree.simps(2) merge.simps(3))    
        have "is_heap r2"
          using 3(4)
          by (metis False Tree.exhaust \<open>r2 \<noteq> E\<close> is_heap.simps(5))
        obtain ll1 lr1 lv1 where "r2 = T lv1 ll1 lr1"
          using \<open>r2 \<noteq> E\<close>
          by (metis Tree.exhaust)
        obtain rl1 rr1 rv1 where "merge l2 (T v1 l1 r1) = T rv1 rl1 rr1"
          using \<open>merge l2 (T v1 l1 r1) \<noteq> E\<close>
          by (metis Tree.exhaust)
        have "val (merge l2 (T v1 l1 r1)) \<le> v2"
          using \<open>val (merge l2 (T v1 l1 r1)) = val l2 \<or> 
                 val(merge l2 (T v1 l1 r1)) = v1\<close>
          using \<open>\<not> v1 \<ge> v2\<close> \<open>v2 \<ge> val l2\<close>
          by auto
        hence "is_heap (T v2 (merge l2 (T v1 l1 r1)) r2)"
          using is_heap.simps(5)[of v1 lv1 ll1 lr1 rv1 rl1 rr1]
          using \<open>r2 = T lv1 ll1 lr1\<close> \<open>merge l2 (T v1 l1 r1) = T rv1 rl1 rr1\<close>
          using \<open>is_heap r2\<close> \<open>is_heap (merge l2 (T v1 l1 r1))\<close> \<open>v2 \<ge> val r2\<close>
          by auto
        thus ?thesis
          using \<open>\<not> v2 \<le> v1\<close>
          by auto
      qed
    qed    
  qed
qed

definition insert :: "'a::linorder \<Rightarrow> 'a Tree \<Rightarrow> 'a Tree" where
  "insert v t =  merge t (T v E E)"

primrec hs_of_list where
  "hs_of_list [] = E"
| "hs_of_list (v # l) = insert v (hs_of_list l)"

definition hs_is_empty where
[simp]: "hs_is_empty t \<longleftrightarrow>  t = E"

text\<open>Definition of function {\em remove\_max}:\<close>

fun hs_remove_max:: "'a::linorder Tree \<Rightarrow> 'a \<times> 'a Tree"  where
  "hs_remove_max (T v l r) = (v, merge l r)"

lemma merge_multiset:
  "multiset l + multiset g = multiset (merge l g)"
proof(induct l g rule:merge.induct)
  case (1 l)
  thus ?case
    by auto
next
  case (2 g)
  thus ?case
    by auto
next
  case (3 v1 l1 r1 v2 l2 r2)
  thus ?case
  proof(cases "v2 \<le> v1")
    case  True
    hence "multiset (merge (T v1 l1 r1) (T v2 l2 r2)) = 
           {#v1#} + multiset (merge l1 (T v2 l2 r2)) +  multiset r1"
      by auto
    hence "multiset (merge (T v1 l1 r1) (T v2 l2 r2)) = 
           {#v1#} + multiset l1 + multiset (T v2 l2 r2) + multiset r1"
      using 3 True
      by (metis union_assoc)
    hence "multiset (merge (T v1 l1 r1) (T v2 l2 r2)) = 
           {#v1#} + multiset l1 + multiset r1 + multiset (T v2 l2 r2)"
      by (metis union_commute union_lcomm)
    thus ?thesis
      by auto
  next
    case False
    hence "multiset (merge (T v1 l1 r1) (T v2 l2 r2)) = 
           {#v2#} + multiset (merge l2 (T v1 l1 r1)) + multiset r2"
      by auto
    hence "multiset (merge (T v1 l1 r1) (T v2 l2 r2)) = 
           {#v2#} + multiset l2 + multiset r2 +  multiset (T v1 l1 r1)"
      using 3 False
      by (metis union_commute union_lcomm)
    thus ?thesis
      by (metis multiset.simps(2) union_commute)    
  qed
qed

text\<open>Proof that defined functions are interpretation of abstract functions from locale {\em Collection}:\<close>

interpretation HS: Collection "E" hs_is_empty hs_of_list multiset
proof
   fix t
  assume "hs_is_empty t"
  thus "t = E"
    by auto
next
  show "hs_is_empty E"
    by auto
next
  show "multiset E = {#}"
    by auto
next
  fix l 
  show "multiset (hs_of_list l) = mset l"
  proof(induct l)
    case Nil
    thus ?case
      by auto
  next
    case (Cons a l)
    have "multiset (hs_of_list (a # l)) = multiset (hs_of_list l) + {#a#}"
      using merge_multiset[of "hs_of_list l" "T a E E"]
      apply auto
      unfolding insert_def
      by auto    
    thus ?case
      using Cons
      by auto
  qed
qed

text\<open>Proof that defined functions are interpretation of abstract functions from locale {\em Heap}:\<close>

interpretation Heap "E" hs_is_empty hs_of_list multiset id hs_remove_max
proof
  fix l
  show "multiset l = Heap.multiset (id l)"
    by auto
next
  fix l
  show "is_heap (id (hs_of_list l))"
  proof(induct l)
    case Nil
    thus ?case
      by auto
  next
    case (Cons a l)
    have "hs_of_list (a # l) = merge (hs_of_list l) (T a E E)"
      apply auto
      unfolding insert_def
      by auto
    have "is_heap (T a E E)"
      by auto    
    hence "is_heap (merge (hs_of_list l) (T a E E))"
      using Cons merge_heap_is_heap[of "hs_of_list l" "T a E E"]
      by auto
    thus ?case
      using \<open>hs_of_list (a # l) = merge (hs_of_list l) (T a E E)\<close>
      by auto     
  qed
next
  fix t
  show " (id t = E) = hs_is_empty t"
    by auto
next
  fix t m t'
  assume "\<not> hs_is_empty t" "(m, t') = hs_remove_max t"
  then obtain l r where "t = T m l r"
    by (metis Pair_inject Tree.exhaust hs_is_empty_def hs_remove_max.simps)
  thus "add_mset m (multiset t') = multiset t"
    using merge_multiset[of l r]
    using \<open>(m, t') = hs_remove_max t\<close>
    by auto
next
  fix t m t'
  assume "\<not> hs_is_empty t" "is_heap (id t)" "(m, t') = hs_remove_max t"
  then obtain v l r where "t = T v l r"
    by (metis Tree.exhaust hs_is_empty_def) 
  hence "t' = merge l r"
    using \<open>(m, t') = hs_remove_max t\<close>
    by auto
  have "is_heap l \<and> is_heap r"
    using \<open>is_heap (id t)\<close>
    using \<open>t = T v l r\<close>
    by (metis Tree.exhaust id_apply is_heap.simps(1) 
        is_heap.simps(3) is_heap.simps(4) is_heap.simps(5))
  thus "is_heap (id t')"
    using \<open>t' = merge l r\<close> 
    using merge_heap_is_heap
    by auto
next
  fix t m t'
  assume "\<not> hs_is_empty t" "(m, t') = hs_remove_max t"
  thus "m = val (id t)"
    by (metis Pair_inject Tree.exhaust hs_is_empty_def 
        hs_remove_max.simps id_apply val.simps)
qed 

end
