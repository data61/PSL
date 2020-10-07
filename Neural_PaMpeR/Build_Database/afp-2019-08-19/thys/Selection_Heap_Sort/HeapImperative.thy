(*  Title:      Sort.thy
    Author:     Danijela Petrovi\'c, Facylty of Mathematics, University of Belgrade *)

section \<open>Verification of Imperative Heap Sort\<close>

theory HeapImperative
imports Heap
begin 

primrec left :: "'a Tree \<Rightarrow> 'a Tree" where
  "left (T v l r) = l"

abbreviation left_val :: "'a Tree \<Rightarrow> 'a" where
  "left_val t \<equiv> val (left t)"

primrec right :: "'a Tree \<Rightarrow> 'a Tree" where
  "right (T v l r) = r"

abbreviation right_val :: "'a Tree \<Rightarrow> 'a" where
  "right_val t \<equiv> val (right t)"

abbreviation set_val :: "'a Tree \<Rightarrow> 'a \<Rightarrow> 'a Tree" where
  "set_val t x \<equiv> T x (left t) (right t)"

text\<open>The first step is to implement function {\em siftDown}. If some node
does not satisfy heap property, this function moves it down the heap
until it does. For a node is checked weather it satisfies heap property or not. If it
does nothing is changed. If it does not, value of the root node
becomes a value of the larger child and the value of that child
becomes the value of the root node. This is the reason this function
is called {\tt siftDown} -- value of the node is places down in the
heap. Now, the problem is that the child node may not satisfy the heap
property and that is the reason why function {\tt siftDown} is
recursively applied.\<close>

fun siftDown :: "'a::linorder Tree \<Rightarrow> 'a Tree" where
   "siftDown E = E"
|  "siftDown (T v E E) = T v E E"
|  "siftDown (T v l E) = 
        (if v \<ge> val l then T v l E else T (val l) (siftDown (set_val l v)) E)"
|  "siftDown (T v E r) = 
        (if v \<ge> val r then T v E r else T (val r) E (siftDown (set_val r v)))"
|  "siftDown (T v l r) = 
        (if val l \<ge> val r then 
            if v \<ge> val l then T v l r else T (val l) (siftDown (set_val l v)) r
        else
            if v \<ge> val r then T v l r else T (val r) l (siftDown (set_val r v)))"

lemma siftDown_Node:
  assumes "t = T v l r"
  shows "\<exists> l' v' r'. siftDown t = T v' l' r' \<and> v' \<ge> v"
using assms
apply(induct t rule:siftDown.induct)
by auto

lemma siftDown_in_tree:
  assumes "t \<noteq> E"
  shows "in_tree (val (siftDown t)) t"
using assms
apply(induct t rule:siftDown.induct)
by auto

lemma siftDown_in_tree_set: 
  shows "in_tree v t \<longleftrightarrow> in_tree v (siftDown t)"
proof
  assume "in_tree v t"
  thus "in_tree v (siftDown t)"
    apply (induct t rule:siftDown.induct)
    by auto
next
  assume " in_tree v (siftDown t)"
  thus "in_tree v t"
  proof (induct t rule:siftDown.induct)
    case 1
    thus ?case
      by auto
  next
    case (2 v1)
    thus ?case
      by auto
  next
    case (3 v2 v1 l1 r1)
    show ?case
    proof(cases "v2 \<ge> v1")
      case True
      thus ?thesis
        using 3
        by auto
    next
      case False
      show ?thesis
      proof(cases "v1 = v")
        case True
        thus ?thesis
          using 3 False
          by auto
      next
        case False
        hence "in_tree v (siftDown (set_val (T v1 l1 r1) v2))"
          using \<open>\<not> v2 \<ge> v1\<close> 3(2)
          by auto
        hence "in_tree v (T v2 l1 r1)"
          using 3(1) \<open>\<not> v2 \<ge> v1\<close>
          by auto
        thus ?thesis
        proof(cases "v2 = v")
          case True
          thus ?thesis
            by auto
        next
          case False
          hence "in_tree v (T v1 l1 r1)"
            using \<open>in_tree v (T v2 l1 r1)\<close>
            by auto
          thus ?thesis
            by auto
        qed
      qed
    qed
  next
    case (4 v2 v1 l1 r1)
    show ?case
    proof(cases "v2 \<ge> v1")
      case True
      thus ?thesis
        using 4
        by auto
    next
      case False
      show ?thesis
      proof(cases "v1 = v")
        case True
        thus ?thesis
          using 4 False
          by auto
      next
        case False
        hence "in_tree v (siftDown (set_val (T v1 l1 r1) v2))"
          using \<open>\<not> v2 \<ge> v1\<close> 4(2)
          by auto
        hence "in_tree v (T v2 l1 r1)"
          using 4(1) \<open>\<not> v2 \<ge> v1\<close>
          by auto
        thus ?thesis
        proof(cases "v2 = v")
          case True
          thus ?thesis
            by auto
        next
          case False
          hence "in_tree v (T v1 l1 r1)"
            using \<open>in_tree v (T v2 l1 r1)\<close>
            by auto
          thus ?thesis
            by auto
        qed
      qed
    qed
  next
    case ("5_1" v' v1 l1 r1 v2 l2 r2)
    show ?case
    proof(cases "v = v' \<or> v= v1 \<or> v = v2")
      case True
      thus ?thesis
        by auto
    next
      case False
      show ?thesis
      proof(cases "v1 \<ge> v2")
        case True
        show ?thesis
        proof(cases "v' \<ge> v1")
          case True
          thus ?thesis 
            using \<open>v1 \<ge> v2\<close> "5_1"
            by auto
        next
          case False
          thus ?thesis
          proof(cases "in_tree v (T v2 l2 r2)")
            case True
            thus ?thesis
              by auto
          next
            case False
            hence "in_tree v (siftDown (set_val (T v1 l1 r1) v'))"
              using "5_1"(3) \<open>\<not> in_tree v (T v2 l2 r2)\<close> \<open>v1 \<ge> v2\<close> \<open>\<not> v' \<ge> v1\<close>
              using \<open> \<not> (v = v' \<or> v = v1 \<or> v = v2)\<close>
              by auto
            hence "in_tree v (T v' l1 r1)"
              using "5_1"(1) \<open>v1 \<ge> v2\<close> \<open>\<not> v' \<ge> v1\<close>
              by auto
            hence "in_tree v (T v1 l1 r1)"
              using  \<open>\<not> (v = v' \<or> v = v1 \<or> v = v2)\<close>
              by auto
            thus ?thesis
              by auto
          qed
        qed
      next
        case False
        show ?thesis
        proof(cases "v' \<ge> v2")
          case True
          thus ?thesis 
            using \<open>\<not> v1 \<ge> v2\<close> "5_1"
            by auto
        next
          case False
          thus ?thesis
          proof(cases "in_tree v (T v1 l1 r1)")
            case True
            thus ?thesis
              by auto
          next
            case False
            hence "in_tree v (siftDown (set_val (T v2 l2 r2) v'))"
              using "5_1"(3) \<open>\<not> in_tree v (T v1 l1 r1)\<close> \<open>\<not> v1 \<ge> v2\<close> \<open>\<not> v' \<ge> v2\<close>
              using \<open> \<not> (v = v' \<or> v = v1 \<or> v = v2)\<close>
              by auto
            hence "in_tree v (T v' l2 r2)"
              using "5_1"(2) \<open>\<not> v1 \<ge> v2\<close> \<open>\<not> v' \<ge> v2\<close>
              by auto
            hence "in_tree v (T v2 l2 r2)"
              using  \<open>\<not> (v = v' \<or> v = v1 \<or> v = v2)\<close>
              by auto
            thus ?thesis
              by auto
          qed
        qed
      qed
    qed
  next
    case ("5_2" v' v1 l1 r1 v2 l2 r2)
    show ?case
    proof(cases "v = v' \<or> v= v1 \<or> v = v2")
      case True
      thus ?thesis
        by auto
    next
      case False
      show ?thesis
      proof(cases "v1 \<ge> v2")
        case True
        show ?thesis
        proof(cases "v' \<ge> v1")
          case True
          thus ?thesis 
            using \<open>v1 \<ge> v2\<close> "5_2"
            by auto
        next
          case False
          thus ?thesis
          proof(cases "in_tree v (T v2 l2 r2)")
            case True
            thus ?thesis
              by auto
          next
            case False
            hence "in_tree v (siftDown (set_val (T v1 l1 r1) v'))"
              using "5_2"(3) \<open>\<not> in_tree v (T v2 l2 r2)\<close> \<open>v1 \<ge> v2\<close> \<open>\<not> v' \<ge> v1\<close>
              using \<open> \<not> (v = v' \<or> v = v1 \<or> v = v2)\<close>
              by auto
            hence "in_tree v (T v' l1 r1)"
              using "5_2"(1) \<open>v1 \<ge> v2\<close> \<open>\<not> v' \<ge> v1\<close>
              by auto
            hence "in_tree v (T v1 l1 r1)"
              using  \<open>\<not> (v = v' \<or> v = v1 \<or> v = v2)\<close>
              by auto
            thus ?thesis
              by auto
          qed
        qed
      next
        case False
        show ?thesis
        proof(cases "v' \<ge> v2")
          case True
          thus ?thesis 
            using \<open>\<not> v1 \<ge> v2\<close> "5_2"
            by auto
        next
          case False
          thus ?thesis
          proof(cases "in_tree v (T v1 l1 r1)")
            case True
            thus ?thesis
              by auto
          next
            case False
            hence "in_tree v (siftDown (set_val (T v2 l2 r2) v'))"
              using "5_2"(3) \<open>\<not> in_tree v (T v1 l1 r1)\<close> \<open>\<not> v1 \<ge> v2\<close> \<open>\<not> v' \<ge> v2\<close>
              using \<open> \<not> (v = v' \<or> v = v1 \<or> v = v2)\<close>
              by auto
            hence "in_tree v (T v' l2 r2)"
              using "5_2"(2) \<open>\<not> v1 \<ge> v2\<close> \<open>\<not> v' \<ge> v2\<close>
              by auto
            hence "in_tree v (T v2 l2 r2)"
              using  \<open>\<not> (v = v' \<or> v = v1 \<or> v = v2)\<close>
              by auto
            thus ?thesis
              by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma siftDown_heap_is_heap:
  assumes "is_heap l" "is_heap r" "t = T v l r"
  shows "is_heap (siftDown t)"
using assms
proof (induct t arbitrary: v l r  rule:siftDown.induct)
  case 1
  thus ?case
    by simp
next
  case (2 v')
  show ?case
    by simp
next
  case (3 v2 v1 l1 r1)
  show ?case
  proof (cases "v2 \<ge> v1")
    case True
    thus ?thesis
      using 3(2) 3(4)
      by auto
  next
    case False
    show ?thesis
    proof-
      let ?t = "siftDown (T v2 l1 r1)"
      obtain l' v' r' where *: "?t = T v' l' r'" "v' \<ge> v2"
        using siftDown_Node[of "T v2 l1 r1" v2 l1 r1]
        by auto
      have "l = T v1 l1 r1"
        using 3(4)
        by auto
      hence "is_heap l1" "is_heap r1"
        using 3(2)
        apply (induct l rule:is_heap.induct)
        by auto        
      hence "is_heap ?t"
        using 3(1)[of l1 r1 v2] False 3
        by auto
      show ?thesis
      proof (cases "v' = v2")
        case True
        thus ?thesis
          using False \<open>is_heap ?t\<close> *
          by auto
      next
        case False
        have "in_tree v' ?t"
          using *
          using siftDown_in_tree[of ?t]
          by simp
        hence "in_tree v' (T v2 l1 r1)"
          using siftDown_in_tree_set[symmetric, of v' "T v2 l1 r1"]
          by auto
        hence "in_tree v' (T v1 l1 r1)"
          using False
          by simp
        hence "v1 \<ge> v'"
          using 3
          using is_heap_max[of v' "T v1 l1 r1"]
          by auto
        thus ?thesis
          using \<open>is_heap ?t\<close> * \<open>\<not> v2 \<ge> v1\<close>
          by auto
      qed
    qed
  qed
next
  case (4 v2 v1 l1 r1) 
  show ?case
  proof(cases "v2 \<ge> v1")
    case True
    thus ?thesis
      using 4(2-4)
      by auto
  next
    case False
    let ?t = "siftDown (T v2 l1 r1)" 
    obtain v' l' r' where *: "?t = T v' l' r'" "v' \<ge> v2"
      using siftDown_Node[of "T v2 l1 r1" v2 l1 r1]
      by auto
    have "r = T v1 l1 r1"
      using 4(4)
      by auto
    hence "is_heap l1" "is_heap r1"
      using 4(3)
      apply (induct r rule:is_heap.induct)
      by auto
    hence "is_heap ?t"
      using False  4(1)[of l1 r1 v2]
      by auto
    show ?thesis
    proof(cases "v' = v2")
      case True
      thus ?thesis
        using * \<open>is_heap ?t\<close> False
        by auto
    next
      case False
      have "in_tree v' ?t"
        using *
        using siftDown_in_tree[of ?t]
        by auto
      hence "in_tree v' (T v2 l1 r1)"
        using * siftDown_in_tree_set[of v' "T v2 l1 r1"]
        by auto
      hence "in_tree v' (T v1 l1 r1)"
        using False
        by auto
      hence "v1 \<ge> v'"
        using is_heap_max[of v' "T v1 l1 r1"] 4
        by auto
      thus ?thesis
        using \<open>is_heap ?t\<close> False *
        by auto
    qed
  qed
next
  case ("5_1" v1 v2 l2 r2 v3 l3 r3)
  show ?case
  proof(cases "v2 \<ge> v3")
    case True
    show ?thesis
    proof(cases "v1 \<ge> v2")
      case True
      thus ?thesis
        using \<open>v2 \<ge> v3\<close> "5_1"
        by auto
    next
      case False
      let ?t = "siftDown (T v1 l2 r2)"
      obtain l' v' r' where *: "?t = T v' l' r'" "v' \<ge> v1"
        using siftDown_Node
        by blast
      have "is_heap l2" "is_heap r2"
        using "5_1"(3, 5)
        apply(induct l rule:is_heap.induct)
        by auto
      hence "is_heap ?t"
        using "5_1"(1)[of l2 r2 v1] \<open>v2 \<ge> v3\<close> False 
        by auto
      have "v2 \<ge> v'"
      proof(cases "v' = v1")
        case True
        thus ?thesis
          using False
          by auto
      next
        case False
        have "in_tree v' ?t"
          using * siftDown_in_tree
          by auto
        hence "in_tree v' (T v1 l2 r2)"
          using siftDown_in_tree_set[of v' "T v1 l2 r2"]
          by auto
        hence "in_tree v' (T v2 l2 r2)"
          using False
          by auto
        thus ?thesis
          using is_heap_max[of v' "T v2 l2 r2"] "5_1"
          by auto
      qed
      thus ?thesis
        using \<open>is_heap ?t\<close> \<open>v2 \<ge> v3\<close> * False "5_1"
        by auto
    qed
  next
    case False
    show ?thesis
    proof(cases "v1 \<ge> v3")
      case True
      thus ?thesis
        using \<open>\<not> v2 \<ge> v3\<close> "5_1"
        by auto
    next
      case False
      let ?t = "siftDown (T v1 l3 r3)"
      obtain l' v' r' where *: "?t = T v' l' r'" "v' \<ge> v1"
        using siftDown_Node
        by blast
      have "is_heap l3" "is_heap r3"
        using "5_1"(4, 5)
        apply(induct r rule:is_heap.induct)
        by auto
      hence "is_heap ?t"
        using "5_1"(2)[of l3 r3 v1] \<open>\<not> v2 \<ge> v3\<close> False 
        by auto
      have "v3 \<ge> v'"
      proof(cases "v' = v1")
        case True
        thus ?thesis
          using False
          by auto
      next
        case False
        have "in_tree v' ?t"
          using * siftDown_in_tree
          by auto
        hence "in_tree v' (T v1 l3 r3)"
          using siftDown_in_tree_set[of v' "T v1 l3 r3"]
          by auto
        hence "in_tree v' (T v3 l3 r3)"
          using False
          by auto
        thus ?thesis
          using is_heap_max[of v' "T v3 l3 r3"] "5_1"
          by auto
      qed
      thus ?thesis
        using \<open>is_heap ?t\<close> \<open>\<not> v2 \<ge> v3\<close> * False "5_1"
        by auto
    qed
  qed          
next
  case ("5_2" v1 v2 l2 r2 v3 l3 r3)
  show ?case
  proof(cases "v2 \<ge> v3")
    case True
    show ?thesis
    proof(cases "v1 \<ge> v2")
      case True
      thus ?thesis
        using \<open>v2 \<ge> v3\<close> "5_2"
        by auto
    next
      case False
      let ?t = "siftDown (T v1 l2 r2)"
      obtain l' v' r' where *: "?t = T v' l' r'" "v1 \<le> v'"
        using siftDown_Node
        by blast
      have "is_heap l2" "is_heap r2"
        using "5_2"(3, 5)
        apply(induct l rule:is_heap.induct)
        by auto
      hence "is_heap ?t"
        using "5_2"(1)[of l2 r2 v1] \<open>v2 \<ge> v3\<close> False 
        by auto
      have "v2 \<ge> v'"
      proof(cases "v' = v1")
        case True
        thus ?thesis
          using False
          by auto
      next
        case False
        have "in_tree v' ?t"
          using * siftDown_in_tree
          by auto
        hence "in_tree v' (T v1 l2 r2)"
          using siftDown_in_tree_set[of v' "T v1 l2 r2"]
          by auto
        hence "in_tree v' (T v2 l2 r2)"
          using False
          by auto
        thus ?thesis
          using is_heap_max[of v' "T v2 l2 r2"] "5_2"
          by auto
      qed
      thus ?thesis
        using \<open>is_heap ?t\<close> \<open>v2 \<ge> v3\<close> * False "5_2"
        by auto
    qed
  next
    case False
    show ?thesis
    proof(cases "v1 \<ge> v3")
      case True
      thus ?thesis
        using \<open>\<not> v2 \<ge> v3\<close> "5_2"
        by auto
    next
      case False
      let ?t = "siftDown (T v1 l3 r3)"
      obtain l' v' r' where *: "?t = T v' l' r'" "v' \<ge> v1"
        using siftDown_Node
        by blast
      have "is_heap l3" "is_heap r3"
        using "5_2"(4, 5)
        apply(induct r rule:is_heap.induct)
        by auto
      hence "is_heap ?t"
        using "5_2"(2)[of l3 r3 v1] \<open>\<not> v2 \<ge> v3\<close> False 
        by auto
      have "v3 \<ge> v'"
      proof(cases "v' = v1")
        case True
        thus ?thesis
          using False
          by auto
      next
        case False
        have "in_tree v' ?t"
          using * siftDown_in_tree
          by auto
        hence "in_tree v' (T v1 l3 r3)"
          using siftDown_in_tree_set[of v' "T v1 l3 r3"]
          by auto
        hence "in_tree v' (T v3 l3 r3)"
          using False
          by auto
        thus ?thesis
          using is_heap_max[of v' "T v3 l3 r3"] "5_2"
          by auto
      qed
      thus ?thesis
        using \<open>is_heap ?t\<close> \<open>\<not> v2 \<ge> v3\<close> * False "5_2"
        by auto
    qed
  qed          
qed

text\<open>Definition of the function {\em heapify} which
makes a heap from any given binary tree.\<close>

primrec heapify where
   "heapify E = E"
|  "heapify (T v l r) = siftDown (T v (heapify l) (heapify r))"

lemma heapify_heap_is_heap:
  "is_heap (heapify t)"
proof(induct t)
  case E
  thus ?case
    by auto
next
  case (T v l r)
  thus ?case
    using siftDown_heap_is_heap[of "heapify l" "heapify r" "T v (heapify l) (heapify r)" v]
    by auto
qed

text\<open>Definition of {\em removeLeaf} function.  Function returns two values. The first one
is the value of romoved leaf element. The second returned value is tree without that leaf.\<close>

fun removeLeaf:: "'a::linorder Tree \<Rightarrow> 'a \<times> 'a Tree" where
  "removeLeaf (T v E E) = (v, E)"
| "removeLeaf (T v l E) = (fst (removeLeaf l), T v (snd (removeLeaf l)) E)"
| "removeLeaf (T v E r) = (fst (removeLeaf r), T v E (snd (removeLeaf r)))"
| "removeLeaf (T v l r) = (fst (removeLeaf l), T v (snd (removeLeaf l)) r)"

text\<open>Function {\em of\_list\_tree} makes a binary tree from any given
list.\<close>

primrec of_list_tree:: "'a::linorder list \<Rightarrow> 'a Tree" where
  "of_list_tree [] = E"
| "of_list_tree (v # tail) = T v (of_list_tree tail) E"

text\<open>By applying {\em heapify} binary tree is transformed into
heap.\<close>

definition hs_of_list where
  "hs_of_list l = heapify (of_list_tree l)"

text\<open>Definition of function {\em hs\_remove\_max}. As it is already well
established, finding maximum is not a problem, since it is in the root
element of the heap. The root element is replaced with leaf of the
heap and that leaf is erased from its previous position. However, now
the new root element may not satisfy heap property and that is the
reason to apply function {\em siftDown}.\<close>

definition hs_remove_max :: "'a::linorder Tree \<Rightarrow> 'a \<times> 'a Tree" where
  "hs_remove_max t \<equiv>
     (let v' = fst (removeLeaf t);
          t' = snd (removeLeaf t) in
     (if t' = E then (val t, E)
      else (val t, siftDown (set_val t' v'))))"

definition hs_is_empty where
[simp]: "hs_is_empty t \<longleftrightarrow>  t = E"

lemma siftDown_multiset:
  "multiset (siftDown t) = multiset t"
proof(induct t rule:siftDown.induct)
  case 1
  thus ?case
    by simp
next
  case (2 v)
  thus ?case
    by simp
next
  case (3 v1 v l r)
  thus ?case
  proof(cases "v \<le> v1")
    case True
    thus ?thesis
      by auto
  next
    case False
    hence "multiset (siftDown (T v1 (T v l r) E)) = 
           multiset l + {#v1#} + multiset r + {#v#}"
      using 3
      by auto
    moreover
    have "multiset (T v1 (T v l r) E) = 
          multiset l + {#v#} + multiset r + {#v1#}"
      by auto
    moreover
    have "multiset l + {#v1#} + multiset r + {#v#} = 
          multiset l + {#v#} + multiset r + {#v1#}"
      by (metis union_commute union_lcomm)
    ultimately
    show ?thesis
      by auto
  qed
next
  case (4 v1 v l r)
  thus ?case
  proof(cases "v \<le> v1")
    case True
    thus ?thesis
      by auto
  next
    case False
    have "multiset (set_val (T v l r) v1) = 
          multiset l + {#v1#} + multiset r"
      by auto
    hence "multiset (siftDown (T v1 E (T v l r))) = 
           {#v#} +  multiset (set_val (T v l r) v1)"
      using 4 False
      by auto
    hence "multiset (siftDown (T v1 E (T v l r))) = 
           {#v#} + multiset l + {#v1#} + multiset r"
      using \<open>multiset (set_val (T v l r) v1) = 
             multiset l + {#v1#} + multiset r\<close>
      by (metis union_commute union_lcomm)
    moreover
    have "multiset (T v1 E (T v l r)) =  
          {#v1#} + multiset l + {#v#} + multiset r"
      by (metis calculation monoid_add_class.add.left_neutral 
          multiset.simps(1) multiset.simps(2) union_commute union_lcomm)
    moreover
    have "{#v#} + multiset l + {#v1#} + multiset r = 
          {#v1#} + multiset l + {#v#} + multiset r"
      by (metis union_commute union_lcomm)
    ultimately
    show ?thesis
      by auto
  qed
next
  case ("5_1" v v1 l1 r1 v2 l2 r2)
  thus ?case
  proof(cases "v1 \<ge> v2")
    case True
    thus ?thesis
    proof(cases "v \<ge> v1")
      case True
      thus ?thesis
        using \<open>v1 \<ge> v2\<close>
        by auto
    next
      case False
      hence "multiset (siftDown (T v (T v1 l1 r1) (T v2 l2 r2))) = 
             multiset l1 + {#v#} + multiset r1 + {#v1#} + 
             multiset (T v2 l2 r2)"
        using \<open>v1 \<ge> v2\<close> "5_1"(1)
        by auto
      moreover
      have "multiset (T v (T v1 l1 r1) (T v2 l2 r2)) = 
              multiset l1 + {#v1#} + multiset r1 + {#v#} +
              multiset(T v2 l2 r2)"
        by auto
      moreover
      have "multiset l1 + {#v1#} + multiset r1 + {#v#} + 
            multiset(T v2 l2 r2) = 
                multiset l1 + {#v#} + multiset r1 + {#v1#} + 
                multiset (T v2 l2 r2)"
        by (metis union_commute union_lcomm)
      ultimately
      show ?thesis
        by auto
    qed
  next
    case False
    show ?thesis
    proof(cases "v \<ge> v2")
      case True
      thus ?thesis
        using False
        by auto
    next
      case False
      hence "multiset (siftDown (T v (T v1 l1 r1) (T v2 l2 r2))) = 
             multiset (T v1 l1 r1) + {#v2#} + 
             multiset l2 + {#v#} + multiset r2"
        using \<open>\<not> v1 \<ge> v2\<close> "5_1"(2)
        by (simp add: ac_simps)
      moreover
      have 
        "multiset (T v (T v1 l1 r1) (T v2 l2 r2)) = 
         multiset (T v1 l1 r1) + {#v#} + multiset l2 + 
         {#v2#} + multiset r2"
        by simp
      moreover
      have 
        "multiset (T v1 l1 r1) + {#v#} + multiset l2 + {#v2#} + 
         multiset r2 = 
            multiset (T v1 l1 r1) + {#v2#} + multiset l2 + 
            {#v#} + multiset r2"
        by (metis union_commute union_lcomm)
      ultimately
      show ?thesis
        by auto
    qed
  qed
next
  case ("5_2" v v1 l1 r1 v2 l2 r2)
  thus ?case
  proof(cases "v1 \<ge> v2")
    case True
    thus ?thesis
    proof(cases "v \<ge> v1")
      case True
      thus ?thesis
        using \<open>v1 \<ge> v2\<close>
        by auto
    next
      case False
      hence "multiset (siftDown (T v (T v1 l1 r1) (T v2 l2 r2))) = 
               multiset l1 + {#v#} + multiset r1 + {#v1#} + 
               multiset (T v2 l2 r2)"
        using \<open>v1 \<ge> v2\<close> "5_2"(1)
        by auto
      moreover
      have "multiset (T v (T v1 l1 r1) (T v2 l2 r2)) = 
              multiset l1 + {#v1#} + multiset r1 + 
              {#v#} + multiset(T v2 l2 r2)"
        by auto
      moreover
      have "multiset l1 + {#v1#} + multiset r1 + {#v#} + 
            multiset(T v2 l2 r2) = 
              multiset l1 + {#v#} + multiset r1 + {#v1#} + 
              multiset (T v2 l2 r2)"
        by (metis union_commute union_lcomm)
      ultimately
      show ?thesis
        by auto
    qed
  next
    case False
    show ?thesis
    proof(cases "v \<ge> v2")
      case True
      thus ?thesis
        using False
        by auto
    next
      case False
      hence "multiset (siftDown (T v (T v1 l1 r1) (T v2 l2 r2))) = 
               multiset (T v1 l1 r1) + {#v2#} + multiset l2 + {#v#} + 
               multiset r2"
        using \<open>\<not> v1 \<ge> v2\<close> "5_2"(2)
        by (simp add: ac_simps)
      moreover
      have "multiset (T v (T v1 l1 r1) (T v2 l2 r2)) = 
              multiset (T v1 l1 r1) + {#v#} + multiset l2 + {#v2#} + 
              multiset r2"
        by simp
      moreover
      have "multiset (T v1 l1 r1) + {#v#} + multiset l2 + {#v2#} + 
            multiset r2 = 
              multiset (T v1 l1 r1) + {#v2#} + multiset l2 + {#v#} + 
              multiset r2"
        by (metis union_commute union_lcomm)
      ultimately
      show ?thesis
        by auto
    qed
  qed
qed

lemma mset_list_tree:
 "multiset (of_list_tree l) = mset l"
proof(induct l)
  case Nil
  thus ?case
    by auto
next
  case (Cons v tail)
  hence "multiset (of_list_tree (v # tail)) = mset tail + {#v#}"
    by auto
  also have "... = mset (v # tail)"
    by auto
  finally show "multiset (of_list_tree (v # tail)) = mset (v # tail)"
    by auto
qed
  

lemma multiset_heapify:
  "multiset (heapify t) = multiset t"
proof(induct t)
  case E
  thus ?case
    by auto
next
  case (T v l r)
  hence "multiset (heapify (T v l r)) = multiset l + {#v#} + multiset r"
    using siftDown_multiset[of "T v (heapify l) (heapify r)"]
    by auto
  thus ?case
    by auto
qed
    

lemma multiset_heapify_of_list_tree:
  "multiset (heapify (of_list_tree l)) = mset l"
using multiset_heapify[of "of_list_tree l"]
using mset_list_tree[of l]
by auto

lemma removeLeaf_val_val:
  assumes "snd (removeLeaf t) \<noteq> E" "t \<noteq> E"
  shows "val t = val (snd (removeLeaf t))"
using assms
apply (induct t rule:removeLeaf.induct)
by auto

lemma removeLeaf_heap_is_heap: 
  assumes "is_heap t" "t \<noteq> E"
  shows "is_heap (snd (removeLeaf t))"
using assms
proof(induct t rule:removeLeaf.induct)
  case (1 v)
  thus ?case
    by auto
next
  case (2 v v1 l1 r1)
  have "is_heap (T v1 l1 r1)"
    using 2(3)
    by auto
  hence "is_heap (snd (removeLeaf (T v1 l1 r1)))"
    using 2(1)
    by auto
  let ?t = "(snd (removeLeaf (T v1 l1 r1)))"
  show ?case
  proof(cases "?t = E")
    case True
    thus ?thesis
      by auto
  next
    case False
    have "v \<ge> v1"
      using 2(3)
      by auto
    hence "v \<ge> val ?t"
      using False removeLeaf_val_val[of "T v1 l1 r1"]
      by auto
    hence "is_heap (T v (snd (removeLeaf (T v1 l1 r1))) E)"
      using \<open>is_heap (snd (removeLeaf (T v1 l1 r1)))\<close>
      by (metis Tree.exhaust is_heap.simps(2) is_heap.simps(4))
    thus ?thesis
      using 2
      by auto
  qed
next
  case (3 v v1 l1 r1)
  have "is_heap (T v1 l1 r1)"
    using 3(3)
    by auto
  hence "is_heap (snd (removeLeaf (T v1 l1 r1)))"
    using 3(1)
    by auto
  let ?t = "(snd (removeLeaf (T v1 l1 r1)))"
  show ?case
  proof(cases "?t = E")
    case True
    thus ?thesis
      by auto
  next
    case False
    have "v \<ge> v1"
      using 3(3)
      by auto
    hence "v \<ge> val ?t"
      using False removeLeaf_val_val[of "T v1 l1 r1"]
      by auto
    hence "is_heap (T v E (snd (removeLeaf (T v1 l1 r1))))"
      using \<open>is_heap (snd (removeLeaf (T v1 l1 r1)))\<close>
      by (metis False Tree.exhaust is_heap.simps(3))
    thus ?thesis
      using 3
      by auto
  qed
next
  case ("4_1" v v1 l1 r1 v2 l2 r2)
  have "is_heap (T v1 l1 r1)" "is_heap (T v2 l2 r2)" "v \<ge> v1" "v \<ge> v2"
    using "4_1"(3)
    by (simp add:is_heap.simps(5))+
  hence "is_heap (snd (removeLeaf (T v1 l1 r1)))"
    using "4_1"(1)
    by auto
  let ?t = "(snd (removeLeaf (T v1 l1 r1)))"
  show ?case
  proof(cases "?t = E")
    case True
    thus ?thesis
      using \<open>is_heap (T v2 l2 r2)\<close> \<open>v \<ge> v2\<close>
      by auto
  next
    case False
    then obtain v1' l1' r1' where "?t = T v1' l1' r1'"
      by (metis Tree.exhaust)
    hence "is_heap (T v1' l1' r1')"
      using \<open>is_heap (snd (removeLeaf (T v1 l1 r1)))\<close>
      by auto
    have "v \<ge> v1"
      using "4_1"(3)
      by auto
    hence "v \<ge> val ?t"
      using False removeLeaf_val_val[of "T v1 l1 r1"]
      by auto
    hence "v \<ge> v1'"
      using \<open>?t = T v1' l1' r1'\<close>
      by auto
    hence "is_heap (T v (T v1' l1' r1') (T v2 l2 r2))"
      using \<open>is_heap (T v1' l1' r1')\<close>
      using \<open>is_heap (T v2 l2 r2)\<close> \<open>v \<ge> v2\<close>
      by (simp add: is_heap.simps(5))
    thus ?thesis
      using "4_1" \<open>?t = T v1' l1' r1'\<close>
      by auto
  qed
next
  case ("4_2" v v1 l1 r1 v2 l2 r2)
  have "is_heap (T v1 l1 r1)" "is_heap (T v2 l2 r2)" "v \<ge> v1" "v \<ge> v2"
    using "4_2"(3)
    by (simp add:is_heap.simps(5))+
  hence "is_heap (snd (removeLeaf (T v1 l1 r1)))"
    using "4_2"(1)
    by auto
  let ?t = "(snd (removeLeaf (T v1 l1 r1)))"
  show ?case
  proof(cases "?t = E")
    case True
    thus ?thesis
      using \<open>is_heap (T v2 l2 r2)\<close> \<open>v \<ge> v2\<close>
      by auto
  next
    case False
    then obtain v1' l1' r1' where "?t = T v1' l1' r1'"
      by (metis Tree.exhaust)
    hence "is_heap (T v1' l1' r1')"
      using \<open>is_heap (snd (removeLeaf (T v1 l1 r1)))\<close>
      by auto
    have "v \<ge> v1"
      using "4_2"(3)
      by auto
    hence "v \<ge> val ?t"
      using False removeLeaf_val_val[of "T v1 l1 r1"]
      by auto
    hence "v \<ge> v1'"
      using \<open>?t = T v1' l1' r1'\<close>
      by auto
    hence "is_heap (T v (T v1' l1' r1') (T v2 l2 r2))"
      using \<open>is_heap (T v1' l1' r1')\<close>
      using \<open>is_heap (T v2 l2 r2)\<close> \<open>v \<ge> v2\<close>
      by (simp add: is_heap.simps(5))
    thus ?thesis
      using "4_2" \<open>?t = T v1' l1' r1'\<close>
      by auto
  qed
next
  case 5
  thus ?case
    by auto
qed

text\<open>Difined functions satisfy conditions of locale {\em Collection} and thus represent 
       interpretation of this locale.\<close>

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
    unfolding hs_of_list_def
    using multiset_heapify_of_list_tree[of l]
    by auto
qed

lemma removeLeaf_multiset:
  assumes "(v', t') = removeLeaf t" "t \<noteq> E"
  shows "{#v'#} + multiset t' = multiset t"
using assms
proof(induct t arbitrary: v' t' rule:removeLeaf.induct)
  case 1
  thus ?case
    by auto
next
  case (2 v v1 l1 r1)
  have "t' = T v (snd (removeLeaf (T v1 l1 r1))) E"
    using 2(3)
    by auto
  have "v' = fst (removeLeaf (T v1 l1 r1))"
    using 2(3)
    by auto
  hence "{#v'#} + multiset t' = 
           {#fst (removeLeaf (T v1 l1 r1))#} + 
           multiset (snd (removeLeaf (T v1 l1 r1))) + 
           {#v#}"
    using \<open>t' = T v (snd (removeLeaf (T v1 l1 r1))) E\<close>
    by (simp add: ac_simps)
  have "{#fst (removeLeaf (T v1 l1 r1))#} + 
        multiset (snd (removeLeaf (T v1 l1 r1))) = 
          multiset (T v1 l1 r1)"
    using 2(1)
    by auto
  hence "{#v'#} + multiset t' = multiset (T v1 l1 r1) + {#v#}"
    using \<open>{#v'#} + multiset t' = 
           {#fst (removeLeaf (T v1 l1 r1))#} + 
           multiset (snd (removeLeaf (T v1 l1 r1))) + {#v#}\<close>
    by auto
  thus ?case
    by auto
next
  case (3 v v1 l1 r1)
  have "t' = T v E (snd (removeLeaf (T v1 l1 r1)))"
    using 3(3)
    by auto
  have "v' = fst (removeLeaf (T v1 l1 r1))"
    using 3(3)
    by auto
  hence "{#v'#} + multiset t' = 
          {#fst (removeLeaf (T v1 l1 r1))#} + 
          multiset (snd (removeLeaf (T v1 l1 r1))) + 
          {#v#}"
    using \<open>t' = T v E (snd (removeLeaf (T v1 l1 r1)))\<close>
    by (simp add: ac_simps)
  have "{#fst (removeLeaf (T v1 l1 r1))#} + 
        multiset (snd (removeLeaf (T v1 l1 r1))) = 
          multiset (T v1 l1 r1)"
    using 3(1)
    by auto
  hence "{#v'#} + multiset t' = multiset (T v1 l1 r1) + {#v#}"
    using \<open>{#v'#} + multiset t' = 
           {#fst (removeLeaf (T v1 l1 r1))#} + 
           multiset (snd (removeLeaf (T v1 l1 r1))) + {#v#}\<close>
    by auto
  thus ?case
    by (metis monoid_add_class.add.right_neutral 
        multiset.simps(1) multiset.simps(2) union_commute)
next
  case ("4_1" v v1 l1 r1 v2 l2 r2)
  have "t' = T v (snd (removeLeaf (T v1 l1 r1))) (T v2 l2 r2)"
    using "4_1"(3)
    by auto
  have "v' = fst (removeLeaf (T v1 l1 r1))"
    using "4_1"(3)
    by auto
  hence "{#v'#} + multiset t' = 
         {#fst (removeLeaf (T v1 l1 r1))#} + 
         multiset (snd (removeLeaf (T v1 l1 r1))) + 
         {#v#} + multiset (T v2 l2 r2)"
    using \<open>t' = T v (snd (removeLeaf (T v1 l1 r1))) (T v2 l2 r2)\<close>
    by (metis multiset.simps(2) union_assoc)
  have "{#fst (removeLeaf (T v1 l1 r1))#} + 
        multiset (snd (removeLeaf (T v1 l1 r1))) = 
          multiset (T v1 l1 r1)"
    using "4_1"(1)
    by auto
  hence "{#v'#} + multiset t' = 
           multiset (T v1 l1 r1) + {#v#} + multiset (T v2 l2 r2)"
    using \<open>{#v'#} + multiset t' = 
           {#fst (removeLeaf (T v1 l1 r1))#} + 
           multiset (snd (removeLeaf (T v1 l1 r1))) + 
           {#v#} + multiset (T v2 l2 r2)\<close>
    by auto
  thus ?case
    by auto
next
  case ("4_2" v v1 l1 r1 v2 l2 r2)
  have "t' = T v (snd (removeLeaf (T v1 l1 r1))) (T v2 l2 r2)"
    using "4_2"(3)
    by auto
  have "v' = fst (removeLeaf (T v1 l1 r1))"
    using "4_2"(3)
    by auto
  hence "{#v'#} + multiset t' = 
         {#fst (removeLeaf (T v1 l1 r1))#} + 
         multiset (snd (removeLeaf (T v1 l1 r1))) + 
         {#v#} + multiset (T v2 l2 r2)"
    using \<open>t' = T v (snd (removeLeaf (T v1 l1 r1))) (T v2 l2 r2)\<close>
    by (metis multiset.simps(2) union_assoc)
  have "{#fst (removeLeaf (T v1 l1 r1))#} + 
        multiset (snd (removeLeaf (T v1 l1 r1))) = 
          multiset (T v1 l1 r1)"
    using "4_2"(1)
    by auto
  hence "{#v'#} + multiset t' = 
         multiset (T v1 l1 r1) + {#v#} + multiset (T v2 l2 r2)"
    using \<open>{#v'#} + multiset t' = 
           {#fst (removeLeaf (T v1 l1 r1))#} + 
           multiset (snd (removeLeaf (T v1 l1 r1))) + 
           {#v#} + multiset (T v2 l2 r2)\<close>
    by auto
  thus ?case
    by auto
next
  case 5
  thus ?case
    by auto
qed

lemma set_val_multiset:
  assumes "t \<noteq> E"
  shows "multiset (set_val t v') +  {#val t#} = {#v'#} + multiset t"
proof-
  obtain v l r where "t = T v l r"
    using assms
    by (metis Tree.exhaust)
  hence "multiset (set_val t v') + {#val t#} = 
         multiset l + {#v'#} + multiset r + {#v#}"
    by auto
  have "{#v'#} + multiset t = 
        {#v'#} + multiset l + {#v#} + multiset r"
    using \<open>t = T v l r\<close>
    by (metis multiset.simps(2) union_assoc)
  have "{#v'#} + multiset l + {#v#} + multiset r = 
        multiset l + {#v'#} + multiset r + {#v#}"
    by (metis union_commute union_lcomm)
  thus ?thesis
    using \<open>multiset (set_val t v') + {#val t#} = 
           multiset l + {#v'#} + multiset r + {#v#}\<close>
    using \<open>{#v'#} + multiset t = 
           {#v'#} + multiset l + {#v#} + multiset r\<close>
    by auto
qed

lemma hs_remove_max_multiset:
  assumes "(m, t') = hs_remove_max t" "t \<noteq> E"
  shows "{#m#} + multiset t' = multiset t"
proof-
  let ?v1 = "fst (removeLeaf t)"
  let ?t1 = "snd (removeLeaf t)"
  show ?thesis
  proof(cases "?t1 = E")
    case True
    hence "{#m#} + multiset t' = {#m#}"
      using assms
      unfolding hs_remove_max_def
      by auto
    have "?v1 = val t"
      using True assms(2)
      apply (induct t rule:removeLeaf.induct)
      by auto
    hence "?v1 = m"
      using assms(1) True
      unfolding hs_remove_max_def
      by auto
    hence "multiset t = {#m#}"
      using removeLeaf_multiset[of ?v1 ?t1 t] True assms(2)
      by (metis empty_neutral(2) multiset.simps(1) prod.collapse)
    thus ?thesis
      using \<open>{#m#} + multiset t' = {#m#}\<close>
      by auto
  next
    case False
    hence "t' = siftDown (set_val ?t1 ?v1)"
      using assms(1)
      by (auto simp add: hs_remove_max_def) (metis prod.inject)
    hence "multiset t' + {#val ?t1#} = multiset t"
      using siftDown_multiset[of "set_val ?t1 ?v1"]
      using removeLeaf_multiset[of ?v1 ?t1 t] assms(2)
      using set_val_multiset[of ?t1 ?v1] False
      by auto
    have "val ?t1 = val t"
      using False assms(2)
      apply (induct t rule:removeLeaf.induct)
      by auto
    have "val t = m"
      using assms(1) False
      using \<open>t' = siftDown (set_val ?t1 ?v1)\<close>
      unfolding hs_remove_max_def
      by (metis (full_types) fst_conv removeLeaf.simps(1))    
    hence "val ?t1 = m"
      using \<open>val ?t1 = val t\<close>
      by auto
    hence "multiset t' + {#m#} = multiset t"
      using \<open>multiset t' + {#val ?t1#} = multiset t\<close>
      by metis
    thus ?thesis
      by (metis union_commute)
  qed
qed

text\<open>Difined functions satisfy conditions of locale {\em Heap} and thus represent 
       interpretation of this locale.\<close>

interpretation Heap "E" hs_is_empty hs_of_list multiset id hs_remove_max
proof
  fix t
  show "multiset t = multiset (id t)"
    by auto
next
  fix t
  show " is_heap (id (hs_of_list t))"
    unfolding hs_of_list_def
    using heapify_heap_is_heap[of "of_list_tree t"]
    by auto
next
  fix t
  show "(id t = E) = hs_is_empty t"
    by auto
next
  fix t m t'
  assume "\<not> hs_is_empty t" "(m, t') = hs_remove_max t"
  thus "add_mset m (multiset t') = multiset t"
    using hs_remove_max_multiset[of m t' t]
    by auto
next
  fix t v' t' 
  assume "\<not> hs_is_empty t" "is_heap (id t)" "(v', t') = hs_remove_max t"
  let ?v1 = "fst (removeLeaf t)"
  let ?t1 = "snd (removeLeaf t)"
  have "is_heap ?t1"
    using \<open>\<not> hs_is_empty t\<close> \<open>is_heap (id t)\<close>
    using removeLeaf_heap_is_heap[of t]
    by auto
  show "is_heap (id t')"
  proof(cases "?t1 = E")
    case True
    hence "t' = E"
      using \<open>(v', t') = hs_remove_max t\<close>
      unfolding hs_remove_max_def
      by auto
    thus ?thesis
      by auto
  next
    case False
    then obtain v_t1 l_t1 r_t1 where "?t1 = T v_t1 l_t1 r_t1"
      by (metis Tree.exhaust)
    hence "is_heap l_t1" "is_heap r_t1"
      using \<open>is_heap ?t1\<close>
      by (auto, metis (full_types) Tree.exhaust 
         is_heap.simps(1) is_heap.simps(4) is_heap.simps(5))
         (metis (full_types) Tree.exhaust 
          is_heap.simps(1) is_heap.simps(3) is_heap.simps(5))
    have "set_val ?t1 ?v1 = T ?v1 l_t1 r_t1"
      using \<open>?t1 = T v_t1 l_t1 r_t1\<close>
      by auto
    hence "is_heap (siftDown (set_val ?t1 ?v1))"
      using \<open>is_heap l_t1\<close> \<open>is_heap r_t1\<close>
      using siftDown_heap_is_heap[of l_t1 r_t1 "set_val ?t1 ?v1" ?v1]
      by auto
    have "t' = siftDown (set_val ?t1 ?v1)"
      using \<open>(v', t') = hs_remove_max t\<close> False
      by (auto simp add: hs_remove_max_def) (metis prod.inject)
    thus ?thesis
      using \<open>is_heap (siftDown (set_val ?t1 ?v1))\<close>
      by auto
  qed
next
  fix t m t'
  let ?t1 = "snd (removeLeaf t)"
  assume "\<not> hs_is_empty t" "(m, t') = hs_remove_max t"
  hence "m = val t"
    apply (simp add: hs_remove_max_def)
    apply (cases "?t1 = E")
    by (auto, metis prod.inject)    
  thus "m = val (id t)"
    by auto
qed




end 
