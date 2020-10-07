(*  Title:       Binary Search Trees, Isar-Style
    Author:      Viktor Kuncak, MIT CSAIL, November 2003
    Maintainer:  Larry Paulson <Larry.Paulson at cl.cam.ac.uk>
    License:     LGPL
*)

section \<open>Isar-style Reasoning for Binary Tree Operations\<close>
theory BinaryTree imports Main begin

text \<open>We prove correctness of operations on 
 binary search tree implementing a set.

 This document is LGPL.

 Author: Viktor Kuncak, MIT CSAIL, November 2003\<close>

(*============================================================*)
section \<open>Tree Definition\<close>
(*============================================================*)

datatype 'a Tree = Tip | T "'a Tree" 'a "'a Tree"

primrec
  setOf :: "'a Tree => 'a set" 
  \<comment> \<open>set abstraction of a tree\<close> 
where
  "setOf Tip = {}"
| "setOf (T t1 x t2) = (setOf t1) Un (setOf t2) Un {x}"

type_synonym
  \<comment> \<open>we require index to have an irreflexive total order <\<close>
  \<comment> \<open>apart from that, we do not rely on index being int\<close>
  index = int 

type_synonym \<comment> \<open>hash function type\<close>
  'a hash = "'a => index"

definition eqs :: "'a hash => 'a => 'a set" where
  \<comment> \<open>equivalence class of elements with the same hash code\<close>
  "eqs h x == {y. h y = h x}"

primrec
  sortedTree :: "'a hash => 'a Tree => bool"
  \<comment> \<open>check if a tree is sorted\<close>
where
  "sortedTree h Tip = True"
| "sortedTree h (T t1 x t2) = 
    (sortedTree h t1 & 
     (\<forall>l \<in> setOf t1. h l < h x) &
     (\<forall>r \<in> setOf t2. h x < h r) &
     sortedTree h t2)"

lemma sortLemmaL: 
  "sortedTree h (T t1 x t2) ==> sortedTree h t1" by simp
lemma sortLemmaR: 
  "sortedTree h (T t1 x t2) ==> sortedTree h t2" by simp

(*============================================================*)
section \<open>Tree Lookup\<close>
(*============================================================*)

primrec
  tlookup :: "'a hash => index => 'a Tree => 'a option"
where
  "tlookup h k Tip = None"
| "tlookup h k (T t1 x t2) = 
   (if k < h x then tlookup h k t1
    else if h x < k then tlookup h k t2
    else Some x)"

lemma tlookup_none: 
     "sortedTree h t & (tlookup h k t = None) --> (\<forall>x\<in>setOf t. h x ~= k)"
by (induct t, auto) 

lemma tlookup_some:
     "sortedTree h t & (tlookup h k t = Some x) --> x:setOf t & h x = k"
apply (induct t)
  \<comment> \<open>Just auto will do it, but very slowly\<close>
apply (simp)
apply (clarify, auto)
apply (simp_all split: if_split_asm) 
done

definition sorted_distinct_pred :: "'a hash => 'a => 'a => 'a Tree => bool" where
  \<comment> \<open>No two elements have the same hash code\<close>
  "sorted_distinct_pred h a b t == sortedTree h t & 
      a:setOf t & b:setOf t & h a = h b --> 
      a = b"

declare sorted_distinct_pred_def [simp]

\<comment> \<open>for case analysis on three cases\<close>
lemma cases3: "[| C1 ==> G; C2 ==> G; C3 ==> G;
                  C1 | C2 | C3 |] ==> G"
by auto

text \<open>@{term sorted_distinct_pred} holds for out trees:\<close>

lemma sorted_distinct: "sorted_distinct_pred h a b t" (is "?P t")
proof (induct t)
  show "?P Tip" by simp
  fix t1 :: "'a Tree" assume h1: "?P t1"
  fix t2 :: "'a Tree" assume h2: "?P t2"
  fix x :: 'a
  show "?P (T t1 x t2)"
  proof (unfold sorted_distinct_pred_def, safe)
    assume s: "sortedTree h (T t1 x t2)"
    assume adef: "a : setOf (T t1 x t2)"
    assume bdef: "b : setOf (T t1 x t2)"
    assume hahb: "h a = h b"
    from s have s1: "sortedTree h t1" by auto
    from s have s2: "sortedTree h t2" by auto
    show "a = b"
    \<comment> \<open>We consider 9 cases for the position of a and b are in the tree\<close>
    proof -
    \<comment> \<open>three cases for a\<close>
    from adef have "a : setOf t1 | a = x | a : setOf t2" by auto
    moreover { assume adef1: "a : setOf t1"
      have ?thesis
      proof - 
      \<comment> \<open>three cases for b\<close>
      from bdef have "b : setOf t1 | b = x | b : setOf t2" by auto
      moreover { assume bdef1: "b : setOf t1"
        from s1 adef1 bdef1 hahb h1 have ?thesis by simp }
      moreover { assume bdef1: "b = x"
        from adef1 bdef1 s have "h a < h b" by auto
        from this hahb have ?thesis by simp }
      moreover { assume bdef1: "b : setOf t2"
        from adef1 s have o1: "h a < h x" by auto
        from bdef1 s have o2: "h x < h b" by auto
        from o1 o2 have "h a < h b" by simp
        from this hahb have ?thesis by simp } \<comment> \<open>case impossible\<close>
      ultimately show ?thesis by blast
      qed 
    } 
    moreover { assume adef1: "a = x"
      have ?thesis 
      proof -
      \<comment> \<open>three cases for b\<close>
      from bdef have "b : setOf t1 | b = x | b : setOf t2" by auto
      moreover { assume bdef1: "b : setOf t1"
        from this s have "h b < h x" by auto
        from this adef1 have "h b < h a" by auto
        from hahb this have ?thesis by simp } \<comment> \<open>case impossible\<close>
      moreover { assume bdef1: "b = x"
        from adef1 bdef1 have ?thesis by simp }
      moreover { assume bdef1: "b : setOf t2"
        from this s have "h x < h b" by auto
        from this adef1 have "h a < h b" by simp
        from hahb this have ?thesis by simp } \<comment> \<open>case impossible\<close>
      ultimately show ?thesis by blast
      qed
    }
    moreover { assume adef1: "a : setOf t2"
      have ?thesis
      proof -
      \<comment> \<open>three cases for b\<close>
      from bdef have "b : setOf t1 | b = x | b : setOf t2" by auto
      moreover { assume bdef1: "b : setOf t1"
        from bdef1 s have o1: "h b < h x" by auto
        from adef1 s have o2: "h x < h a" by auto
        from o1 o2 have "h b < h a" by simp
        from this hahb have ?thesis by simp } \<comment> \<open>case impossible\<close>
      moreover { assume bdef1: "b = x"
        from adef1 bdef1 s have "h b < h a" by auto
        from this hahb have ?thesis by simp } \<comment> \<open>case impossible\<close>
      moreover { assume bdef1: "b : setOf t2"
        from s2 adef1 bdef1 hahb h2 have ?thesis by simp }
      ultimately show ?thesis by blast
      qed
    }
    ultimately show ?thesis by blast
    qed
  qed
qed

lemma tlookup_finds: \<comment> \<open>if a node is in the tree, lookup finds it\<close>
"sortedTree h t & y:setOf t --> 
 tlookup h (h y) t = Some y"
proof safe
  assume s: "sortedTree h t"
  assume yint: "y : setOf t"
  show "tlookup h (h y) t = Some y"
  proof (cases "tlookup h (h y) t")
  case None note res = this    
    from s res have "sortedTree h t & (tlookup h (h y) t = None)" by simp
    from this have o1: "\<forall>x\<in>setOf t. h x ~= h y" by (simp add: tlookup_none)
    from o1 yint have "h y ~= h y" by fastforce (* auto does not work *)
    from this show ?thesis by simp
  next case (Some z) note res = this
    have ls: "sortedTree h t & (tlookup h (h y) t = Some z) -->
              z:setOf t & h z = h y" by (simp add: tlookup_some)
    have sd: "sorted_distinct_pred h y z t" 
    by (insert sorted_distinct [of h y z t], simp) 
       (* for some reason simplifier would never guess this substitution *)
    from s res ls have o1: "z:setOf t & h z = h y" by simp
    from s yint o1 sd have "y = z" by auto
    from this res show "tlookup h (h y) t = Some y" by simp
  qed
qed

subsection \<open>Tree membership as a special case of lookup\<close>

definition memb :: "'a hash => 'a => 'a Tree => bool" where
  "memb h x t == 
   (case (tlookup h (h x) t) of
      None => False
    | Some z => (x=z))"

lemma assumes s: "sortedTree h t" 
      shows memb_spec: "memb h x t = (x : setOf t)"
proof (cases "tlookup h (h x) t")
case None note tNone = this
  from tNone have res: "memb h x t = False" by (simp add: memb_def)
  from s tNone tlookup_none have o1: "\<forall>y\<in>setOf t. h y ~= h x" by fastforce
  have notIn: "x ~: setOf t"
  proof
    assume h: "x : setOf t"
    from h o1 have "h x ~= h x" by fastforce
    from this show False by simp
  qed
  from res notIn show ?thesis by simp
next case (Some z) note tSome = this
  from s tSome tlookup_some have zin: "z : setOf t" by fastforce
  show ?thesis
  proof (cases "x=z")
  case True note xez = this
    from tSome xez have res: "memb h x t" by (simp add: memb_def)  
    from res zin xez show ?thesis by simp
  next case False note xnez = this
    from tSome xnez have res: "~ memb h x t" by (simp add: memb_def)
    have "x ~: setOf t"
    proof
      assume xin: "x : setOf t"
      from s tSome tlookup_some have hzhx: "h x = h z" by fastforce
      have o1: "sorted_distinct_pred h x z t"
      by (insert sorted_distinct [of h x z t], simp)
      from s xin zin hzhx o1 have "x = z" by fastforce
      from this xnez show False by simp
    qed  
    from this res show ?thesis by simp
  qed
qed

declare sorted_distinct_pred_def [simp del]

(*============================================================*)
section \<open>Insertion into a Tree\<close>
(*============================================================*)

primrec
  binsert :: "'a hash => 'a => 'a Tree => 'a Tree"
where
  "binsert h e Tip = (T Tip e Tip)"
| "binsert h e (T t1 x t2) = (if h e < h x then
                             (T (binsert h e t1) x t2)
                            else
                             (if h x < h e then
                               (T t1 x (binsert h e t2))
                              else (T t1 e t2)))"

text \<open>A technique for proving disjointness of sets.\<close>
lemma disjCond: "[| !! x. [| x:A; x:B |] ==> False |] ==> A Int B = {}"
by fastforce

text \<open>The following is a proof that insertion correctly implements
        the set interface.
        Compared to \<open>BinaryTree_TacticStyle\<close>, the claim is more
        difficult, and this time we need to assume as a hypothesis
        that the tree is sorted.\<close>

lemma binsert_set: "sortedTree h t -->
                    setOf (binsert h e t) = (setOf t) - (eqs h e) Un {e}" 
      (is "?P t")
proof (induct t)
  \<comment> \<open>base case\<close>
  show "?P Tip" by (simp add: eqs_def)
  \<comment> \<open>inductition step\<close>
  fix t1 :: "'a Tree" assume h1: "?P t1"
  fix t2 :: "'a Tree" assume h2: "?P t2"
  fix x :: 'a
  show "?P (T t1 x t2)"
  proof 
    assume s: "sortedTree h (T t1 x t2)"
    from s have s1: "sortedTree h t1" by (rule sortLemmaL)
    from s1 and h1 have c1: "setOf (binsert h e t1) = setOf t1 - eqs h e Un {e}" by simp
    from s have s2: "sortedTree h t2" by (rule sortLemmaR)
    from s2 and h2 have c2: "setOf (binsert h e t2) = setOf t2 - eqs h e Un {e}" by simp
    show "setOf (binsert h e (T t1 x t2)) = 
          setOf (T t1 x t2) - eqs h e Un {e}"
    proof (cases "h e < h x")
      case True note eLess = this
        from eLess have res: "binsert h e (T t1 x t2) = (T (binsert h e t1) x t2)" by simp
        show "setOf (binsert h e (T t1 x t2)) = 
              setOf (T t1 x t2) - eqs h e Un {e}"
        proof (simp add: res eLess c1)
          show "insert x (insert e (setOf t1 - eqs h e Un setOf t2)) = 
                insert e (insert x (setOf t1 Un setOf t2) - eqs h e)"
          proof -
            have eqsLessX: "\<forall>el \<in> eqs h e. h el < h x" by (simp add: eqs_def eLess)
            from this have eqsDisjX: "\<forall>el \<in> eqs h e. h el ~= h x" by fastforce
            from s have xLessT2: "\<forall>r \<in> setOf t2. h x < h r" by auto
            have eqsLessT2: "\<forall>el \<in> eqs h e. \<forall>r \<in> setOf t2. h el < h r"
            proof safe
              fix el assume hel: "el : eqs h e"
              from hel eqs_def have o1: "h el = h e" by fastforce (* auto fails here! *)
              fix r assume hr: "r : setOf t2"
              from xLessT2 hr o1 eLess show "h el < h r" by auto
            qed
            from eqsLessT2 have eqsDisjT2: "\<forall>el \<in> eqs h e. \<forall>r \<in> setOf t2. h el ~= h r"
            by fastforce (* auto fails here *)
            from eqsDisjX eqsDisjT2 show ?thesis by fastforce
          qed
        qed
      next case False note eNotLess = this
      show "setOf (binsert h e (T t1 x t2)) = setOf (T t1 x t2) - eqs h e Un {e}"
      proof (cases "h x < h e")
        case True note xLess = this
        from xLess have res: "binsert h e (T t1 x t2) = (T t1 x (binsert h e t2))" by simp
        show "setOf (binsert h e (T t1 x t2)) = 
              setOf (T t1 x t2) - eqs h e Un {e}"
        proof (simp add: res xLess eNotLess c2)
          show "insert x (insert e (setOf t1 Un (setOf t2 - eqs h e))) = 
                insert e (insert x (setOf t1 Un setOf t2) - eqs h e)"
          proof -
            have XLessEqs: "\<forall>el \<in> eqs h e. h x < h el" by (simp add: eqs_def xLess)
            from this have eqsDisjX: "\<forall>el \<in> eqs h e. h el ~= h x" by auto
            from s have t1LessX: "\<forall>l \<in> setOf t1. h l < h x" by auto
            have T1lessEqs: "\<forall>el \<in> eqs h e. \<forall>l \<in> setOf t1. h l < h el"
            proof safe
              fix el assume hel: "el : eqs h e"
              fix l assume hl: "l : setOf t1"
              from hel eqs_def have o1: "h el = h e" by fastforce (* auto fails here! *)
              from t1LessX hl o1 xLess show "h l < h el" by auto
            qed
            from T1lessEqs have T1disjEqs: "\<forall>el \<in> eqs h e. \<forall>l \<in> setOf t1. h el ~= h l"
            by fastforce
            from eqsDisjX T1lessEqs show ?thesis by auto
          qed
        qed      
      next case False note xNotLess = this
        from xNotLess eNotLess have xeqe: "h x = h e" by simp
        from xeqe have res: "binsert h e (T t1 x t2) = (T t1 e t2)" by simp
        show "setOf (binsert h e (T t1 x t2)) = 
              setOf (T t1 x t2) - eqs h e Un {e}"
        proof (simp add: res eNotLess xeqe)
          show "insert e (setOf t1 Un setOf t2) = 
                insert e (insert x (setOf t1 Un setOf t2) - eqs h e)"
          proof -
            have "insert x (setOf t1 Un setOf t2) - eqs h e = 
                  setOf t1 Un setOf t2" 
            proof -
              have (* o1: *) "x : eqs h e" by (simp add: eqs_def xeqe)
              moreover have (* o2: *) "(setOf t1) Int (eqs h e) = {}"
              proof (rule disjCond)
                fix w
                assume whSet: "w : setOf t1"
                assume whEq: "w : eqs h e"
                from whSet s have o1: "h w < h x" by simp
                from whEq eqs_def have o2: "h w = h e" by fastforce
                from o2 xeqe have o3: "~ h w < h x" by simp
                from o1 o3 show False by contradiction
              qed
              moreover have (* o3: *) "(setOf t2) Int (eqs h e) = {}"
              proof (rule disjCond)
                fix w
                assume whSet: "w : setOf t2"
                assume whEq: "w : eqs h e"
                from whSet s have o1: "h x < h w" by simp
                from whEq eqs_def have o2: "h w = h e" by fastforce
                from o2 xeqe have o3: "~ h x < h w" by simp
                from o1 o3 show False by contradiction
              qed
              ultimately show ?thesis by auto
            qed
            from this show ?thesis by simp
          qed
        qed
      qed
    qed
  qed
qed

text \<open>Using the correctness of set implementation,
        preserving sortedness is still simple.\<close>
lemma binsert_sorted: "sortedTree h t --> sortedTree h (binsert h x t)"
by (induct t) (auto simp add: binsert_set)

text \<open>We summarize the specification of binsert as follows.\<close>
corollary binsert_spec: "sortedTree h t -->
                     sortedTree h (binsert h x t) &
                     setOf (binsert h e t) = (setOf t) - (eqs h e) Un {e}"
by (simp add: binsert_set binsert_sorted)

(*============================================================*)
section \<open>Removing an element from a tree\<close>
(*============================================================*)

text \<open>These proofs are influenced by those in \<open>BinaryTree_Tactic\<close>\<close>

primrec
  rm :: "'a hash => 'a Tree => 'a"
  \<comment> \<open>rightmost element of a tree\<close>
where
"rm h (T t1 x t2) =
  (if t2=Tip then x else rm h t2)"

primrec
  wrm :: "'a hash => 'a Tree => 'a Tree"
  \<comment> \<open>tree without the rightmost element\<close>
where
"wrm h (T t1 x t2) =
  (if t2=Tip then t1 else (T t1 x (wrm h t2)))"

primrec
  wrmrm :: "'a hash => 'a Tree => 'a Tree * 'a"
  \<comment> \<open>computing rightmost and removal in one pass\<close>
where
"wrmrm h (T t1 x t2) =
  (if t2=Tip then (t1,x)
   else (T t1 x (fst (wrmrm h t2)),
         snd (wrmrm h t2)))"

primrec
  remove :: "'a hash => 'a => 'a Tree => 'a Tree"
   \<comment> \<open>removal of an element from the tree\<close>
where
  "remove h e Tip = Tip"
| "remove h e (T t1 x t2) = 
    (if h e < h x then (T (remove h e t1) x t2)
     else if h x < h e then (T t1 x (remove h e t2))
     else (if t1=Tip then t2
           else let (t1p,r) = wrmrm h t1
                in (T t1p r t2)))"

theorem wrmrm_decomp: "t ~= Tip --> wrmrm h t = (wrm h t, rm h t)"
apply (induct_tac t)
apply simp_all
done

lemma rm_set: "t ~= Tip & sortedTree h t --> rm h t : setOf t"
apply (induct_tac t)
apply simp_all
done

lemma wrm_set: "t ~= Tip & sortedTree h t --> 
                setOf (wrm h t) = setOf t - {rm h t}" (is "?P t")
proof (induct t)
  show "?P Tip" by simp
  fix t1 :: "'a Tree" assume h1: "?P t1"
  fix t2 :: "'a Tree" assume h2: "?P t2" 
  fix x :: 'a
  show "?P (T t1 x t2)"
  proof (rule impI, erule conjE)
    assume s: "sortedTree h (T t1 x t2)"
    show "setOf (wrm h (T t1 x t2)) = 
          setOf (T t1 x t2) - {rm h (T t1 x t2)}"
    proof (cases "t2 = Tip")
    case True note t2tip = this
      from t2tip have rm_res: "rm h (T t1 x t2) = x" by simp
      from t2tip have wrm_res: "wrm h (T t1 x t2) = t1" by simp
      from s have "x ~: setOf t1" by auto
      from this rm_res wrm_res t2tip show ?thesis by simp
    next case False note t2nTip = this
      from t2nTip have rm_res: "rm h (T t1 x t2) = rm h t2" by simp
      from t2nTip have wrm_res: "wrm h (T t1 x t2) = T t1 x (wrm h t2)" by simp
      from s have s2: "sortedTree h t2" by simp    
      from h2 t2nTip s2 
      have o1: "setOf (wrm h t2) = setOf t2 - {rm h t2}" by simp
      show ?thesis
      proof (simp add: rm_res wrm_res t2nTip h2 o1)
        show "insert x (setOf t1 Un (setOf t2 - {rm h t2})) = 
              insert x (setOf t1 Un setOf t2) - {rm h t2}"
        proof -
          from s rm_set t2nTip have xOk: "h x < h (rm h t2)" by auto 
          have t1Ok: "\<forall>l \<in> setOf t1. h l < h (rm h t2)"
          proof safe
            fix l :: 'a  assume ldef: "l : setOf t1"
            from ldef s have lx: "h l < h x" by auto
            from lx xOk show "h l < h (rm h t2)" by auto
          qed
          from xOk t1Ok show ?thesis by auto
        qed
      qed
    qed
  qed
qed

lemma wrm_set1: "t ~= Tip & sortedTree h t --> setOf (wrm h t) <= setOf t"
by (auto simp add: wrm_set)

lemma wrm_sort: "t ~= Tip & sortedTree h t --> sortedTree h (wrm h t)" (is "?P t")
proof (induct t)
  show "?P Tip" by simp  
  fix t1 :: "'a Tree" assume h1: "?P t1"
  fix t2 :: "'a Tree" assume h2: "?P t2" 
  fix x :: 'a
  show "?P (T t1 x t2)"
  proof safe
    assume s: "sortedTree h (T t1 x t2)"
    show "sortedTree h (wrm h (T t1 x t2))"
    proof (cases "t2 = Tip")
    case True note t2tip = this
      from t2tip have res: "wrm h (T t1 x t2) = t1" by simp
      from res s show ?thesis by simp
    next case False note t2nTip = this
      from t2nTip have res: "wrm h (T t1 x t2) = T t1 x (wrm h t2)" by simp
      from s have s1: "sortedTree h t1" by simp
      from s have s2: "sortedTree h t2" by simp
      from s2 h2 t2nTip have o1: "sortedTree h (wrm h t2)" by simp
      from s2 t2nTip wrm_set1 have o2: "setOf (wrm h t2) <= setOf t2" by auto
      from s o2 have o3: "\<forall>r \<in> setOf (wrm h t2). h x < h r" by auto
      from s1 o1 o3 res s show "sortedTree h (wrm h (T t1 x t2))" by simp
    qed
  qed
qed

lemma wrm_less_rm: 
  "t ~= Tip & sortedTree h t --> 
   (\<forall>l \<in> setOf (wrm h t). h l < h (rm h t))" (is "?P t")
proof (induct t)
  show "?P Tip" by simp
  fix t1 :: "'a Tree" assume h1: "?P t1"
  fix t2 :: "'a Tree" assume h2: "?P t2"
  fix x :: 'a   
  show "?P (T t1 x t2)"
  proof safe 
    fix l :: "'a" assume ldef: "l : setOf (wrm h (T t1 x t2))"
    assume s: "sortedTree h (T t1 x t2)"
    from s have s1: "sortedTree h t1" by simp
    from s have s2: "sortedTree h t2" by simp
    show "h l < h (rm h (T t1 x t2))"
    proof (cases "t2 = Tip")
    case True note t2tip = this
      from t2tip have rm_res: "rm h (T t1 x t2) = x" by simp
      from t2tip have wrm_res: "wrm h (T t1 x t2) = t1" by simp
      from ldef wrm_res have o1: "l : setOf t1" by simp
      from rm_res o1 s show ?thesis by simp
    next case False note t2nTip = this
      from t2nTip have rm_res: "rm h (T t1 x t2) = rm h t2" by simp
      from t2nTip have wrm_res: "wrm h (T t1 x t2) = T t1 x (wrm h t2)" by simp
      from ldef wrm_res 
      have l_scope: "l : {x} Un setOf t1 Un setOf (wrm h t2)" by simp
      have hLess: "h l < h (rm h t2)"
      proof (cases "l = x")
      case True note lx = this
        from s t2nTip rm_set s2 have o1: "h x < h (rm h t2)" by auto
        from lx o1 show ?thesis by simp
      next case False note lnx = this
        show ?thesis
        proof (cases "l : setOf t1")
        case True note l_in_t1 = this
          from s t2nTip rm_set s2 have o1: "h x < h (rm h t2)" by auto
          from l_in_t1 s have o2: "h l < h x" by auto
          from o1 o2 show ?thesis by simp
        next case False note l_notin_t1 = this
          from l_scope lnx l_notin_t1 
          have l_in_res: "l : setOf (wrm h t2)" by auto
          from l_in_res h2 t2nTip s2 show ?thesis by auto
        qed
      qed
      from rm_res hLess show ?thesis by simp
    qed
  qed
qed

lemma remove_set: "sortedTree h t --> 
  setOf (remove h e t) = setOf t - eqs h e" (is "?P t")
proof (induct t)
  show "?P Tip" by auto
  fix t1 :: "'a Tree" assume h1: "?P t1"
  fix t2 :: "'a Tree" assume h2: "?P t2"
  fix x :: 'a
  show "?P (T t1 x t2)"
  proof 
    assume s: "sortedTree h (T t1 x t2)"
    show "setOf (remove h e (T t1 x t2)) = setOf (T t1 x t2) - eqs h e"
    proof (cases "h e < h x")
    case True note elx = this
      from elx have res: "remove h e (T t1 x t2) = T (remove h e t1) x t2" 
      by simp
      from s have s1: "sortedTree h t1" by simp
      from s1 h1 have o1: "setOf (remove h e t1) = setOf t1 - eqs h e" by simp
      show ?thesis
      proof (simp add: o1 elx)
        show "insert x (setOf t1 - eqs h e Un setOf t2) = 
              insert x (setOf t1 Un setOf t2) - eqs h e"
        proof -
          have xOk: "x ~: eqs h e" 
          proof 
            assume h: "x : eqs h e"
            from h have o1: "~ (h e < h x)" by (simp add: eqs_def)
            from elx o1 show "False" by contradiction
          qed
          have t2Ok: "(setOf t2) Int (eqs h e) = {}"
          proof (rule disjCond)
            fix y :: 'a 
            assume y_in_t2: "y : setOf t2"
            assume y_in_eq: "y : eqs h e"
            from y_in_t2 s have xly: "h x < h y" by auto
            from y_in_eq have eey: "h y = h e" by (simp add: eqs_def) (* must "add:" not "from" *)
            from xly eey have nelx: "~ (h e < h x)" by simp
            from nelx elx show False by contradiction
          qed
          from xOk t2Ok show ?thesis by auto
        qed
      qed
    next case False note nelx = this
      show ?thesis 
      proof (cases "h x < h e")
      case True note xle = this
        from xle have res: "remove h e (T t1 x t2) = T t1 x (remove h e t2)" by simp
        from s have s2: "sortedTree h t2" by simp
        from s2 h2 have o1: "setOf (remove h e t2) = setOf t2 - eqs h e" by simp
        show ?thesis
        proof (simp add: o1 xle nelx)
          show "insert x (setOf t1 Un (setOf t2 - eqs h e)) = 
                insert x (setOf t1 Un setOf t2) - eqs h e"
          proof -
            have xOk: "x ~: eqs h e" 
            proof 
              assume h: "x : eqs h e"
              from h have o1: "~ (h x < h e)" by (simp add: eqs_def)
              from xle o1 show "False" by contradiction
            qed
            have t1Ok: "(setOf t1) Int (eqs h e) = {}"
            proof (rule disjCond)
              fix y :: 'a 
              assume y_in_t1: "y : setOf t1"
              assume y_in_eq: "y : eqs h e"
              from y_in_t1 s have ylx: "h y < h x" by auto
              from y_in_eq have eey: "h y = h e" by (simp add: eqs_def)
              from ylx eey have nxle: "~ (h x < h e)" by simp
              from nxle xle show False by contradiction
            qed
            from xOk t1Ok show ?thesis by auto
          qed
        qed
      next case False note nxle = this
        from nelx nxle have ex: "h e = h x" by simp
        have t2Ok: "(setOf t2) Int (eqs h e) = {}"
        proof (rule disjCond)
          fix y :: 'a 
          assume y_in_t2: "y : setOf t2"
          assume y_in_eq: "y : eqs h e"
          from y_in_t2 s have xly: "h x < h y" by auto
          from y_in_eq have eey: "h y = h e" by (simp add: eqs_def)
          from y_in_eq ex eey have nxly: "~ (h x < h y)" by simp
          from nxly xly show False by contradiction
        qed
        show ?thesis 
        proof (cases "t1 = Tip")
        case True note t1tip = this
          from ex t1tip have res: "remove h e (T t1 x t2) = t2" by simp
          show ?thesis
          proof (simp add: res t1tip ex)
            show "setOf t2 = insert x (setOf t2) - eqs h e"              
            proof -
              from ex have x_in_eqs: "x : eqs h e" by (simp add: eqs_def)
              from x_in_eqs t2Ok show ?thesis by auto
           qed
          qed
        next case False note t1nTip = this
          from nelx nxle ex t1nTip
          have res: "remove h e (T t1 x t2) =
                     T (wrm h t1) (rm h t1) t2" 
          by (simp add: Let_def wrmrm_decomp)
          from res show ?thesis
          proof simp
            from s have s1: "sortedTree h t1" by simp
            show "insert (rm h t1) (setOf (wrm h t1) Un setOf t2) = 
                  insert x (setOf t1 Un setOf t2) - eqs h e"
            proof (simp add: t1nTip s1 rm_set wrm_set)
              show "insert (rm h t1) (setOf t1 - {rm h t1} Un setOf t2) = 
                    insert x (setOf t1 Un setOf t2) - eqs h e"
              proof -
                from t1nTip s1 rm_set
                have o1: "insert (rm h t1) (setOf t1 - {rm h t1} Un setOf t2) =
                          setOf t1 Un setOf t2" by auto
                have o2: "insert x (setOf t1 Un setOf t2) - eqs h e =
                          setOf t1 Un setOf t2" 
                proof -
                  from ex have xOk: "x : eqs h e" by (simp add: eqs_def)                  
                  have t1Ok: "(setOf t1) Int (eqs h e) = {}"
                  proof (rule disjCond)
                    fix y :: 'a 
                    assume y_in_t1: "y : setOf t1"
                    assume y_in_eq: "y : eqs h e"
                    from y_in_t1 s ex have o1: "h y < h e" by auto
                    from y_in_eq have o2: "~ (h y < h e)" by (simp add: eqs_def)
                    from o1 o2 show False by contradiction
                  qed
                  from xOk t1Ok t2Ok show ?thesis by auto
                qed
                from o1 o2 show ?thesis by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed  
qed

lemma remove_sort: "sortedTree h t --> 
                    sortedTree h (remove h e t)" (is "?P t")
proof (induct t)
  show "?P Tip" by auto
  fix t1 :: "'a Tree" assume h1: "?P t1"
  fix t2 :: "'a Tree" assume h2: "?P t2"
  fix x :: 'a
  show "?P (T t1 x t2)"
  proof 
    assume s: "sortedTree h (T t1 x t2)"
    from s have s1: "sortedTree h t1" by simp
    from s have s2: "sortedTree h t2" by simp
    from h1 s1 have sr1: "sortedTree h (remove h e t1)" by simp
    from h2 s2 have sr2: "sortedTree h (remove h e t2)" by simp   
    show "sortedTree h (remove h e (T t1 x t2))"
    proof (cases "h e < h x")
    case True note elx = this
      from elx have res: "remove h e (T t1 x t2) = T (remove h e t1) x t2" 
      by simp
      show ?thesis
      proof (simp add: s sr1 s2 elx res)
        let ?C1 = "\<forall>l \<in> setOf (remove h e t1). h l < h x"
        let ?C2 = "\<forall>r \<in> setOf t2. h x < h r"
        have o1: "?C1"
        proof -
          from s1 have "setOf (remove h e t1) = setOf t1 - eqs h e" by (simp add: remove_set)
          from s this show ?thesis by auto
        qed
        from o1 s show "?C1 & ?C2" by auto
      qed
    next case False note nelx = this
      show ?thesis 
      proof (cases "h x < h e")
      case True note xle = this
        from xle have res: "remove h e (T t1 x t2) = T t1 x (remove h e t2)" by simp
        show ?thesis
        proof (simp add: s s1 sr2 xle nelx res)
          let ?C1 = "\<forall>l \<in> setOf t1. h l < h x"
          let ?C2 = "\<forall>r \<in> setOf (remove h e t2). h x < h r"
          have o2: "?C2"
          proof -
            from s2 have "setOf (remove h e t2) = setOf t2 - eqs h e" by (simp add: remove_set)
            from s this show ?thesis by auto
          qed
          from o2 s show "?C1 & ?C2" by auto
        qed
      next case False note nxle = this
        from nelx nxle have ex: "h e = h x" by simp
        show ?thesis 
        proof (cases "t1 = Tip")
        case True note t1tip = this
          from ex t1tip have res: "remove h e (T t1 x t2) = t2" by simp
          show ?thesis by (simp add: res t1tip ex s2)
        next case False note t1nTip = this
          from nelx nxle ex t1nTip
          have res: "remove h e (T t1 x t2) =
                     T (wrm h t1) (rm h t1) t2" 
          by (simp add: Let_def wrmrm_decomp)
          from res show ?thesis
          proof simp
            let ?C1 = "sortedTree h (wrm h t1)"
            let ?C2 = "\<forall>l \<in> setOf (wrm h t1). h l < h (rm h t1)"
            let ?C3 = "\<forall>r \<in> setOf t2. h (rm h t1) < h r"
            let ?C4 = "sortedTree h t2"
            from s1 t1nTip have o1: ?C1 by (simp add: wrm_sort)
            from s1 t1nTip have o2: ?C2 by (simp add: wrm_less_rm)
            have o3: ?C3
            proof
              fix r :: 'a 
              assume rt2: "r : setOf t2"
              from s rm_set s1 t1nTip have o1: "h (rm h t1) < h x" by auto
              from rt2 s have o2: "h x < h r" by auto
              from o1 o2 show "h (rm h t1) < h r" by simp
            qed
            from o1 o2 o3 s2 show "?C1 & ?C2 & ?C3 & ?C4" by simp
          qed
        qed
      qed
    qed
  qed  
qed

text \<open>We summarize the specification of remove as follows.\<close>
corollary remove_spec: "sortedTree h t --> 
     sortedTree h (remove h e t) &
     setOf (remove h e t) = setOf t - eqs h e"
by (simp add: remove_sort remove_set)

definition "test = tlookup id 4 (remove id 3 (binsert id 4 (binsert id 3 Tip)))"

export_code test
  in SML module_name BinaryTree_Code file \<open>BinaryTree_Code.ML\<close>

end
