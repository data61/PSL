(*    Title:              SATSolverVerification/Trail.thy
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

section\<open>Trail datatype definition and its properties\<close>

theory Trail
imports MoreList
begin

text\<open>Trail is a list in which some elements can be marked.\<close>
type_synonym 'a Trail = "('a*bool) list"

abbreviation
  element :: "('a*bool) \<Rightarrow> 'a"
  where "element x == fst x"

abbreviation
  marked :: "('a*bool) \<Rightarrow> bool"
  where "marked  x == snd x"

(*--------------------------------------------------------------------------------*)
subsection\<open>Trail elements\<close>

text\<open>Elements of the trail with marks removed\<close>
primrec
elements              :: "'a Trail \<Rightarrow> 'a list"
where
  "elements [] = []"
| "elements (h#t) = (element h) # (elements t)"

lemma
"elements t = map fst t"
by (induct t) auto

lemma eitherMarkedOrNotMarkedElement: 
  shows "a = (element a, True) \<or> a = (element a, False)"
by (cases a) auto

lemma eitherMarkedOrNotMarked:
  assumes "e \<in> set (elements M)"
  shows "(e, True) \<in> set M \<or> (e, False) \<in> set M"
using assms
proof (induct M)
  case (Cons m M')
  thus ?case
    proof (cases "e = element m")
      case True
      thus ?thesis
        using eitherMarkedOrNotMarkedElement [of "m"]
        by auto
    next
      case False
      with Cons
      show ?thesis
        by auto
    qed
qed simp

lemma elementMemElements [simp]:
  assumes "x \<in> set M"
  shows "element x \<in> set (elements M)"
using assms
by (induct M) (auto split: if_split_asm)

lemma elementsAppend [simp]:
  shows "elements (a @ b) = elements a @ elements b"
by (induct a) auto

lemma elementsEmptyIffTrailEmpty [simp]:
  shows "(elements list = []) = (list = [])"
by (induct list) auto

lemma elementsButlastTrailIsButlastElementsTrail [simp]:
  shows "elements (butlast M) = butlast (elements M)"
by (induct M) auto

lemma elementLastTrailIsLastElementsTrail [simp]:
  assumes "M \<noteq> []"
  shows "element (last M) = last (elements M)" 
using assms
by (induct M) auto

lemma isPrefixElements:
  assumes "isPrefix a b"
  shows "isPrefix (elements a) (elements b)"
using assms
unfolding isPrefix_def
by auto

lemma prefixElementsAreTrailElements:
  assumes 
  "isPrefix p M" 
  shows 
  "set (elements p) \<subseteq> set (elements M)"
using assms
unfolding isPrefix_def
by auto

lemma uniqElementsTrailImpliesUniqElementsPrefix:
  assumes 
  "isPrefix p M" and "uniq (elements M)"
  shows
  "uniq (elements p)"
proof-
  from \<open>isPrefix p M\<close>
  obtain s 
    where "M = p @ s"
    unfolding isPrefix_def
    by auto
  with \<open>uniq (elements M)\<close>
  show ?thesis
    using uniqAppend[of "elements p" "elements s"]
    by simp
qed

lemma [simp]: 
  assumes "(e, d) \<in> set M"
  shows "e \<in> set (elements M)"
  using assms
  by (induct M) auto

lemma uniqImpliesExclusiveTrueOrFalse:
  assumes
  "(e, d) \<in> set M" and "uniq (elements M)"
  shows
  "\<not> (e, \<not> d) \<in> set M"
using assms
proof (induct M)
  case (Cons m M')
  {
    assume "(e, d) = m"
    hence "(e, \<not> d) \<noteq> m"
      by auto
    from \<open>(e, d) = m\<close> \<open>uniq (elements (m # M'))\<close>
    have "\<not> (e, d) \<in> set M'"
      by (auto simp add: uniqAppendIff)
    with Cons
    have ?case
      by (auto split: if_split_asm)
  }
  moreover
  {
    assume "(e, \<not> d) = m"
    hence "(e, d) \<noteq> m"
      by auto
    from \<open>(e, \<not> d) = m\<close> \<open>uniq (elements (m # M'))\<close>
    have "\<not> (e, \<not> d) \<in> set M'"
      by (auto simp add: uniqAppendIff)
    with Cons
    have ?case
      by (auto split: if_split_asm)
  }
  moreover
  {
    assume "(e, d) \<noteq> m" "(e, \<not> d) \<noteq> m"
    from \<open>(e, d) \<noteq> m\<close> \<open>(e, d) \<in> set (m # M')\<close> have 
      "(e, d) \<in> set M'"
      by simp
    with \<open>uniq (elements (m # M'))\<close> Cons(1)
    have "\<not> (e, \<not> d) \<in> set M'"
      by simp
    with \<open>(e, \<not> d) \<noteq> m\<close>
    have ?case
      by simp
  }
  moreover 
  {
    have "(e, d) = m \<or> (e, \<not> d) = m \<or> (e, d) \<noteq> m \<and> (e, \<not> d) \<noteq> m"
      by auto
  }
  ultimately
  show ?case
    by auto
qed simp

(*--------------------------------------------------------------------------------*)
subsection\<open>Marked trail elements\<close>

primrec
markedElements        :: "'a Trail \<Rightarrow> 'a list"
where
  "markedElements [] = []"
| "markedElements (h#t) =  (if (marked h) then (element h) # (markedElements t) else (markedElements t))"

lemma
"markedElements t = (elements (filter snd t))"
by (induct t) auto

lemma markedElementIsMarkedTrue: 
  shows "(m \<in> set (markedElements M)) = ((m, True) \<in> set M)"
by (induct M) (auto split: if_split_asm)

lemma markedElementsAppend: 
  shows "markedElements (M1 @ M2) = markedElements M1 @ markedElements M2"
by (induct M1) auto

lemma markedElementsAreElements:
  assumes "m \<in> set (markedElements M)"
  shows   "m \<in> set (elements M)"
using assms markedElementIsMarkedTrue[of "m" "M"]
by auto

lemma markedAndMemberImpliesIsMarkedElement:
  assumes "marked m" "m \<in> set M"
  shows "(element m) \<in> set (markedElements M)"
proof-
  have "m = (element m, marked m)"
    by auto
  with \<open>marked m\<close> 
  have "m = (element m, True)"
    by simp
  with \<open>m \<in> set M\<close> have
    "(element m, True) \<in> set M"
    by simp
  thus ?thesis
    using markedElementIsMarkedTrue [of "element m" "M"]
    by simp
qed

lemma markedElementsPrefixAreMarkedElementsTrail:
  assumes "isPrefix p M" "m \<in> set (markedElements p)"
  shows "m \<in> set (markedElements M)"
proof-
  from \<open>m \<in> set (markedElements p)\<close> 
  have "(m, True) \<in> set p"
    by (simp add: markedElementIsMarkedTrue)
  with \<open>isPrefix p M\<close>
  have "(m, True) \<in> set M"
    using prefixIsSubset[of "p" "M"]
    by auto
  thus ?thesis
    by (simp add: markedElementIsMarkedTrue)
qed

lemma markedElementsTrailMemPrefixAreMarkedElementsPrefix:
  assumes 
  "uniq (elements M)" and
  "isPrefix p M" and
  "m \<in> set (elements p)" and
  "m \<in> set (markedElements M)" 
  shows
  "m \<in> set (markedElements p)"
proof-
  from \<open>m \<in> set (markedElements M)\<close> have "(m, True) \<in> set M"
    by (simp add: markedElementIsMarkedTrue)
  with \<open>uniq (elements M)\<close> \<open>m \<in> set (elements p)\<close>
  have "(m, True) \<in> set p"
  proof-
    {
      assume "(m, False) \<in> set p"
      with \<open>isPrefix p M\<close>
      have "(m, False) \<in> set M"
        using prefixIsSubset[of "p" "M"]
        by auto
      with \<open>(m, True) \<in> set M\<close> \<open>uniq (elements M)\<close>
      have False
        using uniqImpliesExclusiveTrueOrFalse[of "m" "True" "M"]
        by simp
    }
    with \<open>m \<in> set (elements p)\<close>
    show ?thesis
      using eitherMarkedOrNotMarked[of "m" "p"]
      by auto
  qed
  thus ?thesis
    using markedElementIsMarkedTrue[of "m" "p"]
    by simp
qed

(*--------------------------------------------------------------------------------*)
subsection\<open>Prefix before/upto a trail element\<close>

text\<open>Elements of the trail before the first occurrence of a given element - not incuding it\<close>
primrec
prefixBeforeElement  :: "'a \<Rightarrow> 'a Trail \<Rightarrow> 'a Trail"
where
  "prefixBeforeElement e [] = []"
| "prefixBeforeElement e (h#t) = 
 (if (element h) = e then
     []
  else
     (h # (prefixBeforeElement e t))
 )"

lemma "prefixBeforeElement e t = takeWhile (\<lambda> e'. element e' \<noteq> e) t"
by (induct t) auto

lemma "prefixBeforeElement e t = take (firstPos e (elements t)) t"
by (induct t) auto

text\<open>Elements of the trail before the first occurrence of a given element - incuding it\<close>
primrec
prefixToElement  :: "'a \<Rightarrow> 'a Trail \<Rightarrow> 'a Trail"
where
  "prefixToElement e [] = []"
| "prefixToElement e (h#t) = 
   (if (element h) = e then
      [h]
    else
      (h # (prefixToElement e t))
   )"

lemma "prefixToElement e t = take ((firstPos e (elements t)) + 1) t"
by (induct t) auto


lemma isPrefixPrefixToElement:
  shows "isPrefix (prefixToElement e t) t"
unfolding isPrefix_def
by (induct t) auto

lemma isPrefixPrefixBeforeElement:
  shows "isPrefix (prefixBeforeElement e t) t"
unfolding isPrefix_def
by (induct t) auto

lemma prefixToElementContainsTrailElement:
  assumes "e \<in> set (elements M)"
  shows "e \<in> set (elements (prefixToElement e M))"
using assms
by (induct M) auto

lemma prefixBeforeElementDoesNotContainTrailElement:
  assumes "e \<in> set (elements M)"
  shows "e \<notin> set (elements (prefixBeforeElement e M))"
using assms
by (induct M) auto

lemma prefixToElementAppend: 
  shows "prefixToElement e (M1 @ M2) = 
            (if e \<in> set (elements M1) then 
                prefixToElement e M1
             else   
                M1 @ prefixToElement e M2
             )"
by (induct M1) auto


lemma prefixToElementToPrefixElement:
  assumes
  "isPrefix p M" and "e \<in> set (elements p)"
  shows
  "prefixToElement e M = prefixToElement e p"
using assms
unfolding isPrefix_def
proof (induct p arbitrary: M)
  case (Cons a p')
  then obtain s 
    where "(a # p') @ s = M"
    by auto
  show ?case
  proof (cases "(element a) = e")
    case True
    from True \<open>(a # p') @ s = M\<close> have "prefixToElement e M = [a]"
      by auto
    moreover
    from True have "prefixToElement e (a # p') = [a]"
      by auto
    ultimately
    show ?thesis
      by simp
  next
    case False
    from False \<open>(a # p') @ s = M\<close> have "prefixToElement e M = a # prefixToElement e (p' @ s)"
      by auto
    moreover
    from False have "prefixToElement e (a # p') = a # prefixToElement e p'"
      by simp
    moreover
    from False \<open>e \<in> set (elements (a # p'))\<close> have "e \<in> set (elements p')"
      by simp
    have "? s . (p' @ s = p' @ s)"
      by simp
    from \<open>e \<in> set (elements p')\<close>  \<open>? s. (p' @ s = p' @ s)\<close> 
      have "prefixToElement e (p' @ s) = prefixToElement e p'"
      using Cons(1) [of "p' @ s"]
      by simp
    ultimately show ?thesis
      by simp
  qed
qed simp

(*--------------------------------------------------------------------------------*)
subsection\<open>Marked elements upto a given trail element\<close>

text\<open>Marked elements of the trail upto the given element (which is also included if it is marked)\<close>
definition
markedElementsTo :: "'a \<Rightarrow> 'a Trail \<Rightarrow> 'a list"
where
"markedElementsTo e t = markedElements (prefixToElement e t)"

lemma markedElementsToArePrefixOfMarkedElements:
  shows "isPrefix (markedElementsTo e M) (markedElements M)"
unfolding isPrefix_def
unfolding markedElementsTo_def
by (induct M) auto

lemma markedElementsToAreMarkedElements: 
  assumes "m \<in> set (markedElementsTo e M)"
  shows "m \<in> set (markedElements M)"
using assms
using markedElementsToArePrefixOfMarkedElements[of "e" "M"]
using prefixIsSubset
by auto

lemma markedElementsToNonMemberAreAllMarkedElements:
  assumes "e \<notin> set (elements M)"
  shows "markedElementsTo e M = markedElements M" 
using assms
unfolding markedElementsTo_def
by (induct M) auto

lemma markedElementsToAppend: 
  shows "markedElementsTo e (M1 @ M2) = 
          (if e \<in> set (elements M1) then 
                 markedElementsTo e M1
           else 
                 markedElements M1 @ markedElementsTo e M2
          )"
unfolding markedElementsTo_def
by (auto simp add: prefixToElementAppend markedElementsAppend)

lemma markedElementsEmptyImpliesMarkedElementsToEmpty: 
  assumes "markedElements M = []"
  shows "markedElementsTo e M = []"
using assms
using markedElementsToArePrefixOfMarkedElements [of "e" "M"]
unfolding isPrefix_def
by auto

lemma markedElementIsMemberOfItsMarkedElementsTo: 
  assumes
  "uniq (elements M)" and "marked e" and "e \<in> set M"
  shows 
  "element e \<in> set (markedElementsTo (element e) M)"
using assms
unfolding markedElementsTo_def
by (induct M) (auto split: if_split_asm)

lemma markedElementsToPrefixElement: 
  assumes "isPrefix p M" and "e \<in> set (elements p)"
  shows "markedElementsTo e M = markedElementsTo e p"
unfolding markedElementsTo_def
using assms
by (simp add: prefixToElementToPrefixElement)


(*--------------------------------------------------------------------------------*)
subsection\<open>Last marked element in a trail\<close>

definition
lastMarked :: "'a Trail \<Rightarrow> 'a"
where
"lastMarked t = last (markedElements t)"

lemma lastMarkedIsMarkedElement: 
  assumes "markedElements M \<noteq> []" 
  shows "lastMarked M \<in> set (markedElements M)"
using assms
unfolding lastMarked_def
by simp

lemma removeLastMarkedFromMarkedElementsToLastMarkedAreAllMarkedElementsInPrefixLastMarked: 
  assumes
  "markedElements M \<noteq> []"
  shows
  "removeAll (lastMarked M) (markedElementsTo (lastMarked M) M) = markedElements (prefixBeforeElement (lastMarked M) M)"
using assms
unfolding lastMarked_def
unfolding markedElementsTo_def
by (induct M) auto

lemma markedElementsToLastMarkedAreAllMarkedElements:
  assumes
  "uniq (elements M)" and "markedElements M \<noteq> []"
  shows
  "markedElementsTo (lastMarked M) M = markedElements M"
using assms
unfolding lastMarked_def
unfolding markedElementsTo_def
by (induct M) (auto simp add: markedElementsAreElements)

lemma lastTrailElementMarkedImpliesMarkedElementsToLastElementAreAllMarkedElements:
  assumes
  "marked (last M)" and "last (elements M) \<notin> set (butlast (elements M))"
  shows
  "markedElementsTo (last (elements M)) M = markedElements M"
using assms
unfolding markedElementsTo_def
by (induct M) auto

lemma lastMarkedIsMemberOfItsMarkedElementsTo: 
  assumes
  "uniq (elements M)" and "markedElements M \<noteq> []"
  shows
  "lastMarked M \<in> set (markedElementsTo (lastMarked M) M)"
using assms
using markedElementsToLastMarkedAreAllMarkedElements [of "M"]
using lastMarkedIsMarkedElement [of "M"]
by auto

lemma lastTrailElementNotMarkedImpliesMarkedElementsToLAreMarkedElementsToLInButlastTrail: 
  assumes "\<not> marked (last M)"
  shows "markedElementsTo e M = markedElementsTo e (butlast M)"
using assms
unfolding markedElementsTo_def
by (induct M) auto


(*--------------------------------------------------------------------------------*)
subsection\<open>Level of a trail element\<close>

text\<open>Level of an element is the number of marked elements that precede it\<close>

definition
elementLevel :: "'a \<Rightarrow> 'a Trail \<Rightarrow> nat"
where
"elementLevel e t = length (markedElementsTo e t)"

lemma elementLevelMarkedGeq1:
  assumes
  "uniq (elements M)" and "e \<in> set (markedElements M)"
  shows
  "elementLevel e M >= 1"
proof-
  from \<open>e \<in> set (markedElements M)\<close> have "(e, True) \<in> set M"
    by (simp add: markedElementIsMarkedTrue)
  with \<open>uniq (elements M)\<close>  have "e \<in> set (markedElementsTo e M)"
    using markedElementIsMemberOfItsMarkedElementsTo[of "M" "(e, True)"]
    by simp
  hence "markedElementsTo e M \<noteq> []"
    by auto
  thus ?thesis
    unfolding elementLevel_def
    using length_greater_0_conv[of "markedElementsTo e M"]
    by arith
qed

lemma elementLevelAppend:
  assumes "a \<in> set (elements M)"
  shows "elementLevel a M = elementLevel a (M @ M')"
using assms
unfolding elementLevel_def
by (simp add: markedElementsToAppend)


lemma elementLevelPrecedesLeq: 
  assumes
  "precedes a b (elements M)" 
  shows
  "elementLevel a M \<le> elementLevel b M"
using assms
proof (induct M)
  case (Cons m M')
  {
    assume "a = element m"
    hence ?case
      unfolding elementLevel_def
      unfolding markedElementsTo_def
      by simp
  }
  moreover
  {
    assume "b = element m"
    {
      assume "a \<noteq> b"
      hence "\<not> precedes a b (b # (elements M'))"
        by (rule noElementsPrecedesFirstElement)
      with \<open>b = element m\<close> \<open>precedes a b (elements (m # M'))\<close>
      have False
        by simp
    }
    hence "a = b"
      by auto
    hence ?case
      by simp
  }
  moreover 
  { 
    assume "a \<noteq> element m" "b \<noteq> element m"
    moreover
    from \<open>precedes a b (elements (m # M'))\<close>
    have "a \<in> set (elements (m # M'))" "b \<in> set (elements (m # M'))"
      unfolding precedes_def
      by (auto split: if_split_asm)
    from \<open>a \<noteq> element m\<close> \<open>a \<in> set (elements (m # M'))\<close>
    have "a \<in> set (elements M')"
      by simp
    moreover
    from \<open>b \<noteq> element m\<close> \<open>b \<in> set (elements (m # M'))\<close>
    have "b \<in> set (elements M')"
      by simp
    ultimately
    have "elementLevel a M' \<le> elementLevel b M'"
      using Cons
      unfolding precedes_def
      by auto
    hence ?case
      using \<open>a \<noteq> element m\<close> \<open>b \<noteq> element m\<close>
      unfolding elementLevel_def
      unfolding markedElementsTo_def
      by auto
  }
  ultimately
  show ?case
    by auto
next
  case Nil
  thus ?case
    unfolding precedes_def
    by simp
qed


lemma elementLevelPrecedesMarkedElementLt: 
  assumes
  "uniq (elements M)" and
  "e \<noteq> d" and
  "d \<in> set (markedElements M)" and
  "precedes e d (elements M)"
  shows
  "elementLevel e M < elementLevel d M"
using assms
proof (induct M)
  case (Cons m M')
  {
    assume "e = element m"
    moreover
    with \<open>e \<noteq> d\<close> have "d \<noteq> element m"
      by simp
    moreover
    from \<open>uniq (elements (m # M'))\<close> \<open>d \<in> set (markedElements (m # M'))\<close>
    have "1 \<le> elementLevel d (m # M')"
      using elementLevelMarkedGeq1[of "m # M'" "d"]
      by auto
    moreover
    from \<open>d \<noteq> element m\<close> \<open>d \<in> set (markedElements (m # M'))\<close>
    have "d \<in> set (markedElements M')"
      by (simp split: if_split_asm)
    from \<open>uniq (elements (m # M'))\<close> \<open>d \<in> set (markedElements M')\<close>
    have "1 \<le> elementLevel d M'"
      using elementLevelMarkedGeq1[of "M'" "d"]
      by auto
    ultimately
    have ?case
      unfolding elementLevel_def
      unfolding markedElementsTo_def
      by (auto split: if_split_asm)
  }
  moreover
  {
    assume "d = element m"
    from \<open>e \<noteq> d\<close> have "\<not> precedes e d (d # (elements M'))"
      using noElementsPrecedesFirstElement[of "e" "d" "elements M'"]
      by simp
    with \<open>d = element m\<close> \<open>precedes e d (elements (m # M'))\<close>
    have False
      by simp
    hence ?case
      by simp
  }
  moreover
  {
    assume "e \<noteq> element m" "d \<noteq> element m"    
    moreover
    from \<open>precedes e d (elements (m # M'))\<close>
    have "e \<in> set (elements (m # M'))" "d \<in> set (elements (m # M'))"
      unfolding precedes_def
      by (auto split: if_split_asm)
    from \<open>e \<noteq> element m\<close> \<open>e \<in> set (elements (m # M'))\<close>
    have "e \<in> set (elements M')"
      by simp
    moreover
    from \<open>d \<noteq> element m\<close> \<open>d \<in> set (elements (m # M'))\<close>
    have "d \<in> set (elements M')"
      by simp
    moreover
    from \<open>d \<noteq> element m\<close> \<open>d \<in> set (markedElements (m # M'))\<close>
    have "d \<in> set (markedElements M')"
      by (simp split: if_split_asm)
    ultimately
    have "elementLevel e M' < elementLevel d M'"
      using \<open>uniq (elements (m # M'))\<close> Cons
      unfolding precedes_def
      by auto
    hence ?case
      using \<open>e \<noteq> element m\<close> \<open>d \<noteq> element m\<close>
      unfolding elementLevel_def
      unfolding markedElementsTo_def
      by auto
  }
  ultimately
  show ?case
    by auto
qed simp

lemma differentMarkedElementsHaveDifferentLevels:
  assumes
  "uniq (elements M)" and
  "a \<in> set (markedElements M)" and
  "b \<in> set (markedElements M)" and
  "a \<noteq> b" 
  shows "elementLevel a M \<noteq> elementLevel b M"
proof-
  from \<open>a \<in> set (markedElements M)\<close>
  have "a \<in> set (elements M)"
    by (simp add: markedElementsAreElements)
  moreover
  from \<open>b \<in> set (markedElements M)\<close>
  have "b \<in> set (elements M)"
    by (simp add: markedElementsAreElements)
  ultimately
  have "precedes a b (elements M) \<or> precedes b a (elements M)"
    using \<open>a \<noteq> b\<close>
    using precedesTotalOrder[of "a" "elements M" "b"]
    by simp
  moreover
  {
    assume "precedes a b (elements M)"
    with assms
    have ?thesis
      using elementLevelPrecedesMarkedElementLt[of "M" "a" "b"]
      by auto
  }
  moreover
  {
    assume "precedes b a (elements M)"
    with assms
    have ?thesis
      using elementLevelPrecedesMarkedElementLt[of "M" "b" "a"]
      by auto
  }
  ultimately
  show ?thesis
    by auto
qed


(* ------------------------------------------------------------------------- *)
subsection\<open>Current trail level\<close>

text\<open>Current level is the number of marked elements in the trail\<close>

definition
currentLevel :: "'a Trail \<Rightarrow> nat"
where
"currentLevel t = length (markedElements t)"

lemma currentLevelNonMarked: 
  shows "currentLevel M = currentLevel (M @ [(l, False)])"
by (auto simp add:currentLevel_def markedElementsAppend)

lemma currentLevelPrefix:
  assumes "isPrefix a b" 
  shows "currentLevel a <= currentLevel b"
using assms
unfolding isPrefix_def
unfolding currentLevel_def
by (auto simp add: markedElementsAppend)

lemma elementLevelLeqCurrentLevel:
  shows "elementLevel a M \<le> currentLevel M"
proof-
  have "isPrefix (prefixToElement a M) M"
    using isPrefixPrefixToElement[of "a" "M"]
    .
  then obtain s
    where "prefixToElement a M @ s = M"
    unfolding isPrefix_def
    by auto
  hence "M = prefixToElement a M @ s"
    by (rule sym)
  hence "currentLevel M = currentLevel (prefixToElement a M @ s)"
    by simp
  hence "currentLevel M = length (markedElements (prefixToElement a M)) + length (markedElements s)"
    unfolding currentLevel_def
    by (simp add: markedElementsAppend)
  thus ?thesis
    unfolding elementLevel_def
    unfolding markedElementsTo_def
    by simp
qed

lemma elementOnCurrentLevel:
  assumes "a \<notin> set (elements M)"
  shows "elementLevel a (M @ [(a, d)]) = currentLevel  (M @ [(a, d)])"
using assms
unfolding currentLevel_def
unfolding elementLevel_def
unfolding markedElementsTo_def 
by (auto simp add: prefixToElementAppend)

(*--------------------------------------------------------------------------------*)
subsection\<open>Prefix to a given trail level\<close>

text\<open>Prefix is made or elements of the trail up to a given element level\<close>


primrec
prefixToLevel_aux :: "'a Trail \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Trail"
where
  "(prefixToLevel_aux [] l cl) = []"
| "(prefixToLevel_aux (h#t) l cl) = 
  (if (marked h) then
    (if (cl >= l) then [] else (h # (prefixToLevel_aux t l (cl+1))))
  else
    (h # (prefixToLevel_aux t l cl))
  )"

definition
prefixToLevel :: "nat \<Rightarrow> 'a Trail \<Rightarrow> 'a Trail"
where
prefixToLevel_def: "(prefixToLevel l t) == (prefixToLevel_aux t l 0)"


lemma isPrefixPrefixToLevel_aux:
  shows "\<exists> s. prefixToLevel_aux t l i @ s = t"
by (induct t arbitrary: i) auto

lemma isPrefixPrefixToLevel:
  shows "(isPrefix (prefixToLevel l t) t)"
using isPrefixPrefixToLevel_aux[of "t" "l"]
unfolding isPrefix_def
unfolding prefixToLevel_def
by simp

lemma currentLevelPrefixToLevel_aux: 
  assumes "l \<ge> i"
  shows "currentLevel (prefixToLevel_aux M l i) <= l - i"
using assms
proof (induct M arbitrary: i)
  case (Cons m M')
  {
    assume "marked m" "i = l"
    hence ?case
      unfolding currentLevel_def
      by simp
  }
  moreover
  {
    assume "marked m" "i < l"
    hence ?case
      using Cons(1) [of "i+1"]
      unfolding currentLevel_def
      by simp
  }
  moreover
  {
    assume "\<not> marked m"
    hence ?case
      using Cons
      unfolding currentLevel_def
      by simp
  }
  ultimately
  show ?case
    using \<open>i <= l\<close>
    by auto
next
  case Nil
  thus ?case
    unfolding currentLevel_def
    by simp
qed

lemma currentLevelPrefixToLevel: 
  shows "currentLevel (prefixToLevel level M) \<le> level"
using currentLevelPrefixToLevel_aux[of "0" "level" "M"]
unfolding prefixToLevel_def
by simp

lemma currentLevelPrefixToLevelEq_aux: 
  assumes "l \<ge> i" "currentLevel M >= l - i"
  shows "currentLevel (prefixToLevel_aux M l i) = l - i"
using assms
proof (induct M arbitrary: i)
  case (Cons m M')
  {
    assume "marked m" "i = l"
    hence ?case
      unfolding currentLevel_def
      by simp
  }
  moreover
  {
    assume "marked m" "i < l"
    hence ?case
      using Cons(1) [of "i+1"]
      using Cons(3)
      unfolding currentLevel_def
      by simp
  }
  moreover
  {
    assume "\<not> marked m"
    hence ?case
      using Cons
      unfolding currentLevel_def
      by simp
  }
  ultimately
  show ?case
    using \<open>i <= l\<close>
    by auto
next
  case Nil
  thus ?case
    unfolding currentLevel_def
    by simp
qed

lemma currentLevelPrefixToLevelEq:
assumes
  "level \<le> currentLevel M"
shows
  "currentLevel (prefixToLevel level M) = level"
using assms
unfolding prefixToLevel_def
using currentLevelPrefixToLevelEq_aux[of "0" "level" "M"]
by simp

lemma prefixToLevel_auxIncreaseAuxilaryCounter: 
  assumes "k \<ge> i"
  shows "prefixToLevel_aux M l i = prefixToLevel_aux M (l + (k - i)) k"
using assms
proof (induct M arbitrary: i k)
  case (Cons m M')
  {
    assume "\<not> marked m"
    hence ?case
      using Cons(1)[of "i" "k"] Cons(2)
      by simp
  }
  moreover
  {
    assume "i \<ge> l" "marked m"
    hence ?case
      using \<open>k \<ge> i\<close>
      by simp
  }
  moreover
  {
    assume "i < l" "marked m"
    hence ?case
      using Cons(1)[of "i+1" "k+1"] Cons(2)
      by simp
  }
  ultimately
  show ?case
    by (auto split: if_split_asm)
qed simp

lemma isPrefixPrefixToLevel_auxLowerLevel:
  assumes "i \<le> j"
  shows "isPrefix (prefixToLevel_aux M i k) (prefixToLevel_aux M j k)"
using assms
by (induct M arbitrary: k) (auto simp add:isPrefix_def)

lemma isPrefixPrefixToLevelLowerLevel:
assumes "level < level'"
shows "isPrefix (prefixToLevel level M) (prefixToLevel level' M)"
using assms
unfolding prefixToLevel_def
using isPrefixPrefixToLevel_auxLowerLevel[of "level" "level'" "M" "0"]
by simp

lemma prefixToLevel_auxPrefixToLevel_auxHigherLevel: 
  assumes "i \<le> j"
  shows "prefixToLevel_aux a i k = prefixToLevel_aux (prefixToLevel_aux a j k) i k"
using assms
by (induct a arbitrary: k) auto

lemma prefixToLevelPrefixToLevelHigherLevel: 
  assumes "level \<le> level'"
  shows "prefixToLevel level M = prefixToLevel level (prefixToLevel level' M)"
using assms
unfolding prefixToLevel_def
using prefixToLevel_auxPrefixToLevel_auxHigherLevel[of "level" "level'" "M" "0"]
by simp

lemma prefixToLevelAppend_aux1:
  assumes
  "l \<ge> i" and "l - i < currentLevel a"
  shows 
  "prefixToLevel_aux (a @ b) l i = prefixToLevel_aux a l i"
using assms
proof (induct a arbitrary: i)
  case (Cons a a')
  {
    assume "\<not> marked a"
    hence ?case
      using Cons(1)[of "i"] \<open>i \<le> l\<close> \<open>l - i < currentLevel (a # a')\<close>
      unfolding currentLevel_def
      by simp
  }
  moreover
  {
    assume "marked a" "l = i"
    hence ?case
      by simp
  }
  moreover
  {
    assume "marked a" "l > i"
    hence ?case
      using Cons(1)[of "i + 1"] \<open>i \<le> l\<close> \<open>l - i < currentLevel (a # a')\<close>
      unfolding currentLevel_def
      by simp
  }
  ultimately
  show ?case
    using \<open>i \<le> l\<close>
    by auto
next
  case Nil
  thus ?case
    unfolding currentLevel_def
    by simp
qed


lemma prefixToLevelAppend_aux2: 
  assumes 
  "i \<le> l" and "currentLevel a + i \<le> l"
  shows "prefixToLevel_aux (a @ b) l i = a @ prefixToLevel_aux b l (i + (currentLevel a))"
using assms
proof (induct a arbitrary: i)
  case (Cons a a')
  {
    assume "\<not> marked a"
    hence ?case
      using Cons
      unfolding currentLevel_def
      by simp
  }
  moreover
  {
    assume "marked a" "l = i"
    hence ?case
      using \<open>(currentLevel (a # a')) + i \<le> l\<close>
      unfolding currentLevel_def
      by simp
  }
  moreover
  {
    assume "marked a" "l > i"
    hence "prefixToLevel_aux (a' @ b) l (i + 1) = a' @ prefixToLevel_aux b l (i + 1 + currentLevel a')"
      using Cons(1) [of "i + 1"] \<open>(currentLevel (a # a')) + i \<le> l\<close>
      unfolding currentLevel_def
      by simp
    moreover
    have "i + 1 + length (markedElements a') = i + (1 + length (markedElements a'))"
      by simp
    ultimately
    have ?case
      using \<open>marked a\<close> \<open>l > i\<close>
      unfolding currentLevel_def
      by simp
  }
  ultimately
  show ?case
    using \<open>l \<ge> i\<close>
    by auto
next
  case Nil
  thus ?case
    unfolding currentLevel_def
    by simp
qed

lemma prefixToLevelAppend:
  shows "prefixToLevel level (a @ b) = 
  (if level < currentLevel a then 
      prefixToLevel level a
  else 
      a @ prefixToLevel_aux b level (currentLevel a)
  )"
proof (cases "level < currentLevel a")
  case True
  thus ?thesis
    unfolding prefixToLevel_def
    using prefixToLevelAppend_aux1[of "0" "level" "a"]
    by simp
next
  case False
  thus ?thesis
    unfolding prefixToLevel_def
    using prefixToLevelAppend_aux2[of "0" "level" "a"]
    by simp
qed

lemma isProperPrefixPrefixToLevel:
  assumes "level < currentLevel t" 
  shows "\<exists> s. (prefixToLevel level t) @ s = t \<and> s \<noteq> [] \<and> (marked (hd s))"
proof-
  have "isPrefix (prefixToLevel level t) t"
    by (simp add:isPrefixPrefixToLevel)
  then obtain s::"'a Trail"
    where "(prefixToLevel level t) @ s = t"
    unfolding isPrefix_def
    by auto
  moreover
  have "s \<noteq> []"
  proof-
    {
      assume "s = []"
      with \<open>(prefixToLevel level t) @ s = t\<close> 
      have "prefixToLevel level t = t"
        by simp
      hence "currentLevel (prefixToLevel level t) \<le> level"
        using currentLevelPrefixToLevel[of "level" "t"]
        by simp
      with \<open>prefixToLevel level t = t\<close> have "currentLevel t \<le> level"
        by simp
      with \<open>level < currentLevel t\<close> have False
        by simp
    }
    thus ?thesis
      by auto
  qed
  moreover
  have "marked (hd s)"
  proof-
    {
      assume "\<not> marked (hd s)"
      have "currentLevel (prefixToLevel level t) \<le> level"
        by (simp add:currentLevelPrefixToLevel)
      from \<open>s \<noteq> []\<close> have "s = [hd s] @ (tl s)"
        by simp
      with \<open>(prefixToLevel level t) @ s = t\<close> have
        "t = (prefixToLevel level t) @ [hd s] @ (tl s)"
        by simp
      hence "(prefixToLevel level t) = (prefixToLevel level ((prefixToLevel level t) @ [hd s] @ (tl s)))"
        by simp
      also
      with \<open>currentLevel (prefixToLevel level t) \<le> level\<close> 
      have "\<dots> = ((prefixToLevel level t) @ (prefixToLevel_aux ([hd s] @ (tl s)) level (currentLevel (prefixToLevel level t))))"
        by (auto simp add: prefixToLevelAppend)
      also
      have "\<dots> = 
        ((prefixToLevel level t) @ (hd s) # prefixToLevel_aux (tl s) level (currentLevel (prefixToLevel level t)))"
      proof-
        from \<open>currentLevel (prefixToLevel level t) <= level\<close> \<open>\<not> marked (hd s)\<close>
        have "prefixToLevel_aux ([hd s] @ (tl s)) level (currentLevel (prefixToLevel level t)) = 
          (hd s) # prefixToLevel_aux (tl s) level (currentLevel (prefixToLevel level t))"
          by simp
        thus ?thesis
          by simp
      qed
      ultimately
      have "(prefixToLevel level t) = (prefixToLevel level t) @ (hd s) # prefixToLevel_aux (tl s) level (currentLevel (prefixToLevel level t))"
        by simp
      hence "False"
        by auto
    }
    thus ?thesis
      by auto
  qed
  ultimately
  show ?thesis
    by auto
qed

lemma prefixToLevelElementsElementLevel: 
  assumes 
  "e  \<in> set (elements (prefixToLevel level M))"
  shows
  "elementLevel e M \<le> level"
proof -
  have "elementLevel e (prefixToLevel level M) \<le> currentLevel (prefixToLevel  level M)"
    by (simp add: elementLevelLeqCurrentLevel)
  moreover
  hence "currentLevel (prefixToLevel level M) \<le> level"
    using currentLevelPrefixToLevel[of "level" "M"]
    by simp
  ultimately have "elementLevel e (prefixToLevel level M) \<le> level"
    by simp
  moreover
  have "isPrefix (prefixToLevel level M) M"
    by (simp add:isPrefixPrefixToLevel)
  then obtain s
    where "(prefixToLevel level M) @ s = M"
    unfolding isPrefix_def
    by auto
  with \<open>e  \<in> set (elements (prefixToLevel level M))\<close> 
  have "elementLevel e (prefixToLevel level M) = elementLevel e M"
    using elementLevelAppend [of "e" "prefixToLevel level M" "s"]
    by simp
  ultimately
  show ?thesis
    by simp
qed

lemma elementLevelLtLevelImpliesMemberPrefixToLevel_aux:
  assumes
  "e  \<in> set(elements M)" and
  "elementLevel e M + i \<le> level" and
  "i \<le> level"
  shows 
  "e  \<in> set (elements (prefixToLevel_aux M level i))"
using assms
proof (induct M arbitrary: i)
  case (Cons m M')
  thus ?case
  proof (cases "e = element m")
    case True
    thus ?thesis
      using \<open>elementLevel e (m # M') + i \<le> level\<close>
      unfolding prefixToLevel_def
      unfolding elementLevel_def
      unfolding markedElementsTo_def
      by (simp split: if_split_asm)
  next
    case False
    with \<open>e \<in> set (elements (m # M'))\<close>
    have "e \<in> set (elements M')"
      by simp

    show ?thesis
    proof (cases "marked m")
      case True
      with Cons \<open>e \<noteq> element m\<close>
      have "(elementLevel e M') + i + 1 \<le> level"
        unfolding elementLevel_def
        unfolding markedElementsTo_def
        by (simp split: if_split_asm)
      moreover
      have "elementLevel e M' \<ge> 0"
        by auto
      ultimately
      have "i + 1 \<le> level"
        by simp
      with \<open>e \<in> set (elements M')\<close> \<open>(elementLevel e M') + i + 1 \<le> level\<close> Cons(1)[of "i+1"]
      have "e \<in> set (elements (prefixToLevel_aux M' level (i + 1)))"
        by simp
      with \<open>e \<noteq> element m\<close> \<open>i + 1 \<le> level\<close> True 
      show ?thesis
        by simp
    next
      case False
      with \<open>e \<noteq> element m\<close> \<open>elementLevel e (m # M') + i \<le> level\<close> have "elementLevel e M' + i \<le> level"
        unfolding elementLevel_def
        unfolding markedElementsTo_def
        by (simp split: if_split_asm)
      with \<open>e \<in> set (elements M')\<close> have "e \<in> set (elements (prefixToLevel_aux M' level i))"
        using Cons
        by (auto split: if_split_asm)
      with \<open>e \<noteq> element m\<close> False show ?thesis
        by simp
    qed
  qed
qed simp

lemma elementLevelLtLevelImpliesMemberPrefixToLevel:
  assumes
  "e \<in> set (elements M)" and
  "elementLevel e M \<le> level"
  shows 
  "e \<in> set (elements (prefixToLevel level M))"
using assms
using elementLevelLtLevelImpliesMemberPrefixToLevel_aux[of "e" "M" "0" "level"]
unfolding prefixToLevel_def
by simp

lemma literalNotInEarlierLevelsThanItsLevel: 
  assumes
  "level < elementLevel e M" 
  shows 
  "e \<notin> set (elements (prefixToLevel level M))"
proof-
  {
    assume "\<not> ?thesis"
    hence "level \<ge> elementLevel e M"
      by (simp add: prefixToLevelElementsElementLevel)
    with \<open>level < elementLevel e M\<close>
    have False
      by simp
  }
  thus ?thesis
    by auto
qed

lemma elementLevelPrefixElement: 
  assumes "e \<in> set (elements (prefixToLevel level M))"
  shows "elementLevel e (prefixToLevel level M) = elementLevel e M"
using assms
proof-
  have "isPrefix (prefixToLevel level M) M"
    by (simp add: isPrefixPrefixToLevel)
  then obtain s where "(prefixToLevel level M) @ s = M"
    unfolding isPrefix_def
    by auto
  with assms show ?thesis
    using elementLevelAppend[of "e" "prefixToLevel level M" "s"]
    by auto
qed

lemma currentLevelZeroTrailEqualsItsPrefixToLevelZero:
  assumes "currentLevel M = 0" 
  shows "M = prefixToLevel 0 M"
using assms
proof (induct M)
  case (Cons a M')
  show ?case
  proof-
    from Cons
    have "currentLevel M' = 0" and "markedElements M' = []" and "\<not> marked a"
      unfolding currentLevel_def
      by (auto split: if_split_asm)
    thus ?thesis
      using Cons
      unfolding prefixToLevel_def
      by auto
  qed
next
  case Nil
  thus ?case
    unfolding currentLevel_def
    unfolding prefixToLevel_def
    by simp
qed

(*--------------------------------------------------------------------------------*)
subsection\<open>Number of literals of every trail level\<close>

primrec
levelsCounter_aux :: "'a Trail \<Rightarrow> nat list \<Rightarrow> nat list"
where
  "levelsCounter_aux [] l = l"
| "levelsCounter_aux (h # t) l = 
    (if (marked h) then 
        levelsCounter_aux t (l @ [1]) 
     else
        levelsCounter_aux t (butlast l @ [Suc (last l)])
    )"

definition
levelsCounter :: "'a Trail \<Rightarrow> nat list"
where
"levelsCounter t = levelsCounter_aux t [0]"


lemma levelsCounter_aux_startIrellevant: 
  "\<forall> y. y \<noteq> [] \<longrightarrow> levelsCounter_aux a (x @ y) = (x @ levelsCounter_aux a y)"
by (induct a) (auto simp add: butlastAppend)

lemma levelsCounter_auxSuffixContinues: "\<forall> l. levelsCounter_aux (a @ b) l = levelsCounter_aux b (levelsCounter_aux a l)"
by (induct a) auto

lemma levelsCounter_auxNotEmpty: "\<forall> l. l \<noteq> [] \<longrightarrow> levelsCounter_aux a l \<noteq> []"
by (induct a) auto

lemma levelsCounter_auxIncreasesFirst: 
"\<forall> m n l1 l2. levelsCounter_aux a (m # l1) = n # l2 \<longrightarrow> m <= n"
proof (induct "a")
  case Nil
  {
    fix m::nat and n::nat and l1::"nat list" and l2::"nat list"
    assume "levelsCounter_aux [] (m # l1) = n # l2"
    hence "m = n"
      by simp
  }
  thus ?case
    by simp
next
  case (Cons a list)
  {
    fix m::nat and n::nat and l1::"nat list" and l2::"nat list"
    assume "levelsCounter_aux (a # list) (m # l1) = n # l2"
    have "m <= n"
    proof (cases "marked a")
      case True
      with \<open>levelsCounter_aux (a # list) (m # l1) = n # l2\<close> 
      have "levelsCounter_aux list (m # l1 @ [Suc 0]) = n # l2"
        by simp
      with Cons
      show ?thesis
        by auto
    next
      case False
      show ?thesis 
      proof (cases "l1 = []")
        case True
        with \<open>\<not> marked a\<close> \<open>levelsCounter_aux (a # list) (m # l1) = n # l2\<close> 
        have "levelsCounter_aux list [Suc m] = n # l2"
          by simp
        with Cons
        have "Suc m <= n"
          by auto
        thus ?thesis
          by simp
      next
        case False
        with \<open>\<not> marked a\<close> \<open>levelsCounter_aux (a # list) (m # l1) = n # l2\<close> 
        have "levelsCounter_aux list (m # butlast l1 @ [Suc (last l1)]) = n # l2"
          by simp
        with Cons
        show ?thesis
          by auto
      qed
    qed
  }
  thus ?case
    by simp
qed

lemma levelsCounterPrefix:
  assumes "(isPrefix p a)"
  shows "? rest. rest \<noteq> [] \<and> levelsCounter a = butlast (levelsCounter p) @ rest \<and> last (levelsCounter p) \<le> hd rest"
proof-
  from assms
  obtain s :: "'a Trail" where "p @ s = a"
    unfolding isPrefix_def
    by auto
  from \<open>p @ s = a\<close> have "levelsCounter a = levelsCounter (p @ s)"
    by simp
  show ?thesis
  proof (cases "s = []")
    case True
    have "(levelsCounter a) = (butlast (levelsCounter p)) @ [last (levelsCounter p)] \<and> 
      (last (levelsCounter p)) <= hd [last (levelsCounter p)]"
      using \<open>p @ s = a\<close> \<open>s = []\<close>
      unfolding levelsCounter_def
      using levelsCounter_auxNotEmpty[of "p"]
      by auto
    thus ?thesis
      by auto
  next
    case False
    show ?thesis
    proof (cases "marked (hd s)")
      case True
      from \<open>p @ s = a\<close> have "levelsCounter a = levelsCounter (p @ s)"
        by simp
      also
      have "\<dots> = levelsCounter_aux s (levelsCounter_aux p [0])"
        unfolding levelsCounter_def
        by (simp add: levelsCounter_auxSuffixContinues)
      also
      have "\<dots> = levelsCounter_aux (tl s) ((levelsCounter_aux p [0]) @ [1])"
      proof-
        from \<open>s \<noteq> []\<close> have "s = hd s # tl s"
          by simp
        then have "levelsCounter_aux s (levelsCounter_aux p [0]) = levelsCounter_aux (hd s # tl s) (levelsCounter_aux p [0])"
          by simp
        with \<open>marked (hd s)\<close> show ?thesis
          by simp
      qed
      also
      have "\<dots> = levelsCounter_aux p [0] @ (levelsCounter_aux (tl s) [1])"
        by (simp add: levelsCounter_aux_startIrellevant)
      finally 
      have "levelsCounter a = levelsCounter p @ (levelsCounter_aux (tl s) [1])"
        unfolding levelsCounter_def
        by simp
      hence "(levelsCounter a) = (butlast (levelsCounter p)) @ ([last (levelsCounter p)] @ (levelsCounter_aux (tl s) [1])) \<and> 
        (last (levelsCounter p)) <= hd ([last (levelsCounter p)] @ (levelsCounter_aux (tl s) [1]))"
        unfolding levelsCounter_def
        using levelsCounter_auxNotEmpty[of "p"]
        by auto
      thus ?thesis
        by auto
    next
      case False
      from \<open>p @ s = a\<close> have "levelsCounter a = levelsCounter (p @ s)"
        by simp
      also
      have "\<dots> = levelsCounter_aux s (levelsCounter_aux p [0])"
        unfolding levelsCounter_def
        by (simp add: levelsCounter_auxSuffixContinues)
      also
      have "\<dots> = levelsCounter_aux (tl s) ((butlast (levelsCounter_aux p [0])) @ [Suc (last (levelsCounter_aux p [0]))])"
      proof-
        from \<open>s \<noteq> []\<close> have "s = hd s # tl s"
          by simp
        then have "levelsCounter_aux s (levelsCounter_aux p [0]) = levelsCounter_aux (hd s # tl s) (levelsCounter_aux p [0])"
          by simp
        with \<open>~marked (hd s)\<close> show ?thesis
          by simp
      qed
      also
      have "\<dots> = butlast (levelsCounter_aux p [0]) @ (levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))])"
        by (simp add: levelsCounter_aux_startIrellevant)
      finally 
      have "levelsCounter a = butlast (levelsCounter_aux p [0]) @ (levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))])"
        unfolding levelsCounter_def
        by simp
      moreover
      have "hd (levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))]) >= Suc (last (levelsCounter_aux p [0]))"
      proof-
        have "(levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))]) \<noteq> []"
          using levelsCounter_auxNotEmpty[of "tl s"]
          by simp
        then obtain h t where "(levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))]) = h # t"
          using neq_Nil_conv[of "(levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))])"]
          by auto
        hence "h \<ge> Suc (last (levelsCounter_aux p [0]))"
          using levelsCounter_auxIncreasesFirst[of "tl s"]
          by auto
        with \<open>(levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))]) = h # t\<close> 
        show ?thesis
          by simp
      qed
      ultimately
      have "levelsCounter a = butlast (levelsCounter p) @ (levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))]) \<and> 
        last (levelsCounter p) \<le> hd (levelsCounter_aux (tl s) [Suc (last (levelsCounter_aux p [0]))])"
        unfolding levelsCounter_def
        by simp
      thus ?thesis
        using levelsCounter_auxNotEmpty[of "tl s"]
        by auto
    qed
  qed
qed
  
lemma levelsCounterPrefixToLevel:
  assumes "p = prefixToLevel level a" "level \<ge> 0" "level < currentLevel a" 
  shows "? rest . rest \<noteq> [] \<and> (levelsCounter a) = (levelsCounter p) @ rest"
proof-
  from assms
  obtain s :: "'a Trail" where "p @ s = a" "s \<noteq> []" "marked (hd s)"
    using isProperPrefixPrefixToLevel[of "level" "a"]
    by auto
  from \<open>p @ s = a\<close> have "levelsCounter a = levelsCounter (p @ s)"
    by simp
  also
  have "\<dots> = levelsCounter_aux s (levelsCounter_aux p [0])"
    unfolding levelsCounter_def
    by (simp add: levelsCounter_auxSuffixContinues)
  also
  have "\<dots> = levelsCounter_aux (tl s) ((levelsCounter_aux p [0]) @ [1])"
  proof-
    from \<open>s \<noteq> []\<close> have "s = hd s # tl s"
      by simp
    then have "levelsCounter_aux s (levelsCounter_aux p [0]) = levelsCounter_aux (hd s # tl s) (levelsCounter_aux p [0])"
      by simp
    with \<open>marked (hd s)\<close> show ?thesis
      by simp
  qed
  also
  have "\<dots> = levelsCounter_aux p [0] @ (levelsCounter_aux (tl s) [1])"
    by (simp add: levelsCounter_aux_startIrellevant)
  finally 
  have "levelsCounter a = levelsCounter p @ (levelsCounter_aux (tl s) [1])"
    unfolding levelsCounter_def
    by simp
  moreover
  have "levelsCounter_aux (tl s) [1] \<noteq> []"
    by (simp add: levelsCounter_auxNotEmpty)
  ultimately
  show ?thesis
    by simp
qed


(*--------------------------------------------------------------------------------*)
subsection\<open>Prefix before last marked element\<close>

primrec
prefixBeforeLastMarked  :: "'a Trail \<Rightarrow> 'a Trail"
where
  "prefixBeforeLastMarked [] = []"
| "prefixBeforeLastMarked (h#t) =  (if (marked h) \<and> (markedElements t) = [] then [] else (h#(prefixBeforeLastMarked t)))"

lemma prefixBeforeLastMarkedIsPrefixBeforeLastLevel:
  assumes "markedElements M \<noteq> []"
  shows "prefixBeforeLastMarked M = prefixToLevel ((currentLevel M) - 1) M"
using assms
proof (induct M)
  case Nil
  thus ?case
    by simp
next
  case (Cons a M')
  thus ?case
  proof (cases "marked a")
    case True
    hence "currentLevel (a # M') \<ge> 1"
      unfolding currentLevel_def
      by simp
    with True Cons show ?thesis
      using prefixToLevel_auxIncreaseAuxilaryCounter[of "0" "1" "M'" "currentLevel M' - 1"]
      unfolding prefixToLevel_def
      unfolding currentLevel_def
      by auto
  next
    case False
    with Cons show ?thesis
      unfolding prefixToLevel_def
      unfolding currentLevel_def
      by auto
  qed
qed

lemma isPrefixPrefixBeforeLastMarked:
  shows "isPrefix (prefixBeforeLastMarked M) M"
unfolding isPrefix_def
by (induct M) auto

lemma lastMarkedNotInPrefixBeforeLastMarked:
  assumes "uniq (elements M)" and "markedElements M \<noteq> []"
  shows "\<not> (lastMarked M) \<in> set (elements (prefixBeforeLastMarked M))"
using assms
unfolding lastMarked_def
by (induct M) (auto split: if_split_asm simp add: markedElementsAreElements)

lemma uniqImpliesPrefixBeforeLastMarkedIsPrefixBeforeLastMarked:
  assumes "markedElements M \<noteq> []" and "(lastMarked M) \<notin> set (elements M)"
  shows "prefixBeforeLastMarked M = prefixBeforeElement (lastMarked M) M"
using assms
unfolding lastMarked_def
proof (induct M)
  case Nil
  thus ?case
    by auto
next
  case (Cons a M')
  show ?case
  proof (cases "marked a \<and> (markedElements M') = []")
    case True
    thus ?thesis
      unfolding lastMarked_def
      by auto
  next
    case False
    hence "last (markedElements (a # M')) = last (markedElements M')"
      by auto
    thus ?thesis
      using Cons
      by (auto split: if_split_asm simp add: markedElementsAreElements)
  qed
qed

lemma markedElementsAreElementsBeforeLastDecisionAndLastDecision: 
  assumes "markedElements M \<noteq> []"
  shows "(markedElements M) = (markedElements (prefixBeforeLastMarked M)) @ [lastMarked M]"
using assms
unfolding lastMarked_def
by (induct M) (auto split: if_split_asm)

end
