(*    Title:              SATSolverVerification/MoreList.thy
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

section\<open>MoreList\<close>

theory MoreList
imports Main "HOL-Library.Multiset"
begin

text\<open>Theory contains some additional lemmas and functions for the
@{term List} datatype. Warning: some of these notions are obsolete
because they already exist in {\em List.thy} in similiar form.\<close>

(*********************************************************)
(*               last and butlast                        *)
(*********************************************************)
subsection\<open>@{term "last"} and @{term "butlast"} - last element of list and elements before it\<close>
lemma listEqualsButlastAppendLast: 
  assumes "list \<noteq> []"
  shows "list = (butlast list) @ [last list]"
using assms
by (induct list) auto

lemma lastListInList [simp]: 
  assumes "list \<noteq> []"
  shows "last list \<in> set list"
using assms
by (induct list) auto

lemma butlastIsSubset: 
  shows "set (butlast list) \<subseteq> set list"
by (induct list) (auto split: if_split_asm)

lemma setListIsSetButlastAndLast: 
  shows "set list \<subseteq> set (butlast list) \<union> {last list}" 
by (induct list) auto

lemma butlastAppend: 
  shows "butlast (list1 @ list2) = (if list2 = [] then butlast list1 else (list1 @ butlast list2))"
by (induct list1) auto

(*********************************************************)
(*                   removeAll                           *)
(*********************************************************)
subsection\<open>@{term removeAll} - element removal\<close>

lemma removeAll_multiset:
  assumes "distinct a" "x \<in> set a"
  shows "mset a = {#x#} + mset (removeAll x a)"
using assms
proof (induct a)
  case (Cons y a')
  thus ?case
  proof (cases "x = y")
    case True
    with \<open>distinct (y # a')\<close> \<open>x \<in> set (y # a')\<close>
    have "\<not>  x \<in> set a'"
      by auto
    hence "removeAll x a' = a'"
      by (rule removeAll_id)
    with \<open>x = y\<close> show ?thesis
      by (simp add: union_commute)
  next
    case False
    with \<open>x \<in> set (y # a')\<close> 
    have "x \<in> set a'"
      by simp
    with \<open>distinct (y # a')\<close>
    have "x \<noteq> y" "distinct a'"
      by auto
    hence "mset a' = {#x#} + mset (removeAll x a')"
      using \<open>x \<in> set a'\<close>
      using Cons(1)
      by simp
    thus ?thesis
      using \<open>x \<noteq> y\<close>
      by (simp add: union_assoc)
  qed
qed simp

lemma removeAll_map:
  assumes "\<forall> x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y"
  shows "removeAll (f x) (map f a) = map f (removeAll x a)"
using assms
by (induct a arbitrary: x) auto

 
(*********************************************************)
(*                   uniq                                *)
(*********************************************************)
subsection\<open>@{term uniq} - no duplicate elements.\<close>
text\<open>@{term "(uniq list)"} holds iff there are no repeated elements
in a list.  Obsolete: same as @{term "distinct"} in {\em List.thy}.\<close>

primrec uniq :: "'a list => bool"
where
"uniq [] = True" |
"uniq (h#t) = (h \<notin> set t \<and> uniq t)"

lemma uniqDistinct:
"uniq l = distinct l"
by (induct l) auto

lemma uniqAppend: 
  assumes "uniq (l1 @ l2)" 
  shows "uniq l1" "uniq l2"
using assms
by (induct l1) auto

lemma uniqAppendIff: 
  "uniq (l1 @ l2) = (uniq l1 \<and> uniq l2 \<and> set l1 \<inter> set l2 = {})" (is "?lhs = ?rhs")
by (induct l1) auto

lemma uniqAppendElement: 
  assumes "uniq l" 
  shows "e \<notin> set l = uniq (l @ [e])"
using assms
by (induct l) (auto split: if_split_asm)

lemma uniqImpliesNotLastMemButlast:
  assumes "uniq l"
  shows "last l \<notin> set (butlast l)"
proof (cases "l = []")
  case True
  thus ?thesis
    using assms
    by simp
next
  case False
  hence "l = butlast l @ [last l]"
    by (rule listEqualsButlastAppendLast)
  moreover
  with \<open>uniq l\<close> 
  have "uniq (butlast l)"
    using uniqAppend[of "butlast l" "[last l]"]
    by simp
  ultimately
  show ?thesis
    using assms
    using uniqAppendElement[of "butlast l" "last l"]
    by simp
qed

lemma uniqButlastNotUniqListImpliesLastMemButlast: 
  assumes "uniq (butlast l)" "\<not> uniq l" 
  shows "last l \<in> set (butlast l)"
proof (cases "l = []")
  case True
  thus ?thesis
    using assms
    by auto
next
  case False
  hence "l = butlast l @ [(last l)]"
    by (rule listEqualsButlastAppendLast)
  thus ?thesis
    using assms
    using uniqAppendElement[of "butlast l" "last l"]
    by auto
qed

lemma uniqRemdups:
  shows "uniq (remdups x)"
by (induct x) auto

lemma uniqHeadTailSet:
  assumes "uniq l"
  shows "set (tl l) = (set l) - {hd l}"
using assms
by (induct l) auto

lemma uniqLengthEqCardSet:
assumes "uniq l"
shows "length l = card (set l)"
using assms
by (induct l) auto

lemma lengthGtOneTwoDistinctElements:
assumes 
  "uniq l" "length l > 1" "l \<noteq> []"
shows
  "\<exists> a1 a2. a1 \<in> set l \<and> a2 \<in> set l \<and> a1 \<noteq> a2"
proof-
  let ?a1 = "l ! 0"
  let ?a2 = "l ! 1"
  have "?a1 \<in> set l"
    using nth_mem[of "0" "l"]
    using assms
    by simp
  moreover
  have "?a2 \<in> set l"
    using nth_mem[of "1" "l"]
    using assms
    by simp
  moreover
  have "?a1 \<noteq> ?a2"
    using nth_eq_iff_index_eq[of "l" "0" "1"]
    using assms
    by (auto simp add: uniqDistinct)
  ultimately
  show ?thesis
    by auto
qed

(*********************************************************)
(*                   firstPos                            *)
(*********************************************************)
subsection \<open>@{term firstPos} - first position of an element\<close>
text\<open>@{term "firstPos"} returns the zero-based index of the first
  occurrence of an element int a list, or the length of the list if the
  element does not occur.\<close>

primrec firstPos :: "'a => 'a list => nat"
where
"firstPos a [] = 0" |
"firstPos a (h # t) = (if a = h then 0 else 1 + (firstPos a t))"

lemma firstPosEqualZero:
  shows "(firstPos a (m # M') = 0) = (a = m)"
by (induct M') auto

lemma firstPosLeLength: 
  assumes "a \<in> set l"
  shows "firstPos a l < length l"
using assms
by (induct l) auto

lemma firstPosAppend: 
  assumes "a \<in> set l" 
  shows "firstPos a l = firstPos a (l @ l')"
using assms
by (induct l) auto

lemma firstPosAppendNonMemberFirstMemberSecond: 
  assumes "a \<notin> set l1" and  "a \<in> set l2"
  shows "firstPos a (l1 @ l2) = length l1 + firstPos a l2"
using assms
by (induct l1) auto

lemma firstPosDomainForElements: 
  shows "(0 \<le> firstPos a l \<and> firstPos a l < length l) = (a \<in> set l)" (is "?lhs = ?rhs")
  by (induct l) auto

lemma firstPosEqual: 
  assumes "a \<in> set l" and "b \<in> set l" 
  shows "(firstPos a l = firstPos b l) = (a = b)" (is "?lhs = ?rhs")
proof-
  {
    assume "?lhs"
    hence "?rhs"
      using assms
    proof (induct l)
      case (Cons m l')
      {
        assume "a = m"
        have "b = m"
        proof-
          from \<open>a = m\<close> 
          have "firstPos a (m # l') = 0"
            by simp
          with Cons 
          have "firstPos b (m # l') = 0"
            by simp
          with \<open>b \<in> set (m # l')\<close> 
          have "firstPos b (m # l') = 0"
            by simp
          thus ?thesis
            using firstPosEqualZero[of "b" "m" "l'"]
            by simp
        qed
        with \<open>a = m\<close> 
        have ?case
          by simp
      }
      note * = this
      moreover
      {
        assume "b = m"
        have "a = m"
        proof-
          from \<open>b = m\<close> 
          have "firstPos b (m # l') = 0"
            by simp
          with Cons 
          have "firstPos a (m # l') = 0"
            by simp
          with \<open>a \<in> set (m # l')\<close> 
          have "firstPos a (m # l') = 0"
            by simp
          thus ?thesis
            using firstPosEqualZero[of "a" "m" "l'"]
            by simp
        qed
        with \<open>b = m\<close> 
        have ?case
          by simp
      }
      note ** = this
      moreover
      {
        assume Q: "a \<noteq> m" "b \<noteq> m"
        from Q \<open>a \<in> set (m # l')\<close>
        have "a \<in> set l'"
          by simp
        from Q \<open>b \<in> set (m # l')\<close>
        have "b \<in> set l'"
          by simp
        from \<open>a \<in> set l'\<close> \<open>b \<in> set l'\<close> Cons
        have "firstPos a l' = firstPos b l'"
          by (simp split: if_split_asm)
        with Cons 
        have ?case
          by (simp split: if_split_asm)
      }
      note *** = this
      moreover
      {
        have "a = m \<or> b = m \<or> a \<noteq> m \<and> b \<noteq> m"
          by auto
      }
      ultimately
      show ?thesis
      proof (cases "a = m")
        case True
        thus ?thesis
          by (rule *)
      next
        case False
        thus ?thesis
        proof (cases "b = m")
          case True
          thus ?thesis
            by (rule **)
        next
          case False
          with \<open>a \<noteq> m\<close> show ?thesis
            by (rule ***)
        qed
      qed
    qed simp
  } thus ?thesis
    by auto
qed

lemma firstPosLast:
  assumes "l \<noteq> []" "uniq l"
  shows "(firstPos x l = length l - 1) = (x = last l)"
using assms
by (induct l) auto


(*********************************************************)
(*                   precedes                            *)
(*********************************************************)
subsection\<open>@{term precedes} - ordering relation induced by @{term firstPos}\<close>
definition precedes :: "'a => 'a => 'a list => bool"
where
"precedes a b l == (a \<in> set l \<and> b \<in> set l \<and>  firstPos a l <= firstPos b l)"

lemma noElementsPrecedesFirstElement: 
  assumes "a \<noteq> b"
  shows "\<not> precedes a b (b # list)"
proof-
  {
    assume "precedes a b (b # list)"
    hence "a \<in> set (b # list)" "firstPos a (b # list) <= 0"
      unfolding precedes_def
      by (auto split: if_split_asm)
    hence  "firstPos a (b # list) = 0"
      by auto
    with \<open>a \<noteq> b\<close> 
    have False
      using firstPosEqualZero[of "a" "b" "list"]
      by simp
  }
  thus ?thesis
    by auto
qed

lemma lastPrecedesNoElement:
assumes "uniq l"
shows "\<not>(\<exists> a. a \<noteq> last l \<and> precedes (last l) a l)"
proof-
  {
    assume "\<not> ?thesis"
    then obtain "a"
      where "precedes (last l) a l" "a \<noteq> last l"
      by auto
    hence "a \<in> set l" "last l \<in> set l" "firstPos (last l) l \<le> firstPos a l"
      unfolding precedes_def
      by auto
    hence "length l - 1 \<le> firstPos a l"
      using firstPosLast[of "l" "last l"]
      using \<open>uniq l\<close>
      by force
    hence "firstPos a l = length l - 1"
      using firstPosDomainForElements[of "a" "l"]
      using \<open>a \<in> set l\<close>
      by auto
    hence "a = last l"
      using firstPosLast[of "l" "last l"]
      using \<open>a \<in> set l\<close> \<open>last l \<in> set l\<close>
      using \<open>uniq l\<close>
      using firstPosEqual[of "a" "l" "last l"]
      by force
    with \<open>a \<noteq> last l\<close>
    have False
      by simp
  }
  thus ?thesis
    by auto
qed

lemma precedesAppend: 
  assumes "precedes a b l" 
  shows "precedes a b (l @ l')"
proof-
  from \<open>precedes a b l\<close> 
  have "a \<in> set l" "b \<in> set l" "firstPos a l \<le> firstPos b l"
    unfolding precedes_def
    by (auto split: if_split_asm)
  thus ?thesis
    using firstPosAppend[of "a" "l" "l'"]
    using firstPosAppend[of "b" "l" "l'"]
    unfolding precedes_def
    by simp
qed

lemma precedesMemberHeadMemberTail: 
  assumes "a \<in> set l1" and "b \<notin> set l1" and "b \<in> set l2"
  shows "precedes a b (l1 @ l2)"
proof-
  from \<open>a \<in> set l1\<close> 
  have "firstPos a l1 < length l1"
    using firstPosLeLength [of "a" "l1"]
    by simp
  moreover
  from \<open>a \<in> set l1\<close> 
  have "firstPos a (l1 @ l2) = firstPos a l1"
    using firstPosAppend[of "a" "l1" "l2"]
    by simp
  moreover
  from \<open>b \<notin> set l1\<close> \<open>b \<in> set l2\<close>
  have "firstPos b (l1 @ l2) = length l1 + firstPos b l2"
    by (rule firstPosAppendNonMemberFirstMemberSecond)
  moreover
  have "firstPos b l2 \<ge> 0"
    by auto
  ultimately
  show ?thesis
    unfolding precedes_def
    using \<open>a \<in> set l1\<close> \<open>b \<in> set l2\<close>
    by simp
qed


lemma precedesReflexivity: 
  assumes "a \<in> set l"
  shows "precedes a a l"
using assms
unfolding precedes_def
by simp

lemma precedesTransitivity: 
  assumes 
  "precedes a b l" and "precedes b c l" 
  shows 
  "precedes a c l"
using assms
unfolding precedes_def
by auto

lemma precedesAntisymmetry: 
  assumes
  "a \<in> set l" and "b \<in> set l" and
  "precedes a b l" and "precedes b a l"
  shows
  "a = b"
proof-
  from assms
  have "firstPos a l = firstPos b l"
    unfolding precedes_def
    by auto
  thus ?thesis
    using firstPosEqual[of "a" "l" "b"]
    using assms
    by simp
qed

lemma precedesTotalOrder: 
  assumes "a \<in> set l" and "b \<in> set l"
  shows "a=b \<or> precedes a b l \<or> precedes b a l"
using assms
unfolding precedes_def
by auto

lemma precedesMap:
  assumes "precedes a b list" and "\<forall> x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y"
  shows "precedes (f a) (f b) (map f list)"
using assms
proof (induct list)
  case (Cons l list')
    {
      assume "a = l"
      have ?case
      proof-
        from \<open>a = l\<close> 
        have "firstPos (f a) (map f (l # list')) = 0"
          using firstPosEqualZero[of "f a" "f l" "map f list'"]
          by simp
        moreover
        from \<open>precedes a b (l # list')\<close> 
        have "b \<in> set (l # list')"
          unfolding precedes_def
          by simp
        hence "f b \<in> set (map f (l # list'))"
          by auto
        moreover
        hence "firstPos (f b) (map f (l # list')) \<ge>  0"
          by auto
        ultimately
        show ?thesis
          using \<open>a = l\<close> \<open>f b \<in> set (map f (l # list'))\<close>
          unfolding precedes_def
          by simp
      qed
    }
    moreover
    {
      assume "b = l"
      with \<open>precedes a b (l # list')\<close>
      have "a = l"
        using noElementsPrecedesFirstElement[of "a" "l" "list'"]
        by auto
      from \<open>a = l\<close> \<open>b = l\<close> 
      have ?case
        unfolding precedes_def
        by simp
    }
    moreover
    {
      assume "a \<noteq> l" "b \<noteq> l"
      with \<open>\<forall> x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y\<close>
      have "f a \<noteq> f l" "f b \<noteq> f l"
        by auto
      from \<open>precedes a b (l # list')\<close> 
      have "b \<in> set(l # list')" "a \<in> set(l # list')" "firstPos a (l # list') \<le> firstPos b (l # list')"
        unfolding precedes_def
        by auto
      with \<open>a \<noteq> l\<close> \<open>b \<noteq> l\<close> 
      have "a \<in> set list'" "b \<in> set list'" "firstPos a list' \<le> firstPos b list'"
        by auto
      hence "precedes a b list'"
        unfolding precedes_def
        by simp
      with Cons
      have "precedes (f a) (f b) (map f list')"
        by simp
      with \<open>f a \<noteq> f l\<close> \<open>f b \<noteq> f l\<close>
      have ?case
        unfolding precedes_def
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

lemma precedesFilter: 
  assumes "precedes a b list" and "f a" and "f b"
  shows "precedes a b (filter f list)"
using assms
proof(induct list)
  case (Cons l list')
  show ?case
  proof-
    from \<open>precedes a b (l # list')\<close> 
    have "a \<in> set(l # list')" "b \<in> set(l # list')" "firstPos a (l # list') \<le> firstPos b (l # list')"
      unfolding precedes_def
      by auto
    from \<open>f a\<close> \<open>a \<in> set(l # list')\<close> 
    have "a \<in> set(filter f (l # list'))"
      by auto
    moreover
    from \<open>f b\<close> \<open>b \<in> set(l # list')\<close> 
    have "b \<in> set(filter f (l # list'))"
      by auto
    moreover
    have "firstPos a (filter f (l # list')) \<le> firstPos b (filter f (l # list'))"
    proof- 
      {
        assume "a = l"
        with \<open>f a\<close> 
        have "firstPos a (filter f (l # list')) = 0"
          by auto
        with \<open>b \<in> set (filter f (l # list'))\<close> 
        have ?thesis
          by auto
      }
      moreover
      {
        assume "b = l"
        with \<open>precedes a b (l # list')\<close>
        have "a = b"
          using noElementsPrecedesFirstElement[of "a" "b" "list'"]
          by auto
        hence ?thesis
          by (simp add: precedesReflexivity)
      }
      moreover
      {
        assume "a \<noteq> l" "b \<noteq> l"
        with \<open>precedes a b (l # list')\<close> 
        have "firstPos a list' \<le> firstPos b list'"
          unfolding precedes_def
          by auto
        moreover
        from \<open>a \<noteq> l\<close> \<open>a \<in> set (l # list')\<close> 
        have "a \<in> set list'"
          by simp
        moreover
        from \<open>b \<noteq> l\<close> \<open>b \<in> set (l # list')\<close> 
        have "b \<in> set list'"
          by simp
        ultimately
        have "precedes a b list'"
          unfolding precedes_def
          by simp
        with \<open>f a\<close> \<open>f b\<close> Cons(1)
        have "precedes a b (filter f list')"
          by simp
        with \<open>a \<noteq> l\<close> \<open>b \<noteq> l\<close>
        have ?thesis
          unfolding precedes_def
          by auto
      }
      ultimately
      show ?thesis
        by blast
    qed
    ultimately
    show ?thesis
      unfolding precedes_def
      by simp
  qed
qed simp

definition
"precedesOrder list == {(a, b). precedes a b list \<and> a \<noteq> b}"

lemma transPrecedesOrder: 
  "trans (precedesOrder list)"
proof-
  {
    fix x y z
    assume "precedes x y list" "x \<noteq> y" "precedes y z list" "y \<noteq> z"
    hence "precedes x z list" "x \<noteq> z"
      using precedesTransitivity[of "x" "y" "list" "z"]
      using firstPosEqual[of "y" "list" "z"]
      unfolding precedes_def
      by auto
  }
  thus ?thesis
    unfolding trans_def
    unfolding precedesOrder_def
    by blast
qed
    

lemma wellFoundedPrecedesOrder:
  shows "wf (precedesOrder list)"
unfolding wf_eq_minimal
proof-
  show "\<forall>Q a. a:Q \<longrightarrow> (\<exists> aMin \<in> Q. \<forall> a'. (a', aMin) \<in> precedesOrder list \<longrightarrow> a' \<notin> Q)"
  proof-
    {
      fix a :: "'a" and Q::"'a set"
      assume "a \<in> Q"
      let ?listQ = "filter (\<lambda> x. x \<in> Q) list"
      have "\<exists> aMin \<in> Q. \<forall> a'. (a', aMin) \<in> precedesOrder list \<longrightarrow> a' \<notin> Q"
      proof (cases "?listQ = []")
        case True
        let ?aMin = a
        have "\<forall> a'. (a', ?aMin) \<in> precedesOrder list \<longrightarrow> a' \<notin> Q"
        proof-
          {
            fix a'
            assume "(a', ?aMin) \<in> precedesOrder list"
            hence "a \<in> set list"
              unfolding precedesOrder_def
              unfolding precedes_def
              by simp
            with \<open>a \<in> Q\<close>
            have "a \<in> set ?listQ"
              by (induct list) auto
            with \<open>?listQ = []\<close> 
            have "False"
              by simp
            hence "a' \<notin> Q"
              by simp
          }
          thus ?thesis
            by simp
        qed
        with \<open>a \<in> Q\<close> obtain aMin where "aMin \<in> Q" "\<forall> a'. (a', aMin) \<in> precedesOrder list \<longrightarrow> a' \<notin> Q"
          by auto
        thus ?thesis
          by auto
      next
        case False
        let ?aMin = "hd ?listQ"
        from False 
        have "?aMin \<in> Q"
          by (induct list) auto
        have "\<forall> a'. (a', ?aMin) \<in> precedesOrder list \<longrightarrow> a' \<notin> Q"
        proof
          fix a'
          {
            assume "(a', ?aMin) \<in> precedesOrder list"
            hence "a' \<in> set list" "precedes a' ?aMin list" "a' \<noteq> ?aMin"
              unfolding precedesOrder_def
              unfolding precedes_def
              by auto
            have "a' \<notin> Q"
            proof-
              {
                assume "a' \<in> Q"
                with \<open>?aMin \<in> Q\<close> \<open>precedes a' ?aMin list\<close>
                have "precedes a' ?aMin ?listQ"
                    using precedesFilter[of "a'" "?aMin" "list" "\<lambda> x. x \<in> Q"]
                    by blast
                from \<open>a' \<noteq> ?aMin\<close> 
                have "\<not> precedes a' (hd ?listQ) (hd ?listQ # tl ?listQ)"
                  by (rule noElementsPrecedesFirstElement)
                with False \<open>precedes a' ?aMin ?listQ\<close>
                have "False"
                  by auto
              }
              thus ?thesis
                by auto
            qed
          } thus "(a', ?aMin) \<in> precedesOrder list \<longrightarrow> a' \<notin> Q"
            by simp
        qed
        with \<open>?aMin \<in> Q\<close>
        show ?thesis
          ..
      qed
    }
    thus ?thesis
      by simp
  qed
qed


(*********************************************************)
(*                   prefix                              *)
(*********************************************************)
subsection\<open>@{term isPrefix} - prefixes of list.\<close>
text\<open>Check if a list is a prefix of another list. Obsolete: similiar
notion is defined in {\em List\_prefixes.thy}.\<close>

definition
  isPrefix :: "'a list => 'a list => bool"
  where "isPrefix p t = (\<exists> s. p @ s = t)"

lemma prefixIsSubset:
  assumes "isPrefix p l"
  shows "set p \<subseteq> set l"
using assms
unfolding isPrefix_def
by auto

lemma uniqListImpliesUniqPrefix:
assumes "isPrefix p l" and "uniq l"
shows "uniq p"
proof-
  from \<open>isPrefix p l\<close> obtain s
    where "p @ s = l"
    unfolding isPrefix_def
    by auto
  with \<open>uniq l\<close>
  show ?thesis
    using uniqAppend[of "p" "s"]
    by simp
qed

lemma firstPosPrefixElement: 
  assumes "isPrefix p l" and "a \<in> set p"
  shows "firstPos a p = firstPos a l"
proof-
  from \<open>isPrefix p l\<close> obtain s
    where "p @ s = l"
    unfolding isPrefix_def
    by auto
  with \<open>a \<in> set p\<close> 
  show ?thesis
    using firstPosAppend[of "a" "p" "s"]
    by simp
qed

lemma laterInPrefixRetainsPrecedes: 
  assumes 
  "isPrefix p l" and "precedes a b l" and "b \<in> set p"
  shows 
  "precedes a b p"
proof-
  from \<open>isPrefix p l\<close> obtain s
    where "p @ s = l"
    unfolding isPrefix_def
    by auto
  from \<open>precedes a b l\<close> 
  have "a \<in> set l" "b \<in> set l" "firstPos a l \<le> firstPos b l"
    unfolding precedes_def
    by (auto split: if_split_asm)

  from \<open>p @ s = l\<close> \<open>b \<in> set p\<close> 
  have "firstPos b l = firstPos b p"
    using firstPosAppend [of "b" "p" "s"]
    by simp

  show ?thesis
  proof (cases "a \<in> set p")
    case True
    from \<open>p @ s = l\<close> \<open>a \<in> set p\<close> 
    have "firstPos a l = firstPos a p"
      using firstPosAppend [of "a" "p" "s"]
      by simp

    from \<open>firstPos a l = firstPos a p\<close> \<open>firstPos b l = firstPos b p\<close> \<open>firstPos a l \<le> firstPos b l\<close>
    \<open>a \<in> set p\<close> \<open>b \<in> set p\<close>
    show ?thesis
      unfolding precedes_def
      by simp
  next
    case False
    from \<open>a \<notin> set p\<close> \<open>a \<in> set l\<close> \<open>p @ s = l\<close>
    have "a \<in> set s"
      by auto
    with \<open>a \<notin> set p\<close> \<open>p @ s = l\<close>
    have "firstPos a l = length p + firstPos a s"
      using firstPosAppendNonMemberFirstMemberSecond[of "a" "p" "s"]
      by simp
    moreover
    from \<open>b \<in> set p\<close> 
    have "firstPos b p < length p"
      by (rule firstPosLeLength)
    ultimately
    show ?thesis
      using \<open>firstPos b l = firstPos b p\<close> \<open>firstPos a l \<le> firstPos b l\<close>
      by simp
  qed
qed

(*********************************************************)
(*                       List diff                       *)
(*********************************************************)
subsection\<open>@{term "list_diff"} - the set difference operation on two lists.\<close>

primrec list_diff :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
"list_diff x [] = x" |
"list_diff x (y#ys) = list_diff (removeAll y x) ys"

lemma [simp]: 
  shows "list_diff [] y = []"
by (induct y) auto

lemma [simp]: 
  shows "list_diff (x # xs) y = (if x \<in> set y then list_diff xs y else x # list_diff xs y)"
proof (induct y arbitrary: xs)
  case (Cons y ys)
  thus ?case
  proof (cases "x = y")
    case True
    thus ?thesis
      by simp
  next
    case False
    thus ?thesis
    proof (cases "x \<in> set ys")
      case True
      thus ?thesis
        using Cons
        by simp
    next
      case False
      thus ?thesis
        using Cons
        by simp
    qed
  qed
qed simp

lemma listDiffIff:
  shows "(x \<in> set a \<and> x \<notin> set b) = (x \<in> set (list_diff a b))"
by (induct a) auto

lemma listDiffDoubleRemoveAll: 
  assumes "x \<in> set a"
  shows "list_diff b a = list_diff b (x # a)"
using assms
by (induct b) auto

lemma removeAllListDiff[simp]:
  shows "removeAll x (list_diff a b) = list_diff (removeAll x a) b"
by (induct a) auto

lemma listDiffRemoveAllNonMember:
  assumes "x \<notin> set a"
  shows "list_diff a b = list_diff a (removeAll x b)"
using assms
proof (induct b arbitrary: a)
  case (Cons y b')
  from \<open>x \<notin> set a\<close> 
  have "x \<notin> set (removeAll y a)"
    by auto
  thus ?case
  proof (cases "x = y")
    case False
    thus ?thesis
      using Cons(2)
      using Cons(1)[of "removeAll y a"]
      using \<open>x \<notin> set (removeAll y a)\<close>
      by auto
  next
    case True
    thus ?thesis
      using Cons(1)[of "removeAll y a"]
      using \<open>x \<notin> set a\<close>
      using \<open>x \<notin> set (removeAll y a)\<close>
      by auto
  qed
qed simp

lemma listDiffMap: 
  assumes "\<forall> x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y"
  shows "map f (list_diff a b) = list_diff (map f a) (map f b)"
using assms
by (induct b arbitrary: a) (auto simp add: removeAll_map)

(*********************************************************)
(*                       Remdups                         *)
(*********************************************************)
subsection\<open>@{term remdups} - removing duplicates\<close>
lemma remdupsRemoveAllCommute[simp]:
  shows "remdups (removeAll a list) = removeAll a (remdups list)"
by (induct list) auto

lemma remdupsAppend: 
  shows "remdups (a @ b) = remdups (list_diff a b) @ remdups b"
proof (induct a)
  case (Cons x a')
  thus ?case
    using listDiffIff[of "x" "a'" "b"]
    by auto
qed simp

lemma remdupsAppendSet: 
  shows "set (remdups (a @ b)) = set (remdups a @ remdups (list_diff b a))"
proof (induct a)
  case Nil
  thus ?case
    by auto
next
  case (Cons x a')
  thus ?case
  proof (cases "x \<in> set a'")
    case True
    thus ?thesis
      using Cons
      using listDiffDoubleRemoveAll[of "x" "a'" "b"]
      by simp
  next
    case False
    thus ?thesis
    proof (cases "x \<in> set b")
      case True
      show ?thesis
      proof-
        have "set (remdups (x # a') @ remdups (list_diff b (x # a'))) = 
          set (x # remdups a' @ remdups (list_diff b (x # a')))"
          using \<open>x \<notin> set a'\<close>
          by auto
        also have "\<dots> = set (x # remdups a' @ remdups (list_diff (removeAll x b) a'))"
          by auto
        also have "\<dots> = set (x # remdups a' @ remdups (removeAll x (list_diff b a')))"
          by simp
        also have "\<dots> = set (remdups a' @ x # remdups (removeAll x (list_diff b a')))"
          by simp
        also have "\<dots> = set (remdups a' @ x # removeAll x (remdups (list_diff b a')))"
          by (simp only: remdupsRemoveAllCommute)
        also have "\<dots> = set (remdups a') \<union> set (x # removeAll x (remdups (list_diff b a')))"
          by simp
        also have "\<dots> = set (remdups a') \<union> {x} \<union> set (removeAll x (remdups (list_diff b a')))"
          by auto
        also have "\<dots> = set (remdups a') \<union> set (remdups (list_diff b a'))"
        proof-
          from \<open>x \<notin> set a'\<close> \<open>x \<in> set b\<close>
          have "x \<in> set (list_diff b a')"
            using listDiffIff[of "x" "b" "a'"]
            by simp
          hence "x \<in> set (remdups (list_diff b a'))"
            by auto
          thus ?thesis
            by auto
        qed
        also have "\<dots> = set (remdups (a' @ b))"
          using Cons(1)
          by simp
        also have "\<dots> = set (remdups ((x # a') @ b))"
          using \<open>x \<in> set b\<close>
          by simp
        finally show ?thesis
          by simp
      qed
    next
      case False
      thus ?thesis
      proof-
        have "set (remdups (x # a') @ remdups (list_diff b (x # a'))) = 
          set (x # (remdups a') @ remdups (list_diff b (x # a')))"
          using \<open>x \<notin> set a'\<close>
          by auto
        also have "\<dots> = set (x # remdups a' @ remdups (list_diff (removeAll x b) a'))"
          by auto
        also have "\<dots> = set (x # remdups a' @ remdups (list_diff b a'))"
          using \<open>x \<notin> set b\<close>
          by auto
        also have "\<dots> = {x} \<union> set (remdups (a' @ b))"
          using Cons(1)
          by simp
        also have "\<dots> = set (remdups ((x # a') @ b))"
          by auto
        finally show ?thesis
          by simp
      qed
    qed
  qed
qed

lemma remdupsAppendMultiSet: 
  shows "mset (remdups (a @ b)) = mset (remdups a @ remdups (list_diff b a))"
proof (induct a)
  case Nil
  thus ?case
    by auto
next
  case (Cons x a')
  thus ?case
  proof (cases "x \<in> set a'")
    case True
    thus ?thesis
      using Cons
      using listDiffDoubleRemoveAll[of "x" "a'" "b"]
      by simp
    next
    case False
    thus ?thesis
    proof (cases "x \<in> set b")
      case True
      show ?thesis
      proof-
        have "mset (remdups (x # a') @ remdups (list_diff b (x # a'))) = 
          mset (x # remdups a' @ remdups (list_diff b (x # a')))"
        proof-
          have "remdups (x # a') = x # remdups a'"
            using \<open>x \<notin> set a'\<close>
            by auto
          thus ?thesis
            by simp
        qed
        also have "\<dots> = mset (x # remdups a' @ remdups (list_diff (removeAll x b) a'))"
          by auto
        also have "\<dots> = mset (x # remdups a' @ remdups (removeAll x (list_diff b a')))"
          by simp
        also have "\<dots> = mset (remdups a' @ x # remdups (removeAll x (list_diff b a')))"
          by (simp add: union_assoc)
        also have "\<dots> = mset (remdups a' @ x # removeAll x (remdups (list_diff b a')))"
          by (simp only: remdupsRemoveAllCommute)
        also have "\<dots> = mset (remdups a') + mset (x # removeAll x (remdups (list_diff b a')))"
          by simp
        also have "\<dots> = mset (remdups a') + {#x#} + mset (removeAll x (remdups (list_diff b a')))"
          by simp
        also have "\<dots> = mset (remdups a') + mset (remdups (list_diff b a'))"
        proof-
          from \<open>x \<notin> set a'\<close> \<open>x \<in> set b\<close>
          have "x \<in> set (list_diff b a')"
            using listDiffIff[of "x" "b" "a'"]
            by simp
          hence "x \<in> set (remdups (list_diff b a'))"
            by auto
          thus ?thesis
            using removeAll_multiset[of "remdups (list_diff b a')" "x"]
            by (simp add: union_assoc)
        qed
        also have "\<dots> = mset (remdups (a' @ b))"
          using Cons(1)
          by simp
        also have "\<dots> = mset (remdups ((x # a') @ b))"
          using \<open>x \<in> set b\<close>
          by simp
        finally show ?thesis
          by simp
      qed
    next
      case False
      thus ?thesis
      proof-
        have "mset (remdups (x # a') @ remdups (list_diff b (x # a'))) = 
          mset (x # remdups a' @ remdups (list_diff b (x # a')))"
        proof-
          have "remdups (x # a') = x # remdups a'"
            using \<open>x \<notin> set a'\<close>
            by auto
          thus ?thesis
            by simp
        qed
        also have "\<dots> = mset (x # remdups a' @ remdups (list_diff (removeAll x b) a'))"
          by auto
        also have "\<dots> = mset (x # remdups a' @ remdups (list_diff b a'))"
          using \<open>x \<notin> set b\<close>
          using removeAll_id[of "x" "b"]
          by simp
        also have "\<dots> = {#x#} + mset (remdups (a' @ b))"
          using Cons(1)
          by (simp add: union_commute)
        also have "\<dots> = mset (remdups ((x # a') @ b))"
          using \<open>x \<notin> set a'\<close> \<open>x \<notin> set b\<close>
          by (auto simp add: union_commute)
        finally show ?thesis
          by simp
      qed
    qed
  qed
qed
 
lemma remdupsListDiff:
"remdups (list_diff a b) = list_diff (remdups a) (remdups b)"
proof(induct a)
  case Nil
  thus ?case
    by simp
next
  case (Cons x a')
  thus ?case
    using listDiffIff[of "x" "a'" "b"]
    by auto
qed

(*********************************************************)
(*                       Multiset                        *)
(*********************************************************)

(* Repetition of lemmas from Multiset.thy -
   neccessary for r which I do not know how to represent as order instance. *)

definition
"multiset_le a b r == a = b \<or> (a, b) \<in> mult r"

lemma multisetEmptyLeI:
  "multiset_le {#} a r"
unfolding multiset_le_def
using one_step_implies_mult[of "a" "{#}" r "{#}"]
by auto

lemma multisetUnionLessMono2:
shows
  "trans r \<Longrightarrow> (b1, b2) \<in> mult r \<Longrightarrow> (a + b1, a + b2) \<in> mult r"
unfolding mult_def
apply (erule trancl_induct)
apply (blast intro: mult1_union transI)
apply (blast intro: mult1_union transI trancl_trans)
done


lemma multisetUnionLessMono1:
shows
  "trans r \<Longrightarrow> (a1, a2) \<in> mult r \<Longrightarrow> (a1 + b, a2 + b) \<in> mult r"
  by (metis multisetUnionLessMono2 union_commute)


lemma multisetUnionLeMono2:
assumes
  "trans r"
  "multiset_le b1 b2 r"
shows
  "multiset_le (a + b1) (a + b2) r"
using assms
unfolding multiset_le_def
using multisetUnionLessMono2[of "r" "b1" "b2" "a"]
by auto

lemma multisetUnionLeMono1:
assumes
  "trans r"
  "multiset_le a1 a2 r"
shows
  "multiset_le (a1 + b) (a2 + b) r"
using assms
unfolding multiset_le_def
using multisetUnionLessMono1[of "r" "a1" "a2" "b"]
by auto

lemma multisetLeTrans:
assumes
  "trans r"
  "multiset_le x y r"
  "multiset_le y z r"
shows
  "multiset_le x z r"
using assms
unfolding multiset_le_def
unfolding mult_def
by (blast intro: trancl_trans)


lemma multisetUnionLeMono:
assumes
  "trans r"
  "multiset_le a1 a2 r"
  "multiset_le b1 b2 r"
shows
  "multiset_le (a1 + b1) (a2 + b2) r"
using assms
using multisetUnionLeMono1[of "r" "a1" "a2" "b1"]
using multisetUnionLeMono2[of "r" "b1" "b2" "a2"]
using multisetLeTrans[of "r" "a1 + b1" "a2 + b1" "a2 + b2"]
by simp

lemma multisetLeListDiff:
assumes
  "trans r"
shows 
  "multiset_le (mset (list_diff a b)) (mset a) r"
proof (induct a)
  case Nil
  thus ?case
    unfolding multiset_le_def
    by simp
next
  case (Cons x a')
  thus ?case
    using assms
    using multisetEmptyLeI[of "{#x#}" "r"]
    using multisetUnionLeMono[of "r" "mset (list_diff a' b)" "mset a'" "{#}" "{#x#}"]
    using multisetUnionLeMono1[of "r" "mset (list_diff a' b)" "mset a'" "{#x#}"]
    by auto
qed

(*********************************************************)
(*                       Levi                            *)
(*********************************************************)
subsection\<open>Levi's lemma\<close>

text\<open>Obsolete: these two lemmas are already proved as @{term
append_eq_append_conv2} and @{term append_eq_Cons_conv}.\<close>

lemma FullLevi: 
  shows "(x @ y = z @ w) = 
                (x = z \<and> y = w \<or> 
                (\<exists> t. z @ t = x \<and> t @ y = w) \<or> 
                (\<exists> t. x @ t = z \<and> t @ w = y))" (is "?lhs = ?rhs")
proof
  assume "?rhs"
  thus "?lhs"
    by auto
next
  assume "?lhs"
  thus "?rhs"
  proof (induct x arbitrary: z)
    case (Cons a x')
    show ?case
    proof (cases "z = []")
      case True
      with \<open>(a # x') @ y = z @ w\<close>
      obtain t where "z @ t = a # x'" "t @ y = w"
        by auto
      thus ?thesis
        by auto
    next
      case False
      then obtain b and z' where "z = b # z'"
        by (auto simp add: neq_Nil_conv)
      with \<open>(a # x') @ y = z @ w\<close>
      have "x' @ y = z' @ w" "a = b"
        by auto
      with Cons(1)[of "z'"]
      have "x' = z' \<and> y = w \<or> (\<exists>t. z' @ t = x' \<and> t @ y = w) \<or> (\<exists>t. x' @ t = z' \<and> t @ w = y)"
        by simp
      with \<open>a = b\<close> \<open>z = b # z'\<close> 
      show ?thesis
        by auto
    qed
  qed simp
qed

lemma SimpleLevi:
  shows "(p @ s = a # list) = 
             ( p = [] \<and> s = a # list \<or> 
              (\<exists> t. p = a # t \<and> t @ s = list))"
by (induct p) auto

subsection\<open>Single element lists\<close>
lemma lengthOneCharacterisation:
  shows "(length l = 1) = (l = [hd l])"
by (induct l) auto

lemma lengthOneImpliesOnlyElement:
  assumes "length l = 1" and "a : set l"
  shows "\<forall> a'. a' : set l \<longrightarrow> a' = a"
proof (cases l) 
  case (Cons literal' clause')
  with assms 
  show ?thesis 
    by auto
qed simp


end
