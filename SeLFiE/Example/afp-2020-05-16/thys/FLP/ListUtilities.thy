section \<open>ListUtilities\<close>

text \<open>
  \file{ListUtilities} defines a (proper) prefix relation for lists, and proves some
  additional lemmata, mostly about lists.
\<close>

theory ListUtilities
imports Main
begin

subsection \<open>List Prefixes\<close>

inductive prefixList ::
  "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "prefixList [] (x # xs)"
| "prefixList xa xb \<Longrightarrow> prefixList (x # xa) (x # xb)"

lemma PrefixListHasTail:
fixes 
  l1 :: "'a list" and
  l2 :: "'a list"
assumes
  "prefixList l1 l2"
shows
  "\<exists> l . l2 = l1 @ l \<and> l \<noteq> []"
using assms by (induct rule: prefixList.induct, auto)

lemma PrefixListMonotonicity:
fixes 
  l1 :: "'a list" and
  l2 :: "'a list"
assumes
  "prefixList l1 l2"
shows
  "length l1 < length l2"
using assms by (induct rule: prefixList.induct, auto)

lemma TailIsPrefixList : 
fixes 
  l1 :: "'a list" and
  tail :: "'a list"
assumes "tail \<noteq> []"
shows "prefixList l1 (l1 @ tail)"
using assms
proof (induct l1, auto)
  have "\<exists> x xs . tail = x # xs"
    using assms by (metis neq_Nil_conv)
  thus "prefixList [] tail"
    using assms  by (metis prefixList.intros(1))
next
  fix a l1
  assume "prefixList l1 (l1 @ tail)"
  thus "prefixList (a # l1) (a # l1 @ tail)"
    by (metis prefixList.intros(2))
qed

lemma PrefixListTransitive:
fixes 
  l1 :: "'a list" and
  l2 :: "'a list" and
  l3 :: "'a list"
assumes
  "prefixList l1 l2"
  "prefixList l2 l3"
shows
  "prefixList l1 l3"
using assms
proof -
  from assms(1) have "\<exists> l12 . l2 = l1 @ l12 \<and> l12 \<noteq> []" 
    using PrefixListHasTail by auto
  then obtain l12 where Extend1: "l2 = l1 @ l12 \<and> l12 \<noteq> []" by blast
  from assms(2) have Extend2: "\<exists> l23 . l3 = l2 @ l23 \<and> l23 \<noteq> []" 
    using PrefixListHasTail by auto
  then obtain l23 where Extend2: "l3 = l2 @ l23 \<and> l23 \<noteq> []" by blast
  have "l3 = l1 @ (l12 @ l23) \<and> (l12 @ l23) \<noteq> []" 
    using Extend1 Extend2 by simp
  hence "\<exists> l . l3 = l1 @ l \<and> l \<noteq> []" by blast
  thus "prefixList l1 l3" using TailIsPrefixList by auto  
qed

subsection \<open>Lemmas for lists and nat predicates\<close>

lemma NatPredicateTippingPoint:
fixes 
  n2 Pr
assumes
  Min:     "0 < n2" and
  Pr0:     "Pr 0" and
  NotPrN2: "\<not>Pr n2"
shows
  "\<exists>n<n2. Pr n \<and> \<not>Pr (Suc n)"                       
proof (rule classical, simp)
  assume Asm: "\<forall>n. Pr n \<longrightarrow> n < n2 \<longrightarrow> Pr (Suc n)"
  have "\<And>n. n < n2 \<Longrightarrow> Pr n"
  proof-
    fix n
    show "n < n2 \<Longrightarrow> Pr n"
    by (induct n, auto simp add: Pr0 Asm)
  qed
  hence False
    using Asm[rule_format, of "n2 - 1"] Min NotPrN2 by auto
  thus ?thesis by auto
qed

lemma MinPredicate:
fixes 
  P::"nat \<Rightarrow> bool"
assumes
  "\<exists> n . P n"
shows 
  "(\<exists> n0 . (P n0) \<and> (\<forall> n' . (P n') \<longrightarrow> (n' \<ge> n0)))"
using assms
by (metis LeastI2_wellorder Suc_n_not_le_n)

text \<open>
  The lemma \isb{MinPredicate2} describes one case of \isb{MinPredicate}
  where the aforementioned smallest element is zero.
\<close>

lemma MinPredicate2:
fixes
  P::"nat \<Rightarrow> bool"
assumes
 "\<exists> n . P n"
shows
  "\<exists> n0 . (P n0) \<and> (n0 = 0 \<or> \<not> P (n0 - 1))"
using assms MinPredicate
by (metis add_diff_cancel_right' diff_is_0_eq diff_mult_distrib mult_eq_if)

text \<open>
  \isb{PredicatePairFunction} allows to obtain functions mapping two arguments
  to pairs from 4-ary predicates which are left-total on their first
  two arguments.
\<close>

lemma PredicatePairFunction: 
fixes
  P::"'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
assumes
  A1: "\<forall>x1 x2 . \<exists>y1 y2 . (P x1 x2 y1 y2)"
shows 
  "\<exists>f . \<forall>x1 x2 . \<exists>y1 y2 .
    (f x1 x2) = (y1, y2) 
    \<and> (P x1 x2 (fst (f x1 x2)) (snd (f x1 x2)))"
proof -
  define P' where "P' x y = P (fst x) (snd x) (fst y) (snd y)" for x y
  hence "\<forall>x. \<exists>y. P' x  y" using A1 by auto
  hence "\<exists>f. \<forall>x. P' x (f x)" by metis
  then obtain f where "\<forall>x. P' x (f x)" by blast
  moreover define f' where "f' x1 x2 = f (x1, x2)" for x1 x2
  ultimately have "\<forall>x. P' x (f' (fst x) (snd x))" by auto
  hence "\<exists>f'. \<forall>x. P' x (f' (fst x) (snd x))" by blast
  thus ?thesis using P'_def by auto
qed           

lemma PredicatePairFunctions2: 
fixes
  P::"'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
assumes
  A1: "\<forall>x1 x2 . \<exists>y1 y2 . (P x1 x2 y1 y2)"
obtains f1 f2  where
  "\<forall>x1 x2 . \<exists>y1 y2 .
    (f1 x1 x2) = y1 \<and> (f2 x1 x2) = y2 
    \<and> (P x1 x2 (f1 x1 x2) (f2 x1 x2))"
proof (cases thesis, auto)
  assume ass: "\<And>f1 f2. \<forall>x1 x2. P x1 x2 (f1 x1 x2) (f2 x1 x2) \<Longrightarrow> False"
  obtain f where F: "\<forall>x1 x2. \<exists>y1 y2. f x1 x2 = (y1, y2) \<and> P x1 x2 (fst (f x1 x2)) (snd (f x1 x2))"
    using PredicatePairFunction[OF A1] by blast
  define f1 where "f1 x1 x2 = fst (f x1 x2)" for x1 x2
  define f2 where "f2 x1 x2 = snd (f x1 x2)" for x1 x2
  show False
    using ass[of f1 f2] F unfolding f1_def f2_def by auto
qed

lemma PredicatePairFunctions2Inv: 
fixes
  P::"'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
assumes
  A1: "\<forall>x1 x2 . \<exists>y1 y2 . (P x1 x2 y1 y2)"
obtains f1 f2  where
  "\<forall>x1 x2 . (P x1 x2 (f1 x1 x2) (f2 x1 x2))"
using PredicatePairFunctions2[OF A1] by auto

lemma SmallerMultipleStepsWithLimit:
fixes
  k A limit
assumes
  "\<forall> n \<ge> limit . (A (Suc n)) < (A n)"
shows
  "\<forall> n \<ge> limit . (A (n + k)) \<le> (A n) - k"
proof(induct k,auto)
  fix n k
  assume IH: "\<forall>n\<ge>limit. A (n + k) \<le> A n - k" "limit \<le> n"
  hence "A (Suc (n + k)) < A (n + k)" using assms by simp 
  hence "A (Suc (n + k)) < A n - k" using IH by auto
  thus "A (Suc (n + k)) \<le> A n - Suc k" 
    by (metis Suc_lessI add_Suc_right add_diff_cancel_left' 
       less_diff_conv less_or_eq_imp_le add.commute)
qed

lemma PrefixSameOnLow:
fixes
  l1 l2
assumes
  "prefixList l1 l2"
shows
  "\<forall> index < length l1 . l1 ! index = l2 ! index"
using assms
proof(induct rule: prefixList.induct, auto)
  fix xa xb ::"'a list" and x index
  assume AssumpProof: "prefixList xa xb" 
        "\<forall>index < length xa. xa ! index = xb ! index"
        "prefixList l1 l2" "index < Suc (length xa)"
  show "(x # xa) ! index = (x # xb) ! index" using AssumpProof
  proof(cases "index = 0", auto)
  qed
qed

lemma KeepProperty:
fixes
  P Q low
assumes
  "\<forall> i \<ge> low . P i \<longrightarrow> (P (Suc i) \<and> Q i)" "P low"
shows
  "\<forall> i \<ge> low . Q i"
using assms
proof(clarify)
  fix i
  assume Assump:
    "\<forall>i\<ge>low. P i \<longrightarrow> P (Suc i) \<and> Q i"
    "P low"
    "low \<le> i"
  hence "\<forall>i\<ge>low. P i \<longrightarrow> P (Suc i)" by blast
  hence "\<forall> i \<ge> low . P i" using Assump(2) by (metis dec_induct)
  hence "P i" using Assump(3) by blast
  thus "Q i" using Assump by blast
qed

lemma ListLenDrop: 
fixes
  i la lb
assumes
  "i < length lb"
  "i \<ge> la"
shows
  "lb ! i \<in> set (drop la lb)" 
using assms
by (metis Cons_nth_drop_Suc in_set_member member_rec(1) 
       set_drop_subset_set_drop rev_subsetD)

lemma DropToShift:
fixes
  l i list
assumes
  "l + i < length list"
shows
  "(drop l list) ! i = list ! (l + i)"
using assms
by (induct l, auto)

lemma SetToIndex:
fixes
  a and liste::"'a list"
assumes
  AssumpSetToIndex: "a \<in> set liste"
shows
  "\<exists> index < length liste . a = liste ! index"
proof -
  have LenInduct:
    "\<And>xs. \<forall>ys. length ys < length xs \<longrightarrow> a \<in> set ys 
          \<longrightarrow> (\<exists>index<length ys. a = ys ! index) 
          \<Longrightarrow> a \<in> set xs \<longrightarrow> (\<exists>index<length xs. a = xs ! index)" 
  proof(auto)
    fix xs
    assume AssumpLengthInduction: 
      "\<forall>ys. length ys < length xs \<longrightarrow> a \<in> set ys 
      \<longrightarrow> (\<exists>index<length ys. a = ys ! index)" "a \<in> set xs"
    have "\<exists> x xs' . xs = x#xs'" using AssumpLengthInduction(2) 
      by (metis ListMem.cases ListMem_iff)
    then obtain x xs' where XSSplit: "xs = x#xs'" by blast
    hence "a \<in> insert x (set xs')" using set_simps AssumpLengthInduction 
      by simp
    hence "a = x \<or> a \<in> set xs'" by simp
    thus "\<exists>index<length xs. a = xs ! index"
    proof(cases "a = x",auto)
      show "\<exists>index<length xs. x = xs ! index" using XSSplit by auto
    next
      assume AssumpCases: "a \<in> set xs'" "a \<noteq> x"
      have "length xs' < length xs" using XSSplit by simp
      hence "\<exists>index<length xs'. a = xs' ! index" 
        using AssumpLengthInduction(1) AssumpCases(1) by simp
      thus "\<exists>index<length xs. a = xs ! index" using XSSplit by auto
    qed
  qed
  thus "\<exists> index < length liste . a = liste ! index" 
    using length_induct[of 
      "\<lambda>l. a \<in> set l \<longrightarrow> (\<exists> index < length l . a = l ! index)" "liste"] 
    AssumpSetToIndex by blast
qed

lemma DropToIndex:
fixes
  a::"'a" and l liste 
assumes
  AssumpDropToIndex: "a \<in> set (drop l liste)"
shows
  "\<exists> i \<ge> l . i < length liste \<and> a = liste ! i"
proof-
  have "\<exists> index < length (drop l liste) . a = (drop l liste) ! index"
    using AssumpDropToIndex SetToIndex[of "a" "drop l liste"] by blast
  then obtain index where Index: "index < length (drop l liste)" 
    "a = (drop l liste) ! index" by blast
  have "l + index < length liste" using Index(1) 
    by (metis length_drop less_diff_conv add.commute)
  hence "a = liste ! (l + index)" 
    using DropToShift[of "l" "index"] Index(2) by blast
  thus "\<exists>i\<ge>l. i < length liste \<and> a = liste ! i" 
    by (metis \<open>l + index < length liste\<close> le_add1)
qed

end
