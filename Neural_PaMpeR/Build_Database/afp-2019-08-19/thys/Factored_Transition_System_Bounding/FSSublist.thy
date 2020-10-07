(*
 * cf. planning/hol/sublistScript
 *)
theory FSSublist
  imports Main "HOL-Library.Sublist" ListUtils
begin

text \<open> This file is a port of the original HOL4 source file sublistScript.sml. \<close>

section "Factored System Sublist"
subsection "Sublist Characterization"

text \<open> We take a look at the characterization of sublists. As a precursor, we are replacing the 
original definition of `sublist` in HOL4 (sublistScript.sml:10) with the semantically equivalent
`subseq` of Isabelle/HOL's to be able to use the associated theorems and automation. 

In HOL4 `sublist` is defined as
  
  (sublist [] l1 = T) /\
  (sublist (h::t) [] = F) /\
  (sublist (x::l1) (y::l2) = (x = y) /\ sublist l1 l2 \/ sublist (x::l1) l2)

[Abdulaziz et al., HOL4 Definition 10, p.19]. Whereas `subseq` (Sublist.tyh:927) is defined as an 
abbrevation of `list\_emb` with the predicate @{term "\<lambda> x y. x = y"}, i.e. 

    @{term "subseq xs ys \<equiv> list_emb (=) xs ys"}

`list\_emb` itself is defined as an inductive predicate. However, an equivalent function definition
is provided in `list\_emb\_code` (Sublist.thy:784) which is very close to `sublist` in HOL4.

The correctness of the equivalence claim is shown below by the technical lemma 
`sublist\_HOL4\_equiv\_subseq` (where the HOL4 definition of `sublist` is renamed to `sublist\_HOL4`).
\<close>

\<comment> \<open>NOTE added definition\<close>
fun sublist_HOL4 where
  "sublist_HOL4 [] l1 = True"
| "(sublist_HOL4 (h # t) [] = False)"
| "(sublist_HOL4 (x # l1) (y # l2) = ((x = y) \<and> sublist_HOL4 l1 l2 \<or> sublist_HOL4 (x # l1) l2))"


\<comment> \<open>NOTE added lemma\<close>
lemma sublist_HOL4_equiv_subseq:
  fixes l1 l2
  shows "sublist_HOL4 l1 l2 \<longleftrightarrow> subseq l1 l2" 
proof - 
  have "subseq l1 l2 = list_emb (\<lambda>x y. x = y) l1 l2" 
    by blast
  moreover {
    have "sublist_HOL4 l1 l2 \<longleftrightarrow> list_emb (\<lambda>x y. x = y) l1 l2" 
    proof (induction rule: sublist_HOL4.induct)
      case (3 x l1 y l2)
      then show "sublist_HOL4 (x # l1) (y # l2) \<longleftrightarrow> list_emb (\<lambda>x y. x = y) (x # l1) (y # l2)" 
      proof (cases "x = y")
        case True
        then show ?thesis
          using "3.IH"(1, 2)
          by (metis sublist_HOL4.simps(3) subseq_Cons' subseq_Cons2_iff)
      next
        case False
        then show ?thesis
          using "3.IH"(2)
          by force
      qed 
    qed simp+
  }
  ultimately show ?thesis
    by blast
qed


text \<open> Likewise as with `sublist` and `subseq`, the HOL4 definition of `list\_frag` 
(list\_utilsScript.sml:207) has a an Isabelle/HOL counterpart in `sublist` (Sublist.thy:1124).

The equivalence claim is proven in the technical lemma `list\_frag\_HOL4\_equiv\_sublist`. Note that
`sublist` reverses the argument order of `list\_frag`. Other than that, both definitions are
syntactically identical. \<close>
definition list_frag_HOL4 where
  "list_frag_HOL4 l frag \<equiv> \<exists>pfx sfx. pfx @ frag @ sfx = l"

lemma list_frag_HOL4_equiv_sublist:
  shows "list_frag_HOL4 l l' \<longleftrightarrow> sublist l' l" 
  unfolding list_frag_HOL4_def sublist_def 
  by blast


text \<open> Given these equivalences, occurences of `sublist` and `list\_frag` in the original HOL4 
source are now always translated directly to `subseq` and `sublist` respectively.

The remainer of this subsection is concerned with characterizations of `sublist`/ `subseq`. \<close>


lemma sublist_EQNS: 
  "subseq [] l = True" 
  "subseq (h # t) [] = False" 
  by auto


lemma sublist_refl: "subseq l l" 
  by auto


lemma sublist_cons: 
  assumes "subseq l1 l2"
  shows "subseq l1 (h # l2)" 
  using assms
  by blast


lemma sublist_NIL: "subseq l1 [] = (l1 = [])" 
  by fastforce


lemma sublist_trans: 
  fixes l1 l2
  assumes "subseq l1 l2" "subseq l2 l3" 
  shows "subseq l1 l3"
  using assms 
  by force 


\<comment> \<open>NOTE can be solved directly with 'list\_emb\_length'.\<close>  
lemma sublist_length:
  fixes l l'
  assumes "subseq l l'"
  shows "length l \<le> length l'" 
  using assms list_emb_length
  by blast 


\<comment> \<open>NOTE can be solved directly with subseq\_Cons'.\<close>
lemma sublist_CONS1_E: 
  fixes l1 l2
  assumes "subseq (h # l1) l2"
  shows "subseq l1 l2"
  using assms subseq_Cons'
  by metis


lemma sublist_equal_lengths: 
  fixes l1 l2
  assumes "subseq l1 l2" "(length l1 = length l2)"
  shows "(l1 = l2)" 
  using assms subseq_same_length
  by blast


\<comment> \<open>NOTE can be solved directly with 'subseq\_order.antisym'.\<close>
lemma sublist_antisym: 
  assumes "subseq l1 l2" "subseq l2 l1"
  shows "(l1 = l2)"
  using assms subseq_order.antisym
  by blast


lemma sublist_append_back: 
  fixes l1 l2 
  shows "subseq l1 (l2 @ l1)" 
  by blast


\<comment> \<open>NOTE can be solved directly with 'subseq\_rev\_drop\_many'.\<close>
lemma sublist_snoc: 
  fixes l1 l2 
  assumes "subseq l1 l2"
  shows "subseq l1 (l2 @ [h])"
  using assms subseq_rev_drop_many 
  by blast


lemma sublist_append_front: 
  fixes l1 l2
  shows "subseq l1 (l1 @ l2)"
  by fast


lemma append_sublist_1: 
  assumes "subseq (l1 @ l2) l"
  shows "subseq l1 l \<and> subseq l2 l" 
  using assms sublist_append_back sublist_append_front sublist_trans 
  by blast 


\<comment> \<open>NOTE added lemma (eventually wasn't needed in the remaining proofs).\<close>
lemma sublist_prefix:  
  shows "subseq (h # l1) l2 \<Longrightarrow> \<exists>l2a l2b. l2 = l2a @ [h] @ l2b \<and> \<not>ListMem h l2a"
proof (induction l2 arbitrary: h l1)
  \<comment> \<open>NOTE l2 cannot be empty when @{term "(h # l1)"} isn't.\<close>
  case Nil
  have "\<not>(subseq (h # l1) [])"
    by simp 
  then show ?case 
    using Nil.prems
    by blast
next
  case (Cons a l2)
  then show ?case proof (cases "a = h")
    \<comment> \<open>NOTE If a = h then a trivial solution exists in l2a = [] and l2b = l2.\<close>
    case True
    then show "\<exists> l2a l2b. (Cons a l2) = l2a @ [h] @ l2b \<and> \<not>ListMem h l2a" 
      using ListMem_iff 
      by force
  next 
    case False
    have "subseq (h # l1) l2" 
      using Cons.prems False subseq_Cons2_neq
      by force
    then obtain l2a l2b where "l2 = l2a @ [h] @ l2b" "\<not>ListMem h l2a"
      using Cons.IH Cons.prems
      by meson
    moreover have "a # l2 = (a # l2a) @ [h] @ l2b" 
      using calculation(1)
      by simp
    moreover have "\<not>(ListMem h (a # l2a))" 
      using False calculation(2) ListMem.simps
      by fastforce
    ultimately show ?thesis 
      by blast
  qed
qed

\<comment> \<open>NOTE added lemma (eventually wasn't needed in the remaining proofs).\<close>
lemma sublist_skip: 
  fixes l1 l2 h l1'
  assumes "l1 = (h # l1')" "l2 = l2a @ [h] @ l2b" "subseq l1 l2" "\<not>(ListMem h l2a)"
  shows "subseq l1 (h # l2b)" 
  using assms
proof (induction l2a arbitrary: l1 l2 h l1')
  case Nil
  then have "l2 = h # l2b" 
    by fastforce
  then show ?case using Nil.prems(3)
    by blast
next
  case (Cons a l2a)
  have "a \<noteq> h" 
    using Cons.prems(4) ListMem.simps 
    by fast
  then have "subseq l1 (l2a @ [h] @ l2b)"
    using Cons.prems(1, 2, 3) subseq_Cons2_neq
    by force
  moreover have "\<not>ListMem h l2a" 
    using Cons.prems(4) insert
    by metis
  ultimately have "subseq l1 (h # l2b)"
    using Cons.IH Cons.prems
    by meson 
  then show ?case
    by simp
qed

\<comment> \<open>NOTE added lemma (eventually wasn't needed in the remaining proofs).\<close>
lemma sublist_split_trans:
  fixes l1 l2 h l1'
  assumes "l1 = (h # l1')" "l2 = l2a @ [h] @ l2b" "subseq l1 l2" "\<not>(ListMem h l2a)"
  shows "subseq l1' l2b"
proof -
  have "subseq (h # l1') (h # l2b)"
    using assms sublist_skip 
    by metis
  then show ?thesis
    using subseq_Cons2'
    by metis
qed

lemma sublist_cons_exists: 
  shows "
    subseq (h # l1) l2 
    \<longleftrightarrow> (\<exists>l2a l2b. (l2 = l2a @ [h] @ l2b) \<and> \<not>ListMem h l2a \<and> subseq l1 l2b)
  " 
proof -
  \<comment> \<open>NOTE show both directions of the equivalence in pure proof blocks.\<close>
  {
    have 
      "subseq (h # l1) l2 \<Longrightarrow> (\<exists>l2a l2b. (l2 = l2a @ [h] @ l2b) \<and> \<not>ListMem h l2a \<and> subseq l1 l2b)" 
    proof (induction l2 arbitrary: h l1)
      case (Cons a l2)
      show ?case 
      proof (cases "a = h")
        case True
          \<comment> \<open>NOTE This case has a trivial solution in '?l2a = []', '?l2b = l2'.\<close>
        let ?l2a="[]"
        have "(a # l2) = ?l2a @ [h] @ l2" 
          using True
          by auto
        moreover have "\<not>(ListMem h ?l2a)"
          using ListMem_iff
          by force
        moreover have "subseq l1 l2" 
          using Cons.prems True 
          by simp
        ultimately show ?thesis
          by blast
      next
        case False
        have 1: "subseq (h # l1) l2" 
          using Cons.prems False subseq_Cons2_neq
          by metis
        then obtain l2a l2b where "l2 = l2a @ [h] @ l2b" "\<not>ListMem h l2a"
          using Cons.IH Cons.prems
          by meson
        moreover have "a # l2 = (a # l2a) @ [h] @ l2b" 
          using calculation(1)
          by simp
        moreover have "\<not>(ListMem h (a # l2a))" 
          using False calculation(2) ListMem.simps
          by fastforce
        ultimately show ?thesis 
          using 1 sublist_split_trans
          by metis
      qed
    qed simp
  }
  moreover
  {
    assume "\<exists>l2a l2b. (l2 = l2a @ [h] @ l2b) \<and> \<not>ListMem h l2a \<and> subseq l1 l2b"
    then have  "subseq (h # l1) l2"
      by auto
  }
  ultimately show ?thesis
    by argo
qed


lemma sublist_append_exists: 
  fixes l1 l2 
  shows "subseq (l1 @ l2) l3 \<Longrightarrow> \<exists>l3a l3b. (l3 = l3a @ l3b) \<and> subseq l1 l3a \<and> subseq l2 l3b"
  using list_emb_appendD 
  by fast


\<comment> \<open>NOTE can be solved directly with 'list\_emb\_append\_mono'.\<close>
lemma sublist_append_both_I: 
  assumes "subseq a b" "subseq c d"
  shows "subseq (a @ c) (b @ d)"
  using assms list_emb_append_mono
  by blast


lemma sublist_append: 
  assumes "subseq l1 l1'" "subseq l2 l2'"
  shows "subseq (l1 @ l2) (l1' @ l2')"
  using assms sublist_append_both_I
  by blast


lemma sublist_append2: 
  assumes "subseq l1 l2"
  shows "subseq l1 (l2 @ l3)" 
  using assms sublist_append[of "l1" "l2" "[]" "l3"]
  by fast 


lemma append_sublist: 
  shows "subseq (l1 @ l2 @ l3) l \<Longrightarrow> subseq (l1 @ l3) l"
proof (induction l)
  case Nil
  then show ?case 
    using sublist_NIL
    by fastforce
next
  case (Cons a l)
  then show ?case 
  proof (cases l1)
    case Nil
    then show ?thesis
      using Cons.prems append_sublist_1 
      by auto
  next
    case (Cons a list)
    then show ?thesis
      using Cons.prems subseq_append' subseq_order.dual_order.trans
      by blast
  qed
qed


lemma sublist_subset: 
  assumes "subseq l1 l2"
  shows "set l1 \<subseteq> set l2" 
  using assms set_nths_subset subseq_conv_nths
  by metis


lemma sublist_filter: 
  fixes P l 
  shows "subseq (filter P l) l"
  using subseq_filter_left 
  by blast


lemma sublist_cons_2: 
  fixes l1 l2 h
  shows "(subseq (h # l1) (h # l2) \<longleftrightarrow> (subseq l1 l2))"
  by fastforce


lemma sublist_every: 
  fixes l1 l2 P
  assumes "(subseq l1 l2 \<and> list_all P l2)"
  shows "list_all P l1"
  by (metis (full_types) Ball_set assms list_emb_set)


lemma sublist_SING_MEM: "subseq [h] l \<longleftrightarrow> ListMem h l"
  using ListMem_iff subseq_singleton_left
  by metis


\<comment> \<open>NOTE renamed due to previous declaration of `sublist\_append\_exists\_2.\<close>
lemma sublist_append_exists_2: 
  fixes l1 l2 l3
  assumes "subseq (h # l1) l2"
  shows "(\<exists>l3 l4. (l2 = l3 @ [h] @ l4) \<and> (subseq l1 l4))"
  using assms sublist_cons_exists
  by metis


lemma sublist_append_4: 
  fixes l l1 l2 h
  assumes "(subseq (h # l) (l1 @ [h] @ l2))" "(list_all (\<lambda>x. \<not>(h = x)) l1)"
  shows "subseq l l2"
  using assms 
proof (induction l1)
qed auto


lemma sublist_append_5: 
  fixes l l1 l2 h
  assumes "(subseq (h # l) (l1 @ l2))" "(list_all (\<lambda>x. \<not>(h = x)) l1)"
  shows "subseq (h # l) l2"
  using assms
proof (induction l1)
qed auto


lemma sublist_append_6: 
  fixes l l1 l2 h
  assumes "(subseq (h # l) (l1 @ l2))" "(\<not>(ListMem h l1))"
  shows "subseq (h # l) l2"
  using assms 
proof (induction l1)
  case (Cons a l1)
  then show ?case
    by (simp add: ListMem_iff) 
qed simp


lemma sublist_MEM: 
  fixes h l1 l2 
  shows "subseq (h # l1) l2 \<Longrightarrow> ListMem h l2"
proof (induction l2)
next
  case (Cons a l2)
  then show ?case
    using elem insert subseq_Cons2_neq 
    by metis
qed simp


lemma sublist_cons_4: 
  fixes l h l'
  shows "subseq l l' \<Longrightarrow> subseq l (h # l')" 
  using sublist_cons
  by blast


subsection "Main Theorems"

theorem sublist_imp_len_filter_le: 
  fixes P l l'
  assumes "subseq l' l" 
  shows "length (filter P l') \<le> length (filter P l)"
  using assms
  by (simp add: sublist_length)


\<comment> \<open>TODO showcase (non-trivial proof translation/ obscurity).\<close>
theorem list_with_three_types_shorten_type2: 
  fixes P1 P2 P3 k1 f PProbs PProbl s l
  assumes "(PProbs s)" "(PProbl l)" 
    "(\<forall>l s. 
      (PProbs s)
      \<and> (PProbl l)
      \<and> (list_all P1 l) 
      \<longrightarrow> (\<exists>l'. 
          (f s l' = f s l) 
          \<and> (length (filter P2 l') \<le> k1)
          \<and> (length (filter P3 l') \<le> length (filter P3 l))
          \<and> (list_all P1 l')
          \<and> (subseq l' l)
      )
    )" 
    "(\<forall>s l1 l2. f (f s l1) l2 = f s (l1 @ l2))" 
    "(\<forall>s l. (PProbs s) \<and> (PProbl l) \<longrightarrow> (PProbs (f s l)))" 
    "(\<forall>l1 l2. (subseq l1 l2) \<and> (PProbl l2) \<longrightarrow> (PProbl l1))" 
    "(\<forall>l1 l2. PProbl (l1 @ l2) \<longleftrightarrow> (PProbl l1 \<and> PProbl l2))" 
  shows "(\<exists>l'. 
    (f s l' = f s l)
    \<and> (length (filter P3 l') \<le> length (filter P3 l)) 
    \<and> (\<forall>l''. 
      (sublist l'' l') \<and> (list_all P1 l'')
       \<longrightarrow> (length (filter P2 l'') \<le> k1)
    )
    \<and> (subseq l' l)
  )"
  using assms 
proof (induction "filter (\<lambda>x. \<not>P1 x) l" arbitrary: P1 P2 P3 k1 f PProbs PProbl s l)
  case Nil
  then have "list_all (\<lambda>x. P1 x) l" 
    using Nil(1) filter_empty_every_not[of "\<lambda>x. \<not>P1 x" l]
    by presburger
  then obtain l' where 1:
    "(f s l' = f s l)" "length (filter P2 l') \<le> k1" "length (filter P3 l') \<le> length (filter P3 l)" 
    "list_all P1 l'" "subseq l' l"
    using Nil.prems(1, 2, 3)
    by blast
  moreover {
    fix l''
    assume "sublist l'' l'" "list_all P1 l''"
    then have "subseq l'' l'"
      by blast
        \<comment> \<open>NOTE original proof uses `frag\_len\_filter\_le` which however requires the fact
      `sublist l' ?l`. Unfortunately, this could not be derived in Isabelle/HOL.\<close>
    then have "length (filter P2 l'') \<le> length (filter P2 l')" 
      using sublist_imp_len_filter_le
      by blast
    then have "length (filter P2 l'') \<le> k1"
      using 1
      by linarith
  }
  ultimately show ?case
    by blast
next
  case (Cons a x)
    \<comment> \<open>NOTE The proof of the induction step basically consists of construction a list 
    `?l'=l'' @ [a] @ l'''` where `l''` and `l'''` are lists obtained from certain specifications
    of the induction hypothesis.\<close>
  then obtain l1 l2 where 2: 
    "l = l1 @ a # l2" "(\<forall>u\<in>set l1. P1 u)" "\<not> P1 a \<and> x = [x\<leftarrow>l2 . \<not> P1 x]"
    using Cons(2) filter_eq_Cons_iff[of "\<lambda>x. \<not>P1 x"] 
    by metis
  then have 3: "PProbl l2" 
    using Cons.prems(2, 6) 2(1) sublist_append_back 
    by blast
      \<comment> \<open>NOTE Use the induction hypothesis to obtain a specific  `l'''`.\<close>
  {
    have "x = filter (\<lambda>x. \<not>P1 x) l2"
      using 2(3)
      by blast
    moreover have "PProbs (f (f s l1) [a])"
      using Cons.prems(1, 2, 5, 6, 7) 2(1) elem sublist_SING_MEM
      by metis
    moreover have "\<forall>l s. PProbs s \<and> PProbl l \<and> list_all P1 l \<longrightarrow> (\<exists>l'. 
      f s l' = f s l \<and> length (filter P2 l') \<le> k1 \<and> length (filter P3 l') \<le> length (filter P3 l)
      \<and> list_all P1 l' \<and> subseq l' l)"
      using Cons.prems(3)
      by blast
    moreover have "\<forall>s l1 l2. f (f s l1) l2 = f s (l1 @ l2)" 
      "\<forall>s l. PProbs s \<and> PProbl l \<longrightarrow> PProbs (f s l)" 
      "\<forall>l1 l2. subseq l1 l2 \<and> PProbl l2 \<longrightarrow> PProbl l1"
      "\<forall>l1 l2. PProbl (l1 @ l2) = (PProbl l1 \<and> PProbl l2)"
      using Cons.prems(4, 5, 6, 7)
      by blast+
    ultimately have "\<exists>l'. 
      f (f (f s l1) [a]) l' = f (f (f s l1) [a]) l2 \<and> length (filter P3 l') \<le> length (filter P3 l2)
      \<and> (\<forall>l''. sublist l'' l' \<and> list_all P1 l'' \<longrightarrow> length (filter P2 l'') \<le> k1) \<and> subseq l' l2" 
      using 3 Cons(1)[of P1 l2, where s="(f (f s l1) [a])"]
      by blast
  }
  then obtain l''' where 4:
    "f (f (f s l1) [a]) l''' = f (f (f s l1) [a]) l2" 
    "length (filter P3 l''') \<le> length (filter P3 l2)" 
    "(\<forall>l''. sublist l'' l''' \<and> list_all P1 l'' \<longrightarrow> length (filter P2 l'') \<le> k1) \<and> subseq l''' l2" 
    by blast
  then have "f s (l1 @ [a] @ l''') = f s (l1 @ [a] @ l2)" 
    using Cons.prems(4)
    by auto
  then have "subseq l''' l2"
    using 4(3) 
    by blast
      \<comment> \<open>NOTE Use the induction hypothesis to obtain a specific  `l''`.\<close>
  {
    have "\<forall>l s. 
        PProbs s \<and> PProbl l1 \<and> list_all P1 l1 
        \<longrightarrow> (\<exists>l''. 
          f s l'' = f s l1 \<and> length (filter P2 l'') \<le> k1 \<and> length (filter P3 l'') \<le> length (filter P3 l1)
          \<and> list_all P1 l'' \<and> subseq l'' l1)"
      using Cons.prems(3)
      by blast
    then have "\<exists>l''. 
        f s l'' = f s l1 \<and> length (filter P2 l'') \<le> k1 \<and> length (filter P3 l'') \<le> length (filter P3 l1)
        \<and> list_all P1 l'' \<and> subseq l'' l1"
      using Cons.prems(1, 2, 7) 2(1, 2) 
      by (metis Ball_set) 
  }

  then obtain l'' where 5:
    "f s l'' = f s l1" "length (filter P2 l'') \<le> k1" 
    "length (filter P3 l'') \<le> length (filter P3 l1)" "list_all P1 l'' \<and> subseq l'' l1"
    by blast
  text \<open> Proof the proposition by providing the witness @{term "l'=(l'' @ [a] @ l''')"}. \<close>
  let ?l'="(l'' @ [a] @ l''') " 
  {
    have "\<forall>s l1 l2. f (f s l1) l2 = f s (l1 @ l2)"
      by (simp add: Cons.prems(4))
    text \<open> Rewrite and show the goal.\<close>
    have "f s ?l' = f s (l1 @ [a] @ l2) \<longleftrightarrow> f s (l'' @ (a # l''')) = f s (l1 @ (a # l2))"
      by simp
    also have "\<dots> \<longleftrightarrow> f (f (f s l1) [a]) l''' = f (f (f s l1) [a]) l2"
      by (metis Cons.prems(4) \<open>f s l'' = f s l1\<close> calculation)
    finally have "f s ?l' = f s (l1 @ [a] @ l2)" 
      using 4(1)
      by blast
  }
  moreover 
  {
    have "
      length (filter P3 ?l') \<le> length (filter P3 (l1 @ [a] @ l2))
      \<longleftrightarrow> 
        (length (filter P3 l'') + 1 + length (filter P3 l''') 
        \<le> length (filter P3 l1) + 1 + length (filter P3 l2))"
      by force
    then have " 
      length (filter P3 ?l') \<le> length (filter P3 (l1 @ [a] @ l2))
      \<longleftrightarrow>
        length (filter P3 l'') + length (filter P3 l''') 
        \<le> length (filter P3 l1) + length (filter P3 l2)"
      by linarith
    then have "length (filter P3 ?l') \<le> length (filter P3 (l1 @ [a] @ l2))"
      using 4(2) \<open>length (filter P3 l'') \<le> length (filter P3 l1)\<close> 
        add_mono_thms_linordered_semiring(1) 
      by blast
  }
  moreover 
  {
    fix l''''
    assume P: "sublist l'''' ?l'" "list_all P1 l''''"
    have "list_all P1 l1"
      using 2(2) Ball_set
      by blast 
    consider (i) "sublist l'''' l''" | (ii) "sublist l'''' l'''"
      using P(1, 2) 2(3)  LIST_FRAG_DICHOTOMY_2
      by metis
    then have "length (filter P2 l'''') \<le> k1" 
    proof (cases)
      case i
      then have "length (filter P2 l'''') \<le> length (filter P2 l'')"
        using frag_len_filter_le
        by blast
      then show ?thesis 
        using 5(2) order_trans
        by blast
    next
      case ii
      then show ?thesis
        using 4(3) P(2)
        by blast
    qed
  }
    \<comment> \<open>NOTE the following two steps seem to be necessary to convince Isabelle that the split 
  @{term "l = l1 @ a # l2"} matches the split `(l1 @ [a] @ l2` and the previous proof steps therefore is 
  prove the goal.\<close>
  moreover {
    have "subseq ?l' (l1 @ [a] @ l2)"
      by (simp add: FSSublist.sublist_append \<open>list_all P1 l'' \<and> subseq l'' l1\<close> \<open>subseq l''' l2\<close>)
  }
  moreover have "l = l1 @ [a] @ l2"
    using 2 
    by force
  ultimately show ?case 
    by blast
qed


lemma isPREFIX_sublist: 
  fixes x y
  assumes "prefix x y"
  shows "subseq x y"
  using assms prefix_order.dual_order.antisym 
  by blast

end