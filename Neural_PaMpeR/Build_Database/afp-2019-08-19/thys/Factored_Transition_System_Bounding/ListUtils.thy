theory ListUtils
  imports Main "HOL-Library.Sublist"
begin 

\<comment> \<open>TODO assure translations
  * 'sublist' --> 'subseq'
  * list\_frag l l' --> sublist l' l (switch operands!)\<close>

lemma len_ge_0: 
  fixes l
  shows "length l \<ge> 0" 
  by simp

lemma len_gt_pref_is_pref: 
  fixes l l1 l2
  assumes "(length l2 > length l1)" "(prefix l1 l)" "(prefix l2 l)"
  shows "(prefix l1 l2)"
  using assms proof (induction l2 arbitrary: l1 l)
  case Nil
  then have "\<not>(length [] > length l1)"
    by simp
  then show ?case 
    using Nil
    by blast
next
  case (Cons a l2)
  then show ?case proof(induction l1 arbitrary: l)
    case Nil
    then show ?case 
      using Nil_prefix
      by blast
  next
    case (Cons b l1)
    then show ?case proof(cases l)
      case Nil
      then have "\<not>(prefix (a # l2) l)"
        by simp
      then show ?thesis using Cons.prems(4)
        by simp
    next
      case (Cons c l)
      then have 1: "length l2 > length l1" 
        using Cons.prems(2)
        by fastforce
      then show ?thesis using Cons proof(cases l)
        case Nil
        then have "l1 = [c]" "l2 = [c]" 
          using Cons.prems(3, 4) local.Cons 1 
          by fastforce+
        then show ?thesis 
          using 1 
          by auto
      next
        case (Cons d l')
        {
          thm len_ge_0
          have "length l1 \<ge> 0" 
            by simp
          then have "length l2 > 0" 
            using 1 
            by force
          then have "l2 \<noteq> []" using 1
            by blast
        }
        then have "length (a # l1) \<le> length (b # l2)"
          using 1 le_eq_less_or_eq
          by simp
        then show ?thesis
          using Cons.prems(3, 4) prefix_length_prefix 
          by fastforce
      qed
    qed 
  qed
qed

lemma nempty_list_append_length_add: 
  fixes l1 l2 l3
  assumes "l2 \<noteq> []"
  shows "length (l1 @ l3) < length (l1 @ l2 @l3)"
  using assms
  by (induction l2) auto


lemma append_filter: 
  fixes f1 :: "'a \<Rightarrow> bool" and f2 as1 as2 and p :: "'a list"
  assumes "(as1 @ as2 = filter f1 (map f2 p))"
  shows "(\<exists>p_1 p_2. 
    (p_1 @ p_2 = p) 
    \<and> (as1 = filter f1 (map f2 p_1)) 
    \<and> (as2 = filter f1 (map f2 p_2))
  )"
  using assms
proof (induction p arbitrary: f1 f2 as1 as2)
  case Nil
  from Nil have 1: "as1 @ as2 = []"
    by force
  then have 2: "as1 = []" "as2 = []" 
    by blast+
  let ?p1="[]"
  let ?p2="[]"
  from 1 2 
  have "?p1 @ ?p2 = []" "as1 = (filter f1 (map f2 ?p1))" "as2 = (filter f1 (map f2 ?p2))"
    subgoal by blast
    subgoal using 2(1) by simp
    subgoal using 2(2) by simp
    done
  then show ?case 
    by fast
next
  case cons: (Cons a p)
  then show ?case 
  proof (cases "as1")
    case Nil
    from cons.prems Nil 
    have 1: "as2 = filter f1 (map f2 (a # p))" 
      by simp
    let ?p1="[]"
    let ?p2="a # p"
    have "?p1 @ ?p2 = a # p" "as1 = filter f1 (map f2 ?p1)" "as2 = filter f1 (map f2 ?p2)"
      subgoal by simp 
      subgoal using Nil by simp
      subgoal using 1 by auto
      done
    then show ?thesis 
      by blast
  next
    case (Cons a' p')
    then show ?thesis 
    proof (cases "\<not>f1 (f2 a)")
      case True
      hence "filter f1 (map f2 (a # p)) = filter f1 (map f2 p)"
        by fastforce
      hence "as1 @ as2 = filter f1 (map f2 p)" 
        using cons.prems 
        by argo
      then obtain p1 p2 where a:
        "p1 @ p2 = p" "as1 = filter f1 (map f2 p1)" "as2 = filter f1 (map f2 p2)" 
        using cons.IH 
        by meson
      let ?p1="a # p1"
      let ?p2="p2"
      have "?p1 @ ?p2 = a # p" "as1 = filter f1 (map f2 ?p1)" "as2 = filter f1 (map f2 ?p2)" 
        subgoal using a(1) by fastforce
        subgoal using True a(2) by auto
        subgoal using a(3) by blast
        done
      then show ?thesis 
        by blast
    next
      case False
      hence "filter f1 (map f2 (a # p)) = f2 a # filter f1 (map f2 p)"
        by fastforce
      then have 1: "a' = f2 a" "p' @ as2 = filter f1 (map f2 p)" "as1 = a' # p'" 
        using cons.prems Cons
        by fastforce+
      then obtain p1 p2 where 2:
        "p1 @ p2 = p" "p' = filter f1 (map f2 p1)" "as2 = filter f1 (map f2 p2)" 
        using cons.IH 
        by meson
      let ?p1="a # p1"
      let ?p2="p2"
      have "?p1 @ ?p2 = a # p" "as1 = filter f1 (map f2 ?p1)" "as2 = filter f1 (map f2 ?p2)"
        subgoal using 2(1) by simp
        subgoal using False 1(1, 3) 2(2) by force
        subgoal using 2(3) by blast
        done
      then show ?thesis
        by blast
    qed
  qed    
qed

\<comment> \<open>NOTE types of `f1` and `p` had to be fixed for `append\_eq\_as\_proj\_1`.\<close> 
lemma append_eq_as_proj_1: 
  fixes f1 :: "'a \<Rightarrow> bool" and f2 as1 as2 as3 and p :: "'a list"
  assumes "(as1 @ as2 @ as3 = filter f1 (map f2  p))"
  shows "(\<exists>p_1 p_2 p_3. 
    (p_1 @ p_2 @ p_3 = p) 
    \<and> (as1 = filter f1 (map f2 p_1)) 
    \<and> (as2 = filter f1 (map f2 p_2)) 
    \<and> (as3 = filter f1 (map f2 p_3))
  )"
proof -
  from assms
  obtain p_1 p_2 where 1: "(p_1 @ p_2 = p)" "(as1 = filter f1 (map f2 p_1))" 
    "(as2 @ as3 = filter f1 (map f2 p_2))" 
    using append_filter[of as1 "(as2 @ as3)"]
    by meson
  moreover from 1 
  obtain p_a p_b where "(p_a @ p_b = p_2)" "(as2 = filter f1 (map f2 p_a))"
    "(as3 = filter f1 (map f2 p_b))" 
    using append_filter[where p=p_2]
    by meson
  ultimately show ?thesis
    by blast
qed

lemma filter_empty_every_not: "\<And>P l. (filter (\<lambda>x. P x) l = []) = list_all (\<lambda>x. \<not>P x) l"
proof -
  fix P l
  show "(filter (\<lambda>x. P x) l = []) = list_all (\<lambda>x. \<not>P x) l" 
    apply(induction l)
     apply(auto)
    done
qed

\<comment> \<open>NOTE added lemma (listScript.sml:810).\<close>
lemma MEM_SPLIT:
  fixes x l
  assumes "\<not>ListMem x l" 
  shows "\<forall>l1 l2. l \<noteq> l1 @ [x] @ l2" 
proof -
  {
    assume C: "\<not>(\<forall>l1 l2. l \<noteq> l1 @ [x] @ l2)"
    then have "\<exists>l1 l2. l = l1 @ [x] @ l2"
      by blast
    then obtain l1 l2 where 1: "l = l1 @ [x] @ l2" 
      by blast
    from assms
    have 2: "(\<forall>xs. l \<noteq> x # xs) \<and> (\<forall>xs. (\<forall>y. l \<noteq> y # xs) \<or> \<not> ListMem x xs)"
      using ListMem_iff
      by fastforce
    then have False 
    proof (cases l1)
      case Nil
      let ?xs="l2"
      from 1 Nil have "l = [x] @ ?xs"
        by blast
      then show ?thesis 
        using 2
        by simp
    next
      case (Cons a list)
      {
        let ?y="a"
        let ?xs="list @ [x] @ l2"
        from 1 Cons have "l = ?y # ?xs"
          by simp
        moreover have "ListMem x ?xs"
          by (simp add: ListMem_iff)
        ultimately have "\<exists>xs. \<exists>y. l = y # xs \<and> ListMem x xs"
          by blast
        then have "\<not>(\<forall>xs. (\<forall>y. l \<noteq> y # xs) \<or> \<not> ListMem x xs)"
          by presburger
      }
      then show ?thesis 
        using 2
        by auto
    qed
  }
  then show ?thesis
    by blast
qed


\<comment> \<open>NOTE added lemma (listScript.sml:2784)\<close>
lemma APPEND_EQ_APPEND_MID:
  fixes l1 l2 m1 m2 e
  shows 
    "(l1 @ [e] @ l2 = m1 @ m2) 
      \<longleftrightarrow>
        (\<exists>l. (m1 = l1 @ [e] @ l) \<and> (l2 = l @ m2)) \<or>
        (\<exists>l. (l1 = m1 @ l) \<and> (m2 = l @ [e] @ l2))"
proof (induction "l1" arbitrary: m1)
  case Nil
  then show ?case
    by (simp; metis Cons_eq_append_conv)+
next
  case (Cons a l1)
  then show ?case
    by (cases m1; simp; blast)
qed

\<comment> \<open>NOTE variable `P` was removed (redundant).\<close>
lemma LIST_FRAG_DICHOTOMY:
  fixes l la x lb
  assumes "sublist l (la @ [x] @ lb)" "\<not>ListMem x l"
  shows "sublist l la \<or> sublist l lb"
proof -
  {
    from assms(1) 
    obtain pfx sfx where 1: "pfx @ l @ sfx = la @ [x] @ lb"
      unfolding sublist_def 
      by force
    from assms(2)
    have 2: "\<forall>l1 l2. l \<noteq> l1 @ [x] @ l2"
      using MEM_SPLIT[OF assms(2)]
      by blast
    from 1 
    consider (a) "(\<exists>lc. pfx = la @ [x] @ lc \<and> lb = lc @ l @ sfx)" 
      | (b) "(\<exists>lc. la = pfx @ lc \<and> l @ sfx = lc @ [x] @ lb)"
      using APPEND_EQ_APPEND_MID[of la x lb pfx "l @ sfx"] 
      by presburger
    then have "\<exists>pfx' sfx. (pfx' @ l @ sfx = la) \<or> (pfx'@  l @ sfx = lb)" 
    proof (cases)
      case a
        \<comment> \<open>NOTE `lc` is `l'` in original proof.\<close>
      then obtain lc where a: "pfx = la @ [x] @ lc" "lb = lc @ l @ sfx"
        by blast
      then show ?thesis
        by blast
    next
      case b
      then obtain lc where i: "la = pfx @ lc" "l @ sfx = lc @ [x] @ lb"
        by blast
      then show ?thesis
        using 2
        by (metis APPEND_EQ_APPEND_MID) 
    qed
  }
  then show ?thesis 
    unfolding sublist_def
    by blast
qed


lemma LIST_FRAG_DICHOTOMY_2:
  fixes l la x lb P
  assumes "sublist l (la @ [x] @ lb) " "\<not>P x" "list_all P l"
  shows "sublist l la \<or> sublist l lb"
proof -
  {
    assume "\<not>P x" "list_all P l" 
    then have "\<not>ListMem x l" 
    proof (induction l arbitrary: x P) 
      case Nil
      then show ?case 
        using ListMem_iff
        by force
    next
      case (Cons a l)
      {
        have "list_all P l"
          using Cons.prems(2) 
          by simp
        then have "\<not>ListMem x l"
          using Cons.prems(1) Cons.IH
          by blast
      }
      moreover {
        have "P a" 
          using Cons.prems(2)
          by simp
        then  have "a \<noteq> x" 
          using Cons.prems(1)
          by meson
      }
      ultimately show ?case
        using Cons.prems(1, 2) ListMem_iff list.pred_set
        by metis
    qed
  }
  then have "\<not>ListMem x l"
    using assms(2, 3) 
    by fast
  then show ?thesis 
    using assms(1) LIST_FRAG_DICHOTOMY
    by metis
qed

lemma frag_len_filter_le:
  fixes P l' l
  assumes "sublist l' l"
  shows "length (filter P l') \<le> length (filter P l)"
proof -
  obtain ps ss where "l = ps @ l' @ ss"
    using assms sublist_def 
    by blast
  then have 1:
    "length (filter P l) = length (filter P ps) + length (filter P l') + length (filter P ss)"
    by force 
  then have "length (filter P ps) \<ge> 0" "length (filter P ss) \<ge> 0" 
    by blast+ 
  then show ?thesis
    using 1
    by linarith
qed

end