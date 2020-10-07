(* Authors: F. Maric, M. Spasic *)
theory Rel_Chain
  imports
    Simplex_Auxiliary
begin

definition
  rel_chain :: "'a list \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"
  where
    "rel_chain l r = (\<forall> k < length l - 1. (l ! k, l ! (k + 1)) \<in> r)"

lemma 
  rel_chain_Nil: "rel_chain [] r" and
  rel_chain_Cons: "rel_chain (x # xs) r = (if xs = [] then True else ((x, hd xs) \<in> r) \<and> rel_chain xs r)"
  by (auto simp add: rel_chain_def hd_conv_nth nth_Cons split: nat.split_asm nat.split)

lemma rel_chain_drop:
  "rel_chain l R ==> rel_chain (drop n l) R"
  unfolding rel_chain_def
  by simp

lemma rel_chain_take:
  "rel_chain l R ==> rel_chain (take n l) R"
  unfolding rel_chain_def
  by simp

lemma rel_chain_butlast:
  "rel_chain l R ==> rel_chain (butlast l) R"
  unfolding rel_chain_def
  by (auto simp add: butlast_nth)

lemma rel_chain_tl:
  "rel_chain l R ==> rel_chain (tl l) R"
  unfolding rel_chain_def
  by (cases "l = []") (auto simp add: tl_nth)

lemma rel_chain_append:
  assumes "rel_chain l R" "rel_chain l' R" "(last l, hd l') \<in> R"
  shows "rel_chain (l @ l') R"
  using assms
  by (induct l) (auto simp add: rel_chain_Cons split: if_splits)

lemma rel_chain_appendD:
  assumes "rel_chain (l @ l') R"
  shows "rel_chain l R" "rel_chain l' R" "l \<noteq> [] \<and> l' \<noteq> [] \<longrightarrow> (last l, hd l') \<in> R"
  using assms
  by (induct l) (auto simp add: rel_chain_Cons rel_chain_Nil split: if_splits)

lemma rtrancl_rel_chain:
  "(x, y) \<in> R\<^sup>* \<longleftrightarrow> (\<exists> l. l \<noteq> [] \<and> hd l = x \<and> last l = y \<and> rel_chain l R)" 
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (induct rule: converse_rtrancl_induct) (auto simp add: rel_chain_Cons)
next
  assume ?rhs
  then obtain l where "l \<noteq> []" "hd l = x" "last l = y" "rel_chain l R"
    by auto
  then show ?lhs
    by (induct l arbitrary: x) (auto simp add: rel_chain_Cons, force)
qed

lemma trancl_rel_chain:
  "(x, y) \<in> R\<^sup>+ \<longleftrightarrow> (\<exists> l. l \<noteq> [] \<and> length l > 1 \<and> hd l = x \<and> last l = y \<and> rel_chain l R)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain z where "(x, z) \<in> R" "(z, y) \<in> R\<^sup>*"
    by (auto dest: tranclD)
  then obtain l where  "l \<noteq> [] \<and> hd l = z \<and> last l = y \<and> rel_chain l R"
    by (auto simp add: rtrancl_rel_chain)
  then show ?rhs
    using \<open>(x, z) \<in> R\<close>
    by (rule_tac x="x # l" in exI) (auto simp add: rel_chain_Cons)
next
  assume ?rhs
  then obtain l where "1 < length l" "l \<noteq> []" "hd l = x" "last l = y" "rel_chain l R"
    by auto
  then obtain l' where
    "l' \<noteq> []" "l = x # l'" "(x, hd l') \<in> R" "rel_chain l' R"
    using \<open>1 < length l\<close>
    by (cases l) (auto simp add: rel_chain_Cons)
  then have "(x, hd l') \<in> R" "(hd l', y) \<in> R\<^sup>*"
    using \<open>last l = y\<close>
    by (auto simp add: rtrancl_rel_chain)
  then show ?lhs
    by auto
qed

lemma rel_chain_elems_rtrancl:
  assumes "rel_chain l R" "i \<le> j" "j < length l" 
  shows "(l ! i, l ! j) \<in> R\<^sup>*"
proof (cases "i = j")
  case True
  then show ?thesis
    by simp
next
  case False
  then have "i < j"
    using \<open>i \<le> j\<close>
    by simp
  then have "l \<noteq> []"
    using \<open>j < length l\<close>
    by auto

  let ?l = "drop i (take (j + 1) l)"

  have "?l \<noteq> []"
    using \<open>i < j\<close> \<open>j < length l\<close>
    by simp
  moreover
  have "hd ?l = l ! i"
    using \<open>?l \<noteq> []\<close> \<open>i < j\<close>
    by (auto simp add: hd_conv_nth)
  moreover
  have "last ?l = l ! j"
    using \<open>?l \<noteq> []\<close> \<open>l \<noteq> []\<close> \<open>i < j\<close> \<open>j < length l\<close>
    by (cases "length l = j + 1") (auto simp add: last_conv_nth min_def)
  moreover
  have "rel_chain ?l R"
    using \<open>rel_chain l R\<close>
    by (auto intro: rel_chain_drop rel_chain_take)
  ultimately
  show ?thesis
    by (subst rtrancl_rel_chain) blast
qed

lemma reorder_cyclic_list:
  assumes  "hd l = s" "last l = s" "length l > 2" "sl + 1 < length l" 
    "rel_chain l r"
  obtains l' :: "'a list"
  where "hd l' = l ! (sl + 1)" "last l' = l ! sl" "rel_chain l' r" "length l' = length l - 1"
    "\<forall> i. i + 1 < length l' \<longrightarrow> 
     (\<exists> j. j + 1 < length l \<and> l' ! i = l ! j \<and> l' ! (i + 1) = l ! (j + 1))"
proof-
  have "l \<noteq> []" 
    using \<open>length l > 2\<close>
    by auto

  have  "length (tl l) > 1" "tl l \<noteq> []"
    using \<open>length l > 2\<close> 
    by (auto simp add: length_0_conv[THEN sym])

  let ?l' = "if sl = 0 then 
                 tl l
             else
                 drop (sl + 1) l @ tl (take (sl + 1) l)"

  have "hd ?l' = l ! (sl + 1)"
  proof (cases "sl > 0", simp_all)
    show "hd (tl l) = l ! (Suc 0)"
      using \<open>tl l \<noteq> []\<close> \<open>l \<noteq> []\<close>
      by (simp add: hd_conv_nth tl_nth)
  next
    assume "0 < sl"
    show "hd (drop (Suc sl) l @ tl (take (Suc sl) l)) = l ! (Suc sl)"
      using \<open>sl + 1 < length l\<close> \<open>l \<noteq> []\<close>
      by (auto simp add: hd_append hd_drop_conv_nth)
  qed

  moreover

  have "last ?l' = l ! sl"
  proof (cases "sl > 0", simp_all)
    show "last (tl l) = l ! 0"
      using \<open>l \<noteq> []\<close> \<open>last l = s\<close> \<open>hd l = s\<close> \<open>length l > 2\<close>
      by (simp add: hd_conv_nth last_tl)
  next
    assume "sl > 0"
    then show "last (drop (Suc sl) l @ tl (take (Suc sl) l)) = l ! sl"
      using \<open>l \<noteq> []\<close> \<open>tl l \<noteq> []\<close> \<open>sl + 1 < length l\<close>
      by (auto simp add: last_append drop_Suc tl_take last_take_conv_nth tl_nth)
  qed

  moreover

  have "rel_chain ?l' r"
  proof (cases "sl = 0", simp_all)
    case True
    show "rel_chain (tl l) r"
      using \<open>rel_chain l r\<close>
      by (auto intro: rel_chain_tl)
  next
    assume "sl > 0"
    show  "rel_chain (drop (Suc sl) l @ tl (take (Suc sl) l)) r"
    proof (rule rel_chain_append)
      show "rel_chain (drop (Suc sl) l) r"
        using \<open>rel_chain l r\<close>
        by (auto intro: rel_chain_drop)
    next
      show "rel_chain (tl (take (Suc sl) l)) r"
        using \<open>rel_chain l r\<close>
        by (auto intro: rel_chain_tl rel_chain_take)
    next
      have "last (drop (sl + 1) l) = l ! 0"
        using \<open>sl + 1 < length l\<close> \<open>last l = s\<close> \<open>hd l = s\<close> \<open>l \<noteq> []\<close>
        by (auto simp add: hd_conv_nth)
      moreover
      have "sl > 0 \<longrightarrow> tl (take (sl + 1) l) \<noteq> []"
        using \<open>sl + 1 < length l\<close> \<open>l \<noteq> []\<close> \<open>tl l \<noteq> []\<close>
        by (auto simp add: take_Suc)
      then have "sl > 0 \<longrightarrow> hd (tl (take (sl + 1) l)) = l ! 1"
        using \<open>l \<noteq> []\<close>
        by (auto simp add: hd_conv_nth take_Suc tl_nth)
      ultimately
      show "(last (drop (Suc sl) l), hd (tl (take (Suc sl) l))) \<in> r"
        using \<open>rel_chain l r\<close> \<open>length l > 2\<close> \<open>sl > 0\<close>
        unfolding rel_chain_def
        by simp
    qed
  qed

  moreover

  have "length ?l' = length l - 1" 
    by auto

  ultimately

  obtain l' where *: "l' = ?l'" "hd l' = l ! (sl + 1)" "last l' = l ! sl" "rel_chain l' r" "length l' = length l - 1"
    by auto

  have l'_l: "\<forall> i. i + 1 < length l' \<longrightarrow> 
    (\<exists> j. j + 1 < length l \<and> l' ! i = l ! j \<and> l' ! (i + 1) = l ! (j + 1))"
  proof (safe)
    fix i
    assume "i + 1 < length l'"
    show "\<exists> j. j + 1 < length l \<and> l' ! i = l ! j \<and> l' ! (i + 1) = l ! (j + 1)"
    proof (cases "sl = 0")
      case True
      then show ?thesis
        using \<open>i + 1 < length l'\<close>
        using \<open>l' = ?l'\<close> \<open>l \<noteq> []\<close>
        by (force simp add: tl_nth)
    next
      case False
      then have "length l' = length l - 1"
        using \<open>l' = ?l'\<close> \<open>sl + 1 < length l\<close>
        by (simp add: min_def)
      then have "i + 2 < length l"
        using \<open>i + 1 < length l'\<close>
        by simp

      show ?thesis
      proof (cases "i + 1 < length (drop (sl + 1) l)")
        case True
        then show ?thesis
          using \<open>sl \<noteq> 0\<close> \<open>l' = ?l'\<close>
          by (force simp add: nth_append)
      next
        case False
        show ?thesis
        proof (cases "i + 1 > length (drop (sl + 1) l)")
          case True
          then have "i + 1 > length l - (sl + 1)"
            by auto
          have
            "l' ! i = l ! Suc (i - (length l - Suc sl))" 
            "l' ! (i + 1) = l ! Suc (Suc i - (length l - Suc sl))" 
            using \<open>i + 2 < length l\<close> \<open>sl + 1 < length l\<close>
            using \<open>i + 1 > length l - (sl + 1)\<close>
            using \<open>sl \<noteq> 0\<close> \<open>l' = ?l'\<close> \<open>l \<noteq> []\<close>
            using tl_nth[of "take (sl + 1) l" "i - (length l - Suc sl)"]
            using tl_nth[of "take (sl + 1) l" "Suc i - (length l - Suc sl)"]
            by (auto simp add: nth_append)

          have "Suc (i - (length l - Suc sl)) = i + sl + 1 - length l + 1"
            "Suc (Suc i - (length l - Suc sl)) = (i + sl + 1 - length l + 1) + 1"
            "i + sl + 1 - length l + 1 + 1 < length l"
            using \<open>sl + 1 < length l\<close>
            using \<open>i + 1 > length l - (sl + 1)\<close>
            using \<open>i + 2 < length l\<close>
            by auto

          have "l' ! i = l ! (i + sl + 1 - length l + 1)"
            using \<open>l' ! i = l ! Suc (i - (length l - Suc sl))\<close>
            by (subst \<open>Suc (i - (length l - Suc sl)) = i + sl + 1 - length l + 1\<close>[THEN sym])
          moreover
          have "l' ! (i + 1) = l ! ((i + sl + 1 - length l + 1) + 1)"
            using \<open>l' ! (i + 1) = l ! Suc (Suc i - (length l - Suc sl))\<close>
            by (subst \<open>Suc (Suc i - (length l - Suc sl)) = (i + sl + 1 - length l + 1) + 1\<close>[THEN sym])
          ultimately
          show ?thesis
            using \<open>i + sl + 1 - length l + 1 + 1 < length l\<close>
            by force
        next
          case False
          then have "i + 1 = length l - sl - 1"
            using \<open>\<not> i + 1 < length (drop (sl + 1) l)\<close>
            by simp
          then have "length l - 1 = sl + i + 1"
            by auto
          then have "l ! Suc (sl + i) = last l"
            using last_conv_nth[of l, THEN sym] \<open>l \<noteq> []\<close>
            by simp
          then show ?thesis
            using \<open>i + 1 = length l - sl - 1\<close>
            using \<open>l' = ?l'\<close> \<open>sl \<noteq> 0\<close> \<open>l \<noteq> []\<close>
            using tl_nth[of "take (sl + 1) l" 0]
            using \<open>hd l = s\<close> \<open>last l = s\<close>
            by (force simp add: nth_append hd_conv_nth)
        qed
      qed
    qed
  qed

  then show thesis
    using * l'_l
    apply -
    ..
qed

end
