(* Authors: F. Maric, M. Spasic *)
section \<open>Auxiliary Results\<close>
theory Simplex_Auxiliary
  imports 
    "HOL-Library.Permutation"
    "HOL-Library.Mapping"
begin

(* -------------------------------------------------------------------------- *)
(* MoreList *)
(* -------------------------------------------------------------------------- *)
lemma map_reindex:
  assumes "\<forall> i < length l. g (l ! i) = f i"
  shows "map f [0..<length l] = map g l"
  using assms
  by (induct l rule: rev_induct) (auto simp add: nth_append split: if_splits)

lemma map_parametrize_idx: 
  "map f l = map (\<lambda>i. f (l ! i)) [0..<length l]"
  by (induct l rule: rev_induct) (auto simp add: nth_append)

lemma last_tl:
  assumes "length l > 1"
  shows "last (tl l) = last l"
  using assms
  by (induct l) auto

lemma hd_tl:
  assumes "length l > 1"
  shows "hd (tl l) = l ! 1"
  using assms
  by (induct l) (auto simp add: hd_conv_nth)

lemma butlast_empty_conv_length:
  shows "(butlast l = []) = (length l \<le> 1)"
  by (induct l) (auto split: if_splits)

lemma butlast_nth:
  assumes "n + 1 < length l"
  shows "butlast l ! n = l ! n"
  using assms
  by (induct l rule: rev_induct) (auto simp add: nth_append)

lemma last_take_conv_nth:
  assumes "0 < n" "n \<le> length l"
  shows "last (take n l) = l ! (n - 1)"
  using assms
  by (cases "l = []") (auto simp add: last_conv_nth min_def)

lemma tl_nth:
  assumes "l \<noteq> []" 
  shows "tl l ! n = l ! (n + 1)"
  using assms
  by (induct l) auto

lemma interval_3split:
  assumes "i < n"
  shows "[0..<n] = [0..<i] @ [i] @ [i+1..<n]"
proof-
  have "[0..<n] = [0..<i + 1] @ [i + 1..<n]"
    using upt_add_eq_append[of 0 "i + 1" "n - i - 1"]
    using \<open>i < n\<close>
    by (auto simp del: upt_Suc)
  then show ?thesis
    by simp
qed

abbreviation "list_min l \<equiv> foldl min (hd l) (tl l)"
lemma list_min_Min[simp]: "l \<noteq> [] \<Longrightarrow> list_min l = Min (set l)"
proof (induct l rule: rev_induct)
  case (snoc a l')
  then show ?case
    by (cases "l' = []") (auto simp add: ac_simps)
qed simp

(* Minimal element of a list satisfying the given property *)

definition min_satisfying :: "(('a::linorder) \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option" where
  "min_satisfying P l \<equiv>
    let xs = filter P l in
    if xs = [] then None else Some (list_min xs)"

lemma min_satisfying_None:
  "min_satisfying P l = None \<longrightarrow> 
    (\<forall> x \<in> set l. \<not> P x)"
  unfolding min_satisfying_def Let_def
  by (simp add: filter_empty_conv)

lemma min_satisfying_Some: 
  "min_satisfying P l = Some x \<longrightarrow> 
      x \<in> set l \<and> P x \<and> (\<forall> x' \<in> set l. x' < x \<longrightarrow> \<not> P x')"
proof (safe)
  let ?xs = "filter P l"
  assume "min_satisfying P l = Some x"
  then have "set ?xs \<noteq> {}" "x = Min (set ?xs)"
    unfolding min_satisfying_def Let_def
    by (auto split: if_splits simp add: filter_empty_conv)
  then show "x \<in> set l" "P x" 
    using Min_in[of "set ?xs"]
    by simp_all
  fix x'
  assume "x' \<in> set l" "P x'" "x' < x"
  have "x' \<notin> set ?xs"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "x' \<ge> x"
      using \<open>x = Min (set ?xs)\<close>
      by simp
    then show False
      using \<open>x' < x\<close>
      by simp
  qed
  then show "False"
    using \<open>x' \<in> set l\<close> \<open>P x'\<close>
    by simp
qed

(* -------------------------------------------------------------------------- *)
(* MoreNat *)
(* -------------------------------------------------------------------------- *)

lemma min_element:
  fixes k :: nat
  assumes "\<exists> (m::nat). P m"
  shows "\<exists> mm. P mm \<and> (\<forall> m'. m' < mm \<longrightarrow> \<not> P m')"
proof-
  from assms obtain m where "P m"
    by auto
  show ?thesis
  proof (cases "\<forall>m'<m. \<not> P m'")
    case True
    then show ?thesis 
      using \<open>P m\<close>
      by auto
  next
    case False
    then show ?thesis
    proof (induct m)
      case 0
      then show ?case
        by auto
    next
      case (Suc m')
      then show ?case
        by (cases "\<not> (\<forall>m'a<m'. \<not> P m'a)") auto
    qed
  qed
qed

(* -------------------------------------------------------------------------- *)
(* MoreFun *)
(* -------------------------------------------------------------------------- *)

lemma finite_fun_args:
  assumes "finite A" "\<forall> a \<in> A. finite (B a)"
  shows "finite {f. (\<forall> a. if a \<in> A then f a \<in> B a else f a = f0 a)}" (is "finite (?F A)")
  using assms
proof (induct) 
  case empty
  have "?F {} = {\<lambda> x. f0 x}"
    by auto
  then show ?case
    by auto
next
  case (insert a A')
  then have "finite (?F A')"
    by auto
  let ?f = "\<lambda> f. {f'. (\<forall> a'. if a = a' then f' a \<in> B a else f' a' = f a')}"
  have "\<forall> f \<in> ?F A'. finite (?f f)"
  proof
    fix f
    assume "f \<in> ?F A'"
    then have "?f f = (\<lambda> b. f (a := b)) ` B a"
      by (force split: if_splits)
    then show "finite (?f f)"
      using \<open>\<forall>a\<in>insert a A'. finite (B a)\<close>
      by auto
  qed
  then have "finite (\<Union> (?f ` (?F A')))"
    using \<open>finite (?F A')\<close>
    by auto
  moreover
  have "?F (insert a A') = \<Union> (?f ` (?F A'))"
  proof
    show "?F (insert a A') \<subseteq> \<Union> (?f ` (?F A'))"
    proof
      fix f
      assume "f \<in> ?F (insert a A')"
      then have "f \<in> ?f (f (a := f0 a))" "f (a := f0 a) \<in> ?F A'"
        using \<open>a \<notin> A'\<close>
        by auto
      then show "f \<in> \<Union> (?f ` (?F A'))"
        by blast
    qed
  next
    show "\<Union> (?f ` (?F A')) \<subseteq> ?F (insert a A')"
    proof
      fix f
      assume "f \<in> \<Union> (?f ` (?F A'))"
      then obtain f0 where "f0 \<in> ?F A'" "f \<in> ?f f0"
        by auto
      then show "f \<in> ?F (insert a A')"
        using \<open>a \<notin> A'\<close>
        by (force split: if_splits)
    qed
  qed
  ultimately
  show ?case
    by simp
qed

(* -------------------------------------------------------------------------- *)
(* MoreMapping *)
(* -------------------------------------------------------------------------- *)

lemma foldl_mapping_update:
  assumes "X \<in> set l" "distinct (map f l)"
  shows "Mapping.lookup (foldl (\<lambda>m a. Mapping.update (f a) (g a) m) i l) (f X) = Some (g X)"
  using assms
proof(induct l rule:rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc h t)
  show ?case
  proof (cases "f h = f X")
    case True
    then show ?thesis using snoc by (auto simp: lookup_update)
  next
    case False
    show ?thesis by (simp add: lookup_update' False, rule snoc, insert False snoc, auto)
  qed
qed

end
