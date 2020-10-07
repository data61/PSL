theory List_Aux
imports
  "List-Index.List_Index"
begin

section \<open>Auxiliary List Lemmas\<close>

lemma nth_rotate_conv_nth1_conv_nth:
  assumes "m < length xs"
  shows "rotate1 xs ! m = xs ! (Suc m mod length xs)"
  using assms
proof (induction xs arbitrary: m)
  case (Cons x xs)
  show ?case
  proof (cases "m < length xs")
    case False
    with Cons.prems have "m = length xs" by force
    then show ?thesis by (auto simp: nth_append)
  qed (auto simp: nth_append)
qed simp

lemma nth_rotate_conv_nth:
  assumes "m < length xs"
  shows "rotate n xs ! m = xs ! ((m + n) mod length xs)"
  using assms
proof (induction n arbitrary: m)
  case 0 then show ?case by simp
next
  case (Suc n)
  show ?case
  proof cases
    assume "m + 1 < length xs"
    with Suc show ?thesis using Suc by (auto simp: nth_rotate_conv_nth1_conv_nth)
  next
    assume "\<not>(m + 1 < length xs)"
    with Suc have "m + 1 = length xs" "0 < length xs" by auto
    moreover
    { have "Suc (m + n) mod length xs = (Suc m + n) mod length xs"
        by auto
      also have "\<dots> = n mod length xs" using \<open>m + 1 = _\<close> by simp
      finally have "Suc (m + n) mod length xs = n mod length xs" .}
    ultimately
    show ?thesis by (auto simp: nth_rotate_conv_nth1_conv_nth Suc.IH)
  qed
qed

lemma not_nil_if_in_set:
  assumes "x \<in> set xs" shows "xs \<noteq> []"
  using assms by auto

lemma length_fold_remove1_le:
 "length (fold remove1 ys xs) \<le> length xs"
proof (induct ys arbitrary: xs)
  case (Cons y ys)
  then have "length (fold remove1 ys (remove1 y xs)) \<le> length (remove1 y xs)" by auto
  also have "\<dots> \<le> length xs" by (auto simp: length_remove1)
  finally show ?case by simp
qed simp

lemma set_fold_remove1':
  assumes "x \<in> set xs - set ys" shows "x \<in> set (fold remove1 ys xs)"
  using assms by (induct ys arbitrary: xs) auto

lemma set_fold_remove1:
  "set (fold remove1 xs ys) \<subseteq> set ys"
  by (induct xs arbitrary: ys) (auto, metis notin_set_remove1 subsetCE)

lemma set_fold_remove1_distinct:
  assumes "distinct xs" shows "set (fold remove1 ys xs) = set xs - set ys"
  using assms by (induct ys arbitrary: xs) auto

lemma distinct_fold_remove1:
  assumes "distinct xs"
  shows "distinct (fold remove1 ys xs)"
  using assms by (induct ys arbitrary: xs) auto

end
