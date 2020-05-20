theory Find_First
imports
  "HOL-Library.Finite_Map"
  "List-Index.List_Index"
begin

fun find_first :: "'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
"find_first _ [] = None" |
"find_first x (y # ys) = (if x = y then Some 0 else map_option Suc (find_first x ys))"

lemma find_first_correct:
  assumes "find_first x xs = Some i"
  shows "i < length xs" "xs ! i = x" "x \<notin> set (take i xs)"
using assms
proof (induction xs arbitrary: i)
  case (Cons y ys)
  { case 1 with Cons show ?case by (cases "x = y") auto }
  { case 2 with Cons show ?case by (cases "x = y") auto }
  { case 3 with Cons show ?case by (cases "x = y") auto }
qed auto

lemma find_first_none: "x \<notin> set xs \<Longrightarrow> find_first x xs = None"
by (induct xs) auto

lemma find_first_some_strong:
  assumes "x \<in> set (take n xs)" "n \<le> length xs"
  obtains i where "find_first x xs = Some i" "i < n"
using assms
proof (induction xs arbitrary: thesis n)
  case (Cons y ys)
  show ?case
    proof (cases "x = y")
      case True
      show ?thesis
        proof (rule Cons.prems)
          show "find_first x (y # ys) = Some 0"
            unfolding \<open>x = y\<close> by simp
        next
          show "0 < n"
            using Cons by (metis length_pos_if_in_set length_take min.absorb2)
          qed
    next
      case False
      show ?thesis
        proof (rule Cons.IH)
          fix i
          assume "find_first x ys = Some i" "i < n - 1"
          with False have "find_first x (y # ys) = Some (Suc i)" "Suc i < n"
            using False by auto
          thus thesis
            using Cons by metis
        next
          show "x \<in> set (take (n - 1) ys)"
            using Cons False by (metis empty_iff list.set(1) set_ConsD take_Cons')
        next
          show "n - 1 \<le> length ys"
            using Cons by (metis One_nat_def le_diff_conv list.size(4))
        qed
    qed
qed simp

lemma find_first_some:
  assumes "x \<in> set xs"
  obtains i where "find_first x xs = Some i" "i < length xs"
using assms
by (metis order_refl take_all find_first_some_strong)

lemma find_first_some_index: "i < length xs \<Longrightarrow> distinct xs \<Longrightarrow> find_first (xs ! i) xs = Some i"
proof (induction xs arbitrary: i)
  case (Cons x xs)
  show ?case
    proof (cases "i = 0")
      case False
      have "find_first ((x # xs) ! i) (x # xs) = map_option Suc (Some (i - 1))"
        using Cons False by auto
      also have "\<dots> = Some i"
        using False by auto
      finally show ?thesis .
    qed simp
qed auto

lemma find_first_append:
  "find_first x (ys @ zs) =
    (case find_first x ys of None \<Rightarrow> map_option (\<lambda>i. i + length ys) (find_first x zs) | Some a \<Rightarrow> Some a)"
by (induct ys) (auto simp: option.map_comp comp_def map_option.identity split: option.splits)

lemma find_first_first:
  assumes "i < length xs" "x \<notin> set (take i xs)" "xs ! i = x"
  shows "find_first x xs = Some i"
proof -
  let ?ys = "take i xs"
  let ?zs = "drop i xs"

  have "?zs ! 0 = x"
    using assms by simp
  hence "find_first x ?zs = Some 0"
    using assms by (cases ?zs) auto
  moreover have "find_first x ?ys = None"
    using assms by (simp add: find_first_none)
  ultimately have "find_first x (?ys @ ?zs) = Some i"
    unfolding find_first_append
    using assms by simp
  thus ?thesis
    using assms by simp
qed

lemma find_first_prefix:
  assumes "find_first x xs = Some i" "i < n"
  shows "find_first x (take n xs) = Some i"
proof (rule find_first_first)
  show "i < length (take n xs)"
    using assms by (simp add: find_first_correct)
next
  have "x \<notin> set (take i xs)"
    using assms by (simp add: find_first_correct)
  with assms show "x \<notin> set (take i (take n xs))"
    by (simp add: min.absorb1)
next
  show "take n xs ! i = x"
    using assms by (simp add: find_first_correct)
qed

lemma find_first_later:
  assumes "i < length xs" "j < length xs" "i < j"
  assumes "xs ! i = x" "xs ! j = x"
  shows "find_first x xs \<noteq> Some j"
proof (cases "x \<in> set (take i xs)")
  case True
  then obtain k where "find_first x xs = Some k" "k < i"
    using assms by (auto elim: find_first_some_strong)
  thus ?thesis
    using assms by simp
next
  case False
  hence "find_first x xs = Some i"
    using assms by (simp add: find_first_first)
  thus ?thesis
    using assms by simp
qed

lemma find_first_in_map:
  assumes "length xs \<le> length ys" "find_first n xs = Some i"
  shows "fmlookup (fmap_of_list (zip xs ys)) n = Some (ys ! i)"
using assms proof (induction xs arbitrary: ys i)
  case (Cons x xs)
  then obtain y ys' where "ys = y # ys'"
    by (metis Skolem_list_nth le_0_eq length_greater_0_conv less_nat_zero_code list.set_cases listrel_Cons1 listrel_iff_nth nth_mem)
  with Cons show ?case
    by (cases "x = n") auto
qed auto

fun common_prefix where
"common_prefix (x # xs) (y # ys) = (if x = y then x # common_prefix xs ys else [])" |
"common_prefix _ _ = []"

lemma common_prefix_find:
  assumes "z \<in> set (common_prefix xs ys)"
  shows "find_first z xs = find_first z ys"
using assms
by (induct xs ys rule: common_prefix.induct) auto

lemma find_first_insert_nth_eq:
  assumes "n \<le> length xs" "x \<notin> set (take n xs)"
  shows "find_first x (insert_nth n x xs) = Some n"
using assms
  by (auto simp: find_first_append find_first_none split: option.splits)

lemma insert_nth_induct:
  fixes P :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
    and a0 :: "nat"
    and a1 :: "'a"
    and a2 :: "'a list"
  assumes "\<And>x xs. P 0 x xs"
    and "\<And>n x y ys. P n x ys \<Longrightarrow> P (Suc n) x (y # ys)"
    and "\<And>n x. P (Suc n) x []"
  shows "P a0 a1 a2"
using assms
apply induction_schema
apply pat_completeness
apply lexicographic_order
done

lemma find_first_insert_nth_neq:
  assumes "x \<noteq> y"
  shows "find_first x (insert_nth n y xs) = map_option (\<lambda>i. if i < n then i else Suc i) (find_first x xs)"
using assms
proof (induction n y xs rule: insert_nth_induct)
  case 2
  note insert_nth_take_drop[simp del]
  show ?case
    apply auto
    apply (subst 2)
    apply (rule 2)
    unfolding option.map_comp
    apply (rule option.map_cong0)
    by auto
qed auto

end