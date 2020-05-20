(*
  File: Arrays_Ex.thy
  Author: Bohua Zhan
*)

section \<open>Arrays\<close>

theory Arrays_Ex
  imports "Auto2_HOL.Auto2_Main"
begin

text \<open>Basic examples for arrays.\<close>

subsection \<open>List swap\<close>

definition list_swap :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where [rewrite]:
  "list_swap xs i j = xs[i := xs ! j, j := xs ! i]"
setup \<open>register_wellform_data ("list_swap xs i j", ["i < length xs", "j < length xs"])\<close>
setup \<open>add_prfstep_check_req ("list_swap xs i j", "i < length xs \<and> j < length xs")\<close>

lemma list_swap_eval:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow>
   (list_swap xs i j) ! k = (if k = i then xs ! j else if k = j then xs ! i else xs ! k)" by auto2
setup \<open>add_rewrite_rule_cond @{thm list_swap_eval} [with_cond "?k \<noteq> ?i", with_cond "?k \<noteq> ?j"]\<close>

lemma list_swap_eval_triv [rewrite]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> (list_swap xs i j) ! i = xs ! j"
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> (list_swap xs i j) ! j = xs ! i" by auto2+

lemma length_list_swap [rewrite_arg]:
  "length (list_swap xs i j) = length xs" by auto2

lemma mset_list_swap [rewrite]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> mset (list_swap xs i j) = mset xs" by auto2

lemma set_list_swap [rewrite]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> set (list_swap xs i j) = set xs" by auto2
setup \<open>del_prfstep_thm @{thm list_swap_def}\<close>
setup \<open>add_rewrite_rule_back @{thm list_swap_def}\<close>

subsection \<open>Reverse\<close>

lemma rev_nth [rewrite]:
  "n < length xs \<Longrightarrow> rev xs ! n = xs ! (length xs - 1 - n)"
@proof @induct xs @qed

fun rev_swap :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "rev_swap xs i j = (if i < j then rev_swap (list_swap xs i j) (i + 1) (j - 1) else xs)"
setup \<open>register_wellform_data ("rev_swap xs i j", ["j < length xs"])\<close>
setup \<open>add_prfstep_check_req ("rev_swap xs i j", "j < length xs")\<close>

lemma rev_swap_length [rewrite_arg]:
  "j < length xs \<Longrightarrow> length (rev_swap xs i j) = length xs"
@proof @fun_induct "rev_swap xs i j" @unfold "rev_swap xs i j" @qed

lemma rev_swap_eval [rewrite]:
  "j < length xs \<Longrightarrow> (rev_swap xs i j) ! k =
    (if k < i then xs ! k else if k > j then xs ! k else xs ! (j - (k - i)))"
@proof @fun_induct "rev_swap xs i j" @unfold "rev_swap xs i j"
  @case "i < j" @with
    @case "k < i" @case "k > j" @have "j - (k - i) = j - k + i"
  @end
@qed

lemma rev_swap_is_rev [rewrite]:
  "length xs \<ge> 1 \<Longrightarrow> rev_swap xs 0 (length xs - 1) = rev xs" by auto2

subsection \<open>Copy one array to the beginning of another\<close>

fun array_copy :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "array_copy xs xs' 0 = xs'"
| "array_copy xs xs' (Suc n) = list_update (array_copy xs xs' n) n (xs ! n)"
setup \<open>fold add_rewrite_rule @{thms array_copy.simps}\<close>
setup \<open>register_wellform_data ("array_copy xs xs' n", ["n \<le> length xs", "n \<le> length xs'"])\<close>
setup \<open>add_prfstep_check_req ("array_copy xs xs' n", "n \<le> length xs \<and> n \<le> length xs'")\<close>

lemma array_copy_length [rewrite_arg]:
  "n \<le> length xs \<Longrightarrow> n \<le> length xs' \<Longrightarrow> length (array_copy xs xs' n) = length xs'"
@proof @induct n @qed

lemma array_copy_ind [rewrite]:
  "n \<le> length xs \<Longrightarrow> n \<le> length xs' \<Longrightarrow> k < n \<Longrightarrow> (array_copy xs xs' n) ! k = xs ! k"
@proof @induct n @qed

lemma array_copy_correct [rewrite]:
  "n \<le> length xs \<Longrightarrow> n \<le> length xs' \<Longrightarrow> take n (array_copy xs xs' n) = take n xs" by auto2

subsection \<open>Sublist\<close>

definition sublist :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where [rewrite]:
  "sublist l r xs = drop l (take r xs)"
setup \<open>register_wellform_data ("sublist l r xs", ["l \<le> r", "r \<le> length xs"])\<close>
setup \<open>add_prfstep_check_req ("sublist l r xs", "l \<le> r \<and> r \<le> length xs")\<close>

lemma length_sublist [rewrite_arg]:
  "r \<le> length xs \<Longrightarrow> length (sublist l r xs) = r - l" by auto2

lemma nth_sublist [rewrite]:
  "r \<le> length xs \<Longrightarrow> xs' = sublist l r xs \<Longrightarrow> i < length xs' \<Longrightarrow> xs' ! i = xs ! (i + l)" by auto2

lemma sublist_nil [rewrite]:
  "r \<le> length xs \<Longrightarrow> r \<le> l \<Longrightarrow> sublist l r xs = []" by auto2

lemma sublist_0 [rewrite]:
  "sublist 0 l xs = take l xs" by auto2

lemma sublist_drop [rewrite]:
  "sublist l r (drop n xs) = sublist (l + n) (r + n) xs" by auto2

setup \<open>del_prfstep_thm @{thm sublist_def}\<close>

lemma sublist_single [rewrite]:
  "l + 1 \<le> length xs \<Longrightarrow> sublist l (l + 1) xs = [xs ! l]"
@proof @have "length [xs ! l] = 1" @qed

lemma sublist_append [rewrite]:
  "l \<le> m \<Longrightarrow> m \<le> r \<Longrightarrow> r \<le> length xs \<Longrightarrow> sublist l m xs @ sublist m r xs = sublist l r xs"
@proof
  @let "xs1 = sublist l r xs" "xs2 = sublist l m xs" "xs3 = sublist m r xs"
  @have "length (xs2 @ xs3) = (r - m) + (m - l)"
  @have "\<forall>i<length xs1. xs1 ! i = (xs2 @ xs3) ! i" @with
    @case "i < length xs2"
    @have "i - length xs2 < length xs3"
  @end
@qed

lemma sublist_Cons [rewrite]:
  "r \<le> length xs \<Longrightarrow> l < r \<Longrightarrow> xs ! l # sublist (l + 1) r xs = sublist l r xs"
@proof
  @have "sublist l r xs = sublist l (l + 1) xs @ sublist (l + 1) r xs"
@qed

lemma sublist_equalityI:
  "i \<le> j \<Longrightarrow> j \<le> length xs \<Longrightarrow> length xs = length ys \<Longrightarrow>
   \<forall>k. i \<le> k \<longrightarrow> k < j \<longrightarrow> xs ! k = ys ! k \<Longrightarrow> sublist i j xs = sublist i j ys" by auto2
setup \<open>add_backward2_prfstep_cond @{thm sublist_equalityI} [with_filt (order_filter "xs" "ys")]\<close>

lemma set_sublist [resolve]:
  "j \<le> length xs \<Longrightarrow> x \<in> set (sublist i j xs) \<Longrightarrow> \<exists>k. k \<ge> i \<and> k < j \<and> x = xs ! k"
@proof
  @let "xs' = sublist i j xs"
  @obtain l where "l < length xs'" "xs' ! l = x"
@qed

lemma list_take_sublist_drop_eq [rewrite]:
  "l \<le> r \<Longrightarrow> r \<le> length xs \<Longrightarrow> take l xs @ sublist l r xs @ drop r xs = xs"
@proof
  @have "take l xs = sublist 0 l xs"
  @have "drop r xs = sublist r (length xs) xs"
@qed

subsection \<open>Updating a set of elements in an array\<close>

definition list_update_set :: "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list" where [rewrite]:
  "list_update_set S f xs = list (\<lambda>i. if S i then f i else xs ! i) (length xs)"

lemma list_update_set_length [rewrite_arg]:
  "length (list_update_set S f xs) = length xs" by auto2

lemma list_update_set_nth [rewrite]:
  "xs' = list_update_set S f xs \<Longrightarrow> i < length xs' \<Longrightarrow> xs' ! i = (if S i then f i else xs ! i)" by auto2
setup \<open>del_prfstep_thm @{thm list_update_set_def}\<close>

fun list_update_set_impl :: "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "list_update_set_impl S f xs 0 = xs"
| "list_update_set_impl S f xs (Suc k) =
   (let xs' = list_update_set_impl S f xs k in
      if S k then xs' [k := f k] else xs')"
setup \<open>fold add_rewrite_rule @{thms list_update_set_impl.simps}\<close>
setup \<open>register_wellform_data ("list_update_set_impl S f xs n", ["n \<le> length xs"])\<close>

lemma list_update_set_impl_ind [rewrite]:
  "n \<le> length xs \<Longrightarrow> list_update_set_impl S f xs n =
   list (\<lambda>i. if i < n then if S i then f i else xs ! i else xs ! i) (length xs)"
@proof @induct n arbitrary xs @qed

lemma list_update_set_impl_correct [rewrite]:
  "list_update_set_impl S f xs (length xs) = list_update_set S f xs" by auto2

end
