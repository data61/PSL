(*
  File: Lists_Thms.thy
  Author: Bohua Zhan

  Setup for proof steps related to lists.
*)

section \<open>Setup for lists\<close>

theory Lists_Thms
  imports Set_Thms
begin

subsection \<open>Definition of lists\<close>

setup \<open>add_resolve_prfstep @{thm list.distinct(2)}\<close>
setup \<open>add_forward_prfstep (equiv_forward_th @{thm list.simps(1)})\<close>
setup \<open>fold add_rewrite_rule @{thms List.list.sel}\<close>
setup \<open>add_rewrite_rule @{thm list.collapse}\<close>
setup \<open>add_var_induct_rule @{thm list.induct}\<close>

subsection \<open>Length\<close>

setup \<open>add_rewrite_rule @{thm List.list.size(3)}\<close>
lemma length_one [rewrite]: "length [x] = 1" by simp
lemma length_Cons [rewrite]: "length (a # b) = length b + 1" by simp
lemma length_snoc [rewrite]: "length (xs @ [x]) = length xs + 1" by auto
lemma length_zero_is_nil [forward]: "length xs = 0 \<Longrightarrow> xs = []" by simp
lemma length_gt_zero [forward]: "length xs > 0 \<Longrightarrow> xs \<noteq> []" by simp

subsection \<open>Append\<close>

setup \<open>add_rewrite_rule @{thm List.length_append}\<close>
setup \<open>add_rewrite_rule_cond @{thm List.append.simps(2)} [with_cond "?xs \<noteq> []"]\<close>
setup \<open>add_rewrite_rule @{thm List.hd_append2}\<close>
lemma append_is_empty [forward]: "xs @ ys = [] \<Longrightarrow> xs = [] \<and> ys = []" by simp

lemma cons_to_append [rewrite_back]: "a # b = [a] @ b" by simp

ML_file \<open>list_ac.ML\<close>
ML_file \<open>list_ac_test.ML\<close>

subsection \<open>Showing two lists are equal\<close>

setup \<open>add_backward2_prfstep_cond @{thm nth_equalityI} [with_filt (order_filter "xs" "ys")]\<close>

subsection \<open>Set of elements of a list\<close>

setup \<open>add_rewrite_rule @{thm List.set_simps(1)}\<close>
lemma set_one [rewrite]: "set [u] = {u}" by simp
lemma set_two [rewrite]: "set [u, v] = {u, v}" by simp
lemma set_simps2: "set (x # xs) = {x} \<union> set xs" by simp
setup \<open>add_rewrite_rule_cond @{thm set_simps2} [with_cond "?xs \<noteq> []", with_cond "?xs \<noteq> [?y]"]\<close>
setup \<open>add_rewrite_rule @{thm List.set_append}\<close>
setup \<open>add_rewrite_rule @{thm List.set_rev}\<close>
setup \<open>add_resolve_prfstep @{thm List.finite_set}\<close>
setup \<open>add_backward_prfstep (equiv_forward_th @{thm in_set_conv_nth})\<close>

subsection \<open>hd\<close>

setup \<open>register_wellform_data ("hd xs", ["xs \<noteq> []"])\<close>
setup \<open>add_forward_prfstep_cond @{thm List.hd_in_set} [with_term "hd ?xs"]\<close>

subsection \<open>tl\<close>

setup \<open>add_rewrite_rule @{thm length_tl}\<close>
lemma nth_tl' [rewrite]: "i < length (tl xs) \<Longrightarrow> tl xs ! i = xs ! (i + 1)"
  by (simp add: nth_tl)
lemma set_tl_subset [forward_arg1]: "set (tl xs) \<subseteq> set xs"
  by (metis list.set_sel(2) subsetI tl_Nil)

subsection \<open>nth\<close>

setup \<open>register_wellform_data ("xs ! i", ["i < length xs"])\<close>
setup \<open>add_prfstep_check_req ("xs ! i", "i < length xs")\<close>
setup \<open>add_rewrite_rule_back @{thm hd_conv_nth}\<close>
setup \<open>add_rewrite_rule @{thm List.nth_Cons'}\<close>
setup \<open>add_rewrite_rule @{thm List.nth_append}\<close>
setup \<open>add_forward_prfstep_cond @{thm nth_mem} [with_term "?xs ! ?n"]\<close>

subsection \<open>sorted\<close>

lemma sorted_Nil [resolve]: "sorted []" by simp
lemma sorted_single [resolve]: "sorted [x]" by simp
setup \<open>add_backward_prfstep (equiv_backward_th @{thm sorted.simps(2)})\<close>

lemma sorted_ConsD1 [forward]: "sorted (x # xs) \<Longrightarrow> sorted xs"
  using sorted.simps(2) by blast
lemma sorted_ConsD2 [forward, backward2]: "sorted (x # xs) \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<le> y"
  using sorted.simps(2) by blast

lemma sorted_appendI [backward]:
  "sorted xs \<and> sorted ys \<and> (\<forall>x\<in>set xs. \<forall>y\<in>set ys. x \<le> y) \<Longrightarrow> sorted (xs @ ys)"
  by (simp add: sorted_append)

lemma sorted_appendE [forward]: "sorted (xs @ ys) \<Longrightarrow> sorted xs \<and> sorted ys"
  by (simp add: sorted_append)

lemma sorted_appendE2 [forward]:
  "sorted (xs @ ys) \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<forall>y\<in>set ys. x \<le> y"
  using sorted_append by blast

lemma sorted_nth_mono' [backward]:
  "sorted xs \<Longrightarrow> j < length xs \<Longrightarrow> i \<le> j \<Longrightarrow> xs ! i \<le> xs ! j" using sorted_nth_mono by auto

lemma sorted_nth_mono_less [forward]:
  "sorted xs \<Longrightarrow> i < length xs \<Longrightarrow> xs ! i < xs ! j \<Longrightarrow> i < j" by (meson leD not_le_imp_less sorted_nth_mono)

subsection \<open>sort\<close>

setup \<open>add_forward_prfstep_cond @{thm sorted_sort} [with_term "sort ?xs"]\<close>
setup \<open>add_rewrite_rule @{thm length_sort}\<close>
setup \<open>add_rewrite_rule @{thm mset_sort}\<close>
setup \<open>add_rewrite_rule @{thm set_sort}\<close>
setup \<open>add_backward_prfstep @{thm properties_for_sort}\<close>
lemma sort_Nil [rewrite]: "sort [] = []" by auto
lemma sort_singleton [rewrite]: "sort [a] = [a]" by auto

subsection \<open>distinct\<close>
  
lemma distinct_Nil [resolve]: "distinct []" by simp
setup \<open>add_resolve_prfstep @{thm List.distinct_singleton}\<close>
setup \<open>add_rewrite_rule_cond @{thm distinct.simps(2)} [with_cond "?xs \<noteq> []"]\<close>
setup \<open>add_rewrite_rule @{thm distinct_append}\<close>
setup \<open>add_rewrite_rule @{thm distinct_rev}\<close>
setup \<open>add_rewrite_rule @{thm distinct_sort}\<close>
setup \<open>add_resolve_prfstep (equiv_backward_th @{thm distinct_conv_nth})\<close>

lemma distinct_nthE [forward]:
  "distinct xs \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i = xs ! j \<Longrightarrow> i = j"
  using nth_eq_iff_index_eq by blast

subsection \<open>map function\<close>

setup \<open>fold add_rewrite_rule @{thms List.list.map}\<close>
setup \<open>add_rewrite_rule @{thm List.length_map}\<close>
setup \<open>add_rewrite_rule @{thm List.nth_map}\<close>
setup \<open>add_rewrite_rule @{thm List.map_append}\<close>

subsection \<open>Replicate\<close>

setup \<open>add_rewrite_arg_rule @{thm length_replicate}\<close>
setup \<open>add_rewrite_rule @{thm List.nth_replicate}\<close>

subsection \<open>last\<close>

setup \<open>register_wellform_data ("last xs", ["xs \<noteq> []"])\<close>
lemma last_eval1 [rewrite]: "last [x] = x" by simp
lemma last_eval2 [rewrite]: "last [u, v] = v" by simp
setup \<open>add_rewrite_rule @{thm List.last_ConsR}\<close>
setup \<open>add_rewrite_rule @{thm List.last_appendR}\<close>
setup \<open>add_rewrite_rule @{thm List.last_snoc}\<close>
setup \<open>add_rewrite_rule_back @{thm last_conv_nth}\<close>
setup \<open>add_forward_prfstep_cond @{thm List.last_in_set} [with_term "last ?as"]\<close>

subsection \<open>butlast\<close>

setup \<open>add_rewrite_arg_rule @{thm List.length_butlast}\<close>
setup \<open>add_rewrite_rule @{thm List.nth_butlast}\<close>
setup \<open>add_rewrite_rule_back @{thm List.butlast_conv_take}\<close>
setup \<open>add_rewrite_rule @{thm List.butlast_snoc}\<close>
lemma butlast_eval1 [rewrite]: "butlast [x] = []" by simp
lemma butlast_eval2 [rewrite]: "butlast [x, y] = [x]" by simp
lemma butlast_cons [rewrite]: "as \<noteq> [] \<Longrightarrow> butlast (a # as) = a # butlast as" by simp
lemma butlast_append' [rewrite]: "bs \<noteq> [] \<Longrightarrow> butlast (as @ bs) = as @ butlast bs"
  by (simp add: butlast_append)

setup \<open>add_rewrite_rule @{thm List.append_butlast_last_id}\<close>
lemma set_butlast_is_subset: "set (butlast xs) \<subseteq> set xs" by (simp add: in_set_butlastD subsetI)
setup \<open>add_forward_arg1_prfstep @{thm set_butlast_is_subset}\<close>

subsection \<open>List update\<close>

setup \<open>register_wellform_data ("xs[i := x]", ["i < length xs"])\<close>
setup \<open>add_rewrite_arg_rule @{thm List.length_list_update}\<close>
setup \<open>add_rewrite_rule @{thm List.nth_list_update_eq}\<close>
setup \<open>add_rewrite_rule @{thm List.nth_list_update_neq}\<close>
setup \<open>add_rewrite_rule @{thm List.nth_list_update}\<close>

subsection \<open>take\<close>

setup \<open>register_wellform_data ("take n xs", ["n \<le> length xs"])\<close>
setup \<open>add_prfstep_check_req ("take n xs", "n \<le> length xs")\<close>

lemma length_take [rewrite_arg]: "n \<le> length xs \<Longrightarrow> length (take n xs) = n" by simp
lemma nth_take [rewrite]: "i < length (take n xs) \<Longrightarrow> take n xs ! i = xs ! i" by simp

setup \<open>add_rewrite_rule @{thm List.take_0}\<close>
setup \<open>add_rewrite_rule @{thm List.take_Suc_conv_app_nth}\<close>
lemma take_length [rewrite]: "take (length xs) xs = xs" by simp

setup \<open>add_forward_arg1_prfstep @{thm List.set_take_subset}\<close>

lemma take_Suc [rewrite]: "Suc n \<le> length xs \<Longrightarrow> take (Suc n) xs = take n xs @ [nth xs n]"
  using Suc_le_lessD take_Suc_conv_app_nth by blast

setup \<open>add_rewrite_rule @{thm List.take_update_cancel}\<close>
setup \<open>add_rewrite_rule @{thm List.append_take_drop_id}\<close>
setup \<open>add_rewrite_rule @{thm List.take_all}\<close>

subsection \<open>drop\<close>

setup \<open>add_rewrite_arg_rule @{thm List.length_drop}\<close>
lemma nth_drop [rewrite]:
  "i < length (drop n xs) \<Longrightarrow> drop n xs ! i = xs ! (n + i)" by simp

setup \<open>add_rewrite_rule @{thm List.drop_0}\<close>
setup \<open>add_rewrite_rule @{thm List.drop_all}\<close>
setup \<open>add_rewrite_rule_back @{thm List.take_drop}\<close>
setup \<open>add_rewrite_rule @{thm List.drop_drop}\<close>

subsection \<open>rev\<close>

setup \<open>add_rewrite_arg_rule @{thm List.length_rev}\<close>
setup \<open>fold add_rewrite_rule @{thms List.rev.simps}\<close>
setup \<open>add_rewrite_rule @{thm List.rev_append}\<close>
setup \<open>add_rewrite_rule @{thm List.rev_rev_ident}\<close>

subsection \<open>filter\<close>

setup \<open>fold add_rewrite_rule @{thms filter.simps}\<close>
setup \<open>add_rewrite_rule @{thm filter_append}\<close>
setup \<open>add_rewrite_rule_bidir @{thm rev_filter}\<close>

subsection \<open>concat\<close>

setup \<open>fold add_rewrite_rule @{thms concat.simps}\<close>

subsection \<open>mset\<close>

setup \<open>add_rewrite_rule @{thm mset.simps(1)}\<close>
lemma mset_simps_2 [rewrite]: "mset (a # x) = mset x + {#a#}" by simp
setup \<open>add_rewrite_rule @{thm mset_append}\<close>

setup \<open>add_rewrite_rule @{thm mset_eq_setD}\<close>
setup \<open>add_rewrite_rule_cond @{thm in_multiset_in_set} [with_term "set ?xs"]\<close>
setup \<open>add_rewrite_rule_back_cond @{thm in_multiset_in_set} [with_term "mset ?xs"]\<close>
setup \<open>add_backward_prfstep @{thm Multiset.nth_mem_mset}\<close>

lemma in_mset_conv_nth [resolve]: "x \<in># mset xs \<Longrightarrow> \<exists>i<length xs. x = xs ! i"
  by (metis in_multiset_in_set in_set_conv_nth)

lemma hd_in_mset: "xs \<noteq> [] \<Longrightarrow> hd xs \<in># mset xs" by simp
setup \<open>add_forward_prfstep_cond @{thm hd_in_mset} [with_term "hd ?xs", with_term "mset ?xs"]\<close>

lemma last_in_mset: "xs \<noteq> [] \<Longrightarrow> last xs \<in># mset xs" by simp
setup \<open>add_forward_prfstep_cond @{thm last_in_mset} [with_term "last ?xs", with_term "mset ?xs"]\<close>

subsection \<open>Relationship between mset and set of lists\<close>

lemma mset_butlast [rewrite]: "xs \<noteq> [] \<Longrightarrow> mset (butlast xs) = mset xs - {# last xs #}"
  by (metis add_diff_cancel_right' append_butlast_last_id mset.simps(1) mset.simps(2) union_code)

lemma insert_mset_to_set [rewrite]: "mset xs' = mset xs + {# x #} \<Longrightarrow> set xs' = set xs \<union> {x}"
  by (metis set_mset_mset set_mset_single set_mset_union)

lemma delete_mset_to_set [rewrite]:
  "distinct xs \<Longrightarrow> mset xs' = mset xs - {# x #} \<Longrightarrow> set xs' = set xs - {x}"
  by (metis mset_eq_setD mset_remove1 set_remove1_eq)

lemma update_mset_to_set [rewrite]:
  "distinct xs \<Longrightarrow> mset xs' = {# y #} + (mset xs - {# x #}) \<Longrightarrow> set xs' = (set xs - {x}) \<union> {y}"
  by (metis insert_mset_to_set mset_remove1 set_remove1_eq union_commute)

lemma mset_update' [rewrite]:
  "i < length ls \<Longrightarrow> mset (ls[i := v]) = {#v#} + (mset ls - {# ls ! i #})"
  using mset_update by fastforce

subsection \<open>swap\<close>

setup \<open>add_rewrite_rule @{thm mset_swap}\<close>
setup \<open>add_rewrite_rule @{thm set_swap}\<close>

subsection \<open>upto lists\<close>

lemma upt_zero_length [rewrite]: "length [0..<n] = n" by simp
lemma nth_upt_zero [rewrite]: "i < length [0..<n] \<Longrightarrow> [0..<n] ! i = i" by simp

subsection \<open>Lambda lists\<close>

definition list :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list" where
  "list s n = map s [0 ..< n]"

lemma list_length [rewrite_arg]: "length (list s n) = n" by (simp add: list_def)
lemma list_nth [rewrite]: "i < length (list s n) \<Longrightarrow> (list s n) ! i = s i" by (simp add: list_def)

subsection \<open>Splitting of lists\<close>

setup \<open>add_resolve_prfstep @{thm split_list}\<close>
setup \<open>add_backward_prfstep @{thm not_distinct_decomp}\<close>

subsection \<open>Finiteness\<close>

setup \<open>add_resolve_prfstep @{thm finite_lists_length_le}\<close>

subsection \<open>Cardinality\<close>

setup \<open>add_rewrite_rule @{thm distinct_card}\<close>

end
