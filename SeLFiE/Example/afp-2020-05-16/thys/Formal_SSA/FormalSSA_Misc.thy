(*  Title:      FormalSSA_Misc.thy
    Author:     Sebastian Ullrich, Denis Lohner
*)

section \<open>Prelude\<close>

subsection \<open>Miscellaneous Lemmata\<close>

theory FormalSSA_Misc
imports Main "HOL-Library.Sublist"
begin

lemma length_1_last_hd: "length ns = 1 \<Longrightarrow> last ns = hd ns"
  by (metis One_nat_def append.simps(1) append_butlast_last_id diff_Suc_Suc diff_zero length_0_conv length_butlast list.sel(1) zero_neq_one)

lemma not_in_butlast[simp]: "\<lbrakk>x \<in> set ys; x \<notin> set (butlast ys)\<rbrakk> \<Longrightarrow> x = last ys"
  apply (cases "ys = []")
   apply simp
  apply (subst(asm) append_butlast_last_id[symmetric])
  by (simp_all del:append_butlast_last_id)

lemma in_set_butlastI: "x \<in> set xs \<Longrightarrow> x \<noteq> last xs \<Longrightarrow> x \<in> set (butlast xs)"
  by (metis append_butlast_last_id append_is_Nil_conv list.distinct(1) rotate1.simps(2) set_ConsD set_rotate1 split_list)

lemma butlast_strict_prefix: "xs \<noteq> [] \<Longrightarrow> strict_prefix (butlast xs) xs"
  by (metis append_butlast_last_id strict_prefixI')

lemma set_tl: "set (tl xs) \<subseteq> set xs"
  by (metis set_mono_suffix suffix_tl)

lemma in_set_tlD[elim]: "x \<in> set (tl xs) \<Longrightarrow> x \<in> set xs"
  using set_tl[of xs] by auto

lemma suffix_unsnoc:
  assumes "suffix xs ys" "xs \<noteq> []"
  obtains x where "xs = butlast xs@[x]" "ys = butlast ys@[x]"
  by (metis append_butlast_last_id append_is_Nil_conv assms(1) assms(2) last_appendR suffix_def)

lemma prefix_split_first:
  assumes "x \<in> set xs"
  obtains as where "prefix (as@[x]) xs" and "x \<notin> set as"
proof atomize_elim
  from assms obtain as bs where "xs = as@x#bs \<and> x \<notin> set as" by (atomize_elim, rule split_list_first)
  thus "\<exists>as. prefix (as@[x]) xs \<and> x \<notin> set as" by -(rule exI[where x = as], auto)
qed

lemma in_prefix[elim]:
  assumes "prefix xs ys" and "x \<in> set xs"
  shows "x \<in> set ys"
using assms by (auto elim!:prefixE)

lemma strict_prefix_butlast:
  assumes "prefix xs (butlast ys)" "ys \<noteq> []"
  shows "strict_prefix xs ys"
using assms unfolding append_butlast_last_id[symmetric] by (auto simp add:less_le butlast_strict_prefix prefix_order.le_less_trans)

lemma prefix_tl_subset: "prefix xs ys \<Longrightarrow> set (tl xs) \<subseteq> set (tl ys)"
  by (metis Nil_tl prefix_bot.bot.extremum prefix_def set_mono_prefix tl_append2)

lemma suffix_tl_subset: "suffix xs ys \<Longrightarrow> set (tl xs) \<subseteq> set (tl ys)"
  by (metis append_Nil suffix_def set_mono_suffix suffix_tl suffix_order.order_trans tl_append2)

lemma set_tl_append': "set (tl (xs @ ys)) \<subseteq> set (tl xs) \<union> set ys"
  by (metis list.sel(2) order_refl set_append set_mono_suffix suffix_tl tl_append2)

lemma last_in_tl: "length xs > 1 \<Longrightarrow> last xs \<in> set (tl xs)"
  by (metis One_nat_def diff_Suc_Suc last_in_set last_tl length_tl less_numeral_extra(4) list.size(3) zero_less_diff)

lemma concat_join: "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> last xs = hd ys \<Longrightarrow> butlast xs@ys = xs@tl ys"
  by (induction xs, auto)

lemma fold_induct[case_names Nil Cons]: "P s \<Longrightarrow> (\<And>x s. x \<in> set xs \<Longrightarrow> P s \<Longrightarrow> P (f x s)) \<Longrightarrow> P (fold f xs s)"
by (rule fold_invariant [where Q = "\<lambda>x. x \<in> set xs"]) simp

lemma fold_union_elem:
  assumes "x \<in> fold (\<union>) xss xs"
  obtains ys where "x \<in> ys" "ys \<in> set xss \<union> {xs}"
using assms
by (induction rule:fold_induct) auto

lemma fold_union_elemI:
  assumes "x \<in> ys" "ys \<in> set xss \<union> {xs}"
  shows "x \<in> fold (\<union>) xss xs"
using assms
by (metis Sup_empty Sup_insert Sup_set_fold Un_insert_right UnionI ccpo_Sup_singleton fold_simps(2) list.simps(15))

lemma fold_union_elemI':
  assumes "x \<in> xs \<or> (\<exists>xs \<in> set xss. x \<in> xs)"
  shows "x \<in> fold (\<union>) xss xs"
using assms
using fold_union_elemI by fastforce

lemma fold_union_finite[intro!]:
  assumes "finite xs" "\<forall>xs \<in> set xss. finite xs"
  shows "finite (fold (\<union>) xss xs)"
using assms by - (rule fold_invariant, auto)

lemma in_set_zip_map:
  assumes "(x,y) \<in> set (zip xs (map f ys))"
  obtains y' where "(x,y') \<in> set (zip xs ys)" "f y' = y"
proof-
  from assms obtain i where "x = xs ! i" "y = map f ys ! i" "i < length xs" "i < length ys" by (auto simp:set_zip)
  thus thesis by - (rule that[of "ys ! i"], auto simp:set_zip)
qed

lemma dom_comp_subset: "g ` dom (f \<circ> g) \<subseteq> dom f"
by (auto simp add:dom_def)

lemma finite_dom_comp:
  assumes "finite (dom f)" "inj_on g (dom (f \<circ> g))"
  shows "finite (dom (f \<circ> g))"
proof (rule finite_imageD)
  have "g ` dom (f \<circ> g) \<subseteq> dom f" by auto
  with assms(1) show "finite (g ` dom (f \<circ> g))" by - (rule finite_subset)
qed (simp add:assms(2))

lemma the1_list: "\<exists>!x \<in> set xs. P x \<Longrightarrow> (THE x. x \<in> set xs \<and> P x) = hd (filter P xs)"
proof (induction xs)
  case (Cons y xs)
  let ?Q = "\<lambda>xs x. x \<in> set xs \<and> P x"
  from Cons.prems obtain x where x: "?Q (y#xs) x" by auto
  have "x = hd (filter P (y#xs))"
  proof (cases "x=y")
    case True
    with x show ?thesis by auto
  next
    case False
    with Cons.prems x have 1: "\<exists>!x. x \<in> set xs \<and> P x" by auto
    hence "(THE x. x \<in> set xs \<and> P x) = x" using x False by - (rule the1_equality, auto)
    also from 1 have "(THE x. x \<in> set xs \<and> P x) = hd (filter P xs)" by (rule Cons.IH)
    finally show ?thesis using False x Cons.prems by auto
  qed
  thus ?case using x by - (rule the1_equality[OF Cons.prems], auto)
qed auto

lemma set_zip_leftI:
  assumes "length xs = length ys"
  assumes "y \<in> set ys"
  obtains x where "(x,y) \<in> set (zip xs ys)"
proof-
  from assms(2) obtain i where "y = ys ! i" "i < length ys" by (metis in_set_conv_nth)
  with assms(1) show thesis by - (rule that[of "xs ! i"], auto simp add:set_zip)
qed

lemma butlast_idx:
  assumes "y \<in> set (butlast xs)"
  obtains i where "xs ! i = y" "i < length xs - 1"
apply atomize_elim
using assms proof (induction xs arbitrary:y)
  case (Cons x xs)
  from Cons.prems have[simp]: "xs \<noteq> []" by (simp split:if_split_asm)
  show ?case
  proof (cases "y = x")
    case True
    show ?thesis by (rule exI[where x=0], simp_all add:True)
  next
    case False
    with Cons.prems have "y \<in> set (butlast xs)" by simp
    from Cons.IH[OF this] obtain i where "y = xs ! i" and "i < length xs - 1" by auto
    thus ?thesis by - (rule exI[where x="Suc i"], simp)
  qed
qed simp

lemma butlast_idx':
  assumes "xs ! i = y" "i < length xs - 1" "length xs > 1"
  shows "y \<in> set (butlast xs)"
using assms proof (induction xs arbitrary:i)
  case (Cons x xs)
  show ?case
  proof (cases i)
    case 0
    with Cons.prems(1,3) show ?thesis by simp
  next
    case (Suc j)
    with Cons.prems(1)[symmetric] Cons.prems(2,3) have "y \<in> set (butlast xs)" by - (rule Cons.IH, auto)
    with Cons.prems(3) show ?thesis by simp
  qed
qed simp

lemma card_eq_1_singleton:
  assumes "card A = 1"
  obtains x where "A = {x}"
using assms[simplified] by - (drule card_eq_SucD, auto)

lemma set_take_two:
  assumes "card A \<ge> 2"
  obtains x y where "x \<in> A" "y \<in> A" "x \<noteq> y"
proof-
  from assms obtain k where "card A = Suc (Suc k)"
    by (auto simp: le_iff_add)
  from card_eq_SucD[OF this] obtain x B where x: "A = insert x B" "x \<notin> B" "card B = Suc k" by auto
  from card_eq_SucD[OF this(3)] obtain y where y: "y \<in> B" by auto
  from x y show ?thesis by - (rule that[of x y], auto)
qed

lemma singleton_list_hd_last: "length xs = 1 \<Longrightarrow> hd xs = last xs"
  by (metis One_nat_def impossible_Cons last.simps length_0_conv less_nat_zero_code list.sel(1) nat_less_le neq_Nil_conv not_less_eq_eq)

lemma distinct_hd_tl: "distinct xs \<Longrightarrow> hd xs \<notin> set (tl xs)"
  by (metis distinct.simps(2) hd_Cons_tl in_set_member list.sel(2) member_rec(2))

lemma set_mono_strict_prefix: "strict_prefix xs ys \<Longrightarrow> set xs \<subseteq> set (butlast ys)"
  by (metis append_butlast_last_id strict_prefixE strict_prefix_simps(1) prefix_snoc set_mono_prefix)

lemma set_butlast_distinct: "distinct xs \<Longrightarrow> set (butlast xs) \<inter> {last xs} = {}"
  by (metis append_butlast_last_id butlast.simps(1) distinct_append inf_bot_right inf_commute list.set(1) set_simps(2))

lemma disjoint_elem[elim]: "A \<inter> B = {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<notin> B" by auto

lemma prefix_butlastD[elim]: "prefix xs (butlast ys) \<Longrightarrow> prefix xs ys"
  using strict_prefix_butlast by fastforce

lemma butlast_prefix: "prefix xs ys \<Longrightarrow> prefix (butlast xs) (butlast ys)"
  by (induction xs ys rule: list_induct2'; auto)

lemma hd_in_butlast: "length xs > 1 \<Longrightarrow> hd xs \<in> set (butlast xs)"
  by (metis butlast.simps(2) dual_order.strict_iff_order hd_Cons_tl hd_in_set length_greater_0_conv length_tl less_le_trans list.distinct(1) list.sel(1) neq0_conv zero_less_diff)

lemma nonsimple_length_gt_1: "xs \<noteq> [] \<Longrightarrow> hd xs \<noteq> last xs \<Longrightarrow> length xs > 1"
  by (metis length_0_conv less_one nat_neq_iff singleton_list_hd_last)

lemma set_hd_tl: "xs \<noteq> [] \<Longrightarrow> set [hd xs] \<union> set (tl xs) = set xs"
  by (metis inf_sup_aci(5) rotate1_hd_tl set_append set_rotate1)

lemma fold_update_conv:
  "fold (\<lambda>n m. m(n \<mapsto> g n)) xs m x =
  (if (x \<in> set xs) then Some (g x) else m x)"
  by (induction xs arbitrary: m) auto

lemmas removeAll_le = length_removeAll_less_eq

lemmas removeAll_less [intro] = length_removeAll_less

lemma removeAll_induct:
  assumes "\<And>xs. (\<And>x. x \<in> set xs \<Longrightarrow> P (removeAll x xs)) \<Longrightarrow> P xs"
  shows "P xs"
by (induct xs rule:length_induct, rule assms) auto

lemma The_Min: "Ex1 P \<Longrightarrow> The P = Min {x. P x}"
apply (rule the_equality)
 apply (metis (mono_tags) Min.infinite Min_in Min_singleton all_not_in_conv finite_subset insert_iff mem_Collect_eq subsetI)
by (metis (erased, hide_lams) Least_Min Least_equality Set.set_insert ex_in_conv finite.emptyI finite_insert insert_iff mem_Collect_eq order_refl)

lemma The_Max: "Ex1 P \<Longrightarrow> The P = Max {x. P x}"
apply (rule the_equality)
 apply (metis (mono_tags) Max.infinite Max_in Max_singleton all_not_in_conv finite_subset insert_iff mem_Collect_eq subsetI)
by (metis Max_singleton Min_singleton Nitpick.Ex1_unfold The_Min the_equality)

lemma set_sorted_list_of_set_remove [simp]:
"set (sorted_list_of_set (Set.remove x A)) = Set.remove x (set (sorted_list_of_set A))"
  unfolding Set.remove_def
by (cases "finite A"; simp)

lemma set_minus_one: "\<lbrakk>v \<noteq> v'; v' \<in> set vs\<rbrakk> \<Longrightarrow> set vs - {v'} \<subseteq> {v} \<longleftrightarrow> set vs = {v'} \<or> set vs = {v,v'}"
  by auto

lemma set_single_hd: "set vs = {v} \<Longrightarrow> hd vs = v"
  by (induction vs; auto)

lemma set_double_filter_hd: "\<lbrakk> set vs = {v,v'}; v \<noteq> v' \<rbrakk> \<Longrightarrow> hd [v'\<leftarrow>vs . v' \<noteq> v] = v'"
apply (induction vs)
 apply simp
apply auto
apply (case_tac "v \<in> set vs")
 prefer 2
 apply (subgoal_tac "set vs = {v'}")
  prefer 2
  apply fastforce
 apply (clarsimp simp: set_single_hd)
by fastforce

lemma map_option_the: "x = map_option f y \<Longrightarrow> x \<noteq> None \<Longrightarrow> the x = f (the y)"
  by (auto simp: map_option_case split: option.split prod.splits)

end
