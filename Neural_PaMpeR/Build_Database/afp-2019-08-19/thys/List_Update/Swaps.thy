(* Author: Tobias Nipkow *)

section "Swapping Adjacent Elements in a List"

theory Swaps
imports Inversion
begin

text\<open>Swap elements at index \<open>n\<close> and @{term "Suc n"}:\<close>

definition "swap n xs =
  (if Suc n < size xs then xs[n := xs!Suc n, Suc n := xs!n] else xs)"

lemma length_swap[simp]: "length(swap i xs) = length xs"
by(simp add: swap_def)

lemma swap_id[simp]: "Suc n \<ge> size xs \<Longrightarrow> swap n xs = xs"
by(simp add: swap_def)

lemma distinct_swap[simp]:
  "distinct(swap i xs) = distinct xs"
by(simp add: swap_def)

lemma swap_Suc[simp]: "swap (Suc n) (a # xs) = a # swap n xs"
by(induction xs) (auto simp: swap_def)

lemma index_swap_distinct:
  "distinct xs \<Longrightarrow> Suc n < length xs \<Longrightarrow>
  index (swap n xs) x =
  (if x = xs!n then Suc n else if x = xs!Suc n then n else index xs x)"
by(auto simp add: swap_def index_swap_if_distinct)

lemma set_swap[simp]: "set(swap n xs) = set xs"
by(auto simp add: swap_def set_conv_nth nth_list_update) metis

lemma nth_swap_id[simp]: "Suc i < length xs \<Longrightarrow> swap i xs ! i = xs!(i+1)"
by(simp add: swap_def)

lemma before_in_swap:
 "dist_perm xs ys \<Longrightarrow> Suc n < size xs \<Longrightarrow>
  x < y in (swap n xs) \<longleftrightarrow>
  x < y in xs \<and> \<not> (x = xs!n \<and> y = xs!Suc n) \<or> x = xs!Suc n \<and> y = xs!n"
by(simp add:before_in_def index_swap_distinct)
  (metis Suc_lessD Suc_lessI index_less_size_conv index_nth_id less_Suc_eq n_not_Suc_n nth_index)

lemma Inv_swap: assumes "dist_perm xs ys"
shows "Inv xs (swap n ys) = 
  (if Suc n < size xs
   then if ys!n < ys!Suc n in xs
        then Inv xs ys \<union> {(ys!n, ys!Suc n)}
        else Inv xs ys - {(ys!Suc n, ys!n)}
   else Inv xs ys)"
proof-
  have "length xs = length ys" using assms by (metis distinct_card)
  with assms show ?thesis
    by(simp add: Inv_def set_eq_iff)
      (metis before_in_def not_before_in before_in_swap)
qed


text\<open>Perform a list of swaps, from right to left:\<close>

abbreviation swaps where "swaps == foldr swap"

lemma swaps_inv[simp]:
  "set (swaps sws xs) = set xs \<and>
  size(swaps sws xs) = size xs \<and>
  distinct(swaps sws xs) = distinct xs"
by (induct sws arbitrary: xs) (simp_all add: swap_def)

lemma swaps_eq_Nil_iff[simp]: "swaps acts xs = [] \<longleftrightarrow> xs = []"
by(induction acts)(auto simp: swap_def)

lemma swaps_map_Suc[simp]:
  "swaps (map Suc sws) (a # xs) = a # swaps sws xs"
by(induction sws arbitrary: xs) auto

lemma card_Inv_swaps_le:
  "distinct xs \<Longrightarrow> card (Inv xs (swaps sws xs)) \<le> length sws"
by(induction sws) (auto simp: Inv_swap card_insert_if card_Diff_singleton_if)

lemma nth_swaps: "\<forall>i\<in>set is. j < i \<Longrightarrow> swaps is xs ! j = xs ! j"
by(induction "is")(simp_all add: swap_def)

lemma not_before0[simp]: "~ x < xs ! 0 in xs"
apply(cases "xs = []")
by(auto simp: before_in_def neq_Nil_conv)

lemma before_id[simp]: "\<lbrakk> distinct xs; i < size xs; j < size xs \<rbrakk> \<Longrightarrow>
  xs ! i < xs ! j in xs \<longleftrightarrow> i < j"
by(simp add: before_in_def index_nth_id)

lemma before_swaps:
  "\<lbrakk> distinct is; \<forall>i\<in>set is. Suc i < size xs; distinct xs; i \<notin> set is; i < j; j < size xs \<rbrakk> \<Longrightarrow>
  swaps is xs ! i < swaps is xs ! j in xs"
apply(induction "is" arbitrary: i j)
 apply simp
apply(auto simp: swap_def nth_list_update)
done

lemma card_Inv_swaps:
  "\<lbrakk> distinct is; \<forall>i\<in>set is. Suc i < size xs; distinct xs \<rbrakk> \<Longrightarrow>
  card(Inv xs (swaps is xs)) = length is"
apply(induction "is")
 apply simp
apply(simp add: Inv_swap before_swaps card_insert_if)
apply(simp add: Inv_def)
done

lemma swaps_eq_nth_take_drop: "i < length xs \<Longrightarrow>
    swaps [0..<i] xs = xs!i # take i xs @ drop (Suc i) xs"
apply(induction i arbitrary: xs)
apply (auto simp add: neq_Nil_conv swap_def drop_update_swap
  take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric])
done

lemma index_swaps_size: "distinct s \<Longrightarrow>
  index s q \<le> index (swaps sws s) q + length sws"
apply(induction sws arbitrary: s)
apply simp
 apply (fastforce simp: swap_def index_swap_if_distinct index_nth_id)
done

lemma index_swaps_last_size: "distinct s \<Longrightarrow>
  size s \<le> index (swaps sws s) (last s) + length sws + 1"
apply(cases "s = []")
 apply simp
using index_swaps_size[of s "last s" sws] by simp

end
