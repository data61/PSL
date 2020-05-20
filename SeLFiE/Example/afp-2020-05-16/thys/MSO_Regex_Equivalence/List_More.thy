(* Author: Dmitry Traytel *)

theory List_More
imports Main "List-Index.List_Index" "HOL-Library.Multiset"
begin

subsection \<open>Library Functions\<close>

abbreviation "bool_product_lists n \<equiv> product_lists (replicate n [True, False])"

lemma in_set_bool_product_lists[simp]:
  "bs \<in> set (bool_product_lists n) \<longleftrightarrow> length bs = n"
proof (induct n arbitrary: bs)
  case (Suc n) thus ?case by (cases bs) auto
qed simp

text \<open>More on sort and remdups\<close>

lemma insort_min[simp]: "\<forall>y \<in> set xs. x < y \<Longrightarrow> insort x xs = x # xs"
  by (induct xs) auto

lemma insort_max[simp]: "\<forall>y \<in> set xs. x > y \<Longrightarrow> insort x xs = xs @ [x]"
  by (induct xs) auto

lemma insort_snoc[simp]: "\<forall>z \<in> set xs. y > z \<Longrightarrow>
  insort x (xs @ [y]) = (if x < y then insort x xs @ [y] else xs @ [y, x])"
  by (induct xs) auto

declare set_insort_key[simp]

lemma insort_remdups[simp]: "\<lbrakk>sorted xs; a \<notin> set xs\<rbrakk> \<Longrightarrow> insort a (remdups xs) = remdups (insort a xs)"
proof (induct xs)
  case (Cons x xs) thus ?case by (cases xs) (auto)
qed simp

lemma remdups_insort[simp]: "a \<in> set xs \<Longrightarrow> remdups (insort a xs) = remdups xs"
  by (induct xs) auto

lemma sort_remdups[simp]: "sort (remdups xs) = remdups (sort xs)"
  by (induct xs) auto

lemma sort_map_insort[simp]: "sorted xs \<Longrightarrow> sort (map f (insort a xs)) = insort (f a) (sort (map f xs))"
  by (induct xs) (auto simp: insort_left_comm)

lemma sort_map_sort[simp]: "sort (map f (sort xs)) = sort (map f xs)"
  by (induct xs) auto

lemma remdups_append: "remdups (xs @ ys) = remdups (filter (\<lambda>x. x \<notin> set ys) xs) @ remdups ys"
  by (induct xs) auto

lemma remdups_concat_map_remdups:
  "remdups (concat (map f (remdups xs))) = remdups (concat (map f xs))"
  by (induct xs) (auto simp: remdups_append filter_empty_conv)

(*remdups'*)

primrec remdups' where
  "remdups' f [] = []"
| "remdups' f (x # xs) =
    (case List.find (\<lambda>y. f x = f y) xs of None \<Rightarrow> x # remdups' f xs | _ \<Rightarrow> remdups' f xs)"

lemma map_remdups'[simp]: "map f (remdups' f xs) = remdups (map f xs)"
  by (induct xs) (auto split: option.splits simp add: find_Some_iff find_None_iff)

lemma remdups'_map[simp]: "remdups' f (map g xs) = map g (remdups' (f o g) xs)"
  by (induct xs) (auto split: option.splits simp add: find_None_iff,
                auto simp: find_Some_iff elim: imageI[OF nth_mem])

lemma map_apfst_remdups':
  "map (f o fst) (remdups' snd xs) = map fst (remdups' snd (map (apfst f) xs))"
  by (auto simp: comp_def)

lemma set_remdups'[simp]: "f ` set (remdups' f xs) = f ` set xs"
  by (induct xs) (auto split: option.splits simp add: find_Some_iff)

lemma subset_remdups': "set (remdups' f xs) \<subseteq> set xs"
  by (induct xs) (auto split: option.splits)

lemma find_append[simp]:
  "List.find P (xs @ ys) = None = (List.find P xs = None \<and> List.find P ys = None)"
  by (induct xs) auto

lemma subset_remdups'_append: "set (remdups' f (xs @ ys)) \<subseteq> set (remdups' f xs) \<union> set (remdups' f ys)"
  by (induct xs arbitrary: ys) (auto split: option.splits)

lemmas mp_remdups' = subsetD[OF subset_remdups']
lemmas mp_remdups'_append = subsetD[OF subset_remdups'_append]

lemma inj_on_set_remdups'[simp]: "inj_on f (set (remdups' f xs))"
  by (induct xs) (auto split: option.splits simp add: find_None_iff dest!: mp_remdups')

lemma distinct_remdups'[simp]: "distinct (map f (remdups' f xs))"
  by (induct xs) (auto split: option.splits simp: find_None_iff)

lemma distinct_remdups'_strong: "(\<forall>x\<in>set xs. \<forall>y\<in>set xs. g x = g y \<longrightarrow> f x = f y) \<Longrightarrow>
  distinct (map g (remdups' f xs))"
proof (induct xs)
  case (Cons x xs) thus ?case
    by (auto split: option.splits) (fastforce simp: find_None_iff dest!: mp_remdups')
qed simp

lemma set_remdups'_strong:
  "f ` set (remdups' g xs) = f ` set xs" if "\<forall>x\<in>set xs. \<forall>y\<in>set xs. g x = g y \<longrightarrow> f x = f y"
using that proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then have "\<forall>x\<in>set xs. \<forall>y\<in>set xs. g x = g y \<longrightarrow> f x = f y"
    by (auto simp only: set_simps)
  then have "f ` set (remdups' g xs) = f ` set xs"
    by (rule Cons.IH)
  then show ?case
    by (auto simp add: find_Some_iff split: option.splits)
      (metis Cons.prems image_eqI list.set_intros(1) list.set_intros(2) nth_mem)
qed

(*multisets only needed below*)
lemma multiset_concat_gen: "M + mset (concat xs) = fold (\<lambda>x M. M + mset x) xs M"
  by (induct xs arbitrary: M) (auto, metis union_assoc)

corollary multiset_concat: "mset (concat xs) = fold (\<lambda>x M. M + mset x) xs {#}"
  using multiset_concat_gen[of "{#}" xs] by simp

lemma fold_mset_insort[simp]: "fold (\<lambda>x M. M + mset (f x)) (insort x xs) M =
  fold (\<lambda>x M. M + mset (f x)) xs (mset (f x) + M)"
  by (induct xs arbitrary: M) (auto simp: ac_simps)

lemma fold_mset_sort[simp]:
  "fold (\<lambda>x M. M + mset (f x)) (sort xs) M = fold (\<lambda>x M. M + mset (f x)) xs M"
  by (induct xs arbitrary: M) (auto simp: ac_simps)

lemma multiset_concat_map_sort[simp]:
  "mset (concat (map f (sort xs))) = mset (concat (map f xs))"
  by (auto simp: multiset_concat fold_map o_def)

lemma sort_concat_map_sort[simp]: "sort (concat (map f (sort xs))) = sort (concat (map f xs))"
  by (auto intro: properties_for_sort)

end
