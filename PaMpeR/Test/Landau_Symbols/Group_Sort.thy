(*
  File: Group_Sort.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  A sorting algorithm that sorts values according to a key function and groups equivalent 
  elements using a commutative and associative binary operation.
*)
section {* Sorting and grouping factors *}

theory Group_Sort
imports Main "HOL-Library.Multiset"
begin

text {*
  For the reification of products of powers of primitive functions such as
  @{term "\<lambda>x. x * ln x ^2"} into a canonical form, we need to be able to sort the factors 
  according to the growth of the primitive function it contains and merge terms with the same 
  function by adding their exponents. The following locale defines such an operation in a 
  general setting; we can then instantiate it for our setting.

  The locale takes as parameters a key function @{term "f"} that sends list elements into a 
  linear ordering that determines the sorting order, a @{term "merge"} function to merge to 
  equivalent (w.r.t. @{term "f"}) elements into one, and a list reduction function @{term "g"} 
  that reduces a list to a single value. This function must be invariant w.r.t. the order of 
  list elements and be compatible with merging of equivalent elements. In our case, this list 
  reduction function will be the product of all list elements.
*}

locale groupsort = 
  fixes f :: "'a \<Rightarrow> ('b::linorder)"
  fixes merge :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes g :: "'a list \<Rightarrow> 'c"
  assumes f_merge: "f x = f y \<Longrightarrow> f (merge x y) = f x"
  assumes g_cong: "mset xs = mset ys \<Longrightarrow> g xs = g ys"
  assumes g_merge: "f x = f y \<Longrightarrow> g [x,y] = g [merge x y]"
  assumes g_append_cong: "g xs1 = g xs2 \<Longrightarrow> g ys1 = g ys2 \<Longrightarrow> g (xs1 @ ys1) = g (xs2 @ ys2)"
begin

context
begin

private function part_aux :: 
  "'b \<Rightarrow> 'a list \<Rightarrow> ('a list) \<times> ('a list) \<times> ('a list) \<Rightarrow> ('a list) \<times> ('a list) \<times> ('a list)" 
where
  "part_aux p [] (ls, eq, gs) = (ls, eq, gs)"
| "f x < p \<Longrightarrow> part_aux p (x#xs) (ls, eq, gs) = part_aux p xs (x#ls, eq, gs)"
| "f x > p \<Longrightarrow> part_aux p (x#xs) (ls, eq, gs) = part_aux p xs (ls, eq, x#gs)"
| "f x = p \<Longrightarrow> part_aux p (x#xs) (ls, eq, gs) = part_aux p xs (ls, eq@[x], gs)"
proof (clarify, goal_cases)
  case prems: (1 P p xs ls eq gs)
  show ?case
  proof (cases xs)
    fix x xs' assume "xs = x # xs'"
    thus ?thesis using prems by (cases "f x" p rule: linorder_cases) auto
  qed (auto intro: prems(1))
qed simp_all
termination by (relation "Wellfounded.measure (size \<circ> fst \<circ> snd)") simp_all

private lemma groupsort_locale: "groupsort f merge g" by unfold_locales

private lemmas part_aux_induct = part_aux.induct[split_format (complete), OF groupsort_locale]

private definition part where "part p xs = part_aux (f p) xs ([], [p], [])"

private lemma part: 
  "part p xs = (rev (filter (\<lambda>x. f x < f p) xs), 
     p # filter (\<lambda>x. f x = f p) xs, rev (filter (\<lambda>x. f x > f p) xs))"
proof-
  {
    fix p xs ls eq gs
    have "fst (part_aux p xs (ls, eq, gs)) = rev (filter (\<lambda>x. f x < p) xs) @ ls"
      by (induction p xs ls eq gs rule: part_aux_induct) simp_all
  } note A = this
  {
    fix p xs ls eq gs
    have "snd (snd (part_aux p xs (ls, eq, gs))) = rev (filter (\<lambda>x. f x > p) xs) @ gs"
      by (induction p xs ls eq gs rule: part_aux_induct) simp_all
  } note B = this
  {
    fix p xs ls eq gs
    have "fst (snd (part_aux p xs (ls, eq, gs))) = eq @ filter (\<lambda>x. f x = p) xs"
      by (induction p xs ls eq gs rule: part_aux_induct) auto
  } note C = this
  note ABC = A B C
  from ABC[of "f p" xs "[]" "[p]" "[]"] show ?thesis unfolding part_def
    by (intro prod_eqI) simp_all
qed

private function sort :: "'a list \<Rightarrow> 'a list" where
  "sort [] = []"
| "sort (x#xs) = (case part x xs of (ls, eq, gs) \<Rightarrow> sort ls @ eq @ sort gs)"
by pat_completeness simp_all
termination by (relation "Wellfounded.measure length") (simp_all add: part less_Suc_eq_le)

private lemma filter_mset_union:
  assumes "\<And>x. x \<in># A \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> False"
  shows "filter_mset P A + filter_mset Q A = filter_mset (\<lambda>x. P x \<or> Q x) A" (is "?lhs = ?rhs")
  using assms by (auto simp add: count_eq_zero_iff intro!: multiset_eqI) blast

private lemma multiset_of_sort: "mset (sort xs) = mset xs"
proof (induction xs rule: sort.induct)
  case (2 x xs)
  let ?M = "\<lambda>oper. {#y:# mset xs. oper (f y) (f x)#}"
  from 2 have "mset (sort (x#xs)) = ?M (op <) + ?M (op =) + ?M (op >) + {#x#}"
    by (simp add: part Multiset.union_assoc mset_filter)
  also have "?M (op <) + ?M (op =) + ?M (op >) = mset xs"
    by ((subst filter_mset_union, force)+, subst multiset_eq_iff, force)
  finally show ?case by simp
qed simp

private lemma g_sort: "g (sort xs) = g xs"
  by (intro g_cong multiset_of_sort)

private lemma set_sort: "set (sort xs) = set xs"
  using arg_cong[OF multiset_of_sort[of xs], of "set_mset"] by (simp only: set_mset_mset)

private lemma sorted_all_equal: "(\<And>x. x \<in> set xs \<Longrightarrow> x = y) \<Longrightarrow> sorted xs"
  by (induction xs) (auto simp: sorted_Cons)

private lemma sorted_sort: "sorted (map f (sort xs))"
apply (induction xs rule: sort.induct)
apply simp
apply (simp only: sorted_append sorted_Cons sort.simps part map_append split)
apply (intro conjI TrueI)
using sorted_map_same by (auto simp: set_sort sorted_Cons)



private fun group where
  "group [] = []"
| "group (x#xs) = (case partition (\<lambda>y. f y = f x) xs of (xs', xs'') \<Rightarrow> 
                     fold merge xs' x # group xs'')"

private lemma f_fold_merge: "(\<And>y. y \<in> set xs \<Longrightarrow> f y = f x) \<Longrightarrow> f (fold merge xs x) = f x"
  by (induction xs rule: rev_induct) (auto simp: f_merge)

private lemma f_group: "x \<in> set (group xs) \<Longrightarrow> \<exists>x'\<in>set xs. f x = f x'"
proof (induction xs rule: group.induct)
  case (2 x' xs)
  hence "x = fold merge [y\<leftarrow>xs . f y = f x'] x' \<or> x \<in> set (group [xa\<leftarrow>xs . f xa \<noteq> f x'])"
    by (auto simp: o_def)
  thus ?case
  proof
    assume "x = fold merge [y\<leftarrow>xs . f y = f x'] x'"
    also have "f ... = f x'" by (rule f_fold_merge) simp
    finally show ?thesis by simp
  next
    assume "x \<in> set (group [xa\<leftarrow>xs . f xa \<noteq> f x'])"
    from 2(1)[OF _ this] have "\<exists>x'\<in>set [xa\<leftarrow>xs . f xa \<noteq> f x']. f x = f x'" by (simp add: o_def)
    thus ?thesis by force
  qed
qed simp

private lemma sorted_group: "sorted (map f xs) \<Longrightarrow> sorted (map f (group xs))"
proof (induction xs rule: group.induct)
  case (2 x xs)
  {
    fix x' assume x': "x' \<in> set (group [y\<leftarrow>xs . f y \<noteq> f x])"
    with f_group obtain x'' where x'': "x'' \<in> set xs" "f x' = f x''" by force
    have "f (fold merge [y\<leftarrow>xs . f y = f x] x) = f x"
      by (subst f_fold_merge) simp_all
    also from 2(2) x'' have "... \<le> f x'" by (auto simp: sorted_Cons) 
    finally have "f (fold merge [y\<leftarrow>xs . f y = f x] x) \<le> f x'" .
  }
  moreover from 2(2) have "sorted (map f (group [xa\<leftarrow>xs . f xa \<noteq> f x]))"
    by (intro 2 sorted_filter) (simp_all add: sorted_Cons o_def)
  ultimately show ?case by (simp add: o_def sorted_Cons)
qed simp_all

private lemma distinct_group: "distinct (map f (group xs))"
proof (induction xs rule: group.induct)
  case (2 x xs)
  have "distinct (map f (group [xa\<leftarrow>xs . f xa \<noteq> f x]))" by (intro 2) (simp_all add: o_def)
  moreover have "f (fold merge [y\<leftarrow>xs . f y = f x] x) \<notin> set (map f (group [xa\<leftarrow>xs . f xa \<noteq> f x]))"
    by (rule notI, subst (asm) f_fold_merge) (auto dest: f_group)
  ultimately show ?case by (simp add: o_def)
qed simp

private lemma g_fold_same:
  assumes "\<And>z. z \<in> set xs \<Longrightarrow> f z = f x"
  shows   "g (fold merge xs x # ys) = g (x#xs@ys)"
using assms
proof (induction xs arbitrary: x)
  case (Cons y xs)
  have "g (x # y # xs @ ys) = g (y # x # xs @ ys)" by (intro g_cong) (auto simp: add_ac)
  also have "y # x # xs @ ys = [y,x] @ xs @ ys" by simp
  also from Cons.prems have "g ... = g ([merge y x] @ xs @ ys)" 
    by (intro g_append_cong g_merge) auto
  also have "[merge y x] @ xs @ ys = merge y x # xs @ ys" by simp
  also from Cons.prems have "g ... = g (fold merge xs (merge y x) # ys)"
    by (intro Cons.IH[symmetric]) (auto simp: f_merge)
  also have "... = g (fold merge (y # xs) x # ys)" by simp
  finally show ?case by simp
qed simp

private lemma g_group: "g (group xs) = g xs"
proof (induction xs rule: group.induct)
  case (2 x xs)
  have "g (group (x#xs)) = g (fold merge [y\<leftarrow>xs . f y = f x] x # group [xa\<leftarrow>xs . f xa \<noteq> f x])"
    by (simp add: o_def)
  also have "... = g (x # [y\<leftarrow>xs . f y = f x] @ group [y\<leftarrow>xs . f y \<noteq> f x])"
    by (intro g_fold_same) simp_all
  also have "... = g ((x # [y\<leftarrow>xs . f y = f x]) @ group [y\<leftarrow>xs . f y \<noteq> f x])" (is "_ = ?A") by simp
  also from 2 have "g (group [y\<leftarrow>xs . f y \<noteq> f x]) = g [y\<leftarrow>xs . f y \<noteq> f x]" by (simp add: o_def)
  hence "?A = g ((x # [y\<leftarrow>xs . f y = f x]) @ [y\<leftarrow>xs . f y \<noteq> f x])"
    by (intro g_append_cong) simp_all
  also have "... = g (x#xs)" by (intro g_cong) simp_all
  finally show ?case .
qed simp


function group_part_aux :: 
  "'b \<Rightarrow> 'a list \<Rightarrow> ('a list) \<times> 'a \<times> ('a list) \<Rightarrow> ('a list) \<times> 'a \<times> ('a list)" 
where
  "group_part_aux p [] (ls, eq, gs) = (ls, eq, gs)"
| "f x < p \<Longrightarrow> group_part_aux p (x#xs) (ls, eq, gs) = group_part_aux p xs (x#ls, eq, gs)"
| "f x > p \<Longrightarrow> group_part_aux p (x#xs) (ls, eq, gs) = group_part_aux p xs (ls, eq, x#gs)"
| "f x = p \<Longrightarrow> group_part_aux p (x#xs) (ls, eq, gs) = group_part_aux p xs (ls, merge x eq, gs)"
proof (clarify, goal_cases)
  case prems: (1 P p xs ls eq gs)
  show ?case
  proof (cases xs)
    fix x xs' assume "xs = x # xs'"
    thus ?thesis using prems by (cases "f x" p rule: linorder_cases) auto
  qed (auto intro: prems(1))
qed simp_all
termination by (relation "Wellfounded.measure (size \<circ> fst \<circ> snd)") simp_all

private lemmas group_part_aux_induct = 
  group_part_aux.induct[split_format (complete), OF groupsort_locale]

definition group_part where "group_part p xs = group_part_aux (f p) xs ([], p, [])"

private lemma group_part: 
  "group_part p xs = (rev (filter (\<lambda>x. f x < f p) xs), 
     fold merge (filter (\<lambda>x. f x = f p) xs) p, rev (filter (\<lambda>x. f x > f p) xs))"
proof-
  {
    fix p xs ls eq gs
    have "fst (group_part_aux p xs (ls, eq, gs)) = rev (filter (\<lambda>x. f x < p) xs) @ ls"
      by (induction p xs ls eq gs rule: group_part_aux_induct) simp_all
  } note A = this
  {
    fix p xs ls eq gs
    have "snd (snd (group_part_aux p xs (ls, eq, gs))) = rev (filter (\<lambda>x. f x > p) xs) @ gs"
      by (induction p xs ls eq gs rule: group_part_aux_induct) simp_all
  } note B = this
  {
    fix p xs ls eq gs
    have "fst (snd (group_part_aux p xs (ls, eq, gs))) = 
            fold merge (filter (\<lambda>x. f x = p) xs) eq"
      by (induction p xs ls eq gs rule: group_part_aux_induct) auto
  } note C = this
  note ABC = A B C
  from ABC[of "f p" xs "[]" "p" "[]"] show ?thesis unfolding group_part_def
    by (intro prod_eqI) simp_all
qed


function group_sort :: "'a list \<Rightarrow> 'a list" where
  "group_sort [] = []"
| "group_sort (x#xs) = (case group_part x xs of (ls, eq, gs) \<Rightarrow> group_sort ls @ eq # group_sort gs)"
by pat_completeness simp_all
termination by (relation "Wellfounded.measure length") (simp_all add: group_part less_Suc_eq_le)

private lemma group_append:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x \<noteq> f y"
  shows   "group (xs @ ys) = group xs @ group ys"
using assms
proof (induction xs arbitrary: ys rule: length_induct)
  case (1 xs')
  hence IH: "\<And>x xs ys. length xs < length xs' \<Longrightarrow> (\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x \<noteq> f y)
                \<Longrightarrow> group (xs @ ys) = group xs @ group ys" by blast
  show ?case
  proof (cases xs')
    case (Cons x xs)
    note [simp] = this
    have "group (xs' @ ys) = fold merge [y\<leftarrow>xs@ys . f y = f x] x #
            group ([xa\<leftarrow>xs . f xa \<noteq> f x] @ [xa\<leftarrow>ys . f xa \<noteq> f x])" by (simp add: o_def)
    also from 1(2) have "[y\<leftarrow>xs@ys . f y = f x] = [y\<leftarrow>xs . f y = f x]"
      by (force simp: filter_empty_conv)
    also from 1(2) have "[xa\<leftarrow>ys . f xa \<noteq> f x] = ys" by (force simp: filter_id_conv)
    also have "group ([xa\<leftarrow>xs . f xa \<noteq> f x] @ ys) =
               group [xa\<leftarrow>xs . f xa \<noteq> f x] @ group ys" using 1(2)
      by (intro IH) (simp_all add: less_Suc_eq_le)
    finally show ?thesis by (simp add: o_def)
  qed simp
qed

private lemma group_empty_iff [simp]: "group xs = [] \<longleftrightarrow> xs = []"
  by (induction xs rule: group.induct) auto

lemma group_sort_correct: "group_sort xs = group (sort xs)"
proof (induction xs rule: group_sort.induct)
  case (2 x xs)
  have "group_sort (x#xs) = 
          group_sort (rev [xa\<leftarrow>xs . f xa < f x]) @ group (x#[xa\<leftarrow>xs . f xa = f x]) @
          group_sort (rev [xa\<leftarrow>xs . f x < f xa])" by (simp add: group_part)
  also have "group_sort (rev [xa\<leftarrow>xs . f xa < f x]) = group (sort (rev [xa\<leftarrow>xs . f xa < f x]))"
    by (rule 2) (simp_all add: group_part)
  also have "group_sort (rev [xa\<leftarrow>xs . f xa > f x]) = group (sort (rev [xa\<leftarrow>xs . f xa > f x]))"
    by (rule 2) (simp_all add: group_part)
  also have "group (x#[xa\<leftarrow>xs . f xa = f x]) @ group (sort (rev [xa\<leftarrow>xs . f xa > f x])) =
             group ((x#[xa\<leftarrow>xs . f xa = f x]) @ sort (rev [xa\<leftarrow>xs . f xa > f x]))"
    by (intro group_append[symmetric]) (auto simp: set_sort)
  also have "group (sort (rev [xa\<leftarrow>xs . f xa < f x])) @ ... = 
             group (sort (rev [xa\<leftarrow>xs . f xa < f x]) @ (x#[xa\<leftarrow>xs . f xa = f x]) @
                 sort (rev [xa\<leftarrow>xs . f xa > f x]))"
    by (intro group_append[symmetric]) (auto simp: set_sort)
  also have "sort (rev [xa\<leftarrow>xs . f xa < f x]) @ (x#[xa\<leftarrow>xs . f xa = f x]) @
                 sort (rev [xa\<leftarrow>xs . f xa > f x]) = sort (x # xs)" by (simp add: part)
  finally show ?case .
qed simp


lemma sorted_group_sort: "sorted (map f (group_sort xs))"
  by (auto simp: group_sort_correct intro!: sorted_group sorted_sort)

lemma distinct_group_sort: "distinct (map f (group_sort xs))"
  by (simp add: group_sort_correct distinct_group)

lemma g_group_sort: "g (group_sort xs) = g xs"
  by (simp add: group_sort_correct g_group g_sort)

lemmas [simp del] = group_sort.simps group_part_aux.simps

end
end

end
