(*
  File:     List_Inversions.thy
  Author:   Manuel Eberl, TU München

  A formalisation of inversions of a list and the O(n log n) divide-and-conquer algorithm
  to count them.
*)
section \<open>The Inversions of a List\<close>
theory List_Inversions
  imports Main "HOL-Library.Permutations"
begin

subsection \<open>Definition of inversions\<close>

context preorder
begin

text \<open>
  We define inversions as pair of indices w.\,r.\,t.\ a preorder.
\<close>
inductive_set inversions :: "'a list \<Rightarrow> (nat \<times> nat) set" for xs :: "'a list" where
  "i < j \<Longrightarrow> j < length xs \<Longrightarrow> less (xs ! j) (xs ! i) \<Longrightarrow> (i, j) \<in> inversions xs"

lemma inversions_subset: "inversions xs \<subseteq> Sigma {..<length xs} (\<lambda>i. {i<..<length xs})"
  by (auto simp: inversions.simps)

lemma finite_inversions [intro]: "finite (inversions xs)"
  by (rule finite_subset[OF inversions_subset]) auto

lemma inversions_altdef: "inversions xs = {(i, j). i < j \<and> j < length xs \<and> less (xs ! j) (xs ! i)}"
  by (auto simp: inversions.simps)

lemma inversions_code:
  "inversions xs =
     Sigma {..<length xs} (\<lambda>i. Set.filter (\<lambda>j. less (xs ! j) (xs ! i)) {i<..<length xs})"
  by (auto simp: inversions_altdef)

lemmas (in -) [code] = inversions_code

lemma inversions_trivial [simp]: "length xs \<le> Suc 0 \<Longrightarrow> inversions xs = {}"
  by (auto simp: inversions_altdef)

lemma inversions_imp_less:
  "z \<in> inversions xs \<Longrightarrow> fst z < snd z"
  "z \<in> inversions xs \<Longrightarrow> snd z < length xs"
  by (auto simp: inversions_altdef)

lemma inversions_Nil [simp]: "inversions [] = {}"
  by (auto simp: inversions_altdef)

lemma inversions_Cons:
  "inversions (x # xs) =
     (\<lambda>j. (0, j + 1)) ` {j\<in>{..<length xs}. less (xs ! j) x} \<union>
     map_prod Suc Suc ` inversions xs" (is "_ = ?rhs")
proof -
  have "z \<in> inversions (x # xs) \<longleftrightarrow> z \<in> ?rhs" for z
    by (cases z) (auto simp: inversions_altdef map_prod_def nth_Cons split: nat.splits)
  thus ?thesis by blast
qed


text \<open>
  The following function returns the inversions between two lists, i.\,e.\ all pairs of
  an element in the first list with an element in the second list such that the former
  is greater than the latter.
\<close>
definition inversions_between :: "'a list \<Rightarrow> 'a list \<Rightarrow> (nat \<times> nat) set" where
  "inversions_between xs ys =
     {(i, j) \<in> {..<length xs}\<times>{..<length ys}. less (ys ! j) (xs ! i)}"

lemma finite_inversions_between [intro]: "finite (inversions_between xs ys)"
    by (rule finite_subset[of _ "{..<length xs} \<times> {..<length xs + length ys}"])
       (auto simp: inversions_between_def)

lemma inversions_between_Nil [simp]:
  "inversions_between [] ys = {}"
  "inversions_between xs [] = {}"
  by (simp_all add: inversions_between_def)

text \<open>
  We can now show the following equality for the inversions of the concatenation of two lists:
\<close>
proposition inversions_append:
  fixes xs ys
  defines "m \<equiv> length xs" and "n \<equiv> length ys"
  shows "inversions (xs @ ys) =
           inversions xs \<union> map_prod ((+) m) ((+) m) ` inversions ys \<union>
           map_prod id ((+) m) ` inversions_between xs ys"
        (is "_ = ?rhs")
proof -
  note defs = inversions_altdef inversions_between_def m_def n_def map_prod_def
  have "z \<in> inversions (xs @ ys) \<longleftrightarrow> z \<in> ?rhs" for z
  proof
    assume "z \<in> inversions (xs @ ys)"
    then obtain i j where [simp]: "z = (i, j)"
                      and ij: "i < j" "j < m + n" "less ((xs @ ys) ! j) ((xs @ ys) ! i)"
      by (cases z) (auto simp: inversions_altdef m_def n_def)
    from ij consider "j < m" | "i \<ge> m" | "i < m" "j \<ge> m" by linarith
    thus "z \<in> ?rhs"
    proof cases
      assume "i < m" "j \<ge> m"
      define j' where "j' = j - m"
      have [simp]: "j = m + j'"
        using \<open>j \<ge> m\<close> by (simp add: j'_def)
      from ij and \<open>i < m\<close> show ?thesis
        by (auto simp: inversions_altdef map_prod_def inversions_between_def nth_append m_def n_def)
    next
      assume "i \<ge> m"
      define i' j' where "i' = i - m" and "j' = j - m"
      have [simp]: "i = m + i'" "j = m + j'"
        using \<open>i < j\<close> and \<open>i \<ge> m\<close> by (simp_all add: i'_def j'_def)
      from ij show ?thesis
        by (auto simp: inversions_altdef map_prod_def nth_append m_def n_def)
    qed (use ij in \<open>auto simp: nth_append defs\<close>)
  qed (auto simp: nth_append defs)
  thus ?thesis by blast
qed


subsection \<open>Counting inversions\<close>

text \<open>
  We now define versions of @{const inversions} and @{const inversions_between} that
  only return the \<^emph>\<open>number\<close> of inversions.
\<close>
definition inversion_number :: "'a list \<Rightarrow> nat" where
  "inversion_number xs = card (inversions xs)"

definition inversion_number_between where
  "inversion_number_between xs ys = card (inversions_between xs ys)"

lemma inversions_between_code:
  "inversions_between xs ys =
     Set.filter (\<lambda>(i,j). less (ys ! j) (xs ! i)) ({..<length xs}\<times>{..<length ys})"
  by (auto simp: inversions_between_def)

lemmas (in -) [code] = inversions_between_code

lemma inversion_number_Nil [simp]: "inversion_number [] = 0"
  by (simp add: inversion_number_def)

lemma inversion_number_trivial [simp]: "length xs \<le> Suc 0 \<Longrightarrow> inversion_number xs = 0"
  by (auto simp: inversion_number_def)

lemma inversion_number_between_Nil [simp]:
  "inversion_number_between [] ys = 0"
  "inversion_number_between xs [] = 0"
  by (simp_all add: inversion_number_between_def)

text \<open>
  We again get the following nice equation for the number of inversions of a concatenation:
\<close>
proposition inversion_number_append:
  "inversion_number (xs @ ys) =
     inversion_number xs + inversion_number ys + inversion_number_between xs ys"
proof -
  define m n where "m = length xs" and "n = length ys"
  let ?A = "inversions xs"
  let ?B = "map_prod ((+) m) ((+) m) ` inversions ys"
  let ?C = "map_prod id ((+) m) ` inversions_between xs ys"

  have "inversion_number (xs @ ys) = card (?A \<union> ?B \<union> ?C)"
    by (simp add: inversion_number_def inversions_append m_def)
  also have "\<dots> = card (?A \<union> ?B) + card ?C"
    by (intro card_Un_disjoint finite_inversions finite_inversions_between finite_UnI finite_imageI)
       (auto simp: inversions_altdef inversions_between_def m_def n_def)
  also have "card (?A \<union> ?B) = inversion_number xs + card ?B" unfolding inversion_number_def
    by (intro card_Un_disjoint finite_inversions finite_UnI finite_imageI)
       (auto simp: inversions_altdef m_def n_def)
  also have "card ?B = inversion_number ys" unfolding inversion_number_def
    by (intro card_image) (auto simp: map_prod_def inj_on_def)
  also have "card ?C = inversion_number_between xs ys"
    unfolding inversion_number_between_def by (intro card_image inj_onI) (auto simp: map_prod_def)
  finally show ?thesis .
qed


subsection \<open>Stability of inversions between lists under permutations\<close>

text \<open>
  A crucial fact for counting list inversions with merge sort is that the number
  of inversions \<^emph>\<open>between\<close> two lists does not change when the lists are permuted. This is
  true because the set of inversions commutes with the act of permuting the list:
\<close>
lemma inversions_between_permute1:
  assumes "\<pi> permutes {..<length xs}"
  shows   "inversions_between (permute_list \<pi> xs) ys =
             map_prod (inv \<pi>) id ` inversions_between xs ys"
proof -
  from assms have [simp]: "\<pi> i < length xs" if "i < length xs" "\<pi> permutes {..<length xs}" for i \<pi>
    using permutes_in_image[OF that(2)] that by auto
  have *: "inv \<pi> permutes {..<length xs}"
    using assms by (rule permutes_inv)
  from assms * show ?thesis unfolding inversions_between_def map_prod_def
    by (force simp: image_iff permute_list_nth permutes_inverses intro: exI[of _ "\<pi> i" for i])
qed

lemma inversions_between_permute2:
  assumes "\<pi> permutes {..<length ys}"
  shows   "inversions_between xs (permute_list \<pi> ys) =
             map_prod id (inv \<pi>) ` inversions_between xs ys"
proof -
  from assms have [simp]: "\<pi> i < length ys" if "i < length ys" "\<pi> permutes {..<length ys}" for i \<pi>
    using permutes_in_image[OF that(2)] that by auto
  have *: "inv \<pi> permutes {..<length ys}"
    using assms by (rule permutes_inv)
  from assms * show ?thesis unfolding inversions_between_def map_prod_def
    by (force simp: image_iff permute_list_nth permutes_inverses intro: exI[of _ "\<pi> i" for i])
qed

proposition inversions_between_permute:
  assumes "\<pi>1 permutes {..<length xs}" and "\<pi>2 permutes {..<length ys}"
  shows   "inversions_between (permute_list \<pi>1 xs) (permute_list \<pi>2 ys) =
             map_prod (inv \<pi>1) (inv \<pi>2) ` inversions_between xs ys"
  by (simp add: inversions_between_permute1 inversions_between_permute2 assms
                map_prod_def image_image case_prod_unfold)

corollary inversion_number_between_permute:
  assumes "\<pi>1 permutes {..<length xs}" and "\<pi>2 permutes {..<length ys}"
  shows   "inversion_number_between (permute_list \<pi>1 xs) (permute_list \<pi>2 ys) =
             inversion_number_between xs ys"
proof -
  have "inversion_number_between (permute_list \<pi>1 xs) (permute_list \<pi>2 ys) =
          card (map_prod (inv \<pi>1) (inv \<pi>2) ` inversions_between xs ys)"
    by (simp add: inversion_number_between_def inversions_between_permute assms)
  also have "\<dots> = inversion_number_between xs ys"
    unfolding inversion_number_between_def using assms[THEN permutes_inj_on[OF permutes_inv]]
    by (intro card_image inj_onI) (auto simp: map_prod_def)
  finally show ?thesis .
qed

text \<open>
  The following form of the above theorem is nicer to apply since it has the form of a 
  congruence rule.
\<close>
corollary inversion_number_between_cong_mset:
  assumes "mset xs = mset xs'" and "mset ys = mset ys'"
  shows   "inversion_number_between xs ys = inversion_number_between xs' ys'"
proof -
  obtain \<pi>1 \<pi>2 where \<pi>12: "\<pi>1 permutes {..<length xs'}" "xs = permute_list \<pi>1 xs'"
                          "\<pi>2 permutes {..<length ys'}" "ys = permute_list \<pi>2 ys'"
    using assms[THEN mset_eq_permutation] by metis
  thus ?thesis by (simp add: inversion_number_between_permute)
qed


subsection \<open>Inversions between sorted lists\<close>

text \<open>
  Another fact that is crucial to the efficient computation of the inversion number is this:
  If we have two sorted lists, we can reduce computing the inversions by inspecting the 
  first elements and deleting one of them.
\<close>
lemma inversions_between_Cons_Cons:
  assumes "sorted_wrt less_eq (x # xs)" and "sorted_wrt less_eq (y # ys)"
  shows   "inversions_between (x # xs) (y # ys) =
             (if \<not>less y x then
                map_prod Suc id ` inversions_between xs (y # ys)
              else
                {..<length (x#xs)} \<times> {0} \<union>
                map_prod id Suc ` inversions_between (x # xs) ys)"
  using assms  unfolding inversions_between_def map_prod_def
  by (auto, (auto simp: set_conv_nth nth_Cons less_le_not_le image_iff 
                  intro: order_trans split: nat.splits)?)
  (* A bit fragile, but doing this manually is annoying *)

text \<open>
  This leads to the following analogous equation for counting the inversions between two
  sorted lists. Note that a single step of this only takes constant time (assuming we 
  pre-computed the lengths of the lists) so that the entire function runs in linear time.
\<close>
lemma inversion_number_between_Cons_Cons:
  assumes "sorted_wrt less_eq (x # xs)" and "sorted_wrt less_eq (y # ys)"
  shows   "inversion_number_between (x # xs) (y # ys) =
             (if \<not>less y x then
                inversion_number_between xs (y # ys)
              else
                inversion_number_between (x # xs) ys + length (x # xs))"
proof (cases "less y x")
  case False
  hence "inversion_number_between (x # xs) (y # ys) = 
           card (map_prod Suc id ` inversions_between xs (y # ys))"
    by (simp add: inversion_number_between_def inversions_between_Cons_Cons[OF assms])
  also have "\<dots> = inversion_number_between xs (y # ys)"
    unfolding inversion_number_between_def by (intro card_image inj_onI) (auto simp: map_prod_def)
  finally show ?thesis using False by simp
next
  case True
  hence "inversion_number_between (x # xs) (y # ys) =
           card ({..<length (x # xs)} \<times> {0} \<union> map_prod id Suc ` inversions_between (x # xs) ys)"
    by (simp add: inversion_number_between_def inversions_between_Cons_Cons[OF assms])
  also have "\<dots> = length (x # xs) + card (map_prod id Suc ` inversions_between (x # xs) ys)"
    by (subst card_Un_disjoint) auto
  also have "card (map_prod id Suc ` inversions_between (x # xs) ys) =
               inversion_number_between (x # xs) ys"
    unfolding inversion_number_between_def by (intro card_image inj_onI) (auto simp: map_prod_def)
  finally show ?thesis using True by simp
qed

text \<open>
  We now define a function to compute the inversion number between two lists that are
  assumed to be sorted using the equalities we just derived.
\<close>
fun inversion_number_between_sorted :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "inversion_number_between_sorted [] ys = 0"
| "inversion_number_between_sorted xs [] = 0"
| "inversion_number_between_sorted (x # xs) (y # ys) =
             (if \<not>less y x then
                inversion_number_between_sorted xs (y # ys)
              else
                inversion_number_between_sorted (x # xs) ys + length (x # xs))"

theorem inversion_number_between_sorted_correct:
  "sorted_wrt less_eq xs \<Longrightarrow> sorted_wrt less_eq ys \<Longrightarrow>
     inversion_number_between_sorted xs ys = inversion_number_between xs ys"
  by (induction xs ys rule: inversion_number_between_sorted.induct)
     (simp_all add: inversion_number_between_Cons_Cons)

end


subsection \<open>Merge sort\<close>

(* TODO: Could be replaced by mergesort from HOL-Library in Isabelle 2019. *)
text \<open>
  For convenience, we first define a simple merge sort that does not compute the inversions.
  At this point, we need to start assuming a linear ordering since the merging function
  does not work otherwise.
\<close>

context linorder
begin

definition split_list
  where "split_list xs = (let n = length xs div 2 in (take n xs, drop n xs))"

fun merge_lists :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge_lists [] ys = ys"
| "merge_lists xs [] = xs"
| "merge_lists (x # xs) (y # ys) =
    (if less_eq x y then x # merge_lists xs (y # ys) else y # merge_lists (x # xs) ys)"

lemma set_merge_lists [simp]: "set (merge_lists xs ys) = set xs \<union> set ys"
  by (induction xs ys rule: merge_lists.induct) auto

lemma mset_merge_lists [simp]: "mset (merge_lists xs ys) = mset xs + mset ys"
  by (induction xs ys rule: merge_lists.induct) auto

lemma sorted_merge_lists [simp, intro]:
  "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> sorted (merge_lists xs ys)"
  by (induction xs ys rule: merge_lists.induct) auto


fun merge_sort :: "'a list \<Rightarrow> 'a list" where
  "merge_sort xs =
    (if length xs \<le> 1 then
       xs 
     else
       merge_lists (merge_sort (take (length xs div 2) xs))
                   (merge_sort (drop (length xs div 2) xs)))"

lemmas [simp del] = merge_sort.simps

lemma merge_sort_trivial [simp]: "length xs \<le> Suc 0 \<Longrightarrow> merge_sort xs = xs"
  by (subst merge_sort.simps) auto

theorem mset_merge_sort [simp]: "mset (merge_sort xs) = mset xs"
  by (induction xs rule: merge_sort.induct)
     (subst merge_sort.simps, auto simp flip: mset_append)

corollary set_merge_sort [simp]: "set (merge_sort xs) = set xs"
  by (rule mset_eq_setD) simp_all

theorem sorted_merge_sort [simp, intro]: "sorted (merge_sort xs)"
  by (induction xs rule: merge_sort.induct)
     (subst merge_sort.simps, use sorted01 in auto)

lemma inversion_number_between_code:
  "inversion_number_between xs ys = inversion_number_between_sorted (sort xs) (sort ys)"
  by (subst inversion_number_between_sorted_correct)
     (simp_all add: sorted_sorted_wrt [symmetric] cong: inversion_number_between_cong_mset)

lemmas (in -) [code_unfold] = inversion_number_between_code


subsection \<open>Merge sort with inversion counting\<close>

text \<open>
  Finally, we can put together all the components and define a variant of merge sort that
  counts the number of inversions in the original list:
\<close>
function sort_and_count_inversions :: "'a list \<Rightarrow> 'a list \<times> nat" where
  "sort_and_count_inversions xs =
     (if length xs \<le> 1 then
        (xs, 0)
      else
        let (xs1, xs2) = split_list xs;
            (xs1', m) = sort_and_count_inversions xs1;
            (xs2', n) = sort_and_count_inversions xs2
        in
            (merge_lists xs1' xs2', m + n + inversion_number_between_sorted xs1' xs2'))"
  by auto
termination by (relation "measure length") (auto simp: split_list_def Let_def)

lemmas [simp del] = sort_and_count_inversions.simps


text \<open>
  The projection of this function to the first component is simply the standard merge sort
  algorithm that we defined and proved correct before.
\<close>
theorem fst_sort_and_count_inversions [simp]:
  "fst (sort_and_count_inversions xs) = merge_sort xs"
  by (induction xs rule: length_induct)
     (subst sort_and_count_inversions.simps, subst merge_sort.simps,
      simp_all add: split_list_def case_prod_unfold Let_def)

text \<open>
  The projection to the second component is the inversion number.
\<close>
theorem snd_sort_and_count_inversions [simp]:
  "snd (sort_and_count_inversions xs) = inversion_number xs"
proof (induction xs rule: length_induct)
  case (1 xs)
  show ?case
  proof (cases "length xs \<le> 1")
    case False
    have "xs = take (length xs div 2) xs @ drop (length xs div 2) xs" by simp
    also have "inversion_number \<dots> = snd (sort_and_count_inversions xs)"
      by (subst inversion_number_append, subst sort_and_count_inversions.simps)
         (use False 1 in \<open>auto simp: Let_def split_list_def case_prod_unfold 
                                     inversion_number_between_sorted_correct
                                     sorted_sorted_wrt [symmetric]
                               cong: inversion_number_between_cong_mset\<close>)
    finally show ?thesis ..
  qed (auto simp: sort_and_count_inversions.simps)
qed

lemmas (in -) [code_unfold] = snd_sort_and_count_inversions [symmetric]

end

end