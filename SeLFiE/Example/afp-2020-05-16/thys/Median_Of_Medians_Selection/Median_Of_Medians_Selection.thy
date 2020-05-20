(*
  File:     Median_Of_Medians_Selection.thy
  Author:   Manuel Eberl, TU München

  The median-of-medians selection algorithm, which runs deterministically in linear time.
*)
section \<open>The Median-of-Medians Selection Algorithm\<close>
theory Median_Of_Medians_Selection
  imports Complex_Main "HOL-Library.Multiset"
begin

subsection \<open>Some facts about lists and multisets\<close>

lemma mset_concat: "mset (concat xss) = sum_list (map mset xss)"
  by (induction xss) simp_all

lemma set_mset_sum_list [simp]: "set_mset (sum_list xs) = (\<Union>x\<in>set xs. set_mset x)"
  by (induction xs) auto

lemma filter_mset_image_mset:
  "filter_mset P (image_mset f A) = image_mset f (filter_mset (\<lambda>x. P (f x)) A)"
  by (induction A) auto

lemma filter_mset_sum_list: "filter_mset P (sum_list xs) = sum_list (map (filter_mset P) xs)"
  by (induction xs) simp_all

lemma sum_mset_mset_mono: 
  assumes "(\<And>x. x \<in># A \<Longrightarrow> f x \<subseteq># g x)"
  shows   "(\<Sum>x\<in>#A. f x) \<subseteq># (\<Sum>x\<in>#A. g x)"
  using assms by (induction A) (auto intro!: subset_mset.add_mono)

lemma mset_filter_mono:
  assumes "A \<subseteq># B" "\<And>x. x \<in># A \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows   "filter_mset P A \<subseteq># filter_mset Q B"
  by (rule mset_subset_eqI) (insert assms, auto simp: mset_subset_eq_count count_eq_zero_iff)

lemma size_mset_sum_mset_distrib: "size (sum_mset A :: 'a multiset) = sum_mset (image_mset size A)"
  by (induction A) auto

lemma sum_mset_mono:
  assumes "\<And>x. x \<in># A \<Longrightarrow> f x \<le> (g x :: 'a :: {ordered_ab_semigroup_add,comm_monoid_add})"
  shows   "(\<Sum>x\<in>#A. f x) \<le> (\<Sum>x\<in>#A. g x)"
  using assms by (induction A) (auto intro!: add_mono)

lemma filter_mset_is_empty_iff: "filter_mset P A = {#} \<longleftrightarrow> (\<forall>x. x \<in># A \<longrightarrow> \<not>P x)"
  by (auto simp: multiset_eq_iff count_eq_zero_iff)

lemma sorted_filter_less_subset_take:
  assumes "sorted xs" "i < length xs"
  shows   "{# x \<in># mset xs. x < xs ! i #} \<subseteq># mset (take i xs)"
  using assms
proof (induction xs arbitrary: i rule: list.induct)
  case (Cons x xs i)
  show ?case
  proof (cases i)
    case 0
    thus ?thesis using Cons.prems by (auto simp: filter_mset_is_empty_iff)
  next
    case (Suc i')
    have "{#y \<in># mset (x # xs). y < (x # xs) ! i#} \<subseteq># add_mset x {#y \<in># mset xs. y < xs ! i'#}"
      using Suc Cons.prems by (auto)
    also have "\<dots> \<subseteq># add_mset x (mset (take i' xs))"
      unfolding mset_subset_eq_add_mset_cancel using Cons.prems Suc
      by (intro Cons.IH) (auto)
    also have "\<dots> = mset (take i (x # xs))" by (simp add: Suc)
    finally show ?thesis .
  qed
qed auto

lemma sorted_filter_greater_subset_drop:
  assumes "sorted xs" "i < length xs"
  shows   "{# x \<in># mset xs. x > xs ! i #} \<subseteq># mset (drop (Suc i) xs)"
  using assms
proof (induction xs arbitrary: i rule: list.induct)
  case (Cons x xs i)
  show ?case
  proof (cases i)
    case 0
    thus ?thesis by (auto simp: sorted_append filter_mset_is_empty_iff)
  next
    case (Suc i')
    have "{#y \<in># mset (x # xs). y > (x # xs) ! i#} \<subseteq># {#y \<in># mset xs. y > xs ! i'#}"
      using Suc Cons.prems by (auto simp: set_conv_nth)
    also have "\<dots> \<subseteq># mset (drop (Suc i') xs)"
      using Cons.prems Suc by (intro Cons.IH) (auto)
    also have "\<dots> = mset (drop (Suc i) (x # xs))" by (simp add: Suc)
    finally show ?thesis .
  qed
qed auto


subsection \<open>The dual order type\<close>

text \<open>
  The following type is a copy of a given ordered base type, but with the ordering reversed.
  This will be useful later because we can do some of our reasoning simply by symmetry.
\<close>
typedef 'a dual_ord = "UNIV :: 'a set" morphisms of_dual_ord to_dual_ord
  by auto

setup_lifting type_definition_dual_ord

instantiation dual_ord :: (ord) ord
begin

lift_definition less_eq_dual_ord :: "'a dual_ord \<Rightarrow> 'a dual_ord \<Rightarrow> bool" is
  "\<lambda>a b :: 'a. a \<ge> b" .

lift_definition less_dual_ord :: "'a dual_ord \<Rightarrow> 'a dual_ord \<Rightarrow> bool" is
  "\<lambda>a b :: 'a. a > b" .

instance ..
end

instance dual_ord :: (preorder) preorder
  by standard (transfer; force simp: less_le_not_le intro: order_trans)+

instance dual_ord :: (linorder) linorder
  by standard (transfer; force simp: not_le)+


subsection \<open>Chopping a list into equal-sized sublists\<close>

(* TODO: Move to library? *)
function chop :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "chop n [] = []"
| "chop 0 xs = []"
| "n > 0 \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> chop n xs = take n xs # chop n (drop n xs)"
  by force+
termination by lexicographic_order

context
  includes lifting_syntax
begin

lemma chop_transfer [transfer_rule]: 
  "((=) ===> list_all2 R ===> list_all2 (list_all2 R)) chop chop"
proof (intro rel_funI)
  fix m n ::nat and xs :: "'a list" and ys :: "'b list"
  assume "m = n" "list_all2 R xs ys"
  from this(2) have "list_all2 (list_all2 R) (chop n xs) (chop n ys)"
  proof (induction n xs arbitrary: ys rule: chop.induct)
    case (3 n xs ys)
    hence "ys \<noteq> []" by auto
    with 3 show ?case by auto
  qed auto
  with \<open>m = n\<close> show "list_all2 (list_all2 R) (chop m xs) (chop n ys)" by simp
qed

end

lemma chop_reduce: "chop n xs = (if n = 0 \<or> xs = [] then [] else take n xs # chop n (drop n xs))"
  by (cases "n = 0"; cases "xs = []") auto

lemma concat_chop [simp]: "n > 0 \<Longrightarrow> concat (chop n xs) = xs"
  by (induction n xs rule: chop.induct) auto

lemma chop_elem_not_Nil [simp,dest]: "ys \<in> set (chop n xs) \<Longrightarrow> ys \<noteq> []"
  by (induction n xs rule: chop.induct) (auto simp: eq_commute[of "[]"])

lemma chop_eq_Nil_iff [simp]: "chop n xs = [] \<longleftrightarrow> n = 0 \<or> xs = []"
  by (induction n xs rule: chop.induct) auto  

lemma chop_ge_length_eq: "n > 0 \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> n \<ge> length xs \<Longrightarrow> chop n xs = [xs]"
  by simp

lemma length_chop_part_le: "ys \<in> set (chop n xs) \<Longrightarrow> length ys \<le> n"
  by (induction n xs rule: chop.induct) auto

lemma length_nth_chop:
  assumes "i < length (chop n xs)"
  shows   "length (chop n xs ! i) = 
             (if i = length (chop n xs) - 1 \<and> \<not>n dvd length xs then length xs mod n else n)"
proof (cases "n = 0")
  case False
  thus ?thesis
    using assms
  proof (induction n xs arbitrary: i rule: chop.induct)
    case (3 n xs i)
    show ?case
    proof (cases i)
      case 0
      thus ?thesis using "3.prems"
      by (cases "length xs < n") (auto simp: le_Suc_eq dest: dvd_imp_le)
    next
      case [simp]: (Suc i')
      with "3.prems" have [simp]: "xs \<noteq> []" by auto
      with "3.prems" have *: "length xs > n" by (cases "length xs \<le> n") simp_all
      with "3.prems" have "chop n xs ! i = chop n (drop n xs) ! i'" by simp
      also have "length \<dots> = (if i = length (chop n xs) - 1 \<and> \<not> n dvd (length xs - n)
                                then (length xs - n) mod n else n)"
        by (subst "3.IH") (use Suc "3.prems" in auto)
      also have "n dvd (length xs - n) \<longleftrightarrow> n dvd length xs"
        using * by (subst dvd_minus_self) auto
      also have "(length xs - n) mod n = length xs mod n"
        using * by (subst le_mod_geq [symmetric]) auto
      finally show ?thesis .
    qed
  qed auto
qed (insert assms, auto)

lemma length_chop:
  assumes "n > 0"
  shows   "length (chop n xs) = nat \<lceil>length xs / n\<rceil>"
  using assms
proof (induction n xs rule: chop.induct)
  case (3 n xs)
  show ?case
  proof (cases "length xs \<ge> n")
    case False
    hence "\<lceil>real (length xs) / real n\<rceil> = 1" using "3.hyps"
      by (intro ceiling_unique) auto
    with False show ?thesis using "3.prems" "3.hyps"
      by (auto simp: chop_ge_length_eq not_le)
  next
    case True
    hence "real (length xs) = real n + real (length (drop n xs))"
      by simp
    also have "\<dots> / real n = real (length (drop n xs)) / real n + 1"
      using \<open>n > 0\<close> by (simp add: divide_simps)
    also have "ceiling \<dots> = ceiling (real (length (drop n xs)) / real n) + 1" by simp
    also have "nat \<dots> = nat (ceiling (real (length (drop n xs)) / real n)) + nat 1"
      by (intro nat_add_distrib[OF order.trans[OF _ ceiling_mono[of 0]]]) auto
    also have "\<dots> = length (chop n xs)"
      using \<open>n > 0\<close> "3.hyps" by (subst "3.IH" [symmetric]) auto
    finally show ?thesis ..
  qed
qed auto

lemma sum_msets_chop: "n > 0 \<Longrightarrow> (\<Sum>ys\<leftarrow>chop n xs. mset ys) = mset xs"
  by (subst mset_concat [symmetric]) simp_all

lemma UN_sets_chop: "n > 0 \<Longrightarrow> (\<Union>ys\<in>set (chop n xs). set ys) = set xs"
  by (simp only: set_concat [symmetric] concat_chop)

lemma in_set_chopD [dest]:
  assumes "x \<in> set ys" "ys \<in> set (chop d xs)"
  shows   "x \<in> set xs"
proof (cases "d > 0")
  case True
  thus ?thesis by (subst UN_sets_chop [symmetric]) (use assms in auto)
qed (use assms in auto)


subsection \<open>$k$-th order statistics and medians\<close>

text \<open>
  This returns the $k$-th smallest element of a list. This is also known as the $k$-th order
  statistic.
\<close>
definition select :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a :: linorder)" where
  "select k xs = sort xs ! k"

text \<open>
  The median of a list, where, for lists of even lengths, the smaller one is favoured:
\<close>
definition median where "median xs = select ((length xs - 1) div 2) xs"

lemma select_in_set [intro,simp]:
  assumes "k < length xs"
  shows   "select k xs \<in> set xs"
proof -
  from assms have "sort xs ! k \<in> set (sort xs)" by (intro nth_mem) auto
  also have "set (sort xs) = set xs" by simp
  finally show ?thesis by (simp add: select_def)
qed

lemma median_in_set [intro, simp]: 
  assumes "xs \<noteq> []"
  shows   "median xs \<in> set xs"
proof -
  from assms have "length xs > 0" by auto
  hence "(length xs - 1) div 2 < length xs" by linarith
  thus ?thesis by (simp add: median_def)
qed

text \<open>
  We show that selection and medians does not depend on the order of the elements:
\<close>
lemma sort_cong: "mset xs = mset ys \<Longrightarrow> sort xs = sort ys"
  by (rule properties_for_sort) simp_all

lemma select_cong:
  "k = k' \<Longrightarrow> mset xs = mset xs' \<Longrightarrow> select k xs = select k' xs'"
  by (auto simp: select_def dest: sort_cong)

lemma median_cong: "mset xs = mset xs' \<Longrightarrow> median xs = median xs'"
  unfolding median_def by (intro select_cong) (auto dest: mset_eq_length)


text \<open>
  Selection distributes over appending lists under certain conditions:
\<close>
lemma sort_append:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> x \<le> y"
  shows   "sort (xs @ ys) = sort xs @ sort ys"
  using assms  by (intro properties_for_sort) (auto simp: sorted_append)

lemma select_append:
  assumes "\<And>y z. y \<in> set ys \<Longrightarrow> z \<in> set zs \<Longrightarrow> y \<le> z"
  shows   "k < length ys \<Longrightarrow> select k (ys @ zs) = select k ys"
          "k \<in> {length ys..<length ys + length zs} \<Longrightarrow>
             select k (ys @ zs) = select (k - length ys) zs"
  using assms by (simp_all add: select_def sort_append nth_append)

lemma select_append':
  assumes "\<And>y z. y \<in> set ys \<Longrightarrow> z \<in> set zs \<Longrightarrow> y \<le> z" "k < length ys + length zs"
  shows   "select k (ys @ zs) = (if k < length ys then select k ys else select (k - length ys) zs)"
  using assms by (auto intro!: select_append)


text \<open>
  We can find simple upper bounds for the number of elements that are strictly less than (resp.
  greater than) the median of a list.
\<close>
lemma size_less_than_median:
  "size {#y \<in># mset xs. y < median xs#} \<le> (length xs - 1) div 2"
proof (cases "xs = []")
  case False
  hence "length xs > 0" by simp
  hence "(length xs - 1) div 2 < length xs" by linarith
  hence "size {#y \<in># mset (sort xs). y < median xs#} \<le> 
           size (mset (take ((length xs - 1) div 2) (sort xs)))"
    unfolding median_def select_def using False
    by (intro size_mset_mono sorted_filter_less_subset_take) auto
  thus ?thesis using False by simp
qed auto

lemma size_greater_than_median:
  "size {#y \<in># mset xs. y > median xs#} \<le> length xs div 2"
proof (cases "xs = []")
  case False
  hence "length xs > 0" by simp
  hence "(length xs - 1) div 2 < length xs" by linarith
  hence "size {#y \<in># mset (sort xs). y > median xs#} \<le> 
           size (mset (drop (Suc ((length xs - 1) div 2)) (sort xs)))"
    unfolding median_def select_def using False
    by (intro size_mset_mono sorted_filter_greater_subset_drop) auto
  hence "size (filter_mset (\<lambda>y. y > median xs) (mset xs)) \<le>
           length xs - Suc ((length xs - 1) div 2)" by simp
  also have "\<dots> = length xs div 2" by linarith
  finally show ?thesis .
qed auto


subsection \<open>A more liberal notion of medians\<close>

text \<open>
  We now define a more relaxed version of being ``a median'' as opposed to being ``\emph{the}
  median''. A value is a median if at most half the values in the list are strictly smaller 
  than it and at most half are strictly greater. Note that, by this definition, the median does
  not even have to be in the list itself.
\<close>
definition is_median :: "'a :: linorder \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_median x xs \<longleftrightarrow> length (filter (\<lambda>y. y < x) xs) \<le> length xs div 2 \<and>
                      length (filter (\<lambda>y. y > x) xs) \<le> length xs div 2"

text \<open>
  We set up some transfer rules for @{const is_median}. In particular, we have a rule that
  shows that something is a median for a list iff it is a median on that list w.\,r.\,t.\ 
  the dual order, which will later allow us to argue by symmetry.
\<close>
context
  includes lifting_syntax
begin
lemma transfer_is_median [transfer_rule]:
  assumes [transfer_rule]: "(r ===> r ===> (=)) (<) (<)"
  shows   "(r ===> list_all2 r ===> (=)) is_median is_median"
  unfolding is_median_def by transfer_prover

lemma list_all2_eq_fun_conv_map: "list_all2 (\<lambda>x y. x = f y) xs ys \<longleftrightarrow> xs = map f ys"
proof
  assume "list_all2 (\<lambda>x y. x = f y) xs ys"
  thus "xs = map f ys" by induction auto
next
  assume "xs = map f ys"
  moreover have "list_all2 (\<lambda>x y. x = f y) (map f ys) ys"
    by (induction ys) auto
  ultimately show "list_all2 (\<lambda>x y. x = f y) xs ys" by simp
qed

lemma transfer_is_median_dual_ord [transfer_rule]:
  "(pcr_dual_ord (=) ===> list_all2 (pcr_dual_ord (=)) ===> (=)) is_median is_median"
  by (auto simp: pcr_dual_ord_def cr_dual_ord_def OO_def rel_fun_def is_median_def 
        list_all2_eq_fun_conv_map o_def less_dual_ord.rep_eq)
end

lemma is_median_to_dual_ord_iff [simp]:
  "is_median (to_dual_ord x) (map to_dual_ord xs) \<longleftrightarrow> is_median x xs"
  unfolding is_median_def by transfer auto


text \<open>
  The following is an obviously equivalent definition of @{const is_median} in terms of
  multisets that is occasionally nicer to use.
\<close>
lemma is_median_altdef:
  "is_median x xs \<longleftrightarrow> size (filter_mset (\<lambda>y. y < x) (mset xs)) \<le> length xs div 2 \<and>
                      size (filter_mset (\<lambda>y. y > x) (mset xs)) \<le> length xs div 2"
proof -
  have *: "length (filter P xs) = size (filter_mset P (mset xs))" for P and xs :: "'a list"
    by (simp flip: mset_filter)
  show ?thesis by (simp only: is_median_def *)
qed

lemma is_median_cong:
  assumes "x = y" "mset xs = mset ys"
  shows   "is_median x xs \<longleftrightarrow> is_median y ys"
  unfolding is_median_altdef by (simp only: assms mset_eq_length[OF assms(2)])

text \<open>
  If an element is the median of a list of odd length, we can add any element to the list
  and the element is still a median. Conversely, if we want to compute a median of a list with
  even length $n$, we can simply drop one element and reduce the problem to a median of a list
  of size $n - 1$.
\<close>
lemma is_median_Cons_odd:
  assumes "is_median x xs" and "odd (length xs)"
  shows   "is_median x (y # xs)"
  using assms by (auto simp: is_median_def)

text \<open>
  And, of course, \emph{the} median is a median.
\<close>
lemma is_median_median [simp,intro]: "is_median (median xs) xs"
  using size_less_than_median[of xs] size_greater_than_median[of xs]
  unfolding is_median_def size_mset [symmetric] mset_filter by linarith+


subsection \<open>Properties of a median-of-medians\<close>

text \<open>
  We can now bound the number of list elements that can be strictly smaller than a 
  median-of-medians of a chopped-up list (where each part has length $d$ except for the last one,
  which can also be shorter).

  The core argument is that at least roughly half of the medians of the sublists are greater or 
  equal to the median-of-medians, and about $\frac{d}{2}$ elements in each such sublist are greater
  than or equal to their median and thereby also than the median-of-medians.
\<close>
lemma size_less_than_median_of_medians_strong:
  fixes xs :: "'a :: linorder list" and d :: nat
  assumes d: "d > 0"
  assumes median: "\<And>xs. xs \<noteq> [] \<Longrightarrow> length xs \<le> d \<Longrightarrow> is_median (med xs) xs"
  assumes median': "is_median x (map med (chop d xs))"
  defines "m \<equiv> length (chop d xs)"
  shows   "size {#y \<in># mset xs. y < x#} \<le> m * (d div 2) + m div 2 * ((d + 1) div 2)"
proof -
  define n where [simp]: "n = length xs"
  \<comment> \<open>The medians of the sublists\<close>
  define M where "M = mset (map med (chop d xs))"
  define YS where "YS = mset (chop d xs)"
  \<comment> \<open>The sublists with a smaller median than the median-of-medians @{term x} and the rest.\<close>
  define YS1 where "YS1 = filter_mset (\<lambda>ys. med ys < x) (mset (chop d xs))"
  define YS2 where "YS2 = filter_mset (\<lambda>ys. \<not>(med ys < x)) (mset (chop d xs))"

  \<comment> \<open>At most roughly half of the lists have a median that is smaller than @{term M}\<close>
  have "size YS1 = size (image_mset med YS1)" by simp
  also have "image_mset med YS1 = {#y \<in># mset (map med (chop d xs)). y < x#}"
    unfolding YS1_def by (subst filter_mset_image_mset [symmetric]) simp_all
  also have "size \<dots> \<le> (length (map med (chop d xs))) div 2"
    using median' unfolding is_median_altdef by simp
  also have "\<dots> = m div 2" by (simp add: m_def)
  finally have size_YS1: "size YS1 \<le> m div 2" .

  have "m = size (mset (chop d xs))" by (simp add: m_def)
  also have "mset (chop d xs) = YS1 + YS2" unfolding YS1_def YS2_def
    by (rule multiset_partition)
  finally have m_eq: "m = size YS1 + size YS2" by simp

  \<comment> \<open>We estimate the number of elements less than @{term x} by grouping them into elements
      coming from @{term YS1} and elements coming from @{term YS2}. In the first case, we 
      just note that no more than @{term d} elements can come from each sublist, whereas in
      the second case, we make the analysis more precise and note that only elements that are
      less than the median of their sublist can be less than @{term x}.\<close>
  have "{# y \<in># mset xs. y < x#} = {# y \<in># (\<Sum>ys\<leftarrow>chop d xs. mset ys). y < x#}" using d
    by (subst sum_msets_chop) simp_all
  also have "\<dots> = (\<Sum>ys\<leftarrow>chop d xs. {#y \<in># mset ys. y < x#})"
    by (subst filter_mset_sum_list) (simp add: o_def)
  also have "\<dots> = (\<Sum>ys\<in>#YS. {#y \<in># mset ys. y < x#})" unfolding YS_def
    by (subst sum_mset_sum_list [symmetric]) simp_all
  also have "YS = YS1 + YS2"
    by (simp add: YS_def YS1_def YS2_def not_le)
  also have "(\<Sum>ys\<in>#\<dots>. {#y \<in># mset ys. y < x#}) = 
               (\<Sum>ys\<in>#YS1. {#y \<in># mset ys. y < x#}) + (\<Sum>ys\<in>#YS2. {#y \<in># mset ys. y < x#})"
    by simp
  also have "\<dots> \<subseteq># (\<Sum>ys\<in>#YS1. mset ys) + (\<Sum>ys\<in>#YS2. {#y \<in># mset ys. y < med ys#})"
    by (intro subset_mset.add_mono sum_mset_mset_mono mset_filter_mono) (auto simp: YS2_def)
  finally have "{# y \<in># mset xs. y < x #} \<subseteq># \<dots>" .
  hence "size {# y \<in># mset xs. y < x #} \<le> size \<dots>" by (rule size_mset_mono)

  \<comment> \<open>We do some further straightforward estimations and arrive at our goal.\<close>
  also have "\<dots> = (\<Sum>ys\<in>#YS1. length ys) + (\<Sum>x\<in>#YS2. size {#y \<in># mset x. y < med x#})"
    by (simp add: size_mset_sum_mset_distrib multiset.map_comp o_def)
  also have "(\<Sum>ys\<in>#YS1. length ys) \<le> (\<Sum>ys\<in>#YS1. d)"
    by (intro sum_mset_mono) (auto simp: YS1_def length_chop_part_le)
  also have "\<dots> = size YS1 * d" by simp
  also have d: "d = (d div 2) + ((d + 1) div 2)" using d by linarith
  have "size YS1 * d = size YS1 * (d div 2) + size YS1 * ((d + 1) div 2)"
    by (subst d) (simp add: algebra_simps)
  also have "(\<Sum>ys\<in>#YS2. size {#y \<in># mset ys. y < med ys#}) \<le>
               (\<Sum>ys\<in>#YS2. length ys div 2)"
  proof (intro sum_mset_mono size_less_than_median, goal_cases)
    case (1 ys)
    hence "ys \<noteq> []" "length ys \<le> d" by (auto simp: YS2_def length_chop_part_le)
    from median[OF this] show ?case by (auto simp: is_median_altdef)
  qed
  also have "\<dots> \<le> (\<Sum>ys\<in>#YS2. d div 2)"
    by (intro sum_mset_mono div_le_mono diff_le_mono) (auto simp: YS2_def dest: length_chop_part_le)
  also have "\<dots> = size YS2 * (d div 2)" by simp
  also have "size YS1 * (d div 2) + size YS1 * ((d + 1) div 2) + \<dots> =
               m * (d div 2) + size YS1 * ((d + 1) div 2)" by (simp add: m_eq algebra_simps)
  also have "size YS1 * ((d + 1) div 2) \<le> (m div 2) * ((d + 1) div 2)"
    by (intro mult_right_mono size_YS1) auto
  finally show "size {#y \<in># mset xs. y < x#} \<le>
                  m * (d div 2) + m div 2 * ((d + 1) div 2)" by simp_all
qed

text \<open>
  We now focus on the case of an odd chopping size and make some further estimations to 
  simplify the above result a little bit.
\<close>
theorem size_less_than_median_of_medians:
  fixes xs :: "'a :: linorder list" and d :: nat
  assumes median: "\<And>xs. xs \<noteq> [] \<Longrightarrow> length xs \<le> Suc (2 * d) \<Longrightarrow> is_median (med xs) xs"
  assumes median': "is_median x (map med (chop (Suc (2*d)) xs))"
  defines "n \<equiv> length xs"
  defines "c \<equiv> (3 * real d + 1) / (2 * (2 * d + 1))"
  shows   "size {#y \<in># mset xs. y < x#} \<le> nat \<lceil>c * n\<rceil> + (5 * d) div 2 + 1"
proof (cases "xs = []")
  case False
  define m where "m = length (chop (Suc (2*d)) xs)"

  have "real (m div 2) \<le> real (nat \<lceil>real n / (1 + 2 * real d)\<rceil>) / 2"
    by (simp add: m_def length_chop n_def)
  also have "real (nat \<lceil>real n / (1 + 2 * real d)\<rceil>) =
               of_int \<lceil>real n / (1 + 2 * real d)\<rceil>"
    by (intro of_nat_nat) (auto simp: divide_simps)
  also have "\<dots> / 2 \<le> (real n / (1 + 2 * real d) + 1) / 2"
    by (intro divide_right_mono) linarith+
  also have "\<dots> = n / (2 * (2 * real d + 1)) + 1 / 2" by (simp add: field_simps)
  finally have m: "real (m div 2) \<le> \<dots>" .

  have "size {#y \<in># mset xs. y < x#} \<le> d * m + Suc d * (m div 2)"
    using size_less_than_median_of_medians_strong[of "Suc (2 * d)" med x xs] assms
    unfolding m_def by (simp add: algebra_simps)
  also have "\<dots> \<le> d * (2 * (m div 2) + 1) + Suc d * (m div 2)"
    by (intro add_mono mult_left_mono) linarith+
  also have "\<dots> = (3 * d + 1) * (m div 2) + d"
    by (simp add: algebra_simps)
  finally have "real (size {#y \<in># mset xs. y < x#}) \<le> real \<dots>"
    by (subst of_nat_le_iff)
  also have "\<dots> \<le> (3 * real d + 1) * (n / (2 * (2 * d + 1)) + 1/2) + real d"
    unfolding of_nat_add of_nat_mult of_nat_1 of_nat_numeral
    by (intro add_mono mult_mono order.refl m) (auto simp: m_def length_chop n_def add_ac)
  also have "\<dots> = c * real n + (5 * real d + 1) / 2"
    by (simp add: field_simps c_def)
  also have "\<dots> \<le> real (nat \<lceil>c * n\<rceil> + ((5 * d) div 2 + 1))"
    unfolding of_nat_add by (intro add_mono) (linarith, simp add: field_simps)
  finally show ?thesis by (subst (asm) of_nat_le_iff) (simp_all add: add_ac)
qed auto

text \<open>
  We get the analogous result for the number of elements that are greater than a median-of-medians
  by looking at the dual order and using the \emph{transfer} method.
\<close>
theorem size_greater_than_median_of_medians:
  fixes xs :: "'a :: linorder list" and d :: nat
  assumes median: "\<And>xs. xs \<noteq> [] \<Longrightarrow> length xs \<le> Suc (2 * d) \<Longrightarrow> is_median (med xs) xs"
  assumes median': "is_median x (map med (chop (Suc (2*d)) xs))" 
  defines "n \<equiv> length xs"
  defines "c \<equiv> (3 * real d + 1) / (2 * (2 * d + 1))"
  shows   "size {#y \<in># mset xs. y > x#} \<le> nat \<lceil>c * n\<rceil> + (5 * d) div 2 + 1"
proof -
  include lifting_syntax
  define med' where "med' = (\<lambda>xs. to_dual_ord (med (map of_dual_ord xs)))"
  have "xs = map of_dual_ord ys" if "list_all2 cr_dual_ord xs ys" for xs :: "'a list" and ys
    using that by induction (auto simp: cr_dual_ord_def)
  hence [transfer_rule]: "(list_all2 (pcr_dual_ord (=)) ===> pcr_dual_ord (=)) med med'"
    by (auto simp: rel_fun_def pcr_dual_ord_def OO_def med'_def cr_dual_ord_def 
                   dual_ord.to_dual_ord_inverse)

  have "size {#y \<in># mset xs. y > x#} = length (filter (\<lambda>y. y > x) xs)"
    by (subst size_mset [symmetric]) (simp only: mset_filter)
  also have "\<dots> = length (map to_dual_ord (filter (\<lambda>y. y > x) xs))" by simp
  also have "(\<lambda>y. y > x) = (\<lambda>y. to_dual_ord y < to_dual_ord x)"
    by transfer simp_all
  hence "length (map to_dual_ord (filter (\<lambda>y. y > x) xs)) = length (map to_dual_ord (filter \<dots> xs))"
    by simp
  also have "\<dots> = length (filter (\<lambda>y. y < to_dual_ord x) (map to_dual_ord xs))"
    unfolding filter_map o_def by simp
  also have "\<dots> = size {#y \<in># mset (map to_dual_ord xs). y < to_dual_ord x#}"
    by (subst size_mset [symmetric]) (simp only: mset_filter)
  also have "\<dots> \<le> nat \<lceil>(3 * real d + 1) / real (2 * (2 * d + 1)) * length (map to_dual_ord xs)\<rceil>
                    + 5 * d div 2 + 1"
  proof (intro size_less_than_median_of_medians)
    fix xs :: "'a dual_ord list" assume xs: "xs \<noteq> []" "length xs \<le> Suc (2 * d)"
    from xs show "is_median (med' xs) xs" by (transfer fixing: d) (rule median)
  next
    show "is_median (to_dual_ord x) (map med' (chop (Suc (2 * d)) (map to_dual_ord xs)))"
      by (transfer fixing: d x xs) (use median' in simp_all)
  qed
  finally show ?thesis by (simp add: n_def c_def)
qed


text \<open>
  The most important case is that of chopping size 5, since that is the most practical one
  for the median-of-medians selection algorithm. For it, we obtain the following nice
  and simple bounds:
\<close>
corollary size_less_greater_median_of_medians_5:
  fixes xs :: "'a :: linorder list"
  assumes "\<And>xs. xs \<noteq> [] \<Longrightarrow> length xs \<le> 5 \<Longrightarrow> is_median (med xs) xs"
  assumes "is_median x (map med (chop 5 xs))" 
  shows "length (filter (\<lambda>y. y < x) xs) \<le> nat \<lceil>0.7 * length xs\<rceil> + 6"
    and "length (filter (\<lambda>y. y > x) xs) \<le> nat \<lceil>0.7 * length xs\<rceil> + 6"
  using size_less_than_median_of_medians[of 2 med x xs]
        size_greater_than_median_of_medians[of 2 med x xs] assms
  by (simp_all add: size_mset [symmetric] mset_filter mult_ac add_ac del: size_mset)


subsection \<open>The recursive step\<close>

text \<open>
  We now turn to the actual selection algorithm itself. The following simple reduction lemma 
  illustrates the idea of the algorithm quite well already, but it has the disadvantage that,
  if one were to use it as a recursive algorithm, it would only work for lists with distinct
  elements. If the list contains repeated elements, this may not even terminate.

  The basic idea is that we choose some pivot element, partition the list into elements that 
  are bigger than the pivot and those that are not, and then recurse into one of these (hopefully
  smaller) lists.
\<close>
theorem select_rec_partition:
  assumes "d > 0" "k < length xs"
  shows "select k xs = (
           let (ys, zs) = partition (\<lambda>y. y \<le> x) xs
           in  if k < length ys then select k ys else select (k - length ys) zs
          )" (is "_ = ?rhs")
proof -
  define ys zs where "ys = filter (\<lambda>y. y \<le> x) xs" and "zs = filter (\<lambda>y. \<not>(y \<le> x)) xs"
  have "select k xs = select k (ys @ zs)"
    by (intro select_cong) (simp_all add: ys_def zs_def)
  also have "\<dots> = (if k < length ys then select k ys else select (k - length ys) zs)"
    using assms(2) by (intro select_append') (auto simp: ys_def zs_def sum_length_filter_compl)
  finally show ?thesis by (simp add: ys_def zs_def Let_def o_def)
qed

text \<open>
  The following variant uses a three-way partitioning function instead. This way, the size of
  the list in the final recursive call decreases by a factor of at least $\frac{3d'+1}{2(2d'+1)}$ 
  by the previous estimates, given that the chopping size is $d = 2d'+1$. For a chopping size of 5,
  we get a factor of $0.7$. 
\<close>
definition threeway_partition :: "'a \<Rightarrow> 'a :: linorder list \<Rightarrow> 'a list \<times> 'a list \<times> 'a list" where
  "threeway_partition x xs = (filter (\<lambda>y. y < x) xs, filter (\<lambda>y. y = x) xs, filter (\<lambda>y. y > x) xs)"

lemma threeway_partition_code [code]:
  "threeway_partition x [] = ([], [], [])"
  "threeway_partition x (y # ys) =
     (case threeway_partition x ys of (ls, es, gs) \<Rightarrow>
        if y < x then (y # ls, es, gs) else if x = y then (ls, y # es, gs) else (ls, es, y # gs))"
  by (auto simp: threeway_partition_def)

theorem select_rec_threeway_partition:
  assumes "d > 0" "k < length xs"
  shows "select k xs = (
           let (ls, es, gs) = threeway_partition x xs;
               nl = length ls; ne = length es
           in
             if k < nl then select k ls 
             else if k < nl + ne then x
             else select (k - nl - ne) gs
          )" (is "_ = ?rhs")
proof -
  define ls es gs where "ls = filter (\<lambda>y. y < x) xs" and "es = filter (\<lambda>y. y = x) xs"
                    and "gs = filter (\<lambda>y. y > x) xs"
  define nl ne where [simp]: "nl = length ls" "ne = length es"
  have mset_eq: "mset xs = mset ls + mset es + mset gs" unfolding ls_def es_def gs_def
    by (induction xs) auto
  have length_eq: "length xs = length ls + length es + length gs" unfolding ls_def es_def gs_def
    by (induction xs) auto
  have [simp]: "select i es = x" if "i < length es" for i
  proof -
    have "select i es \<in> set (sort es)" unfolding select_def
      using that by (intro nth_mem) auto
    hence "select i es \<in> set es" using that by (auto simp: select_def)
    also have "set es \<subseteq> {x}" unfolding es_def by (induction es) auto
    finally show ?thesis by simp
  qed

  have "select k xs = select k (ls @ (es @ gs))"
    by (intro select_cong) (simp_all add: mset_eq)
  also have "\<dots> = (if k < nl then select k ls else select (k - nl) (es @ gs))" 
    unfolding nl_ne_def using assms
    by (intro select_append') (auto simp: ls_def es_def gs_def length_eq)
  also have "\<dots> = (if k < nl then select k ls else if k < nl + ne then x
                    else select (k - nl - ne) gs)" (is "?lhs' = ?rhs'")
  proof (cases "k < nl")
    case False
    hence "?lhs' = select (k - nl) (es @ gs)" by simp
    also have "\<dots> = (if k - nl < ne then select (k - nl) es else select (k - nl - ne) gs)"
      unfolding nl_ne_def using assms False
      by (intro select_append') (auto simp: ls_def es_def gs_def length_eq)
    also have "\<dots> = (if k - nl < ne then x else select (k - nl - ne) gs)"
      by simp
    also from False have "\<dots> = ?rhs'" by auto
    finally show ?thesis .
  qed simp_all
  also have "\<dots> = ?rhs"
    by (simp add: threeway_partition_def Let_def ls_def es_def gs_def)
  finally show ?thesis .
qed

text \<open>
  By the above results, it can be seen quite easily that, in each recursive step, the algorithm
  takes a list of length $n$, does $O(n)$ work for the chopping, computing the medians of the
  sublists, and partitioning, and it calls itself recursively with lists of size at most
  $\lceil 0.2n\rceil$ and $\lceil 0.7n\rceil + 6$, respectively. This means that the runtime
  of the algorithm is bounded above by the Akra--Bazzi-style recurrence
    \[T(n) = T(\lceil 0.2n\rceil) + T(\lceil 0.7n\rceil + 6) + O(n)\]
  which, by the Akra--Bazzi theorem, can be shown to fulfil $T\in \Theta(n)$.

  However, a proper analysis of this would require an actual execution model and some way of 
  measuring the runtime of the algorithm, which is not what we aim to do here. Additionally, the
  entire algorithm can be performed in-place in an imperative way, but this because quite tedious.

  Instead of this, we will now focus on developing the above recursion into an executable 
  functional algorithm.
\<close>


subsection \<open>Medians of lists of length at most 5\<close>

text \<open>
  We now show some basic results about how to efficiently find a median of a list of size
  at most 5. For length 1 or 2, this is trivial, since we can just pick any element. For length 
  3 and 4, we need at most three comparisons. For length 5, we need at most six comparisons.

  This allows us to save some comparisons compared with the naive method of performing insertion
  sort and then returning the element in the middle.
\<close>
definition median_3 :: "'a :: linorder \<Rightarrow> _" where
  "median_3 a b c =
     (if a \<le> b then
        if b \<le> c then b else max a c
      else
        if c \<le> b then b else min a c)"

lemma median_3: "median_3 a b c = median [a, b, c]"
  by (auto simp: median_3_def median_def select_def min_def max_def)

definition median_5_aux :: "'a :: linorder \<Rightarrow> _" where
  "median_5_aux x1 x2 x3 x4 x5 = (
     if x2 \<le> x3 then if x2 \<le> x4 then min x3 x4 else min x2 x5
     else if x4 \<le> x3 then min x3 x5 else min x2 x4)"

lemma median_5_aux:
  assumes "x1 \<le> x2" "x4 \<le> x5" "x1 \<le> x4" 
  shows   "median_5_aux x1 x2 x3 x4 x5 = median [x1,x2,x3,x4,x5]"
  using assms by (auto simp: median_5_aux_def median_def select_def min_def)

definition median_5 :: "'a :: linorder \<Rightarrow> _" where
  "median_5 a b c d e = (
     let (x1, x2) = (if a \<le> b then (a, b) else (b, a));
         (x4, x5) = (if d \<le> e then (d, e) else (e, d))
     in
         if x1 \<le> x4 then median_5_aux x1 x2 c x4 x5 else median_5_aux x4 x5 c x1 x2)"

lemma median_5: "median_5 a b c d e = median [a, b, c, d, e]"
  by (auto simp: median_5_def Let_def median_5_aux intro: median_cong)

fun median_le_5 where
  "median_le_5 [a] = a"
| "median_le_5 [a,b] = a"
| "median_le_5 [a,b,c] = median_3 a b c"
| "median_le_5 [a,b,c,d] = median_3 a b c"
| "median_le_5 [a,b,c,d,e] = median_5 a b c d e"
| "median_le_5 _ = undefined"

lemma median_5_in_set: "median_5 a b c d e \<in> {a, b, c, d, e}"
proof -
  have "median_5 a b c d e \<in> set [a, b, c, d, e]"
    unfolding median_5 by (rule median_in_set) auto
  thus ?thesis by simp
qed

lemma median_le_5_in_set:
  assumes "xs \<noteq> []" "length xs \<le> 5"
  shows   "median_le_5 xs \<in> set xs"
proof (cases xs rule: median_le_5.cases)
  case (5 a b c d e)
  with median_5_in_set[of a b c d e] show ?thesis by simp
qed (insert assms, auto simp: median_3_def min_def max_def)

lemma median_le_5:
  assumes "xs \<noteq> []" "length xs \<le> 5"
  shows   "is_median (median_le_5 xs) xs"
proof (cases xs rule: median_le_5.cases)
  case (3 a b c)
  have "is_median (median xs) xs" by simp
  also have "median xs = median_3 a b c" by (simp add: median_3 3)
  finally show ?thesis using 3 by simp
next
  case (4 a b c d)
  have "is_median (median [a,b,c]) [a,b,c]" by simp
  also have "median [a,b,c] = median_3 a b c" by (simp add: median_3 4)
  finally have "is_median (median_3 a b c) (d # [a,b,c])" by (rule is_median_Cons_odd) auto
  also have "?this \<longleftrightarrow> is_median (median_3 a b c) [a,b,c,d]" by (intro is_median_cong) auto
  finally show ?thesis using 4 by simp
next
  case (5 a b c d e)
  have "is_median (median xs) xs" by simp
  also have "median xs = median_5 a b c d e" by (simp add: median_5 5)
  finally show ?thesis using 5 by simp  
qed (insert assms, auto simp: is_median_def)


subsection \<open>Median-of-medians selection algorithm\<close>

text \<open>
  The fast selection function now simply computes the median-of-medians of the chopped-up list
  as a pivot, partitions the list into with respect to that pivot, and recurses into one of 
  the resulting sublists.
\<close>
function fast_select where
  "fast_select k xs = (
     if length xs \<le> 20 then
       sort xs ! k
     else
       let x = fast_select (((length xs + 4) div 5 - 1) div 2) (map median_le_5 (chop 5 xs));
           (ls, es, gs) = threeway_partition x xs
       in
         if k < length ls then fast_select k ls 
         else if k < length ls + length es then x
         else fast_select (k - length ls - length es) gs
      )"
  by auto

text \<open>
  The correctness of this is obvious from the above theorems, but the proof is still
  somewhat complicated by the fact that termination depends on the correctness of the
  function.
\<close>
lemma fast_select_correct_aux:
  assumes "fast_select_dom (k, xs)" "k < length xs"
  shows   "fast_select k xs = select k xs"
  using assms
proof induction
  case (1 k xs)
  show ?case
  proof (cases "length xs \<le> 20")
    case True
    thus ?thesis using "1.prems" "1.hyps"
      by (subst fast_select.psimps) (auto simp: select_def)
  next
    case False
    define x where
      "x = fast_select (((length xs + 4) div 5 - Suc 0) div 2) (map median_le_5 (chop 5 xs))"
    define ls where "ls = filter (\<lambda>y. y < x) xs"
    define es where "es = filter (\<lambda>y. y = x) xs"
    define gs where "gs = filter (\<lambda>y. y > x) xs"
    define nl ne where "nl = length ls" and "ne = length es"
    note defs = nl_def ne_def x_def ls_def es_def gs_def
    have tw: "(ls, es, gs) = threeway_partition (fast_select (((length xs + 4) div 5 - 1) div 2)
                               (map median_le_5 (chop 5 xs))) xs"
      unfolding threeway_partition_def defs One_nat_def ..
    have tw': "(ls, es, gs) = threeway_partition x xs"
      by (simp add: tw x_def)

    have "fast_select k xs = (if k < nl then fast_select k ls else if k < nl + ne then x
                                else fast_select (k - nl - ne) gs)" using "1.hyps" False
      by (subst fast_select.psimps) (simp_all add: threeway_partition_def defs [symmetric])
    also have "\<dots> = (if k < nl then select k ls else if k < nl + ne then x 
                       else select (k - nl - ne) gs)"
    proof (intro if_cong refl)
      assume *: "k < nl"
      show "fast_select k ls = select k ls"
        by (rule 1; (rule refl tw)?) 
           (insert *, auto simp: False threeway_partition_def ls_def x_def nl_def)+
    next
      assume *: "\<not>k < nl" "\<not>k < nl + ne"
      have **: "length xs = length ls + length es + length gs"
        unfolding ls_def es_def gs_def by (induction xs) auto
      show "fast_select (k - nl - ne) gs = select (k - nl - ne) gs"
        unfolding nl_def ne_def
        by (rule 1; (rule refl tw)?) (insert False * ** \<open>k < length xs\<close>, auto simp: nl_def ne_def)
    qed
    also have "\<dots> = select k xs" using \<open>k < length xs\<close>
      by (subst (3) select_rec_threeway_partition[of "5::nat" _ _ x])
         (unfold Let_def nl_def ne_def ls_def gs_def es_def x_def threeway_partition_def, simp_all)
    finally show ?thesis .
  qed
qed

text \<open>
  Termination of the algorithm is reasonably obvious because the lists that are recursed into
  never contain the pivot (the median-of-medians), while the original list clearly does.
  The proof is still somewhat technical though.
\<close>
lemma fast_select_termination: "All fast_select_dom"
proof (relation "measure (length \<circ> snd)"; (safe)?, goal_cases)
  case (1 k xs)
  thus ?case
    by (auto simp: length_chop nat_less_iff ceiling_less_iff)
next
  fix k :: nat and xs ls es gs :: "'a list"
  define x where "x = fast_select (((length xs + 4) div 5 - 1) div 2) (map median_le_5 (chop 5 xs))"
  assume A: "\<not> length xs \<le> 20" 
            "(ls, es, gs) = threeway_partition x xs"
            "fast_select_dom (((length xs + 4) div 5 - 1) div 2, 
                             map median_le_5 (chop 5 xs))"
  from A have eq: "ls = filter (\<lambda>y. y < x) xs" "gs = filter (\<lambda>y. y > x) xs"
    by (simp_all add: x_def threeway_partition_def)
  have len: "(length xs + 4) div 5 = nat \<lceil>length xs / 5\<rceil>" by linarith
  have less: "(nat \<lceil>real (length xs) / 5\<rceil> - Suc 0) div 2 < nat \<lceil>real (length xs) / 5\<rceil>"
    using A(1) by linarith
  have "x = select (((length xs + 4) div 5 - 1) div 2) (map median_le_5 (chop 5 xs))"
    using less unfolding x_def by (intro fast_select_correct_aux A) (auto simp: length_chop len)
  also have "\<dots> = median (map median_le_5 (chop 5 xs))" by (simp add: median_def len length_chop)
  finally have x: "x = \<dots>" .
  moreover {
    have "x \<in> set (map median_le_5 (chop 5 xs))"
      using A(1) unfolding x by (intro median_in_set) auto
    also have "\<dots> \<subseteq> (\<Union>ys\<in>set (chop 5 xs). {median_le_5 ys})" by auto
    also have "\<dots> \<subseteq> (\<Union>ys\<in>set (chop 5 xs). set ys)" using A(1)
      by (intro UN_mono) (auto simp: median_le_5_in_set length_chop_part_le)
    also have "\<dots> = set xs" by (subst UN_sets_chop) auto
    finally have "x \<in> set xs" .
  }  
  ultimately show "((k, ls), k, xs) \<in> measure (length \<circ> snd)"
              and "((k - length ls - length es, gs), k, xs) \<in> measure (length \<circ> snd)"
    using A(1) by (auto simp: eq intro!: length_filter_less[of x])
qed


text \<open>
  We now have all the ingredients to show that @{const fast_select} terminates and does,
  indeed, compute the $k$-th order statistic.
\<close>
termination fast_select by (rule fast_select_termination)

theorem fast_select_correct: "k < length xs \<Longrightarrow> fast_select k xs = select k xs"
  using fast_select_termination by (intro fast_select_correct_aux) auto


text \<open>
  The following version is then suitable for code export.
\<close>
lemma fast_select_code [code]:
  "fast_select k xs = (
     if length xs \<le> 20 then
       fold insort xs [] ! k
     else
       let x = fast_select (((length xs + 4) div 5 - 1) div 2) (map median_le_5 (chop 5 xs));
           (ls, es, gs) = threeway_partition x xs;
           nl = length ls; ne = nl + length es
       in
         if k < nl then fast_select k ls 
         else if k < ne then x
         else fast_select (k - ne) gs
      )"
  by (subst fast_select.simps) (simp_all only: Let_def algebra_simps sort_conv_fold)

lemma select_code [code]: 
  "select k xs = (if k < length xs then fast_select k xs 
                    else Code.abort (STR ''Selection index out of bounds.'') (\<lambda>_. select k xs))"
proof (cases "k < length xs")
  case True
  thus ?thesis by (simp only: if_True fast_select_correct)
qed (simp_all only: Code.abort_def if_False)

end
