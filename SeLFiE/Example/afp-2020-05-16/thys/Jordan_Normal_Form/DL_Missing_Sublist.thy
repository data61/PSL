(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Missing Lemmas of Sublist\<close>

theory DL_Missing_Sublist
imports Main
begin

lemma nths_only_one:
assumes "{i. i < length xs \<and> i\<in>I} = {j}"
shows "nths xs I = [xs!j]"
proof -
  have "set (nths xs I) = {xs!j}"
    unfolding set_nths using subset_antisym assms by fastforce
  moreover have "length (nths xs I) = 1"
    unfolding length_nths assms by auto
  ultimately show ?thesis
    by (metis One_nat_def length_0_conv length_Suc_conv the_elem_eq the_elem_set)
qed

lemma nths_replicate:
"nths (replicate n x) A = (replicate (card {i. i < n \<and> i \<in> A}) x)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof (cases "n\<in>A")
    case True
    then have 0:"(if 0 \<in> {j. j + length (replicate n x) \<in> A} then [x] else []) = [x]" by simp
    have "{i. i < Suc n \<and> i \<in> A} = insert n {i. i < n \<and> i \<in> A}" using True by auto
    have "Suc (card {i. i < n \<and> i \<in> A}) = card {i. i < Suc n \<and> i \<in> A}"
      unfolding \<open>{i. i < Suc n \<and> i \<in> A} = insert n {i. i < n \<and> i \<in> A}\<close>
      using finite_Collect_conjI[THEN card_insert_if] finite_Collect_less_nat
       less_irrefl_nat mem_Collect_eq by simp
    then show ?thesis unfolding replicate_Suc replicate_append_same[symmetric] nths_append Suc nths_singleton 0
      unfolding replicate_append_same replicate_Suc[symmetric] by simp
  next
    case False
    then have 0:"(if 0 \<in> {j. j + length (replicate n x) \<in> A} then [x] else []) = []" by simp
    have "{i. i < Suc n \<and> i \<in> A} = {i. i < n \<and> i \<in> A}" using False using le_less less_Suc_eq_le by auto
    then show ?thesis unfolding replicate_Suc replicate_append_same[symmetric] nths_append Suc nths_singleton 0
      by simp
  qed
qed

lemma length_nths_even:
assumes "even (length xs)"
shows "length (nths xs (Collect even)) = length (nths xs (Collect odd))"
using assms proof (induction "length xs div 2" arbitrary:xs)
  case 0
  then have "length xs = 0"
    by (auto elim: evenE)
  then show ?case by simp
next
  case (Suc l xs)
  then have length_drop2: "length (nths (drop 2 xs) (Collect even)) = length (nths (drop 2 xs) {a. odd a})" by simp

  have "length (take 2 xs) = 2" using Suc.hyps(2) by auto
  then have plus_odd: "{j. j + length (take 2 xs) \<in> Collect odd} = Collect odd" and
            plus_even: "{j. j + length (take 2 xs) \<in> Collect even} = Collect even" by simp_all
  have nths_take2: "nths (take 2 xs) (Collect even) = [take 2 xs ! 0]" "nths (take 2 xs) (Collect odd) = [take 2 xs ! 1]"
    using \<open>length (take 2 xs) = 2\<close> less_2_cases nths_only_one[of "take 2 xs" "Collect even" 0]
    nths_only_one[of "take 2 xs" "Collect odd" 1]
    by fastforce+
  then have "length (nths (take 2 xs @ drop 2 xs) (Collect even))
           = length (nths (take 2 xs @ drop 2 xs) {a. odd a})"
    unfolding nths_append length_append plus_odd plus_even nths_take2 length_drop2
    by auto
  then show ?case using append_take_drop_id[of 2 xs] by simp
qed

lemma nths_map:
"nths (map f xs) A = map f (nths xs A)"
proof (induction xs arbitrary:A)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  by (simp add: nths_Cons)
qed


section "Pick"

fun pick :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
"pick S 0 = (LEAST a. a\<in>S)" |
"pick S (Suc n) = (LEAST a. a\<in>S \<and> a > pick S n)"

lemma pick_in_set_inf:
assumes "infinite S"
shows "pick S n \<in> S"
proof (cases n)
  show "n = 0 \<Longrightarrow> pick S n \<in> S"
    unfolding pick.simps using \<open>infinite S\<close> LeastI pick.simps(1) by (metis Collect_mem_eq not_finite_existsD)
next
  fix n' assume "n = Suc n'"
  obtain a where "a\<in>S \<and> a > pick S n'" using assms by (metis bounded_nat_set_is_finite less_Suc_eq nat_neq_iff)
  show "pick S n \<in> S" unfolding \<open>n = Suc n'\<close> pick.simps(2)
    using LeastI[of "\<lambda>a. a \<in> S \<and> pick S n' < a" a, OF \<open>a\<in>S \<and> a > pick S n'\<close>] by blast
qed

lemma pick_mono_inf:
assumes "infinite S"
shows "m < n \<Longrightarrow> pick S m < pick S n"
using assms proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then obtain a where "a \<in> S \<and> pick S n < a" by (metis bounded_nat_set_is_finite less_Suc_eq nat_neq_iff)
  then have "pick S n < pick S (Suc n)" unfolding pick.simps
    using LeastI[of "\<lambda>a. a \<in> S \<and> pick S n < a" a, OF \<open>a\<in>S \<and> a > pick S n\<close>] by simp
  then show ?case using Suc.IH Suc.prems(1) assms dual_order.strict_trans less_Suc_eq by auto
qed

lemma pick_eq_iff_inf:
assumes "infinite S"
shows "x = y \<longleftrightarrow> pick S x = pick S y"
  by (metis assms nat_neq_iff pick_mono_inf)

lemma card_le_pick_inf:
assumes "infinite S"
and "pick S n \<ge> i"
shows "card {a\<in>S. a < i} \<le> n"
using assms proof (induction n arbitrary:i)
  case 0
  then show ?case unfolding pick.simps using not_less_Least
    by (metis (no_types, lifting) Collect_empty_eq card_0_eq card_ge_0_finite dual_order.strict_trans1 leI le_0_eq)
next
  case (Suc n)
  then show ?case
  proof -
    have "card {a \<in> S. a < pick S n} \<le> n" using Suc by blast
    have "{a \<in> S. a < i} \<subseteq> {a \<in> S. a < pick S (Suc n)}" using Suc.prems(2) by auto
    have "{a \<in> S. a < pick S (Suc n)} = {a \<in> S. a < pick S n} \<union> {pick S n}"
      apply (rule subset_antisym; rule subsetI)
      using not_less_Least UnCI mem_Collect_eq nat_neq_iff singleton_conv
       pick_mono_inf[OF Suc.prems(1), of n "Suc n"] pick_in_set_inf[OF Suc.prems(1), of n] by fastforce+
    then have "card {a \<in> S. a < i} \<le> card {a \<in> S. a < pick S n} + card {pick S n}"
      using card_Un_disjoint  card_mono[OF _ \<open>{a \<in> S. a < i} \<subseteq> {a \<in> S. a < pick S (Suc n)}\<close>] by simp
    then show ?thesis using \<open>card {a \<in> S. a < pick S n} \<le> n\<close>  by auto
  qed
qed

lemma card_pick_inf:
assumes "infinite S"
shows "card {a\<in>S. a < pick S n} = n"
using assms proof (induction n)
  case 0
  then show ?case unfolding pick.simps using not_less_Least by auto
next
  case (Suc n)
  then show "card {a\<in>S. a < pick S (Suc n)} = Suc n"
  proof -
    have "{a \<in> S. a < pick S (Suc n)} = {a \<in> S. a < pick S n} \<union> {pick S n}"
      apply (rule subset_antisym; rule subsetI)
      using not_less_Least UnCI mem_Collect_eq nat_neq_iff singleton_conv
       pick_mono_inf[OF Suc.prems, of n "Suc n"] pick_in_set_inf[OF Suc.prems, of n] by fastforce+
    then have "card {a \<in> S. a < pick S (Suc n)} = card {a \<in> S. a < pick S n} + card {pick S n}"  using card_Un_disjoint by auto
    then show ?thesis by (metis One_nat_def Suc_eq_plus1 Suc card_empty card_insert_if empty_iff finite.emptyI)
  qed
qed

lemma
assumes "n < card S"
shows
  pick_in_set_le:"pick S n \<in> S" and
  card_pick_le: "card {a\<in>S. a < pick S n} = n" and
  pick_mono_le: "m < n \<Longrightarrow> pick S m < pick S n"
using assms proof (induction n)
  assume "0 < card S"
  then obtain x where "x\<in>S" by fastforce
  then show "pick S 0 \<in> S" unfolding pick.simps by (meson LeastI)
  then show "card {a \<in> S. a < pick S 0} = 0" using not_less_Least by auto
  show "m < 0 \<Longrightarrow>  pick S m < pick S 0" by auto
next
  fix n
  assume "n < card S \<Longrightarrow> pick S n \<in> S"
    and "n < card S \<Longrightarrow> card {a \<in> S. a < pick S n} = n"
    and "Suc n < card S"
    and "m < n \<Longrightarrow> n < card S \<Longrightarrow> pick S m < pick S n"
  then have "card {a \<in> S. a < pick S n} = n" "pick S n \<in> S" by linarith+
  have "card {a \<in> S. a > pick S n} > 0"
  proof -
    have "S = {a \<in> S. a < pick S n} \<union> {a \<in> S. a \<ge> pick S n}" by fastforce
    then have "card {a \<in> S. a \<ge> pick S n} > 1"
      using \<open>Suc n < card S\<close> \<open>card {a \<in> S. a < pick S n} = n\<close>
      card_Un_le[of "{a \<in> S. a < pick S n}" "{a \<in> S. pick S n \<le> a}"] by force
    then have 0:"{a \<in> S. a \<ge> pick S n} \<subseteq> {pick S n} \<union> {a \<in> S. a > pick S n}" by auto
    have 1:"finite ({pick S n} \<union> {a \<in> S. pick S n < a})"
      unfolding finite_Un using Collect_mem_eq assms card_infinite conjI by force
    have "1 < card {pick S n} + card {a \<in> S. pick S n < a}"
      using card_mono[OF 1 0] card_Un_le[of "{pick S n}" "{a \<in> S. a > pick S n}"]  \<open>card {a \<in> S. a \<ge> pick S n} > 1\<close>
      by linarith
    then show ?thesis by simp
  qed
  then show "pick S (Suc n) \<in> S" unfolding pick.simps
    by (metis (no_types, lifting) Collect_empty_eq LeastI card_0_eq card_infinite less_numeral_extra(3))
  have "pick S (Suc n) > pick S n"
    by (metis (no_types, lifting) pick.simps(2) \<open>card {a \<in> S. a > pick S n} > 0\<close> Collect_empty_eq LeastI card_0_eq card_infinite less_numeral_extra(3))
  then show "m < Suc n \<Longrightarrow> pick S m < pick S (Suc n)"
    using \<open>m < n \<Longrightarrow> n < card S \<Longrightarrow> pick S m < pick S n\<close>
    using \<open>Suc n < card S\<close> dual_order.strict_trans less_Suc_eq by auto
  then show "card {a\<in>S. a < pick S (Suc n)} = Suc n"
  proof -
    have "{a \<in> S. a < pick S (Suc n)} = {a \<in> S. a < pick S n} \<union> {pick S n}"
      apply (rule subset_antisym; rule subsetI)
      using pick.simps not_less_Least \<open>pick S (Suc n) > pick S n\<close> \<open>pick S n \<in> S\<close> by fastforce+
    then have "card {a \<in> S. a < pick S (Suc n)} = card {a \<in> S. a < pick S n} + card {pick S n}"  using card_Un_disjoint by auto
    then show ?thesis by (metis One_nat_def Suc_eq_plus1 \<open>card {a \<in> S. a < pick S n} = n\<close> card_empty card_insert_if empty_iff finite.emptyI)
  qed
qed

lemma card_le_pick_le:
assumes "n < card S"
and "pick S n \<ge> i"
shows "card {a\<in>S. a < i} \<le> n"
using assms proof (induction n arbitrary:i)
  case 0
  then show ?case unfolding pick.simps using not_less_Least
    by (metis (no_types, lifting) Collect_empty_eq card_0_eq card_ge_0_finite dual_order.strict_trans1 leI le_0_eq)
next
  case (Suc n)
  have "card {a \<in> S. a < pick S n} \<le> n" using Suc by (simp add: less_eq_Suc_le nat_less_le)
  have "{a \<in> S. a < i} \<subseteq> {a \<in> S. a < pick S (Suc n)}" using Suc.prems(2) by auto
  have "{a \<in> S. a < pick S (Suc n)} = {a \<in> S. a < pick S n} \<union> {pick S n}"
    apply (rule subset_antisym; rule subsetI)
    using pick.simps not_less_Least  pick_mono_le[OF Suc.prems(1), of n, OF lessI] pick_in_set_le[of n S] Suc by fastforce+
  then have "card {a \<in> S. a < i} \<le> card {a \<in> S. a < pick S n} + card {pick S n}"
    using card_Un_disjoint  card_mono[OF _ \<open>{a \<in> S. a < i} \<subseteq> {a \<in> S. a < pick S (Suc n)}\<close>] by simp
  then show ?case using \<open>card {a \<in> S. a < pick S n} \<le> n\<close>  by auto
qed

lemma
assumes "n < card S \<or> infinite S"
shows
  pick_in_set:"pick S n \<in> S" and
  card_le_pick: "i \<le> pick S n ==> card {a\<in>S. a < i} \<le> n" and
  card_pick: "card {a\<in>S. a < pick S n} = n" and
  pick_mono: "m < n \<Longrightarrow> pick S m < pick S n"
    using assms pick_in_set_inf pick_in_set_le card_pick_inf card_pick_le card_le_pick_le card_le_pick_inf
    pick_mono_inf pick_mono_le by auto

lemma pick_card:
"pick I (card {a\<in>I. a < i}) = (LEAST a. a\<in>I \<and> a \<ge> i)"
proof (induction i)
  case 0
  then show ?case by (simp add: pick_in_set_le)
next
  case (Suc i)
  then show ?case
  proof (cases "i\<in>I")
    case True
    then have 1:"pick I (card {a\<in>I. a < i}) = i" by (metis (mono_tags, lifting) Least_equality Suc.IH order_refl)
    have "{a \<in> I. a < Suc i} = {a \<in> I. a < i} \<union> {i}" using True by auto
    then have 2:"card {a \<in> I. a < Suc i} = Suc (card {a \<in> I. a < i})" by auto
    then show ?thesis unfolding 2 pick.simps 1 using Suc_le_eq by auto
  next
    case False
    then have 1:"{a \<in> I. a < Suc i} = {a \<in> I. a < i}" using Collect_cong less_Suc_eq by auto
    have 2:"\<And>a. (a \<in> I \<and> Suc i \<le> a) = (a \<in> I \<and> i \<le> a)" using False Suc_leD le_less_Suc_eq not_le by blast
    then show ?thesis unfolding 1 2 using Suc.IH by blast
  qed
qed

lemma pick_card_in_set: "i\<in>I \<Longrightarrow> pick I (card {a\<in>I. a < i}) = i"
  unfolding pick_card using Least_equality order_refl by (metis (no_types, lifting))

section "Sublist"

lemma nth_nths_card:
assumes "j<length xs"
and "j\<in>J"
shows "nths xs J ! card {j0. j0 < j \<and> j0 \<in> J} = xs!j"
using assms proof (induction xs rule:rev_induct)
  case Nil
  then show ?case using gr_implies_not0 list.size(3) by auto
next
  case (snoc x xs)
  then show ?case
  proof (cases "j < length xs")
    case True
    have "{j0. j0 < j \<and> j0 \<in> J} \<subset> {i. i < length xs \<and> i \<in> J}"
      using True snoc.prems(2) by auto
    then have "card {j0. j0 < j \<and> j0 \<in> J} < length (nths xs J)" unfolding length_nths
      using psubset_card_mono[of "{i. i < length xs \<and> i \<in> J}"] by simp
    then show ?thesis unfolding nths_append nth_append by (simp add: True snoc.IH snoc.prems(2))
  next
    case False
    then have "length xs = j"
      using length_append_singleton less_antisym snoc.prems(1) by auto
    then show ?thesis unfolding nths_append nth_append length_nths \<open>length xs = j\<close>
      by (simp add: snoc.prems(2))
  qed
qed

lemma pick_reduce_set:
assumes "i<card {a. a<m \<and> a\<in>I}"
shows "pick I i = pick {a. a < m \<and> a \<in> I} i"
using assms proof (induction i)
  let ?L = "LEAST a. a \<in> {a. a < m \<and> a \<in> I}"
  case 0
  then have "{a. a < m \<and> a \<in> I} \<noteq> {}" using card_empty less_numeral_extra(3) by fastforce
  then have "?L \<in> I" "?L < m" by (metis (mono_tags, lifting) Collect_empty_eq LeastI mem_Collect_eq)+
  have "\<And>x. x \<in> {a. a < m \<and> a \<in> I} \<Longrightarrow> ?L \<le> x" by (simp add: Least_le)
  have "\<And>x. x \<in> I \<Longrightarrow> ?L \<le> x"
    by (metis (mono_tags) \<open>?L < m\<close> \<open>\<And>x. x \<in> {a. a < m \<and> a \<in> I} \<Longrightarrow> ?L \<le> x\<close> dual_order.strict_trans2 le_cases mem_Collect_eq)
  then show ?case unfolding pick.simps using Least_equality[of "\<lambda>x. x\<in>I", OF \<open>?L \<in> I\<close>] by blast
next
  case (Suc i)
  let ?L = "LEAST x. x \<in> {a. a < m \<and> a \<in> I} \<and> pick I i < x"
  have 0:"pick {a. a < m \<and> a \<in> I} i = pick I i" using Suc_lessD Suc by linarith
  then have "?L \<in> {a. a < m \<and> a \<in> I}" "pick I i < ?L"
    using LeastI[of "\<lambda>a. a \<in> {a. a < m \<and> a \<in> I} \<and> pick I i < a"] using Suc.prems pick_in_set_le pick_mono_le by fastforce+
  then have "?L \<in> I" by blast
  show ?case unfolding pick.simps 0 using Least_equality[of "\<lambda>a. a \<in> I \<and> pick I i < a" ?L]
    by (metis (no_types, lifting) Least_le \<open>?L \<in> {a. a < m \<and> a \<in> I}\<close> \<open>pick I i < ?L\<close> mem_Collect_eq not_le not_less_iff_gr_or_eq order.trans)
qed

lemma nth_nths:
assumes "i<card {i. i<length xs \<and> i\<in>I}"
shows "nths xs I ! i = xs ! pick I i"
proof -
  have "{a \<in> {i. i < length xs \<and> i \<in> I}. a < pick {i. i < length xs \<and> i \<in> I} i}
        = {a.  a < pick {i. i < length xs \<and> i \<in> I} i \<and> a \<in> I}"
    using assms pick_in_set by fastforce
  then have "card {a. a < pick {i. i < length xs \<and> i \<in> I} i \<and> a \<in> I} = i"
    using card_pick_le[OF assms] by simp
  then have "nths xs I ! i = xs ! pick {i. i < length xs \<and> i \<in> I} i"
    using nth_nths_card[where j = "pick {i. i < length xs \<and> i \<in> I} i", of xs I]
    assms pick_in_set pick_in_set by auto
  then show ?thesis using pick_reduce_set using assms by auto
qed

lemma pick_UNIV: "pick UNIV j = j"
by (induction j, simp, metis (no_types, lifting) LeastI pick.simps(2)  Suc_mono UNIV_I less_Suc_eq not_less_Least)

lemma pick_le:
assumes "n < card {a. a < i \<and> a \<in> S}"
shows "pick S n < i"
proof -
  have 0:"{a \<in> {a. a < i \<and> a \<in> S}. a < i} = {a. a < i \<and> a \<in> S}" by blast
  show ?thesis apply (rule ccontr)
    using card_le_pick_le[OF assms, unfolded pick_reduce_set[OF assms, symmetric], of i, unfolded 0]
    assms not_less not_le by blast
qed

lemma prod_list_complementary_nthss:
fixes f ::"'a \<Rightarrow> 'b::comm_monoid_mult"
shows "prod_list (map f xs) = prod_list (map f (nths xs A)) *  prod_list (map f (nths xs (-A)))"
proof (induction xs rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  show ?case unfolding map_append "prod_list.append" nths_append nths_singleton snoc
    by (cases "(length xs)\<in>A"; simp;metis mult.assoc mult.commute)
qed

lemma nths_zip: "nths (zip xs ys) I = zip (nths xs I) (nths ys I)"
proof (rule nth_equalityI)
  show "length (nths (zip xs ys) I) = length (zip (nths xs I) (nths ys I))"
  proof (cases "length xs \<le> length ys")
    case True
    then have "{i. i < length xs \<and> i \<in> I} \<subseteq> {i. i < length ys \<and> i \<in> I}" by (simp add: Collect_mono less_le_trans)
    then have "card {i. i < length xs \<and> i \<in> I} \<le> card {i. i < length ys \<and> i \<in> I}"
      by (metis (mono_tags, lifting) card_mono finite_nat_set_iff_bounded mem_Collect_eq)
    then show ?thesis unfolding length_nths length_zip using True using min_def by linarith
  next
    case False
    then have "{i. i < length ys \<and> i \<in> I} \<subseteq> {i. i < length xs \<and> i \<in> I}" by (simp add: Collect_mono less_le_trans)
    then have "card {i. i < length ys \<and> i \<in> I} \<le> card {i. i < length xs \<and> i \<in> I}"
      by (metis (mono_tags, lifting) card_mono finite_nat_set_iff_bounded mem_Collect_eq)
    then show ?thesis unfolding length_nths length_zip using False using min_def by linarith
  qed
  show "nths (zip xs ys) I ! i = zip (nths xs I) (nths ys I) ! i" if "i < length (nths (zip xs ys) I)" for i
  proof -
   have "i < length (nths xs I)" "i < length (nths ys I)"
     using that by (simp_all add: \<open>length (nths (zip xs ys) I) = length (zip (nths xs I) (nths ys I))\<close>)
   show "nths (zip xs ys) I ! i = zip (nths xs I) (nths ys I) ! i"
     unfolding nth_nths[OF \<open>i < length (nths (zip xs ys) I)\<close>[unfolded length_nths]]
     unfolding nth_zip[OF \<open>i < length (nths xs I)\<close> \<open>i < length (nths ys I)\<close>]
     unfolding nth_zip[OF pick_le[OF \<open>i < length (nths xs I)\<close>[unfolded length_nths]]
                          pick_le[OF \<open>i < length (nths ys I)\<close>[unfolded length_nths]]]
     by (metis (full_types) \<open>i < length (nths xs I)\<close> \<open>i < length (nths ys I)\<close> length_nths nth_nths)
  qed
qed

section "weave"
    
definition weave :: "nat set \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"weave A xs ys = map (\<lambda>i. if i\<in>A then xs!(card {a\<in>A. a<i}) else ys!(card {a\<in>-A. a<i})) [0..<length xs + length ys]"

lemma length_weave:
shows "length (weave A xs ys) = length xs + length ys"
unfolding weave_def length_map by simp

lemma nth_weave:
assumes "i < length (weave A xs ys)"
shows "weave A xs ys ! i = (if i\<in>A then xs!(card {a\<in>A. a<i}) else ys!(card {a\<in>-A. a<i}))"
proof -
  have "i < length xs + length ys" using length_weave using assms by metis
  then have "i < length [0..<length xs + length ys]" by auto
  then have "[0..<length xs + length ys] ! i = i"
    by (metis \<open>i < length xs + length ys\<close> add.left_neutral nth_upt)
  then show ?thesis
    unfolding weave_def nth_map[OF \<open>i < length [0..<length xs + length ys]\<close>] by presburger
qed

lemma weave_append1:
assumes "length xs + length ys \<in> A"
assumes "length xs = card {a\<in>A. a < length xs + length ys}"
shows "weave A (xs @ [x]) ys = weave A xs ys @ [x]"
proof (rule nth_equalityI)
  show "length (weave A (xs @ [x]) ys) = length (weave A xs ys @ [x])"
    unfolding weave_def length_map by simp
  show "weave A (xs @ [x]) ys ! i = (weave A xs ys @ [x]) ! i"
    if "i < length (weave A (xs @ [x]) ys)" for i
  proof -
    show "weave A (xs @ [x]) ys ! i = (weave A xs ys @ [x]) ! i"
    proof (cases "i = length xs + length ys")
      case True
      then have "(weave A xs ys @ [x]) ! i = x" using length_weave by (metis nth_append_length)
      have "card {a \<in> A. a < i} = length xs" using assms(2) True by auto
      then show ?thesis unfolding nth_weave[OF \<open>i < length (weave A (xs @ [x]) ys)\<close>]
        \<open>(weave A xs ys @ [x]) ! i = x\<close> using True assms(1) by simp
    next
      case False
      have "i < length (weave A xs ys)" using \<open>i < length (weave A (xs @ [x]) ys)\<close>
        \<open>length (weave A (xs @ [x]) ys) = length (weave A xs ys @ [x])\<close> length_append_singleton
        length_weave less_antisym False by fastforce
      then have "(weave A xs ys @ [x]) ! i = (weave A xs ys) ! i" by (simp add: nth_append)
      {
        assume "i\<in>A"
        have  "i<length xs + length ys" by (metis \<open>i < length (weave A xs ys)\<close> length_weave)
        then have "{a \<in> A. a < i} \<subset> {a\<in>A. a < length xs + length ys}"
          using assms(1) \<open>i<length xs + length ys\<close> \<open>i\<in>A\<close> by auto
        then have "card {a \<in> A. a < i} < card {a\<in>A. a < length xs + length ys}"
          using psubset_card_mono[of "{a\<in>A. a < length xs + length ys}" "{a \<in> A. a < i}"]  by simp
        then have "(xs @ [x]) ! card {a \<in> A. a < i} = xs ! card {a \<in> A. a < i}"
        by (metis (no_types, lifting)  assms(2) nth_append)
      }
      then show ?thesis unfolding nth_weave[OF \<open>i < length (weave A (xs @ [x]) ys)\<close>]
        \<open>(weave A xs ys @ [x]) ! i = (weave A xs ys) ! i\<close> nth_weave[OF \<open>i < length (weave A xs ys)\<close>]
        by simp
    qed
  qed
qed

lemma weave_append2:
assumes "length xs + length ys \<notin> A"
assumes "length ys = card {a\<in>-A. a < length xs + length ys}"
shows "weave A xs (ys @ [y]) = weave A xs ys @ [y]"
proof (rule nth_equalityI)
  show "length (weave A xs (ys @ [y])) = length (weave A xs ys @ [y])"
    unfolding weave_def length_map by simp
  show "weave A xs (ys @ [y]) ! i = (weave A xs ys @ [y]) ! i" if "i < length (weave A xs (ys @ [y]))" for i
  proof -
    show "weave A xs (ys @ [y]) ! i = (weave A xs ys @ [y]) ! i"
    proof (cases "i = length xs + length ys")
      case True
      then have "(weave A xs ys @ [y]) ! i = y" using length_weave by (metis nth_append_length)
      have "card {a \<in> -A. a < i} = length ys" using assms(2) True by auto
      then show ?thesis unfolding nth_weave[OF \<open>i < length (weave A xs (ys @ [y]))\<close>]
        \<open>(weave A xs ys @ [y]) ! i = y\<close> using True assms(1) by simp
    next
      case False
      have "i < length (weave A xs ys)" using \<open>i < length (weave A xs (ys @ [y]))\<close>
        \<open>length (weave A xs (ys @ [y])) = length (weave A xs ys @ [y])\<close> length_append_singleton
        length_weave less_antisym False by fastforce
      then have "(weave A xs ys @ [y]) ! i = (weave A xs ys) ! i" by (simp add: nth_append)
      {
        assume "i\<notin>A"
        have  "i<length xs + length ys" by (metis \<open>i < length (weave A xs ys)\<close> length_weave)
        then have "{a \<in> -A. a < i} \<subset> {a\<in>-A. a < length xs + length ys}"
          using assms(1) \<open>i<length xs + length ys\<close> \<open>i\<notin>A\<close> by auto
        then have "card {a \<in> -A. a < i} < card {a\<in>-A. a < length xs + length ys}"
          using psubset_card_mono[of "{a\<in>-A. a < length xs + length ys}" "{a \<in> -A. a < i}"]  by simp
        then have "(ys @ [y]) ! card {a \<in> -A. a < i} = ys ! card {a \<in> -A. a < i}"
        by (metis (no_types, lifting)  assms(2) nth_append)
      }
      then show ?thesis unfolding nth_weave[OF \<open>i < length (weave A xs (ys @ [y]))\<close>]
        \<open>(weave A xs ys @ [y]) ! i = (weave A xs ys) ! i\<close> nth_weave[OF \<open>i < length (weave A xs ys)\<close>]
        by simp
    qed
  qed
qed

lemma nths_nth:
assumes "n\<in>A" "n<length xs"
shows "nths xs A ! (card {i. i<n \<and> i\<in>A}) = xs ! n"
using assms proof (induction xs rule:rev_induct)
  case (snoc x xs)
  then show ?case
  proof (cases "n = length xs")
    case True
    then show ?thesis unfolding nths_append[of xs "[x]" A] nth_append
      using length_nths[of xs A] nths_singleton snoc.prems(1) by auto
  next
    case False
    then have "n < length xs" using snoc by auto
    then have 0:"nths xs A ! card {i. i < n \<and> i \<in> A} = xs ! n" using snoc by auto

    have "{i. i < n \<and> i \<in> A} \<subset> {i. i < length xs \<and> i \<in> A}" using \<open>n < length xs\<close> snoc by force
    then have "card {i. i < n \<and> i \<in> A} < length (nths xs A)" unfolding length_nths
      by (simp add: psubset_card_mono)
    then show ?thesis unfolding nths_append[of xs "[x]" A] nth_append using 0
      by (simp add: \<open>n < length xs\<close>)
  qed
qed simp

lemma list_all2_nths:
assumes "list_all2 P (nths xs A) (nths ys A)"
and     "list_all2 P (nths xs (-A)) (nths ys (-A))"
shows "list_all2 P xs ys"
proof -
  have "length xs = length ys"
  proof (rule ccontr; cases "length xs < length ys")
    case True
    then show False
    proof (cases "length xs \<in> A")
      case False
      have "{i. i < length xs \<and> i \<in> - A} \<subset> {i. i < length ys \<and> i \<in> - A}"
        using False \<open>length xs < length ys\<close> by force
      then have "length (nths ys (-A)) > length (nths xs (-A))"
        unfolding length_nths by (simp add: psubset_card_mono)
      then show False using assms(2) list_all2_lengthD not_less_iff_gr_or_eq by blast
    next
      case True
      have "{i. i < length xs \<and> i \<in> A} \<subset> {i. i < length ys \<and> i \<in> A}"
        using True \<open>length xs < length ys\<close> by force
      then have "length (nths ys A) > length (nths xs A)"
        unfolding length_nths by (simp add: psubset_card_mono)
      then show False using assms(1) list_all2_lengthD not_less_iff_gr_or_eq by blast
    qed
  next
    assume "length xs \<noteq> length ys"
    case False
    then have "length xs > length ys" using \<open>length xs \<noteq> length ys\<close> by auto
    then show False
    proof (cases "length ys \<in> A")
      case False
      have "{i. i < length ys \<and> i \<in> -A} \<subset> {i. i < length xs \<and> i \<in> -A}"
        using False \<open>length xs > length ys\<close>  by force
      then have "length (nths xs (-A)) > length (nths ys (-A))"
        unfolding length_nths by (simp add: psubset_card_mono)
      then show False using assms(2) list_all2_lengthD dual_order.strict_implies_not_eq by blast
    next
      case True
      have "{i. i < length ys \<and> i \<in> A} \<subset> {i. i < length xs \<and> i \<in> A}"
        using True \<open>length xs > length ys\<close> by force
      then have "length (nths xs A) > length (nths ys A)"
        unfolding length_nths by (simp add: psubset_card_mono)
      then show False using assms(1) list_all2_lengthD dual_order.strict_implies_not_eq by blast
    qed
  qed

  have "\<And>n. n < length xs \<Longrightarrow> P (xs ! n) (ys ! n)"
  proof -
    fix n assume "n < length xs"
    then have "n < length ys" using \<open>length xs = length ys\<close> by auto
    then show "P (xs ! n) (ys ! n)"
    proof (cases "n\<in>A")
      case True
      have "{i. i < n \<and> i \<in> A} \<subset> {i. i < length xs \<and> i \<in> A}" using \<open>n < length xs\<close> \<open>n\<in>A\<close> by force
      then have "card {i. i < n \<and> i \<in> A} < length (nths xs A)" unfolding length_nths
        by (simp add: psubset_card_mono)
      show ?thesis using nths_nth[OF \<open>n\<in>A\<close> \<open>n < length xs\<close>] nths_nth[OF \<open>n\<in>A\<close> \<open>n < length ys\<close>]
        list_all2_nthD[OF assms(1), of "card {i. i < n \<and> i \<in> A}"] length_nths
        by (simp add: \<open>card {i. i < n \<and> i \<in> A} < length (nths xs A)\<close>)
    next
      case False then have "n\<in>-A" by auto
      have "{i. i < n \<and> i \<in> -A} \<subset> {i. i < length xs \<and> i \<in> -A}" using \<open>n < length xs\<close> \<open>n\<in>-A\<close> by force
      then have "card {i. i < n \<and> i \<in> -A} < length (nths xs (-A))" unfolding length_nths
        by (simp add: psubset_card_mono)
      show ?thesis using nths_nth[OF \<open>n\<in>-A\<close> \<open>n < length xs\<close>] nths_nth[OF \<open>n\<in>-A\<close> \<open>n < length ys\<close>]
        list_all2_nthD[OF assms(2), of "card {i. i < n \<and> i \<in> -A}"] length_nths
        using \<open>card {i. i < n \<and> i \<in> - A} < length (nths xs (- A))\<close> by auto   next
    qed
  qed
  then show ?thesis using \<open>length xs = length ys\<close> list_all2_all_nthI by blast
qed

lemma nths_weave:
assumes "length xs = card {a\<in>A. a < length xs + length ys}"
assumes "length ys = card {a\<in>(-A). a < length xs + length ys}"
shows "nths (weave A xs ys) A = xs \<and> nths (weave A xs ys) (-A) = ys"
using assms proof (induction "length xs + length ys" arbitrary: xs ys)
  case 0
  then show ?case
    unfolding weave_def nths_map by simp
next
  case (Suc l)
  then show ?case
  proof (cases "l\<in>A")
    case True
    then have "l\<in>{a \<in> A. a < length xs + length ys}" using Suc.hyps mem_Collect_eq zero_less_Suc by auto
    then have "length xs > 0" using Suc by fastforce
    then obtain xs' x where "xs = xs' @ [x]" by (metis append_butlast_last_id length_greater_0_conv)
    then have "l = length xs' + length ys" using Suc.hyps by simp
    have length_xs':"length xs' = card {a \<in> A. a < length xs' + length ys}"
    proof -
      have "{a \<in> A. a < length xs + length ys} = {a \<in> A. a < length xs' + length ys} \<union> {l}"
        using \<open>xs = xs' @ [x]\<close> \<open>l\<in>{a \<in> A. a < length xs + length ys}\<close> \<open>l = length xs' + length ys\<close>
        by force
      then have "card {a \<in> A. a < length xs + length ys} = card {a \<in> A. a < length xs' + length ys} + 1"
        using \<open>l = length xs' + length ys\<close> by fastforce
      then show ?thesis by (metis One_nat_def Suc.prems(1) \<open>xs = xs' @ [x]\<close> add_right_imp_eq
        length_Cons length_append list.size(3))
    qed
    have length_ys:"length ys = card {a \<in> - A. a < length xs' + length ys}"
    proof -
      have "l\<notin>{a \<in> - A. a < length xs + length ys}" using \<open>l\<in>A\<close> \<open>l = length xs' + length ys\<close> by blast
      have "{a \<in> -A. a < length xs + length ys} = {a \<in> -A. a < length xs' + length ys}"
        apply (rule subset_antisym)
        using  \<open>l = length xs' + length ys\<close> \<open>Suc l = length xs + length ys\<close> \<open>l\<notin>{a \<in> - A. a < length xs + length ys}\<close>
        apply (metis (no_types, lifting) Collect_mono less_Suc_eq mem_Collect_eq)
        using Collect_mono Suc.hyps(2) \<open>l = length xs' + length ys\<close> by auto
      then show ?thesis using Suc.prems(2) by auto
    qed
    have "length xs' + length ys \<in> A" using \<open>l\<in>A\<close> \<open>l = length xs' + length ys\<close> by blast

    then have "nths (weave A xs ys) A = nths (weave A xs' ys @ [x]) A" unfolding
       \<open>xs = xs' @ [x]\<close> using weave_append1[OF \<open>length xs' + length ys \<in> A\<close> length_xs'] by metis
    also have "... = nths (weave A xs' ys) A @ nths [x] {a. a + (length xs' + length ys) \<in> A}"
      using nths_append length_weave by metis
    also have "... = nths (weave A xs' ys) A @ [x]"
      using nths_singleton \<open>length xs' + length ys \<in> A\<close> by auto
    also have "... = xs" using Suc.hyps(1)[OF \<open>l = length xs' + length ys\<close> length_xs' length_ys]
     \<open>xs = xs' @ [x]\<close> by presburger
    finally have "nths (weave A xs ys) A = xs" by metis

    have "nths (weave A xs ys) (-A) = nths (weave A xs' ys @ [x]) (-A)" unfolding
       \<open>xs = xs' @ [x]\<close> using weave_append1[OF \<open>length xs' + length ys \<in> A\<close> length_xs'] by metis
    also have "... = nths (weave A xs' ys) (-A) @ nths [x] {a. a + (length xs' + length ys) \<in> (-A)}"
      using nths_append length_weave by metis
    also have "... = nths (weave A xs' ys) (-A)"
      using nths_singleton \<open>length xs' + length ys \<in> A\<close> by auto
    also have "... = ys"
      using Suc.hyps(1)[OF \<open>l = length xs' + length ys\<close> length_xs' length_ys] by presburger
    finally show ?thesis using \<open>nths (weave A xs ys) A = xs\<close> by auto
  next
    case False
    then have "l\<notin>{a \<in> A. a < length xs + length ys}" using Suc.hyps mem_Collect_eq zero_less_Suc by auto
    then have "length ys > 0" using Suc by fastforce
    then obtain ys' y where "ys = ys' @ [y]" by (metis append_butlast_last_id length_greater_0_conv)
    then have "l = length xs + length ys'" using Suc.hyps by simp
    have length_ys':"length ys' = card {a \<in> -A. a < length xs + length ys'}"
    proof -
      have "{a \<in> -A. a < length xs + length ys} = {a \<in> -A. a < length xs + length ys'} \<union> {l}"
        using \<open>ys = ys' @ [y]\<close> \<open>l\<notin>{a \<in> A. a < length xs + length ys}\<close> \<open>l = length xs + length ys'\<close>
        by force
      then have "card {a \<in> -A. a < length xs + length ys} = card {a \<in> -A. a < length xs + length ys'} + 1"
        using \<open>l = length xs + length ys'\<close> by fastforce
      then show ?thesis by (metis One_nat_def Suc.prems(2) \<open>ys = ys' @ [y]\<close> add_right_imp_eq
        length_Cons length_append list.size(3))
    qed
    have length_xs:"length xs = card {a \<in> A. a < length xs + length ys'}"
    proof -
      have "l\<notin>{a \<in> A. a < length xs + length ys}" using \<open>l\<notin>A\<close> \<open>l = length xs + length ys'\<close> by blast
      have "{a \<in> A. a < length xs + length ys} = {a \<in> A. a < length xs + length ys'}"
        apply (rule subset_antisym)
        using  \<open>l = length xs + length ys'\<close> \<open>Suc l = length xs + length ys\<close> \<open>l\<notin>{a \<in> A. a < length xs + length ys}\<close>
        apply (metis (no_types, lifting) Collect_mono less_Suc_eq mem_Collect_eq)
        using Collect_mono Suc.hyps(2) \<open>l = length xs + length ys'\<close> by auto
      then show ?thesis using Suc.prems(1) by auto
    qed
    have "length xs + length ys' \<notin> A" using \<open>l\<notin>A\<close> \<open>l = length xs + length ys'\<close> by blast

    then have "nths (weave A xs ys) A = nths (weave A xs ys' @ [y]) A" unfolding
       \<open>ys = ys' @ [y]\<close> using weave_append2[OF \<open>length xs + length ys' \<notin> A\<close> length_ys'] by metis
    also have "... = nths (weave A xs ys') A @ nths [y] {a. a + (length xs + length ys') \<in> A}"
      using nths_append length_weave by metis
    also have "... = nths (weave A xs ys') A"
      using nths_singleton \<open>length xs + length ys' \<notin> A\<close> by auto
    also have "... = xs"
      using Suc.hyps(1)[OF \<open>l = length xs + length ys'\<close> length_xs length_ys'] by auto
    finally have "nths (weave A xs ys) A = xs" by auto

    have "nths (weave A xs ys) (-A) = nths (weave A xs ys' @ [y]) (-A)" unfolding
       \<open>ys = ys' @ [y]\<close> using weave_append2[OF \<open>length xs + length ys' \<notin> A\<close> length_ys'] by metis
    also have "... = nths (weave A xs ys') (-A) @ nths [y] {a. a + (length xs + length ys') \<in> (-A)}"
      using nths_append length_weave by metis
    also have "... = nths (weave A xs ys') (-A) @ [y]"
      using nths_singleton \<open>length xs + length ys' \<notin> A\<close> by auto
    also have "... = ys"
      using Suc.hyps(1)[OF \<open>l = length xs + length ys'\<close> length_xs length_ys'] \<open>ys = ys' @ [y]\<close> by simp
    finally show ?thesis using \<open>nths (weave A xs ys) A = xs\<close> by auto
  qed
qed

lemma set_weave:
assumes "length xs = card {a\<in>A. a < length xs + length ys}"
assumes "length ys = card {a\<in>-A. a < length xs + length ys}"
shows "set (weave A xs ys) = set xs \<union> set ys"
proof
  show "set (weave A xs ys) \<subseteq> set xs \<union> set ys"
  proof
    fix x assume "x\<in>set (weave A xs ys)"
    then obtain i where "weave A xs ys ! i = x" "i<length (weave A xs ys)" by (meson in_set_conv_nth)
    show "x \<in> set xs \<union> set ys"
    proof (cases "i\<in>A")
      case True
      then have "i \<in> {a\<in>A. a < length xs + length ys}" unfolding length_weave
        by (metis \<open>i < length (weave A xs ys)\<close> length_weave mem_Collect_eq)
      then have "{a \<in> A. a < i} \<subset> {a\<in>A. a < length xs + length ys}"
        using Collect_mono \<open>i < length (weave A xs ys)\<close>[unfolded length_weave] le_Suc_ex  less_imp_le_nat trans_less_add1
        le_neq_trans less_irrefl mem_Collect_eq by auto
      then have "card {a \<in> A. a < i} < card {a\<in>A. a < length xs + length ys}" by (simp add: psubset_card_mono)
      then show "x \<in> set xs \<union> set ys"
        unfolding nth_weave[OF \<open>i<length (weave A xs ys)\<close>, unfolded \<open>weave A xs ys ! i = x\<close>] using True
        using UnI1 assms(1) nth_mem by auto
    next
      case False
      have "i\<notin>A \<Longrightarrow> i \<in> {a\<in>-A. a < length xs + length ys}" unfolding length_weave
        by (metis ComplI \<open>i < length (weave A xs ys)\<close> length_weave mem_Collect_eq)
      then have "{a \<in> -A. a < i} \<subset> {a\<in>-A. a < length xs + length ys}"
        using Collect_mono \<open>i < length (weave A xs ys)\<close>[unfolded length_weave] le_Suc_ex  less_imp_le_nat trans_less_add1
        le_neq_trans less_irrefl mem_Collect_eq using False by auto
      then have "card {a \<in> -A. a < i} < card {a\<in>-A. a < length xs + length ys}" by (simp add: psubset_card_mono)
      then show "x \<in> set xs \<union> set ys"
        unfolding nth_weave[OF \<open>i<length (weave A xs ys)\<close>, unfolded \<open>weave A xs ys ! i = x\<close>] using False
        using UnI1 assms(2) nth_mem by auto
    qed
  qed
  show "set xs \<union> set ys \<subseteq> set (weave A xs ys)"
    using nths_weave[OF assms] by (metis Un_subset_iff set_nths_subset)
qed


lemma weave_complementary_nthss[simp]:
 "weave A (nths xs A) (nths xs (-A)) = xs"
proof (induction xs rule:rev_induct)
  case Nil
  then show ?case by (metis gen_length_def length_0_conv length_code length_weave nths_nil)
next
  case (snoc x xs)
  have length_xs:"length xs = length (nths xs A) + length (nths xs (-A))" by (metis length_weave snoc.IH)
  show ?case
  proof (cases "(length xs)\<in>A")
    case True
    have 0:"length (nths xs A) + length (nths xs (-A)) \<in> A" using length_xs True by metis
    have 1:"length (nths xs A) = card {a \<in> A. a < length (nths xs A) + length (nths xs (-A))}"
      using length_nths[of xs A] by (metis (no_types, lifting) Collect_cong length_xs)
    have 2:"nths (xs @ [x]) A = nths xs A @ [x]"
      unfolding nths_append[of xs "[x]" A] using nths_singleton True by auto
    have 3:"nths (xs @ [x]) (-A) = nths xs (-A)"
      unfolding nths_append[of xs "[x]" "-A"] using True by auto
    show ?thesis unfolding 2 3 weave_append1[OF 0 1] snoc.IH by metis
  next
    case False
    have 0:"length (nths xs A) + length (nths xs (-A)) \<notin> A" using length_xs False by metis
    have 1:"length (nths xs (-A)) = card {a \<in> -A. a < length (nths xs A) + length (nths xs (-A))}"
      using length_nths[of xs "-A"] by (metis (no_types, lifting) Collect_cong length_xs)
    have 2:"nths (xs @ [x]) A = nths xs A"
      unfolding nths_append[of xs "[x]" A] using nths_singleton False by auto
    have 3:"nths (xs @ [x]) (-A) = nths xs (-A) @ [x]"
      unfolding nths_append[of xs "[x]" "-A"] using False by auto
    show ?thesis unfolding 2 3 weave_append2[OF 0 1] snoc.IH by metis
  qed
qed

lemma length_nths': "length (nths xs I) = card {i\<in>I. i < length xs}"
unfolding length_nths by meson

end
