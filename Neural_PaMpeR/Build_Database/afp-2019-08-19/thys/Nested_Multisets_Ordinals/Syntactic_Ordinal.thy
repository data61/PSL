(*  Title:       Syntactic Ordinals in Cantor Normal Form
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Author:      Mathias Fleury <mfleury at mpi-inf.mpg.de>, 2016
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Syntactic Ordinals in Cantor Normal Form\<close>

theory Syntactic_Ordinal
imports Hereditary_Multiset "HOL-Library.Product_Order" "HOL-Library.Extended_Nat"
begin


subsection \<open>Natural (Hessenberg) Product\<close>

instantiation hmultiset :: comm_semiring_1
begin

abbreviation \<omega>_exp :: "hmultiset \<Rightarrow> hmultiset" ("\<omega>^") where
  "\<omega>^ \<equiv> \<lambda>m. HMSet {#m#}"

definition one_hmultiset :: hmultiset where
  "1 = \<omega>^0"

abbreviation \<omega> :: hmultiset where
  "\<omega> \<equiv> \<omega>^1"

definition times_hmultiset :: "hmultiset \<Rightarrow> hmultiset \<Rightarrow> hmultiset"  where
  "A * B = HMSet (image_mset (case_prod (+)) (hmsetmset A \<times># hmsetmset B))"

lemma hmsetmset_times:
  "hmsetmset (m * n) = image_mset (case_prod (+)) (hmsetmset m \<times># hmsetmset n)"
  unfolding times_hmultiset_def by simp

instance
proof (intro_classes, goal_cases assoc comm one distrib_plus zeroL zeroR zero_one)
  case (assoc a b c)
  thus ?case
    by (auto simp: times_hmultiset_def Times_mset_image_mset1 Times_mset_image_mset2
      Times_mset_assoc ac_simps intro: multiset.map_cong)
next
  case (comm a b)
  thus ?case
    unfolding times_hmultiset_def
    by (subst product_swap_mset[symmetric]) (auto simp: ac_simps intro: multiset.map_cong)
next
  case (one a)
  thus ?case
    by (auto simp: one_hmultiset_def times_hmultiset_def Times_mset_single_left)
next
  case (distrib_plus a b c)
  thus ?case
    by (auto simp: plus_hmultiset_def times_hmultiset_def)
next
  case (zeroL a)
  thus ?case
    by (auto simp: times_hmultiset_def)
next
  case (zeroR a)
  thus ?case
    by (auto simp: times_hmultiset_def)
next
  case zero_one
  thus ?case
    by (auto simp: one_hmultiset_def)
qed

end

lemma empty_times_left_hmset[simp]: "HMSet {#} * M = 0"
  by (simp add: times_hmultiset_def)

lemma empty_times_right_hmset[simp]: "M * HMSet {#} = 0"
  by (metis mult_zero_right zero_hmultiset_def)

lemma singleton_times_left_hmset[simp]: "\<omega>^M * N = HMSet (image_mset ((+) M) (hmsetmset N))"
  by (simp add: times_hmultiset_def Times_mset_single_left)

lemma singleton_times_right_hmset[simp]: "N * \<omega>^M = HMSet (image_mset ((+) M) (hmsetmset N))"
  by (metis mult.commute singleton_times_left_hmset)


subsection \<open>Inequalities\<close>

definition plus_nmultiset :: "unit nmultiset \<Rightarrow> unit nmultiset \<Rightarrow> unit nmultiset"  where
  "plus_nmultiset X Y = Rep_hmultiset (Abs_hmultiset X + Abs_hmultiset Y)"

lemma plus_nmultiset_mono:
  assumes less: "(X, Y) < (X', Y')" and no_elem: "no_elem X" "no_elem Y" "no_elem X'" "no_elem Y'"
  shows "plus_nmultiset X Y < plus_nmultiset X' Y'"
  using less[unfolded less_le_not_le] no_elem
  by (auto simp: plus_nmultiset_def plus_hmultiset_def less_multiset_ext\<^sub>D\<^sub>M_less less_eq_nmultiset_def
          union_less_mono type_definition.Abs_inverse[OF type_definition_hmultiset, simplified]
        elim!: no_elem.cases)

lemma plus_hmultiset_transfer[transfer_rule]:
  "(rel_fun pcr_hmultiset (rel_fun pcr_hmultiset pcr_hmultiset)) plus_nmultiset (+)"
  unfolding rel_fun_def plus_nmultiset_def pcr_hmultiset_def nmultiset.rel_eq eq_OO cr_hmultiset_def
  by (auto simp: type_definition.Rep_inverse[OF type_definition_hmultiset])

lemma Times_mset_monoL:
  assumes less: "M < N" and Z_nemp: "Z \<noteq> {#}"
  shows "M \<times># Z < N \<times># Z"
proof -
  obtain Y X where
    Y_nemp: "Y \<noteq> {#}" and Y_sub_N: "Y \<subseteq># N" and M_eq: "M = N - Y + X" and
    ex_Y: "\<forall>x. x \<in># X \<longrightarrow> (\<exists>y. y \<in># Y \<and> x < y)"
    using less[unfolded less_multiset\<^sub>D\<^sub>M] by blast

  let ?X = "X \<times># Z"
  let ?Y = "Y \<times># Z"

  show ?thesis
    unfolding less_multiset\<^sub>D\<^sub>M
  proof (intro exI conjI)
    show "M \<times># Z = N \<times># Z - ?Y + ?X"
      unfolding M_eq by (auto simp: Sigma_mset_Diff_distrib1)
  next
    obtain y where y: "\<forall>x. x \<in># X \<longrightarrow> y x \<in># Y \<and> x < y x"
      using ex_Y by moura

    show "\<forall>x. x \<in># ?X \<longrightarrow> (\<exists>y. y \<in># ?Y \<and> x < y)"
    proof (intro allI impI)
      fix x
      assume "x \<in># ?X"
      thus "\<exists>y. y \<in># ?Y \<and> x < y"
        using y by (intro exI[of _ "(y (fst x), snd x)"]) (auto simp: less_le_not_le)
    qed
  qed (auto simp: Z_nemp Y_nemp Y_sub_N Sigma_mset_mono)
qed

lemma times_hmultiset_monoL:
  "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a * c < b * c" for a b c :: hmultiset
  by (cases a, cases b, cases c, hypsubst_thin,
    unfold times_hmultiset_def zero_hmultiset_def hmultiset.sel, transfer,
    auto simp: less_multiset_ext\<^sub>D\<^sub>M_less multiset.pred_set
      intro!: image_mset_strict_mono Times_mset_monoL elim!: plus_nmultiset_mono)

instance hmultiset :: linordered_semiring_strict
  by intro_classes (subst (1 2) mult.commute, rule times_hmultiset_monoL)

lemma mult_le_mono1_hmset: "i \<le> j \<Longrightarrow> i * k \<le> j * k" for i j k :: hmultiset
  by (simp add: mult_right_mono)

lemma mult_le_mono2_hmset: "i \<le> j \<Longrightarrow> k * i \<le> k * j" for i j k :: hmultiset
  by (simp add: mult_left_mono)

lemma mult_le_mono_hmset: "i \<le> j \<Longrightarrow> k \<le> l \<Longrightarrow> i * k \<le> j * l" for i j k l :: hmultiset
  by (simp add: mult_mono)

lemma less_iff_add1_le_hmset: "m < n \<longleftrightarrow> m + 1 \<le> n" for m n :: hmultiset
proof (cases m n rule: hmultiset.exhaust[case_product hmultiset.exhaust])
  case (HMSet_HMSet m0 n0)
  note m = this(1) and n = this(2)

  show ?thesis
  proof (simp add: m n one_hmultiset_def plus_hmultiset_def order.order_iff_strict
      less_multiset_ext\<^sub>D\<^sub>M_less, intro iffI)
    assume m0_lt_n0: "m0 < n0"
    note
      m0_ne_n0 = m0_lt_n0[unfolded less_multiset\<^sub>H\<^sub>O, THEN conjunct1] and
      ex_n0_gt_m0 = m0_lt_n0[unfolded less_multiset\<^sub>H\<^sub>O, THEN conjunct2, rule_format]

    {
      assume zero_m0_gt_n0: "add_mset 0 m0 > n0"
      note
        n0_ne_0m0 = zero_m0_gt_n0[unfolded less_multiset\<^sub>H\<^sub>O, THEN conjunct1] and
        ex_0m0_gt_n0 = zero_m0_gt_n0[unfolded less_multiset\<^sub>H\<^sub>O, THEN conjunct2, rule_format]

      {
        fix y
        assume m0y_lt_n0y: "count m0 y < count n0 y"

        have "\<exists>x > y. count n0 x < count m0 x"
        proof (cases "count (add_mset 0 m0) y < count n0 y")
          case True
          then obtain aa where
            aa_gt_y: "aa > y" and
            count_n0aa_lt_count_0m0aa: "count n0 aa < count (add_mset 0 m0) aa"
            using ex_0m0_gt_n0 by blast
          have "aa \<noteq> 0"
            by (rule gr_implies_not_zero_hmset[OF aa_gt_y])
          hence "count (add_mset 0 m0) aa = count m0 aa"
            by simp
          thus ?thesis
            using count_n0aa_lt_count_0m0aa aa_gt_y by auto
        next
          case not_0m0_y_lt_n0y: False
          hence y_eq_0: "y = 0"
            by (metis count_add_mset m0y_lt_n0y)
          have sm0y_eq_n0y: "Suc (count m0 y) = count n0 y"
            using m0y_lt_n0y not_0m0_y_lt_n0y count_add_mset[of 0 _ 0] unfolding y_eq_0 by simp

          obtain bb where "count n0 bb < count (add_mset 0 m0) bb"
            using lt_imp_ex_count_lt[OF zero_m0_gt_n0] by blast
          hence n0bb_lt_m0bb: "count n0 bb < count m0 bb"
            unfolding count_add_mset by (metis (full_types) less_irrefl_nat sm0y_eq_n0y y_eq_0)
          hence "bb \<noteq> 0"
            using sm0y_eq_n0y y_eq_0 by auto
          thus ?thesis
            unfolding y_eq_0 using n0bb_lt_m0bb not_gr_zero_hmset by blast
        qed
      }
      hence "n0 < m0"
        unfolding less_multiset\<^sub>H\<^sub>O using m0_ne_n0 by blast
      hence False
        using m0_lt_n0 by simp
    }
    thus "add_mset 0 m0 < n0 \<or> add_mset 0 m0 = n0"
      using antisym_conv3 by blast
  next
    assume "add_mset 0 m0 < n0 \<or> add_mset 0 m0 = n0"
    thus "m0 < n0"
      using dual_order.strict_trans le_multiset_right_total by blast
  qed
qed

lemma zero_less_iff_1_le_hmset: "0 < n \<longleftrightarrow> 1 \<le> n" for n :: hmultiset
  by (rule less_iff_add1_le_hmset[of 0, simplified])

lemma less_add_1_iff_le_hmset: "m < n + 1 \<longleftrightarrow> m \<le> n" for m n :: hmultiset
  by (rule less_iff_add1_le_hmset[of m "n + 1", simplified])

instance hmultiset :: ordered_cancel_comm_semiring
  by intro_classes (simp add: mult_le_mono2_hmset)

instance hmultiset :: zero_less_one
  by intro_classes (simp add: zero_less_iff_neq_zero_hmset)

instance hmultiset :: linordered_semiring_1_strict
  by intro_classes

instance hmultiset :: bounded_lattice_bot
  by intro_classes

instance hmultiset :: linordered_nonzero_semiring
  by intro_classes simp

instance hmultiset :: semiring_no_zero_divisors
  by intro_classes (use mult_pos_pos not_gr_zero_hmset in blast)

lemma lt_1_iff_eq_0_hmset: "M < 1 \<longleftrightarrow> M = 0" for M :: hmultiset
  by (simp add: less_iff_add1_le_hmset)

lemma zero_less_mult_iff_hmset[simp]: "0 < m * n \<longleftrightarrow> 0 < m \<and> 0 < n" for m n :: hmultiset
  using mult_eq_0_iff not_gr_zero_hmset by blast

lemma one_le_mult_iff_hmset[simp]: "1 \<le> m * n \<longleftrightarrow> 1 \<le> m \<and> 1 \<le> n" for m n :: hmultiset
  by (metis lt_1_iff_eq_0_hmset mult_eq_0_iff not_le)

lemma mult_less_cancel2_hmset[simp]: "m * k < n * k \<longleftrightarrow> 0 < k \<and> m < n" for k m n :: hmultiset
  by (metis gr_zeroI_hmset leD leI le_cases mult_right_mono mult_zero_right times_hmultiset_monoL)

lemma mult_less_cancel1_hmset[simp]: "k * m < k * n \<longleftrightarrow> 0 < k \<and> m < n" for k m n :: hmultiset
  by (simp add: mult.commute[of k])

lemma mult_le_cancel1_hmset[simp]: "k * m \<le> k * n \<longleftrightarrow> (0 < k \<longrightarrow> m \<le> n)" for k m n :: hmultiset
  by (simp add: linorder_not_less[symmetric], auto)

lemma mult_le_cancel2_hmset[simp]: "m * k \<le> n * k \<longleftrightarrow> (0 < k \<longrightarrow> m \<le> n)" for k m n :: hmultiset
  by (simp add: linorder_not_less[symmetric], auto)

lemma mult_le_cancel_left1_hmset: "y > 0 \<Longrightarrow> x \<le> x * y" for x y :: hmultiset
  by (metis zero_less_iff_1_le_hmset mult.commute mult.left_neutral mult_le_cancel2_hmset)

lemma mult_le_cancel_left2_hmset: "y \<le> 1 \<Longrightarrow> x * y \<le> x" for x y :: hmultiset
  by (metis mult.commute mult.left_neutral mult_le_cancel2_hmset)

lemma mult_le_cancel_right1_hmset: "y > 0 \<Longrightarrow> x \<le> y * x" for x y :: hmultiset
  by (subst mult.commute) (fact mult_le_cancel_left1_hmset)

lemma mult_le_cancel_right2_hmset: "y \<le> 1 \<Longrightarrow> y * x \<le> x" for x y :: hmultiset
  by (subst mult.commute) (fact mult_le_cancel_left2_hmset)

lemma le_square_hmset: "m \<le> m * m" for m :: hmultiset
  using mult_le_cancel_left1_hmset by force

lemma le_cube_hmset: "m \<le> m * (m * m)" for m :: hmultiset
  using mult_le_cancel_left1_hmset by force

lemma
  less_imp_minus_plus_hmset: "m < n \<Longrightarrow> k < k - m + n" and
  le_imp_minus_plus_hmset: "m \<le> n \<Longrightarrow> k \<le> k - m + n" for k m n :: hmultiset
  by (meson add_less_cancel_left leD le_minus_plus_same_hmset less_le_trans not_le_imp_less)+

lemma gt_0_lt_mult_gt_1_hmset:
  fixes m n :: hmultiset
  assumes "m > 0" and "n > 1"
  shows "m < m * n"
  using assms by (metis mult.right_neutral mult_less_cancel1_hmset)

instance hmultiset :: linordered_comm_semiring_strict
  by intro_classes simp


subsection \<open>Embedding of Natural Numbers\<close>

lemma of_nat_hmset: "of_nat n = HMSet (replicate_mset n 0)"
  by (induct n) (auto simp: zero_hmultiset_def one_hmultiset_def plus_hmultiset_def)

lemma of_nat_inject_hmset[simp]: "(of_nat m :: hmultiset) = of_nat n \<longleftrightarrow> m = n"
  unfolding of_nat_hmset by simp

lemma of_nat_minus_hmset: "of_nat (m - n) = (of_nat m :: hmultiset) - of_nat n"
  unfolding of_nat_hmset minus_hmultiset_def by simp

lemma plus_of_nat_plus_of_nat_hmset:
  "k + of_nat m + of_nat n = k + of_nat (m + n)" for k :: hmultiset
  by simp

lemma plus_of_nat_minus_of_nat_hmset:
  fixes k :: hmultiset
  assumes "n \<le> m"
  shows "k + of_nat m - of_nat n = k + of_nat (m - n)"
  using assms by (metis add.left_commute add_diff_cancel_left' le_add_diff_inverse of_nat_add)

lemma of_nat_lt_\<omega>[simp]: "of_nat n < \<omega>"
  by (auto simp: of_nat_hmset zero_less_iff_neq_zero_hmset less_multiset_ext\<^sub>D\<^sub>M_less)

lemma of_nat_ne_\<omega>[simp]: "of_nat n \<noteq> \<omega>"
  by (simp add: neq_iff)

lemma of_nat_less_hmset[simp]: "(of_nat M :: hmultiset) < of_nat N \<longleftrightarrow> M < N"
  unfolding of_nat_hmset less_multiset_ext\<^sub>D\<^sub>M_less by simp

lemma of_nat_le_hmset[simp]: "(of_nat M :: hmultiset) \<le> of_nat N \<longleftrightarrow> M \<le> N"
  unfolding of_nat_hmset order_le_less less_multiset_ext\<^sub>D\<^sub>M_less by simp

lemma of_nat_times_\<omega>_exp: "of_nat n * \<omega>^m = HMSet (replicate_mset n m)"
  by (induct n) (simp_all add: hmsetmset_plus one_hmultiset_def)

lemma \<omega>_exp_times_of_nat: "\<omega>^m * of_nat n = HMSet (replicate_mset n m)"
  using of_nat_times_\<omega>_exp by simp


subsection \<open>Embedding of Extended Natural Numbers\<close>

primrec hmset_of_enat :: "enat \<Rightarrow> hmultiset" where
  "hmset_of_enat (enat n) = of_nat n"
| "hmset_of_enat \<infinity> = \<omega>"

lemma hmset_of_enat_0[simp]: "hmset_of_enat 0 = 0"
  by (simp add: zero_enat_def)

lemma hmset_of_enat_1[simp]: "hmset_of_enat 1 = 1"
  by (simp add: one_enat_def del: One_nat_def)

lemma hmset_of_enat_of_nat[simp]: "hmset_of_enat (of_nat n) = of_nat n"
  using of_nat_eq_enat by auto

lemma hmset_of_enat_numeral[simp]: "hmset_of_enat (numeral n) = numeral n"
  by (simp add: numeral_eq_enat)

lemma hmset_of_enat_le_\<omega>[simp]: "hmset_of_enat n \<le> \<omega>"
  using of_nat_lt_\<omega>[THEN less_imp_le] by (cases n) auto

lemma hmset_of_enat_eq_\<omega>_iff[simp]: "hmset_of_enat n = \<omega> \<longleftrightarrow> n = \<infinity>"
  by (cases n) auto


subsection \<open>Head Omega\<close>

definition head_\<omega> :: "hmultiset \<Rightarrow> hmultiset" where
  "head_\<omega> M = (if M = 0 then 0 else \<omega>^(Max (set_mset (hmsetmset M))))"

lemma head_\<omega>_subseteq: "hmsetmset (head_\<omega> M) \<subseteq># hmsetmset M"
  unfolding head_\<omega>_def by simp

lemma head_\<omega>_eq_0_iff[simp]: "head_\<omega> m = 0 \<longleftrightarrow> m = 0"
  unfolding head_\<omega>_def zero_hmultiset_def by simp

lemma head_\<omega>_0[simp]: "head_\<omega> 0 = 0"
  by simp

lemma head_\<omega>_1[simp]: "head_\<omega> 1 = 1"
  unfolding head_\<omega>_def one_hmultiset_def by simp

lemma head_\<omega>_of_nat[simp]: "head_\<omega> (of_nat n) = (if n = 0 then 0 else 1)"
  unfolding head_\<omega>_def one_hmultiset_def of_nat_hmset by simp

lemma head_\<omega>_numeral[simp]: "head_\<omega> (numeral n) = 1"
  by (metis head_\<omega>_of_nat of_nat_numeral zero_neq_numeral)

lemma head_\<omega>_\<omega>[simp]: "head_\<omega> \<omega> = \<omega>"
  unfolding head_\<omega>_def by simp

lemma le_imp_head_\<omega>_le:
  assumes m_le_n: "m \<le> n"
  shows "head_\<omega> m \<le> head_\<omega> n"
proof -
  have le_in_le_max: "\<And>a M N. M \<le> N \<Longrightarrow> a \<in># M \<Longrightarrow> a \<le> Max (set_mset N)"
    by (metis (no_types) Max_ge finite_set_mset le_less less_eq_multiset\<^sub>H\<^sub>O linorder_not_less
      mem_Collect_eq neq0_conv order_trans set_mset_def)
  show ?thesis
    using m_le_n unfolding head_\<omega>_def
    by (cases m, cases n,
      auto simp del: hmsetmset_le simp: head_\<omega>_def hmsetmset_le[symmetric] zero_hmultiset_def,
      metis Max_in dual_order.antisym finite_set_mset le_in_le_max le_less set_mset_eq_empty_iff)
qed

lemma head_\<omega>_lt_imp_lt: "head_\<omega> m < head_\<omega> n \<Longrightarrow> m < n"
  unfolding head_\<omega>_def hmsetmset_less[symmetric]
  by (rule all_lt_Max_imp_lt_mset, auto simp: zero_hmultiset_def split: if_splits)

lemma head_\<omega>_plus[simp]: "head_\<omega> (m + n) = sup (head_\<omega> m) (head_\<omega> n)"
proof (cases m n rule: hmultiset.exhaust[case_product hmultiset.exhaust])
  case m_n: (HMSet_HMSet M N)
  show ?thesis
  proof (cases "Max_mset M < Max_mset N")
    case True
    thus ?thesis
      unfolding m_n head_\<omega>_def sup_hmultiset_def zero_hmultiset_def plus_hmultiset_def
      by (simp add: Max.union max_def dual_order.strict_implies_order)
  next
    case False
    thus ?thesis
      unfolding m_n head_\<omega>_def sup_hmultiset_def zero_hmultiset_def plus_hmultiset_def
      by simp (metis False Max.union finite_set_mset leI max_def set_mset_eq_empty_iff sup.commute)
  qed
qed

lemma head_\<omega>_times[simp]: "head_\<omega> (m * n) = head_\<omega> m * head_\<omega> n"
proof (cases "m = 0 \<or> n = 0")
  case False
  hence m_nz: "m \<noteq> 0" and n_nz: "n \<noteq> 0"
    by simp+

  define \<delta> where "\<delta> = hmsetmset m"
  define \<epsilon> where "\<epsilon> = hmsetmset n"

  have \<delta>_nemp: "\<delta> \<noteq> {#}"
    unfolding \<delta>_def using m_nz by simp
  have \<epsilon>_nemp: "\<epsilon> \<noteq> {#}"
    unfolding \<epsilon>_def using n_nz by simp

  let ?D = "set_mset \<delta>"
  let ?E = "set_mset \<epsilon>"
  let ?DE = "{z. \<exists>x \<in> ?D. \<exists>y \<in> ?E. z = x + y}"

  have max_D_in: "Max ?D \<in> ?D"
    using \<delta>_nemp by simp
  have max_E_in: "Max ?E \<in> ?E"
    using \<epsilon>_nemp by simp

  have "Max ?DE = Max ?D + Max ?E"
  proof (rule order_antisym, goal_cases le ge)
    case le
    have "\<And>x y. x \<in> ?D \<Longrightarrow> y \<in> ?E \<Longrightarrow> x + y \<le> Max ?D + Max ?E"
      by (simp add: add_mono)
    hence mem_imp_le: "\<And>z. z \<in> ?DE \<Longrightarrow> z \<le> Max ?D + Max ?E"
      by auto
    show ?case
      by (intro mem_imp_le Max_in, simp, use \<delta>_nemp \<epsilon>_nemp in fast)
  next
    case ge
    have "{z. \<exists>x \<in> {Max ?D}. \<exists>y \<in> {Max ?E}. z = x + y} \<subseteq> {z. \<exists>x \<in># \<delta>. \<exists>y \<in># \<epsilon>. z = x + y}"
      using max_D_in max_E_in by fast
    thus ?case
      by simp
  qed
  thus ?thesis
    unfolding \<delta>_def \<epsilon>_def by (auto simp: head_\<omega>_def image_def times_hmultiset_def)
qed auto


subsection \<open>More Inequalities and Some Equalities\<close>

lemma zero_lt_\<omega>[simp]: "0 < \<omega>"
  by (metis of_nat_lt_\<omega> of_nat_0)

lemma one_lt_\<omega>[simp]: "1 < \<omega>"
  by (metis enat_defs(2) hmset_of_enat.simps(1) hmset_of_enat_1 of_nat_lt_\<omega>)

lemma numeral_lt_\<omega>[simp]: "numeral n < \<omega>"
  using hmset_of_enat_numeral[symmetric] hmset_of_enat.simps(1) of_nat_lt_\<omega> numeral_eq_enat
  by presburger

lemma one_le_\<omega>[simp]: "1 \<le> \<omega>"
  by (simp add: less_imp_le)

lemma of_nat_le_\<omega>[simp]: "of_nat n \<le> \<omega>"
  by (simp add: le_less)

lemma numeral_le_\<omega>[simp]: "numeral n \<le> \<omega>"
  by (simp add: less_imp_le)

lemma not_\<omega>_lt_1[simp]: "\<not> \<omega> < 1"
  by (simp add: not_less)

lemma not_\<omega>_lt_of_nat[simp]: "\<not> \<omega> < of_nat n"
  by (simp add: not_less)

lemma not_\<omega>_lt_numeral[simp]: "\<not> \<omega> < numeral n"
  by (simp add: not_less)

lemma not_\<omega>_le_1[simp]: "\<not> \<omega> \<le> 1"
  by (simp add: not_le)

lemma not_\<omega>_le_of_nat[simp]: "\<not> \<omega> \<le> of_nat n"
  by (simp add: not_le)

lemma not_\<omega>_le_numeral[simp]: "\<not> \<omega> \<le> numeral n"
  by (simp add: not_le)

lemma zero_ne_\<omega>[simp]: "0 \<noteq> \<omega>"
  by (metis not_\<omega>_le_1 zero_le_hmset)

lemma one_ne_\<omega>[simp]: "1 \<noteq> \<omega>"
  using not_\<omega>_le_1 by force

lemma numeral_ne_\<omega>[simp]: "numeral n \<noteq> \<omega>"
  by (metis not_\<omega>_le_numeral numeral_le_\<omega>)

lemma
  \<omega>_ne_0[simp]: "\<omega> \<noteq> 0" and
  \<omega>_ne_1[simp]: "\<omega> \<noteq> 1" and
  \<omega>_ne_of_nat[simp]: "\<omega> \<noteq> of_nat m" and
  \<omega>_ne_numeral[simp]: "\<omega> \<noteq> numeral n"
  using zero_ne_\<omega> one_ne_\<omega> of_nat_ne_\<omega> numeral_ne_\<omega> by metis+

lemma
  hmset_of_enat_inject[simp]: "hmset_of_enat m = hmset_of_enat n \<longleftrightarrow> m = n" and
  hmset_of_enat_less[simp]: "hmset_of_enat m < hmset_of_enat n \<longleftrightarrow> m < n" and
  hmset_of_enat_le[simp]: "hmset_of_enat m \<le> hmset_of_enat n \<longleftrightarrow> m \<le> n"
  by (cases m; cases n; simp)+

lemma lt_\<omega>_imp_ex_of_nat:
  assumes M_lt_\<omega>: "M < \<omega>"
  shows "\<exists>n. M = of_nat n"
proof -
  have M_lt_single_1: "hmsetmset M < {#1#}"
    by (rule M_lt_\<omega>[unfolded hmsetmset_less[symmetric] less_multiset_ext\<^sub>D\<^sub>M_less hmultiset.sel])

  have "N = 0" if "N \<in># hmsetmset M" for N
  proof -
    have "0 < count (hmsetmset M) N"
      using that by auto
    hence "N < 1"
      by (metis (no_types) M_lt_single_1 count_single gr_implies_not0 less_eq_multiset\<^sub>H\<^sub>O less_one
        neq_iff not_le)
    thus ?thesis
      by (simp add: lt_1_iff_eq_0_hmset)
  qed
  then obtain n where hmmM: "M = HMSet (replicate_mset n 0)"
    using ex_replicate_mset_if_all_elems_eq by (metis hmultiset.collapse)
  show ?thesis
    unfolding hmmM of_nat_hmset by blast
qed

lemma le_\<omega>_imp_ex_hmset_of_enat:
  assumes M_le_\<omega>: "M \<le> \<omega>"
  shows "\<exists>n. M = hmset_of_enat n"
proof (cases "M = \<omega>")
  case True
  thus ?thesis
    by (metis hmset_of_enat.simps(2))
next
  case False
  thus ?thesis
    using M_le_\<omega> lt_\<omega>_imp_ex_of_nat by (metis hmset_of_enat.simps(1) le_less)
qed

lemma lt_\<omega>_lt_\<omega>_imp_times_lt_\<omega>: "M < \<omega> \<Longrightarrow> N < \<omega> \<Longrightarrow> M * N < \<omega>"
  by (metis lt_\<omega>_imp_ex_of_nat of_nat_lt_\<omega> of_nat_mult)

lemma times_\<omega>_minus_of_nat[simp]: "m * \<omega> - of_nat n = m * \<omega>"
  by (auto intro!: Diff_triv_mset simp: times_hmultiset_def minus_hmultiset_def
    Times_mset_single_right of_nat_hmset disjunct_not_in image_def)

lemma times_\<omega>_minus_numeral[simp]: "m * \<omega> - numeral n = m * \<omega>"
  by (metis of_nat_numeral times_\<omega>_minus_of_nat)

lemma \<omega>_minus_of_nat[simp]: "\<omega> - of_nat n = \<omega>"
  using times_\<omega>_minus_of_nat[of 1] by (metis mult.left_neutral)

lemma \<omega>_minus_1[simp]: "\<omega> - 1 = \<omega>"
  using \<omega>_minus_of_nat[of 1] by simp

lemma \<omega>_minus_numeral[simp]: "\<omega> - numeral n = \<omega>"
  using times_\<omega>_minus_numeral[of 1] by (metis mult.left_neutral)

lemma hmset_of_enat_minus_enat[simp]: "hmset_of_enat (m - enat n) = hmset_of_enat m - of_nat n"
  by (cases m) (auto simp: of_nat_minus_hmset)

lemma of_nat_lt_hmset_of_enat_iff: "of_nat m < hmset_of_enat n \<longleftrightarrow> enat m < n"
  by (metis hmset_of_enat.simps(1) hmset_of_enat_less)

lemma of_nat_le_hmset_of_enat_iff: "of_nat m \<le> hmset_of_enat n \<longleftrightarrow> enat m \<le> n"
  by (metis hmset_of_enat.simps(1) hmset_of_enat_le)

lemma hmset_of_enat_lt_iff_ne_infinity: "hmset_of_enat x < \<omega> \<longleftrightarrow> x \<noteq> \<infinity>"
  by (cases x; simp)

lemma minus_diff_sym_hmset: "m - (m - n) = n - (n - m)" for m n :: hmultiset
  unfolding minus_hmultiset_def by simp (metis multiset_inter_def subset_mset.inf_aci(1))

lemma diff_plus_sym_hmset: "(c - b) + b = (b - c) + c" for b c :: hmultiset
proof -
  have f1: "\<And>h ha :: hmultiset. h - (ha + h) = 0"
    by (simp add: add.commute)
  have f2: "\<And>h ha hb :: hmultiset. h + ha - (h - hb) = hb + ha - (hb - h)"
    by (metis (no_types) add_diff_cancel_right minus_diff_sym_hmset)
  have "\<And>h ha hb :: hmultiset. h + (ha + hb) - hb = h + ha"
    by (metis (no_types) add.assoc add_diff_cancel_right')
  then show ?thesis
    using f2 f1 by (metis (no_types) add.commute add.right_neutral diff_diff_add_hmset)
qed

lemma times_diff_plus_sym_hmset: "a * (c - b) + a * b = a * (b - c) + a * c" for a b c :: hmultiset
  by (metis distrib_left diff_plus_sym_hmset)

lemma times_of_nat_minus_left:
  "(of_nat m - of_nat n) * l = of_nat m * l - of_nat n * l" for l :: hmultiset
  by (induct n m rule: diff_induct) (auto simp: ring_distribs)

lemma times_of_nat_minus_right:
  "l * (of_nat m - of_nat n) = l * of_nat m - l * of_nat n" for l :: hmultiset
  by (metis times_of_nat_minus_left mult.commute)

lemma lt_\<omega>_imp_times_minus_left: "m < \<omega> \<Longrightarrow> n < \<omega> \<Longrightarrow> (m - n) * l = m * l - n * l"
  by (metis lt_\<omega>_imp_ex_of_nat times_of_nat_minus_left)

lemma lt_\<omega>_imp_times_minus_right: "m < \<omega> \<Longrightarrow> n < \<omega> \<Longrightarrow> l * (m - n) = l * m - l * n"
  by (metis lt_\<omega>_imp_ex_of_nat times_of_nat_minus_right)

lemma hmset_pair_decompose:
  "\<exists>k n1 n2. m1 = k + n1 \<and> m2 = k + n2 \<and> (head_\<omega> n1 \<noteq> head_\<omega> n2 \<or> n1 = 0 \<and> n2 = 0)"
proof -
  define n1 where n1: "n1 = m1 - m2"
  define n2 where n2: "n2 = m2 - m1"
  define k where k1: "k = m1 - n1"

  have k2: "k = m2 - n2"
    using k1 unfolding n1 n2 by (simp add: minus_diff_sym_hmset)

  have "m1 = k + n1"
    unfolding k1
    by (metis (no_types) n1 add_diff_cancel_left add.commute add_diff_cancel_right' diff_add_zero
      diff_diff_add minus_diff_sym_hmset)
  moreover have "m2 = k + n2"
    unfolding k2
    by (metis n2 add.commute add_diff_cancel_left add_diff_cancel_left' add_diff_cancel_right'
      diff_add_zero diff_diff_add diff_zero k2 minus_diff_sym_hmset)
  moreover have hd_n: "head_\<omega> n1 \<noteq> head_\<omega> n2" if n1_or_n2_nz: "n1 \<noteq> 0 \<or> n2 \<noteq> 0"
  proof (cases "n1 = 0" "n2 = 0" rule: bool.exhaust[case_product bool.exhaust])
    case False_False
    note n1_nz = this(1)[simplified] and n2_nz = this(2)[simplified]

    define \<delta>1 where "\<delta>1 = hmsetmset n1"
    define \<delta>2 where "\<delta>2 = hmsetmset n2"

    have \<delta>1_inter_\<delta>2: "\<delta>1 \<inter># \<delta>2 = {#}"
      unfolding \<delta>1_def \<delta>2_def n1 n2 minus_hmultiset_def by (simp add: diff_intersect_sym_diff)

    have \<delta>1_ne: "\<delta>1 \<noteq> {#}"
      unfolding \<delta>1_def using n1_nz by simp
    have \<delta>2_ne: "\<delta>2 \<noteq> {#}"
      unfolding \<delta>2_def using n2_nz by simp

    have max_\<delta>1: "Max (set_mset \<delta>1) \<in># \<delta>1"
      using \<delta>1_ne by simp
    have max_\<delta>2: "Max (set_mset \<delta>2) \<in># \<delta>2"
      using \<delta>2_ne by simp
    have max_\<delta>1_ne_\<delta>2: "Max (set_mset \<delta>1) \<noteq> Max (set_mset \<delta>2)"
      using \<delta>1_inter_\<delta>2 disjunct_not_in max_\<delta>1 max_\<delta>2 by force

    show ?thesis
      using n1_nz n2_nz
      by (cases n1 rule: hmultiset.exhaust_sel, cases n2 rule: hmultiset.exhaust_sel,
        auto simp: head_\<omega>_def zero_hmultiset_def max_\<delta>1_ne_\<delta>2[unfolded \<delta>1_def \<delta>2_def])
  qed (use n1_or_n2_nz in \<open>auto simp: head_\<omega>_def\<close>)
  ultimately show ?thesis
    by blast
qed

lemma hmset_pair_decompose_less:
  assumes m1_lt_m2: "m1 < m2"
  shows "\<exists>k n1 n2. m1 = k + n1 \<and> m2 = k + n2 \<and> head_\<omega> n1 < head_\<omega> n2"
proof -
  obtain k n1 n2 where
    m1: "m1 = k + n1" and
    m2: "m2 = k + n2" and
    hds: "head_\<omega> n1 \<noteq> head_\<omega> n2 \<or> n1 = 0 \<and> n2 = 0"
    using hmset_pair_decompose[of m1 m2] by blast

  {
    assume "n1 = 0" and "n2 = 0"
    hence "m1 = m2"
      unfolding m1 m2 by simp
    hence False
      using m1_lt_m2 by simp
  }
  moreover
  {
    assume "head_\<omega> n1 > head_\<omega> n2"
    hence "n1 > n2"
      by (rule head_\<omega>_lt_imp_lt)
    hence "m1 > m2"
      unfolding m1 m2 by simp
    hence False
      using m1_lt_m2 by simp
  }
  ultimately show ?thesis
    using m1 m2 hds by (blast elim: neqE)
qed

lemma hmset_pair_decompose_less_eq:
  assumes "m1 \<le> m2"
  shows "\<exists>k n1 n2. m1 = k + n1 \<and> m2 = k + n2 \<and> (head_\<omega> n1 < head_\<omega> n2 \<or> n1 = 0 \<and> n2 = 0)"
  using assms
  by (metis add_cancel_right_right hmset_pair_decompose_less order.not_eq_order_implies_strict)

lemma mono_cross_mult_less_hmset:
  fixes Aa A Ba B :: hmultiset
  assumes A_lt: "A < Aa" and B_lt: "B < Ba"
  shows "A * Ba + B * Aa < A * B + Aa * Ba"
proof -
  obtain j m1 m2 where A: "A = j + m1" and Aa: "Aa = j + m2" and hd_m: "head_\<omega> m1 < head_\<omega> m2"
    by (metis hmset_pair_decompose_less[OF A_lt])
  obtain k n1 n2 where B: "B = k + n1" and Ba: "Ba = k + n2" and hd_n: "head_\<omega> n1 < head_\<omega> n2"
    by (metis hmset_pair_decompose_less[OF B_lt])

  have hd_lt: "head_\<omega> (m1 * n2 + m2 * n1) < head_\<omega> (m1 * n1 + m2 * n2)"
  proof simp
    have "\<And>h ha :: hmultiset. 0 < h \<or> \<not> ha < h"
      by force
    hence "\<not> head_\<omega> m2 * head_\<omega> n2 \<le> sup (head_\<omega> m1 * head_\<omega> n2) (head_\<omega> m2 * head_\<omega> n1)"
      using hd_m hd_n sup_hmultiset_def by auto
    thus "sup (head_\<omega> m1 * head_\<omega> n2) (head_\<omega> m2 * head_\<omega> n1)
      < sup (head_\<omega> m1 * head_\<omega> n1) (head_\<omega> m2 * head_\<omega> n2)"
      by (meson leI sup.bounded_iff)
  qed
  show ?thesis
    unfolding A Aa B Ba ring_distribs by (simp add: algebra_simps head_\<omega>_lt_imp_lt[OF hd_lt])
qed

lemma triple_cross_mult_hmset:
  "An * (Bn * Cn + Bp * Cp - (Bn * Cp + Cn * Bp))
   + (Cn * (An * Bp + Bn * Ap - (An * Bn + Ap * Bp))
      + (Ap * (Bn * Cp + Cn * Bp - (Bn * Cn + Bp * Cp))
         + Cp * (An * Bn + Ap * Bp - (An * Bp + Bn * Ap)))) =
   An * (Bn * Cp + Cn * Bp - (Bn * Cn + Bp * Cp))
   + (Cn * (An * Bn + Ap * Bp - (An * Bp + Bn * Ap))
      + (Ap * (Bn * Cn + Bp * Cp - (Bn * Cp + Cn * Bp))
         + Cp * (An * Bp + Bn * Ap - (An * Bn + Ap * Bp))))"
  for Ap An Bp Bn Cp Cn Dp Dn :: hmultiset
  apply (simp add: algebra_simps)
  apply (unfold add.assoc[symmetric])

  apply (rule add_right_cancel[THEN iffD1, of _ "Cp * (An * Bp + Ap * Bn)"])
  apply (unfold add.assoc)
  apply (subst times_diff_plus_sym_hmset)
  apply (unfold add.assoc[symmetric])
  apply (subst (12) add.commute)
  apply (subst (11) add.commute)
  apply (unfold add.assoc[symmetric])

  apply (rule add_right_cancel[THEN iffD1, of _ "Cn * (An * Bn + Ap * Bp)"])
  apply (unfold add.assoc)
  apply (subst times_diff_plus_sym_hmset)
  apply (unfold add.assoc[symmetric])
  apply (subst (14) add.commute)
  apply (subst (13) add.commute)
  apply (unfold add.assoc[symmetric])

  apply (rule add_right_cancel[THEN iffD1, of _ "Ap * (Bn * Cn + Bp * Cp)"])
  apply (unfold add.assoc)
  apply (subst times_diff_plus_sym_hmset)
  apply (unfold add.assoc[symmetric])
  apply (subst (16) add.commute)
  apply (subst (15) add.commute)
  apply (unfold add.assoc[symmetric])

  apply (rule add_right_cancel[THEN iffD1, of _ "An * (Bn * Cp + Bp * Cn)"])
  apply (unfold add.assoc)
  apply (subst times_diff_plus_sym_hmset)
  apply (unfold add.assoc[symmetric])
  apply (subst (18) add.commute)
  apply (subst (17) add.commute)
  apply (unfold add.assoc[symmetric])

  by (simp add: algebra_simps)


subsection \<open>Conversions to Natural Numbers\<close>

definition offset_hmset :: "hmultiset \<Rightarrow> nat" where
  "offset_hmset M = count (hmsetmset M) 0"

lemma offset_hmset_of_nat[simp]: "offset_hmset (of_nat n) = n"
  unfolding offset_hmset_def of_nat_hmset by simp

lemma offset_hmset_numeral[simp]: "offset_hmset (numeral n) = numeral n"
  unfolding offset_hmset_def by (metis offset_hmset_def offset_hmset_of_nat of_nat_numeral)

definition sum_coefs :: "hmultiset \<Rightarrow> nat" where
  "sum_coefs M = size (hmsetmset M)"

lemma sum_coefs_distrib_plus[simp]: "sum_coefs (M + N) = sum_coefs M + sum_coefs N"
  unfolding plus_hmultiset_def sum_coefs_def by simp

lemma sum_coefs_gt_0: "sum_coefs M > 0 \<longleftrightarrow> M > 0"
  by (auto simp: sum_coefs_def zero_hmultiset_def hmsetmset_less[symmetric] less_multiset_ext\<^sub>D\<^sub>M_less
    nonempty_has_size[symmetric])


subsection \<open>An Example\<close>

text \<open>
The following proof is based on an informal proof by Uwe Waldmann, inspired by
a similar argument by Michel Ludwig.
\<close>

lemma ludwig_waldmann_less:
  fixes \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<gamma> \<delta> :: hmultiset
  assumes
    \<alpha>\<beta>2\<gamma>_lt_\<alpha>\<beta>1\<gamma>: "\<alpha>2 + \<beta>2 * \<gamma> < \<alpha>1 + \<beta>1 * \<gamma>" and
    \<beta>2_le_\<beta>1: "\<beta>2 \<le> \<beta>1" and
    \<gamma>_lt_\<delta>: "\<gamma> < \<delta>"
  shows "\<alpha>2 + \<beta>2 * \<delta> < \<alpha>1 + \<beta>1 * \<delta>"
proof -
  obtain \<beta>0 \<beta>2a \<beta>1a where
    \<beta>1: "\<beta>1 = \<beta>0 + \<beta>1a" and
    \<beta>2: "\<beta>2 = \<beta>0 + \<beta>2a" and
    hd_\<beta>2a_vs_\<beta>1a: "head_\<omega> \<beta>2a < head_\<omega> \<beta>1a \<or> \<beta>2a = 0 \<and> \<beta>1a = 0"
    using hmset_pair_decompose_less_eq[OF \<beta>2_le_\<beta>1] by blast

  obtain \<eta> \<gamma>a \<delta>a where
    \<gamma>: "\<gamma> = \<eta> + \<gamma>a" and
    \<delta>: "\<delta> = \<eta> + \<delta>a" and
    hd_\<gamma>a_lt_\<delta>a: "head_\<omega> \<gamma>a < head_\<omega> \<delta>a"
    using hmset_pair_decompose_less[OF \<gamma>_lt_\<delta>] by blast

  have "\<alpha>2 + \<beta>0 * \<gamma> + \<beta>2a * \<gamma> = \<alpha>2 + \<beta>2 * \<gamma>"
    unfolding \<beta>2 by (simp add: add.commute add.left_commute distrib_left mult.commute)
  also have "\<dots> < \<alpha>1 + \<beta>1 * \<gamma>"
    by (rule \<alpha>\<beta>2\<gamma>_lt_\<alpha>\<beta>1\<gamma>)
  also have "\<dots> = \<alpha>1 + \<beta>0 * \<gamma> + \<beta>1a * \<gamma>"
    unfolding \<beta>1 by (simp add: add.commute add.left_commute distrib_left mult.commute)
  finally have *: "\<alpha>2 + \<beta>2a * \<gamma> < \<alpha>1 + \<beta>1a * \<gamma>"
    by (metis add_less_cancel_right semiring_normalization_rules(23))

  have "\<alpha>2 + \<beta>2 * \<delta> = \<alpha>2 + \<beta>0 * \<delta> + \<beta>2a * \<delta>"
    unfolding \<beta>2 by (simp add: ab_semigroup_add_class.add_ac(1) distrib_right)
  also have "\<dots> = \<alpha>2 + \<beta>0 * \<delta> + \<beta>2a * \<eta> + \<beta>2a * \<delta>a"
    unfolding \<delta> by (simp add: distrib_left semiring_normalization_rules(25))
  also have "\<dots> \<le> \<alpha>2 + \<beta>0 * \<delta> + \<beta>2a * \<eta> + \<beta>2a * \<delta>a + \<beta>2a * \<gamma>a"
    by simp
  also have "\<dots> = \<alpha>2 + \<beta>2a * \<gamma> + \<beta>0 * \<delta> + \<beta>2a * \<delta>a"
    unfolding \<gamma> distrib_left add.assoc[symmetric] by (simp add: semiring_normalization_rules(23))
  also have "\<dots> < \<alpha>1 + \<beta>1a * \<gamma> + \<beta>0 * \<delta> + \<beta>2a * \<delta>a"
    using * by simp
  also have "\<dots> = \<alpha>1 + \<beta>1a * \<eta> + \<beta>1a * \<gamma>a + \<beta>0 * \<eta> + \<beta>0 * \<delta>a + \<beta>2a * \<delta>a"
    unfolding \<gamma> \<delta> distrib_left add.assoc[symmetric] by (rule refl)
  also have "\<dots> \<le> \<alpha>1 + \<beta>1a * \<eta> + \<beta>0 * \<eta> + \<beta>0 * \<delta>a + \<beta>1a * \<delta>a"
  proof -
    have "\<beta>1a * \<gamma>a + \<beta>2a * \<delta>a \<le> \<beta>1a * \<delta>a"
    proof (cases "\<beta>2a = 0 \<and> \<beta>1a = 0")
      case False
      hence "head_\<omega> \<beta>2a < head_\<omega> \<beta>1a"
        using hd_\<beta>2a_vs_\<beta>1a by blast
      hence "head_\<omega> (\<beta>1a * \<gamma>a + \<beta>2a * \<delta>a) < head_\<omega> (\<beta>1a * \<delta>a)"
        using hd_\<gamma>a_lt_\<delta>a by (auto intro: gr_zeroI_hmset simp: sup_hmultiset_def)
      hence "\<beta>1a * \<gamma>a + \<beta>2a * \<delta>a < \<beta>1a * \<delta>a"
        by (rule head_\<omega>_lt_imp_lt)
      thus ?thesis
        by simp
    qed simp
    thus ?thesis
      by simp
  qed
  finally show ?thesis
    unfolding \<beta>1 \<delta>
    by (simp add: distrib_left distrib_right add.assoc[symmetric] semiring_normalization_rules(23))
qed

end
