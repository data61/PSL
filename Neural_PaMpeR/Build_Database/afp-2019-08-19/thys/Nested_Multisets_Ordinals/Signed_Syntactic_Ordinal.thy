(*  Title:       Signed Syntactic Ordinals in Cantor Normal Form
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Author:      Mathias Fleury <mfleury at mpi-inf.mpg.de>, 2016
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Signed Syntactic Ordinals in Cantor Normal Form\<close>

theory Signed_Syntactic_Ordinal
imports Signed_Hereditary_Multiset Syntactic_Ordinal
begin


subsection \<open>Natural (Hessenberg) Product\<close>

instantiation zhmultiset :: comm_ring_1
begin

abbreviation \<omega>\<^sub>z_exp :: "hmultiset \<Rightarrow> zhmultiset" ("\<omega>\<^sub>z^") where
  "\<omega>\<^sub>z^ \<equiv> \<lambda>m. ZHMSet {#m#}\<^sub>z"

lift_definition one_zhmultiset :: zhmultiset is "{#0#}\<^sub>z" .

abbreviation \<omega>\<^sub>z :: zhmultiset where
  "\<omega>\<^sub>z \<equiv> \<omega>\<^sub>z^1"

lemma \<omega>\<^sub>z_as_\<omega>: "\<omega>\<^sub>z = zhmset_of \<omega>"
  by simp

lift_definition times_zhmultiset :: "zhmultiset \<Rightarrow> zhmultiset \<Rightarrow> zhmultiset" is
  "\<lambda>M N.
       zmset_of (hmsetmset (HMSet (mset_pos M) * HMSet (mset_pos N)))
     - zmset_of (hmsetmset (HMSet (mset_pos M) * HMSet (mset_neg N)))
     + zmset_of (hmsetmset (HMSet (mset_neg M) * HMSet (mset_neg N)))
     - zmset_of (hmsetmset (HMSet (mset_neg M) * HMSet (mset_pos N)))" .

lemmas zhmsetmset_times = times_zhmultiset.rep_eq

instance
proof (intro_classes, goal_cases mult_assoc mult_comm mult_1 distrib zero_neq_one)
  case (mult_assoc a b c)
  show ?case
    by (transfer,
      simp add: algebra_simps zmset_of_plus[symmetric] hmsetmset_plus[symmetric] HMSet_diff,
      rule triple_cross_mult_hmset)
next
  case (mult_comm a b)
  show ?case
    by transfer (auto simp: algebra_simps)
next
  case (mult_1 a)
  show ?case
    by transfer (auto simp: algebra_simps mset_pos_neg_partition[symmetric])
next
  case (distrib a b c)

  show ?case
    by (simp add: times_zhmultiset_def ZHMSet_plus[symmetric] zmset_of_plus[symmetric]
        hmsetmset_plus[symmetric] algebra_simps hmset_pos_plus hmset_neg_plus)
     (simp add: mult.commute[of _ "hmset_pos c"] mult.commute[of _ "hmset_neg c"]
        add.commute[of "hmset_neg c * M" "hmset_pos c * N" for M N]
        add.assoc[symmetric] ring_distribs(1)[symmetric] hmset_pos_neg_dual)
next
  case zero_neq_one
  show ?case
    unfolding zero_zhmultiset_def one_zhmultiset_def by simp
qed

end

lemma zhmset_of_1: "zhmset_of 1 = 1"
  by (simp add: one_hmultiset_def one_zhmultiset_def)

lemma zhmset_of_times: "zhmset_of (A * B) = zhmset_of A * zhmset_of B"
  by transfer simp

lemma zhmset_of_prod_list:
  "zhmset_of (prod_list Ms) = prod_list (map zhmset_of Ms)"
  by (induct Ms) (auto simp: one_hmultiset_def one_zhmultiset_def zhmset_of_times)


subsection \<open>Embedding of Natural Numbers\<close>

lemma of_nat_zhmset: "of_nat n = zhmset_of (of_nat n)"
  by (induct n) (auto simp: zero_zhmultiset_def zhmset_of_plus zhmset_of_1)

lemma of_nat_inject_zhmset[simp]: "(of_nat m :: zhmultiset) = of_nat n \<longleftrightarrow> m = n"
  unfolding of_nat_zhmset by simp

lemma plus_of_nat_plus_of_nat_zhmset:
  "k + of_nat m + of_nat n = k + of_nat (m + n)" for k :: zhmultiset
  by simp

lemma plus_of_nat_minus_of_nat_zhmset:
  fixes k :: zhmultiset
  assumes "n \<le> m"
  shows "k + of_nat m - of_nat n = k + of_nat (m - n)"
  using assms by (simp add: of_nat_diff)

lemma of_nat_lt_\<omega>\<^sub>z[simp]: "of_nat n < \<omega>\<^sub>z"
  unfolding \<omega>\<^sub>z_as_\<omega> using of_nat_lt_\<omega> of_nat_zhmset zhmset_of_less by presburger

lemma of_nat_ne_\<omega>\<^sub>z[simp]: "of_nat n \<noteq> \<omega>\<^sub>z"
  by (metis of_nat_lt_\<omega>\<^sub>z mset_le_asym mset_lt_single_iff)


subsection \<open>Embedding of Extended Natural Numbers\<close>

primrec zhmset_of_enat :: "enat \<Rightarrow> zhmultiset" where
  "zhmset_of_enat (enat n) = of_nat n"
| "zhmset_of_enat \<infinity> = \<omega>\<^sub>z"

lemma zhmset_of_enat_0[simp]: "zhmset_of_enat 0 = 0"
  by (simp add: zero_enat_def)

lemma zhmset_of_enat_1[simp]: "zhmset_of_enat 1 = 1"
  by (simp add: one_enat_def del: One_nat_def)

lemma zhmset_of_enat_of_nat[simp]: "zhmset_of_enat (of_nat n) = of_nat n"
  using of_nat_eq_enat by auto

lemma zhmset_of_enat_numeral[simp]: "zhmset_of_enat (numeral n) = numeral n"
  by (simp add: numeral_eq_enat)

lemma zhmset_of_enat_le_\<omega>\<^sub>z[simp]: "zhmset_of_enat n \<le> \<omega>\<^sub>z"
  using of_nat_lt_\<omega>\<^sub>z[THEN less_imp_le] by (cases n) auto

lemma zhmset_of_enat_eq_\<omega>\<^sub>z_iff[simp]: "zhmset_of_enat n = \<omega>\<^sub>z \<longleftrightarrow> n = \<infinity>"
  by (cases n) auto


subsection \<open>Inequalities and Some (Dis)equalities\<close>

instance zhmultiset :: zero_less_one
  by (intro_classes, transfer, transfer, auto)

instantiation zhmultiset :: linordered_idom
begin

definition sgn_zhmultiset :: "zhmultiset \<Rightarrow> zhmultiset" where
  "sgn_zhmultiset M = (if M = 0 then 0 else if M > 0 then 1 else -1)"

definition abs_zhmultiset :: "zhmultiset \<Rightarrow> zhmultiset" where
  "abs_zhmultiset M = (if M < 0 then - M else M)"

lemma gt_0_times_gt_0_imp:
  fixes a b :: zhmultiset
  assumes a_gt0: "a > 0" and b_gt0: "b > 0"
  shows "a * b > 0"
proof -
  show ?thesis
    using a_gt0 b_gt0
    by (subst (asm) (2 4) zhmset_pos_neg_partition, simp, transfer,
        simp del: HMSet_less add: algebra_simps zmset_of_plus[symmetric] hmsetmset_plus[symmetric]
        zmset_of_less HMSet_less[symmetric])
      (rule mono_cross_mult_less_hmset)
qed

instance
proof intro_classes
  fix a b c :: zhmultiset

  assume
    a_lt_b: "a < b" and
    zero_lt_c: "0 < c"

  have "c * b < c * b + c * (b - a)"
    using gt_0_times_gt_0_imp by (simp add: a_lt_b zero_lt_c)
  hence "c * a + c * (b - a) < c * b + c * (b - a)"
    by (simp add: right_diff_distrib')
  thus "c * a < c * b"
    by simp
qed (auto simp: sgn_zhmultiset_def abs_zhmultiset_def)

end

lemma le_zhmset_of_pos: "M \<le> zhmset_of (hmset_pos M)"
  by (simp add: less_eq_zhmultiset.rep_eq mset_pos_supset subset_eq_imp_le_zmset)

lemma minus_zhmset_of_pos_le: "- zhmset_of (hmset_neg M) \<le> M"
  by (metis le_zhmset_of_pos minus_le_iff mset_pos_uminus zhmsetmset_uminus)

lemma zhmset_of_nonneg[simp]: "zhmset_of M \<ge> 0"
  by (metis hmsetmset_0 zero_le_hmset zero_zhmultiset_def zhmset_of_le zmset_of_empty)

lemma
  fixes n :: zhmultiset
  assumes "0 \<le> m"
  shows
    le_add1_hmset: "n \<le> n + m" and
    le_add2_hmset: "n \<le> m + n"
  using assms by simp+

lemma less_iff_add1_le_zhmset: "m < n \<longleftrightarrow> m + 1 \<le> n" for m n :: zhmultiset
proof
  assume m_lt_n: "m < n"
  show "m + 1 \<le> n"
  proof -
    obtain hh :: hmultiset and zz :: zhmultiset and hha :: hmultiset where
      f1: "m = zhmset_of hh + zz \<and> n = zhmset_of hha + zz \<and> hh < hha"
      using less_hmset_zhmsetE[OF m_lt_n] by metis
    hence "zhmset_of (hh + 1) \<le> zhmset_of hha"
      by (metis (no_types) less_iff_add1_le_hmset zhmset_of_le)
    thus ?thesis
      using f1 by (simp add: zhmset_of_1 zhmset_of_plus)
  qed
qed simp

lemma gt_0_lt_mult_gt_1_zhmset:
  fixes m n :: zhmultiset
  assumes "m > 0" and "n > 1"
  shows "m < m * n"
  using assms by simp

lemma zero_less_iff_1_le_zhmset: "0 < n \<longleftrightarrow> 1 \<le> n" for n :: zhmultiset
  by (rule less_iff_add1_le_zhmset[of 0, simplified])

lemma less_add_1_iff_le_hmset: "m < n + 1 \<longleftrightarrow> m \<le> n" for m n :: zhmultiset
  by (rule less_iff_add1_le_zhmset[of m "n + 1", simplified])

lemma nonneg_le_mult_right_mono_zhmset:
  fixes x y z :: zhmultiset
  assumes x: "0 \<le> x" and y: "0 < y" and z: "x \<le> z"
  shows "x \<le> y * z"
  using x zero_less_iff_1_le_zhmset[THEN iffD1, OF y] z
  by (meson dual_order.trans leD mult_less_cancel_right2 not_le_imp_less)

instance hmultiset :: ordered_cancel_comm_semiring
  by intro_classes

instance hmultiset :: linordered_semiring_1_strict
  by intro_classes

instance hmultiset :: bounded_lattice_bot
  by intro_classes

instance hmultiset :: zero_less_one
  by intro_classes

instance hmultiset :: linordered_nonzero_semiring
  by intro_classes

instance hmultiset :: semiring_no_zero_divisors
  by intro_classes

lemma zero_lt_\<omega>\<^sub>z[simp]: "0 < \<omega>\<^sub>z"
  by (metis of_nat_lt_\<omega>\<^sub>z of_nat_0)

lemma one_lt_\<omega>[simp]: "1 < \<omega>\<^sub>z"
  by (metis enat_defs(2) zhmset_of_enat.simps(1) zhmset_of_enat_1 of_nat_lt_\<omega>\<^sub>z)

lemma numeral_lt_\<omega>\<^sub>z[simp]: "numeral n < \<omega>\<^sub>z"
  using zhmset_of_enat_numeral[symmetric] zhmset_of_enat.simps(1) of_nat_lt_\<omega>\<^sub>z numeral_eq_enat
  by presburger

lemma one_le_\<omega>\<^sub>z[simp]: "1 \<le> \<omega>\<^sub>z"
  by (simp add: less_imp_le)

lemma of_nat_le_\<omega>\<^sub>z[simp]: "of_nat n \<le> \<omega>\<^sub>z"
  by (simp add: le_less)

lemma numeral_le_\<omega>\<^sub>z[simp]: "numeral n \<le> \<omega>\<^sub>z"
  by (simp add: less_imp_le)

lemma not_\<omega>\<^sub>z_lt_1[simp]: "\<not> \<omega>\<^sub>z < 1"
  by (simp add: not_less)

lemma not_\<omega>\<^sub>z_lt_of_nat[simp]: "\<not> \<omega>\<^sub>z < of_nat n"
  by (simp add: not_less)

lemma not_\<omega>\<^sub>z_lt_numeral[simp]: "\<not> \<omega>\<^sub>z < numeral n"
  by (simp add: not_less)

lemma not_\<omega>\<^sub>z_le_1[simp]: "\<not> \<omega>\<^sub>z \<le> 1"
  by (simp add: not_le)

lemma not_\<omega>\<^sub>z_le_of_nat[simp]: "\<not> \<omega>\<^sub>z \<le> of_nat n"
  by (simp add: not_le)

lemma not_\<omega>\<^sub>z_le_numeral[simp]: "\<not> \<omega>\<^sub>z \<le> numeral n"
  by (simp add: not_le)

lemma zero_ne_\<omega>\<^sub>z[simp]: "0 \<noteq> \<omega>\<^sub>z"
  using zero_lt_\<omega>\<^sub>z by linarith

lemma one_ne_\<omega>\<^sub>z[simp]: "1 \<noteq> \<omega>\<^sub>z"
  using not_\<omega>\<^sub>z_le_1 by force

lemma numeral_ne_\<omega>\<^sub>z[simp]: "numeral n \<noteq> \<omega>\<^sub>z"
  by (metis not_\<omega>\<^sub>z_le_numeral numeral_le_\<omega>\<^sub>z)

lemma
  \<omega>\<^sub>z_ne_0[simp]: "\<omega>\<^sub>z \<noteq> 0" and
  \<omega>\<^sub>z_ne_1[simp]: "\<omega>\<^sub>z \<noteq> 1" and
  \<omega>\<^sub>z_ne_of_nat[simp]: "\<omega>\<^sub>z \<noteq> of_nat m" and
  \<omega>\<^sub>z_ne_numeral[simp]: "\<omega>\<^sub>z \<noteq> numeral n"
  using zero_ne_\<omega>\<^sub>z one_ne_\<omega>\<^sub>z of_nat_ne_\<omega>\<^sub>z numeral_ne_\<omega>\<^sub>z by metis+

lemma
  zhmset_of_enat_inject[simp]: "zhmset_of_enat m = zhmset_of_enat n \<longleftrightarrow> m = n" and
  zhmset_of_enat_lt_iff_lt[simp]: "zhmset_of_enat m < zhmset_of_enat n \<longleftrightarrow> m < n" and
  zhmset_of_enat_le_iff_le[simp]: "zhmset_of_enat m \<le> zhmset_of_enat n \<longleftrightarrow> m \<le> n"
  by (cases m; cases n; simp)+

lemma of_nat_lt_zhmset_of_enat_iff: "of_nat m < zhmset_of_enat n \<longleftrightarrow> enat m < n"
  by (metis zhmset_of_enat.simps(1) zhmset_of_enat_lt_iff_lt)

lemma of_nat_le_zhmset_of_enat_iff: "of_nat m \<le> zhmset_of_enat n \<longleftrightarrow> enat m \<le> n"
  by (metis zhmset_of_enat.simps(1) zhmset_of_enat_le_iff_le)

lemma zhmset_of_enat_lt_iff_ne_infinity: "zhmset_of_enat x < \<omega>\<^sub>z \<longleftrightarrow> x \<noteq> \<infinity>"
  by (cases x; simp)


subsection \<open>An Example\<close>

text \<open>
A new proof of @{thm ludwig_waldmann_less}:
\<close>

lemma
  fixes \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<gamma> \<delta> :: hmultiset
  assumes
    \<alpha>\<beta>2\<gamma>_lt_\<alpha>\<beta>1\<gamma>: "\<alpha>2 + \<beta>2 * \<gamma> < \<alpha>1 + \<beta>1 * \<gamma>" and
    \<beta>2_le_\<beta>1: "\<beta>2 \<le> \<beta>1" and
    \<gamma>_lt_\<delta>: "\<gamma> < \<delta>"
  shows "\<alpha>2 + \<beta>2 * \<delta> < \<alpha>1 + \<beta>1 * \<delta>"
proof -
  let ?z = zhmset_of

  note \<alpha>\<beta>2\<gamma>_lt_\<alpha>\<beta>1\<gamma>' = \<alpha>\<beta>2\<gamma>_lt_\<alpha>\<beta>1\<gamma>[THEN zhmset_of_less[THEN iffD2],
    simplified zhmset_of_plus zhmset_of_times]
  note \<beta>2_le_\<beta>1' = \<beta>2_le_\<beta>1[THEN zhmset_of_le[THEN iffD2]]
  note \<gamma>_lt_\<delta>' = \<gamma>_lt_\<delta>[THEN zhmset_of_less[THEN iffD2]]

  have "?z \<alpha>2 + ?z \<beta>2 * ?z \<delta> < ?z \<alpha>1 + ?z \<beta>1 * ?z \<gamma> + ?z \<beta>2 * (?z \<delta> - ?z \<gamma>)"
    using \<alpha>\<beta>2\<gamma>_lt_\<alpha>\<beta>1\<gamma>' by (simp add: algebra_simps)
  also have "\<dots> \<le> ?z \<alpha>1 + ?z \<beta>1 * ?z \<gamma> + ?z \<beta>1 * (?z \<delta> - ?z \<gamma>)"
    using \<beta>2_le_\<beta>1' \<gamma>_lt_\<delta>' by simp
  finally show ?thesis
    by (simp add: zmset_of_less zhmset_of_times[symmetric] zhmset_of_plus[symmetric] algebra_simps)
qed

end
