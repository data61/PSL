(*  Title:       Utilities for Lambda-Free Orders
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Utilities for Lambda-Free Orders\<close>

theory Lambda_Free_Util
imports "HOL-Library.Extended_Nat" "HOL-Library.Multiset_Order"
begin

text \<open>
This theory gathers various lemmas that likely belong elsewhere in Isabelle or
the \emph{Archive of Formal Proofs}. Most (but certainly not all) of them are
used to formalize orders on \<open>\<lambda>\<close>-free higher-order terms.
\<close>

hide_const (open) Complex.arg


subsection \<open>Finite Sets\<close>

lemma finite_set_fold_singleton[simp]: "Finite_Set.fold f z {x} = f x z"
proof -
  have "fold_graph f z {x} (f x z)"
    by (auto intro: fold_graph.intros)
  moreover
  {
    fix X y
    have "fold_graph f z X y \<Longrightarrow> (X = {} \<longrightarrow> y = z) \<and> (X = {x} \<longrightarrow> y = f x z)"
      by (induct rule: fold_graph.induct) auto
  }
  ultimately have "(THE y. fold_graph f z {x} y) = f x z"
    by blast
  thus ?thesis
    by (simp add: Finite_Set.fold_def)
qed


subsection \<open>Function Power\<close>

lemma funpow_lesseq_iter:
  fixes f :: "('a::order) \<Rightarrow> 'a"
  assumes mono: "\<And>k. k \<le> f k" and m_le_n: "m \<le> n"
  shows "(f ^^ m) k \<le> (f ^^ n) k"
  using m_le_n by (induct n) (fastforce simp: le_Suc_eq intro: mono order_trans)+

lemma funpow_less_iter:
  fixes f :: "('a::order) \<Rightarrow> 'a"
  assumes mono: "\<And>k. k < f k" and m_lt_n: "m < n"
  shows "(f ^^ m) k < (f ^^ n) k"
  using m_lt_n by (induct n) (auto, blast intro: mono less_trans dest: less_antisym)


subsection \<open>Least Operator\<close>

lemma Least_eq[simp]: "(LEAST y. y = x) = x" and "(LEAST y. x = y) = x" for x :: "'a::order"
  by (blast intro: Least_equality)+

lemma Least_in_nonempty_set_imp_ex:
  fixes f :: "'b \<Rightarrow> ('a::wellorder)"
  assumes
    A_nemp: "A \<noteq> {}" and
    P_least: "P (LEAST y. \<exists>x \<in> A. y = f x)"
  shows "\<exists>x \<in> A. P (f x)"
proof -
  obtain a where a: "a \<in> A"
    using A_nemp by fast
  have "\<exists>x. x \<in> A \<and> (LEAST y. \<exists>x. x \<in> A \<and> y = f x) = f x"
    by (rule LeastI[of _ "f a"]) (fast intro: a)
  thus ?thesis
    by (metis P_least)
qed

lemma Least_eq_0_enat: "P 0 \<Longrightarrow> (LEAST x :: enat. P x) = 0"
  by (simp add: Least_equality)


subsection \<open>Antisymmetric Relations\<close>

lemma irrefl_trans_imp_antisym: "irrefl r \<Longrightarrow> trans r \<Longrightarrow> antisym r"
  unfolding irrefl_def trans_def antisym_def by fast

lemma irreflp_transp_imp_antisymP: "irreflp p \<Longrightarrow> transp p \<Longrightarrow> antisymp p"
  by (fact irrefl_trans_imp_antisym [to_pred])


subsection \<open>Acyclic Relations\<close>

lemma finite_nonempty_ex_succ_imp_cyclic:
  assumes
    fin: "finite A" and
    nemp: "A \<noteq> {}" and
    ex_y: "\<forall>x \<in> A. \<exists>y \<in> A. (y, x) \<in> r"
  shows "\<not> acyclic r"
proof -
  let ?R = "{(x, y). x \<in> A \<and> y \<in> A \<and> (x, y) \<in> r}"

  have R_sub_r: "?R \<subseteq> r"
    by auto

  have "?R \<subseteq> A \<times> A"
    by auto
  hence fin_R: "finite ?R"
    by (auto intro: fin dest!: infinite_super)

  have "\<not> acyclic ?R"
    by (rule notI, drule finite_acyclic_wf[OF fin_R], unfold wf_eq_minimal, drule spec[of _ A],
      use ex_y nemp in blast)
  thus ?thesis
    using R_sub_r acyclic_subset by auto
qed


subsection \<open>Reflexive, Transitive Closure\<close>

lemma relcomp_subset_left_imp_relcomp_trancl_subset_left:
  assumes sub: "R O S \<subseteq> R"
  shows "R O S\<^sup>* \<subseteq> R"
proof
  fix x
  assume "x \<in> R O S\<^sup>*"
  then obtain n where "x \<in> R O S ^^ n"
    using rtrancl_imp_relpow by fastforce
  thus "x \<in> R"
  proof (induct n)
    case (Suc m)
    thus ?case
      by (metis (no_types) O_assoc inf_sup_ord(3) le_iff_sup relcomp_distrib2 relpow.simps(2)
        relpow_commute sub subsetCE)
  qed auto
qed

lemma f_chain_in_rtrancl:
  assumes m_le_n: "m \<le> n" and f_chain: "\<forall>i \<in> {m..<n}. (f i, f (Suc i)) \<in> R"
  shows "(f m, f n) \<in> R\<^sup>*"
proof (rule relpow_imp_rtrancl, rule relpow_fun_conv[THEN iffD2], intro exI conjI)
  let ?g = "\<lambda>i. f (m + i)"
  let ?k = "n - m"

  show "?g 0 = f m"
    by simp
  show "?g ?k = f n"
    using m_le_n by force
  show "(\<forall>i < ?k. (?g i, ?g (Suc i)) \<in> R)"
    by (simp add: f_chain)
qed

lemma f_rev_chain_in_rtrancl:
  assumes m_le_n: "m \<le> n" and f_chain: "\<forall>i \<in> {m..<n}. (f (Suc i), f i) \<in> R"
  shows "(f n, f m) \<in> R\<^sup>*"
  by (rule f_chain_in_rtrancl[OF m_le_n, of "\<lambda>i. f (n + m - i)", simplified])
    (metis f_chain le_add_diff Suc_diff_Suc Suc_leI atLeastLessThan_iff diff_Suc_diff_eq1 diff_less
      le_add1 less_le_trans zero_less_Suc)


subsection \<open>Well-Founded Relations\<close>

lemma wf_app: "wf r \<Longrightarrow> wf {(x, y). (f x, f y) \<in> r}"
  unfolding wf_eq_minimal by (intro allI, drule spec[of _ "f ` Q" for Q]) fast

lemma wfP_app: "wfP p \<Longrightarrow> wfP (\<lambda>x y. p (f x) (f y))"
  unfolding wfP_def by (rule wf_app[of "{(x, y). p x y}" f, simplified])

lemma wf_exists_minimal:
  assumes wf: "wf r" and Q: "Q x"
  shows "\<exists>x. Q x \<and> (\<forall>y. (f y, f x) \<in> r \<longrightarrow> \<not> Q y)"
  using wf_eq_minimal[THEN iffD1, OF wf_app[OF wf], rule_format, of _ "{x. Q x}", simplified, OF Q]
  by blast

lemma wfP_exists_minimal:
  assumes wf: "wfP p" and Q: "Q x"
  shows "\<exists>x. Q x \<and> (\<forall>y. p (f y) (f x) \<longrightarrow> \<not> Q y)"
  by (rule wf_exists_minimal[of "{(x, y). p x y}" Q x, OF wf[unfolded wfP_def] Q, simplified])

lemma finite_irrefl_trans_imp_wf: "finite r \<Longrightarrow> irrefl r \<Longrightarrow> trans r \<Longrightarrow> wf r"
  by (erule finite_acyclic_wf) (simp add: acyclic_irrefl)

lemma finite_irreflp_transp_imp_wfp:
  "finite {(x, y). p x y} \<Longrightarrow> irreflp p \<Longrightarrow> transp p \<Longrightarrow> wfP p"
  using finite_irrefl_trans_imp_wf[of "{(x, y). p x y}"]
  unfolding wfP_def transp_def irreflp_def trans_def irrefl_def mem_Collect_eq prod.case
  by assumption

lemma wf_infinite_down_chain_compatible:
  assumes
    wf_R: "wf R" and
    inf_chain_RS: "\<forall>i. (f (Suc i), f i) \<in> R \<union> S" and
    O_subset: "R O S \<subseteq> R"
  shows "\<exists>k. \<forall>i. (f (Suc (i + k)), f (i + k)) \<in> S"
proof (rule ccontr)
  assume "\<nexists>k. \<forall>i. (f (Suc (i + k)), f (i + k)) \<in> S"
  hence "\<forall>k. \<exists>i. (f (Suc (i + k)), f (i + k)) \<notin> S"
    by blast
  hence "\<forall>k. \<exists>i > k. (f (Suc i), f i) \<notin> S"
    by (metis add.commute add_Suc less_add_Suc1)
  hence "\<forall>k. \<exists>i > k. (f (Suc i), f i) \<in> R"
    using inf_chain_RS by blast
  hence "\<exists>i > k. (f (Suc i), f i) \<in> R \<and> (\<forall>j > k. (f (Suc j), f j) \<in> R \<longrightarrow> j \<ge> i)" for k
    using wf_eq_minimal[THEN iffD1, OF wf_less, rule_format,
      of _ "{i. i > k \<and> (f (Suc i), f i) \<in> R}", simplified]
    by (meson not_less)
  then obtain j_of where
    j_of_gt: "\<And>k. j_of k > k" and
    j_of_in_R: "\<And>k. (f (Suc (j_of k)), f (j_of k)) \<in> R" and
    j_of_min: "\<And>k. \<forall>j > k. (f (Suc j), f j) \<in> R \<longrightarrow> j \<ge> j_of k"
    by moura

  have j_of_min_s: "\<And>k j. j > k \<Longrightarrow> j < j_of k \<Longrightarrow> (f (Suc j), f j) \<in> S"
    using j_of_min inf_chain_RS by fastforce

  define g :: "nat \<Rightarrow> 'a" where "\<And>k. g k = f (Suc ((j_of ^^ k) 0))"

  have between_g[simplified]: "(f ((j_of ^^ (Suc i)) 0), f (Suc ((j_of ^^ i) 0))) \<in> S\<^sup>*" for i
  proof (rule f_rev_chain_in_rtrancl; clarify?)
    show "Suc ((j_of ^^ i) 0) \<le> (j_of ^^ Suc i) 0"
      using j_of_gt by (simp add: Suc_leI)
  next
    fix ia
    assume ia: "ia \<in> {Suc ((j_of ^^ i) 0)..<(j_of ^^ Suc i) 0}"
    have ia_gt: "ia > (j_of ^^ i) 0"
      using ia by auto
    have ia_lt: "ia < j_of ((j_of ^^ i) 0)"
      using ia by auto
    show "(f (Suc ia), f ia) \<in> S"
      by (rule j_of_min_s[OF ia_gt ia_lt])
  qed

  have "\<And>i. (g (Suc i), g i) \<in> R"
    unfolding g_def funpow.simps comp_def
    by (rule subsetD[OF relcomp_subset_left_imp_relcomp_trancl_subset_left[OF O_subset]])
      (rule relcompI[OF j_of_in_R between_g])
  moreover have "\<forall>f. \<exists>i. (f (Suc i), f i) \<notin> R"
    using wf_R[unfolded wf_iff_no_infinite_down_chain] by blast
  ultimately show False
    by blast
qed


subsection \<open>Wellorders\<close>

lemma (in wellorder) exists_minimal:
  fixes x :: 'a
  assumes "P x"
  shows "\<exists>x. P x \<and> (\<forall>y. P y \<longrightarrow> y \<ge> x)"
  using assms by (auto intro: LeastI Least_le)


subsection \<open>Lists\<close>

lemma rev_induct2[consumes 1, case_names Nil snoc]:
  "length xs = length ys \<Longrightarrow> P [] [] \<Longrightarrow>
   (\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs @ [x]) (ys @ [y])) \<Longrightarrow> P xs ys"
proof (induct xs arbitrary: ys rule: rev_induct)
  case (snoc x xs ys)
  thus ?case
    by (induct ys rule: rev_induct) simp_all
qed auto

lemma hd_in_set: "length xs \<noteq> 0 \<Longrightarrow> hd xs \<in> set xs"
  by (cases xs) auto

lemma in_lists_iff_set: "xs \<in> lists A \<longleftrightarrow> set xs \<subseteq> A"
  by fast

lemma butlast_append_Cons[simp]: "butlast (xs @ y # ys) = xs @ butlast (y # ys)"
  using butlast_append[of xs "y # ys", simplified] by simp

lemma rev_in_lists[simp]: "rev xs \<in> lists A \<longleftrightarrow> xs \<in> lists A"
  by auto

lemma hd_le_sum_list:
  fixes xs :: "'a::ordered_ab_semigroup_monoid_add_imp_le list"
  assumes "xs \<noteq> []" and "\<forall>i < length xs. xs ! i \<ge> 0"
  shows "hd xs \<le> sum_list xs"
  using assms
  by (induct xs rule: rev_induct, simp_all,
    metis add_cancel_right_left add_increasing2 hd_append2 lessI less_SucI list.sel(1) nth_append
      nth_append_length order_refl self_append_conv2 sum_list.Nil)

lemma sum_list_ge_length_times:
  fixes a :: "'a::{ordered_ab_semigroup_add,semiring_1}"
  assumes "\<forall>i < length xs. xs ! i \<ge> a"
  shows "sum_list xs \<ge> of_nat (length xs) * a"
  using assms
proof (induct xs)
  case (Cons x xs)
  note ih = this(1) and xxs_i_ge_a = this(2)

  have xs_i_ge_a: "\<forall>i < length xs. xs ! i \<ge> a"
    using xxs_i_ge_a by auto

  have "x \<ge> a"
    using xxs_i_ge_a by auto
  thus ?case
    using ih[OF xs_i_ge_a] by (simp add: ring_distribs ordered_ab_semigroup_add_class.add_mono)
qed auto

lemma prod_list_nonneg:
  fixes xs :: "('a :: {ordered_semiring_0,linordered_nonzero_semiring}) list"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x \<ge> 0"
  shows "prod_list xs \<ge> 0"
  using assms by (induct xs) auto

lemma zip_append_0_upt:
  "zip (xs @ ys) [0..<length xs + length ys] =
   zip xs [0..<length xs] @ zip ys [length xs..<length xs + length ys]"
proof (induct ys arbitrary: xs)
  case (Cons y ys)
  note ih = this
  show ?case
    using ih[of "xs @ [y]"] by (simp, cases ys, simp, simp add: upt_rec)
qed auto

lemma zip_eq_butlast_last:
  assumes len_gt0: "length xs > 0" and len_eq: "length xs = length ys"
  shows "zip xs ys = zip (butlast xs) (butlast ys) @ [(last xs, last ys)]"
  using len_eq len_gt0 by (induct rule: list_induct2) auto


subsection \<open>Extended Natural Numbers\<close>

lemma the_enat_0[simp]: "the_enat 0 = 0"
  by (simp add: zero_enat_def)

lemma the_enat_1[simp]: "the_enat 1 = 1"
  by (simp add: one_enat_def)

lemma enat_le_minus_1_imp_lt: "m \<le> n - 1 \<Longrightarrow> n \<noteq> \<infinity> \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> m < n" for m n :: enat
  by (cases m; cases n; simp add: zero_enat_def one_enat_def)

lemma enat_diff_diff_eq: "k - m - n = k - (m + n)" for k m n :: enat
  by (cases k; cases m; cases n) auto

lemma enat_sub_add_same[intro]: "n \<le> m \<Longrightarrow> m = m - n + n" for m n :: enat
  by (cases m; cases n) auto

lemma enat_the_enat_iden[simp]: "n \<noteq> \<infinity> \<Longrightarrow> enat (the_enat n) = n"
  by auto

lemma the_enat_minus_nat: "m \<noteq> \<infinity> \<Longrightarrow> the_enat (m - enat n) = the_enat m - n"
  by auto

lemma enat_the_enat_le: "enat (the_enat x) \<le> x"
  by (cases x; simp)

lemma enat_the_enat_minus_le: "enat (the_enat (x - y)) \<le> x"
  by (cases x; cases y; simp)

lemma enat_le_imp_minus_le: "k \<le> m \<Longrightarrow> k - n \<le> m" for k m n :: enat
  by (metis Groups.add_ac(2) enat_diff_diff_eq enat_ord_simps(3) enat_sub_add_same
    enat_the_enat_iden enat_the_enat_minus_le idiff_0_right idiff_infinity idiff_infinity_right
    order_trans_rules(23) plus_enat_simps(3))

lemma add_diff_assoc2_enat: "m \<ge> n \<Longrightarrow> m - n + p = m + p - n" for m n p :: enat
  by (cases m; cases n; cases p; auto)

lemma enat_mult_minus_distrib: "enat x * (y - z) = enat x * y - enat x * z"
  by (cases y; cases z; auto simp: enat_0 right_diff_distrib')


subsection \<open>Multisets\<close>

lemma add_mset_lt_left_lt: "a < b \<Longrightarrow> add_mset a A < add_mset b A"
  unfolding less_multiset\<^sub>H\<^sub>O by auto

lemma add_mset_le_left_le: "a \<le> b \<Longrightarrow> add_mset a A \<le> add_mset b A" for a :: "'a :: linorder"
  unfolding less_multiset\<^sub>H\<^sub>O by auto

lemma add_mset_lt_right_lt: "A < B \<Longrightarrow> add_mset a A < add_mset a B"
  unfolding less_multiset\<^sub>H\<^sub>O by auto

lemma add_mset_le_right_le: "A \<le> B \<Longrightarrow> add_mset a A \<le> add_mset a B"
  unfolding less_multiset\<^sub>H\<^sub>O by auto

lemma add_mset_lt_lt_lt:
  assumes a_lt_b: "a < b" and A_le_B: "A < B"
  shows "add_mset a A < add_mset b B"
  by (rule less_trans[OF add_mset_lt_left_lt[OF a_lt_b] add_mset_lt_right_lt[OF A_le_B]])

lemma add_mset_lt_lt_le: "a < b \<Longrightarrow> A \<le> B \<Longrightarrow> add_mset a A < add_mset b B"
  using add_mset_lt_lt_lt le_neq_trans by fastforce

lemma add_mset_lt_le_lt: "a \<le> b \<Longrightarrow> A < B \<Longrightarrow> add_mset a A < add_mset b B" for a :: "'a :: linorder"
  using add_mset_lt_lt_lt by (metis add_mset_lt_right_lt le_less)

lemma add_mset_le_le_le:
  fixes a :: "'a :: linorder"
  assumes a_le_b: "a \<le> b" and A_le_B: "A \<le> B"
  shows "add_mset a A \<le> add_mset b B"
  by (rule order.trans[OF add_mset_le_left_le[OF a_le_b] add_mset_le_right_le[OF A_le_B]])

declare filter_eq_replicate_mset [simp] image_mset_subseteq_mono [intro]

lemma nonempty_subseteq_mset_eq_singleton: "M \<noteq> {#} \<Longrightarrow> M \<subseteq># {#x#} \<Longrightarrow> M = {#x#}"
  by (cases M) (auto dest: subset_mset.diff_add)

lemma nonempty_subseteq_mset_iff_singleton: "(M \<noteq> {#} \<and> M \<subseteq># {#x#} \<and> P) \<longleftrightarrow> M = {#x#} \<and> P"
  by (cases M) (auto dest: subset_mset.diff_add)

lemma count_gt_imp_in_mset[intro]: "count M x > n \<Longrightarrow> x \<in># M"
  using count_greater_zero_iff by fastforce

lemma size_lt_imp_ex_count_lt: "size M < size N \<Longrightarrow> \<exists>x \<in># N. count M x < count N x"
  by (metis count_eq_zero_iff leD not_le_imp_less not_less_zero size_mset_mono subseteq_mset_def)

lemma filter_filter_mset[simp]: "{#x \<in># {#x \<in># M. Q x#}. P x#} = {#x \<in># M. P x \<and> Q x#}"
  by (induct M) auto

lemma size_filter_unsat_elem:
  assumes "x \<in># M" and "\<not> P x"
  shows "size {#x \<in># M. P x#} < size M"
proof -
  have "size (filter_mset P M) \<noteq> size M"
    using assms by (metis add.right_neutral add_diff_cancel_left' count_filter_mset mem_Collect_eq
      multiset_partition nonempty_has_size set_mset_def size_union)
  then show ?thesis
    by (meson leD nat_neq_iff size_filter_mset_lesseq)
qed

lemma size_filter_ne_elem: "x \<in># M \<Longrightarrow> size {#y \<in># M. y \<noteq> x#} < size M"
  by (simp add: size_filter_unsat_elem[of x M "\<lambda>y. y \<noteq> x"])

lemma size_eq_ex_count_lt:
  assumes
    sz_m_eq_n: "size M = size N" and
    m_eq_n: "M \<noteq> N"
  shows "\<exists>x. count M x < count N x"
proof -
  obtain x where "count M x \<noteq> count N x"
    using m_eq_n by (meson multiset_eqI)
  moreover
  {
    assume "count M x < count N x"
    hence ?thesis
      by blast
  }
  moreover
  {
    assume cnt_x: "count M x > count N x"

    have "size {#y \<in># M. y = x#} + size {#y \<in># M. y \<noteq> x#} =
      size {#y \<in># N. y = x#} + size {#y \<in># N. y \<noteq> x#}"
      using sz_m_eq_n multiset_partition by (metis size_union)
    hence sz_m_minus_x: "size {#y \<in># M. y \<noteq> x#} < size {#y \<in># N. y \<noteq> x#}"
      using cnt_x by simp
    then obtain y where "count {#y \<in># M. y \<noteq> x#} y < count {#y \<in># N. y \<noteq> x#} y"
      using size_lt_imp_ex_count_lt[OF sz_m_minus_x] by blast
    hence "count M y < count N y"
      by (metis count_filter_mset less_asym)
    hence ?thesis
      by blast
  }
  ultimately show ?thesis
    by fastforce
qed

lemma count_image_mset_lt_imp_lt_raw:
  assumes
    "finite A" and
    "A = set_mset M \<union> set_mset N" and
    "count (image_mset f M) b < count (image_mset f N) b"
  shows "\<exists>x. f x = b \<and> count M x < count N x"
  using assms
proof (induct A arbitrary: M N b rule: finite_induct)
  case (insert x F)
  note fin = this(1) and x_ni_f = this(2) and ih = this(3) and x_f_eq_m_n = this(4) and
    cnt_b = this(5)

  let ?Ma = "{#y \<in># M. y \<noteq> x#}"
  let ?Mb = "{#y \<in># M. y = x#}"
  let ?Na = "{#y \<in># N. y \<noteq> x#}"
  let ?Nb = "{#y \<in># N. y = x#}"

  have m_part: "M = ?Mb + ?Ma" and n_part: "N = ?Nb + ?Na"
    using multiset_partition by blast+

  have f_eq_ma_na: "F = set_mset ?Ma \<union> set_mset ?Na"
    using x_f_eq_m_n x_ni_f by auto

  show ?case
  proof (cases "count (image_mset f ?Ma) b < count (image_mset f ?Na) b")
    case cnt_ba: True
    obtain xa where "f xa = b" and "count ?Ma xa < count ?Na xa"
      using ih[OF f_eq_ma_na cnt_ba] by blast
    thus ?thesis
      by (metis count_filter_mset not_less0)
  next
    case cnt_ba: False
    have fx_eq_b: "f x = b"
      using cnt_b cnt_ba by (subst (asm) m_part, subst (asm) n_part, auto, presburger)
    moreover have "count M x < count N x"
      using cnt_b cnt_ba by (subst (asm) m_part, subst (asm) n_part, auto simp: fx_eq_b)
    ultimately show ?thesis
      by blast
  qed
qed auto

lemma count_image_mset_lt_imp_lt:
  assumes cnt_b: "count (image_mset f M) b < count (image_mset f N) b"
  shows "\<exists>x. f x = b \<and> count M x < count N x"
  by (rule count_image_mset_lt_imp_lt_raw[of "set_mset M \<union> set_mset N", OF _ refl cnt_b]) auto

lemma count_image_mset_le_imp_lt_raw:
  assumes
    "finite A" and
    "A = set_mset M \<union> set_mset N" and
    "count (image_mset f M) (f a) + count N a < count (image_mset f N) (f a) + count M a"
  shows "\<exists>b. f b = f a \<and> count M b < count N b"
  using assms
proof (induct A arbitrary: M N rule: finite_induct)
  case (insert x F)
  note fin = this(1) and x_ni_f = this(2) and ih = this(3) and x_f_eq_m_n = this(4) and
    cnt_lt = this(5)

  let ?Ma = "{#y \<in># M. y \<noteq> x#}"
  let ?Mb = "{#y \<in># M. y = x#}"
  let ?Na = "{#y \<in># N. y \<noteq> x#}"
  let ?Nb = "{#y \<in># N. y = x#}"

  have m_part: "M = ?Mb + ?Ma" and n_part: "N = ?Nb + ?Na"
    using multiset_partition by blast+

  have f_eq_ma_na: "F = set_mset ?Ma \<union> set_mset ?Na"
    using x_f_eq_m_n x_ni_f by auto

  show ?case
  proof (cases "f x = f a")
    case fx_ne_fa: False

    have cnt_fma_fa: "count (image_mset f ?Ma) (f a) = count (image_mset f M) (f a)"
      using fx_ne_fa by (subst (2) m_part) auto
    have cnt_fna_fa: "count (image_mset f ?Na) (f a) = count (image_mset f N) (f a)"
      using fx_ne_fa by (subst (2) n_part) auto
    have cnt_ma_a: "count ?Ma a = count M a"
      using fx_ne_fa by (subst (2) m_part) auto
    have cnt_na_a: "count ?Na a = count N a"
      using fx_ne_fa by (subst (2) n_part) auto

    obtain b where fb_eq_fa: "f b = f a" and cnt_b: "count ?Ma b < count ?Na b"
      using ih[OF f_eq_ma_na] cnt_lt unfolding cnt_fma_fa cnt_fna_fa cnt_ma_a cnt_na_a by blast
    have fx_ne_fb: "f x \<noteq> f b"
      using fb_eq_fa fx_ne_fa by simp

    have cnt_ma_b: "count ?Ma b = count M b"
      using fx_ne_fb by (subst (2) m_part) auto
    have cnt_na_b: "count ?Na b = count N b"
      using fx_ne_fb by (subst (2) n_part) auto

    show ?thesis
      using fb_eq_fa cnt_b unfolding cnt_ma_b cnt_na_b by blast
  next
    case fx_eq_fa: True
    show ?thesis
    proof (cases "x = a")
      case x_eq_a: True
      have "count (image_mset f ?Ma) (f a) + count ?Na a
        < count (image_mset f ?Na) (f a) + count ?Ma a"
        using cnt_lt x_eq_a by (subst (asm) (1 2) m_part, subst (asm) (1 2) n_part, auto)
      thus ?thesis
        using ih[OF f_eq_ma_na] by (metis count_filter_mset nat_neq_iff)
    next
      case x_ne_a: False
      show ?thesis
      proof (cases "count M x < count N x")
        case True
        thus ?thesis
          using fx_eq_fa by blast
     next
        case False
        hence cnt_x: "count M x \<ge> count N x"
          by fastforce
        have "count M x + count (image_mset f ?Ma) (f a) + count ?Na a
          < count N x + count (image_mset f ?Na) (f a) + count ?Ma a"
          using cnt_lt x_ne_a fx_eq_fa by (subst (asm) (1 2) m_part, subst (asm) (1 2) n_part, auto)
        hence "count (image_mset f ?Ma) (f a) + count ?Na a
          < count (image_mset f ?Na) (f a) + count ?Ma a"
          using cnt_x by linarith
        thus ?thesis
          using ih[OF f_eq_ma_na] by (metis count_filter_mset nat_neq_iff)
      qed
    qed
  qed
qed auto

lemma count_image_mset_le_imp_lt:
  assumes
    "count (image_mset f M) (f a) \<le> count (image_mset f N) (f a)" and
    "count M a > count N a"
  shows "\<exists>b. f b = f a \<and> count M b < count N b"
  using assms by (auto intro: count_image_mset_le_imp_lt_raw[of "set_mset M \<union> set_mset N"])

lemma Max_in_mset: "M \<noteq> {#} \<Longrightarrow> Max_mset M \<in># M"
  by simp

lemma Max_lt_imp_lt_mset:
  assumes n_nemp: "N \<noteq> {#}" and max: "Max_mset M < Max_mset N" (is "?max_M < ?max_N")
  shows "M < N"
proof (cases "M = {#}")
  case m_nemp: False

  have max_n_in_n: "?max_N \<in># N"
    using n_nemp by simp
  have max_n_nin_m: "?max_N \<notin># M"
    using max Max_ge leD by auto

  have "M \<noteq> N"
    using max by auto
  moreover
  {
    fix y
    assume "count N y < count M y"
    hence "y \<in># M"
      by blast
    hence "?max_M \<ge> y"
      by simp
    hence "?max_N > y"
      using max by auto
    hence "\<exists>x > y. count M x < count N x"
      using max_n_nin_m max_n_in_n by fastforce
  }
  ultimately show ?thesis
    unfolding less_multiset\<^sub>H\<^sub>O by blast
qed (auto simp: n_nemp)

lemma fold_mset_singleton[simp]: "fold_mset f z {#x#} = f x z"
  by (simp add: fold_mset_def)

end
