(*  Title:       Extension Orders
    Author:      Heiko Becker <heikobecker92@gmail.com>, 2016
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Author:      Dmitriy Traytel <traytel@inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Extension Orders\<close>

theory Extension_Orders
imports Lambda_Free_Util Infinite_Chain "HOL-Cardinals.Wellorder_Extension"
begin

text \<open>
This theory defines locales for categorizing extension orders used for orders on
\<open>\<lambda>\<close>-free higher-order terms and defines variants of the lexicographic and
multiset orders.
\<close>


subsection \<open>Locales\<close>

locale ext =
  fixes ext :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  assumes
    mono_strong: "(\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt' y x) \<Longrightarrow> ext gt ys xs \<Longrightarrow> ext gt' ys xs" and
    map: "finite A \<Longrightarrow> ys \<in> lists A \<Longrightarrow> xs \<in> lists A \<Longrightarrow> (\<forall>x \<in> A. \<not> gt (f x) (f x)) \<Longrightarrow>
      (\<forall>z \<in> A. \<forall>y \<in> A. \<forall>x \<in> A. gt (f z) (f y) \<longrightarrow> gt (f y) (f x) \<longrightarrow> gt (f z) (f x)) \<Longrightarrow>
      (\<forall>y \<in> A. \<forall>x \<in> A. gt y x \<longrightarrow> gt (f y) (f x)) \<Longrightarrow> ext gt ys xs \<Longrightarrow> ext gt (map f ys) (map f xs)"
begin

lemma mono[mono]: "gt \<le> gt' \<Longrightarrow> ext gt \<le> ext gt'"
  using mono_strong by blast

end

locale ext_irrefl = ext +
  assumes irrefl: "(\<forall>x \<in> set xs. \<not> gt x x) \<Longrightarrow> \<not> ext gt xs xs"

locale ext_trans = ext +
  assumes trans: "zs \<in> lists A \<Longrightarrow> ys \<in> lists A \<Longrightarrow> xs \<in> lists A \<Longrightarrow>
    (\<forall>z \<in> A. \<forall>y \<in> A. \<forall>x \<in> A. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x) \<Longrightarrow> ext gt zs ys \<Longrightarrow> ext gt ys xs \<Longrightarrow>
    ext gt zs xs"

locale ext_irrefl_before_trans = ext_irrefl +
  assumes trans_from_irrefl: "finite A \<Longrightarrow> zs \<in> lists A \<Longrightarrow> ys \<in> lists A \<Longrightarrow> xs \<in> lists A \<Longrightarrow>
    (\<forall>x \<in> A. \<not> gt x x) \<Longrightarrow> (\<forall>z \<in> A. \<forall>y \<in> A. \<forall>x \<in> A. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x) \<Longrightarrow> ext gt zs ys \<Longrightarrow>
    ext gt ys xs \<Longrightarrow> ext gt zs xs"

locale ext_trans_before_irrefl = ext_trans +
  assumes irrefl_from_trans: "(\<forall>z \<in> set xs. \<forall>y \<in> set xs. \<forall>x \<in> set xs. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x) \<Longrightarrow>
    (\<forall>x \<in> set xs. \<not> gt x x) \<Longrightarrow> \<not> ext gt xs xs"

locale ext_irrefl_trans_strong = ext_irrefl +
  assumes trans_strong: "(\<forall>z \<in> set zs. \<forall>y \<in> set ys. \<forall>x \<in> set xs. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x) \<Longrightarrow>
    ext gt zs ys \<Longrightarrow> ext gt ys xs \<Longrightarrow> ext gt zs xs"

sublocale ext_irrefl_trans_strong < ext_irrefl_before_trans
  by standard (erule irrefl, metis in_listsD trans_strong)

sublocale ext_irrefl_trans_strong < ext_trans
  by standard (metis in_listsD trans_strong)

sublocale ext_irrefl_trans_strong < ext_trans_before_irrefl
  by standard (rule irrefl)

locale ext_snoc = ext +
  assumes snoc: "ext gt (xs @ [x]) xs"

locale ext_compat_cons = ext +
  assumes compat_cons: "ext gt ys xs \<Longrightarrow> ext gt (x # ys) (x # xs)"
begin

lemma compat_append_left: "ext gt ys xs \<Longrightarrow> ext gt (zs @ ys) (zs @ xs)"
  by (induct zs) (auto intro: compat_cons)

end

locale ext_compat_snoc = ext +
  assumes compat_snoc: "ext gt ys xs \<Longrightarrow> ext gt (ys @ [x]) (xs @ [x])"
begin

lemma compat_append_right: "ext gt ys xs \<Longrightarrow> ext gt (ys @ zs) (xs @ zs)"
  by (induct zs arbitrary: xs ys rule: rev_induct)
    (auto intro: compat_snoc simp del: append_assoc simp: append_assoc[symmetric])

end

locale ext_compat_list = ext +
  assumes compat_list: "y \<noteq> x \<Longrightarrow> gt y x \<Longrightarrow> ext gt (xs @ y # xs') (xs @ x # xs')"

locale ext_singleton = ext +
  assumes singleton: "y \<noteq> x \<Longrightarrow> ext gt [y] [x] \<longleftrightarrow> gt y x"

locale ext_compat_list_strong = ext_compat_cons + ext_compat_snoc + ext_singleton
begin

lemma compat_list: "y \<noteq> x \<Longrightarrow> gt y x \<Longrightarrow> ext gt (xs @ y # xs') (xs @ x # xs')"
  using compat_append_left[of gt "y # xs'" "x # xs'" xs]
    compat_append_right[of gt, of "[y]" "[x]" xs'] singleton[of y x gt]
  by fastforce

end

sublocale ext_compat_list_strong < ext_compat_list
  by standard (fact compat_list)

locale ext_total = ext +
  assumes total: "(\<forall>y \<in> A. \<forall>x \<in> A. gt y x \<or> gt x y \<or> y = x) \<Longrightarrow> ys \<in> lists A \<Longrightarrow> xs \<in> lists A \<Longrightarrow>
    ext gt ys xs \<or> ext gt xs ys \<or> ys = xs"

locale ext_wf = ext +
  assumes wf: "wfP (\<lambda>x y. gt y x) \<Longrightarrow> wfP (\<lambda>xs ys. ext gt ys xs)"

locale ext_hd_or_tl = ext +
  assumes hd_or_tl: "(\<forall>z y x. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x) \<Longrightarrow> (\<forall>y x. gt y x \<or> gt x y \<or> y = x) \<Longrightarrow>
    length ys = length xs \<Longrightarrow> ext gt (y # ys) (x # xs) \<Longrightarrow> gt y x \<or> ext gt ys xs"

locale ext_wf_bounded = ext_irrefl_before_trans + ext_hd_or_tl
begin

context
  fixes gt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    gt_irrefl: "\<And>z. \<not> gt z z" and
    gt_trans: "\<And>z y x. gt z y \<Longrightarrow> gt y x \<Longrightarrow> gt z x" and
    gt_total: "\<And>y x. gt y x \<or> gt x y \<or> y = x" and
    gt_wf: "wfP (\<lambda>x y. gt y x)"
begin

lemma irrefl_gt: "\<not> ext gt xs xs"
  using irrefl gt_irrefl by simp

lemma trans_gt: "ext gt zs ys \<Longrightarrow> ext gt ys xs \<Longrightarrow> ext gt zs xs"
  by (rule trans_from_irrefl[of "set zs \<union> set ys \<union> set xs" zs ys xs gt])
    (auto intro: gt_trans simp: gt_irrefl)

lemma hd_or_tl_gt: "length ys = length xs \<Longrightarrow> ext gt (y # ys) (x # xs) \<Longrightarrow> gt y x \<or> ext gt ys xs"
  by (rule hd_or_tl) (auto intro: gt_trans simp: gt_total)

lemma wf_same_length_if_total: "wfP (\<lambda>xs ys. length ys = n \<and> length xs = n \<and> ext gt ys xs)"
proof (induct n)
  case 0
  thus ?case
    unfolding wfP_def wf_def using irrefl by auto
next
  case (Suc n)
  note ih = this(1)

  define gt_hd where "\<And>ys xs. gt_hd ys xs \<longleftrightarrow> gt (hd ys) (hd xs)"
  define gt_tl where "\<And>ys xs. gt_tl ys xs \<longleftrightarrow> ext gt (tl ys) (tl xs)"

  have hd_tl: "gt_hd ys xs \<or> gt_tl ys xs"
    if len_ys: "length ys = Suc n" and len_xs: "length xs = Suc n" and ys_gt_xs: "ext gt ys xs"
    for n ys xs
    using len_ys len_xs ys_gt_xs unfolding gt_hd_def gt_tl_def
    by (cases xs; cases ys) (auto simp: hd_or_tl_gt)

  show ?case
    unfolding wfP_iff_no_inf_chain
  proof (intro notI)
    let ?gtsn = "\<lambda>ys xs. length ys = n \<and> length xs = n \<and> ext gt ys xs"
    let ?gtsSn = "\<lambda>ys xs. length ys = Suc n \<and> length xs = Suc n \<and> ext gt ys xs"
    let ?gttlSn = "\<lambda>ys xs. length ys = Suc n \<and> length xs = Suc n \<and> gt_tl ys xs"

    assume "\<exists>f. inf_chain ?gtsSn f"
    then obtain xs where xs_bad: "bad ?gtsSn xs"
      unfolding inf_chain_def bad_def by blast

    let ?ff = "worst_chain ?gtsSn gt_hd"

    have wf_hd: "wf {(xs, ys). gt_hd ys xs}"
      unfolding gt_hd_def by (rule wfP_app[OF gt_wf, of hd, unfolded wfP_def])

    have "inf_chain ?gtsSn ?ff"
      by (rule worst_chain_bad[OF wf_hd xs_bad])
    moreover have "\<not> gt_hd (?ff i) (?ff (Suc i))" for i
      by (rule worst_chain_not_gt[OF wf_hd xs_bad]) (blast intro: trans_gt)
    ultimately have tl_bad: "inf_chain ?gttlSn ?ff"
      unfolding inf_chain_def using hd_tl by blast

    have "\<not> inf_chain ?gtsn (tl \<circ> ?ff)"
      using wfP_iff_no_inf_chain[THEN iffD1, OF ih] by blast
    hence tl_good: "\<not> inf_chain ?gttlSn ?ff"
      unfolding inf_chain_def gt_tl_def by force

    show False
      using tl_bad tl_good by sat
  qed
qed

lemma wf_bounded_if_total: "wfP (\<lambda>xs ys. length ys \<le> n \<and> length xs \<le> n \<and> ext gt ys xs)"
  unfolding wfP_iff_no_inf_chain
proof (intro notI, induct n rule: less_induct)
  case (less n)
  note ih = this(1) and ex_bad = this(2)

  let ?gtsle = "\<lambda>ys xs. length ys \<le> n \<and> length xs \<le> n \<and> ext gt ys xs"

  obtain xs where xs_bad: "bad ?gtsle xs"
    using ex_bad unfolding inf_chain_def bad_def by blast

  let ?ff = "worst_chain ?gtsle (\<lambda>ys xs. length ys > length xs)"

  note wf_len = wf_app[OF wellorder_class.wf, of length, simplified]

  have ff_bad: "inf_chain ?gtsle ?ff"
    by (rule worst_chain_bad[OF wf_len xs_bad])
  have ffi_bad: "\<And>i. bad ?gtsle (?ff i)"
    by (rule inf_chain_bad[OF ff_bad])

  have len_le_n: "\<And>i. length (?ff i) \<le> n"
    using worst_chain_pred[OF wf_len xs_bad] by simp
  have len_le_Suc: "\<And>i. length (?ff i) \<le> length (?ff (Suc i))"
    using worst_chain_not_gt[OF wf_len xs_bad] not_le_imp_less by (blast intro: trans_gt)

  show False
  proof (cases "\<exists>k. length (?ff k) = n")
    case False
    hence len_lt_n: "\<And>i. length (?ff i) < n"
      using len_le_n by (blast intro: le_neq_implies_less)
    hence nm1_le: "n - 1 < n"
      by fastforce

    let ?gtslt = "\<lambda>ys xs. length ys \<le> n - 1 \<and> length xs \<le> n - 1 \<and> ext gt ys xs"

    have "inf_chain ?gtslt ?ff"
      using ff_bad len_lt_n unfolding inf_chain_def
      by (metis (no_types, lifting) Suc_diff_1 le_antisym nat_neq_iff not_less0 not_less_eq_eq)
    thus False
      using ih[OF nm1_le] by blast
  next
    case True
    then obtain k where len_eq_n: "length (?ff k) = n"
      by blast

    let ?gtssl = "\<lambda>ys xs. length ys = n \<and> length xs = n \<and> ext gt ys xs"

    have len_eq_n: "length (?ff (i + k)) = n" for i
      by (induct i) (simp add: len_eq_n,
        metis (lifting) len_le_n len_le_Suc add_Suc dual_order.antisym)

    have "inf_chain ?gtsle (\<lambda>i. ?ff (i + k))"
      by (rule inf_chain_offset[OF ff_bad])
    hence "inf_chain ?gtssl (\<lambda>i. ?ff (i + k))"
      unfolding inf_chain_def using len_eq_n by presburger
    hence "\<not> wfP (\<lambda>xs ys. ?gtssl ys xs)"
      using wfP_iff_no_inf_chain by blast
    thus False
      using wf_same_length_if_total[of n] by sat
  qed
qed

end

context
  fixes gt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    gt_irrefl: "\<And>z. \<not> gt z z" and
    gt_wf: "wfP (\<lambda>x y. gt y x)"
begin

lemma wf_bounded: "wfP (\<lambda>xs ys. length ys \<le> n \<and> length xs \<le> n \<and> ext gt ys xs)"
proof -
  obtain Ge' where
    gt_sub_Ge': "{(x, y). gt y x} \<subseteq> Ge'" and
    Ge'_wo: "Well_order Ge'" and
    Ge'_fld: "Field Ge' = UNIV"
    using total_well_order_extension[OF gt_wf[unfolded wfP_def]] by blast

  define gt' where "\<And>y x. gt' y x \<longleftrightarrow> y \<noteq> x \<and> (x, y) \<in> Ge'"

  have gt_imp_gt': "gt \<le> gt'"
    by (auto simp: gt'_def gt_irrefl intro: gt_sub_Ge'[THEN subsetD])

  have gt'_irrefl: "\<And>z. \<not> gt' z z"
    unfolding gt'_def by simp

  have gt'_trans: "\<And>z y x. gt' z y \<Longrightarrow> gt' y x \<Longrightarrow> gt' z x"
    using Ge'_wo
    unfolding gt'_def well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def
      trans_def antisym_def
    by blast

  have "wf {(x, y). (x, y) \<in> Ge' \<and> x \<noteq> y}"
    by (rule Ge'_wo[unfolded well_order_on_def set_diff_eq
      case_prod_eta[symmetric, of "\<lambda>xy. xy \<in> Ge' \<and> xy \<notin> Id"] pair_in_Id_conv, THEN conjunct2])
  moreover have "\<And>y x. (x, y) \<in> Ge' \<and> x \<noteq> y \<longleftrightarrow> y \<noteq> x \<and> (x, y) \<in> Ge'"
    by auto
  ultimately have gt'_wf: "wfP (\<lambda>x y. gt' y x)"
    unfolding wfP_def gt'_def by simp

  have gt'_total: "\<And>x y. gt' y x \<or> gt' x y \<or> y = x"
    using Ge'_wo unfolding gt'_def well_order_on_def linear_order_on_def total_on_def Ge'_fld
    by blast

  have "wfP (\<lambda>xs ys. length ys \<le> n \<and> length xs \<le> n \<and> ext gt' ys xs)"
    using wf_bounded_if_total gt'_total gt'_irrefl gt'_trans gt'_wf by blast
  thus ?thesis
    by (rule wfP_subset) (auto intro: mono[OF gt_imp_gt', THEN predicate2D])
qed

end

end


subsection \<open>Lexicographic Extension\<close>

inductive lexext :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" for gt where
  lexext_Nil: "lexext gt (y # ys) []"
| lexext_Cons: "gt y x \<Longrightarrow> lexext gt (y # ys) (x # xs)"
| lexext_Cons_eq: "lexext gt ys xs \<Longrightarrow> lexext gt (x # ys) (x # xs)"

lemma lexext_simps[simp]:
  "lexext gt ys [] \<longleftrightarrow> ys \<noteq> []"
  "\<not> lexext gt [] xs"
  "lexext gt (y # ys) (x # xs) \<longleftrightarrow> gt y x \<or> x = y \<and> lexext gt ys xs"
proof
  show "lexext gt ys [] \<Longrightarrow> (ys \<noteq> [])"
    by (metis lexext.cases list.distinct(1))
next
  show "ys \<noteq> [] \<Longrightarrow> lexext gt ys []"
    by (metis lexext_Nil list.exhaust)
next
  show "\<not> lexext gt [] xs"
    using lexext.cases by auto
next
  show "lexext gt (y # ys) (x # xs) = (gt y x \<or> x = y \<and> lexext gt ys xs)"
  proof -
    have fwdd: "lexext gt (y # ys) (x # xs) \<longrightarrow> gt y x \<or> x = y \<and> lexext gt ys xs"
    proof
      assume "lexext gt (y # ys) (x # xs)"
      thus "gt y x \<or> x = y \<and> lexext gt ys xs"
        using lexext.cases by blast
    qed
    have backd: "gt y x \<or> x = y \<and> lexext gt ys xs \<longrightarrow> lexext gt (y # ys) (x # xs)"
      by (simp add: lexext_Cons lexext_Cons_eq)
    show "lexext gt (y # ys) (x # xs) = (gt y x \<or> x = y \<and> lexext gt ys xs)"
      using fwdd backd by blast
  qed
qed

lemma lexext_mono_strong:
  assumes
    "\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt' y x" and
    "lexext gt ys xs"
  shows "lexext gt' ys xs"
  using assms by (induct ys xs rule: list_induct2') auto

lemma lexext_map_strong:
  "(\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt (f y) (f x)) \<Longrightarrow> lexext gt ys xs \<Longrightarrow>
   lexext gt (map f ys) (map f xs)"
  by (induct ys xs rule: list_induct2') auto

lemma lexext_irrefl:
  assumes "\<forall>x \<in> set xs. \<not> gt x x"
  shows "\<not> lexext gt xs xs"
  using assms by (induct xs) auto

lemma lexext_trans_strong:
  assumes
    "\<forall>z \<in> set zs. \<forall>y \<in> set ys. \<forall>x \<in> set xs. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x" and
    "lexext gt zs ys" and "lexext gt ys xs"
  shows "lexext gt zs xs"
  using assms
proof (induct zs arbitrary: ys xs)
  case (Cons z zs)
  note zs_trans = this(1)
  show ?case
    using Cons(2-4)
  proof (induct ys arbitrary: xs rule: list.induct)
    case (Cons y ys)
    note ys_trans = this(1) and gt_trans = this(2) and zzs_gt_yys = this(3) and yys_gt_xs = this(4)
    show ?case
    proof (cases xs)
      case xs: (Cons x xs)
      thus ?thesis
      proof (unfold xs)
        note yys_gt_xxs = yys_gt_xs[unfolded xs]
        note gt_trans = gt_trans[unfolded xs]

        let ?case = "lexext gt (z # zs) (x # xs)"

        {
          assume "gt z y" and "gt y x"
          hence ?case
            using gt_trans by simp
        }
        moreover
        {
          assume "gt z y" and "x = y"
          hence ?case
            by simp
        }
        moreover
        {
          assume "y = z" and "gt y x"
          hence ?case
            by simp
        }
        moreover
        {
          assume
            y_eq_z: "y = z" and
            zs_gt_ys: "lexext gt zs ys" and
            x_eq_y: "x = y" and
            ys_gt_xs: "lexext gt ys xs"

          have "lexext gt zs xs"
            by (rule zs_trans[OF _ zs_gt_ys ys_gt_xs]) (meson gt_trans[simplified])
          hence ?case
            by (simp add: x_eq_y y_eq_z)
        }
        ultimately show ?case
          using zzs_gt_yys yys_gt_xxs by force
      qed
    qed auto
  qed auto
qed auto

lemma lexext_snoc: "lexext gt (xs @ [x]) xs"
  by (induct xs) auto

lemmas lexext_compat_cons = lexext_Cons_eq

lemma lexext_compat_snoc_if_same_length:
  assumes "length ys = length xs" and "lexext gt ys xs"
  shows "lexext gt (ys @ [x]) (xs @ [x])"
  using assms(2,1) by (induct rule: lexext.induct) auto

lemma lexext_compat_list: "gt y x \<Longrightarrow> lexext gt (xs @ y # xs') (xs @ x # xs')"
  by (induct xs) auto

lemma lexext_singleton: "lexext gt [y] [x] \<longleftrightarrow> gt y x"
  by simp

lemma lexext_total: "(\<forall>y \<in> B. \<forall>x \<in> A. gt y x \<or> gt x y \<or> y = x) \<Longrightarrow> ys \<in> lists B \<Longrightarrow> xs \<in> lists A \<Longrightarrow>
  lexext gt ys xs \<or> lexext gt xs ys \<or> ys = xs"
  by (induct ys xs rule: list_induct2') auto

lemma lexext_hd_or_tl: "lexext gt (y # ys) (x # xs) \<Longrightarrow> gt y x \<or> lexext gt ys xs"
  by auto

interpretation lexext: ext lexext
  by standard (fact lexext_mono_strong, rule lexext_map_strong, metis in_listsD)

interpretation lexext: ext_irrefl_trans_strong lexext
  by standard (fact lexext_irrefl, fact lexext_trans_strong)

interpretation lexext: ext_snoc lexext
  by standard (fact lexext_snoc)

interpretation lexext: ext_compat_cons lexext
  by standard (fact lexext_compat_cons)

interpretation lexext: ext_compat_list lexext
  by standard (rule lexext_compat_list)

interpretation lexext: ext_singleton lexext
  by standard (rule lexext_singleton)

interpretation lexext: ext_total lexext
  by standard (fact lexext_total)

interpretation lexext: ext_hd_or_tl lexext
  by standard (rule lexext_hd_or_tl)

interpretation lexext: ext_wf_bounded lexext
  by standard


subsection \<open>Reverse (Right-to-Left) Lexicographic Extension\<close>

abbreviation lexext_rev :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "lexext_rev gt ys xs \<equiv> lexext gt (rev ys) (rev xs)"

lemma lexext_rev_simps[simp]:
  "lexext_rev gt ys [] \<longleftrightarrow> ys \<noteq> []"
  "\<not> lexext_rev gt [] xs"
  "lexext_rev gt (ys @ [y]) (xs @ [x]) \<longleftrightarrow> gt y x \<or> x = y \<and> lexext_rev gt ys xs"
  by simp+

lemma lexext_rev_cons_cons:
  assumes "length ys = length xs"
  shows "lexext_rev gt (y # ys) (x # xs) \<longleftrightarrow> lexext_rev gt ys xs \<or> ys = xs \<and> gt y x"
  using assms
proof (induct arbitrary: y x rule: rev_induct2)
  case Nil
  thus ?case
    by simp
next
  case (snoc y' ys x' xs)
  show ?case
    using snoc(2) by auto
qed

lemma lexext_rev_mono_strong:
  assumes
    "\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt' y x" and
    "lexext_rev gt ys xs"
  shows "lexext_rev gt' ys xs"
  using assms by (simp add: lexext_mono_strong)

lemma lexext_rev_map_strong:
  "(\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt (f y) (f x)) \<Longrightarrow> lexext_rev gt ys xs \<Longrightarrow>
   lexext_rev gt (map f ys) (map f xs)"
  by (simp add: lexext_map_strong rev_map)

lemma lexext_rev_irrefl:
  assumes "\<forall>x \<in> set xs. \<not> gt x x"
  shows "\<not> lexext_rev gt xs xs"
  using assms by (simp add: lexext_irrefl)

lemma lexext_rev_trans_strong:
  assumes
    "\<forall>z \<in> set zs. \<forall>y \<in> set ys. \<forall>x \<in> set xs. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x" and
    "lexext_rev gt zs ys" and "lexext_rev gt ys xs"
  shows "lexext_rev gt zs xs"
  using assms(1) lexext_trans_strong[OF _ assms(2,3), unfolded set_rev] by sat

lemma lexext_rev_compat_cons_if_same_length:
  assumes "length ys = length xs" and "lexext_rev gt ys xs"
  shows "lexext_rev gt (x # ys) (x # xs)"
  using assms by (simp add: lexext_compat_snoc_if_same_length)

lemma lexext_rev_compat_snoc: "lexext_rev gt ys xs \<Longrightarrow> lexext_rev gt (ys @ [x]) (xs @ [x])"
  by (simp add: lexext_compat_cons)

lemma lexext_rev_compat_list: "gt y x \<Longrightarrow> lexext_rev gt (xs @ y # xs') (xs @ x # xs')"
  by (induct xs' rule: rev_induct) auto

lemma lexext_rev_singleton: "lexext_rev gt [y] [x] \<longleftrightarrow> gt y x"
  by simp

lemma lexext_rev_total:
  "(\<forall>y \<in> B. \<forall>x \<in> A. gt y x \<or> gt x y \<or> y = x) \<Longrightarrow> ys \<in> lists B \<Longrightarrow> xs \<in> lists A \<Longrightarrow>
   lexext_rev gt ys xs \<or> lexext_rev gt xs ys \<or> ys = xs"
  by (rule lexext_total[of _ _ _ "rev ys" "rev xs", simplified])

lemma lexext_rev_hd_or_tl:
  assumes
    "length ys = length xs" and
    "lexext_rev gt (y # ys) (x # xs)"
  shows "gt y x \<or> lexext_rev gt ys xs"
  using assms lexext_rev_cons_cons by fastforce

interpretation lexext_rev: ext lexext_rev
  by standard (fact lexext_rev_mono_strong, rule lexext_rev_map_strong, metis in_listsD)

interpretation lexext_rev: ext_irrefl_trans_strong lexext_rev
  by standard (fact lexext_rev_irrefl, fact lexext_rev_trans_strong)

interpretation lexext_rev: ext_compat_snoc lexext_rev
  by standard (fact lexext_rev_compat_snoc)

interpretation lexext_rev: ext_compat_list lexext_rev
  by standard (rule lexext_rev_compat_list)

interpretation lexext_rev: ext_singleton lexext_rev
  by standard (rule lexext_rev_singleton)

interpretation lexext_rev: ext_total lexext_rev
  by standard (fact lexext_rev_total)

interpretation lexext_rev: ext_hd_or_tl lexext_rev
  by standard (rule lexext_rev_hd_or_tl)

interpretation lexext_rev: ext_wf_bounded lexext_rev
  by standard


subsection \<open>Generic Length Extension\<close>

definition lenext :: "('a list \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "lenext gts ys xs \<longleftrightarrow> length ys > length xs \<or> length ys = length xs \<and> gts ys xs"

lemma
  lenext_mono_strong: "(gts ys xs \<Longrightarrow> gts' ys xs) \<Longrightarrow> lenext gts ys xs \<Longrightarrow> lenext gts' ys xs" and
  lenext_map_strong: "(length ys = length xs \<Longrightarrow> gts ys xs \<Longrightarrow> gts (map f ys) (map f xs)) \<Longrightarrow>
    lenext gts ys xs \<Longrightarrow> lenext gts (map f ys) (map f xs)" and
  lenext_irrefl: "\<not> gts xs xs \<Longrightarrow> \<not> lenext gts xs xs" and
  lenext_trans: "(gts zs ys \<Longrightarrow> gts ys xs \<Longrightarrow> gts zs xs) \<Longrightarrow> lenext gts zs ys \<Longrightarrow> lenext gts ys xs \<Longrightarrow>
    lenext gts zs xs" and
  lenext_snoc: "lenext gts (xs @ [x]) xs" and
  lenext_compat_cons: "(length ys = length xs \<Longrightarrow> gts ys xs \<Longrightarrow> gts (x # ys) (x # xs)) \<Longrightarrow>
    lenext gts ys xs \<Longrightarrow> lenext gts (x # ys) (x # xs)" and
  lenext_compat_snoc: "(length ys = length xs \<Longrightarrow> gts ys xs \<Longrightarrow> gts (ys @ [x]) (xs @ [x])) \<Longrightarrow>
    lenext gts ys xs \<Longrightarrow> lenext gts (ys @ [x]) (xs @ [x])" and
  lenext_compat_list: "gts (xs @ y # xs') (xs @ x # xs') \<Longrightarrow>
    lenext gts (xs @ y # xs') (xs @ x # xs')" and
  lenext_singleton: "lenext gts [y] [x] \<longleftrightarrow> gts [y] [x]" and
  lenext_total: "(gts ys xs \<or> gts xs ys \<or> ys = xs) \<Longrightarrow>
    lenext gts ys xs \<or> lenext gts xs ys \<or> ys = xs" and
  lenext_hd_or_tl: "(length ys = length xs \<Longrightarrow> gts (y # ys) (x # xs) \<Longrightarrow> gt y x \<or> gts ys xs) \<Longrightarrow>
    lenext gts (y # ys) (x # xs) \<Longrightarrow> gt y x \<or> lenext gts ys xs"
  unfolding lenext_def by auto


subsection \<open>Length-Lexicographic Extension\<close>

abbreviation len_lexext :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "len_lexext gt \<equiv> lenext (lexext gt)"

lemma len_lexext_mono_strong:
  "(\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt' y x) \<Longrightarrow> len_lexext gt ys xs \<Longrightarrow> len_lexext gt' ys xs"
  by (rule lenext_mono_strong[OF lexext_mono_strong])

lemma len_lexext_map_strong:
  "(\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt (f y) (f x)) \<Longrightarrow> len_lexext gt ys xs \<Longrightarrow>
   len_lexext gt (map f ys) (map f xs)"
  by (rule lenext_map_strong) (metis lexext_map_strong)

lemma len_lexext_irrefl: "(\<forall>x \<in> set xs. \<not> gt x x) \<Longrightarrow> \<not> len_lexext gt xs xs"
  by (rule lenext_irrefl[OF lexext_irrefl])

lemma len_lexext_trans_strong:
  "(\<forall>z \<in> set zs. \<forall>y \<in> set ys. \<forall>x \<in> set xs. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x) \<Longrightarrow> len_lexext gt zs ys \<Longrightarrow>
   len_lexext gt ys xs \<Longrightarrow> len_lexext gt zs xs"
  by (rule lenext_trans[OF lexext_trans_strong])

lemma len_lexext_snoc: "len_lexext gt (xs @ [x]) xs"
  by (rule lenext_snoc)

lemma len_lexext_compat_cons: "len_lexext gt ys xs \<Longrightarrow> len_lexext gt (x # ys) (x # xs)"
  by (intro lenext_compat_cons lexext_compat_cons)

lemma len_lexext_compat_snoc: "len_lexext gt ys xs \<Longrightarrow> len_lexext gt (ys @ [x]) (xs @ [x])"
  by (intro lenext_compat_snoc lexext_compat_snoc_if_same_length)

lemma len_lexext_compat_list: "gt y x \<Longrightarrow> len_lexext gt (xs @ y # xs') (xs @ x # xs')"
  by (intro lenext_compat_list lexext_compat_list)

lemma len_lexext_singleton[simp]: "len_lexext gt [y] [x] \<longleftrightarrow> gt y x"
  by (simp only: lenext_singleton lexext_singleton)

lemma len_lexext_total: "(\<forall>y \<in> B. \<forall>x \<in> A. gt y x \<or> gt x y \<or> y = x) \<Longrightarrow> ys \<in> lists B \<Longrightarrow> xs \<in> lists A \<Longrightarrow>
  len_lexext gt ys xs \<or> len_lexext gt xs ys \<or> ys = xs"
  by (rule lenext_total[OF lexext_total])

lemma len_lexext_iff_lenlex: "len_lexext gt ys xs \<longleftrightarrow> (xs, ys) \<in> lenlex {(x, y). gt y x}"
proof -
  {
    assume "length xs = length ys"
    hence "lexext gt ys xs \<longleftrightarrow> (xs, ys) \<in> lex {(x, y). gt y x}"
      by (induct xs ys rule: list_induct2) auto
  }
  thus ?thesis
    unfolding lenext_def lenlex_conv by auto
qed

lemma len_lexext_wf: "wfP (\<lambda>x y. gt y x) \<Longrightarrow> wfP (\<lambda>xs ys. len_lexext gt ys xs)"
  unfolding wfP_def len_lexext_iff_lenlex by (simp add: wf_lenlex)

lemma len_lexext_hd_or_tl: "len_lexext gt (y # ys) (x # xs) \<Longrightarrow> gt y x \<or> len_lexext gt ys xs"
  using lenext_hd_or_tl lexext_hd_or_tl by metis

interpretation len_lexext: ext len_lexext
  by standard (fact len_lexext_mono_strong, rule len_lexext_map_strong, metis in_listsD)

interpretation len_lexext: ext_irrefl_trans_strong len_lexext
  by standard (fact len_lexext_irrefl, fact len_lexext_trans_strong)

interpretation len_lexext: ext_snoc len_lexext
  by standard (fact len_lexext_snoc)

interpretation len_lexext: ext_compat_cons len_lexext
  by standard (fact len_lexext_compat_cons)

interpretation len_lexext: ext_compat_snoc len_lexext
  by standard (fact len_lexext_compat_snoc)

interpretation len_lexext: ext_compat_list len_lexext
  by standard (rule len_lexext_compat_list)

interpretation len_lexext: ext_singleton len_lexext
  by standard (rule len_lexext_singleton)

interpretation len_lexext: ext_total len_lexext
  by standard (fact len_lexext_total)

interpretation len_lexext: ext_wf len_lexext
  by standard (fact len_lexext_wf)

interpretation len_lexext: ext_hd_or_tl len_lexext
  by standard (rule len_lexext_hd_or_tl)

interpretation len_lexext: ext_wf_bounded len_lexext
  by standard


subsection \<open>Reverse (Right-to-Left) Length-Lexicographic Extension\<close>

abbreviation len_lexext_rev :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "len_lexext_rev gt \<equiv> lenext (lexext_rev gt)"

lemma len_lexext_rev_mono_strong:
  "(\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt' y x) \<Longrightarrow> len_lexext_rev gt ys xs \<Longrightarrow> len_lexext_rev gt' ys xs"
  by (rule lenext_mono_strong) (rule lexext_rev_mono_strong)

lemma len_lexext_rev_map_strong:
  "(\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt (f y) (f x)) \<Longrightarrow> len_lexext_rev gt ys xs \<Longrightarrow>
   len_lexext_rev gt (map f ys) (map f xs)"
  by (rule lenext_map_strong) (rule lexext_rev_map_strong)

lemma len_lexext_rev_irrefl: "(\<forall>x \<in> set xs. \<not> gt x x) \<Longrightarrow> \<not> len_lexext_rev gt xs xs"
  by (rule lenext_irrefl) (rule lexext_rev_irrefl)

lemma len_lexext_rev_trans_strong:
  "(\<forall>z \<in> set zs. \<forall>y \<in> set ys. \<forall>x \<in> set xs. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x) \<Longrightarrow> len_lexext_rev gt zs ys \<Longrightarrow>
   len_lexext_rev gt ys xs \<Longrightarrow> len_lexext_rev gt zs xs"
  by (rule lenext_trans) (rule lexext_rev_trans_strong)

lemma len_lexext_rev_snoc: "len_lexext_rev gt (xs @ [x]) xs"
  by (rule lenext_snoc)

lemma len_lexext_rev_compat_cons: "len_lexext_rev gt ys xs \<Longrightarrow> len_lexext_rev gt (x # ys) (x # xs)"
  by (intro lenext_compat_cons lexext_rev_compat_cons_if_same_length)

lemma len_lexext_rev_compat_snoc: "len_lexext_rev gt ys xs \<Longrightarrow> len_lexext_rev gt (ys @ [x]) (xs @ [x])"
  by (intro lenext_compat_snoc lexext_rev_compat_snoc)

lemma len_lexext_rev_compat_list: "gt y x \<Longrightarrow> len_lexext_rev gt (xs @ y # xs') (xs @ x # xs')"
  by (intro lenext_compat_list lexext_rev_compat_list)

lemma len_lexext_rev_singleton[simp]: "len_lexext_rev gt [y] [x] \<longleftrightarrow> gt y x"
  by (simp only: lenext_singleton lexext_rev_singleton)

lemma len_lexext_rev_total: "(\<forall>y \<in> B. \<forall>x \<in> A. gt y x \<or> gt x y \<or> y = x) \<Longrightarrow> ys \<in> lists B \<Longrightarrow>
  xs \<in> lists A \<Longrightarrow> len_lexext_rev gt ys xs \<or> len_lexext_rev gt xs ys \<or> ys = xs"
  by (rule lenext_total[OF lexext_rev_total])

lemma len_lexext_rev_iff_len_lexext: "len_lexext_rev gt ys xs \<longleftrightarrow> len_lexext gt (rev ys) (rev xs)"
  unfolding lenext_def by simp

lemma len_lexext_rev_wf: "wfP (\<lambda>x y. gt y x) \<Longrightarrow> wfP (\<lambda>xs ys. len_lexext_rev gt ys xs)"
  unfolding len_lexext_rev_iff_len_lexext
  by (rule wfP_app[of "\<lambda>xs ys. len_lexext gt ys xs" rev, simplified]) (rule len_lexext_wf)

lemma len_lexext_rev_hd_or_tl:
  "len_lexext_rev gt (y # ys) (x # xs) \<Longrightarrow> gt y x \<or> len_lexext_rev gt ys xs"
  using lenext_hd_or_tl lexext_rev_hd_or_tl by metis

interpretation len_lexext_rev: ext len_lexext_rev
  by standard (fact len_lexext_rev_mono_strong, rule len_lexext_rev_map_strong, metis in_listsD)

interpretation len_lexext_rev: ext_irrefl_trans_strong len_lexext_rev
  by standard (fact len_lexext_rev_irrefl, fact len_lexext_rev_trans_strong)

interpretation len_lexext_rev: ext_snoc len_lexext_rev
  by standard (fact len_lexext_rev_snoc)

interpretation len_lexext_rev: ext_compat_cons len_lexext_rev
  by standard (fact len_lexext_rev_compat_cons)

interpretation len_lexext_rev: ext_compat_snoc len_lexext_rev
  by standard (fact len_lexext_rev_compat_snoc)

interpretation len_lexext_rev: ext_compat_list len_lexext_rev
  by standard (rule len_lexext_rev_compat_list)

interpretation len_lexext_rev: ext_singleton len_lexext_rev
  by standard (rule len_lexext_rev_singleton)

interpretation len_lexext_rev: ext_total len_lexext_rev
  by standard (fact len_lexext_rev_total)

interpretation len_lexext_rev: ext_wf len_lexext_rev
  by standard (fact len_lexext_rev_wf)

interpretation len_lexext_rev: ext_hd_or_tl len_lexext_rev
  by standard (rule len_lexext_rev_hd_or_tl)

interpretation len_lexext_rev: ext_wf_bounded len_lexext_rev
  by standard


subsection \<open>Dershowitz--Manna Multiset Extension\<close>

definition msetext_dersh where
  "msetext_dersh gt ys xs = (let N = mset ys; M = mset xs in
     (\<exists>Y X. Y \<noteq> {#} \<and> Y \<subseteq># N \<and> M = (N - Y) + X \<and> (\<forall>x. x \<in># X \<longrightarrow> (\<exists>y. y \<in># Y \<and> gt y x))))"

text \<open>
The following proof is based on that of @{thm[source] less_multiset\<^sub>D\<^sub>M_imp_mult}.
\<close>

lemma msetext_dersh_imp_mult_rel:
  assumes
    ys_a: "ys \<in> lists A" and xs_a: "xs \<in> lists A" and
    ys_gt_xs: "msetext_dersh gt ys xs"
  shows "(mset xs, mset ys) \<in> mult {(x, y). x \<in> A \<and> y \<in> A \<and> gt y x}"
proof -
  obtain Y X where y_nemp: "Y \<noteq> {#}" and y_sub_ys: "Y \<subseteq># mset ys" and
    xs_eq: "mset xs = mset ys - Y + X" and ex_y: "\<forall>x. x \<in># X \<longrightarrow> (\<exists>y. y \<in># Y \<and> gt y x)"
    using ys_gt_xs[unfolded msetext_dersh_def Let_def] by blast
  have ex_y': "\<forall>x. x \<in># X \<longrightarrow> (\<exists>y. y \<in># Y \<and> x \<in> A \<and> y \<in> A \<and> gt y x)"
    using ex_y y_sub_ys xs_eq ys_a xs_a by (metis in_listsD mset_subset_eqD set_mset_mset union_iff)
  hence "(mset ys - Y + X, mset ys - Y + Y) \<in> mult {(x, y). x \<in> A \<and> y \<in> A \<and> gt y x}"
    using y_nemp y_sub_ys by (intro one_step_implies_mult) (auto simp: Bex_def trans_def)
  thus ?thesis
    using xs_eq y_sub_ys by (simp add: subset_mset.diff_add)
qed

lemma msetext_dersh_imp_mult: "msetext_dersh gt ys xs \<Longrightarrow> (mset xs, mset ys) \<in> mult {(x, y). gt y x}"
  using msetext_dersh_imp_mult_rel[of _ UNIV] by auto

lemma mult_imp_msetext_dersh_rel:
  assumes
    ys_a: "set_mset (mset ys) \<subseteq> A" and xs_a: "set_mset (mset xs) \<subseteq> A" and
    in_mult: "(mset xs, mset ys) \<in> mult {(x, y). x \<in> A \<and> y \<in> A \<and> gt y x}" and
    trans: "\<forall>z \<in> A. \<forall>y \<in> A. \<forall>x \<in> A. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x"
  shows "msetext_dersh gt ys xs"
  using in_mult ys_a xs_a unfolding mult_def msetext_dersh_def Let_def
proof induct
  case (base Ys)
  then obtain y M0 X where "Ys = M0 + {#y#}" and "mset xs = M0 + X" and "\<forall>a. a \<in># X \<longrightarrow> gt y a"
    unfolding mult1_def by auto
  thus ?case
    by (auto intro: exI[of _ "{#y#}"] exI[of _ X])
next
  case (step Ys Zs)
  note ys_zs_in_mult1 = this(2) and ih = this(3) and zs_a = this(4) and xs_a = this(5)

  have Ys_a: "set_mset Ys \<subseteq> A"
    using ys_zs_in_mult1 zs_a unfolding mult1_def by auto

  obtain Y X where y_nemp: "Y \<noteq> {#}" and y_sub_ys: "Y \<subseteq># Ys" and xs_eq: "mset xs = Ys - Y + X" and
    ex_y: "\<forall>x. x \<in># X \<longrightarrow> (\<exists>y. y \<in># Y \<and> gt y x)"
    using ih[OF Ys_a xs_a] by blast

  obtain z M0 Ya where zs_eq: "Zs = M0 + {#z#}" and ys_eq: "Ys = M0 + Ya" and
    z_gt: "\<forall>y. y \<in># Ya \<longrightarrow> y \<in> A \<and> z \<in> A \<and> gt z y"
    using ys_zs_in_mult1[unfolded mult1_def] by auto

  let ?Za = "Y - Ya + {#z#}"
  let ?Xa = "X + Ya + (Y - Ya) - Y"

  have xa_sub_x_ya: "set_mset ?Xa \<subseteq> set_mset (X + Ya)"
    by (metis diff_subset_eq_self in_diffD subsetI subset_mset.diff_diff_right)

  have x_a: "set_mset X \<subseteq> A"
    using xs_a xs_eq by auto
  have ya_a: "set_mset Ya \<subseteq> A"
    by (simp add: subsetI z_gt)

  have ex_y': "\<exists>y. y \<in># Y - Ya + {#z#} \<and> gt y x" if x_in: "x \<in># X + Ya" for x
  proof (cases "x \<in># X")
    case True
    then obtain y where y_in: "y \<in># Y" and y_gt_x: "gt y x"
      using ex_y by blast
    show ?thesis
    proof (cases "y \<in># Ya")
      case False
      hence "y \<in># Y - Ya + {#z#}"
        using y_in by fastforce
      thus ?thesis
        using y_gt_x by blast
    next
      case True
      hence "y \<in> A" and "z \<in> A" and "gt z y"
        using z_gt by blast+
      hence "gt z x"
        using trans y_gt_x x_a ya_a x_in by (meson subsetCE union_iff)
      thus ?thesis
        by auto
    qed
  next
    case False
    hence "x \<in># Ya"
      using x_in by auto
    hence "x \<in> A" and "z \<in> A" and "gt z x"
      using z_gt by blast+
    thus ?thesis
      by auto
  qed

  show ?case
  proof (rule exI[of _ ?Za], rule exI[of _ ?Xa], intro conjI)
    show "Y - Ya + {#z#} \<subseteq># Zs"
      using mset_subset_eq_mono_add subset_eq_diff_conv y_sub_ys ys_eq zs_eq by fastforce
  next
    show "mset xs = Zs - (Y - Ya + {#z#}) + (X + Ya + (Y - Ya) - Y)"
      unfolding xs_eq ys_eq zs_eq by (auto simp: multiset_eq_iff)
  next
    show "\<forall>x. x \<in># X + Ya + (Y - Ya) - Y \<longrightarrow> (\<exists>y. y \<in># Y - Ya + {#z#} \<and> gt y x)"
      using ex_y' xa_sub_x_ya by blast
  qed auto
qed

lemma msetext_dersh_mono_strong:
  "(\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt' y x) \<Longrightarrow> msetext_dersh gt ys xs \<Longrightarrow>
  msetext_dersh gt' ys xs"
  unfolding msetext_dersh_def Let_def
  by (metis mset_subset_eqD mset_subset_eq_add_right set_mset_mset)

lemma msetext_dersh_map_strong:
  assumes
    compat_f: "\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt (f y) (f x)" and
    ys_gt_xs: "msetext_dersh gt ys xs"
  shows "msetext_dersh gt (map f ys) (map f xs)"
proof -
  obtain Y X where
    y_nemp: "Y \<noteq> {#}" and y_sub_ys: "Y \<subseteq># mset ys" and xs_eq: "mset xs = mset ys - Y + X" and
    ex_y: "\<forall>x. x \<in># X \<longrightarrow> (\<exists>y. y \<in># Y \<and> gt y x)"
    using ys_gt_xs[unfolded msetext_dersh_def Let_def mset_map] by blast

  have x_sub_xs: "X \<subseteq># mset xs"
    using xs_eq by simp

  let ?fY = "image_mset f Y"
  let ?fX = "image_mset f X"

  show ?thesis
    unfolding msetext_dersh_def Let_def mset_map
  proof (intro exI conjI)
    show "image_mset f (mset xs) = image_mset f (mset ys) - ?fY + ?fX"
      using xs_eq[THEN arg_cong, of "image_mset f"] y_sub_ys by (metis image_mset_Diff image_mset_union)
  next
    obtain y where y: "\<forall>x. x \<in># X \<longrightarrow> y x \<in># Y \<and> gt (y x) x"
      using ex_y by moura

    show "\<forall>fx. fx \<in># ?fX \<longrightarrow> (\<exists>fy. fy \<in># ?fY \<and> gt fy fx)"
    proof (intro allI impI)
      fix fx
      assume "fx \<in># ?fX"
      then obtain x where fx: "fx = f x" and x_in: "x \<in># X"
        by auto
      hence y_in: "y x \<in># Y" and y_gt: "gt (y x) x"
        using y[rule_format, OF x_in] by blast+
      hence "f (y x) \<in># ?fY \<and> gt (f (y x)) (f x)"
        using compat_f y_sub_ys x_sub_xs x_in
        by (metis image_eqI in_image_mset mset_subset_eqD set_mset_mset)
      thus "\<exists>fy. fy \<in># ?fY \<and> gt fy fx"
        unfolding fx by auto
    qed
  qed (auto simp: y_nemp y_sub_ys image_mset_subseteq_mono)
qed

lemma msetext_dersh_trans:
  assumes
    zs_a: "zs \<in> lists A" and
    ys_a: "ys \<in> lists A" and
    xs_a: "xs \<in> lists A" and
    trans: "\<forall>z \<in> A. \<forall>y \<in> A. \<forall>x \<in> A. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x" and
    zs_gt_ys: "msetext_dersh gt zs ys" and
    ys_gt_xs: "msetext_dersh gt ys xs"
  shows "msetext_dersh gt zs xs"
proof (rule mult_imp_msetext_dersh_rel[OF _ _ _ trans])
  show "set_mset (mset zs) \<subseteq> A"
    using zs_a by auto
next
  show "set_mset (mset xs) \<subseteq> A"
    using xs_a by auto
next
  let ?Gt = "{(x, y). x \<in> A \<and> y \<in> A \<and> gt y x}"

  have "(mset xs, mset ys) \<in> mult ?Gt"
    by (rule msetext_dersh_imp_mult_rel[OF ys_a xs_a ys_gt_xs])
  moreover have "(mset ys, mset zs) \<in> mult ?Gt"
    by (rule msetext_dersh_imp_mult_rel[OF zs_a ys_a zs_gt_ys])
  ultimately show "(mset xs, mset zs) \<in> mult ?Gt"
    unfolding mult_def by simp
qed

lemma msetext_dersh_irrefl_from_trans:
  assumes
    trans: "\<forall>z \<in> set xs. \<forall>y \<in> set xs. \<forall>x \<in> set xs. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x" and
    irrefl: "\<forall>x \<in> set xs. \<not> gt x x"
  shows "\<not> msetext_dersh gt xs xs"
  unfolding msetext_dersh_def Let_def
proof clarify
  fix Y X
  assume y_nemp: "Y \<noteq> {#}" and y_sub_xs: "Y \<subseteq># mset xs" and xs_eq: "mset xs = mset xs - Y + X" and
    ex_y: "\<forall>x. x \<in># X \<longrightarrow> (\<exists>y. y \<in># Y \<and> gt y x)"

  have x_eq_y: "X = Y"
    using y_sub_xs xs_eq by (metis diff_union_cancelL subset_mset.diff_add)

  let ?Gt = "{(y, x). y \<in># Y \<and> x \<in># Y \<and> gt y x}"

  have "?Gt \<subseteq> set_mset Y \<times> set_mset Y"
    by auto
  hence fin: "finite ?Gt"
    by (auto dest!: infinite_super)
  moreover have "irrefl ?Gt"
    unfolding irrefl_def using irrefl y_sub_xs by (fastforce dest!: set_mset_mono)
  moreover have "trans ?Gt"
    unfolding trans_def using trans y_sub_xs by (fastforce dest!: set_mset_mono)
  ultimately have acyc: "acyclic ?Gt"
    by (rule finite_irrefl_trans_imp_wf[THEN wf_acyclic])

  have fin_y: "finite (set_mset Y)"
    using y_sub_xs by simp
  hence cyc: "\<not> acyclic ?Gt"
    proof (rule finite_nonempty_ex_succ_imp_cyclic)
      show "\<forall>x \<in># Y. \<exists>y \<in># Y. (y, x) \<in> ?Gt"
        using ex_y[unfolded x_eq_y] by auto
    qed (auto simp: y_nemp)

  show False
    using acyc cyc by sat
qed

lemma msetext_dersh_snoc: "msetext_dersh gt (xs @ [x]) xs"
  unfolding msetext_dersh_def Let_def
proof (intro exI conjI)
  show "mset xs = mset (xs @ [x]) - {#x#} + {#}"
    by simp
qed auto

lemma msetext_dersh_compat_cons:
  assumes ys_gt_xs: "msetext_dersh gt ys xs"
  shows "msetext_dersh gt (x # ys) (x # xs)"
proof -
  obtain Y X where
    y_nemp: "Y \<noteq> {#}" and y_sub_ys: "Y \<subseteq># mset ys" and xs_eq: "mset xs = mset ys - Y + X" and
    ex_y: "\<forall>x. x \<in># X \<longrightarrow> (\<exists>y. y \<in># Y \<and> gt y x)"
    using ys_gt_xs[unfolded msetext_dersh_def Let_def mset_map] by blast

  show ?thesis
    unfolding msetext_dersh_def Let_def
  proof (intro exI conjI)
    show "Y \<subseteq># mset (x # ys)"
      using y_sub_ys
      by (metis add_mset_add_single mset.simps(2) mset_subset_eq_add_left
        subset_mset.add_increasing2)
  next
    show "mset (x # xs) = mset (x # ys) - Y + X"
    proof -
      have "X + (mset ys - Y) = mset xs"
        by (simp add: union_commute xs_eq)
      hence "mset (x # xs) = X + (mset (x # ys) - Y)"
        by (metis add_mset_add_single mset.simps(2) mset_subset_eq_multiset_union_diff_commute
          union_mset_add_mset_right y_sub_ys)
      thus ?thesis
        by (simp add: union_commute)
    qed
  qed (auto simp: y_nemp ex_y)
qed

lemma msetext_dersh_compat_snoc: "msetext_dersh gt ys xs \<Longrightarrow> msetext_dersh gt (ys @ [x]) (xs @ [x])"
  using msetext_dersh_compat_cons[of gt ys xs x] unfolding msetext_dersh_def by simp

lemma msetext_dersh_compat_list:
  assumes y_gt_x: "gt y x"
  shows "msetext_dersh gt (xs @ y # xs') (xs @ x # xs')"
  unfolding msetext_dersh_def Let_def
proof (intro exI conjI)
  show "mset (xs @ x # xs') = mset (xs @ y # xs') - {#y#} + {#x#}"
    by auto
qed (auto intro: y_gt_x)

lemma msetext_dersh_singleton: "msetext_dersh gt [y] [x] \<longleftrightarrow> gt y x"
  unfolding msetext_dersh_def Let_def
  by (auto dest: nonempty_subseteq_mset_eq_singleton simp: nonempty_subseteq_mset_iff_singleton)

lemma msetext_dersh_wf:
  assumes wf_gt: "wfP (\<lambda>x y. gt y x)"
  shows "wfP (\<lambda>xs ys. msetext_dersh gt ys xs)"
proof (rule wfP_subset, rule wfP_app[of "\<lambda>xs ys. (xs, ys) \<in> mult {(x, y). gt y x}" mset])
  show "wfP (\<lambda>xs ys. (xs, ys) \<in> mult {(x, y). gt y x})"
    using wf_gt unfolding wfP_def by (auto intro: wf_mult)
next
  show "(\<lambda>xs ys. msetext_dersh gt ys xs) \<le> (\<lambda>x y. (mset x, mset y) \<in> mult {(x, y). gt y x})"
    using msetext_dersh_imp_mult by blast
qed

interpretation msetext_dersh: ext msetext_dersh
  by standard (fact msetext_dersh_mono_strong, rule msetext_dersh_map_strong, metis in_listsD)

interpretation msetext_dersh: ext_trans_before_irrefl msetext_dersh
  by standard (fact msetext_dersh_trans, fact msetext_dersh_irrefl_from_trans)

interpretation msetext_dersh: ext_snoc msetext_dersh
  by standard (fact msetext_dersh_snoc)

interpretation msetext_dersh: ext_compat_cons msetext_dersh
  by standard (fact msetext_dersh_compat_cons)

interpretation msetext_dersh: ext_compat_snoc msetext_dersh
  by standard (fact msetext_dersh_compat_snoc)

interpretation msetext_dersh: ext_compat_list msetext_dersh
  by standard (rule msetext_dersh_compat_list)

interpretation msetext_dersh: ext_singleton msetext_dersh
  by standard (rule msetext_dersh_singleton)

interpretation msetext_dersh: ext_wf msetext_dersh
  by standard (fact msetext_dersh_wf)


subsection \<open>Huet--Oppen Multiset Extension\<close>

definition msetext_huet where
  "msetext_huet gt ys xs = (let N = mset ys; M = mset xs in
     M \<noteq> N \<and> (\<forall>x. count M x > count N x \<longrightarrow> (\<exists>y. gt y x \<and> count N y > count M y)))"

lemma msetext_huet_imp_count_gt:
  assumes ys_gt_xs: "msetext_huet gt ys xs"
  shows "\<exists>x. count (mset ys) x > count (mset xs) x"
proof -
  obtain x where "count (mset ys) x \<noteq> count (mset xs) x"
    using ys_gt_xs[unfolded msetext_huet_def Let_def] by (fastforce intro: multiset_eqI)
  moreover
  {
    assume "count (mset ys) x < count (mset xs) x"
    hence ?thesis
      using ys_gt_xs[unfolded msetext_huet_def Let_def] by blast
  }
  moreover
  {
    assume "count (mset ys) x > count (mset xs) x"
    hence ?thesis
      by fast
  }
  ultimately show ?thesis
    by fastforce
qed

lemma msetext_huet_imp_dersh:
  assumes huet: "msetext_huet gt ys xs"
  shows "msetext_dersh gt ys xs"
proof (unfold msetext_dersh_def Let_def, intro exI conjI)
  let ?X = "mset xs - mset ys"
  let ?Y = "mset ys - mset xs"

  show "?Y \<noteq> {#}"
    by (metis msetext_huet_imp_count_gt[OF huet] empty_iff in_diff_count set_mset_empty)
  show "?Y \<subseteq># mset ys"
    by auto
  show "mset xs = mset ys - ?Y + ?X"
    by (metis add.commute diff_intersect_right_idem multiset_inter_def subset_mset.inf.cobounded2
      subset_mset.le_imp_diff_is_add)
  show "\<forall>x. x \<in># ?X \<longrightarrow> (\<exists>y. y \<in># ?Y \<and> gt y x)"
    using huet[unfolded msetext_huet_def Let_def, THEN conjunct2] by (meson in_diff_count)
qed

text \<open>
The following proof is based on that of @{thm[source] mult_imp_less_multiset\<^sub>H\<^sub>O}.
\<close>

lemma mult_imp_msetext_huet:
  assumes
    irrefl: "irreflp gt" and trans: "transp gt" and
    in_mult: "(mset xs, mset ys) \<in> mult {(x, y). gt y x}"
  shows "msetext_huet gt ys xs"
  using in_mult unfolding mult_def msetext_huet_def Let_def
proof (induct rule: trancl_induct)
  case (base Ys)
  thus ?case
    using irrefl unfolding irreflp_def msetext_huet_def Let_def mult1_def
    by (auto 0 3 split: if_splits)
next
  case (step Ys Zs)

  have asym[unfolded antisym_def, simplified]: "antisymp gt"
    by (rule irreflp_transp_imp_antisymP[OF irrefl trans])

  from step(3) have "mset xs \<noteq> Ys" and
    **: "\<And>x. count Ys x < count (mset xs) x \<Longrightarrow> (\<exists>y. gt y x \<and> count (mset xs) y < count Ys y)"
    by blast+
  from step(2) obtain M0 a K where
    *: "Zs = M0 + {#a#}" "Ys = M0 + K" "a \<notin># K" "\<And>b. b \<in># K \<Longrightarrow> gt a b"
    using irrefl unfolding mult1_def irreflp_def by force
  have "mset xs \<noteq> Zs"
  proof (cases "K = {#}")
    case True
    thus ?thesis
      using \<open>mset xs \<noteq> Ys\<close> ** *(1,2) irrefl[unfolded irreflp_def]
      by (metis One_nat_def add.comm_neutral count_single diff_union_cancelL lessI
        minus_multiset.rep_eq not_add_less2 plus_multiset.rep_eq union_commute zero_less_diff)
  next
    case False
    thus ?thesis
    proof -
      obtain aa :: "'a \<Rightarrow> 'a" where
        f1: "\<forall>a. \<not> count Ys a < count (mset xs) a \<or> gt (aa a) a \<and>
          count (mset xs) (aa a) < count Ys (aa a)"
        using "**" by moura
      have f2: "K + M0 = Ys"
        using "*"(2) union_ac(2) by blast
      have f3: "\<And>aa. count Zs aa = count M0 aa + count {#a#} aa"
        by (simp add: "*"(1))
      have f4: "\<And>a. count Ys a = count K a + count M0 a"
        using f2 by auto
      have f5: "count K a = 0"
        by (meson "*"(3) count_inI)
      have "Zs - M0 = {#a#}"
        using "*"(1) add_diff_cancel_left' by blast
      then have f6: "count M0 a < count Zs a"
        by (metis in_diff_count union_single_eq_member)
      have "\<And>m. count m a = 0 + count m a"
        by simp
      moreover
      { assume "aa a \<noteq> a"
        then have "mset xs = Zs \<and> count Zs (aa a) < count K (aa a) + count M0 (aa a) \<longrightarrow>
          count K (aa a) + count M0 (aa a) < count Zs (aa a)"
          using f5 f3 f2 f1 "*"(4) asym by (auto dest!: antisympD) }
      ultimately show ?thesis
        using f6 f5 f4 f1 by (metis less_imp_not_less)
    qed
  qed
  moreover
  {
    assume "count Zs a \<le> count (mset xs) a"
    with \<open>a \<notin># K\<close> have "count Ys a < count (mset xs) a" unfolding *(1,2)
      by (auto simp add: not_in_iff)
      with ** obtain z where z: "gt z a" "count (mset xs) z < count Ys z"
        by blast
      with * have "count Ys z \<le> count Zs z"
        using asym
        by (auto simp: intro: count_inI dest: antisympD)
      with z have "\<exists>z. gt z a \<and> count (mset xs) z < count Zs z" by auto
  }
  note count_a = this
  {
    fix y
    assume count_y: "count Zs y < count (mset xs) y"
    have "\<exists>x. gt x y \<and> count (mset xs) x < count Zs x"
    proof (cases "y = a")
      case True
      with count_y count_a show ?thesis by auto
    next
      case False
      show ?thesis
      proof (cases "y \<in># K")
        case True
        with *(4) have "gt a y" by simp
        then show ?thesis
          by (cases "count Zs a \<le> count (mset xs) a",
            blast dest: count_a trans[unfolded transp_def, rule_format], auto dest: count_a)
      next
        case False
        with \<open>y \<noteq> a\<close> have "count Zs y = count Ys y" unfolding *(1,2)
          by (simp add: not_in_iff)
        with count_y ** obtain z where z: "gt z y" "count (mset xs) z < count Ys z" by auto
        show ?thesis
        proof (cases "z \<in># K")
          case True
          with *(4) have "gt a z" by simp
          with z(1) show ?thesis
            by (cases "count Zs a \<le> count (mset xs) a")
              (blast dest: count_a not_le_imp_less trans[unfolded transp_def, rule_format])+
        next
          case False
          with \<open>a \<notin># K\<close> have "count Ys z \<le> count Zs z" unfolding *
            by (auto simp add: not_in_iff)
          with z show ?thesis by auto
        qed
      qed
    qed
  }
  ultimately show ?case
    unfolding msetext_huet_def Let_def by blast
qed

theorem msetext_huet_eq_dersh: "irreflp gt \<Longrightarrow> transp gt \<Longrightarrow> msetext_dersh gt = msetext_huet gt"
  using msetext_huet_imp_dersh msetext_dersh_imp_mult mult_imp_msetext_huet by fast

lemma msetext_huet_mono_strong:
  "(\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt' y x) \<Longrightarrow> msetext_huet gt ys xs \<Longrightarrow> msetext_huet gt' ys xs"
  unfolding msetext_huet_def
  by (metis less_le_trans mem_Collect_eq not_le not_less0 set_mset_mset[unfolded set_mset_def])

lemma msetext_huet_map:
  assumes
    fin: "finite A" and
    ys_a: "ys \<in> lists A" and xs_a: "xs \<in> lists A" and
    irrefl_f: "\<forall>x \<in> A. \<not> gt (f x) (f x)" and
    trans_f: "\<forall>z \<in> A. \<forall>y \<in> A. \<forall>x \<in> A. gt (f z) (f y) \<longrightarrow> gt (f y) (f x) \<longrightarrow> gt (f z) (f x)" and
    compat_f: "\<forall>y \<in> A. \<forall>x \<in> A. gt y x \<longrightarrow> gt (f y) (f x)" and
    ys_gt_xs: "msetext_huet gt ys xs"
  shows "msetext_huet gt (map f ys) (map f xs)" (is "msetext_huet _ ?fys ?fxs")
proof -
  have irrefl: "\<forall>x \<in> A. \<not> gt x x"
    using irrefl_f compat_f by blast

  have
    ms_xs_ne_ys: "mset xs \<noteq> mset ys" and
    ex_gt: "\<forall>x. count (mset ys) x < count (mset xs) x \<longrightarrow>
      (\<exists>y. gt y x \<and> count (mset xs) y < count (mset ys) y)"
    using ys_gt_xs[unfolded msetext_huet_def Let_def] by blast+

  have ex_y: "\<exists>y. gt (f y) (f x) \<and> count (mset ?fxs) (f y) < count (mset (map f ys)) (f y)"
    if cnt_x: "count (mset xs) x > count (mset ys) x" for x
  proof -
    have x_in_a: "x \<in> A"
      using cnt_x xs_a dual_order.strict_trans2 by fastforce

    obtain y where y_gt_x: "gt y x" and cnt_y: "count (mset ys) y > count (mset xs) y"
      using cnt_x ex_gt by blast
    have y_in_a: "y \<in> A"
      using cnt_y ys_a dual_order.strict_trans2 by fastforce

    have wf_gt_f: "wfP (\<lambda>y x. y \<in> A \<and> x \<in> A \<and> gt (f y) (f x))"
      by (rule finite_irreflp_transp_imp_wfp)
        (auto elim: trans_f[rule_format] simp: fin irrefl_f Collect_case_prod_Sigma irreflp_def
           transp_def)

    obtain yy where
      fyy_gt_fx: "gt (f yy) (f x)" and
      cnt_yy: "count (mset ys) yy > count (mset xs) yy" and
      max_yy: "\<forall>y \<in> A. yy \<in> A \<longrightarrow> gt (f y) (f yy) \<longrightarrow> gt (f y) (f x) \<longrightarrow>
        count (mset xs) y \<ge> count (mset ys) y"
      using wfP_eq_minimal[THEN iffD1, OF wf_gt_f, rule_format,
          of y "{y. gt (f y) (f x) \<and> count (mset xs) y < count (mset ys) y}", simplified]
        y_gt_x cnt_y
      by (metis compat_f not_less x_in_a y_in_a)
    have yy_in_a: "yy \<in> A"
      using cnt_yy ys_a dual_order.strict_trans2 by fastforce

    {
      assume "count (mset ?fxs) (f yy) \<ge> count (mset ?fys) (f yy)"
      then obtain u where fu_eq_fyy: "f u = f yy" and cnt_u: "count (mset xs) u > count (mset ys) u"
        using count_image_mset_le_imp_lt cnt_yy mset_map by (metis (mono_tags))
      have u_in_a: "u \<in> A"
        using cnt_u xs_a dual_order.strict_trans2 by fastforce

      obtain v where v_gt_u: "gt v u" and cnt_v: "count (mset ys) v > count (mset xs) v"
        using cnt_u ex_gt by blast
      have v_in_a: "v \<in> A"
        using cnt_v ys_a dual_order.strict_trans2 by fastforce

      have fv_gt_fu: "gt (f v) (f u)"
        using v_gt_u compat_f v_in_a u_in_a by blast
      hence fv_gt_fyy: "gt (f v) (f yy)"
        by (simp only: fu_eq_fyy)

      have "gt (f v) (f x)"
        using fv_gt_fyy fyy_gt_fx v_in_a yy_in_a x_in_a trans_f by blast
      hence False
        using max_yy[rule_format, of v] fv_gt_fyy v_in_a yy_in_a cnt_v by linarith
    }
    thus ?thesis
      using fyy_gt_fx leI by blast
  qed

  show ?thesis
    unfolding msetext_huet_def Let_def
  proof (intro conjI allI impI)
    {
      assume len_eq: "length xs = length ys"
      obtain x where cnt_x: "count (mset xs) x > count (mset ys) x"
        using len_eq ms_xs_ne_ys by (metis size_eq_ex_count_lt size_mset)
      hence "mset ?fxs \<noteq> mset ?fys"
        using ex_y by fastforce
    }
    thus "mset ?fxs \<noteq> mset (map f ys)"
      by (metis length_map size_mset)
  next
    fix fx
    assume cnt_fx: "count (mset ?fxs) fx > count (mset ?fys) fx"
    then obtain x where fx: "fx = f x" and cnt_x: "count (mset xs) x > count (mset ys) x"
      using count_image_mset_lt_imp_lt mset_map by (metis (mono_tags))
    thus "\<exists>fy. gt fy fx \<and> count (mset ?fxs) fy < count (mset (map f ys)) fy"
      using ex_y[OF cnt_x] by blast
  qed
qed

lemma msetext_huet_irrefl: "(\<forall>x \<in> set xs. \<not> gt x x) \<Longrightarrow> \<not> msetext_huet gt xs xs"
  unfolding msetext_huet_def by simp

lemma msetext_huet_trans_from_irrefl:
  assumes
    fin: "finite A" and
    zs_a: "zs \<in> lists A" and ys_a: "ys \<in> lists A" and xs_a: "xs \<in> lists A" and
    irrefl: "\<forall>x \<in> A. \<not> gt x x" and
    trans: "\<forall>z \<in> A. \<forall>y \<in> A. \<forall>x \<in> A. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x" and
    zs_gt_ys: "msetext_huet gt zs ys" and
    ys_gt_xs: "msetext_huet gt ys xs"
  shows "msetext_huet gt zs xs"
proof -
  have wf_gt: "wfP (\<lambda>y x. y \<in> A \<and> x \<in> A \<and> gt y x)"
    by (rule finite_irreflp_transp_imp_wfp)
      (auto elim: trans[rule_format] simp: fin irrefl Collect_case_prod_Sigma irreflp_def
         transp_def)

  show ?thesis
    unfolding msetext_huet_def Let_def
  proof (intro conjI allI impI)
    obtain x where cnt_x: "count (mset zs) x > count (mset ys) x"
      using msetext_huet_imp_count_gt[OF zs_gt_ys] by blast
    have x_in_a: "x \<in> A"
      using cnt_x zs_a dual_order.strict_trans2 by fastforce

    obtain xx where
      cnt_xx: "count (mset zs) xx > count (mset ys) xx" and
      max_xx: "\<forall>y \<in> A. xx \<in> A \<longrightarrow> gt y xx \<longrightarrow> count (mset ys) y \<ge> count (mset zs) y"
      using wfP_eq_minimal[THEN iffD1, OF wf_gt, rule_format,
          of x "{y. count (mset ys) y < count (mset zs) y}", simplified]
        cnt_x
      by force
    have xx_in_a: "xx \<in> A"
      using cnt_xx zs_a dual_order.strict_trans2 by fastforce

    show "mset xs \<noteq> mset zs"
    proof (cases "count (mset ys) xx \<ge> count (mset xs) xx")
      case True
      thus ?thesis
        using cnt_xx by fastforce
    next
      case False
      hence "count (mset ys) xx < count (mset xs) xx"
        by fastforce
      then obtain z where z_gt_xx: "gt z xx" and cnt_z: "count (mset ys) z > count (mset xs) z"
        using ys_gt_xs[unfolded msetext_huet_def Let_def] by blast
      have z_in_a: "z \<in> A"
        using cnt_z ys_a dual_order.strict_trans2 by fastforce

      have "count (mset zs) z \<le> count (mset ys) z"
        using max_xx[rule_format, of z] z_in_a xx_in_a z_gt_xx by blast
      moreover
      {
        assume "count (mset zs) z < count (mset ys) z"
        then obtain u where u_gt_z: "gt u z" and cnt_u: "count (mset ys) u < count (mset zs) u"
          using zs_gt_ys[unfolded msetext_huet_def Let_def] by blast
        have u_in_a: "u \<in> A"
          using cnt_u zs_a dual_order.strict_trans2 by fastforce
        have u_gt_xx: "gt u xx"
          using trans u_in_a z_in_a xx_in_a u_gt_z z_gt_xx by blast
        have False
          using max_xx[rule_format, of u] u_in_a xx_in_a u_gt_xx cnt_u by fastforce
      }
      ultimately have "count (mset zs) z = count (mset ys) z"
        by fastforce
      thus ?thesis
        using cnt_z by fastforce
    qed
  next
    fix x
    assume cnt_x_xz: "count (mset zs) x < count (mset xs) x"
    have x_in_a: "x \<in> A"
      using cnt_x_xz xs_a dual_order.strict_trans2 by fastforce

    let ?case = "\<exists>y. gt y x \<and> count (mset zs) y > count (mset xs) y"

    {
      assume cnt_x: "count (mset zs) x < count (mset ys) x"
      then obtain y where y_gt_x: "gt y x" and cnt_y: "count (mset zs) y > count (mset ys) y"
        using zs_gt_ys[unfolded msetext_huet_def Let_def] by blast
      have y_in_a: "y \<in> A"
        using cnt_y zs_a dual_order.strict_trans2 by fastforce

      obtain yy where
        yy_gt_x: "gt yy x" and
        cnt_yy: "count (mset zs) yy > count (mset ys) yy" and
        max_yy: "\<forall>y \<in> A. yy \<in> A \<longrightarrow> gt y yy \<longrightarrow> gt y x \<longrightarrow> count (mset ys) y \<ge> count (mset zs) y"
        using wfP_eq_minimal[THEN iffD1, OF wf_gt, rule_format,
            of y "{y. gt y x \<and> count (mset ys) y < count (mset zs) y}", simplified]
          y_gt_x cnt_y
        by force
      have yy_in_a: "yy \<in> A"
        using cnt_yy zs_a dual_order.strict_trans2 by fastforce

      have ?case
      proof (cases "count (mset ys) yy \<ge> count (mset xs) yy")
        case True
        thus ?thesis
          using yy_gt_x cnt_yy by fastforce
      next
        case False
        hence "count (mset ys) yy < count (mset xs) yy"
          by fastforce
        then obtain z where z_gt_yy: "gt z yy" and cnt_z: "count (mset ys) z > count (mset xs) z"
          using ys_gt_xs[unfolded msetext_huet_def Let_def] by blast
        have z_in_a: "z \<in> A"
          using cnt_z ys_a dual_order.strict_trans2 by fastforce
        have z_gt_x: "gt z x"
          using trans z_in_a yy_in_a x_in_a z_gt_yy yy_gt_x by blast

        have "count (mset zs) z \<le> count (mset ys) z"
          using max_yy[rule_format, of z] z_in_a yy_in_a z_gt_yy z_gt_x by blast
        moreover
        {
          assume "count (mset zs) z < count (mset ys) z"
          then obtain u where u_gt_z: "gt u z" and cnt_u: "count (mset ys) u < count (mset zs) u"
            using zs_gt_ys[unfolded msetext_huet_def Let_def] by blast
          have u_in_a: "u \<in> A"
            using cnt_u zs_a dual_order.strict_trans2 by fastforce
          have u_gt_yy: "gt u yy"
            using trans u_in_a z_in_a yy_in_a u_gt_z z_gt_yy by blast
          have u_gt_x: "gt u x"
            using trans u_in_a z_in_a x_in_a u_gt_z z_gt_x by blast
          have False
            using max_yy[rule_format, of u] u_in_a yy_in_a u_gt_yy u_gt_x cnt_u by fastforce
        }
        ultimately have "count (mset zs) z = count (mset ys) z"
          by fastforce
        thus ?thesis
          using z_gt_x cnt_z by fastforce
      qed
    }
    moreover
    {
      assume "count (mset zs) x \<ge> count (mset ys) x"
      hence "count (mset ys) x < count (mset xs) x"
        using cnt_x_xz by fastforce
      then obtain y where y_gt_x: "gt y x" and cnt_y: "count (mset ys) y > count (mset xs) y"
        using ys_gt_xs[unfolded msetext_huet_def Let_def] by blast
      have y_in_a: "y \<in> A"
        using cnt_y ys_a dual_order.strict_trans2 by fastforce

      obtain yy where
        yy_gt_x: "gt yy x" and
        cnt_yy: "count (mset ys) yy > count (mset xs) yy" and
        max_yy: "\<forall>y \<in> A. yy \<in> A \<longrightarrow> gt y yy \<longrightarrow> gt y x \<longrightarrow> count (mset xs) y \<ge> count (mset ys) y"
        using wfP_eq_minimal[THEN iffD1, OF wf_gt, rule_format,
            of y "{y. gt y x \<and> count (mset xs) y < count (mset ys) y}", simplified]
          y_gt_x cnt_y
        by force
      have yy_in_a: "yy \<in> A"
        using cnt_yy ys_a dual_order.strict_trans2 by fastforce

      have ?case
      proof (cases "count (mset zs) yy \<ge> count (mset ys) yy")
        case True
        thus ?thesis
          using yy_gt_x cnt_yy by fastforce
      next
        case False
        hence "count (mset zs) yy < count (mset ys) yy"
          by fastforce
        then obtain z where z_gt_yy: "gt z yy" and cnt_z: "count (mset zs) z > count (mset ys) z"
          using zs_gt_ys[unfolded msetext_huet_def Let_def] by blast
        have z_in_a: "z \<in> A"
          using cnt_z zs_a dual_order.strict_trans2 by fastforce
        have z_gt_x: "gt z x"
          using trans z_in_a yy_in_a x_in_a z_gt_yy yy_gt_x by blast

        have "count (mset ys) z \<le> count (mset xs) z"
          using max_yy[rule_format, of z] z_in_a yy_in_a z_gt_yy z_gt_x by blast
        moreover
        {
          assume "count (mset ys) z < count (mset xs) z"
          then obtain u where u_gt_z: "gt u z" and cnt_u: "count (mset xs) u < count (mset ys) u"
            using ys_gt_xs[unfolded msetext_huet_def Let_def] by blast
          have u_in_a: "u \<in> A"
            using cnt_u ys_a dual_order.strict_trans2 by fastforce
          have u_gt_yy: "gt u yy"
            using trans u_in_a z_in_a yy_in_a u_gt_z z_gt_yy by blast
          have u_gt_x: "gt u x"
            using trans u_in_a z_in_a x_in_a u_gt_z z_gt_x by blast
          have False
            using max_yy[rule_format, of u] u_in_a yy_in_a u_gt_yy u_gt_x cnt_u by fastforce
        }
        ultimately have "count (mset ys) z = count (mset xs) z"
          by fastforce
        thus ?thesis
          using z_gt_x cnt_z by fastforce
      qed
    }
    ultimately show "\<exists>y. gt y x \<and> count (mset xs) y < count (mset zs) y"
      by fastforce
  qed
qed

lemma msetext_huet_snoc: "msetext_huet gt (xs @ [x]) xs"
  unfolding msetext_huet_def Let_def by simp

lemma msetext_huet_compat_cons: "msetext_huet gt ys xs \<Longrightarrow> msetext_huet gt (x # ys) (x # xs)"
  unfolding msetext_huet_def Let_def by auto

lemma msetext_huet_compat_snoc: "msetext_huet gt ys xs \<Longrightarrow> msetext_huet gt (ys @ [x]) (xs @ [x])"
  unfolding msetext_huet_def Let_def by auto

lemma msetext_huet_compat_list: "y \<noteq> x \<Longrightarrow> gt y x \<Longrightarrow> msetext_huet gt (xs @ y # xs') (xs @ x # xs')"
  unfolding msetext_huet_def Let_def by auto

lemma msetext_huet_singleton: "y \<noteq> x \<Longrightarrow> msetext_huet gt [y] [x] \<longleftrightarrow> gt y x"
  unfolding msetext_huet_def by simp

lemma msetext_huet_wf: "wfP (\<lambda>x y. gt y x) \<Longrightarrow> wfP (\<lambda>xs ys. msetext_huet gt ys xs)"
  by (erule wfP_subset[OF msetext_dersh_wf]) (auto intro: msetext_huet_imp_dersh)

lemma msetext_huet_hd_or_tl:
  assumes
    trans: "\<forall>z y x. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x" and
    total: "\<forall>y x. gt y x \<or> gt x y \<or> y = x" and
    len_eq: "length ys = length xs" and
    yys_gt_xxs: "msetext_huet gt (y # ys) (x # xs)"
  shows "gt y x \<or> msetext_huet gt ys xs"
proof -
  let ?Y = "mset (y # ys)"
  let ?X = "mset (x # xs)"

  let ?Ya = "mset ys"
  let ?Xa = "mset xs"

  have Y_ne_X: "?Y \<noteq> ?X" and
    ex_gt_Y: "\<And>xa. count ?X xa > count ?Y xa \<Longrightarrow> \<exists>ya. gt ya xa \<and> count ?Y ya > count ?X ya"
    using yys_gt_xxs[unfolded msetext_huet_def Let_def] by auto
  obtain yy where
    yy: "\<And>xa. count ?X xa > count ?Y xa \<Longrightarrow> gt (yy xa) xa \<and> count ?Y (yy xa) > count ?X (yy xa)"
    using ex_gt_Y by metis

  have cnt_Y_pres: "count ?Ya xa > count ?Xa xa" if "count ?Y xa > count ?X xa" and "xa \<noteq> y" for xa
    using that by (auto split: if_splits)
  have cnt_X_pres: "count ?Xa xa > count ?Ya xa" if "count ?X xa > count ?Y xa" and "xa \<noteq> x" for xa
    using that by (auto split: if_splits)

  {
    assume y_eq_x: "y = x"
    have "?Xa \<noteq> ?Ya"
      using y_eq_x Y_ne_X by simp
    moreover have "\<And>xa. count ?Xa xa > count ?Ya xa \<Longrightarrow> \<exists>ya. gt ya xa \<and> count ?Ya ya > count ?Xa ya"
    proof -
      fix xa :: 'a
      assume a1: "count (mset ys) xa < count (mset xs) xa"
      from ex_gt_Y obtain aa :: "'a \<Rightarrow> 'a" where
        f3: "\<forall>a. \<not> count (mset (y # ys)) a < count (mset (x # xs)) a \<or> gt (aa a) a \<and>
          count (mset (x # xs)) (aa a) < count (mset (y # ys)) (aa a)"
        by (metis (full_types))
      then have f4: "\<And>a. count (mset (x # xs)) (aa a) < count (mset (x # ys)) (aa a) \<or>
          \<not> count (mset (x # ys)) a < count (mset (x # xs)) a"
        using y_eq_x by meson
      have "\<And>a as aa. count (mset ((a::'a) # as)) aa = count (mset as) aa \<or> aa = a"
        by fastforce
      then have "xa = x \<or> count (mset (x # xs)) (aa xa) < count (mset (x # ys)) (aa xa)"
        using f4 a1 by (metis (no_types))
      then show "\<exists>a. gt a xa \<and> count (mset xs) a < count (mset ys) a"
        using f3 y_eq_x a1 by (metis (no_types) Suc_less_eq count_add_mset mset.simps(2))
    qed
    ultimately have "msetext_huet gt ys xs"
      unfolding msetext_huet_def Let_def by simp
  }
  moreover
  {
    assume x_gt_y: "gt x y" and y_ngt_x: "\<not> gt y x"
    hence y_ne_x: "y \<noteq> x"
      by fast

    obtain z where z_cnt: "count ?X z > count ?Y z"
      using size_eq_ex_count_lt[of ?Y ?X] size_mset size_mset len_eq Y_ne_X by auto

    have Xa_ne_Ya: "?Xa \<noteq> ?Ya"
    proof (cases "z = x")
      case True
      hence "yy z \<noteq> y"
        using y_ngt_x yy z_cnt by blast
      hence "count ?Ya (yy z) > count ?Xa (yy z)"
        using cnt_Y_pres yy z_cnt by blast
      thus ?thesis
        by auto
    next
      case False
      hence "count ?Xa z > count ?Ya z"
        using z_cnt cnt_X_pres by blast
      thus ?thesis
        by auto
    qed

    have "\<exists>ya. gt ya xa \<and> count ?Ya ya > count ?Xa ya"
      if xa_cnta: "count ?Xa xa > count ?Ya xa" for xa
    proof (cases "xa = y")
      case xa_eq_y: True

      {
        assume "count ?Ya x > count ?Xa x"
        moreover have "gt x xa"
          unfolding xa_eq_y by (rule x_gt_y)
        ultimately have ?thesis
          by fast
      }
      moreover
      {
        assume "count ?Xa x \<ge> count ?Ya x"
        hence x_cnt: "count ?X x > count ?Y x"
          by (simp add: y_ne_x)
        hence yyx_gt_x: "gt (yy x) x" and yyx_cnt: "count ?Y (yy x) > count ?X (yy x)"
          using yy by blast+

        have yyx_ne_y: "yy x \<noteq> y"
          using y_ngt_x yyx_gt_x by auto

        have "gt (yy x) xa"
          unfolding xa_eq_y using trans yyx_gt_x x_gt_y by blast
        moreover have "count ?Ya (yy x) > count ?Xa (yy x)"
          using cnt_Y_pres yyx_cnt yyx_ne_y by blast
        ultimately have ?thesis
          by blast
      }
      ultimately show ?thesis
        by fastforce
    next
      case False
      hence xa_cnt: "count ?X xa > count ?Y xa"
        using xa_cnta by fastforce

      show ?thesis
      proof (cases "yy xa = y \<and> count ?Ya y \<le> count ?Xa y")
        case yyxa_ne_y_or: False

        have yyxa_gt_xa: "gt (yy xa) xa" and yyxa_cnt: "count ?Y (yy xa) > count ?X (yy xa)"
          using yy[OF xa_cnt] by blast+

        have "count ?Ya (yy xa) > count ?Xa (yy xa)"
          using cnt_Y_pres yyxa_cnt yyxa_ne_y_or by fastforce
        thus ?thesis
          using yyxa_gt_xa by blast
      next
        case True
        note yyxa_eq_y = this[THEN conjunct1] and y_cnt = this[THEN conjunct2]

        {
          assume "count ?Ya x > count ?Xa x"
          moreover have "gt x xa"
            using trans x_gt_y xa_cnt yy yyxa_eq_y by blast
          ultimately have ?thesis
            by fast
        }
        moreover
        {
          assume "count ?Xa x \<ge> count ?Ya x"
          hence x_cnt: "count ?X x > count ?Y x"
            by (simp add: y_ne_x)
          hence yyx_gt_x: "gt (yy x) x" and yyx_cnt: "count ?Y (yy x) > count ?X (yy x)"
            using yy by blast+

          have yyx_ne_y: "yy x \<noteq> y"
            using y_ngt_x yyx_gt_x by auto

          have "gt (yy x) xa"
            using trans x_gt_y xa_cnt yy yyx_gt_x yyxa_eq_y by blast
          moreover have "count ?Ya (yy x) > count ?Xa (yy x)"
            using cnt_Y_pres yyx_cnt yyx_ne_y by blast
          ultimately have ?thesis
            by blast
        }
        ultimately show ?thesis
          by fastforce
      qed
    qed
    hence "msetext_huet gt ys xs"
      unfolding msetext_huet_def Let_def using Xa_ne_Ya by fast
  }
  ultimately show ?thesis
    using total by blast
qed

interpretation msetext_huet: ext msetext_huet
  by standard (fact msetext_huet_mono_strong, fact msetext_huet_map)

interpretation msetext_huet: ext_irrefl_before_trans msetext_huet
  by standard (fact msetext_huet_irrefl, fact msetext_huet_trans_from_irrefl)

interpretation msetext_huet: ext_snoc msetext_huet
  by standard (fact msetext_huet_snoc)

interpretation msetext_huet: ext_compat_cons msetext_huet
  by standard (fact msetext_huet_compat_cons)

interpretation msetext_huet: ext_compat_snoc msetext_huet
  by standard (fact msetext_huet_compat_snoc)

interpretation msetext_huet: ext_compat_list msetext_huet
  by standard (fact msetext_huet_compat_list)

interpretation msetext_huet: ext_singleton msetext_huet
  by standard (fact msetext_huet_singleton)

interpretation msetext_huet: ext_wf msetext_huet
  by standard (fact msetext_huet_wf)

interpretation msetext_huet: ext_hd_or_tl msetext_huet
  by standard (rule msetext_huet_hd_or_tl)

interpretation msetext_huet: ext_wf_bounded msetext_huet
  by standard


subsection \<open>Componentwise Extension\<close>

definition cwiseext :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "cwiseext gt ys xs \<longleftrightarrow> length ys = length xs
     \<and> (\<forall>i < length ys. gt (ys ! i) (xs ! i) \<or> ys ! i = xs ! i)
     \<and> (\<exists>i < length ys. gt (ys ! i) (xs ! i))"

lemma cwiseext_imp_len_lexext:
  assumes cw: "cwiseext gt ys xs"
  shows "len_lexext gt ys xs"
proof -
  have len_eq: "length ys = length xs"
    using cw[unfolded cwiseext_def] by sat
  moreover have "lexext gt ys xs"
  proof -
    obtain j where
      j_len: "j < length ys" and
      j_gt: "gt (ys ! j) (xs ! j)"
      using cw[unfolded cwiseext_def] by blast
    then obtain j0 where
      j0_len: "j0 < length ys" and
      j0_gt: "gt (ys ! j0) (xs ! j0)" and
      j0_min: "\<And>i. i < j0 \<Longrightarrow> \<not> gt (ys ! i) (xs ! i)"
      using wf_eq_minimal[THEN iffD1, OF wf_less, rule_format, of _ "{i. gt (ys ! i) (xs ! i)}",
        simplified, OF j_gt]
      by (metis less_trans nat_neq_iff)

    have j0_eq: "\<And>i. i < j0 \<Longrightarrow> ys ! i = xs ! i"
      using cw[unfolded cwiseext_def] by (metis j0_len j0_min less_trans)

    have "lexext gt (drop j0 ys) (drop j0 xs)"
      using lexext_Cons[of gt _ _ "drop (Suc j0) ys" "drop (Suc j0) xs", OF j0_gt]
      by (metis Cons_nth_drop_Suc j0_len len_eq)
    thus ?thesis
      using cw len_eq j0_len j0_min
    proof (induct j0 arbitrary: ys xs)
      case (Suc k)
      note ih0 = this(1) and gts_dropSk = this(2) and cw = this(3) and len_eq = this(4) and
        Sk_len = this(5) and Sk_min = this(6)

      have Sk_eq: "\<And>i. i < Suc k \<Longrightarrow> ys ! i = xs ! i"
        using cw[unfolded cwiseext_def] by (metis Sk_len Sk_min less_trans)

      have k_len: "k < length ys"
        using Sk_len by simp
      have k_min: "\<And>i. i < k \<Longrightarrow> \<not> gt (ys ! i) (xs ! i)"
        using Sk_min by simp

      have k_eq: "\<And>i. i < k \<Longrightarrow> ys ! i = xs ! i"
        using Sk_eq by simp

      note ih = ih0[OF _ cw len_eq k_len k_min]

      show ?case
      proof (cases "k < length ys")
        case k_lt_ys: True
        note k_lt_xs = k_lt_ys[unfolded len_eq]

        obtain x where x: "x = xs ! k"
          by simp
        hence y: "x = ys ! k"
          using Sk_eq[of k] by simp

        have dropk_xs: "drop k xs = x # drop (Suc k) xs"
          using k_lt_xs x by (simp add: Cons_nth_drop_Suc)
        have dropk_ys: "drop k ys = x # drop (Suc k) ys"
          using k_lt_ys y by (simp add: Cons_nth_drop_Suc)

        show ?thesis
          by (rule ih, unfold dropk_xs dropk_ys, rule lexext_Cons_eq[OF gts_dropSk])
      next
        case False
        hence "drop k xs = []" and "drop k ys = []"
          using len_eq by simp_all
        hence "lexext gt [] []"
          using gts_dropSk by simp
        hence "lexext gt (drop k ys) (drop k xs)"
          by simp
        thus ?thesis
          by (rule ih)
      qed
    qed simp
  qed
  ultimately show ?thesis
    unfolding lenext_def by sat
qed

lemma cwiseext_mono_strong:
  "(\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt' y x) \<Longrightarrow> cwiseext gt ys xs \<Longrightarrow> cwiseext gt' ys xs"
  unfolding cwiseext_def by (induct, force, fast)

lemma cwiseext_map_strong:
  "(\<forall>y \<in> set ys. \<forall>x \<in> set xs. gt y x \<longrightarrow> gt (f y) (f x)) \<Longrightarrow> cwiseext gt ys xs \<Longrightarrow>
   cwiseext gt (map f ys) (map f xs)"
  unfolding cwiseext_def by auto

lemma cwiseext_irrefl: "(\<forall>x \<in> set xs. \<not> gt x x) \<Longrightarrow> \<not> cwiseext gt xs xs"
  unfolding cwiseext_def by (blast intro: nth_mem)

lemma cwiseext_trans_strong:
  assumes
    "\<forall>z \<in> set zs. \<forall>y \<in> set ys. \<forall>x \<in> set xs. gt z y \<longrightarrow> gt y x \<longrightarrow> gt z x" and
    "cwiseext gt zs ys" and "cwiseext gt ys xs"
  shows "cwiseext gt zs xs"
  using assms unfolding cwiseext_def by (metis (mono_tags) nth_mem)

lemma cwiseext_compat_cons: "cwiseext gt ys xs \<Longrightarrow> cwiseext gt (x # ys) (x # xs)"
  unfolding cwiseext_def
proof (elim conjE, intro conjI)
  assume
    "length ys = length xs" and
    "\<forall>i < length ys. gt (ys ! i) (xs ! i) \<or> ys ! i = xs ! i"
  thus "\<forall>i < length (x # ys). gt ((x # ys) ! i) ((x # xs) ! i) \<or> (x # ys) ! i = (x # xs) ! i"
    by (simp add: nth_Cons')
next
  assume "\<exists>i < length ys. gt (ys ! i) (xs ! i)"
  thus "\<exists>i < length (x # ys). gt ((x # ys) ! i) ((x # xs) ! i)"
    by fastforce
qed auto

lemma cwiseext_compat_snoc: "cwiseext gt ys xs \<Longrightarrow> cwiseext gt (ys @ [x]) (xs @ [x])"
  unfolding cwiseext_def
proof (elim conjE, intro conjI)
  assume
    "length ys = length xs" and
    "\<forall>i < length ys. gt (ys ! i) (xs ! i) \<or> ys ! i = xs ! i"
  thus "\<forall>i < length (ys @ [x]).
    gt ((ys @ [x]) ! i) ((xs @ [x]) ! i) \<or> (ys @ [x]) ! i = (xs @ [x]) ! i"
    by (simp add: nth_append)
next
  assume
    "length ys = length xs" and
    "\<exists>i < length ys. gt (ys ! i) (xs ! i)"
  thus "\<exists>i < length (ys @ [x]). gt ((ys @ [x]) ! i) ((xs @ [x]) ! i)"
    by (metis length_append_singleton less_Suc_eq nth_append)
qed auto

lemma cwiseext_compat_list:
  assumes y_gt_x: "gt y x"
  shows "cwiseext gt (xs @ y # xs') (xs @ x # xs')"
  unfolding cwiseext_def
proof (intro conjI)
  show "\<forall>i < length (xs @ y # xs'). gt ((xs @ y # xs') ! i) ((xs @ x # xs') ! i)
    \<or> (xs @ y # xs') ! i = (xs @ x # xs') ! i"
    using y_gt_x by (simp add: nth_Cons' nth_append)
next
  show "\<exists>i < length (xs @ y # xs'). gt ((xs @ y # xs') ! i) ((xs @ x # xs') ! i)"
    using y_gt_x by (metis add_diff_cancel_right' append_is_Nil_conv diff_less length_append
      length_greater_0_conv list.simps(3) nth_append_length)
qed auto

lemma cwiseext_singleton: "cwiseext gt [y] [x] \<longleftrightarrow> gt y x"
  unfolding cwiseext_def by auto

lemma cwiseext_wf: "wfP (\<lambda>x y. gt y x) \<Longrightarrow> wfP (\<lambda>xs ys. cwiseext gt ys xs)"
  by (auto intro: cwiseext_imp_len_lexext wfP_subset[OF len_lexext_wf])

lemma cwiseext_hd_or_tl: "cwiseext gt (y # ys) (x # xs) \<Longrightarrow> gt y x \<or> cwiseext gt ys xs"
  unfolding cwiseext_def
proof (elim conjE, intro disj_imp[THEN iffD2, rule_format] conjI)
  assume
    "\<exists>i < length (y # ys). gt ((y # ys) ! i) ((x # xs) ! i)" and
    "\<not> gt y x"
  thus "\<exists>i < length ys. gt (ys ! i) (xs ! i)"
    by (metis (no_types) One_nat_def diff_le_self diff_less dual_order.strict_trans2
      length_Cons less_Suc_eq linorder_neqE_nat not_less0 nth_Cons')
qed auto

locale ext_cwiseext = ext_compat_list + ext_compat_cons
begin

context
  fixes gt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    gt_irrefl: "\<not> gt x x" and
    trans_gt: "ext gt zs ys \<Longrightarrow> ext gt ys xs \<Longrightarrow> ext gt zs xs"
begin

lemma
  assumes ys_gtcw_xs: "cwiseext gt ys xs"
  shows "ext gt ys xs"
proof -
  have "length ys = length xs"
    by (rule ys_gtcw_xs[unfolded cwiseext_def, THEN conjunct1])
  thus ?thesis
    using ys_gtcw_xs
  proof (induct rule: list_induct2)
    case Nil
    thus ?case
      unfolding cwiseext_def by simp
  next
    case (Cons y ys x xs)
    note len_ys_eq_xs = this(1) and ih = this(2) and yys_gtcw_xxs = this(3)

    have xys_gts_xxs: "ext gt (x # ys) (x # xs)" if ys_ne_xs: "ys \<noteq> xs"
    proof -
      have ys_gtcw_xs: "cwiseext gt ys xs"
        using yys_gtcw_xxs unfolding cwiseext_def
      proof (elim conjE, intro conjI)
        assume
          "\<forall>i < length (y # ys). gt ((y # ys) ! i) ((x # xs) ! i) \<or> (y # ys) ! i = (x # xs) ! i"
        hence ge: "\<forall>i < length ys. gt (ys ! i) (xs ! i) \<or> ys ! i = xs ! i"
          by auto
        thus "\<exists>i < length ys. gt (ys ! i) (xs ! i)"
          using ys_ne_xs len_ys_eq_xs nth_equalityI by blast
      qed auto
      hence "ext gt ys xs"
        by (rule ih)
      thus "ext gt (x # ys) (x # xs)"
        by (rule compat_cons)
    qed

    have "gt y x \<or> y = x"
      using yys_gtcw_xxs unfolding cwiseext_def by fastforce
    moreover
    {
      assume y_eq_x: "y = x"
      have ?case
      proof (cases "ys = xs")
        case True
        hence False
          using y_eq_x gt_irrefl yys_gtcw_xxs unfolding cwiseext_def by presburger
        thus ?thesis
          by sat
      next
        case False
        thus ?thesis
          using y_eq_x xys_gts_xxs by simp
      qed
    }
    moreover
    {
      assume "y \<noteq> x" and "gt y x"
      hence yys_gts_xys: "ext gt (y # ys) (x # ys)"
        using compat_list[of _ _ gt "[]"] by simp

      have ?case
      proof (cases "ys = xs")
        case ys_eq_xs: True
        thus ?thesis
          using yys_gts_xys by simp
      next
        case False
        thus ?thesis
          using yys_gts_xys xys_gts_xxs trans_gt by blast
      qed
    }
    ultimately show ?case
      by sat
  qed
qed

end

end

interpretation cwiseext: ext cwiseext
  by standard (fact cwiseext_mono_strong, rule cwiseext_map_strong, metis in_listsD)

interpretation cwiseext: ext_irrefl_trans_strong cwiseext
  by standard (fact cwiseext_irrefl, fact cwiseext_trans_strong)

interpretation cwiseext: ext_compat_cons cwiseext
  by standard (fact cwiseext_compat_cons)

interpretation cwiseext: ext_compat_snoc cwiseext
  by standard (fact cwiseext_compat_snoc)

interpretation cwiseext: ext_compat_list cwiseext
  by standard (rule cwiseext_compat_list)

interpretation cwiseext: ext_singleton cwiseext
  by standard (rule cwiseext_singleton)

interpretation cwiseext: ext_wf cwiseext
  by standard (rule cwiseext_wf)

interpretation cwiseext: ext_hd_or_tl cwiseext
  by standard (rule cwiseext_hd_or_tl)

interpretation cwiseext: ext_wf_bounded cwiseext
  by standard

end
