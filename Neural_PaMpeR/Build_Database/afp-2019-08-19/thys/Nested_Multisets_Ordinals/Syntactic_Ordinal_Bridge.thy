(*  Title:       Syntactic Ordinals in Cantor Normal Form
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2017
*)

theory Syntactic_Ordinal_Bridge
imports "HOL-Library.Sublist" Ordinal.OrdinalOmega Syntactic_Ordinal
abbrevs
  "!h" = "\<^sub>h"
begin


section \<open>Bridge between Huffman's Ordinal Library and the Syntactic Ordinals\<close>

subsection \<open>Missing Lemmas about Huffman's Ordinals\<close>

instantiation ordinal :: order_bot
begin

definition bot_ordinal :: ordinal where
  "bot_ordinal = 0"

instance
  by intro_classes (simp add: bot_ordinal_def)

end

lemma insort_bot[simp]: "insort bot xs = bot # xs" for xs :: "'a::{order_bot,linorder} list"
  by (simp add: insort_is_Cons)

lemmas insort_0_ordinal[simp] = insort_bot[of "xs :: ordinal list" for xs, unfolded bot_ordinal_def]

lemma from_cnf_less_\<omega>_exp:
  assumes "\<forall>k \<in> set ks. k < l"
  shows "from_cnf ks < \<omega> ** l"
  using assms by (induct ks) (auto simp: additive_principal.sum_less additive_principal_omega_exp)

lemma from_cnf_0_iff[simp]: "from_cnf ks = 0 \<longleftrightarrow> ks = []"
  by (induct ks) (auto simp: ordinal_plus_not_0)

lemma from_cnf_append[simp]: "from_cnf (ks @ ls) = from_cnf ks + from_cnf ls"
  by (induct ks) (auto simp: ordinal_plus_assoc)

lemma subseq_from_cnf_less_eq: "Sublist.subseq ks ls \<Longrightarrow> from_cnf ks \<le> from_cnf ls"
  by (induct rule: list_emb.induct) (auto intro: ordinal_le_plusL order_trans)


subsection \<open>Embedding of Syntactic Ordinals into Huffman's Ordinals\<close>

abbreviation \<omega>\<^sub>h :: hmultiset where
  "\<omega>\<^sub>h \<equiv> Syntactic_Ordinal.\<omega>"

abbreviation \<omega>\<^sub>h_exp :: "hmultiset \<Rightarrow> hmultiset" ("\<omega>\<^sub>h^") where
  "\<omega>\<^sub>h^ \<equiv> Syntactic_Ordinal.\<omega>_exp"

primrec ordinal_of_hmset :: "hmultiset \<Rightarrow> ordinal" where
  "ordinal_of_hmset (HMSet M) =
   from_cnf (rev (sorted_list_of_multiset (image_mset ordinal_of_hmset M)))"

lemma ordinal_of_hmset_0[simp]: "ordinal_of_hmset 0 = 0"
  unfolding zero_hmultiset_def by simp

lemma ordinal_of_hmset_suc[simp]: "ordinal_of_hmset (k + 1) = ordinal_of_hmset k + 1"
  unfolding plus_hmultiset_def one_hmultiset_def by (cases k) simp

lemma ordinal_of_hmset_1[simp]: "ordinal_of_hmset 1 = 1"
  using ordinal_of_hmset_suc[of 0] by simp

lemma ordinal_of_hmset_\<omega>[simp]: "ordinal_of_hmset \<omega>\<^sub>h = \<omega>"
  by simp

lemma ordinal_of_hmset_singleton[simp]: "ordinal_of_hmset (\<omega>^k) = \<omega> ** ordinal_of_hmset k"
  by simp

lemma ordinal_of_hmset_iff[simp]: "ordinal_of_hmset k = 0 \<longleftrightarrow> k = 0"
  by (induct k) auto

lemma less_imp_ordinal_of_hmset_less: "k < l \<Longrightarrow> ordinal_of_hmset k < ordinal_of_hmset l"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(k, l). {#k, l#}"
        "\<lambda>(k, l). k < l \<longrightarrow> ordinal_of_hmset k < ordinal_of_hmset l" "(k, l)",
      simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix k l
  assume
    ih: "\<And>ka la. {#ka, la#} < {#k, l#} \<Longrightarrow> ka < la \<Longrightarrow> ordinal_of_hmset ka < ordinal_of_hmset la" and
    k_lt_l: "k < l"

  show "ordinal_of_hmset k < ordinal_of_hmset l"
  proof (cases "k = 0")
    case True
    thus ?thesis
      using k_lt_l ordinal_neq_0 by fastforce
  next
    case k_nz: False

    have l_nz: "l \<noteq> 0"
      using k_lt_l by auto

    define K where K: "K = hmsetmset k"
    define L where L: "L = hmsetmset l"

    have k: "k = HMSet K" and l: "l = HMSet L"
      by (simp_all add: K L)

    have K_lt_L: "K < L"
      unfolding K L using k_lt_l by simp

    define x where x: "x = Max_mset K"
    define Ka where Ka: "Ka = K - {#x#}"

    have k_eq_xKa: "k = HMSet (add_mset x Ka)"
      using K x Ka k_nz by auto
    have x_max: "\<forall>a \<in># Ka. a \<le> x"
      unfolding x Ka by (meson Max_ge finite_set_mset in_diffD)

    have ord_x_max: "\<forall>a \<in># Ka. ordinal_of_hmset a \<le> ordinal_of_hmset x"
    proof
      fix a
      assume a_in: "a \<in># Ka"

      have a_le_x: "a \<le> x"
        by (simp add: x_max a_in)
      moreover
      {
        assume a_lt_x: "a < x"
        moreover have x_lt_k: "x < k"
          unfolding k_eq_xKa by (rule mem_imp_less_HMSet) simp
        ultimately have a_lt_k: "a < k"
          by simp

        have "{#a, x#} < {#k#}"
          using x_lt_k a_lt_k by simp
        also have "\<dots> < {#k, l#}"
          unfolding k_eq_xKa using a_in
          by simp
        finally have "ordinal_of_hmset a < ordinal_of_hmset x"
          by (rule ih[OF _ a_lt_x])
      }
      ultimately show "ordinal_of_hmset a \<le> ordinal_of_hmset x"
        by force
    qed

    define y where y: "y = Max_mset L"
    define La where La: "La = L - {#y#}"

    have l_eq_yLa: "l = HMSet (add_mset y La)"
      using L y La l_nz by auto
    have y_max: "\<forall>b \<in># La. b \<le> y"
      unfolding y La by (meson Max_ge finite_set_mset in_diffD)

    have ord_y_max: "\<forall>b \<in># La. ordinal_of_hmset b \<le> ordinal_of_hmset y"
    proof
      fix b
      assume b_in: "b \<in># La"

      have b_le_y: "b \<le> y"
        by (simp add: y_max b_in)
      moreover
      {
        assume b_lt_y: "b < y"
        moreover have y_lt_l: "y < l"
          unfolding l_eq_yLa by (rule mem_imp_less_HMSet) simp
        ultimately have b_lt_l: "b < l"
          by simp

        have "{#b, y#} < {#l#}"
          using y_lt_l b_lt_l by simp
        also have "\<dots> < {#k, l#}"
          unfolding l_eq_yLa using b_in
          by simp
        finally have "ordinal_of_hmset b < ordinal_of_hmset y"
          by (rule ih[OF _ b_lt_y])
      }
      ultimately show "ordinal_of_hmset b \<le> ordinal_of_hmset y"
        by force
    qed

    {
      assume x_eq_y: "x = y"

      have "ordinal_of_hmset (HMSet Ka) < ordinal_of_hmset (HMSet La)"
      proof (rule ih)
        show "{#HMSet Ka, HMSet La#} < {#k, l#}"
          unfolding k l
          by (metis add_mset_add_single hmsetmset_less hmultiset.sel k k_eq_xKa l l_eq_yLa
            le_multiset_right_total mset_lt_single_iff union_less_mono)
      next
        have "\<omega>^x + HMSet Ka < \<omega>^y + HMSet La"
          using k_lt_l[unfolded k_eq_xKa l_eq_yLa]
          by (metis HMSet_plus add.commute add_mset_add_single)
        thus "HMSet Ka < HMSet La"
          using x_eq_y by simp
      qed
      hence ?thesis
        unfolding k_eq_xKa l_eq_yLa
        by (simp, subst (1 2) sorted_insort_is_snoc, simp_all add: ord_x_max ord_y_max,
          force simp: x_eq_y)
    }
    moreover
    {
      assume x_ne_y: "x \<noteq> y"

      have x_lt_y: "x < y"
        by (metis K L head_\<omega>_def head_\<omega>_lt_imp_lt hmsetmset_less hmultiset.sel k_lt_l k_nz l_nz
          less_imp_not_less mset_lt_single_iff neqE x x_ne_y y)

      have ord_y_smax_K: "ordinal_of_hmset a < ordinal_of_hmset y" if a_in_K: "a \<in># K" for a
      proof (rule ih)
        show "{#a, y#} < {#k, l#}"
          unfolding k_eq_xKa l_eq_yLa using a_in_K k k_eq_xKa
          by (metis add_mset_add_single mem_imp_less_HMSet mset_lt_single_iff union_less_mono
            union_single_eq_member)
      next
        show "a < y"
          by (metis Max_ge finite_set_mset less_le_trans not_less_iff_gr_or_eq that x x_lt_y)
      qed

      have "ordinal_of_hmset k < ordinal_of_hmset (\<omega>^y)"
      proof (cases La)
        case empty
        show ?thesis
          unfolding k by (auto intro!: from_cnf_less_\<omega>_exp simp: ord_y_smax_K)
      next
        case La: (add ya Lb)
        show ?thesis
        proof (rule ih)
          show "{#k, \<omega>^y#} < {#k, l#}"
            unfolding l_eq_yLa La by simp
        next
          show "k < \<omega>^y"
          proof -
            have "\<And>m. x < Max_mset (add_mset y m)"
              by (meson Max_ge finite_set_mset less_le_trans union_single_eq_member x_lt_y)
            then show ?thesis
              by (metis K x head_\<omega>_def head_\<omega>_lt_imp_lt hmsetmset_less hmultiset.sel k_nz
                mset_lt_single_iff x_lt_y)
          qed
        qed
      qed
      also have "\<dots> \<le> ordinal_of_hmset l"
        unfolding l_eq_yLa
        by (auto simp del: from_cnf.simps intro!: subseq_from_cnf_less_eq
          simp: subseq_from_cnf_less_eq sorted_insort_is_snoc ord_y_max)
      ultimately have ?thesis
        by simp
    }
    ultimately show ?thesis
      by sat
  qed
qed

lemma ordinal_of_hmset_less[simp]: "ordinal_of_hmset k < ordinal_of_hmset l \<longleftrightarrow> k < l"
  using less_imp_not_less less_imp_ordinal_of_hmset_less neq_iff by blast

end
