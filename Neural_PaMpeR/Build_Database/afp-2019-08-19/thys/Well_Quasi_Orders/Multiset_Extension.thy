(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>Multiset Extension of Orders (as Binary Predicates)\<close>

(*TODO: move theory (and maybe rename)*)

theory Multiset_Extension
imports
  Open_Induction.Restricted_Predicates
  "HOL-Library.Multiset"
begin

definition multisets :: "'a set \<Rightarrow> 'a multiset set" where
  "multisets A = {M. set_mset M \<subseteq> A}"

lemma in_multisets_iff:
  "M \<in> multisets A \<longleftrightarrow> set_mset M \<subseteq> A"
  by (simp add: multisets_def)

lemma empty_multisets [simp]:
  "{#} \<in> multisets F"
  by (simp add: in_multisets_iff)

lemma multisets_union [simp]:
  "M \<in> multisets A \<Longrightarrow> N \<in> multisets A \<Longrightarrow> M + N \<in> multisets A"
  by (auto simp add: in_multisets_iff)

definition mulex1 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "mulex1 P = (\<lambda>M N. (M, N) \<in> mult1 {(x, y). P x y})"

lemma mulex1_empty [iff]:
  "mulex1 P M {#} \<longleftrightarrow> False"
  using not_less_empty [of M "{(x, y). P x y}"]
  by (auto simp: mulex1_def)

lemma mulex1_add: "mulex1 P N (M0 + {#a#}) \<Longrightarrow>
  (\<exists>M. mulex1 P M M0 \<and> N = M + {#a#}) \<or>
  (\<exists>K. (\<forall>b. b \<in># K \<longrightarrow> P b a) \<and> N = M0 + K)"
  using less_add [of N a M0 "{(x, y). P x y}"]
  by (auto simp: mulex1_def)

lemma mulex1_self_add_right [simp]:
  "mulex1 P A (add_mset a A)"
proof -
  let ?R = "{(x, y). P x y}"
  thm mult1_def
  have "A + {#a#} = A + {#a#}" by simp
  moreover have "A = A + {#}" by simp
  moreover have "\<forall>b. b \<in># {#} \<longrightarrow> (b, a) \<in> ?R" by simp
  ultimately have "(A, add_mset a A) \<in> mult1 ?R"
    unfolding mult1_def by blast
  then show ?thesis by (simp add: mulex1_def)
qed

lemma empty_mult1 [simp]:
  "({#}, {#a#}) \<in> mult1 R"
proof -
  have "{#a#} = {#} + {#a#}" by simp
  moreover have "{#} = {#} + {#}" by simp
  moreover have "\<forall>b. b \<in># {#} \<longrightarrow> (b, a) \<in> R" by simp
  ultimately show ?thesis unfolding mult1_def by force
qed

lemma empty_mulex1 [simp]:
  "mulex1 P {#} {#a#}"
  using empty_mult1 [of a "{(x, y). P x y}"] by (simp add: mulex1_def)

definition mulex_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "mulex_on P A = (restrict_to (mulex1 P) (multisets A))\<^sup>+\<^sup>+"

abbreviation mulex :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "mulex P \<equiv> mulex_on P UNIV"

lemma mulex_on_induct [consumes 1, case_names base step, induct pred: mulex_on]:
  assumes "mulex_on P A M N"
    and "\<And>M N. \<lbrakk>M \<in> multisets A; N \<in> multisets A; mulex1 P M N\<rbrakk> \<Longrightarrow> Q M N"
    and "\<And>L M N. \<lbrakk>mulex_on P A L M; Q L M; N \<in> multisets A; mulex1 P M N\<rbrakk> \<Longrightarrow> Q L N"
  shows "Q M N"
  using assms unfolding mulex_on_def by (induct) blast+

lemma mulex_on_self_add_singleton_right [simp]:
  assumes "a \<in> A" and "M \<in> multisets A"
  shows "mulex_on P A M (add_mset a M)"
proof -
  have "mulex1 P M (M + {#a#})" by simp
  with assms have "restrict_to (mulex1 P) (multisets A) M (add_mset a M)"
    by (auto simp: multisets_def)
  then show ?thesis unfolding mulex_on_def by blast
qed

lemma singleton_multisets [iff]:
  "{#x#} \<in> multisets A \<longleftrightarrow> x \<in> A"
  by (auto simp: multisets_def)

lemma union_multisetsD:
  assumes "M + N \<in> multisets A"
  shows "M \<in> multisets A \<and> N \<in> multisets A"
  using assms by (auto simp: multisets_def)

lemma mulex_on_multisetsD [dest]:
  assumes "mulex_on P F M N"
  shows "M \<in> multisets F" and "N \<in> multisets F"
  using assms by (induct) auto

lemma union_multisets_iff [iff]:
  "M + N \<in> multisets A \<longleftrightarrow> M \<in> multisets A \<and> N \<in> multisets A"
  by (auto dest: union_multisetsD)

lemma add_mset_multisets_iff [iff]:
  "add_mset a M \<in> multisets A \<longleftrightarrow> a \<in> A \<and> M \<in> multisets A"
  unfolding add_mset_add_single[of a M] union_multisets_iff by auto

lemma mulex_on_trans:
  "mulex_on P A L M \<Longrightarrow> mulex_on P A M N \<Longrightarrow> mulex_on P A L N"
  by (auto simp: mulex_on_def)

lemma transp_on_mulex_on:
  "transp_on (mulex_on P A) B"
  using mulex_on_trans [of P A] by (auto simp: transp_on_def)
  
lemma mulex_on_add_right [simp]:
  assumes "mulex_on P A M N" and "a \<in> A"
  shows "mulex_on P A M (add_mset a N)"
proof -
  from assms have "a \<in> A" and "N \<in> multisets A" by auto
  then have "mulex_on P A N (add_mset a N)" by simp
  with \<open>mulex_on P A M N\<close> show ?thesis by (rule mulex_on_trans)
qed

lemma empty_mulex_on [simp]:
  assumes "M \<noteq> {#}" and "M \<in> multisets A"
  shows "mulex_on P A {#} M"
using assms
proof (induct M)
  case (add a M)
  show ?case
  proof (cases "M = {#}")
    assume "M = {#}"
    with add show ?thesis by (auto simp: mulex_on_def)
  next
    assume "M \<noteq> {#}"
    with add show ?thesis by (auto intro: mulex_on_trans)
  qed
qed simp

lemma mulex_on_self_add_right [simp]:
  assumes "M \<in> multisets A" and "K \<in> multisets A" and "K \<noteq> {#}"
  shows "mulex_on P A M (M + K)"
using assms
proof (induct K)
  case empty
  then show ?case by (cases "K = {#}") auto
next
  case (add a M)
  show ?case
  proof (cases "M = {#}")
    assume "M = {#}" with add show ?thesis by auto
  next
    assume "M \<noteq> {#}" with add show ?thesis
      by (auto dest: mulex_on_add_right simp add: ac_simps)
  qed
qed

lemma mult1_singleton [iff]:
  "({#x#}, {#y#}) \<in> mult1 R \<longleftrightarrow> (x, y) \<in> R"
proof
  assume "(x, y) \<in> R"
  then have "{#y#} = {#} + {#y#}"
    and "{#x#} = {#} + {#x#}"
    and "\<forall>b. b \<in># {#x#} \<longrightarrow> (b, y) \<in> R" by auto
  then show "({#x#}, {#y#}) \<in> mult1 R" unfolding mult1_def by blast
next
  assume "({#x#}, {#y#}) \<in> mult1 R"
  then obtain M0 K a
    where "{#y#} = add_mset a M0"
    and "{#x#} = M0 + K"
    and "\<forall>b. b \<in># K \<longrightarrow> (b, a) \<in> R"
    unfolding mult1_def by blast
  then show "(x, y) \<in> R" by (auto simp: add_eq_conv_diff)
qed

lemma mulex1_singleton [iff]:
  "mulex1 P {#x#} {#y#} \<longleftrightarrow> P x y"
  using mult1_singleton [of x y "{(x, y). P x y}"] by (simp add: mulex1_def)

lemma singleton_mulex_onI:
  "P x y \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> mulex_on P A {#x#} {#y#}"
  by (auto simp: mulex_on_def)

lemma reflclp_mulex_on_add_right [simp]:
  assumes "(mulex_on P A)\<^sup>=\<^sup>= M N" and "M \<in> multisets A" and "a \<in> A"
  shows "mulex_on P A M (N + {#a#})"
  using assms by (cases "M = N") simp_all

lemma reflclp_mulex_on_add_right' [simp]:
  assumes "(mulex_on P A)\<^sup>=\<^sup>= M N" and "M \<in> multisets A" and "a \<in> A"
  shows "mulex_on P A M ({#a#} + N)"
  using reflclp_mulex_on_add_right [OF assms] by (simp add: ac_simps)

lemma mulex_on_union_right [simp]:
  assumes "mulex_on P F A B" and "K \<in> multisets F"
  shows "mulex_on P F A (K + B)"
using assms
proof (induct K)
  case (add a K)
  then have "a \<in> F" and "mulex_on P F A (B + K)" by (auto simp: multisets_def ac_simps)
  then have "mulex_on P F A ((B + K) + {#a#})" by simp
  then show ?case by (simp add: ac_simps)
qed simp

lemma mulex_on_union_right' [simp]:
  assumes "mulex_on P F A B" and "K \<in> multisets F"
  shows "mulex_on P F A (B + K)"
  using mulex_on_union_right [OF assms] by (simp add: ac_simps)

text \<open>Adapted from @{thm all_accessible} in @{theory "HOL-Library.Multiset"}.\<close>
lemma accessible_on_mulex1_multisets:
  assumes wf: "wfp_on P A"
  shows "\<forall>M\<in>multisets A. accessible_on (mulex1 P) (multisets A) M"
proof
  let ?P = "mulex1 P"
  let ?A = "multisets A"
  let ?acc = "accessible_on ?P ?A"
  {
    fix M M0 a
    assume M0: "?acc M0"
      and "a \<in> A"
      and "M0 \<in> ?A"
      and wf_hyp: "\<And>b. \<lbrakk>b \<in> A; P b a\<rbrakk> \<Longrightarrow> (\<forall>M. ?acc (M) \<longrightarrow> ?acc (M + {#b#}))"
      and acc_hyp: "\<forall>M. M \<in> ?A \<and> ?P M M0 \<longrightarrow> ?acc (M + {#a#})"
    then have "add_mset a M0 \<in> ?A" by (auto simp: multisets_def)
    then have "?acc (add_mset a M0)"
    proof (rule accessible_onI [of "add_mset a M0"])
      fix N
      assume "N \<in> ?A"
        and "?P N (add_mset a M0)"
      then have "((\<exists>M. M \<in> ?A \<and> ?P M M0 \<and> N = M + {#a#}) \<or>
          (\<exists>K. (\<forall>b. b \<in># K \<longrightarrow> P b a) \<and> N = M0 + K))"
        using mulex1_add [of P N M0 a] by (auto simp: multisets_def)
      then show "?acc (N)"
      proof (elim exE disjE conjE)
        fix M assume "M \<in> ?A" and "?P M M0" and N: "N = M + {#a#}"
        from acc_hyp have "M \<in> ?A \<and> ?P M M0 \<longrightarrow> ?acc (M + {#a#})" ..
        with \<open>M \<in> ?A\<close> and \<open>?P M M0\<close> have "?acc (M + {#a#})" by blast
        then show "?acc (N)" by (simp only: N)
      next
        fix K
        assume N: "N = M0 + K"
        assume "\<forall>b. b \<in># K \<longrightarrow> P b a"
        moreover from N and \<open>N \<in> ?A\<close> have "K \<in> ?A" by (auto simp: multisets_def)
        ultimately have "?acc (M0 + K)"
        proof (induct K)
          case empty
          from M0 show "?acc (M0 + {#})" by simp
        next
          case (add x K)
          from add.prems have "x \<in> A" and "P x a" by (auto simp: multisets_def)
          with wf_hyp have "\<forall>M. ?acc M \<longrightarrow> ?acc (M + {#x#})" by blast
          moreover from add have "?acc (M0 + K)" by (auto simp: multisets_def)
          ultimately show "?acc (M0 + (add_mset x K))" by simp
        qed
        then show "?acc N" by (simp only: N)
      qed
    qed
  } note tedious_reasoning = this

  fix M
  assume "M \<in> ?A"
  then show "?acc M"
  proof (induct M)
    show "?acc {#}"
    proof (rule accessible_onI)
      show "{#} \<in> ?A" by (auto simp: multisets_def)
    next
      fix b assume "?P b {#}" then show "?acc b" by simp
    qed
  next
    case (add a M)
    then have "?acc M" by (auto simp: multisets_def)
    from add have "a \<in> A" by (auto simp: multisets_def)
    with wf have "\<forall>M. ?acc M \<longrightarrow> ?acc (add_mset a M)"
    proof (induct)
      case (less a)
      then have r: "\<And>b. \<lbrakk>b \<in> A; P b a\<rbrakk> \<Longrightarrow> (\<forall>M. ?acc M \<longrightarrow> ?acc (M + {#b#}))" by auto
      show "\<forall>M. ?acc M \<longrightarrow> ?acc (add_mset a M)"
      proof (intro allI impI)
        fix M'
        assume "?acc M'"
        moreover then have "M' \<in> ?A" by (blast dest: accessible_on_imp_mem)
        ultimately show "?acc (add_mset a M')"
          by (induct) (rule tedious_reasoning [OF _ \<open>a \<in> A\<close> _ r], auto)
      qed
    qed
    with \<open>?acc (M)\<close> show "?acc (add_mset a M)" by blast
  qed
qed

lemmas wfp_on_mulex1_multisets =
  accessible_on_mulex1_multisets [THEN accessible_on_imp_wfp_on]

lemmas irreflp_on_mulex1 =
  wfp_on_mulex1_multisets [THEN wfp_on_imp_irreflp_on]

lemma wfp_on_mulex_on_multisets:
  assumes "wfp_on P A"
  shows "wfp_on (mulex_on P A) (multisets A)"
  using wfp_on_mulex1_multisets [OF assms]
  by (simp only: mulex_on_def wfp_on_restrict_to_tranclp_wfp_on_conv)

lemmas irreflp_on_mulex_on =
  wfp_on_mulex_on_multisets [THEN wfp_on_imp_irreflp_on]

lemma mulex1_union:
  "mulex1 P M N \<Longrightarrow> mulex1 P (K + M) (K + N)"
  by (auto simp: mulex1_def mult1_union)

lemma mulex_on_union:
  assumes "mulex_on P A M N" and "K \<in> multisets A"
  shows "mulex_on P A (K + M) (K + N)"
using assms
proof (induct)
  case (base M N)
  then have "mulex1 P (K + M) (K + N)" by (blast dest: mulex1_union)
  moreover from base have "(K + M) \<in> multisets A"
    and "(K + N) \<in> multisets A" by (auto simp: multisets_def)
  ultimately have "restrict_to (mulex1 P) (multisets A) (K + M) (K + N)" by auto
  then show ?case by (auto simp: mulex_on_def)
next
  case (step L M N)
  then have "mulex1 P (K + M) (K + N)" by (blast dest: mulex1_union)
  moreover from step have "(K + M) \<in> multisets A" and "(K + N) \<in> multisets A" by blast+
  ultimately have "(restrict_to (mulex1 P) (multisets A))\<^sup>+\<^sup>+ (K + M) (K + N)" by auto
  moreover have "mulex_on P A (K + L) (K + M)" using step by blast
  ultimately show ?case by (auto simp: mulex_on_def)
qed

lemma mulex_on_union':
  assumes "mulex_on P A M N" and "K \<in> multisets A"
  shows "mulex_on P A (M + K) (N + K)"
  using mulex_on_union [OF assms] by (simp add: ac_simps)

lemma mulex_on_add_mset:
  assumes "mulex_on P A M N" and "m \<in> A"
  shows "mulex_on P A (add_mset m M) (add_mset m N)"
  unfolding add_mset_add_single[of m M] add_mset_add_single[of m N]
  apply (rule mulex_on_union')
  using assms by auto

lemma union_mulex_on_mono:
  "mulex_on P F A C \<Longrightarrow> mulex_on P F B D \<Longrightarrow> mulex_on P F (A + B) (C + D)"
  by (metis mulex_on_multisetsD mulex_on_trans mulex_on_union mulex_on_union')

lemma mulex_on_add_mset':
  assumes "P m n" and "m \<in> A" and "n \<in> A" and "M \<in> multisets A"
  shows "mulex_on P A (add_mset m M) (add_mset n M)"
  unfolding add_mset_add_single[of m M] add_mset_add_single[of n M]
  apply (rule mulex_on_union)
  using assms by (auto simp: mulex_on_def)

lemma mulex_on_add_mset_mono:
  assumes "P m n" and "m \<in> A" and "n \<in> A" and "mulex_on P A M N"
  shows "mulex_on P A (add_mset m M) (add_mset n N)"
  unfolding add_mset_add_single[of m M] add_mset_add_single[of n N]
  apply (rule union_mulex_on_mono)
  using assms by (auto simp: mulex_on_def)

lemma union_mulex_on_mono1:
  "A \<in> multisets F \<Longrightarrow> (mulex_on P F)\<^sup>=\<^sup>= A C \<Longrightarrow> mulex_on P F B D \<Longrightarrow>
    mulex_on P F (A + B) (C + D)"
  by (auto intro: union_mulex_on_mono mulex_on_union)

lemma union_mulex_on_mono2:
  "B \<in> multisets F \<Longrightarrow> mulex_on P F A C \<Longrightarrow> (mulex_on P F)\<^sup>=\<^sup>= B D \<Longrightarrow>
    mulex_on P F (A + B) (C + D)"
  by (auto intro: union_mulex_on_mono mulex_on_union')

lemma mult1_mono:
  assumes "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (x, y) \<in> S"
    and "M \<in> multisets A"
    and "N \<in> multisets A"
    and "(M, N) \<in> mult1 R"
  shows "(M, N) \<in> mult1 S"
  using assms unfolding mult1_def multisets_def
  by auto (metis (full_types) subsetD)

lemma mulex1_mono:
  assumes "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; P x y\<rbrakk> \<Longrightarrow> Q x y"
    and "M \<in> multisets A"
    and "N \<in> multisets A"
    and "mulex1 P M N"
  shows "mulex1 Q M N"
  using mult1_mono [of A "{(x, y). P x y}" "{(x, y). Q x y}" M N]
    and assms unfolding mulex1_def by blast

lemma mulex_on_mono:
  assumes *: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; P x y\<rbrakk> \<Longrightarrow> Q x y"
    and "mulex_on P A M N"
  shows "mulex_on Q A M N"
proof -
  let ?rel = "\<lambda>P. (restrict_to (mulex1 P) (multisets A))"
  from \<open>mulex_on P A M N\<close> have "(?rel P)\<^sup>+\<^sup>+ M N" by (simp add: mulex_on_def)
  then have "(?rel Q)\<^sup>+\<^sup>+ M N"
  proof (induct rule: tranclp.induct)
    case (r_into_trancl M N)
    then have "M \<in> multisets A" and "N \<in> multisets A" by auto
    from mulex1_mono [OF * this] and r_into_trancl
      show ?case by auto
  next
    case (trancl_into_trancl L M N)
    then have "M \<in> multisets A" and "N \<in> multisets A" by auto
    from mulex1_mono [OF * this] and trancl_into_trancl
      have "?rel Q M N" by auto
    with \<open>(?rel Q)\<^sup>+\<^sup>+ L M\<close> show ?case by (rule tranclp.trancl_into_trancl)
  qed
  then show ?thesis by (simp add: mulex_on_def)
qed

lemma mult1_reflcl:
  assumes "(M, N) \<in> mult1 R"
  shows "(M, N) \<in> mult1 (R\<^sup>=)"
  using assms by (auto simp: mult1_def)

lemma mulex1_reflclp:
  assumes "mulex1 P M N"
  shows "mulex1 (P\<^sup>=\<^sup>=) M N"
  using mulex1_mono [of UNIV P "P\<^sup>=\<^sup>=" M N, OF _ _ _ assms]
  by (auto simp: multisets_def)

lemma mulex_on_reflclp:
  assumes "mulex_on P A M N"
  shows "mulex_on (P\<^sup>=\<^sup>=) A M N"
  using mulex_on_mono [OF _ assms, of "P\<^sup>=\<^sup>="] by auto                  

lemma surj_on_multisets_mset:
  "\<forall>M\<in>multisets A. \<exists>xs\<in>lists A. M = mset xs"
proof
  fix M
  assume "M \<in> multisets A"
  then show "\<exists>xs\<in>lists A. M = mset xs"
  proof (induct M)
    case empty show ?case by simp
  next
    case (add a M)
    then obtain xs where "xs \<in> lists A" and "M = mset xs" by auto
    then have "add_mset a M = mset (a # xs)" by simp
    moreover have "a # xs \<in> lists A" using \<open>xs \<in> lists A\<close> and add by auto
    ultimately show ?case by blast
  qed
qed

lemma image_mset_lists [simp]:
  "mset ` lists A = multisets A"
  using surj_on_multisets_mset [of A]
  by auto (metis mem_Collect_eq multisets_def set_mset_mset subsetI)

lemma multisets_UNIV [simp]: "multisets UNIV = UNIV"
  by (metis image_mset_lists lists_UNIV surj_mset)

lemma non_empty_multiset_induct [consumes 1, case_names singleton add]:
  assumes "M \<noteq> {#}"
    and "\<And>x. P {#x#}"
    and "\<And>x M. P M \<Longrightarrow> P (add_mset x M)"
  shows "P M"
  using assms by (induct M) auto

lemma mulex_on_all_strict:
  assumes "X \<noteq> {#}"
  assumes "X \<in> multisets A" and "Y \<in> multisets A"
    and *: "\<forall>y. y \<in># Y \<longrightarrow> (\<exists>x. x \<in># X \<and> P y x)"
  shows "mulex_on P A Y X"
using assms
proof (induction X arbitrary: Y rule: non_empty_multiset_induct)
  case (singleton x)
  then have "mulex1 P Y {#x#}"
    unfolding mulex1_def mult1_def
    by auto
  with singleton show ?case by (auto simp: mulex_on_def)
next
  case (add x M)
  let ?Y = "{# y \<in># Y. \<exists>x. x \<in># M \<and> P y x #}"
  let ?Z = "Y - ?Y"
  have Y: "Y = ?Z + ?Y" by (subst multiset_eq_iff) auto
  from \<open>Y \<in> multisets A\<close> have "?Y \<in> multisets A" by (metis multiset_partition union_multisets_iff)
  moreover have "\<forall>y. y \<in># ?Y \<longrightarrow> (\<exists>x. x \<in># M \<and> P y x)" by auto
  moreover have "M \<in> multisets A" using add by auto
  ultimately have "mulex_on P A ?Y M" using add by blast
  moreover have "mulex_on P A ?Z {#x#}"
  proof -
    have "{#x#} = {#} + {#x#}" by simp
    moreover have "?Z = {#} + ?Z" by simp
    moreover have "\<forall>y. y \<in># ?Z \<longrightarrow> P y x"
      using add.prems by (auto simp add: in_diff_count split: if_splits)
    ultimately have "mulex1 P ?Z {#x#}" unfolding mulex1_def mult1_def by blast
    moreover have "{#x#} \<in> multisets A" using add.prems by auto
    moreover have "?Z \<in> multisets A"
      using \<open>Y \<in> multisets A\<close> by (metis diff_union_cancelL multiset_partition union_multisetsD)
    ultimately show ?thesis by (auto simp: mulex_on_def)
  qed
  ultimately have "mulex_on P A (?Y + ?Z) (M + {#x#})" by (rule union_mulex_on_mono)
  then show ?case using Y by (simp add: ac_simps)
qed

text \<open>The following lemma shows that the textbook definition (e.g.,
``Term Rewriting and All That'') is the same as the one used below.\<close>
lemma diff_set_Ex_iff:
  "X \<noteq> {#} \<and> X \<subseteq># M \<and> N = (M - X) + Y \<longleftrightarrow> X \<noteq> {#} \<and> (\<exists>Z. M = Z + X \<and> N = Z + Y)"
  by (auto) (metis add_diff_cancel_left' multiset_diff_union_assoc union_commute)

text \<open>Show that @{const mulex_on} is equivalent to the textbook definition
of multiset-extension for transitive base orders.\<close>
lemma mulex_on_alt_def:
  assumes trans: "transp_on P A"
  shows "mulex_on P A M N \<longleftrightarrow> M \<in> multisets A \<and> N \<in> multisets A \<and> (\<exists>X Y Z.
    X \<noteq> {#} \<and> N = Z + X \<and> M = Z + Y \<and> (\<forall>y. y \<in># Y \<longrightarrow> (\<exists>x. x \<in># X \<and> P y x)))"
  (is "?P M N \<longleftrightarrow> ?Q M N")
proof
  assume "?P M N" then show "?Q M N"
  proof (induct M N)
    case (base M N)
    then obtain a M0 K where N: "N = M0 + {#a#}"
      and M: "M = M0 + K"
      and *: "\<forall>b. b \<in># K \<longrightarrow> P b a"
      and "M \<in> multisets A" and "N \<in> multisets A" by (auto simp: mulex1_def mult1_def)
    moreover then have "{#a#} \<in> multisets A" and "K \<in> multisets A" by auto
    moreover have "{#a#} \<noteq> {#}" by auto
    moreover have "N = M0 + {#a#}" by fact
    moreover have "M = M0 + K" by fact
    moreover have "\<forall>y. y \<in># K \<longrightarrow> (\<exists>x. x \<in># {#a#} \<and> P y x)" using * by auto
    ultimately show ?case by blast
  next
    case (step L M N)
    then obtain X Y Z
      where "L \<in> multisets A" and "M \<in> multisets A" and "N \<in> multisets A"
      and "X \<in> multisets A" and "Y \<in> multisets A"
      and M: "M = Z + X"
      and L: "L = Z + Y" and "X \<noteq> {#}"
      and Y: "\<forall>y. y \<in># Y \<longrightarrow> (\<exists>x. x \<in># X \<and> P y x)"
      and "mulex1 P M N"
      by blast
    from \<open>mulex1 P M N\<close> obtain a M0 K
      where N: "N = add_mset a M0" and M': "M = M0 + K"
      and *: "\<forall>b. b \<in># K \<longrightarrow> P b a" unfolding mulex1_def mult1_def by blast
    have L': "L = (M - X) + Y" by (simp add: L M)
    have K: "\<forall>y. y \<in># K \<longrightarrow> (\<exists>x. x \<in># {#a#} \<and> P y x)" using * by auto

    txt \<open>The remainder of the proof is adapted from the proof of Lemma 2.5.4. of
    the book ``Term Rewriting and All That.''\<close>
    let ?X = "add_mset a (X - K)"
    let ?Y = "(K - X) + Y"
    
    have "L \<in> multisets A" and "N \<in> multisets A" by fact+
    moreover have "?X \<noteq> {#} \<and> (\<exists>Z. N = Z + ?X \<and> L = Z + ?Y)"
    proof -
      have "?X \<noteq> {#}" by auto
      moreover have "?X \<subseteq># N"
        using M N M' by (simp add: add.commute [of "{#a#}"])
          (metis Multiset.diff_subset_eq_self add.commute add_diff_cancel_right)
      moreover have "L = (N - ?X) + ?Y"
      proof (rule multiset_eqI)
        fix x :: 'a
        let ?c = "\<lambda>M. count M x"
        let ?ic = "\<lambda>x. int (?c x)"
        from \<open>?X \<subseteq># N\<close> have *: "?c {#a#} + ?c (X - K) \<le> ?c N"
          by (auto simp add: subseteq_mset_def split: if_splits)
        from * have **: "?c (X - K) \<le> ?c M0" unfolding N by (auto split: if_splits)
        have "?ic (N - ?X + ?Y) = int (?c N - ?c ?X) + ?ic ?Y" by simp
        also have "\<dots> = int (?c N - (?c {#a#} + ?c (X - K))) + ?ic (K - X) + ?ic Y" by simp
        also have "\<dots> = ?ic N - (?ic {#a#} + ?ic (X - K)) + ?ic (K - X) + ?ic Y"
          using of_nat_diff [OF *] by simp
        also have "\<dots> = (?ic N - ?ic {#a#}) - ?ic (X - K) + ?ic (K - X) + ?ic Y" by simp
        also have "\<dots> = (?ic N - ?ic {#a#}) + (?ic (K - X) - ?ic (X - K)) + ?ic Y" by simp
        also have "\<dots> = (?ic N - ?ic {#a#}) + (?ic K - ?ic X) + ?ic Y" by simp
        also have "\<dots> = (?ic N - ?ic ?X) + ?ic ?Y" by (simp add: N)
        also have "\<dots> = ?ic L"
          unfolding L' M' N
          using ** by (simp add: algebra_simps)
        finally show "?c L = ?c (N - ?X + ?Y)" by simp
      qed
      ultimately show ?thesis by (metis diff_set_Ex_iff)
    qed
    moreover have "\<forall>y. y \<in># ?Y \<longrightarrow> (\<exists>x. x \<in># ?X \<and> P y x)"
    proof (intro allI impI)
      fix y assume "y \<in># ?Y"
      then have "y \<in># K - X \<or> y \<in># Y" by auto
      then show "\<exists>x. x \<in># ?X \<and> P y x"
      proof
        assume "y \<in># K - X"
        then have "y \<in># K" by (rule in_diffD)
        with K show ?thesis by auto
      next
        assume "y \<in># Y"
        with Y obtain x where "x \<in># X" and "P y x" by blast
        { assume "x \<in># X - K" with \<open>P y x\<close> have ?thesis by auto }
        moreover
        { assume "x \<in># K" with * have "P x a" by auto
          moreover have "y \<in> A" using \<open>Y \<in> multisets A\<close> and \<open>y \<in># Y\<close> by (auto simp: multisets_def)
          moreover have "a \<in> A" using \<open>N \<in> multisets A\<close> by (auto simp: N)
          moreover have "x \<in> A" using \<open>M \<in> multisets A\<close> and \<open>x \<in># K\<close> by (auto simp: M' multisets_def)
          ultimately have "P y a" using \<open>P y x\<close> and trans unfolding transp_on_def by blast
          then have ?thesis by force }
        moreover from \<open>x \<in># X\<close> have "x \<in># X - K \<or> x \<in># K"
          by (auto simp add: in_diff_count not_in_iff)
        ultimately show ?thesis by auto
      qed
    qed
    ultimately show ?case by blast
  qed
next
  assume "?Q M N"
  then obtain X Y Z where "M \<in> multisets A" and "N \<in> multisets A"
    and "X \<noteq> {#}" and N: "N = Z + X" and M: "M = Z + Y"
    and *: "\<forall>y. y \<in># Y \<longrightarrow> (\<exists>x. x \<in># X \<and> P y x)" by blast
  with mulex_on_all_strict [of X A Y] have "mulex_on P A Y X" by auto
  moreover from \<open>N \<in> multisets A\<close> have "Z \<in> multisets A" by (auto simp: N)
  ultimately show "?P M N" unfolding M N by (metis mulex_on_union)
qed

end

