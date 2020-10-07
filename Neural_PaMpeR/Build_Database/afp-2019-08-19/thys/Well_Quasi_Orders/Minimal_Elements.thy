(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>Minimal elements of sets w.r.t. a well-founded and transitive relation\<close>

theory Minimal_Elements
imports
  Infinite_Sequences
  Open_Induction.Restricted_Predicates
begin

locale minimal_element =
  fixes P A
  assumes po: "po_on P A"
    and wf: "wfp_on P A"
begin

definition "min_elt B = (SOME x. x \<in> B \<and> (\<forall>y \<in> A. P y x \<longrightarrow> y \<notin> B))"

lemma minimal:
  assumes "x \<in> A" and "Q x"
  shows "\<exists>y \<in> A. P\<^sup>=\<^sup>= y x \<and> Q y \<and> (\<forall>z \<in> A. P z y \<longrightarrow> \<not> Q z)"
using wf and assms
proof (induction rule: wfp_on_induct)
  case (less x)
  then show ?case
  proof (cases "\<forall>y \<in> A. P y x \<longrightarrow> \<not> Q y")
    case True
    with less show ?thesis by blast
  next
    case False
    then obtain y where "y \<in> A" and "P y x" and "Q y" by blast
    with less show ?thesis
      using po [THEN po_on_imp_transp_on, unfolded transp_on_def, rule_format, of _ y x] by blast
  qed
qed

lemma min_elt_ex:
  assumes "B \<subseteq> A" and "B \<noteq> {}"
  shows "\<exists>x. x \<in> B \<and> (\<forall>y \<in> A. P y x \<longrightarrow> y \<notin> B)"
using assms using minimal [of _ "\<lambda>x. x \<in> B"] by auto

lemma min_elt_mem:
  assumes "B \<subseteq> A" and "B \<noteq> {}"
  shows "min_elt B \<in> B"
using someI_ex [OF min_elt_ex [OF assms]] by (auto simp: min_elt_def)

lemma min_elt_minimal:
  assumes *: "B \<subseteq> A" "B \<noteq> {}"
  assumes "y \<in> A" and "P y (min_elt B)"
  shows "y \<notin> B"
using someI_ex [OF min_elt_ex [OF *]] and assms by (auto simp: min_elt_def)

text \<open>A lexicographically minimal sequence w.r.t.\ a given set of sequences \<open>C\<close>\<close>
fun lexmin
where
  lexmin: "lexmin C i = min_elt (ith (eq_upto C (lexmin C) i) i)"
declare lexmin [simp del]

lemma eq_upto_lexmin_non_empty:
  assumes "C \<subseteq> SEQ A" and "C \<noteq> {}"
  shows "eq_upto C (lexmin C) i \<noteq> {}"
proof (induct i)
  case 0
  show ?case using assms by auto
next
  let ?A = "\<lambda>i. ith (eq_upto C (lexmin C) i) i"
  case (Suc i)
  then have "?A i \<noteq> {}" by force
  moreover have "eq_upto C (lexmin C) i \<subseteq> eq_upto C (lexmin C) 0" by auto
  ultimately have "?A i \<subseteq> A" and "?A i \<noteq> {}" using assms by (auto simp: ith_def)
  from min_elt_mem [OF this, folded lexmin]
    obtain f where "f \<in> eq_upto C (lexmin C) (Suc i)" by (auto dest: eq_upto_Suc)
  then show ?case by blast
qed

lemma lexmin_SEQ_mem:
  assumes "C \<subseteq> SEQ A" and "C \<noteq> {}"
  shows "lexmin C \<in> SEQ A"
proof -
  { fix i
    let ?X = "ith (eq_upto C (lexmin C) i) i"
    have "?X \<subseteq> A" using assms by (auto simp: ith_def)
    moreover have "?X \<noteq> {}" using eq_upto_lexmin_non_empty [OF assms] by auto
    ultimately have "lexmin C i \<in> A" using min_elt_mem [of ?X] by (subst lexmin) blast }
  then show ?thesis by auto
qed

lemma non_empty_ith:
  assumes "C \<subseteq> SEQ A" and "C \<noteq> {}"
  shows "ith (eq_upto C (lexmin C) i) i \<subseteq> A"
  and "ith (eq_upto C (lexmin C) i) i \<noteq> {}"
using eq_upto_lexmin_non_empty [OF assms, of i] and assms by (auto simp: ith_def)

lemma lexmin_minimal:
  "C \<subseteq> SEQ A \<Longrightarrow> C \<noteq> {} \<Longrightarrow> y \<in> A \<Longrightarrow> P y (lexmin C i) \<Longrightarrow> y \<notin> ith (eq_upto C (lexmin C) i) i"
using min_elt_minimal [OF non_empty_ith, folded lexmin] .

lemma lexmin_mem:
  "C \<subseteq> SEQ A \<Longrightarrow> C \<noteq> {} \<Longrightarrow> lexmin C i \<in> ith (eq_upto C (lexmin C) i) i"
using min_elt_mem [OF non_empty_ith, folded lexmin] .

lemma LEX_chain_on_eq_upto_imp_ith_chain_on:
  assumes "chain_on (LEX P) (eq_upto C f i) (SEQ A)"
  shows "chain_on P (ith (eq_upto C f i) i) A"
using assms
proof -
  { fix x y assume "x \<in> ith (eq_upto C f i) i" and "y \<in> ith (eq_upto C f i) i"
      and "\<not> P x y" and "y \<noteq> x"
    then obtain g h where *: "g \<in> eq_upto C f i" "h \<in> eq_upto C f i"
      and [simp]: "x = g i" "y = h i" and eq: "\<forall>j<i. g j = f j \<and> h j = f j"
      by (auto simp: ith_def eq_upto_def)
    with assms and \<open>y \<noteq> x\<close> consider "LEX P g h" | "LEX P h g" by (force simp: chain_on_def)
    then have "P y x"
    proof (cases)
      assume "LEX P g h"
      with eq and \<open>y \<noteq> x\<close> have "P x y" using assms and *
        by (auto simp: LEX_def)
           (metis SEQ_iff chain_on_imp_subset linorder_neqE_nat minimal subsetCE)
      with \<open>\<not> P x y\<close> show "P y x" ..
    next
      assume "LEX P h g"
      with eq and \<open>y \<noteq> x\<close> show "P y x" using assms and *
        by (auto simp: LEX_def)
           (metis SEQ_iff chain_on_imp_subset linorder_neqE_nat minimal subsetCE)
    qed }
  then show ?thesis using assms by (auto simp: chain_on_def) blast
qed

end

end
