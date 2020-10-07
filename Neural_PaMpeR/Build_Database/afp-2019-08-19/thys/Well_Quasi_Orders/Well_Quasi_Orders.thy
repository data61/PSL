(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>Well-Quasi-Orders\<close>

theory Well_Quasi_Orders
imports Almost_Full_Relations
begin

subsection \<open>Basic Definitions\<close>

definition wqo_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "wqo_on P A \<longleftrightarrow> transp_on P A \<and> almost_full_on P A"

lemma wqo_on_UNIV:
  "wqo_on (\<lambda>_ _. True) UNIV"
  using almost_full_on_UNIV by (auto simp: wqo_on_def transp_on_def)

lemma wqo_onI [Pure.intro]:
  "\<lbrakk>transp_on P A; almost_full_on P A\<rbrakk> \<Longrightarrow> wqo_on P A"
  unfolding wqo_on_def almost_full_on_def by blast

lemma wqo_on_imp_reflp_on:
  "wqo_on P A \<Longrightarrow> reflp_on P A"
  using almost_full_on_imp_reflp_on by (auto simp: wqo_on_def)

lemma wqo_on_imp_transp_on:
  "wqo_on P A \<Longrightarrow> transp_on P A"
  by (auto simp: wqo_on_def)

lemma wqo_on_imp_almost_full_on:
  "wqo_on P A \<Longrightarrow> almost_full_on P A"
  by (auto simp: wqo_on_def)

lemma wqo_on_imp_qo_on:
  "wqo_on P A \<Longrightarrow> qo_on P A"
  by (metis qo_on_def wqo_on_imp_reflp_on wqo_on_imp_transp_on)

lemma wqo_on_imp_good:
  "wqo_on P A \<Longrightarrow> \<forall>i. f i \<in> A \<Longrightarrow> good P f"
  by (auto simp: wqo_on_def almost_full_on_def)

lemma wqo_on_subset:
  "A \<subseteq> B \<Longrightarrow> wqo_on P B \<Longrightarrow> wqo_on P A"
  using almost_full_on_subset [of A B P]
    and transp_on_subset [of A B P]
  unfolding wqo_on_def by blast


subsection \<open>Equivalent Definitions\<close>

text \<open>
  Given a quasi-order @{term P}, the following statements are equivalent:
  \begin{enumerate}
  \item @{term P} is a almost-full.
  \item @{term P} does neither allow decreasing chains nor antichains.
  \item Every quasi-order extending @{term P} is well-founded.
  \end{enumerate}
\<close>

lemma wqo_af_conv:
  assumes "qo_on P A"
  shows "wqo_on P A \<longleftrightarrow> almost_full_on P A"
  using assms by (metis qo_on_def wqo_on_def)

lemma wqo_wf_and_no_antichain_conv:
  assumes "qo_on P A"
  shows "wqo_on P A \<longleftrightarrow> wfp_on (strict P) A \<and> \<not> (\<exists>f. antichain_on P f A)"
  unfolding wqo_af_conv [OF assms]
  using af_trans_imp_wf [OF _ assms [THEN qo_on_imp_transp_on]]
    and almost_full_on_imp_no_antichain_on [of P A]
    and wf_and_no_antichain_imp_qo_extension_wf [of P A]
    and every_qo_extension_wf_imp_af [OF _ assms]
    by blast

lemma wqo_extensions_wf_conv:
  assumes "qo_on P A"
  shows "wqo_on P A \<longleftrightarrow> (\<forall>Q. (\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y) \<and> qo_on Q A \<longrightarrow> wfp_on (strict Q) A)"
  unfolding wqo_af_conv [OF assms]
  using af_trans_imp_wf [OF _ assms [THEN qo_on_imp_transp_on]]
    and almost_full_on_imp_no_antichain_on [of P A]
    and wf_and_no_antichain_imp_qo_extension_wf [of P A]
    and every_qo_extension_wf_imp_af [OF _ assms]
    by blast

lemma wqo_on_imp_wfp_on:
  "wqo_on P A \<Longrightarrow> wfp_on (strict P) A"
  by (metis (no_types) wqo_on_imp_qo_on wqo_wf_and_no_antichain_conv)

text \<open>
  The homomorphic image of a wqo set is wqo.
\<close>
lemma wqo_on_hom:
  assumes "transp_on Q (h ` A)"
    and "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q (h x) (h y)"
    and "wqo_on P A"
  shows "wqo_on Q (h ` A)"
  using assms and almost_full_on_hom [of A P Q h]
  unfolding wqo_on_def by blast

text \<open>
  The monomorphic preimage of a wqo set is wqo.
\<close>
lemma wqo_on_mon:
  assumes *: "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longleftrightarrow> Q (h x) (h y)"
    and bij: "bij_betw h A B"
    and wqo: "wqo_on Q B"
  shows "wqo_on P A"
proof -
  have "transp_on P A"
  proof
    fix x y z assume [intro!]: "x \<in> A" "y \<in> A" "z \<in> A"
      and "P x y" and "P y z"
    with * have "Q (h x) (h y)" and "Q (h y) (h z)" by blast+
    with wqo_on_imp_transp_on [OF wqo] have "Q (h x) (h z)"
      using bij by (auto simp: bij_betw_def transp_on_def)
    with * show "P x z" by blast
  qed
  with assms and almost_full_on_mon [of A P Q h]
    show ?thesis unfolding wqo_on_def by blast
qed


subsection \<open>A Type Class for Well-Quasi-Orders\<close>

text \<open>
  In a well-quasi-order (wqo) every infinite sequence is good.
\<close>
class wqo = preorder +
  assumes good: "good (\<le>) f"

lemma wqo_on_class [simp, intro]:
  "wqo_on (\<le>) (UNIV :: ('a :: wqo) set)"
  using good by (auto simp: wqo_on_def transp_on_def almost_full_on_def dest: order_trans)

lemma wqo_on_UNIV_class_wqo [intro!]:
  "wqo_on P UNIV \<Longrightarrow> class.wqo P (strict P)"
  by (unfold_locales) (auto simp: wqo_on_def almost_full_on_def, unfold transp_on_def, blast)

text \<open>
  The following lemma converts between @{const wqo_on} (for the special case that the domain is the
  universe of a type) and the class predicate @{const class.wqo}.
\<close>
lemma wqo_on_UNIV_conv:
  "wqo_on P UNIV \<longleftrightarrow> class.wqo P (strict P)" (is "?lhs = ?rhs")
proof
  assume "?lhs" then show "?rhs" by auto
next
  assume "?rhs" then show "?lhs"
    unfolding class.wqo_def class.preorder_def class.wqo_axioms_def
    by (auto simp: wqo_on_def almost_full_on_def transp_on_def)
qed

text \<open>
  The strict part of a wqo is well-founded.
\<close>
lemma (in wqo) "wfP (<)"
proof -
  have "class.wqo (\<le>) (<)" ..
  hence "wqo_on (\<le>) UNIV"
    unfolding less_le_not_le [abs_def] wqo_on_UNIV_conv [symmetric] .
  from wqo_on_imp_wfp_on [OF this]
    show ?thesis unfolding less_le_not_le [abs_def] wfp_on_UNIV .
qed

lemma wqo_on_with_bot:
  assumes "wqo_on P A"
  shows "wqo_on (option_le P) A\<^sub>\<bottom>" (is "wqo_on ?P ?A")
proof -
  { from assms have trans [unfolded transp_on_def]: "transp_on P A"
      by (auto simp: wqo_on_def)
    have "transp_on ?P ?A"
      by (auto simp: transp_on_def elim!: with_bot_cases, insert trans) blast }
  moreover
  { from assms and almost_full_on_with_bot
      have "almost_full_on ?P ?A" by (auto simp: wqo_on_def) }
  ultimately
  show ?thesis by (auto simp: wqo_on_def)
qed

lemma wqo_on_option_UNIV [intro]:
  "wqo_on P UNIV \<Longrightarrow> wqo_on (option_le P) UNIV"
  using wqo_on_with_bot [of P UNIV] by simp

text \<open>
  When two sets are wqo, then their disjoint sum is wqo.
\<close>
lemma wqo_on_Plus:
  assumes "wqo_on P A" and "wqo_on Q B"
  shows "wqo_on (sum_le P Q) (A <+> B)" (is "wqo_on ?P ?A")
proof -
  { from assms have trans [unfolded transp_on_def]: "transp_on P A" "transp_on Q B"
      by (auto simp: wqo_on_def)
    have "transp_on ?P ?A"
      unfolding transp_on_def by (auto, insert trans) (blast+) }
  moreover
  { from assms and almost_full_on_Plus have "almost_full_on ?P ?A" by (auto simp: wqo_on_def) }
  ultimately
  show ?thesis by (auto simp: wqo_on_def)
qed

lemma wqo_on_sum_UNIV [intro]:
  "wqo_on P UNIV \<Longrightarrow> wqo_on Q UNIV \<Longrightarrow> wqo_on (sum_le P Q) UNIV"
  using wqo_on_Plus [of P UNIV Q UNIV] by simp


subsection \<open>Dickson's Lemma\<close>

lemma wqo_on_Sigma:
  fixes A1 :: "'a set" and A2 :: "'b set"
  assumes "wqo_on P1 A1" and "wqo_on P2 A2"
  shows "wqo_on (prod_le P1 P2) (A1 \<times> A2)" (is "wqo_on ?P ?A")
proof -
  { from assms have "transp_on P1 A1" and "transp_on P2 A2" by (auto simp: wqo_on_def)
    hence "transp_on ?P ?A" unfolding transp_on_def prod_le_def by blast }
  moreover
  { from assms and almost_full_on_Sigma [of P1 A1 P2 A2]
      have "almost_full_on ?P ?A" by (auto simp: wqo_on_def) }
  ultimately
  show ?thesis by (auto simp: wqo_on_def)
qed

lemmas dickson = wqo_on_Sigma

lemma wqo_on_prod_UNIV [intro]:
  "wqo_on P UNIV \<Longrightarrow> wqo_on Q UNIV \<Longrightarrow> wqo_on (prod_le P Q) UNIV"
  using wqo_on_Sigma [of P UNIV Q UNIV] by simp


subsection \<open>Higman's Lemma\<close>

lemma transp_on_list_emb:
  assumes "transp_on P A"
  shows "transp_on (list_emb P) (lists A)"
  using assms and list_emb_trans [of _ _ _ P]
    unfolding transp_on_def by blast

lemma wqo_on_lists:
  assumes "wqo_on P A" shows "wqo_on (list_emb P) (lists A)"
  using assms and almost_full_on_lists
    and transp_on_list_emb by (auto simp: wqo_on_def)

lemmas higman = wqo_on_lists

lemma wqo_on_list_UNIV [intro]:
  "wqo_on P UNIV \<Longrightarrow> wqo_on (list_emb P) UNIV"
  using wqo_on_lists [of P UNIV] by simp

text \<open>
  Every reflexive and transitive relation on a finite set is a wqo.
\<close>
lemma finite_wqo_on:
  assumes "finite A" and refl: "reflp_on P A" and "transp_on P A"
  shows "wqo_on P A"
  using assms and finite_almost_full_on by (auto simp: wqo_on_def)

lemma finite_eq_wqo_on:
  assumes "finite A"
  shows "wqo_on (=) A"
  using finite_wqo_on [OF assms, of "(=)"]
  by (auto simp: reflp_on_def transp_on_def)

lemma wqo_on_lists_over_finite_sets:
  "wqo_on (list_emb (=)) (UNIV::('a::finite) list set)"
  using wqo_on_lists [OF finite_eq_wqo_on [OF finite [of "UNIV::('a::finite) set"]]] by simp

lemma wqo_on_map:
  fixes P and Q and h
  defines "P' \<equiv> \<lambda>x y. P x y \<and> Q (h x) (h y)"
  assumes "wqo_on P A"
    and "wqo_on Q B"
    and subset: "h ` A \<subseteq> B"
  shows "wqo_on P' A"
proof
  let ?Q = "\<lambda>x y. Q (h x) (h y)"
  from \<open>wqo_on P A\<close> have "transp_on P A"
    by (rule wqo_on_imp_transp_on)
  then show "transp_on P' A"
    using \<open>wqo_on Q B\<close> and subset
    unfolding wqo_on_def transp_on_def P'_def by blast

  from \<open>wqo_on P A\<close> have "almost_full_on P A"
    by (rule wqo_on_imp_almost_full_on)
  from \<open>wqo_on Q B\<close> have "almost_full_on Q B"
    by (rule wqo_on_imp_almost_full_on)

  show "almost_full_on P' A"
  proof
    fix f
    assume *: "\<forall>i::nat. f i \<in> A"
    from almost_full_on_imp_homogeneous_subseq [OF \<open>almost_full_on P A\<close> this]
      obtain g :: "nat \<Rightarrow> nat"
      where g: "\<And>i j. i < j \<Longrightarrow> g i < g j"
      and **: "\<forall>i. f (g i) \<in> A \<and> P (f (g i)) (f (g (Suc i)))"
      using * by auto
    from chain_transp_on_less [OF ** \<open>transp_on P A\<close>]
      have **: "\<And>i j. i < j \<Longrightarrow> P (f (g i)) (f (g j))" .
    let ?g = "\<lambda>i. h (f (g i))"
    from * and subset have B: "\<And>i. ?g i \<in> B" by auto
    with \<open>almost_full_on Q B\<close> [unfolded almost_full_on_def good_def, THEN bspec, of ?g]
      obtain i j :: nat
      where "i < j" and "Q (?g i) (?g j)" by blast
    with ** [OF \<open>i < j\<close>] have "P' (f (g i)) (f (g j))"
      by (auto simp: P'_def)
    with g [OF \<open>i < j\<close>] show "good P' f" by (auto simp: good_def)
  qed
qed

lemma wqo_on_UNIV_nat:
  "wqo_on (\<le>) (UNIV :: nat set)"
  unfolding wqo_on_def transp_on_def
  using almost_full_on_UNIV_nat by simp

end
