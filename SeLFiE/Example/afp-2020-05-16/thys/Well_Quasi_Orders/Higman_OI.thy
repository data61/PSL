(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>A Proof of Higman's Lemma via Open Induction\<close>

theory Higman_OI
imports
  Open_Induction.Open_Induction
  Minimal_Elements
  Almost_Full
begin

subsection \<open>Some facts about the suffix relation\<close>

lemma wfp_on_strict_suffix:
  "wfp_on strict_suffix A"
by (rule wfp_on_mono [OF subset_refl, of _ _ "measure_on length A"])
   (auto simp: strict_suffix_def suffix_def)

lemma po_on_strict_suffix:
  "po_on strict_suffix A"
by (force simp: strict_suffix_def po_on_def transp_on_def irreflp_on_def)


subsection \<open>Lexicographic Order on Infinite Sequences\<close>

lemma antisymp_on_LEX:
  assumes "irreflp_on P A" and "antisymp_on P A"
  shows "antisymp_on (LEX P) (SEQ A)"
proof
  fix f g assume SEQ: "f \<in> SEQ A" "g \<in> SEQ A" and "LEX P f g" and "LEX P g f"
  then obtain i j where "P (f i) (g i)" and "P (g j) (f j)"
    and "\<forall>k<i. f k = g k" and "\<forall>k<j. g k = f k" by (auto simp: LEX_def)
  then have "P (f (min i j)) (f (min i j))"
    using assms(2) and SEQ by (cases "i = j") (auto simp: antisymp_on_def min_def, force)
  with assms(1) and SEQ show  "f = g" by (auto simp: irreflp_on_def)
qed

lemma LEX_trans:
  assumes "transp_on P A" and "f \<in> SEQ A" and "g \<in> SEQ A" and "h \<in> SEQ A"
    and "LEX P f g" and "LEX P g h"
  shows "LEX P f h"
using assms by (auto simp: LEX_def transp_on_def) (metis less_trans linorder_neqE_nat)

lemma qo_on_LEXEQ:
  "transp_on P A \<Longrightarrow> qo_on (LEXEQ P) (SEQ A)"
by (auto simp: qo_on_def reflp_on_def transp_on_def [of "LEXEQ P"] dest: LEX_trans)

context minimal_element
begin

lemma glb_LEX_lexmin:
  assumes "chain_on (LEX P) C (SEQ A)" and "C \<noteq> {}"
  shows "glb (LEX P) C (lexmin C)"
proof
  have "C \<subseteq> SEQ A" using assms by (auto simp: chain_on_def)
  then have "lexmin C \<in> SEQ A" using \<open>C \<noteq> {}\<close> by (intro lexmin_SEQ_mem)
  note * = \<open>C \<subseteq> SEQ A\<close> \<open>C \<noteq> {}\<close>
  note lex = LEX_imp_less [folded irreflp_on_def, OF po [THEN po_on_imp_irreflp_on]]
  \<comment> \<open>\<open>lexmin C\<close> is a lower bound\<close>
  show "lb (LEX P) C (lexmin C)"
  proof
    fix f assume "f \<in> C"
    then show "LEXEQ P (lexmin C) f"
    proof (cases "f = lexmin C")
      define i where "i = (LEAST i. f i \<noteq> lexmin C i)"
      case False
      then have neq: "\<exists>i. f i \<noteq> lexmin C i" by blast
      from LeastI_ex [OF this, folded i_def]
        and not_less_Least [where P = "\<lambda>i. f i \<noteq> lexmin C i", folded i_def]
      have neq: "f i \<noteq> lexmin C i" and eq: "\<forall>j<i. f j = lexmin C j" by auto
      then have **: "f \<in> eq_upto C (lexmin C) i" "f i \<in> ith (eq_upto C (lexmin C) i) i"
        using \<open>f \<in> C\<close> by force+
      moreover from ** have "\<not> P (f i) (lexmin C i)"
        using lexmin_minimal [OF *, of "f i" i] and \<open>f \<in> C\<close> and \<open>C \<subseteq> SEQ A\<close> by blast
      moreover obtain g where "g \<in> eq_upto C (lexmin C) (Suc i)"
        using eq_upto_lexmin_non_empty [OF *] by blast
      ultimately have "P (lexmin C i) (f i)"
        using neq and \<open>C \<subseteq> SEQ A\<close> and assms(1) and lex [of g f i] and lex [of f g i]
        by (auto simp: eq_upto_def chain_on_def)
      with eq show ?thesis by (auto simp: LEX_def)
    qed simp
  qed

  \<comment> \<open>\<open>lexmin C\<close> is greater than or equal to any other lower bound\<close>
  fix f assume lb: "lb (LEX P) C f"
  then show "LEXEQ P f (lexmin C)"
  proof (cases "f = lexmin C")
    define i where "i = (LEAST i. f i \<noteq> lexmin C i)"
    case False
    then have neq: "\<exists>i. f i \<noteq> lexmin C i" by blast
    from LeastI_ex [OF this, folded i_def]
      and not_less_Least [where P = "\<lambda>i. f i \<noteq> lexmin C i", folded i_def]
    have neq: "f i \<noteq> lexmin C i" and eq: "\<forall>j<i. f j = lexmin C j" by auto
    obtain h where "h \<in> eq_upto C (lexmin C) (Suc i)" and "h \<in> C"
      using eq_upto_lexmin_non_empty [OF *] by (auto simp: eq_upto_def)
    then have [simp]: "\<And>j. j < Suc i \<Longrightarrow> h j = lexmin C j" by auto
    with lb and \<open>h \<in> C\<close> have "LEX P f h" using neq by (auto simp: lb_def)
    then have "P (f i) (h i)"
      using neq and eq and \<open>C \<subseteq> SEQ A\<close> and \<open>h \<in> C\<close> by (intro lex) auto
    with eq show ?thesis by (auto simp: LEX_def)
  qed simp
qed

lemma dc_on_LEXEQ:
  "dc_on (LEXEQ P) (SEQ A)"
proof
  fix C assume "chain_on (LEXEQ P) C (SEQ A)" and "C \<noteq> {}"
  then have chain: "chain_on (LEX P) C (SEQ A)" by (auto simp: chain_on_def)
  then have "C \<subseteq> SEQ A" by (auto simp: chain_on_def)
  then have "lexmin C \<in> SEQ A" using \<open>C \<noteq> {}\<close> by (intro lexmin_SEQ_mem)
  have "glb (LEX P) C (lexmin C)" by (rule glb_LEX_lexmin [OF chain \<open>C \<noteq> {}\<close>])
  then have "glb (LEXEQ P) C (lexmin C)" by (auto simp: glb_def lb_def)
  with \<open>lexmin C \<in> SEQ A\<close> show "\<exists>f \<in> SEQ A. glb (LEXEQ P) C f" by blast
qed

end

text \<open>
  Properties that only depend on finite initial segments of a sequence
  (i.e., which are open with respect to the product topology).
\<close>
definition "pt_open_on Q A \<longleftrightarrow> (\<forall>f\<in>A. Q f \<longleftrightarrow> (\<exists>n. (\<forall>g\<in>A. (\<forall>i<n. g i = f i) \<longrightarrow> Q g)))"

lemma pt_open_onD:
  "pt_open_on Q A \<Longrightarrow> Q f \<Longrightarrow> f \<in> A \<Longrightarrow> (\<exists>n. (\<forall>g\<in>A. (\<forall>i<n. g i = f i) \<longrightarrow> Q g))"
  unfolding pt_open_on_def by blast

lemma pt_open_on_good:
  "pt_open_on (good Q) (SEQ A)"
proof (unfold pt_open_on_def, intro ballI)
  fix f assume f: "f \<in> SEQ A"
  show "good Q f = (\<exists>n. \<forall>g\<in>SEQ A. (\<forall>i<n. g i = f i) \<longrightarrow> good Q g)"
  proof
    assume "good Q f"
    then obtain i and j where *: "i < j" "Q (f i) (f j)" by auto
    have "\<forall>g\<in>SEQ A. (\<forall>i<Suc j. g i = f i) \<longrightarrow> good Q g"
    proof (intro ballI impI)
      fix g assume "g \<in> SEQ A" and "\<forall>i<Suc j. g i = f i"
      then show "good Q g" using * by (force simp: good_def)
    qed
    then show "\<exists>n. \<forall>g\<in>SEQ A. (\<forall>i<n. g i = f i) \<longrightarrow> good Q g" ..
  next
    assume "\<exists>n. \<forall>g\<in>SEQ A. (\<forall>i<n. g i = f i) \<longrightarrow> good Q g"
    with f show "good Q f" by blast
  qed
qed

context minimal_element
begin

lemma pt_open_on_imp_open_on_LEXEQ:
  assumes "pt_open_on Q (SEQ A)"
  shows "open_on (LEXEQ P) Q (SEQ A)"
proof
  fix C assume chain: "chain_on (LEXEQ P) C (SEQ A)" and ne: "C \<noteq> {}"
    and "\<exists>g\<in>SEQ A. glb (LEXEQ P) C g \<and> Q g"
  then obtain g where g: "g \<in> SEQ A" and "glb (LEXEQ P) C g"
    and Q: "Q g" by blast
  then have glb: "glb (LEX P) C g" by (auto simp: glb_def lb_def)
  from chain have "chain_on (LEX P) C (SEQ A)" and C: "C \<subseteq> SEQ A" by (auto simp: chain_on_def)
  note * = glb_LEX_lexmin [OF this(1) ne]
  have "lexmin C \<in> SEQ A" using ne and C by (intro lexmin_SEQ_mem)
  from glb_unique [OF _ g this glb *]
    and antisymp_on_LEX [OF po_on_imp_irreflp_on [OF po] po_on_imp_antisymp_on [OF po]]
  have [simp]: "lexmin C = g" by auto
  from assms [THEN pt_open_onD, OF Q g]
  obtain n :: nat where **: "\<And>h. h \<in> SEQ A \<Longrightarrow> (\<forall>i<n. h i = g i) \<longrightarrow> Q h" by blast
  from eq_upto_lexmin_non_empty [OF C ne, of n]
  obtain f where "f \<in> eq_upto C g n" by auto
  then have "f \<in> C" and "Q f" using ** [of f] and C by force+
  then show "\<exists>f\<in>C. Q f" by blast
qed

lemma open_on_good:
  "open_on (LEXEQ P) (good Q) (SEQ A)"
  by (intro pt_open_on_imp_open_on_LEXEQ pt_open_on_good)

end

lemma open_on_LEXEQ_imp_pt_open_on_counterexample:
  fixes a b :: "'a"
  defines "A \<equiv> {a, b}" and "P \<equiv> (\<lambda>x y. False)" and "Q \<equiv> (\<lambda>f. \<forall>i. f i = b)"
  assumes [simp]: "a \<noteq> b"
  shows "minimal_element P A" and "open_on (LEXEQ P) Q (SEQ A)"
    and "\<not> pt_open_on Q (SEQ A)"
proof -
  show "minimal_element P A"
    by standard (auto simp: P_def po_on_def irreflp_on_def transp_on_def wfp_on_def)
  show "open_on (LEXEQ P) Q (SEQ A)"
    by (auto simp: P_def open_on_def chain_on_def SEQ_def glb_def lb_def LEX_def)
  show "\<not> pt_open_on Q (SEQ A)"
  proof
    define f :: "nat \<Rightarrow> 'a" where "f \<equiv> (\<lambda>x. b)"
    have "f \<in> SEQ A" by (auto simp: A_def f_def)
    moreover assume "pt_open_on Q (SEQ A)"
    ultimately have "Q f \<longleftrightarrow> (\<exists>n. (\<forall>g\<in>SEQ A. (\<forall>i<n. g i = f i) \<longrightarrow> Q g))"
      unfolding pt_open_on_def by blast
    moreover have "Q f" by (auto simp: Q_def f_def)
    moreover have "\<exists>g\<in>SEQ A. (\<forall>i<n. g i = f i) \<and> \<not> Q g" for n
      by (intro bexI [of _ "f(n := a)"]) (auto simp: f_def Q_def A_def)
    ultimately show False by blast
  qed
qed

lemma higman:
  assumes "almost_full_on P A"
  shows "almost_full_on (list_emb P) (lists A)"
proof
  interpret minimal_element strict_suffix "lists A"
    by (unfold_locales) (intro po_on_strict_suffix wfp_on_strict_suffix)+
  fix f presume "f \<in> SEQ (lists A)"
  with qo_on_LEXEQ [OF po_on_imp_transp_on [OF po_on_strict_suffix]] and dc_on_LEXEQ and open_on_good
    show "good (list_emb P) f"
  proof (induct rule: open_induct_on)
    case (less f)
    define h where "h i = hd (f i)" for i
    show ?case
    proof (cases "\<exists>i. f i = []")
      case False
      then have ne: "\<forall>i. f i \<noteq> []" by auto
      with \<open>f \<in> SEQ (lists A)\<close> have "\<forall>i. h i \<in> A" by (auto simp: h_def ne_lists)
      from almost_full_on_imp_homogeneous_subseq [OF assms this]
      obtain \<phi> :: "nat \<Rightarrow> nat" where mono: "\<And>i j. i < j \<Longrightarrow> \<phi> i < \<phi> j"
        and P: "\<And>i j. i < j \<Longrightarrow> P (h (\<phi> i)) (h (\<phi> j))" by blast
      define f' where "f' i = (if i < \<phi> 0 then f i else tl (f (\<phi> (i - \<phi> 0))))" for i
      have f': "f' \<in> SEQ (lists A)" using ne and \<open>f \<in> SEQ (lists A)\<close>
        by (auto simp: f'_def dest: list.set_sel)
      have [simp]: "\<And>i. \<phi> 0 \<le> i \<Longrightarrow> h (\<phi> (i - \<phi> 0)) # f' i = f (\<phi> (i - \<phi> 0))"
        "\<And>i. i < \<phi> 0 \<Longrightarrow> f' i = f i" using ne by (auto simp: f'_def h_def)
      moreover have "strict_suffix (f' (\<phi> 0)) (f (\<phi> 0))" using ne by (auto simp: f'_def)
      ultimately have "LEX strict_suffix f' f" by (auto simp: LEX_def)
      with LEX_imp_not_LEX [OF this] have "strict (LEXEQ strict_suffix) f' f"
        using po_on_strict_suffix [of UNIV] unfolding po_on_def irreflp_on_def transp_on_def by blast
      from less(2) [OF f' this] have "good (list_emb P) f'" .
      then obtain i j where "i < j" and emb: "list_emb P (f' i) (f' j)" by (auto simp: good_def)
      consider "j < \<phi> 0" | "\<phi> 0 \<le> i" | "i < \<phi> 0" and "\<phi> 0 \<le> j" by arith
      then show ?thesis
      proof (cases)
        case 1 with \<open>i < j\<close> and emb show ?thesis by (auto simp: good_def)
      next
        case 2
        with \<open>i < j\<close> and P have "P (h (\<phi> (i - \<phi> 0))) (h (\<phi> (j - \<phi> 0)))" by auto
        with emb have "list_emb P (h (\<phi> (i - \<phi> 0)) # f' i) (h (\<phi> (j - \<phi> 0)) # f' j)" by auto
        then have "list_emb P (f (\<phi> (i - \<phi> 0))) (f (\<phi> (j - \<phi> 0)))" using 2 and \<open>i < j\<close> by auto
        moreover with 2 and \<open>i <j\<close> have "\<phi> (i - \<phi> 0) < \<phi> (j - \<phi> 0)" using mono by auto
        ultimately show ?thesis by (auto simp: good_def)
      next
        case 3
        with emb have "list_emb P (f i) (f' j)" by auto
        moreover have "f (\<phi> (j - \<phi> 0)) = h (\<phi> (j - \<phi> 0)) # f' j" using 3 by auto
        ultimately have "list_emb P (f i) (f (\<phi> (j - \<phi> 0)))" by auto
        moreover have "i < \<phi> (j - \<phi> 0)" using mono [of 0 "j - \<phi> 0"] and 3 by force
        ultimately show ?thesis by (auto simp: good_def)
      qed
    qed auto
  qed
qed blast

end
