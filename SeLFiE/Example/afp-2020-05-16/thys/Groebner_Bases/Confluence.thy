(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Properties of Binary Relations\<close>

theory Confluence
  imports "Abstract-Rewriting.Abstract_Rewriting" "Open_Induction.Restricted_Predicates"
begin

text \<open>This theory formalizes some general properties of binary relations, in particular a very weak
  sufficient condition for a relation to be Church-Rosser.\<close>

(* Maybe one could build upon "Decreasing_Diagrams" / "Decreasing_Diagrams_II" from the AFP? *)

subsection \<open>@{const wfp_on}\<close>

(* Probably the converse direction holds, too. *)
lemma wfp_on_imp_wfP:
  assumes "wfp_on r A"
  shows "wfP (\<lambda>x y. r x y \<and> x \<in> A \<and> y \<in> A)" (is "wfP ?r")
proof (simp add: wfP_def wf_def, intro allI impI)
  fix P x
  assume "\<forall>x. (\<forall>y. r y x \<and> y \<in> A \<and> x \<in> A \<longrightarrow> P y) \<longrightarrow> P x"
  hence *: "\<And>x. (\<And>y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> r y x \<Longrightarrow> P y) \<Longrightarrow> P x" by blast
  from assms have **: "\<And>a. a \<in> A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> r y x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"
    by (rule wfp_on_induct) blast+
  show "P x"
  proof (cases "x \<in> A")
    case True
    from this * show ?thesis by (rule **)
  next
    case False
    show ?thesis
    proof (rule *)
      fix y
      assume "x \<in> A"
      with False show "P y" ..
    qed
  qed
qed

lemma wfp_onI_min:
  assumes "\<And>x Q. x \<in> Q \<Longrightarrow> Q \<subseteq> A \<Longrightarrow> \<exists>z\<in>Q. \<forall>y\<in>A. r y z \<longrightarrow> y \<notin> Q"
  shows "wfp_on r A"
proof (intro inductive_on_imp_wfp_on minimal_imp_inductive_on allI impI)
  fix Q x
  assume "x \<in> Q \<and> Q \<subseteq> A"
  hence "x \<in> Q" and "Q \<subseteq> A" by simp_all
  hence "\<exists>z\<in>Q. \<forall>y\<in>A. r y z \<longrightarrow> y \<notin> Q" by (rule assms)
  then obtain z where "z \<in> Q" and 1: "\<And>y. y \<in> A \<Longrightarrow> r y z \<Longrightarrow> y \<notin> Q" by blast
  show "\<exists>z\<in>Q. \<forall>y. r y z \<longrightarrow> y \<notin> Q"
  proof (intro bexI allI impI)
    fix y
    assume "r y z"
    show "y \<notin> Q"
    proof (cases "y \<in> A")
      case True
      thus ?thesis using \<open>r y z\<close> by (rule 1)
    next
      case False
      with \<open>Q \<subseteq> A\<close> show ?thesis by blast
    qed
  qed fact
qed

lemma wfp_onE_min:
  assumes "wfp_on r A" and "x \<in> Q" and "Q \<subseteq> A"
  obtains z where "z \<in> Q" and "\<And>y. r y z \<Longrightarrow> y \<notin> Q"
  using wfp_on_imp_minimal[OF assms(1)] assms(2, 3) by blast

lemma wfp_onI_chain: "\<not> (\<exists>f. \<forall>i. f i \<in> A \<and> r (f (Suc i)) (f i)) \<Longrightarrow> wfp_on r A"
  by (simp add: wfp_on_def)

lemma finite_minimalE:
  assumes "finite A" and "A \<noteq> {}" and "irreflp rel" and "transp rel"
  obtains a where "a \<in> A" and "\<And>b. rel b a \<Longrightarrow> b \<notin> A"
  using assms(1, 2)
proof (induct arbitrary: thesis)
  case empty
  from empty(2) show ?case by simp
next
  case (insert a A)
  show ?case
  proof (cases "A = {}")
    case True
    show ?thesis
    proof (rule insert(4))
      fix b
      assume "rel b a"
      with assms(3) show "b \<notin> insert a A" by (auto simp: True irreflp_def)
    qed simp
  next
    case False
    with insert(3) obtain z where "z \<in> A" and *: "\<And>b. rel b z \<Longrightarrow> b \<notin> A" by blast
    show ?thesis
    proof (cases "rel a z")
      case True
      show ?thesis
      proof (rule insert(4))
        fix b
        assume "rel b a"
        with assms(4) have "rel b z" using \<open>rel a z\<close> by (rule transpD)
        hence "b \<notin> A" by (rule *)
        moreover from \<open>rel b a\<close> assms(3) have "b \<noteq> a" by (auto simp: irreflp_def)
        ultimately show "b \<notin> insert a A" by simp
      qed simp
    next
      case False
      show ?thesis
      proof (rule insert(4))
        fix b
        assume "rel b z"
        hence "b \<notin> A" by (rule *)
        moreover from \<open>rel b z\<close> False have "b \<noteq> a" by blast
        ultimately show "b \<notin> insert a A" by simp
      next
        from \<open>z \<in> A\<close> show "z \<in> insert a A" by simp
      qed
    qed
  qed
qed

lemma wfp_on_finite:
  assumes "irreflp rel" and "transp rel" and "finite A"
  shows "wfp_on rel A"
proof (rule wfp_onI_min)
  fix x Q
  assume "x \<in> Q" and "Q \<subseteq> A"
  from this(2) assms(3) have "finite Q" by (rule finite_subset)
  moreover from \<open>x \<in> Q\<close> have "Q \<noteq> {}" by blast
  ultimately obtain z where "z \<in> Q" and "\<And>y. rel y z \<Longrightarrow> y \<notin> Q" using assms(1, 2)
    by (rule finite_minimalE) blast
  thus "\<exists>z\<in>Q. \<forall>y\<in>A. rel y z \<longrightarrow> y \<notin> Q" by blast
qed

subsection \<open>Relations\<close>

locale relation = fixes r::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>" 50)
begin

abbreviation rtc::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>\<^sup>*" 50)
  where "rtc a b \<equiv> r\<^sup>*\<^sup>* a b"

abbreviation sc::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<leftrightarrow>" 50)
  where "sc a b \<equiv> a \<rightarrow> b \<or> b \<rightarrow> a"

definition is_final::"'a \<Rightarrow> bool" where
  "is_final a \<equiv> \<not> (\<exists>b. r a b)"

definition srtc::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<leftrightarrow>\<^sup>*" 50) where
  "srtc a b \<equiv> sc\<^sup>*\<^sup>* a b"
definition cs::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<down>\<^sup>*" 50) where
  "cs a b \<equiv> (\<exists>s. (a \<rightarrow>\<^sup>* s) \<and> (b \<rightarrow>\<^sup>* s))"

definition is_confluent_on :: "'a set \<Rightarrow> bool"
  where "is_confluent_on A \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b1 b2. (a \<rightarrow>\<^sup>* b1 \<and> a \<rightarrow>\<^sup>* b2) \<longrightarrow> b1 \<down>\<^sup>* b2)"

definition is_confluent :: bool
  where "is_confluent \<equiv> is_confluent_on UNIV"

definition is_loc_confluent :: bool
  where "is_loc_confluent \<equiv> (\<forall>a b1 b2. (a \<rightarrow> b1 \<and> a \<rightarrow> b2) \<longrightarrow> b1 \<down>\<^sup>* b2)"

definition is_ChurchRosser :: bool
  where "is_ChurchRosser \<equiv> (\<forall>a b. a \<leftrightarrow>\<^sup>* b \<longrightarrow> a \<down>\<^sup>* b)"

definition dw_closed :: "'a set \<Rightarrow> bool"
  where "dw_closed A \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b. a \<rightarrow> b \<longrightarrow> b \<in> A)"

lemma dw_closedI [intro]:
  assumes "\<And>a b. a \<in> A \<Longrightarrow> a \<rightarrow> b \<Longrightarrow> b \<in> A"
  shows "dw_closed A"
  unfolding dw_closed_def using assms by auto

lemma dw_closedD:
  assumes "dw_closed A" and "a \<in> A" and "a \<rightarrow> b"
  shows "b \<in> A"
  using assms unfolding dw_closed_def by auto

lemma dw_closed_rtrancl:
  assumes "dw_closed A" and "a \<in> A" and "a \<rightarrow>\<^sup>* b"
  shows "b \<in> A"
  using assms(3)
proof (induct b)
  case base
  from assms(2) show ?case .
next
  case (step y z)
  from assms(1) step(3) step(2) show ?case by (rule dw_closedD)
qed

lemma dw_closed_empty: "dw_closed {}"
  by (rule, simp)

lemma dw_closed_UNIV: "dw_closed UNIV"
  by (rule, intro UNIV_I)

subsection \<open>Setup for Connection to Theory @{theory "Abstract-Rewriting.Abstract_Rewriting"}\<close>

abbreviation (input) relset::"('a * 'a) set" where
  "relset \<equiv> {(x, y). x \<rightarrow> y}"

lemma rtc_rtranclI:
  assumes "a \<rightarrow>\<^sup>* b"
  shows "(a, b) \<in> relset\<^sup>*"
using assms by (simp only: Enum.rtranclp_rtrancl_eq)

lemma final_NF: "(is_final a) = (a \<in> NF relset)"
unfolding is_final_def NF_def by simp

lemma sc_symcl: "(a \<leftrightarrow> b) = ((a, b) \<in> relset\<^sup>\<leftrightarrow>)"
by simp

lemma srtc_conversion: "(a \<leftrightarrow>\<^sup>* b) = ((a, b) \<in> relset\<^sup>\<leftrightarrow>\<^sup>*)"
proof -
  have "{(a, b). (a, b) \<in> {(x, y). x \<rightarrow> y}\<^sup>\<leftrightarrow>} = {(a, b). a \<rightarrow> b}\<^sup>\<leftrightarrow>" by auto
  thus ?thesis unfolding srtc_def conversion_def sc_symcl Enum.rtranclp_rtrancl_eq by simp
qed

lemma cs_join: "(a \<down>\<^sup>* b) = ((a, b) \<in> relset\<^sup>\<down>)"
  unfolding cs_def join_def by (auto simp add: Enum.rtranclp_rtrancl_eq rtrancl_converse)

lemma confluent_CR: "is_confluent = CR relset"
  by (auto simp add: is_confluent_def is_confluent_on_def CR_defs Enum.rtranclp_rtrancl_eq cs_join)

lemma ChurchRosser_conversion: "is_ChurchRosser = (relset\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> relset\<^sup>\<down>)"
  by (auto simp add: is_ChurchRosser_def cs_join srtc_conversion)

lemma loc_confluent_WCR:
  shows "is_loc_confluent = WCR relset"
unfolding is_loc_confluent_def WCR_defs by (auto simp add: cs_join)

lemma wf_converse:
  shows "(wfP r^--1) = (wf (relset\<inverse>))"
unfolding wfP_def converse_def by simp

lemma wf_SN:
  shows "(wfP r^--1) = (SN relset)"
unfolding wf_converse wf_iff_no_infinite_down_chain SN_on_def by auto

subsection \<open>Simple Lemmas\<close>

lemma rtrancl_is_final:
  assumes "a \<rightarrow>\<^sup>* b" and "is_final a"
  shows "a = b"
proof -
  from rtranclpD[OF \<open>a \<rightarrow>\<^sup>* b\<close>] show ?thesis
  proof
    assume "a \<noteq> b \<and> (\<rightarrow>)\<^sup>+\<^sup>+ a b"
    hence "(\<rightarrow>)\<^sup>+\<^sup>+ a b" by simp
    from \<open>is_final a\<close> final_NF have "a \<in> NF relset" by simp
    from NF_no_trancl_step[OF this] have "(a, b) \<notin> {(x, y). x \<rightarrow> y}\<^sup>+" ..
    thus ?thesis using \<open>(\<rightarrow>)\<^sup>+\<^sup>+ a b\<close> unfolding tranclp_unfold ..
  qed
qed

lemma cs_refl:
  shows "x \<down>\<^sup>* x"
unfolding cs_def
proof
  show "x \<rightarrow>\<^sup>* x \<and> x \<rightarrow>\<^sup>* x" by simp
qed

lemma cs_sym:
  assumes "x \<down>\<^sup>* y"
  shows "y \<down>\<^sup>* x"
using assms unfolding cs_def
proof
  fix z
  assume a: "x \<rightarrow>\<^sup>* z \<and> y \<rightarrow>\<^sup>* z"
  show "\<exists>s. y \<rightarrow>\<^sup>* s \<and> x \<rightarrow>\<^sup>* s"
  proof
    from a show "y \<rightarrow>\<^sup>* z \<and> x \<rightarrow>\<^sup>* z" by simp
  qed
qed

lemma rtc_implies_cs:
  assumes "x \<rightarrow>\<^sup>* y"
  shows "x \<down>\<^sup>* y"
proof -
  from joinI_left[OF rtc_rtranclI[OF assms]] cs_join show ?thesis by simp
qed

lemma rtc_implies_srtc:
  assumes "a \<rightarrow>\<^sup>* b"
  shows "a \<leftrightarrow>\<^sup>* b"
proof -
  from conversionI'[OF rtc_rtranclI[OF assms]] srtc_conversion show ?thesis by simp
qed

lemma srtc_symmetric:
  assumes "a \<leftrightarrow>\<^sup>* b"
  shows "b \<leftrightarrow>\<^sup>* a"
proof -
  from symD[OF conversion_sym[of relset], of a b] assms srtc_conversion show ?thesis by simp
qed

lemma srtc_transitive:
  assumes "a \<leftrightarrow>\<^sup>* b" and "b \<leftrightarrow>\<^sup>* c"
  shows "a \<leftrightarrow>\<^sup>* c"
proof -
  from rtranclp_trans[of "(\<leftrightarrow>)" a b c] assms show "a \<leftrightarrow>\<^sup>* c" unfolding srtc_def .
qed

lemma cs_implies_srtc:
  assumes "a \<down>\<^sup>* b"
  shows "a \<leftrightarrow>\<^sup>* b"
proof -
  from assms cs_join have "(a, b) \<in> relset\<^sup>\<down>" by simp
  hence "(a, b) \<in> relset\<^sup>\<leftrightarrow>\<^sup>*" using join_imp_conversion by auto
  thus ?thesis using srtc_conversion by simp
qed

lemma confluence_equiv_ChurchRosser: "is_confluent = is_ChurchRosser"
  by (simp only: ChurchRosser_conversion confluent_CR, fact CR_iff_conversion_imp_join)

corollary confluence_implies_ChurchRosser:
  assumes is_confluent
  shows is_ChurchRosser
  using assms by (simp only: confluence_equiv_ChurchRosser)

lemma ChurchRosser_unique_final:
  assumes "is_ChurchRosser" and "a \<rightarrow>\<^sup>* b1" and "a \<rightarrow>\<^sup>* b2" and "is_final b1" and "is_final b2"
  shows "b1 = b2"
proof -
  from \<open>is_ChurchRosser\<close> confluence_equiv_ChurchRosser confluent_CR have "CR relset" by simp
  from CR_imp_UNF[OF this] assms show ?thesis unfolding UNF_defs normalizability_def
    by (auto simp add: Enum.rtranclp_rtrancl_eq final_NF)
qed

lemma wf_on_imp_nf_ex:
  assumes "wfp_on ((\<rightarrow>)\<inverse>\<inverse>) A" and "dw_closed A" and "a \<in> A"
  obtains b where "a \<rightarrow>\<^sup>* b" and "is_final b"
proof -
  let ?A = "{b\<in>A. a \<rightarrow>\<^sup>* b}"
  note assms(1)
  moreover from assms(3) have "a \<in> ?A" by simp
  moreover have "?A \<subseteq> A" by auto
  ultimately show ?thesis
  proof (rule wfp_onE_min)
    fix z
    assume "z \<in> ?A" and "\<And>y. (\<rightarrow>)\<inverse>\<inverse> y z \<Longrightarrow> y \<notin> ?A"
    from this(2) have *: "\<And>y. z \<rightarrow> y \<Longrightarrow> y \<notin> ?A" by simp
    from \<open>z \<in> ?A\<close> have "z \<in> A" and "a \<rightarrow>\<^sup>* z" by simp_all
    show thesis
    proof (rule, fact)
      show "is_final z" unfolding is_final_def
      proof
        assume "\<exists>y. z \<rightarrow> y"
        then obtain y where "z \<rightarrow> y" ..
        hence "y \<notin> ?A" by (rule *)
        moreover from assms(2) \<open>z \<in> A\<close> \<open>z \<rightarrow> y\<close> have "y \<in> A" by (rule dw_closedD)
        ultimately have "\<not> (a \<rightarrow>\<^sup>* y)" by simp
        with rtranclp_trans[OF \<open>a \<rightarrow>\<^sup>* z\<close>, of y] \<open>z \<rightarrow> y\<close> show False by auto
      qed
    qed
  qed
qed
  
lemma unique_nf_imp_confluence_on:
  assumes major: "\<And>a b1 b2. a \<in> A \<Longrightarrow> (a \<rightarrow>\<^sup>* b1) \<Longrightarrow> (a \<rightarrow>\<^sup>* b2) \<Longrightarrow> is_final b1 \<Longrightarrow> is_final b2 \<Longrightarrow> b1 = b2"
    and wf: "wfp_on ((\<rightarrow>)\<inverse>\<inverse>) A" and dw: "dw_closed A"
  shows "is_confluent_on A"
  unfolding is_confluent_on_def
proof (intro ballI allI impI)
  fix a b1 b2
  assume "a \<rightarrow>\<^sup>* b1 \<and> a \<rightarrow>\<^sup>* b2"
  hence "a \<rightarrow>\<^sup>* b1" and "a \<rightarrow>\<^sup>* b2" by simp_all
  assume "a \<in> A"
  from dw this \<open>a \<rightarrow>\<^sup>* b1\<close> have "b1 \<in> A" by (rule dw_closed_rtrancl)
  from wf dw this obtain c1 where "b1 \<rightarrow>\<^sup>* c1" and "is_final c1" by (rule wf_on_imp_nf_ex)
  from dw \<open>a \<in> A\<close> \<open>a \<rightarrow>\<^sup>* b2\<close> have "b2 \<in> A" by (rule dw_closed_rtrancl)
  from wf dw this obtain c2 where "b2 \<rightarrow>\<^sup>* c2" and "is_final c2" by (rule wf_on_imp_nf_ex)
  have "c1 = c2"
    by (rule major, fact, rule rtranclp_trans[OF \<open>a \<rightarrow>\<^sup>* b1\<close>], fact, rule rtranclp_trans[OF \<open>a \<rightarrow>\<^sup>* b2\<close>], fact+)
  show "b1 \<down>\<^sup>* b2" unfolding cs_def
  proof (intro exI, intro conjI)
    show "b1 \<rightarrow>\<^sup>* c1" by fact
  next
    show "b2 \<rightarrow>\<^sup>* c1" unfolding \<open>c1 = c2\<close> by fact
  qed
qed

corollary wf_imp_nf_ex:
  assumes "wfP ((\<rightarrow>)\<inverse>\<inverse>)"
  obtains b where "a \<rightarrow>\<^sup>* b" and "is_final b"
proof -
  from assms have "wfp_on (r^--1) UNIV" by simp
  moreover note dw_closed_UNIV
  moreover have "a \<in> UNIV" ..
  ultimately obtain b where "a \<rightarrow>\<^sup>* b" and "is_final b" by (rule wf_on_imp_nf_ex)
  thus ?thesis ..
qed

corollary unique_nf_imp_confluence:
  assumes "\<And>a b1 b2. (a \<rightarrow>\<^sup>* b1) \<Longrightarrow> (a \<rightarrow>\<^sup>* b2) \<Longrightarrow> is_final b1 \<Longrightarrow> is_final b2 \<Longrightarrow> b1 = b2"
    and "wfP ((\<rightarrow>)\<inverse>\<inverse>)"
  shows "is_confluent"
  unfolding is_confluent_def
  by (rule unique_nf_imp_confluence_on, erule assms(1), assumption+, simp add: assms(2), fact dw_closed_UNIV)

end (*relation*)

subsection \<open>Advanced Results and the Generalized Newman Lemma\<close>

definition relbelow_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
  where "relbelow_on A ord z rel a b \<equiv> (a \<in> A \<and> b \<in> A \<and> rel a b \<and> ord a z \<and> ord b z)"

definition cbelow_on_1 :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
  where "cbelow_on_1 A ord z rel \<equiv> (relbelow_on A ord z rel)\<^sup>+\<^sup>+"

definition cbelow_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
  where "cbelow_on A ord z rel a b \<equiv> (a = b \<and> b \<in> A \<and> ord b z) \<or> cbelow_on_1 A ord z rel a b"

text \<open>Note that @{const cbelow_on} cannot be defined as the reflexive-transitive closure of
  @{const relbelow_on}, since it is in general not reflexive!\<close>

definition is_loc_connective_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_loc_connective_on A ord r \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b1 b2. r a b1 \<and> r a b2 \<longrightarrow> cbelow_on A ord a (relation.sc r) b1 b2)"

text \<open>Note that @{const wfp_on} is @{emph \<open>not\<close>} the same as @{const SN_on}, since in the definition
  of @{const SN_on} only the @{emph \<open>first\<close>} element of the chain must be in the set.\<close>

lemma cbelow_on_first_below:
  assumes "cbelow_on A ord z rel a b"
  shows "ord a z"
  using assms unfolding cbelow_on_def
proof
  assume "cbelow_on_1 A ord z rel a b"
  thus "ord a z" unfolding cbelow_on_1_def by (induct rule: tranclp_induct, simp add: relbelow_on_def)
qed simp

lemma cbelow_on_second_below:
  assumes "cbelow_on A ord z rel a b"
  shows "ord b z"
  using assms unfolding cbelow_on_def
proof
  assume "cbelow_on_1 A ord z rel a b"
  thus "ord b z" unfolding cbelow_on_1_def
    by (induct rule: tranclp_induct, simp_all add: relbelow_on_def)
qed simp

lemma cbelow_on_first_in:
  assumes "cbelow_on A ord z rel a b"
  shows "a \<in> A"
  using assms unfolding cbelow_on_def
proof
  assume "cbelow_on_1 A ord z rel a b"
  thus ?thesis unfolding cbelow_on_1_def by (induct rule: tranclp_induct, simp add: relbelow_on_def)
qed simp

lemma cbelow_on_second_in:
  assumes "cbelow_on A ord z rel a b"
  shows "b \<in> A"
  using assms unfolding cbelow_on_def
proof
  assume "cbelow_on_1 A ord z rel a b"
  thus ?thesis unfolding cbelow_on_1_def
    by (induct rule: tranclp_induct, simp_all add: relbelow_on_def)
qed simp

lemma cbelow_on_intro [intro]:
  assumes main: "cbelow_on A ord z rel a b" and "c \<in> A" and "rel b c" and "ord c z"
  shows "cbelow_on A ord z rel a c"
proof -
  from main have "b \<in> A" by (rule cbelow_on_second_in)
  from main show ?thesis unfolding cbelow_on_def
  proof (intro disjI2)
    assume cases: "(a = b \<and> b \<in> A \<and> ord b z) \<or> cbelow_on_1 A ord z rel a b"
    from \<open>b \<in> A\<close> \<open>c \<in> A\<close> \<open>rel b c\<close> \<open>ord c z\<close> cbelow_on_second_below[OF main]
      have bc: "relbelow_on A ord z rel b c" by (simp add: relbelow_on_def)
    from cases show "cbelow_on_1 A ord z rel a c"
    proof
      assume "a = b \<and> b \<in> A \<and> ord b z"
      from this bc have "relbelow_on A ord z rel a c" by simp
      thus ?thesis by (simp add: cbelow_on_1_def)
    next
      assume "cbelow_on_1 A ord z rel a b"
      from this bc show ?thesis unfolding cbelow_on_1_def by (rule tranclp.intros(2))
    qed
  qed
qed

lemma cbelow_on_induct [consumes 1, case_names base step]:
  assumes a: "cbelow_on A ord z rel a b"
    and base: "a \<in> A \<Longrightarrow> ord a z \<Longrightarrow> P a"
    and ind: "\<And>b c. [| cbelow_on A ord z rel a b; rel b c; c \<in> A; ord c z; P b |] ==> P c"
  shows "P b"
  using a unfolding cbelow_on_def
proof
  assume "a = b \<and> b \<in> A \<and> ord b z"
  from this base show "P b" by simp
next
  assume "cbelow_on_1 A ord z rel a b"
  thus "P b" unfolding cbelow_on_1_def
  proof (induct x\<equiv>a b)
    fix b
    assume "relbelow_on A ord z rel a b"
    hence "rel a b" and "a \<in> A" and "b \<in> A" and "ord a z" and "ord b z"
      by (simp_all add: relbelow_on_def)
    hence "cbelow_on A ord z rel a a" by (simp add: cbelow_on_def)
    from this \<open>rel a b\<close> \<open>b \<in> A\<close> \<open>ord b z\<close> base[OF \<open>a \<in> A\<close> \<open>ord a z\<close>] show "P b" by (rule ind)
  next
    fix b c
    assume IH: "(relbelow_on A ord z rel)\<^sup>+\<^sup>+ a b" and "P b" and "relbelow_on A ord z rel b c"
    hence "rel b c" and "b \<in> A" and "c \<in> A" and "ord b z" and "ord c z"
      by (simp_all add: relbelow_on_def)
    from IH have "cbelow_on A ord z rel a b" by (simp add: cbelow_on_def cbelow_on_1_def)
    from this \<open>rel b c\<close> \<open>c \<in> A\<close> \<open>ord c z\<close> \<open>P b\<close> show "P c" by (rule ind)
  qed
qed

lemma cbelow_on_symmetric:
  assumes main: "cbelow_on A ord z rel a b" and "symp rel"
  shows "cbelow_on A ord z rel b a"
  using main unfolding cbelow_on_def
proof
  assume a1: "a = b \<and> b \<in> A \<and> ord b z"
  show "b = a \<and> a \<in> A \<and> ord a z \<or> cbelow_on_1 A ord z rel b a"
  proof
    from a1 show "b = a \<and> a \<in> A \<and> ord a z" by simp
  qed
next
  assume a2: "cbelow_on_1 A ord z rel a b"
  show "b = a \<and> a \<in> A \<and> ord a z \<or> cbelow_on_1 A ord z rel b a"
  proof (rule disjI2)
    from \<open>symp rel\<close> have "symp (relbelow_on A ord z rel)" unfolding symp_def
    proof (intro allI impI)
      fix x y
      assume rel_sym: "\<forall>x y. rel x y \<longrightarrow> rel y x"
      assume "relbelow_on A ord z rel x y"
      hence "rel x y" and "x \<in> A" and "y \<in> A" and "ord x z" and "ord y z"
        by (simp_all add: relbelow_on_def)
      show "relbelow_on A ord z rel y x" unfolding relbelow_on_def
      proof (intro conjI)
        from rel_sym \<open>rel x y\<close> show "rel y x" by simp
      qed fact+
    qed
    from sym_trancl[to_pred, OF this] a2 show "cbelow_on_1 A ord z rel b a"
      by (simp add: symp_def cbelow_on_1_def)
  qed
qed

lemma cbelow_on_transitive:
  assumes "cbelow_on A ord z rel a b" and "cbelow_on A ord z rel b c"
  shows "cbelow_on A ord z rel a c"
proof (induct rule: cbelow_on_induct[OF \<open>cbelow_on A ord z rel b c\<close>])
  from \<open>cbelow_on A ord z rel a b\<close> show "cbelow_on A ord z rel a b" .
next
  fix c0 c
  assume "cbelow_on A ord z rel b c0" and "rel c0 c" and "c \<in> A" and "ord c z" and "cbelow_on A ord z rel a c0"
  show "cbelow_on A ord z rel a c" by (rule, fact+)
qed

lemma cbelow_on_mono:
  assumes "cbelow_on A ord z rel a b" and "A \<subseteq> B"
  shows "cbelow_on B ord z rel a b"
  using assms(1)
proof (induct rule: cbelow_on_induct)
  case base
  show ?case by (simp add: cbelow_on_def, intro disjI1 conjI, rule, fact+)
next
  case (step b c)
  from step(3) assms(2) have "c \<in> B" ..
  from step(5) this step(2) step (4) show ?case ..
qed

locale relation_order = relation +
  fixes ord::"'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes A::"'a set"
  assumes trans: "ord x y \<Longrightarrow> ord y z \<Longrightarrow> ord x z"
  assumes wf: "wfp_on ord A"
  assumes refines: "(\<rightarrow>) \<le> ord\<inverse>\<inverse>"
begin

lemma relation_refines:
  assumes "a \<rightarrow> b"
  shows "ord b a"
  using refines assms by auto

lemma relation_wf: "wfp_on (\<rightarrow>)\<inverse>\<inverse> A"
  using subset_refl _ wf
proof (rule wfp_on_mono)
  fix x y
  assume "(\<rightarrow>)\<inverse>\<inverse> x y"
  hence "y \<rightarrow> x" by simp
  with refines have "(ord)\<inverse>\<inverse> y x" ..
  thus "ord x y" by simp
qed

lemma rtc_implies_cbelow_on:
  assumes "dw_closed A" and main: "a \<rightarrow>\<^sup>* b" and "a \<in> A" and "ord a c"
  shows "cbelow_on A ord c (\<leftrightarrow>) a b"
  using main
proof (induct rule: rtranclp_induct)
  from assms(3) assms(4) show "cbelow_on A ord c (\<leftrightarrow>) a a" by (simp add: cbelow_on_def)
next
  fix b0 b
  assume "a \<rightarrow>\<^sup>* b0" and "b0 \<rightarrow> b" and IH: "cbelow_on A ord c (\<leftrightarrow>) a b0"
  from assms(1) assms(3) \<open>a \<rightarrow>\<^sup>* b0\<close> have "b0 \<in> A" by (rule dw_closed_rtrancl)
  from assms(1) this \<open>b0 \<rightarrow> b\<close> have "b \<in> A" by (rule dw_closedD)
  show "cbelow_on A ord c (\<leftrightarrow>) a b"
  proof
    from \<open>b0 \<rightarrow> b\<close> show "b0 \<leftrightarrow> b" by simp
  next
    from relation_refines[OF \<open>b0 \<rightarrow> b\<close>] cbelow_on_second_below[OF IH] show "ord b c" by (rule trans)
  qed fact+
qed

lemma cs_implies_cbelow_on:
  assumes "dw_closed A" and "a \<down>\<^sup>* b" and "a \<in> A" and "b \<in> A" and "ord a c" and "ord b c"
  shows "cbelow_on A ord c (\<leftrightarrow>) a b"
proof -
  from \<open>a \<down>\<^sup>* b\<close> obtain s where "a \<rightarrow>\<^sup>* s" and "b \<rightarrow>\<^sup>* s" unfolding cs_def by auto
  have sym: "symp (\<leftrightarrow>)" unfolding symp_def
  proof (intro allI, intro impI)
    fix x y
    assume "x \<leftrightarrow> y"
    thus "y \<leftrightarrow> x" by auto
  qed
  from assms(1) \<open>a \<rightarrow>\<^sup>* s\<close> assms(3) assms(5) have "cbelow_on A ord c (\<leftrightarrow>) a s"
    by (rule rtc_implies_cbelow_on)
  also have "cbelow_on A ord c (\<leftrightarrow>) s b"
  proof (rule cbelow_on_symmetric)
    from assms(1) \<open>b \<rightarrow>\<^sup>* s\<close> assms(4) assms(6) show "cbelow_on A ord c (\<leftrightarrow>) b s"
      by (rule rtc_implies_cbelow_on)
  qed fact
  finally(cbelow_on_transitive) show ?thesis .
qed

text \<open>The generalized Newman lemma, taken from @{cite Winkler1983}:\<close>

lemma loc_connectivity_implies_confluence:
  assumes "is_loc_connective_on A ord (\<rightarrow>)" and "dw_closed A"
  shows "is_confluent_on A"
  using assms(1) unfolding is_loc_connective_on_def is_confluent_on_def
proof (intro ballI allI impI)
  fix z x y::'a
  assume "\<forall>a\<in>A. \<forall>b1 b2. a \<rightarrow> b1 \<and> a \<rightarrow> b2 \<longrightarrow> cbelow_on A ord a (\<leftrightarrow>) b1 b2"
  hence A: "\<And>a b1 b2. a \<in> A \<Longrightarrow> a \<rightarrow> b1 \<Longrightarrow> a \<rightarrow> b2 \<Longrightarrow> cbelow_on A ord a (\<leftrightarrow>) b1 b2" by simp
  assume "z \<in> A" and "z \<rightarrow>\<^sup>* x \<and> z \<rightarrow>\<^sup>* y"
  with wf show "x \<down>\<^sup>* y"
  proof (induct z arbitrary: x y rule: wfp_on_induct)
    fix z x y::'a
    assume IH: "\<And>z0 x0 y0. z0 \<in> A \<Longrightarrow> ord z0 z \<Longrightarrow> z0 \<rightarrow>\<^sup>* x0 \<and> z0 \<rightarrow>\<^sup>* y0 \<Longrightarrow> x0 \<down>\<^sup>* y0"
      and "z \<rightarrow>\<^sup>* x \<and> z \<rightarrow>\<^sup>* y"
    hence "z \<rightarrow>\<^sup>* x" and "z \<rightarrow>\<^sup>* y" by auto
    assume "z \<in> A"
    from converse_rtranclpE[OF \<open>z \<rightarrow>\<^sup>* x\<close>] obtain x1 where "x = z \<or> (z \<rightarrow> x1 \<and> x1 \<rightarrow>\<^sup>* x)" by auto
    thus "x \<down>\<^sup>* y"
    proof
      assume "x = z"
      show ?thesis unfolding cs_def
      proof
        from \<open>x = z\<close> \<open>z \<rightarrow>\<^sup>* y\<close> show "x \<rightarrow>\<^sup>* y \<and> y \<rightarrow>\<^sup>* y" by simp
      qed
    next
      assume "z \<rightarrow> x1 \<and> x1 \<rightarrow>\<^sup>* x"
      hence "z \<rightarrow> x1" and "x1 \<rightarrow>\<^sup>* x" by auto
      from assms(2) \<open>z \<in> A\<close> this(1) have "x1 \<in> A" by (rule dw_closedD)
      from converse_rtranclpE[OF \<open>z \<rightarrow>\<^sup>* y\<close>] obtain y1 where "y = z \<or> (z \<rightarrow> y1 \<and> y1 \<rightarrow>\<^sup>* y)" by auto
      thus ?thesis
      proof
        assume "y = z"
        show ?thesis unfolding cs_def
        proof
          from \<open>y = z\<close> \<open>z \<rightarrow>\<^sup>* x\<close> show "x \<rightarrow>\<^sup>* x \<and> y \<rightarrow>\<^sup>* x" by simp
        qed
      next
        assume "z \<rightarrow> y1 \<and> y1 \<rightarrow>\<^sup>* y"
        hence "z \<rightarrow> y1" and "y1 \<rightarrow>\<^sup>* y" by auto
        from assms(2) \<open>z \<in> A\<close> this(1) have "y1 \<in> A" by (rule dw_closedD)
        have "x1 \<down>\<^sup>* y1"
        proof (induct rule: cbelow_on_induct[OF A[OF \<open>z \<in> A\<close> \<open>z \<rightarrow> x1\<close> \<open>z \<rightarrow> y1\<close>]])
          from cs_refl[of x1] show "x1 \<down>\<^sup>* x1" .
        next
          fix b c
          assume "cbelow_on A ord z (\<leftrightarrow>) x1 b" and "b \<leftrightarrow> c" and "c \<in> A" and "ord c z" and "x1 \<down>\<^sup>* b"
          from this(1) have "b \<in> A" by (rule cbelow_on_second_in)
          from \<open>x1 \<down>\<^sup>* b\<close> obtain w1 where "x1 \<rightarrow>\<^sup>* w1" and "b \<rightarrow>\<^sup>* w1" unfolding cs_def by auto
          from \<open>b \<leftrightarrow> c\<close> show "x1 \<down>\<^sup>* c"
          proof
            assume "b \<rightarrow> c"
            hence "b \<rightarrow>\<^sup>* c" by simp
            from \<open>cbelow_on A ord z (\<leftrightarrow>) x1 b\<close> have "ord b z" by (rule cbelow_on_second_below)
            from IH[OF \<open>b \<in> A\<close> this] \<open>b \<rightarrow>\<^sup>* c\<close> \<open>b \<rightarrow>\<^sup>* w1\<close> have "c \<down>\<^sup>* w1" by simp
            then obtain w2 where "c \<rightarrow>\<^sup>* w2" and "w1 \<rightarrow>\<^sup>* w2" unfolding cs_def by auto
            show ?thesis unfolding cs_def
            proof
              from rtranclp_trans[OF \<open>x1 \<rightarrow>\<^sup>* w1\<close> \<open>w1 \<rightarrow>\<^sup>* w2\<close>] \<open>c \<rightarrow>\<^sup>* w2\<close>
                show "x1 \<rightarrow>\<^sup>* w2 \<and> c \<rightarrow>\<^sup>* w2" by simp
            qed
          next
            assume "c \<rightarrow> b"
            hence "c \<rightarrow>\<^sup>* b" by simp
            show ?thesis unfolding cs_def
            proof
              from rtranclp_trans[OF \<open>c \<rightarrow>\<^sup>* b\<close> \<open>b \<rightarrow>\<^sup>* w1\<close>] \<open>x1 \<rightarrow>\<^sup>* w1\<close>
                show "x1 \<rightarrow>\<^sup>* w1 \<and> c \<rightarrow>\<^sup>* w1" by simp
            qed
          qed
        qed
        then obtain w1 where "x1 \<rightarrow>\<^sup>* w1" and "y1 \<rightarrow>\<^sup>* w1" unfolding cs_def by auto
        from IH[OF \<open>x1 \<in> A\<close> relation_refines[OF \<open>z \<rightarrow> x1\<close>]] \<open>x1 \<rightarrow>\<^sup>* x\<close> \<open>x1 \<rightarrow>\<^sup>* w1\<close>
          have "x \<down>\<^sup>* w1" by simp
        then obtain v where "x \<rightarrow>\<^sup>* v" and "w1 \<rightarrow>\<^sup>* v" unfolding cs_def by auto
        from IH[OF \<open>y1 \<in> A\<close> relation_refines[OF \<open>z \<rightarrow> y1\<close>]]
             rtranclp_trans[OF \<open>y1 \<rightarrow>\<^sup>* w1\<close> \<open>w1 \<rightarrow>\<^sup>* v\<close>] \<open>y1 \<rightarrow>\<^sup>* y\<close>
          have "v \<down>\<^sup>* y" by simp
        then obtain w where "v \<rightarrow>\<^sup>* w" and "y \<rightarrow>\<^sup>* w" unfolding cs_def by auto
        show ?thesis unfolding cs_def
        proof
          from rtranclp_trans[OF \<open>x \<rightarrow>\<^sup>* v\<close> \<open>v \<rightarrow>\<^sup>* w\<close>] \<open>y \<rightarrow>\<^sup>* w\<close> show "x \<rightarrow>\<^sup>* w \<and> y \<rightarrow>\<^sup>* w" by simp
        qed
      qed
    qed
  qed
qed

end (* relation_order *)

theorem loc_connectivity_equiv_ChurchRosser:
  assumes "relation_order r ord UNIV"
  shows "relation.is_ChurchRosser r = is_loc_connective_on UNIV ord r"
proof                                                                
  assume "relation.is_ChurchRosser r"
  show "is_loc_connective_on UNIV ord r" unfolding is_loc_connective_on_def
  proof (intro ballI allI impI)
    fix a b1 b2
    assume "r a b1 \<and> r a b2"
    hence "r a b1" and "r a b2" by simp_all
    hence "r\<^sup>*\<^sup>* a b1" and "r\<^sup>*\<^sup>* a b2" by simp_all
    from relation.rtc_implies_srtc[OF \<open>r\<^sup>*\<^sup>* a b1\<close>] have "relation.srtc r b1 a" by (rule relation.srtc_symmetric)
    from relation.srtc_transitive[OF this relation.rtc_implies_srtc[OF \<open>r\<^sup>*\<^sup>* a b2\<close>]] have "relation.srtc r b1 b2" .
    with \<open>relation.is_ChurchRosser r\<close> have "relation.cs r b1 b2" by (simp add: relation.is_ChurchRosser_def)
    from relation_order.cs_implies_cbelow_on[OF assms relation.dw_closed_UNIV this]
      relation_order.relation_refines[OF assms, of a] \<open>r a b1\<close> \<open>r a b2\<close>
      show "cbelow_on UNIV ord a (relation.sc r) b1 b2" by simp
  qed
next
  assume "is_loc_connective_on UNIV ord r"
  from assms this relation.dw_closed_UNIV have "relation.is_confluent_on r UNIV"
    by (rule relation_order.loc_connectivity_implies_confluence)
  hence "relation.is_confluent r" by (simp only: relation.is_confluent_def)
  thus "relation.is_ChurchRosser r" by (simp add: relation.confluence_equiv_ChurchRosser)
qed

end
