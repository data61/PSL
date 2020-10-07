(*  Title:      SetIntervalCut.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

section \<open>Cutting linearly ordered and natural sets\<close>

theory SetIntervalCut
imports SetInterval2
begin

subsection \<open>Set restriction\<close>

text \<open>
  A set to set function \<open>f\<close> is a \<open>set restriction\<close>,
  if there exists a predicate \<open>P\<close>,
  so that for every set \<open>s\<close> the function result \<open>f s\<close>
  contains all its elements fulfilling \<open>P\<close>\<close>

definition set_restriction :: "('a set \<Rightarrow> 'a set) \<Rightarrow> bool"
  where "set_restriction f \<equiv> \<exists>P. \<forall>A. f A = {x \<in> A. P x}"

lemma set_restrictionD: "set_restriction f \<Longrightarrow> \<exists>P. \<forall>A. f A = {x \<in> A. P x}"
unfolding set_restriction_def by blast
lemma set_restrictionD_spec: "set_restriction f \<Longrightarrow> \<exists>P. f A = {x \<in> A. P x}"
unfolding set_restriction_def by blast
lemma set_restrictionI: "f = (\<lambda>A. {x \<in> A. P x}) \<Longrightarrow> set_restriction f"
unfolding set_restriction_def by blast

lemma set_restriction_comp: "
  \<lbrakk> set_restriction f; set_restriction g \<rbrakk> \<Longrightarrow> set_restriction (f \<circ> g)"
apply (unfold set_restriction_def)
apply (elim exE, rename_tac P1 P2)
apply (rule_tac x="\<lambda>x. P1 x \<and> P2 x" in exI)
apply fastforce
done
lemma set_restriction_commute: "
  \<lbrakk> set_restriction f; set_restriction g \<rbrakk> \<Longrightarrow> f (g I) = g (f I)"
unfolding set_restriction_def by fastforce

text \<open>Constructs a set restriction function with the given restriction predicate\<close>
definition
  set_restriction_fun :: "('a \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> 'a set)"
where
  "set_restriction_fun P \<equiv> \<lambda>A. {x \<in> A. P x}"

lemma set_restriction_fun_is_set_restriction: "
  set_restriction (set_restriction_fun P)"
unfolding set_restriction_def set_restriction_fun_def by blast

lemma set_restriction_Int_conv:
  "set_restriction f = (\<exists>B. \<forall>A. f A = A \<inter> B)"
apply (unfold set_restriction_def)
apply (rule iffI)
apply (erule exE, rule_tac x="Collect P" in exI, blast)
apply (erule exE, rule_tac x="\<lambda>x. x \<in> B" in exI, blast)
done

lemma set_restriction_Un: "
  set_restriction f \<Longrightarrow> f (A \<union> B) = f A \<union> f B"
unfolding set_restriction_def by fastforce
lemma set_restriction_Int: "
  set_restriction f \<Longrightarrow> f (A \<inter> B) = f A \<inter> f B"
unfolding set_restriction_def by fastforce
lemma set_restriction_Diff: "
  set_restriction f \<Longrightarrow> f (A - B) = f A - f B"
unfolding set_restriction_def by fastforce
lemma set_restriction_mono: "
  \<lbrakk> set_restriction f; A \<subseteq> B \<rbrakk> \<Longrightarrow> f A \<subseteq> f B"
unfolding set_restriction_def by fastforce
lemma set_restriction_absorb: "
  set_restriction f \<Longrightarrow> f (f A) = f A"
unfolding set_restriction_def by fastforce
lemma set_restriction_empty: "
  set_restriction f \<Longrightarrow> f {} = {}"
unfolding set_restriction_def by blast
lemma set_restriction_non_empty_imp: "
  \<lbrakk> set_restriction f; f A \<noteq> {} \<rbrakk> \<Longrightarrow> A \<noteq> {}"
unfolding set_restriction_def by blast
lemma set_restriction_subset: "
  set_restriction f \<Longrightarrow> f A \<subseteq> A"
unfolding set_restriction_def by blast
lemma set_restriction_finite: "
  \<lbrakk> set_restriction f; finite A \<rbrakk> \<Longrightarrow> finite (f A)"
unfolding set_restriction_def by fastforce
lemma set_restriction_card: "
  \<lbrakk> set_restriction f; finite A \<rbrakk> \<Longrightarrow>
  card (f A) = card A - card {a \<in> A. f {a} = {}}"
apply (unfold set_restriction_def)
apply (subgoal_tac "{a \<in> A. f {a} = {}} \<subseteq> A")
 prefer 2
 apply blast
apply (frule finite_subset, simp)
apply (simp only: card_Diff_subset[symmetric])
apply (rule arg_cong[where f=card])
apply fastforce
done

lemma set_restriction_card_le: "
  \<lbrakk> set_restriction f; finite A \<rbrakk> \<Longrightarrow> card (f A) \<le> card A"
by (simp add: set_restriction_card)

lemma set_restriction_not_in_imp: "
  \<lbrakk> set_restriction f; x \<notin> A \<rbrakk> \<Longrightarrow> x \<notin> f A"
unfolding set_restriction_def by blast

lemma set_restriction_in_imp: "
  \<lbrakk> set_restriction f; x \<in> f A \<rbrakk> \<Longrightarrow> x \<in> A"
unfolding set_restriction_def by blast

lemma set_restriction_fun_singleton: "
  set_restriction_fun P {a} = (if P a then {a} else {})"
unfolding set_restriction_fun_def by force
lemma set_restriction_fun_all_conv: "
  ((set_restriction_fun P) A = A) = (\<forall>x\<in>A. P x)"
unfolding set_restriction_fun_def by blast
lemma set_restriction_fun_empty_conv: "
  ((set_restriction_fun P) A = {}) = (\<forall>x\<in>A. \<not> P x)"
unfolding set_restriction_fun_def by blast


subsection \<open>Cut operators for sets/intervals\<close>

subsubsection \<open>Definitions and basic lemmata for cut operators\<close>

definition cut_le :: "'a::linorder set \<Rightarrow> 'a \<Rightarrow> 'a set"   (infixl "\<down>\<le>" 100)
  where "I \<down>\<le> t \<equiv> {x\<in>I. x \<le> t}"

definition cut_less :: "'a::linorder set \<Rightarrow> 'a \<Rightarrow> 'a set"  (infixl "\<down><" 100)
  where "I \<down>< t \<equiv> {x\<in>I. x < t}"

definition cut_ge :: "'a::linorder set \<Rightarrow> 'a \<Rightarrow> 'a set"  (infixl "\<down>\<ge>" 100)
  where "I \<down>\<ge> t \<equiv> {x\<in>I. t \<le> x}"

definition cut_greater :: "'a::linorder set \<Rightarrow> 'a \<Rightarrow> 'a set"  (infixl "\<down>>" 100)
  where "I \<down>> t \<equiv> {x\<in>I. t < x}"

lemmas i_cut_defs =
  cut_le_def cut_less_def
  cut_ge_def cut_greater_def

lemma cut_le_mem_iff: "x \<in> I \<down>\<le> t = (x \<in> I \<and> x \<le> t)"
by (unfold cut_le_def, blast)

lemma cut_less_mem_iff: "x \<in> I \<down>< t = (x \<in> I \<and> x < t)"
by (unfold cut_less_def, blast)

lemma cut_ge_mem_iff: "x \<in> I \<down>\<ge> t = (x \<in> I \<and> t \<le> x)"
by (unfold cut_ge_def, blast)

lemma cut_greater_mem_iff: "x \<in> I \<down>> t = (x \<in> I \<and> t < x)"
by (unfold cut_greater_def, blast)

lemmas i_cut_mem_iff =
  cut_le_mem_iff cut_less_mem_iff
  cut_ge_mem_iff cut_greater_mem_iff

lemma
  cut_leI [intro!]:      "x \<in> I \<Longrightarrow> x \<le> t \<Longrightarrow> x \<in> I \<down>\<le> t" and
  cut_lessI [intro!]:    "x \<in> I \<Longrightarrow> x < t \<Longrightarrow> x \<in> I \<down>< t" and
  cut_geI [intro!]:      "x \<in> I \<Longrightarrow> x \<ge> t \<Longrightarrow> x \<in> I \<down>\<ge> t" and
  cut_greaterI [intro!]: "x \<in> I \<Longrightarrow> x > t \<Longrightarrow> x \<in> I \<down>> t"
by (simp_all add: i_cut_mem_iff)

lemma
  cut_leE [elim!]:      "x \<in> I \<down>\<le> t \<Longrightarrow> (x \<in> I \<Longrightarrow> x \<le> t \<Longrightarrow> P) \<Longrightarrow> P" and
  cut_lessE [elim!]:    "x \<in> I \<down>< t \<Longrightarrow> (x \<in> I \<Longrightarrow> x < t \<Longrightarrow> P) \<Longrightarrow> P" and
  cut_geE [elim!]:      "x \<in> I \<down>\<ge> t \<Longrightarrow> (x \<in> I \<Longrightarrow> x \<ge> t \<Longrightarrow> P) \<Longrightarrow> P" and
  cut_greaterE [elim!]: "x \<in> I \<down>> t \<Longrightarrow> (x \<in> I \<Longrightarrow> x > t \<Longrightarrow> P) \<Longrightarrow> P"
by (simp_all add: i_cut_mem_iff)


lemma
  cut_less_bound:    "n \<in> I \<down>< t \<Longrightarrow> n < t" and
  cut_le_bound:      "n \<in> I \<down>\<le> t \<Longrightarrow> n \<le> t" and
  cut_greater_bound: "n \<in> i \<down>> t \<Longrightarrow> t < n" and
  cut_ge_bound:      "n \<in> i \<down>\<ge> t \<Longrightarrow> t \<le> n"
unfolding i_cut_defs by simp_all

lemmas i_cut_bound =
  cut_less_bound cut_le_bound
  cut_greater_bound cut_ge_bound

lemma
  cut_le_Int_conv: "I \<down>\<le> t = I \<inter> {..t}" and
  cut_less_Int_conv: "I \<down>< t = I \<inter> {..<t}" and
  cut_ge_Int_conv: "I \<down>\<ge> t = I \<inter> {t..}" and
  cut_greater_Int_conv: "I \<down>> t = I \<inter> {t<..}"
unfolding i_cut_defs by blast+

lemmas i_cut_Int_conv =
  cut_le_Int_conv cut_less_Int_conv
  cut_ge_Int_conv cut_greater_Int_conv

lemma
  cut_le_Diff_conv: "I \<down>\<le> t = I - {t<..}" and
  cut_less_Diff_conv: "I \<down>< t = I - {t..}" and
  cut_ge_Diff_conv: "I \<down>\<ge> t = I - {..<t}" and
  cut_greater_Diff_conv: "I \<down>> t = I - {..t}"
by (fastforce simp: i_cut_defs)+
lemmas i_cut_Diff_conv =
  cut_le_Diff_conv cut_less_Diff_conv
  cut_ge_Diff_conv cut_greater_Diff_conv


subsubsection \<open>Basic results for cut operators\<close>

lemma
  cut_less_eq_set_restriction_fun':    "(\<lambda>I. I \<down>< t) = set_restriction_fun (\<lambda>x. x < t)" and
  cut_le_eq_set_restriction_fun':      "(\<lambda>I. I \<down>\<le> t) = set_restriction_fun (\<lambda>x. x \<le> t)" and
  cut_greater_eq_set_restriction_fun': "(\<lambda>I. I \<down>> t) = set_restriction_fun (\<lambda>x. x > t)" and
  cut_ge_eq_set_restriction_fun':      "(\<lambda>I. I \<down>\<ge> t) = set_restriction_fun (\<lambda>x. x \<ge> t)"
unfolding set_restriction_fun_def i_cut_defs by blast+
lemmas i_cut_eq_set_restriction_fun' =
  cut_less_eq_set_restriction_fun' cut_le_eq_set_restriction_fun'
  cut_greater_eq_set_restriction_fun' cut_ge_eq_set_restriction_fun'

lemma
  cut_less_eq_set_restriction_fun:    "I \<down>< t = set_restriction_fun (\<lambda>x. x < t) I" and
  cut_le_eq_set_restriction_fun:      "I \<down>\<le> t = set_restriction_fun (\<lambda>x. x \<le> t) I" and
  cut_greater_eq_set_restriction_fun: "I \<down>> t = set_restriction_fun (\<lambda>x. x > t) I" and
  cut_ge_eq_set_restriction_fun:      "I \<down>\<ge> t = set_restriction_fun (\<lambda>x. x \<ge> t) I"
by (simp_all only: i_cut_eq_set_restriction_fun'[symmetric])
lemmas i_cut_eq_set_restriction_fun =
  cut_less_eq_set_restriction_fun cut_le_eq_set_restriction_fun
  cut_greater_eq_set_restriction_fun cut_ge_eq_set_restriction_fun

lemma i_cut_set_restriction_disj: "
  \<lbrakk> cut_op = (\<down><) \<or> cut_op = (\<down>\<le>) \<or>
    cut_op = (\<down>>) \<or> cut_op = (\<down>\<ge>);
    f = (\<lambda>I. cut_op I t)  \<rbrakk> \<Longrightarrow> set_restriction f"
apply safe
apply (simp_all only: i_cut_eq_set_restriction_fun set_restriction_fun_is_set_restriction)
done

corollary
  i_cut_less_set_restriction:    "set_restriction (\<lambda>I. I \<down>< t)" and
  i_cut_le_set_restriction:      "set_restriction (\<lambda>I. I \<down>\<le> t)" and
  i_cut_greater_set_restriction: "set_restriction (\<lambda>I. I \<down>> t)" and
  i_cut_ge_set_restriction:      "set_restriction (\<lambda>I. I \<down>\<ge> t)"
by (simp_all only: i_cut_eq_set_restriction_fun set_restriction_fun_is_set_restriction)

lemmas i_cut_set_restriction =
  i_cut_le_set_restriction i_cut_less_set_restriction
  i_cut_ge_set_restriction i_cut_greater_set_restriction

lemma i_cut_commute_disj: "\<lbrakk>
  cut_op1 = (\<down><) \<or> cut_op1 = (\<down>\<le>) \<or>
  cut_op1 = (\<down>>) \<or> cut_op1 = (\<down>\<ge>);
  cut_op2 = (\<down><) \<or> cut_op2 = (\<down>\<le>) \<or>
  cut_op2 = (\<down>>) \<or> cut_op2 = (\<down>\<ge>) \<rbrakk> \<Longrightarrow>
  cut_op2 (cut_op1 I t1) t2 = cut_op1 (cut_op2 I t2) t1"
apply (rule set_restriction_commute)
apply (simp_all only: i_cut_set_restriction_disj)
done

lemma
  cut_less_empty:    "{} \<down>< t = {}" and
  cut_le_empty:      "{} \<down>\<le> t = {}" and
  cut_greater_empty: "{} \<down>> t = {}" and
  cut_ge_empty:      "{} \<down>\<ge> t = {}"
by blast+

lemmas i_cut_empty =
  cut_less_empty cut_le_empty
  cut_greater_empty cut_ge_empty

lemma
  cut_less_not_empty_imp:    "I \<down>< t \<noteq> {} \<Longrightarrow> I \<noteq> {}" and
  cut_le_not_empty_imp:      "I \<down>\<le> t \<noteq> {} \<Longrightarrow> I \<noteq> {}" and
  cut_greater_not_empty_imp: "I \<down>> t \<noteq> {} \<Longrightarrow> I \<noteq> {}" and
  cut_ge_not_empty_imp:      "I \<down>\<ge> t \<noteq> {} \<Longrightarrow> I \<noteq> {}"
by blast+


lemma
  cut_less_singleton:    "{a} \<down>< t = (if a < t then {a} else {})" and
  cut_le_singleton:      "{a} \<down>\<le> t = (if a \<le> t then {a} else {})" and
  cut_greater_singleton: "{a} \<down>> t = (if a > t then {a} else {})" and
  cut_ge_singleton:      "{a} \<down>\<ge> t = (if a \<ge> t then {a} else {})"
by (rule i_cut_eq_set_restriction_fun[THEN ssubst], simp only: set_restriction_fun_singleton)+
lemmas i_cut_singleton =
  cut_le_singleton cut_less_singleton
  cut_ge_singleton cut_greater_singleton




lemma
  cut_less_subset:    "I \<down>< t \<subseteq> I" and
  cut_le_subset:      "I \<down>\<le> t \<subseteq> I" and
  cut_greater_subset: "I \<down>> t \<subseteq> I" and
  cut_ge_subset:      "I \<down>\<ge> t \<subseteq> I"
by (simp_all only: i_cut_set_restriction[THEN set_restriction_subset])

lemmas i_cut_subset =
  cut_less_subset cut_le_subset
  cut_greater_subset cut_ge_subset

lemma i_cut_Un_disj: "
  \<lbrakk> cut_op = (\<down><) \<or> cut_op = (\<down>\<le>) \<or>
    cut_op = (\<down>>) \<or> cut_op = (\<down>\<ge>) \<rbrakk>
  \<Longrightarrow> cut_op (A \<union> B) t = cut_op A t \<union> cut_op B t"
apply (drule i_cut_set_restriction_disj[where f="\<lambda>I. cut_op I t"], simp)
by (rule set_restriction_Un)


corollary
  cut_less_Un:    "(A \<union> B) \<down>< t = A \<down>< t \<union> B \<down>< t" and
  cut_le_Un:      "(A \<union> B) \<down>\<le> t = A \<down>\<le> t \<union> B \<down>\<le> t" and
  cut_greater_Un: "(A \<union> B) \<down>> t = A \<down>> t \<union> B \<down>> t" and
  cut_ge_Un:      "(A \<union> B) \<down>\<ge> t = A \<down>\<ge> t \<union> B \<down>\<ge> t"
by (rule i_cut_Un_disj, blast)+
lemmas i_cut_Un =
  cut_less_Un cut_le_Un
  cut_greater_Un cut_ge_Un




lemma i_cut_Int_disj: "
  \<lbrakk> cut_op = (\<down><) \<or> cut_op = (\<down>\<le>) \<or>
    cut_op = (\<down>>) \<or> cut_op = (\<down>\<ge>) \<rbrakk>
  \<Longrightarrow> cut_op (A \<inter> B) t = cut_op A t \<inter> cut_op B t"
apply (drule i_cut_set_restriction_disj[where f="\<lambda>I. cut_op I t"], simp)
by (rule set_restriction_Int)

lemma
  cut_less_Int:    "(A \<inter> B) \<down>< t = A \<down>< t \<inter> B \<down>< t" and
  cut_le_Int:      "(A \<inter> B) \<down>\<le> t = A \<down>\<le> t \<inter> B \<down>\<le> t" and
  cut_greater_Int: "(A \<inter> B) \<down>> t = A \<down>> t \<inter> B \<down>> t" and
  cut_ge_Int:      "(A \<inter> B) \<down>\<ge> t = A \<down>\<ge> t \<inter> B \<down>\<ge> t"
by blast+
lemmas i_cut_Int =
  cut_less_Int cut_le_Int
  cut_greater_Int cut_ge_Int

lemma
  cut_less_Int_left:    "(A \<inter> B) \<down>< t = A \<down>< t \<inter> B" and
  cut_le_Int_left:      "(A \<inter> B) \<down>\<le> t = A \<down>\<le> t \<inter> B" and
  cut_greater_Int_left: "(A \<inter> B) \<down>> t = A \<down>> t \<inter> B" and
  cut_ge_Int_left:      "(A \<inter> B) \<down>\<ge> t = A \<down>\<ge> t \<inter> B"
by blast+
lemmas i_cut_Int_left =
  cut_less_Int_left cut_le_Int_left
  cut_greater_Int_left cut_ge_Int_left

lemma
  cut_less_Int_right:    "(A \<inter> B) \<down>< t = A \<inter> B \<down>< t" and
  cut_le_Int_right:      "(A \<inter> B) \<down>\<le> t = A \<inter> B \<down>\<le> t" and
  cut_greater_Int_right: "(A \<inter> B) \<down>> t = A \<inter> B \<down>> t" and
  cut_ge_Int_right:      "(A \<inter> B) \<down>\<ge> t = A \<inter> B \<down>\<ge> t"
by blast+
lemmas i_cut_Int_right =
  cut_less_Int_right cut_le_Int_right
  cut_greater_Int_right cut_ge_Int_right

lemma i_cut_Diff_disj: "
  \<lbrakk> cut_op = (\<down><) \<or> cut_op = (\<down>\<le>) \<or>
    cut_op = (\<down>>) \<or> cut_op = (\<down>\<ge>) \<rbrakk>
  \<Longrightarrow> cut_op (A - B) t = cut_op A t - cut_op B t"
apply (drule i_cut_set_restriction_disj[where f="\<lambda>I. cut_op I t"], simp)
by (rule set_restriction_Diff)
corollary
  cut_less_Diff:    "(A - B) \<down>< t = A \<down>< t - B \<down>< t" and
  cut_le_Diff:      "(A - B) \<down>\<le> t = A \<down>\<le> t - B \<down>\<le> t" and
  cut_greater_Diff: "(A - B) \<down>> t = A \<down>> t - B \<down>> t" and
  cut_ge_Diff:      "(A - B) \<down>\<ge> t = A \<down>\<ge> t - B \<down>\<ge> t"
by (rule i_cut_Diff_disj, blast)+
lemmas i_cut_Diff =
  cut_less_Diff cut_le_Diff
  cut_greater_Diff cut_ge_Diff

lemma i_cut_subset_mono_disj: "
  \<lbrakk> cut_op = (\<down><) \<or> cut_op = (\<down>\<le>) \<or>
    cut_op = (\<down>>) \<or> cut_op = (\<down>\<ge>); A \<subseteq> B \<rbrakk>
  \<Longrightarrow> cut_op A t \<subseteq> cut_op B t"
apply (drule i_cut_set_restriction_disj[where f="\<lambda>I. cut_op I t"], simp)
by (rule set_restriction_mono[where f="\<lambda>I. cut_op I t"])

corollary
  cut_less_subset_mono:    "A \<subseteq> B \<Longrightarrow> A \<down>< t \<subseteq> B \<down>< t" and
  cut_le_subset_mono:      "A \<subseteq> B \<Longrightarrow> A \<down>\<le> t \<subseteq> B \<down>\<le> t" and
  cut_greater_subset_mono: "A \<subseteq> B \<Longrightarrow> A \<down>> t \<subseteq> B \<down>> t" and
  cut_ge_subset_mono:      "A \<subseteq> B \<Longrightarrow> A \<down>\<ge> t \<subseteq> B \<down>\<ge> t"
by (rule i_cut_subset_mono_disj[of _ A], simp+)+

lemmas i_cut_subset_mono =
  cut_less_subset_mono cut_le_subset_mono
  cut_greater_subset_mono cut_ge_subset_mono





lemma
  cut_less_mono:    "t \<le> t' \<Longrightarrow> I \<down>< t \<subseteq> I \<down>< t'" and
  cut_greater_mono: "t' \<le> t \<Longrightarrow> I \<down>> t \<subseteq> I \<down>> t'" and
  cut_le_mono:      "t \<le> t' \<Longrightarrow> I \<down>\<le> t \<subseteq> I \<down>\<le> t'" and
  cut_ge_mono:      "t' \<le> t \<Longrightarrow> I \<down>\<ge> t \<subseteq> I \<down>\<ge> t'"
by (unfold i_cut_defs, safe, simp_all)
lemmas i_cut_mono =
  cut_le_mono cut_less_mono
  cut_ge_mono cut_greater_mono




lemma
  cut_cut_le: "i \<down>\<le> a \<down>\<le> b = i \<down>\<le> min a b" and
  cut_cut_less: "i \<down>< a \<down>< b = i \<down>< min a b" and
  cut_cut_ge: "i \<down>\<ge> a \<down>\<ge> b = i \<down>\<ge> max a b" and
  cut_cut_greater: "i \<down>> a \<down>> b = i \<down>> max a b"
unfolding i_cut_defs by simp_all
lemmas i_cut_cut =
  cut_cut_le cut_cut_less
  cut_cut_ge cut_cut_greater

lemma i_cut_absorb_disj: "
  \<lbrakk> cut_op = (\<down><) \<or> cut_op = (\<down>\<le>) \<or>
    cut_op = (\<down>>) \<or> cut_op = (\<down>\<ge>) \<rbrakk>
  \<Longrightarrow> cut_op (cut_op I t) t = cut_op I t"
apply (drule i_cut_set_restriction_disj[where f="\<lambda>I. cut_op I t"], blast)
apply (blast dest: set_restriction_absorb)
done

corollary
  cut_le_absorb:      "I \<down>\<le> t \<down>\<le> t = I \<down>\<le> t" and
  cut_less_absorb:    "I \<down>< t \<down>< t = I \<down>< t" and
  cut_ge_absorb:      "I \<down>\<ge> t \<down>\<ge> t = I \<down>\<ge> t" and
  cut_greater_absorb: "I \<down>> t \<down>> t = I \<down>> t"
by (rule i_cut_absorb_disj, blast)+

lemmas i_cut_absorb =
  cut_le_absorb cut_less_absorb
  cut_ge_absorb cut_greater_absorb

lemma
  cut_less_0_empty: "I \<down>< (0::nat) = {}" and
  cut_ge_0_all:     "I \<down>\<ge> (0::nat) = I"
unfolding i_cut_defs by blast+

lemma
  cut_le_all_iff:      "(I \<down>\<le> t = I) = (\<forall>x\<in>I. x \<le> t)" and
  cut_less_all_iff:    "(I \<down>< t = I) = (\<forall>x\<in>I. x < t)" and
  cut_ge_all_iff:      "(I \<down>\<ge> t = I) = (\<forall>x\<in>I. x \<ge> t)" and
  cut_greater_all_iff: "(I \<down>> t = I) = (\<forall>x\<in>I. x > t)"
by blast+

lemmas i_cut_all_iff =
  cut_le_all_iff cut_less_all_iff
  cut_ge_all_iff cut_greater_all_iff

lemma
  cut_le_empty_iff:      "(I \<down>\<le> t = {}) = (\<forall>x\<in>I. t < x)" and
  cut_less_empty_iff:    "(I \<down>< t = {}) = (\<forall>x\<in>I. t \<le> x)" and
  cut_ge_empty_iff:      "(I \<down>\<ge> t = {}) = (\<forall>x\<in>I. x < t)" and
  cut_greater_empty_iff: "(I \<down>> t = {}) = (\<forall>x\<in>I. x \<le> t)"
unfolding i_cut_defs by fastforce+

lemmas i_cut_empty_iff =
  cut_le_empty_iff cut_less_empty_iff
  cut_ge_empty_iff cut_greater_empty_iff

lemma
  cut_le_not_empty_iff:      "(I \<down>\<le> t \<noteq> {}) = (\<exists>x\<in>I. x \<le> t)" and
  cut_less_not_empty_iff:    "(I \<down>< t \<noteq> {}) = (\<exists>x\<in>I. x < t)" and
  cut_ge_not_empty_iff:      "(I \<down>\<ge> t \<noteq> {}) = (\<exists>x\<in>I. t \<le> x)" and
  cut_greater_not_empty_iff: "(I \<down>> t \<noteq> {}) = (\<exists>x\<in>I. t < x)"
unfolding i_cut_defs by blast+

lemmas i_cut_not_empty_iff =
  cut_le_not_empty_iff cut_less_not_empty_iff
  cut_ge_not_empty_iff cut_greater_not_empty_iff

lemma nat_cut_ge_infinite_not_empty: "infinite I \<Longrightarrow> I \<down>\<ge> (t::nat) \<noteq> {}"
by (drule infinite_nat_iff_unbounded_le[THEN iffD1], blast)

lemma nat_cut_greater_infinite_not_empty: "infinite I \<Longrightarrow> I \<down>> (t::nat) \<noteq> {}"
by (drule infinite_nat_iff_unbounded[THEN iffD1], blast)

corollary
  cut_le_not_in_imp:      "x \<notin> I \<Longrightarrow> x \<notin> I \<down>\<le> t" and
  cut_less_not_in_imp:    "x \<notin> I \<Longrightarrow> x \<notin> I \<down>< t" and
  cut_ge_not_in_imp:      "x \<notin> I \<Longrightarrow> x \<notin> I \<down>\<ge> t" and
  cut_greater_not_in_imp: "x \<notin> I \<Longrightarrow> x \<notin> I \<down>> t"
by (rule i_cut_set_restriction[THEN set_restriction_not_in_imp], assumption)+

lemmas i_cut_not_in_imp =
  cut_le_not_in_imp cut_less_not_in_imp
  cut_ge_not_in_imp cut_greater_not_in_imp

corollary
  cut_le_in_imp:      "x \<in> I \<down>\<le> t \<Longrightarrow> x \<in> I" and
  cut_less_in_imp:    "x \<in> I \<down>< t \<Longrightarrow> x \<in> I" and
  cut_ge_in_imp:      "x \<in> I \<down>\<ge> t \<Longrightarrow> x \<in> I" and
  cut_greater_in_imp: "x \<in> I \<down>> t \<Longrightarrow> x \<in> I"
by (rule i_cut_set_restriction[THEN set_restriction_in_imp], assumption)+

lemmas i_cut_in_imp =
  cut_le_in_imp cut_less_in_imp
  cut_ge_in_imp cut_greater_in_imp


lemma Collect_minI_cut: "\<lbrakk> k \<in> I; P (k::('a::wellorder)) \<rbrakk> \<Longrightarrow> \<exists>x\<in>I. P x \<and> (\<forall>y\<in>(I \<down>< x). \<not> P y)"
by (drule Collect_minI, assumption, blast)

corollary Collect_minI_ex_cut: "\<exists>k\<in>I. P (k::('a::wellorder)) \<Longrightarrow> \<exists>x\<in>I. P x \<and> (\<forall>y\<in>(I \<down>< x). \<not> P y)"
by (drule Collect_minI_ex, blast)

corollary Collect_minI_ex2_cut: "{k\<in>I. P (k::('a::wellorder))} \<noteq> {} \<Longrightarrow> \<exists>x\<in>I. P x \<and> (\<forall>y\<in>(I \<down>< x). \<not> P y)"
by (drule Collect_minI_ex2, blast)





lemma cut_le_cut_greater_ident: "t2 \<le> t1 \<Longrightarrow> I \<down>\<le> t1 \<union> I \<down>> t2 = I"
by fastforce
lemma cut_less_cut_ge_ident: "t2 \<le> t1 \<Longrightarrow> I \<down>< t1 \<union> I \<down>\<ge> t2 = I"
by fastforce
lemma cut_le_cut_ge_ident: "t2 \<le> t1 \<Longrightarrow> I \<down>\<le> t1 \<union> I \<down>\<ge> t2 = I"
by fastforce

lemma cut_less_cut_greater_ident: "
  \<lbrakk> t2 \<le> t1; I \<inter> {t1..t2} = {} \<rbrakk> \<Longrightarrow> I \<down>< t1 \<union> I \<down>> t2 = I"
by fastforce
corollary cut_less_cut_greater_ident': "
  t \<notin> I \<Longrightarrow> I \<down>< t \<union> I \<down>> t = I"
by (simp add: cut_less_cut_greater_ident)

lemma insert_eq_cut_less_cut_greater: "insert n I = I \<down>< n \<union> {n} \<union> I \<down>> n"
by fastforce



subsubsection \<open>Relations between cut operators\<close>

lemma insert_Int_conv_if: "A \<inter> (insert x B) = (
  if x \<in> A then insert x (A \<inter> B) else A \<inter> B)"
by simp

lemma cut_le_less_conv_if: "I \<down>\<le> t = (
  if t \<in> I then insert t (I \<down>< t) else (I \<down>< t))"
by (simp add: i_cut_Int_conv lessThan_insert[symmetric] insert_Int_conv_if)

lemma cut_le_less_conv: "I \<down>\<le> t = ({t} \<inter> I) \<union> (I \<down>< t)"
by fastforce

lemma cut_less_le_conv: "I \<down>< t = (I \<down>\<le> t) - {t}"
by fastforce
lemma cut_less_le_conv_if: "I \<down>< t = (
  if t \<in> I then (I \<down>\<le> t) - {t} else (I \<down>\<le> t))"
by (simp only: cut_less_le_conv, force)







lemma cut_ge_greater_conv_if: "I \<down>\<ge> t = (
  if t \<in> I then insert t (I \<down>> t) else (I \<down>> t))"
by (simp add: i_cut_Int_conv greaterThan_insert[symmetric] insert_Int_conv_if)
lemma cut_ge_greater_conv: "I \<down>\<ge> t = ({t} \<inter> I) \<union> (I \<down>> t)"
apply (simp only: cut_ge_greater_conv_if)
apply (case_tac "t \<in> I")
apply simp_all
done
lemma cut_greater_ge_conv: "I \<down>> t = (I \<down>\<ge> t) - {t}"
by fastforce
lemma cut_greater_ge_conv_if: "I \<down>> t = (
  if t \<in> I then (I \<down>\<ge> t) - {t} else (I \<down>\<ge> t))"
by (simp only: cut_greater_ge_conv, force)



lemma nat_cut_le_less_conv: "I \<down>\<le> t = I \<down>< Suc t"
by fastforce
lemma nat_cut_less_le_conv: "0 < t \<Longrightarrow> I \<down>< t = I \<down>\<le> (t - Suc 0)"
by fastforce
lemma nat_cut_ge_greater_conv: "I \<down>\<ge> Suc t = I \<down>> t"
by fastforce
lemma nat_cut_greater_ge_conv: "0 < t \<Longrightarrow> I \<down>> (t - Suc 0) = I \<down>\<ge> t"
by fastforce


subsubsection \<open>Function images with cut operators\<close>

lemma cut_less_image: "
  \<lbrakk> strict_mono_on f A; I \<subseteq> A; n \<in> A \<rbrakk> \<Longrightarrow>
  (f ` I) \<down>< f n = f ` (I \<down>< n)"
apply (rule set_eqI)
apply (simp add: image_iff Bex_def cut_less_mem_iff)
apply (unfold strict_mono_on_def)
apply (rule iffI)
 apply (metis not_less_iff_gr_or_eq rev_subsetD)
apply blast
done

lemma cut_le_image: "
  \<lbrakk> strict_mono_on f A; I \<subseteq> A; n \<in> A \<rbrakk> \<Longrightarrow>
  (f ` I) \<down>\<le> f n = f ` (I \<down>\<le> n)"
apply (frule strict_mono_on_imp_inj_on)
apply (clarsimp simp: cut_le_less_conv_if cut_less_image inj_on_def)
apply blast
done

lemma cut_greater_image: "
  \<lbrakk> strict_mono_on f A; I \<subseteq> A; n \<in> A \<rbrakk> \<Longrightarrow>
  (f ` I) \<down>> f n = f ` (I \<down>> n)"
apply (rule set_eqI)
apply (simp add: image_iff Bex_def cut_greater_mem_iff)
apply (unfold strict_mono_on_def)
apply (rule iffI)
 apply (metis not_less_iff_gr_or_eq rev_subsetD)
apply blast
done

lemma cut_ge_image: "
  \<lbrakk> strict_mono_on f A; I \<subseteq> A; n \<in> A \<rbrakk> \<Longrightarrow>
  (f ` I) \<down>\<ge> f n = f ` (I \<down>\<ge> n)"
apply (frule strict_mono_on_imp_inj_on)
apply (clarsimp simp: cut_ge_greater_conv_if cut_greater_image inj_on_def)
apply blast
done

lemmas i_cut_image =
  cut_le_image cut_less_image
  cut_ge_image cut_greater_image


subsubsection \<open>Finiteness and cardinality with cut operators\<close>

lemma
  cut_le_finite:      "finite I \<Longrightarrow> finite (I \<down>\<le> t)" and
  cut_less_finite:    "finite I \<Longrightarrow> finite (I \<down>< t)" and
  cut_ge_finite:      "finite I \<Longrightarrow> finite (I \<down>\<ge> t)" and
  cut_greater_finite: "finite I \<Longrightarrow> finite (I \<down>> t)"
by (rule finite_subset[of _ I], rule i_cut_subset, assumption+)+

lemma nat_cut_le_finite: "finite (I \<down>\<le> (t::nat))"
by (fastforce simp: finite_nat_iff_bounded_le2 cut_le_def)

lemma nat_cut_less_finite: "finite (I \<down>< (t::nat))"
by (fastforce simp: finite_nat_iff_bounded2 cut_less_def)

lemma nat_cut_ge_finite_iff: "finite (I \<down>\<ge> (t::nat)) = finite I"
apply (rule iffI)
 apply (subst cut_less_cut_ge_ident[of t, OF order_refl, symmetric])
 apply (simp add: nat_cut_less_finite)
apply (simp add: cut_ge_finite)
done

lemma nat_cut_greater_finite_iff: "finite (I \<down>> (t::nat)) = finite I"
by (simp only: nat_cut_ge_greater_conv[symmetric] nat_cut_ge_finite_iff)

lemma
  cut_le_card:      "finite I \<Longrightarrow> card (I \<down>\<le> t) \<le> card I" and
  cut_less_card:    "finite I \<Longrightarrow> card (I \<down>< t) \<le> card I" and
  cut_ge_card:      "finite I \<Longrightarrow> card (I \<down>\<ge> t) \<le> card I" and
  cut_greater_card: "finite I \<Longrightarrow> card (I \<down>> t) \<le> card I"
by (rule card_mono, assumption, rule i_cut_subset)+

lemma nat_cut_greater_card: "card (I \<down>> (t::nat)) \<le> card I"
apply (case_tac "finite I")
 apply (simp add: cut_greater_card)
apply (simp add: nat_cut_greater_finite_iff)
done

lemma nat_cut_ge_card: "card (I \<down>\<ge> (t::nat)) \<le> card I"
apply (case_tac "finite I")
 apply (simp add: cut_ge_card)
apply (simp add: nat_cut_ge_finite_iff)
done


subsubsection \<open>Cutting a set at  \<open>Min\<close> or \<open>Max\<close> element\<close>

lemma cut_greater_Min_eq_Diff: "I \<down>> (iMin I) = I - {iMin I}"
by blast
lemma cut_less_Max_eq_Diff: "finite I \<Longrightarrow> I \<down>< (Max I) = I - {Max I}"
by blast

lemma cut_le_Min_empty: "t < iMin I \<Longrightarrow> I \<down>\<le> t = {}"
by (fastforce simp: i_cut_defs)
lemma cut_less_Min_empty: "t \<le> iMin I \<Longrightarrow> I \<down>< t = {}"
by (fastforce simp: i_cut_defs)


lemma cut_le_Min_not_empty: "\<lbrakk> I \<noteq> {}; iMin I \<le> t \<rbrakk> \<Longrightarrow> I \<down>\<le> t \<noteq> {}"
apply (simp add: i_cut_defs)
apply (rule_tac x="iMin I" in exI)
apply (simp add: iMinI_ex2)
done

lemma cut_less_Min_not_empty: "\<lbrakk> I \<noteq> {}; iMin I < t \<rbrakk> \<Longrightarrow> I \<down>< t \<noteq> {}"
apply (simp add: i_cut_defs)
apply (rule_tac x="iMin I" in exI)
apply (simp add: iMinI_ex2)
done

lemma cut_ge_Min_all: "t \<le> iMin I \<Longrightarrow> I \<down>\<ge> t = I"
apply (simp add: i_cut_defs)
apply safe
apply (drule iMin_le, simp)
done

lemma cut_greater_Min_all: "t < iMin I \<Longrightarrow> I \<down>> t = I"
apply (simp add: i_cut_defs)
apply safe
apply (drule iMin_le, simp)
done

lemmas i_cut_min_empty =
  cut_le_Min_empty
  cut_less_Min_empty
  cut_le_Min_not_empty
  cut_less_Min_not_empty
lemmas i_cut_min_all =
  cut_ge_Min_all
  cut_greater_Min_all

lemma cut_ge_Max_empty: "finite I \<Longrightarrow> Max I < t \<Longrightarrow> I \<down>\<ge> t = {}"
by (fastforce simp: i_cut_defs)

lemma cut_greater_Max_empty: "finite I \<Longrightarrow> Max I \<le> t \<Longrightarrow> I \<down>> t = {}"
by (fastforce simp: i_cut_defs)

lemma cut_ge_Max_not_empty: "\<lbrakk> I \<noteq> {}; finite I; t \<le> Max I \<rbrakk> \<Longrightarrow> I \<down>\<ge> t \<noteq> {}"
apply (simp add: i_cut_defs)
apply (rule_tac x="Max I" in exI)
apply (simp add: MaxI_ex2)
done

lemma cut_greater_Max_not_empty: "\<lbrakk> I \<noteq> {}; finite I; t < Max I \<rbrakk> \<Longrightarrow> I \<down>> t \<noteq> {}"
apply (simp add: i_cut_defs)
apply (rule_tac x="Max I" in exI)
apply (simp add: MaxI_ex2)
done

lemma cut_le_Max_all: "finite I \<Longrightarrow> Max I \<le> t \<Longrightarrow> I \<down>\<le> t = I"
by (fastforce simp: i_cut_defs)

lemma cut_less_Max_all: "finite I \<Longrightarrow> Max I < t \<Longrightarrow> I \<down>< t = I"
by (fastforce simp: i_cut_defs)

lemmas i_cut_max_empty =
  cut_ge_Max_empty
  cut_greater_Max_empty
  cut_ge_Max_not_empty
  cut_greater_Max_not_empty
lemmas i_cut_max_all =
  cut_le_Max_all
  cut_less_Max_all

lemma cut_less_Max_less: "
  \<lbrakk> finite (I \<down>< t); I \<down>< t \<noteq> {} \<rbrakk> \<Longrightarrow> Max (I \<down>< t) < t"
by (rule cut_less_bound[OF Max_in])
lemma cut_le_Max_le: "
  \<lbrakk> finite (I \<down>\<le> t); I \<down>\<le> t \<noteq> {} \<rbrakk> \<Longrightarrow> Max (I \<down>\<le> t) \<le> t"
by (rule cut_le_bound[OF Max_in])
lemma nat_cut_less_Max_less: "
  I \<down>< t \<noteq> {} \<Longrightarrow> Max (I \<down>< t) < (t::nat)"
by (rule cut_less_bound[OF Max_in[OF nat_cut_less_finite]])
lemma nat_cut_le_Max_le: "
  I \<down>\<le> t \<noteq> {} \<Longrightarrow> Max (I \<down>\<le> t) \<le> (t::nat)"
by (rule cut_le_bound[OF Max_in[OF nat_cut_le_finite]])
lemma cut_greater_Min_greater: "
  I \<down>> t \<noteq> {} \<Longrightarrow> iMin (I \<down>> t) > t"
by (rule cut_greater_bound[OF iMinI_ex2])
lemma cut_ge_Min_greater: "
  I \<down>\<ge> t \<noteq> {} \<Longrightarrow> iMin (I \<down>\<ge> t) \<ge> t"
by (rule cut_ge_bound[OF iMinI_ex2])



lemma cut_less_Min_eq: "I \<down>< t \<noteq> {} \<Longrightarrow> iMin (I \<down>< t) = iMin I"
apply (drule cut_less_not_empty_iff[THEN iffD1])
apply (rule iMin_equality)
 apply (fastforce intro: iMinI)
apply blast
done

lemma cut_le_Min_eq: "I \<down>\<le> t \<noteq> {} \<Longrightarrow> iMin (I \<down>\<le> t) = iMin I"
apply (drule cut_le_not_empty_iff[THEN iffD1])
apply (rule iMin_equality)
 apply (fastforce intro: iMinI)
apply blast
done


lemma cut_ge_Max_eq: "\<lbrakk> finite I; I \<down>\<ge> t \<noteq> {} \<rbrakk> \<Longrightarrow> Max (I \<down>\<ge> t) = Max I"
apply (drule cut_ge_not_empty_iff[THEN iffD1])
apply (rule Max_equality)
  apply (fastforce intro: MaxI)
 apply (simp add: cut_ge_finite)
apply fastforce
done

lemma cut_greater_Max_eq: "\<lbrakk> finite I; I \<down>> t \<noteq> {} \<rbrakk> \<Longrightarrow> Max (I \<down>> t) = Max I"
apply (drule cut_greater_not_empty_iff[THEN iffD1])
apply (rule Max_equality)
  apply (fastforce intro: MaxI)
 apply (simp add: cut_greater_finite)
apply fastforce
done


subsubsection \<open>Cut operators with intervals from SetInterval\<close>

lemma
  UNIV_cut_le:      "UNIV \<down>\<le> t = {..t}" and
  UNIV_cut_less:    "UNIV \<down>< t = {..<t}" and
  UNIV_cut_ge:      "UNIV \<down>\<ge> t = {t..}" and
  UNIV_cut_greater: "UNIV \<down>> t = {t<..}"
by blast+

lemma
  lessThan_cut_le:      "{..<n} \<down>\<le> t = (if n \<le> t then {..<n} else {..t})" and
  lessThan_cut_less:    "{..<n} \<down>< t = (if n \<le> t then {..<n} else {..<t})" and
  lessThan_cut_ge:      "{..<n} \<down>\<ge> t = {t..<n}" and
  lessThan_cut_greater: "{..<n} \<down>> t = {t<..<n}" and
  atMost_cut_le:      "{..n} \<down>\<le> t = (if n \<le> t then {..n} else {..t})" and
  atMost_cut_less:    "{..n} \<down>< t = (if n < t then {..n} else {..<t})" and
  atMost_cut_ge:      "{..n} \<down>\<ge> t = {t..n}" and
  atMost_cut_greager: "{..n} \<down>> t = {t<..n}" and
  greaterThan_cut_le:      "{n<..} \<down>\<le> t = {n<..t}" and
  greaterThan_cut_less:    "{n<..} \<down>< t = {n<..<t}" and
  greaterThan_cut_ge:      "{n<..} \<down>\<ge> t = (if t \<le> n then {n<..} else {t..})" and
  greaterThan_cut_greater: "{n<..} \<down>> t = (if t \<le> n then {n<..} else {t<..})" and
  atLeast_cut_le:      "{n..} \<down>\<le> t = {n..t}" and
  atLeast_cut_less:    "{n..} \<down>< t = {n..<t}" and
  atLeast_cut_ge:      "{n..} \<down>\<ge> t = (if t \<le> n then {n..} else {t..})" and
  atLeast_cut_greater: "{n..} \<down>\<ge> t = (if t \<le> n then {n..} else {t..})"
apply (simp_all add: set_eq_iff i_cut_mem_iff linorder_not_le linorder_not_less)
apply fastforce+
done


lemma
  greaterThanLessThan_cut_le:      "{m<..<n} \<down>\<le> t = (if n \<le> t then {m<..<n} else {m<..t})" and
  greaterThanLessThan_cut_less:    "{m<..<n} \<down>< t = (if n \<le> t then {m<..<n} else {m<..<t})" and
  greaterThanLessThan_cut_ge:      "{m<..<n} \<down>\<ge> t = (if t \<le> m then {m<..<n} else {t..<n})" and
  greaterThanLessThan_cut_greater: "{m<..<n} \<down>> t = (if t \<le> m then {m<..<n} else {t<..<n})" and
  atLeastLessThan_cut_le:      "{m..<n} \<down>\<le> t = (if n \<le> t then {m..<n} else {m..t})" and
  atLeastLessThan_cut_less:    "{m..<n} \<down>< t = (if n \<le> t then {m..<n} else {m..<t})" and
  atLeastLessThan_cut_ge:      "{m..<n} \<down>\<ge> t = (if t \<le> m then {m..<n} else {t..<n})" and
  atLeastLessThan_cut_greater: "{m..<n} \<down>> t = (if t < m then {m..<n} else {t<..<n})" and
  greaterThanAtMost_cut_le:      "{m<..n} \<down>\<le> t = (if n \<le> t then {m<..n} else {m<..t})" and
  greaterThanAtMost_cut_less:    "{m<..n} \<down>< t = (if n < t then {m<..n} else {m<..<t})" and
  greaterThanAtMost_cut_ge:      "{m<..n} \<down>\<ge> t = (if t \<le> m then {m<..n} else {t..n})" and
  greaterThanAtMost_cut_greater: "{m<..n} \<down>> t = (if t \<le> m then {m<..n} else {t<..n})" and
  atLeastAtMost_cut_le:      "{m..n} \<down>\<le> t = (if n \<le> t then {m..n} else {m..t})" and
  atLeastAtMost_cut_less:    "{m..n} \<down>< t = (if n < t then {m..n} else {m..<t})" and
  atLeastAtMost_cut_ge:      "{m..n} \<down>\<ge> t = (if t \<le> m then {m..n} else {t..n})" and
  atLeastAtMost_cut_greater: "{m..n} \<down>> t = (if t < m then {m..n} else {t<..n})"
apply (simp_all add: set_eq_iff i_cut_mem_iff if_split linorder_not_le linorder_not_less)
apply fastforce+
done


subsubsection \<open>Mirroring finite natural sets between their @{term Min} and @{term Max} element\<close>

text \<open>Mirroring a number at the middle of the interval {min l r..max l r}\<close>
text_raw \<open>\bigskip\<close>

text \<open>Mirroring a single element n between the interval boundaries l and r\<close>
definition nat_mirror :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "nat_mirror n l r \<equiv> l + r - n"

lemma nat_mirror_commute: "nat_mirror n l r = nat_mirror n r l"
unfolding nat_mirror_def by simp

lemma nat_mirror_inj_on: "inj_on (\<lambda>x. nat_mirror x l r) {..l + r}"
unfolding inj_on_def nat_mirror_def by fastforce

lemma nat_mirror_nat_mirror_ident: "
  n \<le> l + r \<Longrightarrow> nat_mirror (nat_mirror n l r) l r = n"
unfolding nat_mirror_def by simp

lemma nat_mirror_add: "
  nat_mirror (n + k) l r = (nat_mirror n l r) - k"
unfolding nat_mirror_def by simp
lemma nat_mirror_diff: "
  \<lbrakk> k \<le> n; n \<le> l + r \<rbrakk> \<Longrightarrow>
  nat_mirror (n - k) l r = (nat_mirror n l r) + k"
unfolding nat_mirror_def by simp

lemma nat_mirror_le: "a \<le> b \<Longrightarrow> nat_mirror b l r \<le> nat_mirror a l r"
unfolding nat_mirror_def by simp
lemma nat_mirror_le_conv: "
  a \<le> l + r \<Longrightarrow> (nat_mirror b l r \<le> nat_mirror a l r) = (a \<le> b)"
unfolding nat_mirror_def by fastforce

lemma nat_mirror_less: "
  \<lbrakk> a < b; a < l + r \<rbrakk> \<Longrightarrow>
  nat_mirror b l r < nat_mirror a l r"
unfolding nat_mirror_def by simp
lemma nat_mirror_less_imp_less: "
  nat_mirror b l r < nat_mirror a l r \<Longrightarrow> a < b"
unfolding nat_mirror_def by simp
lemma nat_mirror_less_conv: "
  a < l + r \<Longrightarrow> (nat_mirror b l r < nat_mirror a l r) = (a < b)"
unfolding nat_mirror_def by fastforce

lemma nat_mirror_eq_conv: "
  \<lbrakk> a \<le> l + r; b \<le> l + r \<rbrakk> \<Longrightarrow>
  (nat_mirror a l r = nat_mirror b l r) = (a = b)"
unfolding nat_mirror_def by fastforce

text \<open>Mirroring a single element n between the interval boundaries of I\<close>
definition
  mirror_elem :: "nat \<Rightarrow> nat set \<Rightarrow> nat"
where
  "mirror_elem n I \<equiv> nat_mirror n (iMin I) (Max I)"

lemma mirror_elem_inj_on: "finite I \<Longrightarrow> inj_on (\<lambda>x. mirror_elem x I) I"
unfolding mirror_elem_def
by (metis Max_le_imp_subset_atMost nat_mirror_inj_on not_add_less2 not_le_imp_less subset_inj_on)

lemma mirror_elem_add: "
  finite I \<Longrightarrow> mirror_elem (n + k) I = mirror_elem n I - k"
unfolding mirror_elem_def by (rule nat_mirror_add)
lemma mirror_elem_diff: "
  \<lbrakk> finite I; k \<le> n; n \<in> I \<rbrakk> \<Longrightarrow> mirror_elem (n - k) I = mirror_elem n I + k"
apply (unfold mirror_elem_def)
apply (rule nat_mirror_diff, assumption)
apply (simp add: trans_le_add2)
done
lemma mirror_elem_Min: "
  \<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> mirror_elem (iMin I) I = Max I"
unfolding mirror_elem_def nat_mirror_def by simp
lemma mirror_elem_Max: "
  \<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> mirror_elem (Max I) I = iMin I"
unfolding mirror_elem_def nat_mirror_def by simp

lemma mirror_elem_mirror_elem_ident: "
  \<lbrakk> finite I; n \<le> iMin I + Max I \<rbrakk> \<Longrightarrow> mirror_elem (mirror_elem n I) I = n"
unfolding mirror_elem_def nat_mirror_def by simp

lemma mirror_elem_le_conv: "
  \<lbrakk> finite I; a \<in> I; b \<in> I \<rbrakk> \<Longrightarrow>
  (mirror_elem b I \<le> mirror_elem a I) = (a \<le> b)"
apply (unfold mirror_elem_def)
apply (rule nat_mirror_le_conv)
apply (simp add: trans_le_add2)
done

lemma mirror_elem_less_conv: "
  \<lbrakk> finite I; a \<in> I; b \<in> I \<rbrakk> \<Longrightarrow>
  (mirror_elem b I < mirror_elem a I) = (a < b)"
unfolding mirror_elem_def nat_mirror_def
by (metis diff_less_mono2 nat_diff_left_cancel_less nat_ex_greater_infinite_finite_Max_conv' trans_less_add2)

lemma mirror_elem_eq_conv: "
  \<lbrakk> a \<le> iMin I + Max I; b \<le> iMin I + Max I \<rbrakk> \<Longrightarrow>
  (mirror_elem a I = mirror_elem b I) = (a = b)"
by (simp add: mirror_elem_def nat_mirror_eq_conv)
lemma mirror_elem_eq_conv': "
  \<lbrakk> finite I; a \<in> I; b \<in> I \<rbrakk> \<Longrightarrow> (mirror_elem a I = mirror_elem b I) = (a = b)"
apply (rule mirror_elem_eq_conv)
apply (simp_all add: trans_le_add2)
done


definition
  imirror_bounds :: "nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set"
where
  "imirror_bounds I l r \<equiv> (\<lambda>x. nat_mirror x l r) ` I"

text \<open>Mirroring all elements between the interval boundaries of I\<close>
definition
  imirror :: "nat set \<Rightarrow> nat set"
where
  "imirror I \<equiv> (\<lambda>x. iMin I + Max I - x) ` I"

lemma imirror_eq_nat_mirror_image: "
  imirror I = (\<lambda>x. nat_mirror x (iMin I) (Max I)) ` I"
unfolding imirror_def nat_mirror_def by simp
lemma imirror_eq_mirror_elem_image: "
  imirror I = (\<lambda>x. mirror_elem x I) ` I"
by (simp add: mirror_elem_def imirror_eq_nat_mirror_image)

lemma imirror_eq_imirror_bounds: "
  imirror I = imirror_bounds I (iMin I) (Max I)"
unfolding imirror_def imirror_bounds_def nat_mirror_def by simp




lemma imirror_empty: "imirror {} = {}"
unfolding imirror_def by simp
lemma imirror_is_empty: "(imirror I = {}) = (I = {})"
unfolding imirror_def by simp
lemma imirror_not_empty: "I \<noteq> {} \<Longrightarrow> imirror I \<noteq> {}"
unfolding imirror_def by simp

lemma imirror_singleton: "imirror {a} = {a}"
unfolding imirror_def by simp


lemma imirror_finite: "finite I \<Longrightarrow> finite (imirror I)"
unfolding imirror_def by simp

lemma imirror_bounds_iMin: "
  \<lbrakk> finite I; I \<noteq> {}; iMin I \<le> l + r \<rbrakk> \<Longrightarrow>
  iMin (imirror_bounds I l r) = l + r - Max I"
apply (unfold imirror_bounds_def nat_mirror_def)
apply (rule iMin_equality)
 apply (blast intro: Max_in)
apply (blast intro: Max_ge diff_le_mono2)
done

lemma imirror_bounds_Max: "
  \<lbrakk> finite I; I \<noteq> {}; Max I \<le> l + r \<rbrakk> \<Longrightarrow>
  Max (imirror_bounds I l r) = l + r - iMin I"
apply (unfold imirror_bounds_def nat_mirror_def)
apply (rule Max_equality)
  apply (blast intro: iMinI)
 apply simp
apply (blast intro: iMin_le diff_le_mono2)
done

lemma imirror_iMin: "finite I \<Longrightarrow> iMin (imirror I) = iMin I"
apply (case_tac "I = {}", simp add: imirror_empty)
apply (simp add: imirror_eq_imirror_bounds imirror_bounds_iMin le_add1)
done

lemma imirror_Max: "finite I \<Longrightarrow> Max (imirror I) = Max I"
apply (case_tac "I = {}", simp add: imirror_empty)
apply (simp add: imirror_eq_imirror_bounds imirror_bounds_Max trans_le_add2)
done
corollary imirror_iMin_Max: "\<lbrakk> finite I; n \<in> imirror I \<rbrakk> \<Longrightarrow> iMin I \<le> n \<and> n \<le> Max I"
apply (frule Max_ge[OF imirror_finite, of _ n], assumption)
apply (fastforce simp: imirror_iMin imirror_Max)
done

lemma imirror_bounds_iff:
  "(n \<in> imirror_bounds I l r) = (\<exists>x\<in>I. n = l + r - x)"
by (simp add: imirror_bounds_def nat_mirror_def image_iff)

lemma imirror_iff: "(n \<in> imirror I) = (\<exists>x\<in>I. n = iMin I + Max I - x)"
by (simp add: imirror_def image_iff)

lemma imirror_bounds_imirror_bounds_ident: "
  \<lbrakk> finite I; Max I \<le> l + r \<rbrakk> \<Longrightarrow>
  imirror_bounds (imirror_bounds I l r) l r = I"
apply (rule set_eqI)
apply (simp add: imirror_bounds_def image_image image_iff)
apply (rule iffI)
 apply (fastforce simp: nat_mirror_nat_mirror_ident)
apply (rule_tac x=x in bexI)
apply (fastforce simp: nat_mirror_nat_mirror_ident)+
done

lemma imirror_imirror_ident: "finite I \<Longrightarrow> imirror (imirror I) = I"
apply (case_tac "I = {}", simp add: imirror_empty)
apply (simp add: imirror_eq_imirror_bounds imirror_bounds_iMin imirror_bounds_Max
  le_add1 trans_le_add2 imirror_bounds_imirror_bounds_ident)
done

lemma mirror_elem_imirror: "
  finite I \<Longrightarrow> mirror_elem t (imirror I) = mirror_elem t I"
by (simp add: mirror_elem_def imirror_iMin imirror_Max)

lemma imirror_card: "finite I \<Longrightarrow> card (imirror I) = card I"
apply (simp only: imirror_eq_mirror_elem_image)
apply (rule inj_on_iff_eq_card[THEN iffD1], assumption)
apply (rule mirror_elem_inj_on, assumption)
done


lemma imirror_bounds_elem_conv: "
  \<lbrakk> finite I; n \<le> l + r; Max I \<le> l + r \<rbrakk> \<Longrightarrow>
  ((nat_mirror n l r) \<in> imirror_bounds I l r) = (n \<in> I)"
apply (unfold imirror_bounds_def)
apply (rule inj_on_image_mem_iff)
apply (rule nat_mirror_inj_on)
apply fastforce
apply simp
done

lemma imirror_mem_conv: "
  \<lbrakk> finite I; n \<le> iMin I + Max I \<rbrakk> \<Longrightarrow> ((mirror_elem n I) \<in> imirror I) = (n \<in> I)"
by (simp add: mirror_elem_def imirror_eq_imirror_bounds imirror_bounds_elem_conv)

corollary in_imp_mirror_elem_in: "
  \<lbrakk> finite I; n \<in> I \<rbrakk> \<Longrightarrow> (mirror_elem n I) \<in> imirror I"
by (rule imirror_mem_conv[OF _ trans_le_add2[OF Max_ge], THEN iffD2])

lemma imirror_cut_less: "
  finite I \<Longrightarrow>
  imirror I \<down>< (mirror_elem t I) =
  imirror_bounds (I \<down>> t) (iMin I) (Max I)"
apply (simp only: imirror_eq_imirror_bounds)
apply (unfold imirror_def imirror_bounds_def mirror_elem_def)
apply (rule set_eqI)
apply (simp add: Bex_def i_cut_mem_iff image_iff)
apply (rule iffI)
 apply (bestsimp intro: nat_mirror_less_imp_less)
apply (bestsimp simp add: nat_mirror_less)
done

lemma imirror_cut_le: "
  \<lbrakk> finite I; t \<le> iMin I + Max I \<rbrakk> \<Longrightarrow>
  imirror I \<down>\<le> (mirror_elem t I) =
  imirror_bounds (I \<down>\<ge> t) (iMin I) (Max I)"
apply (simp only: nat_cut_le_less_conv)
apply (case_tac "t = 0")
 apply (simp add: cut_ge_0_all i_cut_empty)
 apply (simp only: imirror_eq_imirror_bounds[symmetric])
 apply (rule cut_less_Max_all)
  apply (rule imirror_finite, assumption)
 apply (simp add: mirror_elem_def nat_mirror_def imirror_Max)
apply (simp add: nat_cut_greater_ge_conv[symmetric])
apply (rule subst[of "mirror_elem (t - Suc 0) I" "Suc (mirror_elem t I)"])
 apply (simp add: mirror_elem_def nat_mirror_diff)
apply (rule imirror_cut_less, assumption)
done

lemma imirror_cut_ge: "
  finite I \<Longrightarrow>
  imirror I \<down>\<ge> (mirror_elem t I) =
  imirror_bounds (I \<down>\<le> t) (iMin I) (Max I)"
  (is "?P \<Longrightarrow> ?lhs I = ?rhs I t")
apply (case_tac "iMin I + Max I < t")
 apply (simp add: mirror_elem_def nat_mirror_def cut_ge_0_all cut_le_Max_all imirror_eq_imirror_bounds)
apply (case_tac "t < iMin I")
 apply (simp add: cut_le_Min_empty imirror_bounds_def mirror_elem_def nat_mirror_def cut_ge_Max_empty imirror_Max imirror_finite)
apply (simp add: linorder_not_le linorder_not_less)
apply (rule subst[of "imirror (imirror I) \<down>\<le> mirror_elem (mirror_elem t I) (imirror I)" "I \<down>\<le> t"])
 apply (simp add: imirror_imirror_ident mirror_elem_imirror mirror_elem_mirror_elem_ident)
apply (subgoal_tac "mirror_elem t I \<le> Max (imirror I)")
 prefer 2
 apply (simp add: imirror_Max mirror_elem_def nat_mirror_def)
apply (simp add: imirror_cut_le imirror_finite)
by (metis cut_ge_Max_eq cut_ge_Max_not_empty imirror_Max imirror_bounds_imirror_bounds_ident imirror_finite imirror_iMin le_add2 nat_cut_ge_finite_iff)

lemma imirror_cut_greater: "\<lbrakk> finite I; t \<le> iMin I + Max I \<rbrakk> \<Longrightarrow>
  imirror I \<down>> (mirror_elem t I) =
  imirror_bounds (I \<down>< t) (iMin I) (Max I)"
apply (case_tac "t = 0")
 apply (simp add: cut_less_0_empty imirror_bounds_def)
 apply (rule cut_greater_Max_empty)
   apply (rule imirror_finite, assumption)
 apply (simp add: imirror_Max mirror_elem_def nat_mirror_def)
apply (simp add: nat_cut_ge_greater_conv[symmetric])
apply (rule subst[of "mirror_elem (t - Suc 0) I" "Suc (mirror_elem t I)"])
 apply (simp add: mirror_elem_def nat_mirror_diff)
apply (simp add: imirror_cut_ge nat_cut_less_le_conv)
done

lemmas imirror_cut =
  imirror_cut_less imirror_cut_ge
  imirror_cut_le imirror_cut_greater

corollary imirror_cut_le': "
  \<lbrakk> finite I; t \<in> I \<rbrakk> \<Longrightarrow>
  imirror I \<down>\<le> mirror_elem t I =
  imirror_bounds (I \<down>\<ge> t) (iMin I) (Max I)"
by (rule imirror_cut_le[OF _ trans_le_add2[OF Max_ge]])

corollary imirror_cut_greater': "
  \<lbrakk> finite I; t \<in> I \<rbrakk> \<Longrightarrow>
  imirror I \<down>> mirror_elem t I =
  imirror_bounds (I \<down>< t) (iMin I) (Max I)"
by (rule imirror_cut_greater[OF _ trans_le_add2[OF Max_ge]])

lemmas imirror_cut' =
  imirror_cut_le' imirror_cut_greater'


lemma imirror_bounds_Un: "
  imirror_bounds (A \<union> B) l r =
  imirror_bounds A l r \<union> imirror_bounds B l r"
by (simp add: imirror_bounds_def image_Un)
lemma imirror_bounds_Int: "
  \<lbrakk> A \<subseteq> {..l + r}; B \<subseteq> {..l + r} \<rbrakk> \<Longrightarrow>
  imirror_bounds (A \<inter> B) l r =
  imirror_bounds A l r \<inter> imirror_bounds B l r"
apply (unfold imirror_bounds_def)
apply (rule inj_on_image_Int[OF _ Un_upper1 Un_upper2])
apply (rule subset_inj_on[OF nat_mirror_inj_on])
apply (rule Un_least[of A _ B], assumption+)
done

end
