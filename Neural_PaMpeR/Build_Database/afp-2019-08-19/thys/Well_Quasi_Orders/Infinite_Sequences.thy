(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>Infinite Sequences\<close>

text \<open>Some useful constructions on and facts about infinite sequences.\<close>

theory Infinite_Sequences
imports Main
begin

text \<open>The set of all infinite sequences over elements from @{term A}.\<close>
definition "SEQ A = {f::nat \<Rightarrow> 'a. \<forall>i. f i \<in> A}"

lemma SEQ_iff [iff]:
  "f \<in> SEQ A \<longleftrightarrow> (\<forall>i. f i \<in> A)"
by (auto simp: SEQ_def)


text \<open>The \<open>i\<close>-th "column" of a set \<open>B\<close> of infinite sequences.\<close>
definition "ith B i = {f i | f. f \<in> B}"

lemma ithI [intro]:
  "f \<in> B \<Longrightarrow> f i = x \<Longrightarrow> x \<in> ith B i"
by (auto simp: ith_def)

lemma ithE [elim]:
  "\<lbrakk>x \<in> ith B i; \<And>f. \<lbrakk>f \<in> B; f i = x\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (auto simp: ith_def)

lemma ith_conv:
  "x \<in> ith B i \<longleftrightarrow> (\<exists>f \<in> B. x = f i)"
by auto

text \<open>
  The restriction of a set \<open>B\<close> of sequences to sequences that are equal to a given sequence
  \<open>f\<close> up to position \<open>i\<close>.
\<close>
definition eq_upto :: "(nat \<Rightarrow> 'a) set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) set"
where
  "eq_upto B f i = {g \<in> B. \<forall>j < i. f j = g j}"

lemma eq_uptoI [intro]:
  "\<lbrakk>g \<in> B; \<And>j. j < i \<Longrightarrow> f j = g j\<rbrakk> \<Longrightarrow> g \<in> eq_upto B f i"
by (auto simp: eq_upto_def)

lemma eq_uptoE [elim]:
  "\<lbrakk>g \<in> eq_upto B f i; \<lbrakk>g \<in> B; \<And>j. j < i \<Longrightarrow> f j = g j\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (auto simp: eq_upto_def)

lemma eq_upto_Suc:
  "\<lbrakk>g \<in> eq_upto B f i; g i = f i\<rbrakk> \<Longrightarrow> g \<in> eq_upto B f (Suc i)"
by (auto simp: eq_upto_def less_Suc_eq)

lemma eq_upto_0 [simp]:
  "eq_upto B f 0 = B"
by (auto simp: eq_upto_def)

lemma eq_upto_cong [fundef_cong]:
  assumes "\<And>j. j < i \<Longrightarrow> f j = g j" and "B = C"
  shows "eq_upto B f i = eq_upto C g i"
using assms by (auto simp: eq_upto_def)


subsection \<open>Lexicographic Order on Infinite Sequences\<close>

definition "LEX P f g \<longleftrightarrow> (\<exists>i::nat. P (f i) (g i) \<and> (\<forall>j<i. f j = g j))"
abbreviation "LEXEQ P \<equiv> (LEX P)\<^sup>=\<^sup>="

lemma LEX_imp_not_LEX:
  assumes "LEX P f g"
    and [dest]: "\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
    and [simp]: "\<And>x. \<not> P x x"
  shows "\<not> LEX P g f"
proof -
  { fix i j :: nat
    assume "P (f i) (g i)" and "\<forall>k<i. f k = g k"
      and "P (g j) (f j)" and "\<forall>k<j. g k = f k"
    then have False by (cases "i < j") (auto simp: not_less dest!: le_imp_less_or_eq) }
  then show "\<not> LEX P g f" using \<open>LEX P f g\<close> unfolding LEX_def by blast
qed

lemma LEX_cases:
  assumes "LEX P f g"
  obtains (eq) "f = g" | (neq) k where "\<forall>i<k. f i = g i" and "P (f k) (g k)"
using assms by (auto simp: LEX_def)

lemma LEX_imp_less:
  assumes "\<forall>x\<in>A. \<not> P x x" and "f \<in> SEQ A \<or> g \<in> SEQ A"
    and "LEX P f g" and "\<forall>i<k. f i = g i" and "f k \<noteq> g k"
  shows "P (f k) (g k)"
using assms by (auto elim!: LEX_cases) (metis linorder_neqE_nat)+

end
