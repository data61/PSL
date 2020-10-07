(*
  File:    IMO2019_Q1.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Q1\<close>
theory IMO2019_Q1
  imports Main
begin

text \<open>
  Consider a function \<open>f : \<int> \<rightarrow> \<int>\<close> that fulfils the functional equation
  \<open>f(2a) + 2f(b) = f(f(a+b))\<close> for all \<open>a, b \<in> \<int>\<close>.

  Then \<open>f\<close> is either identically 0 or of the form \<open>f(x) = 2x + c\<close> for some constant \<open>c \<in> \<int>\<close>.
\<close>

context
  fixes f :: "int \<Rightarrow> int" and m :: int
  assumes f_eq: "f (2 * a) + 2 * f b = f (f (a + b))"
  defines "m \<equiv> (f 0 - f (-2)) div 2"
begin

text \<open>
  We first show that \<open>f\<close> is affine with slope \<open>(f(0) - f(-2)) / 2\<close>.
  This follows from plugging in \<open>(0, b)\<close> and \<open>(-1, b + 1)\<close> into the functional equation.
\<close>
lemma f_eq': "f x = m * x + f 0"
proof -
  have rec: "f (b + 1) = f b + m" for b
    using f_eq[of 0 b] f_eq[of "-1" "b + 1"] by (simp add: m_def)
  moreover have "f (b - 1) = f b - m" for b
    using rec[of "b - 1"] by simp
  ultimately show ?thesis
    by (induction x rule: int_induct[of _ 0]) (auto simp: algebra_simps)
qed

text \<open>
  This version is better for the simplifier because it prevents it from looping.
\<close>
lemma f_eq'_aux [simp]: "NO_MATCH 0 x \<Longrightarrow> f x = m * x + f 0"
  by (rule f_eq')

text \<open>
  Plugging in \<open>(0, 0)\<close> and \<open>(0, 1)\<close>.
\<close>
lemma f_classification: "(\<forall>x. f x = 0) \<or> (\<forall>x. f x = 2 * x + f 0)"
  using f_eq[of 0 0] f_eq[of 0 1] by auto

end

text \<open>
  It is now easy to derive the full characterisation of the functions we considered:
\<close>
theorem
  fixes f :: "int \<Rightarrow> int"
  shows "(\<forall>a b. f (2 * a) + 2 * f b = f (f (a + b))) \<longleftrightarrow>
           (\<forall>x. f x = 0) \<or> (\<forall>x. f x = 2 * x + f 0)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs using f_classification[of f] by blast
next
  assume ?rhs
  thus ?lhs by smt
qed

end