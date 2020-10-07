(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: List_Lexord_Alt.thy                                                  *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section \<open>Alternative List Lexicographic Order\<close>

theory List_Lexord_Alt
  imports Main
begin

text \<open> Since we can't instantiate the order class twice for lists, and we want prefix as
  the default order for the UTP we here add syntax for the lexicographic order relation. \<close>

definition list_lex_less :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "<\<^sub>l" 50)
where "xs <\<^sub>l ys \<longleftrightarrow> (xs, ys) \<in> lexord {(u, v). u < v}"

lemma list_lex_less_neq [simp]: "x <\<^sub>l y \<Longrightarrow> x \<noteq> y"
  apply (simp add: list_lex_less_def)
  apply (meson case_prodD less_irrefl lexord_irreflexive mem_Collect_eq)
done

lemma not_less_Nil [simp]: "\<not> x <\<^sub>l []"
  by (simp add: list_lex_less_def)

lemma Nil_less_Cons [simp]: "[] <\<^sub>l a # x"
  by (simp add: list_lex_less_def)

lemma Cons_less_Cons [simp]: "a # x <\<^sub>l b # y \<longleftrightarrow> a < b \<or> a = b \<and> x <\<^sub>l y"
  by (simp add: list_lex_less_def)
end