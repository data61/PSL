section \<open>Preliminaries\<close>

(*<*)
theory Prelim
imports "HOL-Library.Stream"
begin
(*>*)

abbreviation any where "any \<equiv> undefined"

lemma append_singl_rev: "a # as = [a] @ as" by simp

lemma list_pair_induct[case_names Nil Cons]:
assumes "P []" and "\<And>a b list. P list \<Longrightarrow> P ((a,b) # list)"
shows "P lista"
using assms by (induction lista) auto

lemma list_pair_case[elim, case_names Nil Cons]:
assumes "xs = [] \<Longrightarrow> P" and "\<And>a b list. xs = (a,b) # list \<Longrightarrow> P"
shows "P"
using assms by(cases xs, auto)

definition asList :: "'a set \<Rightarrow> 'a list" where
"asList A \<equiv> SOME as. distinct as \<and> set as = A"

lemma asList:
assumes "finite A" shows "distinct (asList A) \<and> set (asList A) = A"
unfolding asList_def by (rule someI_ex) (metis assms finite_distinct_list)

lemmas distinct_asList = asList[THEN conjunct1]
lemmas set_asList = asList[THEN conjunct2]


lemma map_sdrop[simp]: "sdrop 0 = id"
by (auto intro: ext)

lemma stl_o_sdrop[simp]: "stl o sdrop n = sdrop (Suc n)"
by (auto intro: ext)

lemma sdrop_o_stl[simp]: "sdrop n o stl = sdrop (Suc n)"
by (auto intro: ext)

lemma hd_stake[simp]: "i > 0 \<Longrightarrow> hd (stake i \<pi>) = shd \<pi>"
by (cases i) auto



(*<*)
end
(*>*)
