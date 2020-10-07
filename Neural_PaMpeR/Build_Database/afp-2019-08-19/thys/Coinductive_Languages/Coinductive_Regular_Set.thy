section \<open>Coinductively Defined Operations Are Standard\<close>

(*<*)
theory Coinductive_Regular_Set
imports "Regular-Sets.Regular_Set" Coinductive_Language
begin
(*>*)

lemma to_language_empty[simp]: "to_language {} = Zero"
  by (coinduction) auto

lemma in_language_Zero[simp]: "\<not> in_language Zero xs"
  by (induct xs) auto

lemma in_language_One[simp]: "in_language One xs \<Longrightarrow> xs = []"
  by (cases xs) auto

lemma in_language_Atom[simp]: "in_language (Atom a) xs \<Longrightarrow> xs = [a]"
  by (cases xs) (auto split: if_splits)

lemma to_language_eps[simp]: "to_language {[]} = One"
  by (rule bij_is_inj[OF in_language_bij, THEN injD]) auto

lemma to_language_singleton[simp]: "to_language {[a]} = (Atom a)"
  by (rule bij_is_inj[OF in_language_bij, THEN injD]) auto

lemma to_language_Un[simp]: "to_language (A \<union> B) = Plus (to_language A) (to_language B)"
  by (coinduction arbitrary: A B) (auto simp: Collect_disj_eq)

lemma to_language_Int[simp]: "to_language (A \<inter> B) = Inter (to_language A) (to_language B)"
  by (coinduction arbitrary: A B) (auto simp: Collect_conj_eq)

lemma to_language_Neg[simp]: "to_language (- A) = Not (to_language A)"
  by (coinduction arbitrary: A) (auto simp: Collect_neg_eq)

lemma to_language_Diff[simp]: "to_language (A - B) = Inter (to_language A) (Not (to_language B))"
  by (auto simp: Diff_eq)

lemma to_language_conc[simp]: "to_language (A @@ B) = Times (to_language A) (to_language B)"
  by (coinduction arbitrary: A B rule: language_coinduct_upto_Plus)
    (auto simp: Deriv_def[symmetric])

lemma to_language_star[simp]: "to_language (star A) = Star (to_language A)"
  by (coinduction arbitrary: A rule: language_coinduct_upto_regular)
    (auto simp: Deriv_def[symmetric])

lemma to_language_shuffle[simp]: "to_language (A \<parallel> B) = Shuffle (to_language A) (to_language B)"
  by (coinduction arbitrary: A B rule: language_coinduct_upto_Plus)
    (force simp: Deriv_def[symmetric])

(*<*)
end
(*>*)
