subsection\<open>Implication-only formulas\<close>

theory MiniFormulas
imports Formulas
begin

fun is_mini_formula where
"is_mini_formula (Atom _) = True" |
"is_mini_formula \<bottom> = True" |
"is_mini_formula (Imp F G) = (is_mini_formula F \<and> is_mini_formula G)" |
"is_mini_formula _ = False"

text\<open>
  The similarity between these ``mini'' formulas and Johansson's minimal calculus of implications~\cite{johansson1937minimal} is mostly in name.
  Johansson does replace @{term "\<^bold>\<not> F"} by @{term "F \<^bold>\<rightarrow> \<bottom>"} in one place, but generally keeps it.
  The main focus of ~\cite{johansson1937minimal} is on removing rules from Calculi anyway, not on removing connectives.
  We are only borrowing the name.\<close>

(*lemma mini_Top[simp,intro!]: "is_mini_formula \<top>" unfolding Top_def by simp *)

primrec to_mini_formula where
"to_mini_formula (Atom k) = Atom k" |
"to_mini_formula \<bottom> = \<bottom>" |
"to_mini_formula (Imp F G) = to_mini_formula F \<^bold>\<rightarrow> to_mini_formula G" |
"to_mini_formula (Not F) = to_mini_formula F \<^bold>\<rightarrow> \<bottom>" |
"to_mini_formula (And F G) = (to_mini_formula F \<^bold>\<rightarrow> (to_mini_formula G \<^bold>\<rightarrow> \<bottom>)) \<^bold>\<rightarrow> \<bottom>" |
"to_mini_formula (Or F G) = (to_mini_formula F \<^bold>\<rightarrow> \<bottom>) \<^bold>\<rightarrow> to_mini_formula G"

lemma to_mini_is_mini[simp,intro!]: "is_mini_formula (to_mini_formula F)"
  by(induction F; simp)
lemma mini_to_mini: "is_mini_formula F \<Longrightarrow> to_mini_formula F = F"
  by(induction F; simp)
corollary mini_mini[simp]: "to_mini_formula (to_mini_formula F) = to_mini_formula F"
  using mini_to_mini[OF to_mini_is_mini] .

text\<open>We could have used an arbitrary other combination,
  e.g. @{const Atom}, @{const Not}, and @{const And}.
The choice for @{const Atom}, @{term \<bottom>}, and @{const Imp} was made because it is
 (to the best of my knowledge) the only combination that only requires three elements and verifies:\<close>
lemma mini_formula_atoms: "atoms (to_mini_formula F) = atoms F"
 by(induction F; simp)
text\<open>(The story would be different if we had different junctors, e.g. if we allowed a NAND.)\<close>

end
