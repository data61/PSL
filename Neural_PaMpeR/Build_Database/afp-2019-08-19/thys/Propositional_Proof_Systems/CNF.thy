subsection\<open>Conjunctive Normal Forms\<close>
theory CNF
imports Main "HOL-Library.Simps_Case_Conv"
begin

datatype 'a literal = Pos 'a ("(_\<^sup>+)" [1000] 999) | Neg 'a ("(_\<inverse>)" [1000] 999)

type_synonym 'a clause = "'a literal set"
abbreviation empty_clause ("\<box>" (* \box *)) where "\<box> \<equiv> {} :: 'a clause"
(* unfortunately, we'll also have those as lists, occasionally. *)

primrec atoms_of_lit where
"atoms_of_lit (Pos k) = k" |
"atoms_of_lit (Neg k) = k"
case_of_simps lit_atoms_cases: atoms_of_lit.simps

definition "atoms_of_cnf c = atoms_of_lit ` \<Union>c"
lemma atoms_of_cnf_alt: "atoms_of_cnf c = \<Union>(((`) atoms_of_lit) ` c)" 
  unfolding atoms_of_cnf_def by blast (* alt as in the German alt *)

lemma atoms_of_cnf_Un: "atoms_of_cnf (S \<union> T) = atoms_of_cnf S \<union> atoms_of_cnf T"
  unfolding atoms_of_cnf_def by auto

(* unbreak set printing *)
term "{0\<^sup>+}::nat clause"
translations
  "{x}" <= "CONST insert x \<box>"
term "{0\<^sup>+}::nat clause"
(* hope nobody ever loads this with some other definition for \<box> *)

end
