(* Author: Tobias Nipkow *)

section "Extended Regular Expressions"

theory Regular_Exp2
imports Regular_Set
begin

datatype (atoms: 'a) rexp =
  is_Zero: Zero |
  is_One: One |
  Atom 'a |
  Plus "('a rexp)" "('a rexp)" |
  Times "('a rexp)" "('a rexp)" |
  Star "('a rexp)" |
  Not "('a rexp)" |
  Inter "('a rexp)" "('a rexp)"

context
fixes S :: "'a set"
begin

primrec lang :: "'a rexp => 'a lang" where
"lang Zero = {}" |
"lang One = {[]}" |
"lang (Atom a) = {[a]}" |
"lang (Plus r s) = (lang r) Un (lang s)" |
"lang (Times r s) = conc (lang r) (lang s)" |
"lang (Star r) = star(lang r)" |
"lang (Not r) = lists S - lang r" |
"lang (Inter r s) = (lang r Int lang s)"

end

lemma lang_subset_lists: "atoms r \<subseteq> S \<Longrightarrow> lang S r \<subseteq> lists S"
by(induction r)(auto simp: conc_subset_lists star_subset_lists)

primrec nullable :: "'a rexp \<Rightarrow> bool" where
"nullable Zero = False" |
"nullable One = True" |
"nullable (Atom c) = False" |
"nullable (Plus r1 r2) = (nullable r1 \<or> nullable r2)" |
"nullable (Times r1 r2) = (nullable r1 \<and> nullable r2)" |
"nullable (Star r) = True" |
"nullable (Not r) = (\<not> (nullable r))" |
"nullable (Inter r s) = (nullable r \<and> nullable s)"

lemma nullable_iff: "nullable r \<longleftrightarrow> [] \<in> lang S r"
by (induct r) (auto simp add: conc_def split: if_splits)

end
