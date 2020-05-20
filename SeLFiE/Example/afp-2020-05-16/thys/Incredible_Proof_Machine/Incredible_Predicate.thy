theory Incredible_Predicate imports
  Abstract_Rules_To_Incredible
  Predicate_Formulas
begin

text \<open>Our example interpretation with predicate logic will cover implication and the
  universal quantifier.\<close>

text \<open>The rules are introduction and elimination of implication and universal quantifiers.\<close>
datatype prop_rule = allI | allE | impI | impE

definition prop_rules :: "prop_rule stream"
  where "prop_rules = cycle [allI, allE, impI, impE]"

lemma iR_prop_rules [simp]: "sset prop_rules = {allI, allE, impI, impE}"
  unfolding prop_rules_def by simp

text \<open>Just some short notation.\<close>
abbreviation X :: "form"
  where "X \<equiv> Var 10 []"
abbreviation Y :: "form"
  where "Y \<equiv> Var 11 []"
abbreviation x :: "form"
  where "x \<equiv> Var 9 []"
abbreviation t :: "form"
  where "t \<equiv> Var 13 []"
abbreviation P :: "form \<Rightarrow> form"
  where "P f \<equiv> Var 12 [f]"
abbreviation Q :: "form \<Rightarrow> form"
  where "Q f \<equiv> Op ''Q'' [f]"
abbreviation imp :: "form \<Rightarrow> form \<Rightarrow> form"
  where "imp f1 f2 \<equiv> Op ''imp'' [f1, f2]"
abbreviation ForallX :: "form \<Rightarrow> form"
  where "ForallX f \<equiv> Quant ''all'' 9 f"

text \<open>Finally the right- and left-hand sides of the rules.\<close>

fun consequent :: "prop_rule \<Rightarrow> form list"
  where "consequent allI = [ForallX (P x)]"
  | "consequent allE = [P t]"
  | "consequent impI = [imp X Y]"
  | "consequent impE = [Y]"

abbreviation allI_input where "allI_input \<equiv> Antecedent {||} (P (LC 0)) {0}"
abbreviation impI_input where "impI_input \<equiv> Antecedent {|X|} Y {}"

fun antecedent :: "prop_rule \<Rightarrow> (form, lconst) antecedent list"
  where "antecedent allI = [allI_input]"
  | "antecedent allE = [plain_ant (ForallX (P x))]"
  | "antecedent impI = [impI_input]"
  | "antecedent impE = [plain_ant (imp X Y), plain_ant X]"

interpretation predicate: Abstract_Rules
  "curry to_nat :: nat \<Rightarrow> var \<Rightarrow> var"
  map_lc
  lc
  "closed"
  subst
  lc_subst
  map_lc_subst
  "Var 0 []"
  antecedent
  consequent
  prop_rules
proof
  show "\<forall>xs\<in>sset prop_rules. consequent xs \<noteq> []"
    unfolding prop_rules_def
    using consequent.elims by blast
next
  show "\<forall>xs\<in>sset prop_rules. \<Union>(lc ` set (consequent xs)) = {}"
    by auto
next
  fix i' r i ia
  assume "r \<in> sset prop_rules"
    and "ia < length (antecedent r)"
    and "i' < length (antecedent r)"
  then show "a_fresh (antecedent r ! ia) \<inter> a_fresh (antecedent r ! i') = {} \<or> ia = i'"
    by (cases i'; auto)
next
  fix r p
  assume "r \<in> sset prop_rules"
  and "p \<in> set (antecedent r)"
  thus "lc (a_conc p) \<union> \<Union>(lc ` fset (a_hyps p)) \<subseteq> a_fresh p" by auto
qed

end
