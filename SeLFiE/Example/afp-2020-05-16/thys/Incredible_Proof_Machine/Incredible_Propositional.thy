theory Incredible_Propositional imports
  Abstract_Rules_To_Incredible
  Propositional_Formulas
begin

text \<open>Our concrete interpretation with propositional logic will cover conjunction and implication
  as well as constant symbols. The type for variables will be @{typ string}.\<close>

datatype prop_funs = "and" | imp | Const "string"

text \<open>The rules are introduction and elimination of conjunction and implication.\<close>
datatype prop_rule = andI | andE | impI | impE

definition prop_rules :: "prop_rule stream"
  where "prop_rules = cycle [andI, andE, impI, impE]"

lemma iR_prop_rules [simp]: "sset prop_rules = {andI, andE, impI, impE}"
  unfolding prop_rules_def by simp

text \<open>Just some short notation.\<close>
abbreviation X :: "(string,'a) pform"
  where "X \<equiv> Var ''X''"
abbreviation Y :: "(string,'a) pform"
  where "Y \<equiv> Var ''Y''"

text \<open>Finally the right- and left-hand sides of the rules.\<close>

fun consequent :: "prop_rule \<Rightarrow> (string, prop_funs) pform list"
  where "consequent andI = [Fun and [X, Y]]"
  | "consequent andE = [X, Y]"
  | "consequent impI = [Fun imp [X, Y]]"
  | "consequent impE = [Y]"

fun antecedent :: "prop_rule \<Rightarrow> ((string,prop_funs) pform,string) antecedent list"
  where "antecedent andI = [plain_ant X, plain_ant Y]"
  | "antecedent andE = [plain_ant (Fun and [X, Y])]"
  | "antecedent impI = [Antecedent {|X|} Y {}]"
  | "antecedent impE = [plain_ant (Fun imp [X, Y]), plain_ant X]"


interpretation propositional: Abstract_Rules
  "curry (SOME f. bij f):: nat \<Rightarrow> string \<Rightarrow> string"
  "\<lambda>_. id"
  "\<lambda>_. {}"
  "closed :: (string, prop_funs) pform \<Rightarrow> bool"
  subst
  "\<lambda>_. {}"
  "\<lambda>_. id"
  "Var undefined"
  antecedent
  consequent
  prop_rules
proof
  show "\<forall>xs\<in>sset prop_rules. consequent xs \<noteq> []"
    unfolding prop_rules_def
    using consequent.elims by blast
next
  show "\<forall>xs\<in>sset prop_rules. \<Union>((\<lambda>_. {}) ` set (consequent xs)) = {}"
    by clarsimp
next
  fix i' r i ia
  assume "r \<in> sset prop_rules"
    and "ia < length (antecedent r)"
    and "i' < length (antecedent r)"
  then show "a_fresh (antecedent r ! ia) \<inter> a_fresh (antecedent r ! i') = {} \<or> ia = i'"
    by (cases i'; auto)
next
  fix p
  show "{} \<union> \<Union>((\<lambda>_. {}) ` fset (a_hyps p)) \<subseteq> a_fresh p"  by clarsimp
qed

end
