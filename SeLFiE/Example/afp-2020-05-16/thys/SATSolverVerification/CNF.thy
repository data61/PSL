(*    Title:              SATSolver/CNF.thy
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

section \<open>CNF\<close>
theory CNF
imports MoreList
begin
text\<open>Theory describing formulae in Conjunctive Normal Form.\<close>


(********************************************************************)
subsection\<open>Syntax\<close>
(********************************************************************)

(*------------------------------------------------------------------*)
subsubsection\<open>Basic datatypes\<close>
type_synonym Variable  = nat
datatype Literal = Pos Variable | Neg Variable
type_synonym Clause = "Literal list"
type_synonym Formula = "Clause list"

text\<open>Notice that instead of set or multisets, lists are used in
definitions of clauses and formulae. This is done because SAT solver
implementation usually use list-like data structures for representing
these datatypes.\<close>

(*------------------------------------------------------------------*)
subsubsection\<open>Membership\<close>

text\<open>Check if the literal is member of a clause, clause is a member 
  of a formula or the literal is a member of a formula\<close>
consts member  :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infixl "el" 55)

overloading literalElClause \<equiv> "member :: Literal \<Rightarrow> Clause \<Rightarrow> bool"
begin
  definition [simp]: "((literal::Literal) el (clause::Clause)) == literal \<in> set clause"
end

overloading clauseElFormula \<equiv> "member :: Clause \<Rightarrow> Formula \<Rightarrow> bool"
begin
  definition [simp]: "((clause::Clause) el (formula::Formula)) == clause \<in> set formula"
end

overloading el_literal \<equiv> "(el) :: Literal \<Rightarrow> Formula \<Rightarrow> bool"
begin

primrec el_literal where
"(literal::Literal) el ([]::Formula) = False" |
"((literal::Literal) el ((clause # formula)::Formula)) = ((literal el clause) \<or> (literal el formula))"

end

lemma literalElFormulaCharacterization:
  fixes literal :: Literal and formula :: Formula
  shows "(literal el formula) = (\<exists> (clause::Clause). clause el formula \<and> literal el clause)"
by (induct formula) auto


(*------------------------------------------------------------------*)
subsubsection\<open>Variables\<close>

text\<open>The variable of a given literal\<close>
primrec 
var      :: "Literal \<Rightarrow> Variable"
where 
  "var (Pos v) = v"
| "var (Neg v) = v"

text\<open>Set of variables of a given clause, formula or valuation\<close>
primrec
varsClause :: "(Literal list) \<Rightarrow> (Variable set)"
where
  "varsClause [] = {}"
| "varsClause (literal # list) = {var literal} \<union> (varsClause list)"

primrec
varsFormula :: "Formula \<Rightarrow> (Variable set)"
where
  "varsFormula [] = {}"
| "varsFormula (clause # formula) = (varsClause clause) \<union> (varsFormula formula)"

consts vars :: "'a \<Rightarrow> Variable set"

overloading vars_clause \<equiv> "vars :: Clause \<Rightarrow> Variable set"
begin
  definition [simp]: "vars (clause::Clause) == varsClause clause"
end

overloading vars_formula \<equiv> "vars :: Formula \<Rightarrow> Variable set"
begin
  definition [simp]: "vars (formula::Formula) == varsFormula formula"
end

overloading vars_set \<equiv> "vars :: Literal set \<Rightarrow> Variable set"
begin
  definition [simp]: "vars (s::Literal set) == {vbl. \<exists> l. l \<in> s \<and> var l = vbl}"
end

lemma clauseContainsItsLiteralsVariable: 
  fixes literal :: Literal and clause :: Clause
  assumes "literal el clause"
  shows "var literal \<in> vars clause"
using assms
by (induct clause) auto

lemma formulaContainsItsLiteralsVariable:
  fixes literal :: Literal and formula::Formula
  assumes "literal el formula" 
  shows "var literal \<in> vars formula"
using assms
proof (induct formula)
  case Nil
  thus ?case 
    by simp
next
  case (Cons clause formula)
  thus ?case
  proof (cases "literal el clause")
    case True
    with clauseContainsItsLiteralsVariable
    have "var literal \<in> vars clause" 
      by simp
    thus ?thesis 
      by simp
  next
    case False
    with Cons
    show ?thesis 
      by simp
  qed
qed

lemma formulaContainsItsClausesVariables:
  fixes clause :: Clause and formula :: Formula
  assumes "clause el formula"
  shows "vars clause \<subseteq> vars formula"
using assms
by (induct formula) auto

lemma varsAppendFormulae:
  fixes formula1 :: Formula and formula2 :: Formula
  shows "vars (formula1 @ formula2) = vars formula1 \<union> vars formula2"
by (induct formula1) auto

lemma varsAppendClauses:
  fixes clause1 :: Clause and clause2 :: Clause
  shows "vars (clause1 @ clause2) = vars clause1 \<union> vars clause2"
by (induct clause1) auto

lemma varsRemoveLiteral:
  fixes literal :: Literal and clause :: Clause
  shows "vars (removeAll literal clause) \<subseteq> vars clause"
by (induct clause) auto

lemma varsRemoveLiteralSuperset:
  fixes literal :: Literal and clause :: Clause
  shows "vars clause - {var literal}  \<subseteq> vars (removeAll literal clause)"
by (induct clause) auto

lemma varsRemoveAllClause:
  fixes clause :: Clause and formula :: Formula
  shows "vars (removeAll clause formula) \<subseteq> vars formula"
by (induct formula) auto

lemma varsRemoveAllClauseSuperset:
  fixes clause :: Clause and formula :: Formula
  shows "vars formula - vars clause \<subseteq> vars (removeAll clause formula)"
by (induct formula) auto

lemma varInClauseVars:
  fixes variable :: Variable and clause :: Clause
  shows "variable \<in> vars clause = (\<exists> literal. literal el clause \<and> var literal = variable)"
by (induct clause) auto

lemma varInFormulaVars: 
  fixes variable :: Variable and formula :: Formula
  shows "variable \<in> vars formula = (\<exists> literal. literal el formula \<and> var literal = variable)" (is "?lhs formula = ?rhs formula")
proof (induct formula)
  case Nil
  show ?case 
    by simp
next
  case (Cons clause formula)
  show ?case
  proof
    assume P: "?lhs (clause # formula)"
    thus "?rhs (clause # formula)"
    proof (cases "variable \<in> vars clause")
      case True
      with varInClauseVars 
      have "\<exists> literal. literal el clause \<and> var literal = variable" 
        by simp
      thus ?thesis 
        by auto
    next
      case False
      with P 
      have "variable \<in> vars formula" 
        by simp
      with Cons
      show ?thesis 
        by auto
    qed
  next
    assume "?rhs (clause # formula)"
    then obtain l 
      where lEl: "l el clause # formula" and varL:"var l = variable" 
      by auto
    from lEl formulaContainsItsLiteralsVariable [of "l" "clause # formula"] 
    have "var l \<in> vars (clause # formula)" 
      by auto
    with varL 
    show "?lhs (clause # formula)" 
      by simp
  qed
qed

lemma varsSubsetFormula:
  fixes F :: Formula and F' :: Formula
  assumes "\<forall> c::Clause. c el F \<longrightarrow> c el F'"
  shows "vars F \<subseteq> vars F'"
using assms
proof (induct F)
  case Nil
  thus ?case
    by simp
next
  case (Cons c' F'')
  thus ?case
    using formulaContainsItsClausesVariables[of "c'" "F'"]
    by simp
qed

lemma varsClauseVarsSet:
fixes 
  clause :: Clause
shows
  "vars clause = vars (set clause)"
by (induct clause) auto


(*------------------------------------------------------------------*)
subsubsection\<open>Opposite literals\<close>

primrec
opposite :: "Literal \<Rightarrow> Literal"
where
  "opposite (Pos v) = (Neg v)"
| "opposite (Neg v) = (Pos v)"

lemma oppositeIdempotency [simp]:
  fixes literal::Literal
  shows "opposite (opposite literal) = literal"
by (induct literal) auto

lemma oppositeSymmetry [simp]:
  fixes literal1::Literal and literal2::Literal
  shows "(opposite literal1 = literal2) = (opposite literal2 = literal1)"
by auto

lemma oppositeUniqueness [simp]:
  fixes literal1::Literal and literal2::Literal
  shows "(opposite literal1 = opposite literal2) = (literal1 = literal2)"
proof
  assume "opposite literal1 = opposite literal2"
  hence "opposite (opposite literal1) = opposite (opposite literal2)" 
    by simp
  thus "literal1 = literal2" 
    by simp 
qed simp

lemma oppositeIsDifferentFromLiteral [simp]:
  fixes literal::Literal
  shows "opposite literal \<noteq> literal"
by (induct literal) auto

lemma oppositeLiteralsHaveSameVariable [simp]:
  fixes literal::Literal
  shows "var (opposite literal) = var literal"
by (induct literal) auto

lemma literalsWithSameVariableAreEqualOrOpposite:
  fixes literal1::Literal and literal2::Literal
  shows "(var literal1 = var literal2) = (literal1 = literal2 \<or> opposite literal1 = literal2)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  show ?rhs
  proof (cases literal1)
    case "Pos"
    note Pos1 = this
    show ?thesis
    proof (cases literal2)
      case "Pos"
      with \<open>?lhs\<close> Pos1 show ?thesis 
        by simp
    next
      case "Neg"
      with \<open>?lhs\<close> Pos1 show ?thesis 
        by simp
    qed
  next
    case "Neg"
    note Neg1 = this
    show ?thesis
    proof (cases literal2)
      case "Pos"
      with \<open>?lhs\<close> Neg1 show ?thesis 
        by simp
    next
      case "Neg"
      with \<open>?lhs\<close> Neg1 show ?thesis 
        by simp
    qed
  qed
next
  assume ?rhs
  thus ?lhs 
    by auto
qed

text\<open>The list of literals obtained by negating all literals of a
literal list (clause, valuation). Notice that this is not a negation 
of a clause, because the negation of a clause is a conjunction and 
not a disjunction.\<close>
definition
oppositeLiteralList :: "Literal list \<Rightarrow> Literal list"
where
"oppositeLiteralList clause == map opposite clause"

lemma literalElListIffOppositeLiteralElOppositeLiteralList: 
  fixes literal :: Literal and literalList :: "Literal list"
  shows "literal el literalList = (opposite literal) el (oppositeLiteralList literalList)"
unfolding oppositeLiteralList_def
proof (induct literalList)
  case Nil
  thus ?case
    by simp
next
  case (Cons l literalLlist')
  show ?case
  proof (cases "l = literal")
    case True
    thus ?thesis
      by simp
  next
    case False
    thus ?thesis
      by auto
  qed
qed

lemma oppositeLiteralListIdempotency [simp]: 
  fixes literalList :: "Literal list"
  shows "oppositeLiteralList (oppositeLiteralList literalList) = literalList"
unfolding oppositeLiteralList_def
by (induct literalList) auto

lemma oppositeLiteralListRemove: 
  fixes literal :: Literal and literalList :: "Literal list"
  shows "oppositeLiteralList (removeAll literal literalList) = removeAll (opposite literal) (oppositeLiteralList literalList)"
unfolding oppositeLiteralList_def
by (induct literalList) auto

lemma oppositeLiteralListNonempty:
  fixes literalList :: "Literal list"
  shows "(literalList \<noteq> []) = ((oppositeLiteralList literalList) \<noteq> [])"
unfolding oppositeLiteralList_def
by (induct literalList) auto

lemma varsOppositeLiteralList:
shows "vars (oppositeLiteralList clause) = vars clause"
unfolding oppositeLiteralList_def
by (induct clause) auto


(*------------------------------------------------------------------*)
subsubsection\<open>Tautological clauses\<close>

text\<open>Check if the clause contains both a literal and its opposite\<close>
primrec
clauseTautology :: "Clause \<Rightarrow> bool"
where
  "clauseTautology [] = False"
| "clauseTautology (literal # clause) = (opposite literal el clause \<or> clauseTautology clause)"

lemma clauseTautologyCharacterization: 
  fixes clause :: Clause
  shows "clauseTautology clause = (\<exists> literal. literal el clause \<and> (opposite literal) el clause)"
by (induct clause) auto


(********************************************************************)
subsection\<open>Semantics\<close>
(********************************************************************)

(*------------------------------------------------------------------*)
subsubsection\<open>Valuations\<close>

type_synonym Valuation = "Literal list"

lemma valuationContainsItsLiteralsVariable: 
  fixes literal :: Literal and valuation :: Valuation
  assumes "literal el valuation"
  shows "var literal \<in> vars valuation"
using assms
by (induct valuation) auto

lemma varsSubsetValuation: 
  fixes valuation1 :: Valuation and valuation2 :: Valuation
  assumes "set valuation1  \<subseteq> set valuation2"
  shows "vars valuation1 \<subseteq> vars valuation2"
using assms
proof (induct valuation1)
  case Nil
  show ?case 
    by simp
next
  case (Cons literal valuation)
  note caseCons = this
  hence "literal el valuation2" 
    by auto
  with valuationContainsItsLiteralsVariable [of "literal" "valuation2"]
  have "var literal \<in> vars valuation2" .
  with caseCons 
  show ?case 
    by simp
qed

lemma varsAppendValuation:
  fixes valuation1 :: Valuation and valuation2 :: Valuation
  shows "vars (valuation1 @ valuation2) = vars valuation1 \<union> vars valuation2"
by (induct valuation1) auto
lemma varsPrefixValuation:
  fixes valuation1 :: Valuation and valuation2 :: Valuation
  assumes "isPrefix valuation1 valuation2"
  shows "vars valuation1 \<subseteq> vars valuation2"
proof-
  from assms 
  have "set valuation1 \<subseteq> set valuation2"
    by (auto simp add:isPrefix_def)
  thus ?thesis
    by (rule varsSubsetValuation)
qed

(*------------------------------------------------------------------*)
subsubsection\<open>True/False literals\<close>

text\<open>Check if the literal is contained in the given valuation\<close>
definition literalTrue     :: "Literal \<Rightarrow> Valuation \<Rightarrow> bool"
where
literalTrue_def [simp]: "literalTrue literal valuation == literal el valuation"

text\<open>Check if the opposite literal is contained in the given valuation\<close>
definition literalFalse    :: "Literal \<Rightarrow> Valuation \<Rightarrow> bool"
where
literalFalse_def [simp]: "literalFalse literal valuation == opposite literal el valuation"


lemma variableDefinedImpliesLiteralDefined:
  fixes literal :: Literal and valuation :: Valuation
  shows "var literal \<in> vars valuation = (literalTrue literal valuation \<or> literalFalse literal valuation)" 
    (is "(?lhs valuation) = (?rhs valuation)")
proof
  assume "?rhs valuation"
  thus "?lhs valuation" 
  proof
    assume "literalTrue literal valuation"
    hence "literal el valuation" 
      by simp
    thus ?thesis
      using valuationContainsItsLiteralsVariable[of "literal" "valuation"] 
      by simp
  next
    assume "literalFalse literal valuation"
    hence "opposite literal el valuation" 
      by simp
    thus ?thesis
      using valuationContainsItsLiteralsVariable[of "opposite literal" "valuation"] 
      by simp
  qed
next
  assume "?lhs valuation" 
  thus "?rhs valuation"
  proof (induct valuation)
    case Nil
    thus ?case 
      by simp
  next
    case (Cons literal' valuation')
    note ih=this
    show ?case
    proof (cases "var literal \<in> vars valuation'")
      case True
      with ih 
      show "?rhs (literal' # valuation')" 
        by auto
    next
      case False
      with ih 
      have "var literal' = var literal" 
        by simp
      hence "literal' = literal \<or> opposite literal' = literal"
        by (simp add:literalsWithSameVariableAreEqualOrOpposite)
      thus "?rhs (literal' # valuation')" 
        by auto
    qed
  qed
qed

(*------------------------------------------------------------------*)
subsubsection\<open>True/False clauses\<close>

text\<open>Check if there is a literal from the clause which is true in the given valuation\<close>
primrec
clauseTrue      :: "Clause \<Rightarrow> Valuation \<Rightarrow> bool"
where
  "clauseTrue [] valuation = False"
| "clauseTrue (literal # clause) valuation = (literalTrue literal valuation \<or> clauseTrue clause valuation)"

text\<open>Check if all the literals from the clause are false in the given valuation\<close>
primrec
clauseFalse     :: "Clause \<Rightarrow> Valuation \<Rightarrow> bool"
where
  "clauseFalse [] valuation = True"
| "clauseFalse (literal # clause) valuation = (literalFalse literal valuation \<and> clauseFalse clause valuation)"


lemma clauseTrueIffContainsTrueLiteral: 
  fixes clause :: Clause and valuation :: Valuation  
  shows "clauseTrue clause valuation = (\<exists> literal. literal el clause \<and> literalTrue literal valuation)"
by (induct clause) auto

lemma clauseFalseIffAllLiteralsAreFalse:
  fixes clause :: Clause and valuation :: Valuation  
  shows "clauseFalse clause valuation = (\<forall> literal. literal el clause \<longrightarrow> literalFalse literal valuation)"
by (induct clause) auto

lemma clauseFalseRemove:
  assumes "clauseFalse clause valuation"
  shows "clauseFalse (removeAll literal clause) valuation"
proof-
  {
    fix l::Literal
    assume "l el removeAll literal clause"
    hence "l el clause"
      by simp
   with \<open>clauseFalse clause valuation\<close> 
   have "literalFalse l valuation"
     by (simp add:clauseFalseIffAllLiteralsAreFalse)
  }
  thus ?thesis
    by (simp add:clauseFalseIffAllLiteralsAreFalse)
qed

lemma clauseFalseAppendValuation: 
  fixes clause :: Clause and valuation :: Valuation and valuation' :: Valuation
  assumes "clauseFalse clause valuation"
  shows "clauseFalse clause (valuation @ valuation')"
using assms
by (induct clause) auto

lemma clauseTrueAppendValuation:
  fixes clause :: Clause and valuation :: Valuation and valuation' :: Valuation
  assumes "clauseTrue clause valuation"
  shows "clauseTrue clause (valuation @ valuation')"
using assms
by (induct clause) auto

lemma emptyClauseIsFalse:
  fixes valuation :: Valuation
  shows "clauseFalse [] valuation"
by auto

lemma emptyValuationFalsifiesOnlyEmptyClause:
  fixes clause :: Clause
  assumes "clause \<noteq> []"
  shows "\<not>  clauseFalse clause []"
using assms
by (induct clause) auto
  

lemma valuationContainsItsFalseClausesVariables:
  fixes clause::Clause and valuation::Valuation
  assumes "clauseFalse clause valuation"
  shows "vars clause \<subseteq> vars valuation"
proof
  fix v::Variable
  assume "v \<in> vars clause"
  hence "\<exists> l. var l = v \<and> l el clause"
    by (induct clause) auto
  then obtain l 
    where "var l = v" "l el clause"
    by auto
  from \<open>l el clause\<close> \<open>clauseFalse clause valuation\<close>
  have "literalFalse l valuation"
    by (simp add: clauseFalseIffAllLiteralsAreFalse)
  with \<open>var l = v\<close> 
  show "v \<in> vars valuation"
    using valuationContainsItsLiteralsVariable[of "opposite l"]
    by simp
qed
  

(*------------------------------------------------------------------*)
subsubsection\<open>True/False formulae\<close>

text\<open>Check if all the clauses from the formula are false in the given valuation\<close>
primrec
formulaTrue     :: "Formula \<Rightarrow> Valuation \<Rightarrow> bool"
where
  "formulaTrue [] valuation = True"
| "formulaTrue (clause # formula) valuation = (clauseTrue clause valuation \<and> formulaTrue formula valuation)"

text\<open>Check if there is a clause from the formula which is false in the given valuation\<close>
primrec
formulaFalse    :: "Formula \<Rightarrow> Valuation \<Rightarrow> bool"
where
  "formulaFalse [] valuation = False"
| "formulaFalse (clause # formula) valuation = (clauseFalse clause valuation \<or> formulaFalse formula valuation)"


lemma formulaTrueIffAllClausesAreTrue: 
  fixes formula :: Formula and valuation :: Valuation
  shows "formulaTrue formula valuation = (\<forall> clause. clause el formula \<longrightarrow> clauseTrue clause valuation)"
by (induct formula) auto

lemma formulaFalseIffContainsFalseClause: 
  fixes formula :: Formula and valuation :: Valuation
  shows "formulaFalse formula valuation = (\<exists> clause. clause el formula \<and> clauseFalse clause valuation)"
by (induct formula) auto

lemma formulaTrueAssociativity:
  fixes f1 :: Formula and f2 :: Formula and f3 :: Formula and valuation :: Valuation
  shows "formulaTrue ((f1 @ f2) @ f3) valuation = formulaTrue (f1 @ (f2 @ f3)) valuation"
by (auto simp add:formulaTrueIffAllClausesAreTrue)

lemma formulaTrueCommutativity:
  fixes f1 :: Formula and f2 :: Formula and valuation :: Valuation
  shows "formulaTrue (f1 @ f2) valuation = formulaTrue (f2 @ f1) valuation"
by (auto simp add:formulaTrueIffAllClausesAreTrue)

lemma formulaTrueSubset:
  fixes formula :: Formula and formula' :: Formula and valuation :: Valuation
  assumes 
  formulaTrue: "formulaTrue formula valuation" and
  subset: "\<forall> (clause::Clause). clause el formula' \<longrightarrow> clause el formula"
  shows "formulaTrue formula' valuation"
proof -
  {
    fix clause :: Clause
    assume "clause el formula'"
    with formulaTrue subset 
    have "clauseTrue clause valuation"
      by (simp add:formulaTrueIffAllClausesAreTrue)
  }
  thus ?thesis
    by (simp add:formulaTrueIffAllClausesAreTrue)
qed

lemma formulaTrueAppend:
  fixes formula1 :: Formula and formula2 :: Formula and valuation :: Valuation
  shows "formulaTrue (formula1 @ formula2) valuation = (formulaTrue formula1 valuation \<and> formulaTrue formula2 valuation)"
by (induct formula1) auto

lemma formulaTrueRemoveAll:
  fixes formula :: Formula and clause :: Clause and valuation :: Valuation    
  assumes "formulaTrue formula valuation"
  shows "formulaTrue (removeAll clause formula) valuation"
using assms
by (induct formula) auto

lemma formulaFalseAppend: 
  fixes formula :: Formula and formula' :: Formula and valuation :: Valuation  
  assumes "formulaFalse formula valuation"
  shows "formulaFalse (formula @ formula') valuation"
using assms 
by (induct formula) auto

lemma formulaTrueAppendValuation: 
  fixes formula :: Formula and valuation :: Valuation and valuation' :: Valuation
  assumes "formulaTrue formula valuation"
  shows "formulaTrue formula (valuation @ valuation')"
using assms
by (induct formula) (auto simp add:clauseTrueAppendValuation)

lemma formulaFalseAppendValuation: 
  fixes formula :: Formula and valuation :: Valuation and valuation' :: Valuation
  assumes "formulaFalse formula valuation"
  shows "formulaFalse formula (valuation @ valuation')"
using assms
by (induct formula) (auto simp add:clauseFalseAppendValuation)

lemma trueFormulaWithSingleLiteralClause:
  fixes formula :: Formula and literal :: Literal and valuation :: Valuation
  assumes "formulaTrue (removeAll [literal] formula) (valuation @ [literal])"
  shows "formulaTrue formula (valuation @ [literal])"
proof -
  {
    fix clause :: Clause
    assume "clause el formula"
    with assms 
    have "clauseTrue clause (valuation @ [literal])"
    proof (cases "clause = [literal]")
      case True
      thus ?thesis
        by simp
    next
      case False
      with \<open>clause el formula\<close>
      have "clause el (removeAll [literal] formula)"
        by simp
      with \<open>formulaTrue (removeAll [literal] formula) (valuation @ [literal])\<close> 
      show ?thesis
        by (simp add: formulaTrueIffAllClausesAreTrue)
    qed
  }
  thus ?thesis
    by (simp add: formulaTrueIffAllClausesAreTrue)
qed

(*------------------------------------------------------------------*)
subsubsection\<open>Valuation viewed as a formula\<close>

text\<open>Converts a valuation (the list of literals) into formula (list of single member lists of literals)\<close>
primrec
val2form    :: "Valuation \<Rightarrow> Formula"
where
  "val2form [] = []"
| "val2form (literal # valuation) = [literal] # val2form valuation"

lemma val2FormEl: 
  fixes literal :: Literal and valuation :: Valuation 
  shows "literal el valuation = [literal] el val2form valuation"
by (induct valuation) auto

lemma val2FormAreSingleLiteralClauses: 
  fixes clause :: Clause and valuation :: Valuation
  shows "clause el val2form valuation \<longrightarrow> (\<exists> literal. clause = [literal] \<and> literal el valuation)"
by (induct valuation) auto

lemma val2formOfSingleLiteralValuation:
assumes "length v = 1"
shows "val2form v = [[hd v]]"
using assms
by (induct v) auto

lemma val2FormRemoveAll: 
  fixes literal :: Literal and valuation :: Valuation 
  shows "removeAll [literal] (val2form valuation) = val2form (removeAll literal valuation)"
by (induct valuation) auto

lemma val2formAppend: 
  fixes valuation1 :: Valuation and valuation2 :: Valuation
  shows "val2form (valuation1 @ valuation2) = (val2form valuation1 @ val2form valuation2)"
by (induct valuation1) auto

lemma val2formFormulaTrue: 
  fixes valuation1 :: Valuation and valuation2 :: Valuation
  shows "formulaTrue (val2form valuation1) valuation2 = (\<forall> (literal :: Literal). literal el valuation1 \<longrightarrow> literal el valuation2)"
by (induct valuation1) auto


(*------------------------------------------------------------------*)
subsubsection\<open>Consistency of valuations\<close>

text\<open>Valuation is inconsistent if it contains both a literal and its opposite.\<close>
primrec
inconsistent   :: "Valuation \<Rightarrow> bool"
where
  "inconsistent [] = False"
| "inconsistent (literal # valuation) = (opposite literal el valuation \<or> inconsistent valuation)"
definition [simp]: "consistent valuation == \<not> inconsistent valuation"

lemma inconsistentCharacterization: 
  fixes valuation :: Valuation
  shows "inconsistent valuation = (\<exists> literal. literalTrue literal valuation \<and> literalFalse literal valuation)"
by (induct valuation) auto

lemma clauseTrueAndClauseFalseImpliesInconsistent: 
  fixes clause :: Clause and valuation :: Valuation
  assumes "clauseTrue clause valuation" and "clauseFalse clause valuation"
  shows "inconsistent valuation"
proof -
  from \<open>clauseTrue clause valuation\<close> obtain literal :: Literal 
    where "literal el clause" and "literalTrue literal valuation"
    by (auto simp add: clauseTrueIffContainsTrueLiteral)
  with \<open>clauseFalse clause valuation\<close> 
  have "literalFalse literal valuation" 
    by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
  from \<open>literalTrue literal valuation\<close> \<open>literalFalse literal valuation\<close> 
  show ?thesis 
    by (auto simp add: inconsistentCharacterization)
qed

lemma formulaTrueAndFormulaFalseImpliesInconsistent: 
  fixes formula :: Formula and valuation :: Valuation
  assumes "formulaTrue formula valuation" and "formulaFalse formula valuation"
  shows "inconsistent valuation"
proof -
  from \<open>formulaFalse formula valuation\<close> obtain clause :: Clause 
    where "clause el formula" and "clauseFalse clause valuation"
    by (auto simp add: formulaFalseIffContainsFalseClause)
  with \<open>formulaTrue formula valuation\<close> 
  have "clauseTrue clause valuation" 
    by (auto simp add: formulaTrueIffAllClausesAreTrue)
  from \<open>clauseTrue clause valuation\<close> \<open>clauseFalse clause valuation\<close> 
  show ?thesis 
    by (auto simp add: clauseTrueAndClauseFalseImpliesInconsistent)
qed

lemma inconsistentAppend:
  fixes valuation1 :: Valuation and valuation2 :: Valuation
  assumes "inconsistent (valuation1 @ valuation2)"
  shows "inconsistent valuation1 \<or> inconsistent valuation2 \<or> (\<exists> literal. literalTrue literal valuation1 \<and> literalFalse literal valuation2)"
using assms
proof (cases "inconsistent valuation1")
  case True
  thus ?thesis 
    by simp
next
  case False
  thus ?thesis
  proof (cases "inconsistent valuation2")
    case True
    thus ?thesis 
      by simp
  next
    case False
    from \<open>inconsistent (valuation1 @ valuation2)\<close> obtain literal :: Literal 
      where "literalTrue literal (valuation1 @ valuation2)" and "literalFalse literal (valuation1 @ valuation2)"
      by (auto simp add:inconsistentCharacterization)
    hence "(\<exists> literal. literalTrue literal valuation1 \<and> literalFalse literal valuation2)"
    proof (cases "literalTrue literal valuation1")
      case True
      with \<open>\<not> inconsistent valuation1\<close> 
      have "\<not> literalFalse literal valuation1" 
        by (auto simp add:inconsistentCharacterization)
      with \<open>literalFalse literal (valuation1 @ valuation2)\<close> 
      have "literalFalse literal valuation2" 
        by auto
      with True 
      show ?thesis 
        by auto
    next
      case False
      with \<open>literalTrue literal (valuation1 @ valuation2)\<close> 
      have "literalTrue literal valuation2"
        by auto
      with \<open>\<not> inconsistent valuation2\<close> 
      have "\<not> literalFalse literal valuation2"
        by (auto simp add:inconsistentCharacterization)
      with \<open>literalFalse literal (valuation1 @ valuation2)\<close> 
      have "literalFalse literal valuation1"
        by auto
      with \<open>literalTrue literal valuation2\<close>
      show ?thesis 
        by auto
    qed
    thus ?thesis 
      by simp
  qed
qed

lemma consistentAppendElement:
assumes "consistent v" and "\<not> literalFalse l v"
shows "consistent (v @ [l])"
proof-
  {
    assume "\<not> ?thesis"
    with \<open>consistent v\<close>
    have "(opposite l) el v"
      using inconsistentAppend[of "v" "[l]"]
      by auto
    with \<open>\<not> literalFalse l v\<close>
    have False
      by simp
  }
  thus ?thesis
    by auto
qed

lemma inconsistentRemoveAll:
  fixes literal :: Literal and valuation :: Valuation
  assumes "inconsistent (removeAll literal valuation)" 
  shows "inconsistent valuation"
using assms
proof -
  from \<open>inconsistent (removeAll literal valuation)\<close> obtain literal' :: Literal 
    where l'True: "literalTrue literal' (removeAll literal valuation)" and l'False: "literalFalse literal' (removeAll literal valuation)"
    by (auto simp add:inconsistentCharacterization)
  from l'True 
  have "literalTrue literal' valuation"
    by simp
  moreover
  from l'False 
  have "literalFalse literal' valuation"
    by simp
  ultimately
  show ?thesis 
    by (auto simp add:inconsistentCharacterization)
qed

lemma inconsistentPrefix: 
  assumes "isPrefix valuation1 valuation2" and "inconsistent valuation1"
  shows "inconsistent valuation2"
using assms
by (auto simp add:inconsistentCharacterization isPrefix_def)

lemma consistentPrefix:
  assumes "isPrefix valuation1 valuation2" and "consistent valuation2"
  shows "consistent valuation1"
using assms
by (auto simp add:inconsistentCharacterization isPrefix_def)


(*------------------------------------------------------------------*)
subsubsection\<open>Totality of valuations\<close>

text\<open>Checks if the valuation contains all the variables from the given set of variables\<close>
definition total where
[simp]: "total valuation variables == variables \<subseteq> vars valuation"

lemma totalSubset: 
  fixes A :: "Variable set" and B :: "Variable set" and valuation :: "Valuation"
  assumes "A \<subseteq> B" and "total valuation B"
  shows "total valuation A"
using assms
by auto

lemma totalFormulaImpliesTotalClause:
  fixes clause :: Clause and formula :: Formula and valuation :: Valuation
  assumes clauseEl: "clause el formula" and totalFormula: "total valuation (vars formula)"
  shows totalClause: "total valuation (vars clause)"
proof -
  from clauseEl 
  have "vars clause \<subseteq> vars formula" 
    using formulaContainsItsClausesVariables [of "clause" "formula"] 
    by simp
  with totalFormula 
  show ?thesis 
    by (simp add: totalSubset)
qed

lemma totalValuationForClauseDefinesAllItsLiterals:
  fixes clause :: Clause and valuation :: Valuation and literal :: Literal
  assumes 
  totalClause: "total valuation (vars clause)" and
  literalEl: "literal el clause"
  shows trueOrFalse: "literalTrue literal valuation \<or> literalFalse literal valuation"
proof -
  from literalEl 
  have "var literal \<in> vars clause"
    using clauseContainsItsLiteralsVariable 
    by auto
  with totalClause 
  have "var literal \<in> vars valuation" 
    by auto
  thus ?thesis 
    using  variableDefinedImpliesLiteralDefined [of "literal" "valuation"] 
    by simp
qed

lemma totalValuationForClauseDefinesItsValue:
  fixes clause :: Clause and valuation :: Valuation
  assumes totalClause: "total valuation (vars clause)"
  shows "clauseTrue clause valuation \<or> clauseFalse clause valuation"
proof (cases "clauseFalse clause valuation")
  case True
  thus ?thesis 
    by (rule disjI2)
next
  case False
  hence "\<not> (\<forall> l. l el clause \<longrightarrow> literalFalse l valuation)" 
    by (auto simp add:clauseFalseIffAllLiteralsAreFalse)
  then obtain l :: Literal 
    where "l el clause" and "\<not> literalFalse l valuation" 
    by auto
  with totalClause 
  have "literalTrue l valuation \<or> literalFalse l valuation"
    using totalValuationForClauseDefinesAllItsLiterals [of "valuation" "clause" "l"] 
    by auto
  with \<open>\<not> literalFalse l valuation\<close> 
  have "literalTrue l valuation" 
    by simp
  with \<open>l el clause\<close> 
  have "(clauseTrue clause valuation)" 
    by (auto simp add:clauseTrueIffContainsTrueLiteral)
  thus ?thesis 
    by (rule disjI1) 
qed

lemma totalValuationForFormulaDefinesAllItsLiterals: 
  fixes formula::Formula and valuation::Valuation
  assumes totalFormula: "total valuation (vars formula)" and
  literalElFormula: "literal el formula"
  shows "literalTrue literal valuation \<or> literalFalse literal valuation"
proof -
  from literalElFormula 
  have "var literal \<in> vars formula" 
    by (rule formulaContainsItsLiteralsVariable)
  with totalFormula 
  have "var literal \<in> vars valuation" 
    by auto
  thus ?thesis using variableDefinedImpliesLiteralDefined [of "literal" "valuation"] 
    by simp
qed

lemma totalValuationForFormulaDefinesAllItsClauses:
  fixes formula :: Formula and valuation :: Valuation and clause :: Clause
  assumes totalFormula: "total valuation (vars formula)" and 
  clauseElFormula: "clause el formula" 
  shows "clauseTrue clause valuation \<or> clauseFalse clause valuation"
proof -
  from clauseElFormula totalFormula 
  have "total valuation (vars clause)"
    by (rule totalFormulaImpliesTotalClause)
  thus ?thesis
    by (rule totalValuationForClauseDefinesItsValue)
qed

lemma totalValuationForFormulaDefinesItsValue:
  assumes totalFormula: "total valuation (vars formula)"
  shows "formulaTrue formula valuation \<or> formulaFalse formula valuation"
proof (cases "formulaTrue formula valuation")
  case True
  thus ?thesis
    by simp
next
  case False
  then obtain clause :: Clause 
    where clauseElFormula: "clause el formula" and notClauseTrue: "\<not> clauseTrue clause valuation" 
    by (auto simp add: formulaTrueIffAllClausesAreTrue)
  from clauseElFormula totalFormula
  have "total valuation (vars clause)"
    using totalFormulaImpliesTotalClause [of "clause" "formula" "valuation"]
    by simp
  with notClauseTrue 
  have "clauseFalse clause valuation" 
    using totalValuationForClauseDefinesItsValue [of "valuation" "clause"]
    by simp
  with clauseElFormula 
  show ?thesis 
    by (auto simp add:formulaFalseIffContainsFalseClause)
qed

lemma totalRemoveAllSingleLiteralClause:
  fixes literal :: Literal and valuation :: Valuation and formula :: Formula
  assumes varLiteral: "var literal \<in> vars valuation" and totalRemoveAll: "total valuation (vars (removeAll [literal] formula))"
  shows "total valuation (vars formula)"
proof -
  have "vars formula - vars [literal] \<subseteq> vars (removeAll [literal] formula)"
    by (rule varsRemoveAllClauseSuperset)
  with assms 
  show ?thesis 
    by auto
qed


(*------------------------------------------------------------------*)
subsubsection\<open>Models and satisfiability\<close>

text\<open>Model of a formula is a consistent valuation under which formula/clause is true\<close>
consts model :: "Valuation \<Rightarrow> 'a \<Rightarrow> bool"

overloading modelFormula \<equiv> "model :: Valuation \<Rightarrow> Formula \<Rightarrow> bool"
begin
  definition [simp]: "model valuation (formula::Formula) ==
    consistent valuation \<and> (formulaTrue formula valuation)"
end

overloading modelClause \<equiv> "model :: Valuation \<Rightarrow> Clause \<Rightarrow> bool"
begin
  definition [simp]: "model valuation (clause::Clause) ==
    consistent valuation \<and> (clauseTrue clause valuation)"
end

text\<open>Checks if a formula has a model\<close>
definition satisfiable :: "Formula \<Rightarrow> bool"
where
"satisfiable formula == \<exists> valuation. model valuation formula"

lemma formulaWithEmptyClauseIsUnsatisfiable:
  fixes formula :: Formula
  assumes "([]::Clause) el formula"
  shows "\<not> satisfiable formula"
using assms
by (auto simp add: satisfiable_def formulaTrueIffAllClausesAreTrue)

lemma satisfiableSubset: 
  fixes formula0 :: Formula and formula :: Formula
  assumes subset: "\<forall> (clause::Clause). clause el formula0 \<longrightarrow> clause el formula"
  shows  "satisfiable formula \<longrightarrow> satisfiable formula0"
proof
  assume "satisfiable formula"
  show "satisfiable formula0"
  proof -
    from \<open>satisfiable formula\<close> obtain valuation :: Valuation
      where "model valuation formula" 
      by (auto simp add: satisfiable_def)
    {
      fix clause :: Clause
      assume "clause el formula0"
      with subset 
      have "clause el formula" 
        by simp
      with \<open>model valuation formula\<close> 
      have "clauseTrue clause valuation" 
        by (simp add: formulaTrueIffAllClausesAreTrue)
    } hence "formulaTrue formula0 valuation" 
      by (simp add: formulaTrueIffAllClausesAreTrue)
    with \<open>model valuation formula\<close> 
    have "model valuation formula0" 
      by simp
    thus ?thesis 
      by (auto simp add: satisfiable_def)
  qed
qed

lemma satisfiableAppend: 
  fixes formula1 :: Formula and formula2 :: Formula
  assumes "satisfiable (formula1 @ formula2)" 
  shows "satisfiable formula1" "satisfiable formula2"
using assms
unfolding satisfiable_def
by (auto simp add:formulaTrueAppend)

lemma modelExpand: 
  fixes formula :: Formula and literal :: Literal and valuation :: Valuation
  assumes "model valuation formula" and "var literal \<notin> vars valuation"
  shows "model (valuation @ [literal]) formula"
proof -
  from \<open>model valuation formula\<close> 
  have "formulaTrue formula (valuation @ [literal])"
    by (simp add:formulaTrueAppendValuation)
  moreover
  from \<open>model valuation formula\<close> 
  have "consistent valuation" 
    by simp
  with \<open>var literal \<notin> vars valuation\<close> 
  have "consistent (valuation @ [literal])"
  proof (cases "inconsistent (valuation @ [literal])")
    case True
    hence "inconsistent valuation \<or> inconsistent [literal] \<or> (\<exists> l. literalTrue l valuation \<and> literalFalse l [literal])"
      by (rule inconsistentAppend)
    with \<open>consistent valuation\<close> 
    have "\<exists> l. literalTrue l valuation \<and> literalFalse l [literal]"
      by auto
    hence "literalFalse literal valuation" 
      by auto
    hence "var (opposite literal) \<in> (vars valuation)"
      using valuationContainsItsLiteralsVariable [of "opposite literal" "valuation"]
      by simp
    with \<open>var literal \<notin> vars valuation\<close> 
    have "False"
      by simp
    thus ?thesis ..
  qed simp
  ultimately 
  show ?thesis 
    by auto
qed



(*--------------------------------------------------------------------------------*)
subsubsection\<open>Tautological clauses\<close>

lemma tautologyNotFalse:
  fixes clause :: Clause and valuation :: Valuation
  assumes "clauseTautology clause" "consistent valuation"
  shows "\<not> clauseFalse clause valuation"
using assms
  clauseTautologyCharacterization[of "clause"]
  clauseFalseIffAllLiteralsAreFalse[of "clause" "valuation"]
  inconsistentCharacterization
by auto
  

lemma tautologyInTotalValuation:
assumes 
  "clauseTautology clause"
  "vars clause \<subseteq> vars valuation"
shows
  "clauseTrue clause valuation"
proof-
  from \<open>clauseTautology clause\<close>
  obtain literal
    where "literal el clause" "opposite literal el clause"
    by (auto simp add: clauseTautologyCharacterization)
  hence "var literal \<in> vars clause"
    using clauseContainsItsLiteralsVariable[of "literal" "clause"]
    using clauseContainsItsLiteralsVariable[of "opposite literal" "clause"]
    by simp
  hence "var literal \<in> vars valuation"
    using \<open>vars clause \<subseteq> vars valuation\<close>
    by auto
  hence "literalTrue literal valuation \<or> literalFalse literal valuation"
    using varInClauseVars[of "var literal" "valuation"]
    using varInClauseVars[of "var (opposite literal)" "valuation"]
    using literalsWithSameVariableAreEqualOrOpposite
    by auto
  thus ?thesis
    using \<open>literal el clause\<close> \<open>opposite literal el clause\<close>
    by (auto simp add: clauseTrueIffContainsTrueLiteral)
qed

lemma modelAppendTautology:
assumes
  "model valuation F" "clauseTautology c"
  "vars valuation \<supseteq> vars F \<union> vars c"
shows
  "model valuation (F @ [c])"
using assms
using tautologyInTotalValuation[of "c" "valuation"]
by (auto simp add: formulaTrueAppend)

lemma satisfiableAppendTautology:
assumes 
  "satisfiable F" "clauseTautology c"
shows
  "satisfiable (F @ [c])"
proof-
  from \<open>clauseTautology c\<close> 
  obtain l 
    where "l el c" "opposite l el c"
    by (auto simp add: clauseTautologyCharacterization)
  from \<open>satisfiable F\<close>
  obtain valuation
    where "consistent valuation" "formulaTrue F valuation"
    unfolding satisfiable_def
    by auto
  show ?thesis
  proof (cases "var l \<in> vars valuation")
    case True
    hence "literalTrue l valuation \<or> literalFalse l valuation"
      using varInClauseVars[of "var l" "valuation"]
      by (auto simp add: literalsWithSameVariableAreEqualOrOpposite)
    hence "clauseTrue c valuation"
      using \<open>l el c\<close> \<open>opposite l el c\<close>
      by (auto simp add: clauseTrueIffContainsTrueLiteral)
    thus ?thesis
      using \<open>consistent valuation\<close> \<open>formulaTrue F valuation\<close>
      unfolding satisfiable_def
      by (auto simp add: formulaTrueIffAllClausesAreTrue)
  next
    case False
    let ?valuation' = "valuation @ [l]"
    have "model ?valuation' F"
      using \<open>var l \<notin> vars valuation\<close>
      using \<open>formulaTrue F valuation\<close> \<open>consistent valuation\<close>
      using modelExpand[of "valuation" "F" "l"]
      by simp
    moreover
    have "formulaTrue [c] ?valuation'"
      using \<open>l el c\<close>
      using clauseTrueIffContainsTrueLiteral[of "c" "?valuation'"]
      using formulaTrueIffAllClausesAreTrue[of "[c]" "?valuation'"]
      by auto
    ultimately
    show ?thesis
      unfolding satisfiable_def
      by (auto simp add: formulaTrueAppend)
  qed
qed

lemma modelAppendTautologicalFormula:
fixes
  F :: Formula and F' :: Formula
assumes
  "model valuation F" "\<forall> c. c el F' \<longrightarrow> clauseTautology c"
  "vars valuation \<supseteq> vars F \<union> vars F'"
shows
  "model valuation (F @ F')"
using assms
proof (induct F')
  case Nil
  thus ?case
    by simp
next
  case (Cons c F'')
  hence "model valuation (F @ F'')"
    by simp
  hence "model valuation ((F @ F'') @ [c])"
    using Cons(3)
    using Cons(4)
    using modelAppendTautology[of "valuation" "F @ F''" "c"]
    using varsAppendFormulae[of "F" "F''"]
    by simp
  thus ?case
    by (simp add: formulaTrueAppend)
qed


lemma satisfiableAppendTautologicalFormula:
assumes 
  "satisfiable F" "\<forall> c. c el F' \<longrightarrow> clauseTautology c"
shows
  "satisfiable (F @ F')"
using assms
proof (induct F')
  case Nil
  thus ?case
    by simp
next
  case (Cons c F'')
  hence "satisfiable (F @ F'')"
    by simp
  thus ?case
    using Cons(3)
    using satisfiableAppendTautology[of "F @ F''" "c"]
    unfolding satisfiable_def
    by (simp add: formulaTrueIffAllClausesAreTrue)
qed

lemma satisfiableFilterTautologies:
shows "satisfiable F = satisfiable (filter (% c. \<not> clauseTautology c) F)"
proof (induct F)
  case Nil
  thus ?case
    by simp
next
  case (Cons c' F')
  let ?filt  = "\<lambda> F. filter (% c. \<not> clauseTautology c) F"
  let ?filt'  = "\<lambda> F. filter (% c. clauseTautology c) F"
  show ?case
  proof
    assume "satisfiable (c' # F')"
    thus "satisfiable (?filt (c' # F'))"
      unfolding satisfiable_def
      by (auto simp add: formulaTrueIffAllClausesAreTrue)
  next
    assume "satisfiable (?filt (c' # F'))"
    thus "satisfiable (c' # F')"
    proof (cases "clauseTautology c'")
      case True
      hence "?filt (c' # F') = ?filt F'"
        by auto
      hence "satisfiable (?filt F')"
        using \<open>satisfiable (?filt (c' # F'))\<close>
        by simp
      hence "satisfiable F'"
        using Cons
        by simp
      thus ?thesis
        using satisfiableAppendTautology[of "F'" "c'"]
        using \<open>clauseTautology c'\<close>
        unfolding satisfiable_def
        by (auto simp add: formulaTrueIffAllClausesAreTrue)
    next
      case False
      hence "?filt (c' # F') = c' # ?filt F'"
        by auto   
      hence "satisfiable (c' # ?filt F')"
        using \<open>satisfiable (?filt (c' # F'))\<close>
        by simp
      moreover
      have "\<forall> c. c el ?filt' F' \<longrightarrow> clauseTautology c"
        by simp
      ultimately
      have "satisfiable ((c' # ?filt F') @ ?filt' F')"
        using satisfiableAppendTautologicalFormula[of "c' # ?filt F'" "?filt' F'"]
        by (simp (no_asm_use))
      thus ?thesis
        unfolding satisfiable_def
        by (auto simp add: formulaTrueIffAllClausesAreTrue)
    qed
  qed
qed

lemma modelFilterTautologies:
assumes 
  "model valuation (filter (% c. \<not> clauseTautology c) F)" 
  "vars F \<subseteq> vars valuation"
shows "model valuation F"
using assms
proof (induct F)
  case Nil
  thus ?case
    by simp
next
  case (Cons c' F')
  let ?filt  = "\<lambda> F. filter (% c. \<not> clauseTautology c) F"
  let ?filt'  = "\<lambda> F. filter (% c. clauseTautology c) F"
  show ?case
  proof (cases "clauseTautology c'")
    case True
    thus ?thesis
      using Cons
      using tautologyInTotalValuation[of "c'" "valuation"]
      by auto
  next
    case False
    hence "?filt (c' # F') = c' # ?filt F'"
      by auto   
    hence "model valuation (c' # ?filt F')"
      using \<open>model valuation (?filt (c' # F'))\<close>
      by simp
    moreover
    have "\<forall> c. c el ?filt' F' \<longrightarrow> clauseTautology c"
      by simp
    moreover 
    have "vars ((c' # ?filt F') @ ?filt' F') \<subseteq> vars valuation"
      using varsSubsetFormula[of "?filt F'" "F'"]
      using varsSubsetFormula[of "?filt' F'" "F'"]
      using varsAppendFormulae[of "c' # ?filt F'" "?filt' F'"]
      using Cons(3)
      using formulaContainsItsClausesVariables[of _ "?filt F'"]
      by auto
    ultimately
    have "model valuation ((c' # ?filt F') @ ?filt' F')"
      using modelAppendTautologicalFormula[of "valuation" "c' # ?filt F'" "?filt' F'"]
      using varsAppendFormulae[of "c' # ?filt F'" "?filt' F'"]
      by (simp (no_asm_use)) (blast)
    thus ?thesis
      using formulaTrueAppend[of "?filt F'" "?filt' F'" "valuation"]
      using formulaTrueIffAllClausesAreTrue[of "?filt F'" "valuation"]
      using formulaTrueIffAllClausesAreTrue[of "?filt' F'" "valuation"]
      using formulaTrueIffAllClausesAreTrue[of "F'" "valuation"]      
      by auto
  qed
qed

(*------------------------------------------------------------------*)
subsubsection\<open>Entailment\<close>

text\<open>Formula entails literal if it is true in all its models\<close>
definition formulaEntailsLiteral :: "Formula \<Rightarrow> Literal \<Rightarrow> bool"
where
"formulaEntailsLiteral formula literal == 
  \<forall> (valuation::Valuation). model valuation formula \<longrightarrow> literalTrue literal valuation"

text\<open>Clause implies literal if it is true in all its models\<close>
definition clauseEntailsLiteral  :: "Clause \<Rightarrow> Literal \<Rightarrow> bool"
where
"clauseEntailsLiteral clause literal == 
  \<forall> (valuation::Valuation). model valuation clause \<longrightarrow> literalTrue literal valuation"

text\<open>Formula entails clause if it is true in all its models\<close>
definition formulaEntailsClause  :: "Formula \<Rightarrow> Clause \<Rightarrow> bool"
where
"formulaEntailsClause formula clause == 
  \<forall> (valuation::Valuation). model valuation formula \<longrightarrow> model valuation clause"

text\<open>Formula entails valuation if it entails its every literal\<close>
definition formulaEntailsValuation :: "Formula \<Rightarrow> Valuation \<Rightarrow> bool"
where
"formulaEntailsValuation formula valuation ==
    \<forall> literal. literal el valuation \<longrightarrow> formulaEntailsLiteral formula literal"

text\<open>Formula entails formula if it is true in all its models\<close>
definition formulaEntailsFormula  :: "Formula \<Rightarrow> Formula \<Rightarrow> bool"
where
formulaEntailsFormula_def: "formulaEntailsFormula formula formula' == 
  \<forall> (valuation::Valuation). model valuation formula \<longrightarrow> model valuation formula'"

lemma singleLiteralClausesEntailItsLiteral: 
  fixes clause :: Clause and literal :: Literal
  assumes "length clause = 1" and "literal el clause"
  shows "clauseEntailsLiteral clause literal"
proof -
  from assms 
  have onlyLiteral: "\<forall> l. l el clause \<longrightarrow> l = literal" 
    using lengthOneImpliesOnlyElement[of "clause" "literal"]
    by simp
  {
    fix valuation :: Valuation
    assume "clauseTrue clause valuation"
    with onlyLiteral  
    have "literalTrue literal valuation" 
      by (auto simp add:clauseTrueIffContainsTrueLiteral)
  }
  thus ?thesis 
    by (simp add:clauseEntailsLiteral_def)
qed

lemma clauseEntailsLiteralThenFormulaEntailsLiteral:
  fixes clause :: Clause and formula :: Formula and literal :: Literal
  assumes "clause el formula" and "clauseEntailsLiteral clause literal"
  shows "formulaEntailsLiteral formula literal"
proof -
  {
    fix valuation :: Valuation
    assume modelFormula: "model valuation formula"

    with \<open>clause el formula\<close> 
    have "clauseTrue clause valuation"
      by (simp add:formulaTrueIffAllClausesAreTrue)
    with modelFormula \<open>clauseEntailsLiteral clause literal\<close> 
    have "literalTrue literal valuation"
      by (auto simp add: clauseEntailsLiteral_def)
  }
  thus ?thesis 
    by (simp add:formulaEntailsLiteral_def)
qed

lemma formulaEntailsLiteralAppend: 
  fixes formula :: Formula and formula' :: Formula and literal :: Literal
  assumes "formulaEntailsLiteral formula literal"
  shows  "formulaEntailsLiteral (formula @ formula') literal"
proof -
  {
    fix valuation :: Valuation
    assume modelFF': "model valuation (formula @ formula')"

    hence "formulaTrue formula valuation" 
      by (simp add: formulaTrueAppend)
    with modelFF' and \<open>formulaEntailsLiteral formula literal\<close> 
    have "literalTrue literal valuation" 
      by (simp add: formulaEntailsLiteral_def)
  }
  thus ?thesis 
    by (simp add: formulaEntailsLiteral_def)
qed

lemma formulaEntailsLiteralSubset: 
  fixes formula :: Formula and formula' :: Formula and literal :: Literal
  assumes "formulaEntailsLiteral formula literal" and "\<forall> (c::Clause) . c el formula \<longrightarrow> c el formula'"
  shows "formulaEntailsLiteral formula' literal"
proof -
  {
    fix valuation :: Valuation
    assume modelF': "model valuation formula'"
    with \<open>\<forall> (c::Clause) . c el formula \<longrightarrow> c el formula'\<close> 
    have "formulaTrue formula valuation"
      by (auto simp add: formulaTrueIffAllClausesAreTrue)
    with modelF' \<open>formulaEntailsLiteral formula literal\<close> 
    have "literalTrue literal valuation"
      by (simp add: formulaEntailsLiteral_def)
  }
  thus ?thesis 
    by (simp add:formulaEntailsLiteral_def)
qed


lemma formulaEntailsLiteralRemoveAll:
  fixes formula :: Formula and clause :: Clause and literal :: Literal
  assumes "formulaEntailsLiteral (removeAll clause formula) literal"
  shows "formulaEntailsLiteral formula literal"
proof -
  {
    fix valuation :: Valuation
    assume modelF: "model valuation formula"
    hence "formulaTrue (removeAll clause formula) valuation" 
      by (auto simp add:formulaTrueRemoveAll)
    with modelF \<open>formulaEntailsLiteral (removeAll clause formula) literal\<close> 
    have "literalTrue literal valuation"
      by (auto simp add:formulaEntailsLiteral_def)
  }
  thus ?thesis 
    by (simp add:formulaEntailsLiteral_def)
qed

lemma formulaEntailsLiteralRemoveAllAppend:
  fixes formula1 :: Formula and formula2 :: Formula and clause :: Clause and valuation :: Valuation
  assumes "formulaEntailsLiteral ((removeAll clause formula1) @ formula2) literal" 
  shows "formulaEntailsLiteral (formula1 @ formula2) literal"
proof -
  {
    fix valuation :: Valuation
    assume modelF: "model valuation (formula1 @ formula2)"
    hence "formulaTrue ((removeAll clause formula1) @ formula2) valuation" 
      by (auto simp add:formulaTrueRemoveAll formulaTrueAppend)
    with modelF \<open>formulaEntailsLiteral ((removeAll clause formula1) @ formula2) literal\<close> 
    have "literalTrue literal valuation"
      by (auto simp add:formulaEntailsLiteral_def)
  }
  thus ?thesis 
    by (simp add:formulaEntailsLiteral_def)
qed

lemma formulaEntailsItsClauses: 
  fixes clause :: Clause and formula :: Formula
  assumes "clause el formula"
  shows "formulaEntailsClause formula clause"
using assms
by (simp add: formulaEntailsClause_def formulaTrueIffAllClausesAreTrue)

lemma formulaEntailsClauseAppend: 
  fixes clause :: Clause and formula :: Formula and formula' :: Formula
  assumes "formulaEntailsClause formula clause"
  shows "formulaEntailsClause (formula @ formula') clause"
proof -
  { 
    fix valuation :: Valuation
    assume "model valuation (formula @ formula')"
    hence "model valuation formula"
      by (simp add:formulaTrueAppend)
    with \<open>formulaEntailsClause formula clause\<close> 
    have "clauseTrue clause valuation"
      by (simp add:formulaEntailsClause_def)
  }
  thus ?thesis 
    by (simp add: formulaEntailsClause_def)
qed

lemma formulaUnsatIffImpliesEmptyClause: 
  fixes formula :: Formula
  shows "formulaEntailsClause formula [] = (\<not> satisfiable formula)"
by (auto simp add: formulaEntailsClause_def satisfiable_def)

lemma formulaTrueExtendWithEntailedClauses:
  fixes formula :: Formula and formula0 :: Formula and valuation :: Valuation
  assumes formulaEntailed: "\<forall> (clause::Clause). clause el formula \<longrightarrow> formulaEntailsClause formula0 clause" and "consistent valuation"
  shows "formulaTrue formula0 valuation \<longrightarrow> formulaTrue formula valuation"
proof
  assume "formulaTrue formula0 valuation"
  {
    fix clause :: Clause
    assume "clause el formula"
    with formulaEntailed 
    have "formulaEntailsClause formula0 clause"
      by simp
    with \<open>formulaTrue formula0 valuation\<close> \<open>consistent valuation\<close> 
    have "clauseTrue clause valuation"
      by (simp add:formulaEntailsClause_def)
  }
  thus "formulaTrue formula valuation"
    by (simp add:formulaTrueIffAllClausesAreTrue)
qed


lemma formulaEntailsFormulaIffEntailsAllItsClauses: 
  fixes formula :: Formula and formula' :: Formula
  shows "formulaEntailsFormula formula formula' = (\<forall> clause::Clause. clause el formula' \<longrightarrow> formulaEntailsClause formula clause)"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  show ?rhs
  proof
    fix clause :: Clause
    show "clause el formula' \<longrightarrow> formulaEntailsClause formula clause"
    proof
      assume "clause el formula'"
      show "formulaEntailsClause formula clause"
      proof -
        {
          fix valuation :: Valuation
          assume "model valuation formula"
          with \<open>?lhs\<close> 
          have "model valuation formula'"
            by (simp add:formulaEntailsFormula_def)
          with \<open>clause el formula'\<close> 
          have "clauseTrue clause valuation"
            by (simp add:formulaTrueIffAllClausesAreTrue)
        }
        thus ?thesis 
          by (simp add:formulaEntailsClause_def)
      qed
    qed
  qed
next
  assume ?rhs
  thus ?lhs
  proof -
    {
      fix valuation :: Valuation
      assume "model valuation formula"
      {
        fix clause :: Clause
        assume "clause el formula'"
        with \<open>?rhs\<close> 
        have "formulaEntailsClause formula clause"
          by auto
        with \<open>model valuation formula\<close> 
        have "clauseTrue clause valuation"
          by (simp add:formulaEntailsClause_def)
      }
      hence "(formulaTrue formula' valuation)"
        by (simp add:formulaTrueIffAllClausesAreTrue)
    }
    thus ?thesis
      by (simp add:formulaEntailsFormula_def)
  qed
qed

lemma formulaEntailsFormulaThatEntailsClause: 
  fixes formula1 :: Formula and formula2 :: Formula and clause :: Clause
  assumes "formulaEntailsFormula formula1 formula2" and "formulaEntailsClause formula2 clause"
  shows "formulaEntailsClause formula1 clause"
using assms
by (simp add: formulaEntailsClause_def formulaEntailsFormula_def)


lemma 
  fixes formula1 :: Formula and formula2 :: Formula and formula1' :: Formula and literal :: Literal
  assumes "formulaEntailsLiteral (formula1 @ formula2) literal" and "formulaEntailsFormula formula1' formula1"
  shows "formulaEntailsLiteral (formula1' @ formula2) literal"
proof -
  {
    fix valuation :: Valuation
    assume "model valuation (formula1' @ formula2)"
    hence "consistent valuation" and "formulaTrue formula1' valuation"  "formulaTrue formula2 valuation"
      by (auto simp add: formulaTrueAppend)
    with \<open>formulaEntailsFormula formula1' formula1\<close> 
    have "model valuation formula1"
      by (simp add:formulaEntailsFormula_def)
    with \<open>formulaTrue formula2 valuation\<close> 
    have "model valuation (formula1 @ formula2)"
      by (simp add: formulaTrueAppend)
    with \<open>formulaEntailsLiteral (formula1 @ formula2) literal\<close> 
    have "literalTrue literal valuation"
      by (simp add:formulaEntailsLiteral_def)
  }
  thus ?thesis
    by (simp add:formulaEntailsLiteral_def)
qed


lemma formulaFalseInEntailedValuationIsUnsatisfiable: 
  fixes formula :: Formula and valuation :: Valuation
  assumes "formulaFalse formula valuation" and 
          "formulaEntailsValuation formula valuation"
  shows "\<not> satisfiable formula"
proof -
  from \<open>formulaFalse formula valuation\<close> obtain clause :: Clause
    where "clause el formula" and "clauseFalse clause valuation"
    by (auto simp add:formulaFalseIffContainsFalseClause)
  {
    fix valuation' :: Valuation
    assume modelV': "model valuation' formula"
    with \<open>clause el formula\<close> obtain literal :: Literal 
      where "literal el clause" and "literalTrue literal valuation'"
      by (auto simp add: formulaTrueIffAllClausesAreTrue clauseTrueIffContainsTrueLiteral)
    with \<open>clauseFalse clause valuation\<close> 
    have "literalFalse literal valuation"
      by (auto simp add:clauseFalseIffAllLiteralsAreFalse)
    with \<open>formulaEntailsValuation formula valuation\<close> 
    have "formulaEntailsLiteral formula (opposite literal)"
      unfolding formulaEntailsValuation_def
      by simp
    with modelV' 
    have "literalFalse literal valuation'"
      by (auto simp add:formulaEntailsLiteral_def)
    from \<open>literalTrue literal valuation'\<close> \<open>literalFalse literal valuation'\<close> modelV' 
    have "False"
      by (simp add:inconsistentCharacterization)
  }
  thus ?thesis
    by (auto simp add:satisfiable_def)
qed

lemma formulaFalseInEntailedOrPureValuationIsUnsatisfiable: 
  fixes formula :: Formula and valuation :: Valuation
  assumes "formulaFalse formula valuation" and 
  "\<forall> literal'. literal' el valuation \<longrightarrow> formulaEntailsLiteral formula literal' \<or>  \<not> opposite literal' el formula"
  shows "\<not> satisfiable formula"
proof -
  from \<open>formulaFalse formula valuation\<close> obtain clause :: Clause
    where "clause el formula" and "clauseFalse clause valuation"
    by (auto simp add:formulaFalseIffContainsFalseClause)
  {
    fix valuation' :: Valuation
    assume modelV': "model valuation' formula"
    with \<open>clause el formula\<close> obtain literal :: Literal 
      where "literal el clause" and "literalTrue literal valuation'"
      by (auto simp add: formulaTrueIffAllClausesAreTrue clauseTrueIffContainsTrueLiteral)
    with \<open>clauseFalse clause valuation\<close> 
    have "literalFalse literal valuation"
      by (auto simp add:clauseFalseIffAllLiteralsAreFalse)
    with \<open>\<forall> literal'. literal' el valuation \<longrightarrow> formulaEntailsLiteral formula literal' \<or>  \<not> opposite literal' el formula\<close> 
    have "formulaEntailsLiteral formula (opposite literal) \<or> \<not> literal el formula"
      by auto
    moreover
    {
      assume "formulaEntailsLiteral formula (opposite literal)"
      with modelV' 
      have "literalFalse literal valuation'"
        by (auto simp add:formulaEntailsLiteral_def)
      from \<open>literalTrue literal valuation'\<close> \<open>literalFalse literal valuation'\<close> modelV' 
      have "False"
        by (simp add:inconsistentCharacterization)
    }
    moreover
    {
      assume "\<not> literal el formula"
      with \<open>clause el formula\<close> \<open>literal el clause\<close>
      have "False"
        by (simp add:literalElFormulaCharacterization)
    }
    ultimately
    have "False"
      by auto
  }
  thus ?thesis
    by (auto simp add:satisfiable_def)
qed


lemma unsatisfiableFormulaWithSingleLiteralClause:
  fixes formula :: Formula and literal :: Literal
  assumes "\<not> satisfiable formula" and "[literal] el formula"
  shows "formulaEntailsLiteral (removeAll [literal] formula) (opposite literal)"
proof -
  {
    fix valuation :: Valuation
    assume "model valuation (removeAll [literal] formula)"
    hence "literalFalse literal valuation"
    proof (cases "var literal \<in> vars valuation")
      case True
      {
        assume "literalTrue literal valuation"
        with \<open>model valuation (removeAll [literal] formula)\<close> 
        have "model valuation formula"
          by (auto simp add:formulaTrueIffAllClausesAreTrue)
        with \<open>\<not> satisfiable formula\<close> 
        have "False"
          by (auto simp add:satisfiable_def)
      }
      with True 
      show ?thesis 
        using variableDefinedImpliesLiteralDefined [of "literal" "valuation"]
        by auto
    next
      case False
      with \<open>model valuation (removeAll [literal] formula)\<close> 
      have "model (valuation @ [literal]) (removeAll [literal] formula)"
        by (rule modelExpand)
      hence 
        "formulaTrue (removeAll [literal] formula) (valuation @ [literal])" and "consistent (valuation @ [literal])"
        by auto
      from \<open>formulaTrue (removeAll [literal] formula) (valuation @ [literal])\<close> 
      have "formulaTrue formula (valuation @ [literal])"
        by (rule trueFormulaWithSingleLiteralClause)
      with \<open>consistent (valuation @ [literal])\<close> 
      have "model (valuation @ [literal]) formula"
        by simp
      with \<open>\<not> satisfiable formula\<close> 
      have "False"
        by (auto simp add:satisfiable_def)
      thus ?thesis ..
    qed
  }
  thus ?thesis 
    by (simp add:formulaEntailsLiteral_def)
qed

lemma unsatisfiableFormulaWithSingleLiteralClauses:
  fixes F::Formula and c::Clause
  assumes "\<not> satisfiable (F @ val2form (oppositeLiteralList c))" "\<not> clauseTautology c"
  shows "formulaEntailsClause F c"
proof-
  {
    fix v::Valuation
    assume "model v F"
    with \<open>\<not> satisfiable (F @ val2form (oppositeLiteralList c))\<close>
    have "\<not> formulaTrue (val2form (oppositeLiteralList c)) v"
      unfolding satisfiable_def
      by (auto simp add: formulaTrueAppend)
    have "clauseTrue c v"
    proof (cases "\<exists> l. l el c \<and> (literalTrue l v)")
      case True
      thus ?thesis
        using clauseTrueIffContainsTrueLiteral
        by simp
    next
      case False
      let ?v' = "v @ (oppositeLiteralList c)"

      have "\<not> inconsistent (oppositeLiteralList c)"
      proof-
        {
          assume "\<not> ?thesis"
          then obtain l::Literal
            where "l el (oppositeLiteralList c)" "opposite l el (oppositeLiteralList c)"
            using inconsistentCharacterization [of "oppositeLiteralList c"]
            by auto
          hence "(opposite l) el c" "l el c"
            using literalElListIffOppositeLiteralElOppositeLiteralList[of "l" "c"]
            using literalElListIffOppositeLiteralElOppositeLiteralList[of "opposite l" "c"]
            by auto
          hence "clauseTautology c"
            using clauseTautologyCharacterization[of "c"]
            by auto
          with \<open>\<not> clauseTautology c\<close>
          have "False"
            by simp
        }
        thus ?thesis
          by auto
      qed
      with False \<open>model v F\<close>
      have "consistent ?v'"
        using inconsistentAppend[of "v" "oppositeLiteralList c"]
        unfolding consistent_def
        using literalElListIffOppositeLiteralElOppositeLiteralList
        by auto
      moreover
      from \<open>model v F\<close>
      have "formulaTrue F ?v'"
        using formulaTrueAppendValuation
        by simp
      moreover
      have "formulaTrue (val2form (oppositeLiteralList c)) ?v'"
        using val2formFormulaTrue[of "oppositeLiteralList c" "v @ oppositeLiteralList c"]
        by simp
      ultimately
      have "model ?v' (F @ val2form (oppositeLiteralList c))"
        by (simp add: formulaTrueAppend)
      with \<open>\<not> satisfiable (F @ val2form (oppositeLiteralList c))\<close>
      have "False"
        unfolding satisfiable_def
        by auto
      thus ?thesis
        by simp
    qed
  }
  thus ?thesis
    unfolding formulaEntailsClause_def
    by simp
qed

lemma satisfiableEntailedFormula:
  fixes formula0 :: Formula and formula :: Formula
  assumes "formulaEntailsFormula formula0 formula"
  shows "satisfiable formula0 \<longrightarrow> satisfiable formula"
proof
  assume "satisfiable formula0"
  show "satisfiable formula"
  proof -
    from \<open>satisfiable formula0\<close> obtain valuation :: Valuation
      where "model valuation formula0" 
      by (auto simp add: satisfiable_def)
    with \<open>formulaEntailsFormula formula0 formula\<close> 
    have "model valuation formula" 
      by (simp add: formulaEntailsFormula_def)
    thus ?thesis 
      by (auto simp add: satisfiable_def)
  qed
qed

lemma val2formIsEntailed:
shows "formulaEntailsValuation (F' @ val2form valuation @ F'') valuation"
proof-
  {
    fix l::Literal
    assume "l el valuation"
    hence "[l] el val2form valuation"
      by (induct valuation) (auto)

    have "formulaEntailsLiteral (F' @ val2form valuation @ F'') l"
    proof-
      {
        fix valuation'::Valuation
        assume "formulaTrue (F' @ val2form valuation @ F'') valuation'"
        hence "literalTrue l valuation'"
          using \<open>[l] el val2form valuation\<close>
          using formulaTrueIffAllClausesAreTrue[of "F' @ val2form valuation @ F''" "valuation'"]
          by (auto simp add: clauseTrueIffContainsTrueLiteral)
      } thus ?thesis
        unfolding formulaEntailsLiteral_def
        by simp
    qed
  }
  thus ?thesis
    unfolding formulaEntailsValuation_def
    by simp
qed


(*------------------------------------------------------------------*)
subsubsection\<open>Equivalency\<close>

text\<open>Formulas are equivalent if they have same models.\<close>
definition equivalentFormulae :: "Formula \<Rightarrow> Formula \<Rightarrow> bool"
where
"equivalentFormulae formula1 formula2 ==
  \<forall> (valuation::Valuation). model valuation formula1 = model valuation formula2"

lemma equivalentFormulaeIffEntailEachOther:
  fixes formula1 :: Formula and formula2 :: Formula
  shows "equivalentFormulae formula1 formula2 = (formulaEntailsFormula formula1 formula2 \<and> formulaEntailsFormula formula2 formula1)"
by (auto simp add:formulaEntailsFormula_def equivalentFormulae_def)

lemma equivalentFormulaeReflexivity: 
  fixes formula :: Formula
  shows "equivalentFormulae formula formula"
unfolding equivalentFormulae_def
by auto

lemma equivalentFormulaeSymmetry: 
  fixes formula1 :: Formula and formula2 :: Formula
  shows "equivalentFormulae formula1 formula2 = equivalentFormulae formula2 formula1"
unfolding equivalentFormulae_def
by auto

lemma equivalentFormulaeTransitivity: 
  fixes formula1 :: Formula and formula2 :: Formula and formula3 :: Formula
  assumes "equivalentFormulae formula1 formula2" and "equivalentFormulae formula2 formula3"
  shows "equivalentFormulae formula1 formula3"
using assms
unfolding equivalentFormulae_def
by auto

lemma equivalentFormulaeAppend: 
  fixes formula1 :: Formula and formula1' :: Formula and formula2 :: Formula
  assumes "equivalentFormulae formula1 formula1'"
  shows "equivalentFormulae (formula1 @ formula2) (formula1' @ formula2)"
using assms
unfolding equivalentFormulae_def
by (auto simp add: formulaTrueAppend)

lemma satisfiableEquivalent: 
  fixes formula1 :: Formula and formula2 :: Formula
  assumes "equivalentFormulae formula1 formula2"
  shows "satisfiable formula1 = satisfiable formula2"
using assms
unfolding equivalentFormulae_def
unfolding satisfiable_def
by auto

lemma satisfiableEquivalentAppend: 
  fixes formula1 :: Formula and formula1' :: Formula and formula2 :: Formula
  assumes "equivalentFormulae formula1 formula1'" and "satisfiable (formula1 @ formula2)"
  shows "satisfiable (formula1' @ formula2)"
using assms
proof -
  from \<open>satisfiable (formula1 @ formula2)\<close> obtain valuation::Valuation
    where "consistent valuation" "formulaTrue formula1 valuation" "formulaTrue formula2 valuation"
    unfolding satisfiable_def
    by (auto simp add: formulaTrueAppend)
  from \<open>equivalentFormulae formula1 formula1'\<close> \<open>consistent valuation\<close> \<open>formulaTrue formula1 valuation\<close> 
  have "formulaTrue formula1' valuation"
    unfolding equivalentFormulae_def
    by auto
  show ?thesis
    using \<open>consistent valuation\<close> \<open>formulaTrue formula1' valuation\<close> \<open>formulaTrue formula2 valuation\<close>
    unfolding satisfiable_def
    by (auto simp add: formulaTrueAppend)
qed


lemma replaceEquivalentByEquivalent:
  fixes formula :: Formula and formula' :: Formula and formula1 :: Formula and formula2 :: Formula
  assumes "equivalentFormulae formula formula'" 
  shows "equivalentFormulae (formula1 @ formula @ formula2) (formula1 @ formula' @ formula2)"
unfolding equivalentFormulae_def
proof
  fix v :: Valuation
  show "model v (formula1 @ formula @ formula2) = model v (formula1 @ formula' @ formula2)"
  proof
    assume "model v (formula1 @ formula @ formula2)"
    hence *: "consistent v" "formulaTrue formula1 v" "formulaTrue formula v" "formulaTrue formula2 v"
      by (auto simp add: formulaTrueAppend)
    from \<open>consistent v\<close> \<open>formulaTrue formula v\<close> \<open>equivalentFormulae formula formula'\<close>
    have "formulaTrue formula' v"
      unfolding equivalentFormulae_def
      by auto
    thus "model v (formula1 @ formula' @ formula2)"
      using *
      by (simp add: formulaTrueAppend)
  next
    assume "model v (formula1 @ formula' @ formula2)"
    hence *: "consistent v" "formulaTrue formula1 v" "formulaTrue formula' v" "formulaTrue formula2 v"
      by (auto simp add: formulaTrueAppend)
    from \<open>consistent v\<close> \<open>formulaTrue formula' v\<close> \<open>equivalentFormulae formula formula'\<close>
    have "formulaTrue formula v"
      unfolding equivalentFormulae_def
      by auto
    thus "model v (formula1 @ formula @ formula2)"
      using *
      by (simp add: formulaTrueAppend)
  qed
qed

lemma clauseOrderIrrelevant:
  shows "equivalentFormulae (F1 @ F @ F' @ F2) (F1 @ F' @ F @ F2)"
unfolding equivalentFormulae_def
by (auto simp add: formulaTrueIffAllClausesAreTrue)

lemma extendEquivalentFormulaWithEntailedClause:
  fixes formula1 :: Formula and formula2 :: Formula and clause :: Clause
  assumes "equivalentFormulae formula1 formula2" and "formulaEntailsClause formula2 clause"
  shows "equivalentFormulae formula1 (formula2 @ [clause])"
  unfolding equivalentFormulae_def
proof
  fix valuation :: Valuation
  show "model valuation formula1 = model valuation (formula2 @ [clause])"
  proof
    assume "model valuation formula1"
    hence "consistent valuation"
      by simp
    from \<open>model valuation formula1\<close> \<open>equivalentFormulae formula1 formula2\<close>
    have "model valuation formula2"
      unfolding equivalentFormulae_def
      by simp
    moreover
    from \<open>model valuation formula2\<close> \<open>formulaEntailsClause formula2 clause\<close>
    have "clauseTrue clause valuation"
      unfolding formulaEntailsClause_def
      by simp
    ultimately show
      "model valuation (formula2 @ [clause])"
      by (simp add: formulaTrueAppend)
  next
    assume "model valuation (formula2 @ [clause])"
    hence "consistent valuation"
      by simp
    from \<open>model valuation (formula2 @ [clause])\<close>
    have "model valuation formula2"
      by (simp add:formulaTrueAppend)
    with \<open>equivalentFormulae formula1 formula2\<close>
    show "model valuation formula1"
      unfolding equivalentFormulae_def
      by auto
  qed
qed

lemma entailsLiteralRelpacePartWithEquivalent:
  assumes "equivalentFormulae F F'" and "formulaEntailsLiteral (F1 @ F @ F2) l"
  shows "formulaEntailsLiteral (F1 @ F' @ F2) l"
proof-
  {
    fix v::Valuation
    assume "model v (F1 @ F' @ F2)"
    hence "consistent v" and "formulaTrue F1 v" and "formulaTrue F' v" and "formulaTrue F2 v"
      by (auto simp add:formulaTrueAppend)
    with \<open>equivalentFormulae F F'\<close>
    have "formulaTrue F v"
      unfolding equivalentFormulae_def
      by auto
    with \<open>consistent v\<close> \<open>formulaTrue F1 v\<close> \<open>formulaTrue F2 v\<close>
    have "model v (F1 @ F @ F2)"
      by (auto simp add:formulaTrueAppend)
    with \<open>formulaEntailsLiteral (F1 @ F @ F2) l\<close>
    have "literalTrue l v"
      unfolding formulaEntailsLiteral_def
      by auto
  }
  thus ?thesis
    unfolding formulaEntailsLiteral_def
    by auto
qed



(*--------------------------------------------------------------------------------*)
subsubsection\<open>Remove false and duplicate literals of a clause\<close>

definition
removeFalseLiterals :: "Clause \<Rightarrow> Valuation \<Rightarrow> Clause"
where
"removeFalseLiterals clause valuation = filter (\<lambda> l. \<not> literalFalse l valuation) clause"

lemma clauseTrueRemoveFalseLiterals:
  assumes "consistent v"
  shows "clauseTrue c v = clauseTrue (removeFalseLiterals c v) v"
using assms
unfolding removeFalseLiterals_def
by (auto simp add: clauseTrueIffContainsTrueLiteral inconsistentCharacterization)

lemma clauseTrueRemoveDuplicateLiterals:
  shows "clauseTrue c v = clauseTrue (remdups c) v"
by (induct c) (auto simp add: clauseTrueIffContainsTrueLiteral)

lemma removeDuplicateLiteralsEquivalentClause:
  shows "equivalentFormulae [remdups clause] [clause]"
unfolding equivalentFormulae_def
by (auto simp add: formulaTrueIffAllClausesAreTrue clauseTrueIffContainsTrueLiteral)

lemma falseLiteralsCanBeRemoved:
(* val2form v - some single literal clauses *)
fixes F::Formula and F'::Formula and v::Valuation
assumes "equivalentFormulae (F1 @ val2form v @ F2) F'"
shows "equivalentFormulae (F1 @ val2form v @ [removeFalseLiterals c v] @ F2) (F' @ [c])" 
            (is "equivalentFormulae ?lhs ?rhs")
unfolding equivalentFormulae_def
proof
  fix v' :: Valuation
  show "model v' ?lhs = model v' ?rhs"
  proof
    assume "model v' ?lhs"
    hence "consistent v'" and  
      "formulaTrue (F1 @ val2form v @ F2) v'" and 
      "clauseTrue (removeFalseLiterals c v) v'"
      by (auto simp add: formulaTrueAppend formulaTrueIffAllClausesAreTrue)

    from \<open>consistent v'\<close> \<open>formulaTrue (F1 @ val2form v @ F2) v'\<close> \<open>equivalentFormulae (F1 @ val2form v @ F2) F'\<close>
    have "model v' F'"
      unfolding equivalentFormulae_def
      by auto
    moreover
    from \<open>clauseTrue (removeFalseLiterals c v) v'\<close>
    have "clauseTrue c v'"
      unfolding removeFalseLiterals_def
      by (auto simp add: clauseTrueIffContainsTrueLiteral)
    ultimately
    show "model v' ?rhs"
      by (simp add: formulaTrueAppend)
  next
    assume "model v' ?rhs"
    hence "consistent v'" and "formulaTrue F' v'" and "clauseTrue c v'"
      by (auto simp add: formulaTrueAppend formulaTrueIffAllClausesAreTrue)

    from \<open>consistent v'\<close> \<open>formulaTrue F' v'\<close> \<open>equivalentFormulae (F1 @ val2form v @ F2) F'\<close>
    have "model v' (F1 @ val2form v @ F2)"
      unfolding equivalentFormulae_def
      by auto
    moreover
    have "clauseTrue (removeFalseLiterals c v) v'"
    proof-
      from \<open>clauseTrue c v'\<close> 
      obtain l :: Literal
        where "l el c" and "literalTrue l v'"
        by (auto simp add: clauseTrueIffContainsTrueLiteral)
      have "\<not> literalFalse l v"
      proof-
        {
          assume "\<not> ?thesis"
          hence "opposite l el v"
            by simp
          with \<open>model v' (F1 @ val2form v @ F2)\<close>
          have "opposite l el v'"
            using val2formFormulaTrue[of "v" "v'"]
            by auto (simp add: formulaTrueAppend)
          with \<open>literalTrue l v'\<close> \<open>consistent v'\<close>
          have "False"
            by (simp add: inconsistentCharacterization)
        }
        thus ?thesis
          by auto
      qed
      with \<open>l el c\<close>
      have  "l el (removeFalseLiterals c v)"
        unfolding removeFalseLiterals_def
        by simp
      with \<open>literalTrue l v'\<close>
      show ?thesis
        by (auto simp add: clauseTrueIffContainsTrueLiteral)
    qed
    ultimately
    show "model v' ?lhs"
      by (simp add: formulaTrueAppend)
  qed
qed

lemma falseAndDuplicateLiteralsCanBeRemoved:
(* val2form v - some single literal clauses *)
assumes "equivalentFormulae (F1 @ val2form v @ F2) F'"
shows "equivalentFormulae (F1 @ val2form v @ [remdups (removeFalseLiterals c v)] @ F2) (F' @ [c])" 
  (is "equivalentFormulae ?lhs ?rhs")
proof-
  from \<open>equivalentFormulae (F1 @ val2form v @ F2) F'\<close> 
  have "equivalentFormulae (F1 @ val2form v @ [removeFalseLiterals c v] @ F2) (F' @ [c])"
    using falseLiteralsCanBeRemoved
    by simp
  have "equivalentFormulae [remdups (removeFalseLiterals c v)] [removeFalseLiterals c v]"
    using removeDuplicateLiteralsEquivalentClause
    by simp
  hence "equivalentFormulae (F1 @ val2form v @ [remdups (removeFalseLiterals c v)] @ F2)
    (F1 @ val2form v @ [removeFalseLiterals c v] @ F2)"
    using replaceEquivalentByEquivalent
    [of "[remdups (removeFalseLiterals c v)]" "[removeFalseLiterals c v]" "F1 @ val2form v" "F2"]
    by auto
  thus ?thesis
    using \<open>equivalentFormulae (F1 @ val2form v @ [removeFalseLiterals c v] @ F2) (F' @ [c])\<close>
    using equivalentFormulaeTransitivity[of 
              "(F1 @ val2form v @ [remdups (removeFalseLiterals c v)] @ F2)"
              "(F1 @ val2form v @ [removeFalseLiterals c v] @ F2)" 
              "F' @ [c]"]
    by simp
qed

lemma satisfiedClauseCanBeRemoved:
assumes
  "equivalentFormulae (F @ val2form v) F'"
  "clauseTrue c v"
shows "equivalentFormulae (F @ val2form v) (F' @ [c])"
unfolding equivalentFormulae_def
proof
  fix v' :: Valuation
  show "model v' (F @ val2form v) = model v' (F' @ [c])"
  proof
    assume "model v' (F @ val2form v)"
    hence "consistent v'" and "formulaTrue (F @ val2form v) v'"
      by auto
    
    from \<open>model v' (F @ val2form v)\<close> \<open>equivalentFormulae (F @ val2form v) F'\<close>
    have "model v' F'"
      unfolding equivalentFormulae_def
      by auto
    moreover
    have "clauseTrue c v'"
    proof-
      from \<open>clauseTrue c v\<close>
      obtain l :: Literal
        where "literalTrue l v" and "l el c"
        by (auto simp add:clauseTrueIffContainsTrueLiteral)
      with \<open>formulaTrue (F @ val2form v) v'\<close>
      have "literalTrue l v'"
        using val2formFormulaTrue[of "v" "v'"]
        using formulaTrueAppend[of "F" "val2form v"]
        by simp
      thus ?thesis
        using \<open>l el c\<close>
        by (auto simp add:clauseTrueIffContainsTrueLiteral)
    qed
    ultimately
    show "model v' (F' @ [c])"
      by (simp add: formulaTrueAppend)
  next
    assume "model v' (F' @ [c])"
    thus "model v' (F @ val2form v)"
      using \<open>equivalentFormulae (F @ val2form v) F'\<close>
      unfolding equivalentFormulae_def
      using formulaTrueAppend[of "F'" "[c]" "v'"]
      by auto
  qed
qed

lemma formulaEntailsClauseRemoveEntailedLiteralOpposites:
assumes
  "formulaEntailsClause F clause"
  "formulaEntailsValuation F valuation"
shows
  "formulaEntailsClause F (list_diff clause (oppositeLiteralList valuation))"
proof-
  {
    fix valuation'
    assume "model valuation' F"
    hence "consistent valuation'" "formulaTrue F valuation'"
      by (auto simp add: formulaTrueAppend)

    have "model valuation' clause"
      using \<open>consistent valuation'\<close>
      using \<open>formulaTrue F valuation'\<close>
      using \<open>formulaEntailsClause F clause\<close>
      unfolding formulaEntailsClause_def
      by simp

    then obtain l::Literal
      where "l el clause" "literalTrue l valuation'"
      by (auto simp add: clauseTrueIffContainsTrueLiteral)
    moreover
    hence "\<not> l el (oppositeLiteralList valuation)"
    proof-
      {
        assume "l el (oppositeLiteralList valuation)"
        hence "(opposite l) el valuation"
          using literalElListIffOppositeLiteralElOppositeLiteralList[of "l" "oppositeLiteralList valuation"]
          by simp
        hence "formulaEntailsLiteral F (opposite l)"
          using \<open>formulaEntailsValuation F valuation\<close>
          unfolding formulaEntailsValuation_def
          by simp
        hence "literalFalse l valuation'"
          using \<open>consistent valuation'\<close>
          using \<open>formulaTrue F valuation'\<close>
          unfolding formulaEntailsLiteral_def
          by simp
        with \<open>literalTrue l valuation'\<close>
          \<open>consistent valuation'\<close>
        have False
          by (simp add: inconsistentCharacterization)
      } thus ?thesis
        by auto
    qed
    ultimately
    have "model valuation' (list_diff clause (oppositeLiteralList valuation))"
      using \<open>consistent valuation'\<close>
      using listDiffIff[of "l" "clause" "oppositeLiteralList valuation"]
      by (auto simp add: clauseTrueIffContainsTrueLiteral)
  } thus ?thesis
    unfolding formulaEntailsClause_def
    by simp
qed



(*--------------------------------------------------------------------------------*)
subsubsection\<open>Resolution\<close>

definition
"resolve clause1 clause2 literal == removeAll literal clause1 @ removeAll (opposite literal) clause2"

lemma resolventIsEntailed: 
  fixes clause1 :: Clause and clause2 :: Clause and literal :: Literal
  shows "formulaEntailsClause [clause1, clause2] (resolve clause1 clause2 literal)"
proof -
  {
    fix valuation :: Valuation
    assume "model valuation [clause1, clause2]"
    from \<open>model valuation [clause1, clause2]\<close> obtain l1 :: Literal
      where "l1 el clause1" and "literalTrue l1 valuation"
      by (auto simp add: formulaTrueIffAllClausesAreTrue clauseTrueIffContainsTrueLiteral)
    from \<open>model valuation [clause1, clause2]\<close> obtain l2 :: Literal
      where "l2 el clause2" and "literalTrue l2 valuation"
      by (auto simp add: formulaTrueIffAllClausesAreTrue clauseTrueIffContainsTrueLiteral)
    have "clauseTrue (resolve clause1 clause2 literal) valuation"
    proof (cases "literal = l1")
      case False
      with \<open>l1 el clause1\<close> 
      have "l1 el (resolve clause1 clause2 literal)" 
        by (auto simp add:resolve_def)
      with \<open>literalTrue l1 valuation\<close> 
      show ?thesis 
        by (auto simp add: clauseTrueIffContainsTrueLiteral)
    next
      case True
      from \<open>model valuation [clause1, clause2]\<close> 
      have "consistent valuation" 
        by simp
      from True \<open>literalTrue l1 valuation\<close> \<open>literalTrue l2 valuation\<close> \<open>consistent valuation\<close> 
      have "literal \<noteq> opposite l2"
        by (auto simp add:inconsistentCharacterization)
      with \<open>l2 el clause2\<close> 
      have "l2 el (resolve clause1 clause2 literal)"
        by (auto simp add:resolve_def)
      with \<open>literalTrue l2 valuation\<close> 
      show ?thesis
        by (auto simp add: clauseTrueIffContainsTrueLiteral)
    qed
  } 
  thus ?thesis 
    by (simp add: formulaEntailsClause_def)
qed

lemma formulaEntailsResolvent:
  fixes formula :: Formula and clause1 :: Clause and clause2 :: Clause
  assumes "formulaEntailsClause formula clause1" and "formulaEntailsClause formula clause2"
  shows "formulaEntailsClause formula (resolve clause1 clause2 literal)"
proof -
  {
    fix valuation :: Valuation
    assume "model valuation formula"
    hence "consistent valuation" 
      by simp
    from \<open>model valuation formula\<close> \<open>formulaEntailsClause formula clause1\<close> 
    have "clauseTrue clause1 valuation"
      by (simp add:formulaEntailsClause_def)
    from \<open>model valuation formula\<close> \<open>formulaEntailsClause formula clause2\<close> 
    have "clauseTrue clause2 valuation"
      by (simp add:formulaEntailsClause_def)
    from \<open>clauseTrue clause1 valuation\<close> \<open>clauseTrue clause2 valuation\<close> \<open>consistent valuation\<close> 
    have "clauseTrue (resolve clause1 clause2 literal) valuation" 
      using resolventIsEntailed
      by (auto simp add: formulaEntailsClause_def)
    with \<open>consistent valuation\<close> 
    have "model valuation (resolve clause1 clause2 literal)"
      by simp
  }
  thus ?thesis
    by (simp add: formulaEntailsClause_def)
qed

lemma resolveFalseClauses:
  fixes literal :: Literal and clause1 :: Clause and clause2 :: Clause and valuation :: Valuation
  assumes 
  "clauseFalse (removeAll literal clause1) valuation" and
  "clauseFalse (removeAll (opposite literal) clause2) valuation"
  shows "clauseFalse (resolve clause1 clause2 literal) valuation"
proof -
  {
    fix l :: Literal
    assume "l el (resolve clause1 clause2 literal)"
    have "literalFalse l valuation"
    proof-
      from \<open>l el (resolve clause1 clause2 literal)\<close> 
      have "l el (removeAll literal clause1) \<or> l el (removeAll (opposite literal) clause2)"
        unfolding resolve_def
        by simp
      thus ?thesis 
      proof
        assume "l el (removeAll literal clause1)"
        thus "literalFalse l valuation"
          using \<open>clauseFalse (removeAll literal clause1) valuation\<close>
          by (simp add: clauseFalseIffAllLiteralsAreFalse)
      next
        assume "l el (removeAll (opposite literal) clause2)"
        thus "literalFalse l valuation"
          using \<open>clauseFalse (removeAll (opposite literal) clause2) valuation\<close>
          by (simp add: clauseFalseIffAllLiteralsAreFalse)
      qed
    qed
  }
  thus ?thesis
    by (simp add: clauseFalseIffAllLiteralsAreFalse)
qed

(*--------------------------------------------------------------------------------*)
subsubsection\<open>Unit clauses\<close>

text\<open>Clause is unit in a valuation if all its literals but one are false, and that one is undefined.\<close>
definition isUnitClause :: "Clause \<Rightarrow> Literal \<Rightarrow> Valuation \<Rightarrow> bool"
where
"isUnitClause uClause uLiteral valuation == 
   uLiteral el uClause \<and> 
   \<not> (literalTrue uLiteral valuation) \<and> 
   \<not> (literalFalse uLiteral valuation) \<and> 
   (\<forall> literal. literal el uClause \<and> literal \<noteq> uLiteral \<longrightarrow> literalFalse literal valuation)"


lemma unitLiteralIsEntailed:
  fixes uClause :: Clause and uLiteral :: Literal and formula :: Formula and valuation :: Valuation
  assumes "isUnitClause uClause uLiteral valuation" and "formulaEntailsClause formula uClause"
  shows "formulaEntailsLiteral (formula @ val2form valuation) uLiteral"
proof -
  {
    fix valuation'
    assume "model valuation' (formula @ val2form valuation)"
    hence "consistent valuation'"
      by simp
    from \<open>model valuation' (formula @ val2form valuation)\<close> 
    have "formulaTrue formula valuation'" and "formulaTrue (val2form valuation) valuation'"
      by (auto simp add:formulaTrueAppend)
    from \<open>formulaTrue formula valuation'\<close> \<open>consistent valuation'\<close> \<open>formulaEntailsClause formula uClause\<close> 
    have "clauseTrue uClause valuation'"
      by (simp add:formulaEntailsClause_def)
    then obtain l :: Literal
      where "l el uClause" "literalTrue l valuation'"
      by (auto simp add: clauseTrueIffContainsTrueLiteral)
    hence "literalTrue uLiteral valuation'" 
    proof (cases "l = uLiteral")
      case True
      with \<open>literalTrue l valuation'\<close> 
      show ?thesis
        by simp
    next
      case False
      with \<open>l el uClause\<close> \<open>isUnitClause uClause uLiteral valuation\<close> 
      have "literalFalse l valuation"
        by (simp add: isUnitClause_def)
      from \<open>formulaTrue (val2form valuation) valuation'\<close> 
      have "\<forall> literal :: Literal. literal el valuation \<longrightarrow> literal el valuation'"
        using val2formFormulaTrue [of "valuation" "valuation'"]
        by simp
      with \<open>literalFalse l valuation\<close> 
      have "literalFalse l valuation'"
        by auto
      with \<open>literalTrue l valuation'\<close> \<open>consistent valuation'\<close> 
      have "False"
        by (simp add:inconsistentCharacterization)
      thus ?thesis ..
    qed
  }
  thus ?thesis
    by (simp add: formulaEntailsLiteral_def)
qed

lemma isUnitClauseRemoveAllUnitLiteralIsFalse: 
  fixes uClause :: Clause and uLiteral :: Literal and valuation :: Valuation
  assumes "isUnitClause uClause uLiteral valuation"
  shows "clauseFalse (removeAll uLiteral uClause) valuation"
proof -
  {
    fix literal :: Literal
    assume "literal el (removeAll uLiteral uClause)"
    hence "literal el uClause" and "literal \<noteq> uLiteral"
      by auto
    with \<open>isUnitClause uClause uLiteral valuation\<close> 
    have "literalFalse literal valuation"
      by (simp add: isUnitClause_def)
  }
  thus ?thesis 
    by (simp add: clauseFalseIffAllLiteralsAreFalse)
qed

lemma isUnitClauseAppendValuation:
  assumes "isUnitClause uClause uLiteral valuation" "l \<noteq> uLiteral" "l \<noteq> opposite uLiteral"
  shows "isUnitClause uClause uLiteral (valuation @ [l])"
using assms
unfolding isUnitClause_def
by auto

lemma containsTrueNotUnit:
assumes
  "l el c" and "literalTrue l v" and "consistent v"
shows
  "\<not> (\<exists> ul. isUnitClause c ul v)"
using assms
unfolding isUnitClause_def
by (auto simp add: inconsistentCharacterization)

lemma unitBecomesFalse:
assumes
  "isUnitClause uClause uLiteral valuation" 
shows
  "clauseFalse uClause (valuation @ [opposite uLiteral])"
using assms
using isUnitClauseRemoveAllUnitLiteralIsFalse[of "uClause" "uLiteral" "valuation"]
by (auto simp add: clauseFalseIffAllLiteralsAreFalse)


(*--------------------------------------------------------------------------------*)
subsubsection\<open>Reason clauses\<close>

text\<open>A clause is @{term reason} for unit propagation of a given literal if it was a unit clause before it 
  is asserted, and became true when it is asserted.\<close>
  
definition
isReason::"Clause \<Rightarrow> Literal \<Rightarrow> Valuation \<Rightarrow> bool"
where
"(isReason clause literal valuation) ==
  (literal el clause) \<and> 
  (clauseFalse (removeAll literal clause) valuation) \<and>
  (\<forall> literal'. literal' el (removeAll literal clause) 
       \<longrightarrow> precedes (opposite literal') literal valuation \<and> opposite literal' \<noteq> literal)"

lemma isReasonAppend: 
  fixes clause :: Clause and literal :: Literal and valuation :: Valuation and valuation' :: Valuation
  assumes "isReason clause literal valuation" 
  shows "isReason clause literal (valuation @ valuation')"
proof -
  from assms 
  have "literal el clause" and 
    "clauseFalse (removeAll literal clause) valuation" (is "?false valuation") and
    "\<forall> literal'. literal' el (removeAll literal clause) \<longrightarrow> 
          precedes (opposite literal') literal valuation \<and> opposite literal' \<noteq> literal" (is "?precedes valuation")
    unfolding isReason_def
    by auto
  moreover
  from  \<open>?false valuation\<close> 
  have "?false (valuation @ valuation')"
    by (rule clauseFalseAppendValuation)
  moreover
  from  \<open>?precedes valuation\<close> 
  have "?precedes (valuation @ valuation')"
    by (simp add:precedesAppend)
  ultimately 
  show ?thesis
    unfolding isReason_def
    by auto
qed

lemma isUnitClauseIsReason: 
  fixes uClause :: Clause and uLiteral :: Literal and valuation :: Valuation
  assumes "isUnitClause uClause uLiteral valuation" "uLiteral el valuation'"
  shows "isReason uClause uLiteral (valuation @ valuation')"
proof -
  from assms 
  have "uLiteral el uClause" and "\<not> literalTrue uLiteral valuation" and "\<not> literalFalse uLiteral valuation"
    and "\<forall> literal. literal el uClause \<and> literal \<noteq> uLiteral \<longrightarrow> literalFalse literal valuation"
    unfolding isUnitClause_def
    by auto
  hence "clauseFalse (removeAll uLiteral uClause) valuation" 
    by (simp add: clauseFalseIffAllLiteralsAreFalse)
  hence "clauseFalse (removeAll uLiteral uClause) (valuation @ valuation')"
    by (simp add: clauseFalseAppendValuation)
  moreover
  have "\<forall> literal'. literal' el (removeAll uLiteral uClause) \<longrightarrow> 
    precedes (opposite literal') uLiteral (valuation @ valuation') \<and> (opposite literal') \<noteq> uLiteral"
  proof -
    {
      fix literal' :: Literal
      assume "literal' el (removeAll uLiteral uClause)"
      with \<open>clauseFalse (removeAll uLiteral uClause) valuation\<close> 
      have "literalFalse literal' valuation"
        by (simp add:clauseFalseIffAllLiteralsAreFalse)
      with \<open>\<not> literalTrue uLiteral valuation\<close> \<open>\<not> literalFalse uLiteral valuation\<close>
      have "precedes (opposite literal') uLiteral (valuation @ valuation') \<and> (opposite literal') \<noteq> uLiteral"
        using \<open>uLiteral el valuation'\<close>
        using precedesMemberHeadMemberTail [of "opposite literal'" "valuation" "uLiteral" "valuation'"]
        by auto
    }
    thus ?thesis 
      by simp
  qed
  ultimately
  show ?thesis using \<open>uLiteral el uClause\<close>
    by (auto simp add: isReason_def)
qed

lemma isReasonHoldsInPrefix: 
  fixes prefix :: Valuation and valuation :: Valuation and clause :: Clause and literal :: Literal
  assumes 
  "literal el prefix" and 
  "isPrefix prefix valuation" and 
  "isReason clause literal valuation"
  shows 
  "isReason clause literal prefix"
proof -
  from \<open>isReason clause literal valuation\<close> 
  have
    "literal el clause" and 
    "clauseFalse (removeAll literal clause) valuation" (is "?false valuation") and
    "\<forall> literal'. literal' el (removeAll literal clause) \<longrightarrow> 
         precedes (opposite literal') literal valuation \<and> opposite literal' \<noteq> literal" (is "?precedes valuation")
    unfolding isReason_def
    by auto
  {
    fix literal' :: Literal
    assume "literal' el (removeAll literal clause)"
    with \<open>?precedes valuation\<close> 
    have "precedes (opposite literal') literal valuation" "(opposite literal') \<noteq> literal"
      by auto
    with \<open>literal el prefix\<close> \<open>isPrefix prefix valuation\<close>
    have "precedes (opposite literal') literal prefix \<and> (opposite literal') \<noteq> literal" 
      using laterInPrefixRetainsPrecedes [of "prefix" "valuation" "opposite literal'" "literal"]
      by auto
  } 
  note * = this
  hence "?precedes prefix"
    by auto
  moreover
  have "?false prefix" 
  proof -
    {
      fix literal' :: Literal
      assume "literal' el (removeAll literal clause)"
      from \<open>literal' el (removeAll literal clause)\<close> * 
      have "precedes (opposite literal') literal prefix"
        by simp
      with \<open>literal el prefix\<close> 
      have "literalFalse literal' prefix"
        unfolding precedes_def
        by (auto split: if_split_asm)
    }
    thus ?thesis
      by (auto simp add:clauseFalseIffAllLiteralsAreFalse)
  qed
  ultimately
  show ?thesis using \<open>literal el clause\<close>
    unfolding isReason_def
    by auto
qed


(*--------------------------------------------------------------------------------*)
subsubsection\<open>Last asserted literal of a list\<close>

text\<open>@{term lastAssertedLiteral} from a list is the last literal from a clause that is asserted in 
  a valuation.\<close>
definition 
isLastAssertedLiteral::"Literal \<Rightarrow> Literal list \<Rightarrow> Valuation \<Rightarrow> bool"
where
"isLastAssertedLiteral literal clause valuation ==
  literal el clause \<and> 
  literalTrue literal valuation \<and> 
  (\<forall> literal'. literal' el clause \<and> literal' \<noteq> literal \<longrightarrow> \<not> precedes literal literal' valuation)"

text\<open>Function that gets the last asserted literal of a list - specified only by its postcondition.\<close>
definition
getLastAssertedLiteral :: "Literal list \<Rightarrow> Valuation \<Rightarrow> Literal"
where
"getLastAssertedLiteral clause valuation == 
   last (filter (\<lambda> l::Literal. l el clause) valuation)"

lemma getLastAssertedLiteralCharacterization:
assumes
  "clauseFalse clause valuation"
  "clause \<noteq> []"
  "uniq valuation"
shows
  "isLastAssertedLiteral (getLastAssertedLiteral (oppositeLiteralList clause) valuation) (oppositeLiteralList clause) valuation"
proof-
  let ?oppc = "oppositeLiteralList clause"
  let ?l = "getLastAssertedLiteral ?oppc valuation"
  let ?f = "filter (\<lambda> l. l el ?oppc) valuation"

  have "?oppc \<noteq> []" 
    using \<open>clause \<noteq> []\<close>
    using oppositeLiteralListNonempty[of "clause"]
    by simp
  then obtain l'::Literal
    where "l' el ?oppc"
    by force
  
  have "\<forall> l::Literal. l el ?oppc \<longrightarrow> l el valuation"
  proof
    fix l::Literal
    show "l el ?oppc \<longrightarrow> l el valuation"
    proof
      assume "l el ?oppc"
      hence "opposite l el clause"
        using literalElListIffOppositeLiteralElOppositeLiteralList[of "l" "?oppc"]
        by simp
      thus "l el valuation"
        using \<open>clauseFalse clause valuation\<close>
        using clauseFalseIffAllLiteralsAreFalse[of "clause" "valuation"]
        by auto
    qed
  qed
  hence "l' el valuation"
    using \<open>l' el ?oppc\<close>
    by simp
  hence "l' el ?f"
    using \<open>l' el ?oppc\<close>
    by simp
  hence "?f \<noteq> []"
    using set_empty[of "?f"]
    by auto
  hence "last ?f el ?f"
    using last_in_set[of "?f"]
    by simp
  hence "?l el ?oppc" "literalTrue ?l valuation"
    unfolding getLastAssertedLiteral_def
    by auto
  moreover
  have "\<forall>literal'. literal' el ?oppc \<and> literal' \<noteq> ?l \<longrightarrow>
                    \<not> precedes ?l literal' valuation"
  proof
    fix literal'
    show "literal' el ?oppc \<and> literal' \<noteq> ?l \<longrightarrow> \<not> precedes ?l literal' valuation"
    proof
      assume "literal' el ?oppc \<and> literal' \<noteq> ?l"
      show "\<not> precedes ?l literal' valuation"
      proof (cases "literalTrue literal' valuation")
        case False
        thus ?thesis
          unfolding precedes_def
          by simp
      next
        case True
        with \<open>literal' el ?oppc \<and> literal' \<noteq> ?l\<close>
        have "literal' el ?f"
          by simp
        have "uniq ?f"
          using \<open>uniq valuation\<close>
          by (simp add: uniqDistinct)
        hence "\<not> precedes ?l literal' ?f"
          using lastPrecedesNoElement[of "?f"]
          using \<open>literal' el ?oppc \<and> literal' \<noteq> ?l\<close>
          unfolding getLastAssertedLiteral_def
          by auto
        thus ?thesis
          using precedesFilter[of "?l" "literal'" "valuation" "\<lambda> l. l el ?oppc"]
          using \<open>literal' el ?oppc \<and> literal' \<noteq> ?l\<close>
          using \<open>?l el ?oppc\<close>
          by auto
      qed
    qed
  qed
  ultimately
  show ?thesis
    unfolding isLastAssertedLiteral_def
    by simp
qed

lemma lastAssertedLiteralIsUniq: 
  fixes literal :: Literal and literal' :: Literal and literalList :: "Literal list" and valuation :: Valuation
  assumes 
  lastL: "isLastAssertedLiteral literal  literalList valuation" and
  lastL': "isLastAssertedLiteral literal' literalList valuation"
  shows "literal = literal'"
using assms
proof -
  from lastL have *: 
    "literal el literalList"  
    "\<forall> l. l el literalList \<and> l \<noteq> literal \<longrightarrow> \<not>  precedes literal l valuation" 
    and
    "literalTrue literal valuation"  
    by (auto simp add: isLastAssertedLiteral_def)
  from lastL' have **: 
    "literal' el literalList"
    "\<forall> l. l el literalList \<and> l \<noteq> literal' \<longrightarrow> \<not>  precedes literal' l valuation"
    and
    "literalTrue literal' valuation"
    by (auto simp add: isLastAssertedLiteral_def)
  {
    assume "literal' \<noteq> literal"
    with * ** have "\<not> precedes literal literal' valuation" and "\<not> precedes literal' literal valuation"
      by auto
    with \<open>literalTrue literal valuation\<close> \<open>literalTrue literal' valuation\<close> 
    have "False"
      using precedesTotalOrder[of "literal" "valuation" "literal'"]
      unfolding precedes_def
      by simp
  }
  thus ?thesis
    by auto
qed

lemma isLastAssertedCharacterization: 
  fixes literal :: Literal and literalList :: "Literal list" and v :: Valuation
  assumes "isLastAssertedLiteral literal (oppositeLiteralList literalList) valuation"
  shows "opposite literal el literalList" and "literalTrue literal valuation"
proof -
  from assms have
    *: "literal el (oppositeLiteralList literalList)" and **: "literalTrue literal valuation"  
    by (auto simp add: isLastAssertedLiteral_def)
  from * show "opposite literal el literalList"
    using literalElListIffOppositeLiteralElOppositeLiteralList [of "literal" "oppositeLiteralList literalList"]
    by simp
  from ** show "literalTrue literal valuation" 
    by simp
qed

lemma isLastAssertedLiteralSubset:
assumes
  "isLastAssertedLiteral l c M"
  "set c' \<subseteq> set c"
  "l el c'"
shows
  "isLastAssertedLiteral l c' M"
using assms
unfolding isLastAssertedLiteral_def
by auto

lemma lastAssertedLastInValuation: 
  fixes literal :: Literal and literalList :: "Literal list" and valuation :: Valuation
  assumes "literal el literalList" and "\<not> literalTrue literal valuation" 
  shows "isLastAssertedLiteral literal literalList (valuation @ [literal])"
proof -
  have "literalTrue literal [literal]" 
    by simp
  hence "literalTrue literal (valuation @ [literal])"
    by simp
  moreover
  have "\<forall> l. l el literalList \<and> l \<noteq> literal \<longrightarrow> \<not>  precedes literal l (valuation @ [literal])"
  proof -
    {
      fix l
      assume "l el literalList" "l \<noteq> literal"
      have "\<not> precedes literal l (valuation @ [literal])" 
      proof (cases "literalTrue l valuation")
        case False
        with \<open>l \<noteq> literal\<close> 
        show ?thesis
          unfolding precedes_def
          by simp
      next
        case True
        from \<open>\<not> literalTrue literal valuation\<close> \<open>literalTrue literal [literal]\<close> \<open>literalTrue l valuation\<close> 
        have "precedes l literal (valuation @ [literal])"
          using precedesMemberHeadMemberTail[of "l" "valuation" "literal" "[literal]"]
          by auto
        with \<open>l \<noteq> literal\<close> \<open>literalTrue l valuation\<close> \<open>literalTrue literal [literal]\<close>
        show ?thesis
          using precedesAntisymmetry[of "l" "valuation @ [literal]" "literal"]
          unfolding precedes_def
          by auto
      qed
    } thus ?thesis 
      by simp
  qed
  ultimately
  show ?thesis using \<open>literal el literalList\<close>
    by (simp add:isLastAssertedLiteral_def)
qed

end
