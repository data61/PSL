(*    Title:              SatSolverVerification/SatSolverVerification.thy
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

section\<open>Verification of DPLL based SAT solvers.\<close>
theory SatSolverVerification
imports CNF Trail
begin

text\<open>This theory contains a number of lemmas used in verification of
different SAT solvers. Although this file does not contain any
theorems significant on their own, it is an essential part of the SAT
solver correctness proof because it contains most of the technical
details used in the proofs that follow. These lemmas serve as a basis
for partial correctness proof for pseudo-code implementation of modern
SAT solvers described in \cite{JARrad}, in terms of Hoare logic.\<close>

(******************************************************************************)
subsection\<open>Literal Trail\<close>
(******************************************************************************)
text\<open>LiteralTrail is a Trail consisting of literals, where decision literals are marked.\<close>

type_synonym LiteralTrail = "Literal Trail"

abbreviation isDecision :: "('a \<times> bool) \<Rightarrow> bool"
  where "isDecision l == marked l"

abbreviation lastDecision :: "LiteralTrail \<Rightarrow> Literal"
  where "lastDecision M == Trail.lastMarked M"

abbreviation decisions :: "LiteralTrail \<Rightarrow> Literal list"
  where "decisions M == Trail.markedElements M"

abbreviation decisionsTo :: "Literal \<Rightarrow> LiteralTrail \<Rightarrow> Literal list"
  where "decisionsTo M l == Trail.markedElementsTo M l"

abbreviation prefixBeforeLastDecision :: "LiteralTrail \<Rightarrow> LiteralTrail"
  where "prefixBeforeLastDecision M == Trail.prefixBeforeLastMarked M"

(*--------------------------------------------------------------------------*)
(*                            I N V A R I A N T S                           *)
(*--------------------------------------------------------------------------*)
(******************************************************************************)
subsection\<open>Invariants\<close>
(******************************************************************************)
text\<open>In this section a number of conditions will be formulated and
it will be shown that these conditions are invariant after applying
different DPLL-based transition rules.\<close>

definition
"InvariantConsistent (M::LiteralTrail) == consistent (elements M)"

definition
"InvariantUniq (M::LiteralTrail) == uniq (elements M)"

definition
"InvariantImpliedLiterals (F::Formula) (M::LiteralTrail) == \<forall> l. l el elements M \<longrightarrow> formulaEntailsLiteral (F @ val2form (decisionsTo l M)) l"

definition
"InvariantEquivalent (F0::Formula) (F::Formula) == equivalentFormulae F0 F"

definition
"InvariantVarsM  (M::LiteralTrail) (F0::Formula) (Vbl::Variable set) == vars (elements M) \<subseteq> vars F0 \<union> Vbl"

definition
"InvariantVarsF (F::Formula) (F0::Formula) (Vbl::Variable set) == vars F \<subseteq> vars F0 \<union> Vbl"


text\<open>The following invariants are used in conflict analysis.\<close>
definition
"InvariantCFalse (conflictFlag::bool) (M::LiteralTrail) (C::Clause) == conflictFlag \<longrightarrow> clauseFalse C (elements M)"

definition
"InvariantCEntailed (conflictFlag::bool) (F::Formula) (C::Clause) == conflictFlag \<longrightarrow> formulaEntailsClause F C"

definition
"InvariantReasonClauses (F::Formula) (M::LiteralTrail) == 
  \<forall> literal. literal el (elements M) \<and> \<not> literal el decisions M \<longrightarrow> 
             (\<exists> clause. formulaEntailsClause F clause \<and> isReason clause literal (elements M))"



(*----------------------------------------------------------------------*)
(*           V E R I F I C A T I O N     L E M M A S                    *)
(*----------------------------------------------------------------------*)
subsubsection\<open>Auxiliary lemmas\<close>
text\<open>This section contains some auxiliary lemmas that additionally 
  characterize some of invariants that have been defined.\<close>

(*-------------------------   InvariantImpliedLiterals    ---------------------*)
text\<open>Lemmas about @{term InvariantImpliedLiterals}.\<close>
lemma InvariantImpliedLiteralsWeakerVariant:
  fixes M :: LiteralTrail and F :: Formula
  assumes "\<forall> l. l el elements M \<longrightarrow> formulaEntailsLiteral (F @ val2form (decisionsTo l M)) l"
  shows "\<forall> l. l el elements M \<longrightarrow> formulaEntailsLiteral (F @ val2form (decisions M)) l"
proof -
  { 
    fix l :: Literal
    assume "l el elements M"
    with assms 
    have "formulaEntailsLiteral (F @ val2form (decisionsTo l M)) l"
      by simp
    have "isPrefix (decisionsTo l M) (decisions M)"
      by (simp add: markedElementsToArePrefixOfMarkedElements)
    then obtain s :: Valuation 
      where "(decisionsTo l M) @ s = (decisions M)"
      using isPrefix_def [of "decisionsTo l M" "decisions M"]
      by auto
    hence "(decisions M) = (decisionsTo l M) @ s"
      by (rule sym)
    with \<open>formulaEntailsLiteral (F @ val2form (decisionsTo l M)) l\<close>
    have "formulaEntailsLiteral (F @ val2form (decisions M)) l"
      using formulaEntailsLiteralAppend [of "F @ val2form (decisionsTo l M)" "l" "val2form s"]
      by (auto simp add:formulaEntailsLiteralAppend val2formAppend)
  }
  thus ?thesis
    by simp
qed

lemma InvariantImpliedLiteralsAndElementsEntailLiteralThenDecisionsEntailLiteral: 
  fixes M :: LiteralTrail and F :: Formula and literal :: Literal
  assumes "InvariantImpliedLiterals F M" and "formulaEntailsLiteral (F @ (val2form (elements M))) literal"
  shows "formulaEntailsLiteral (F @ val2form (decisions M)) literal"
proof -
  {
    fix valuation :: Valuation
    assume "model valuation (F @ val2form (decisions M))"
    hence "formulaTrue F valuation" and "formulaTrue (val2form (decisions M)) valuation" and "consistent valuation"
      by (auto simp add: formulaTrueAppend)
    {
      fix l :: Literal
      assume "l el (elements M)"
      from \<open>InvariantImpliedLiterals F M\<close>
      have "\<forall> l. l el (elements M) \<longrightarrow> formulaEntailsLiteral (F @ val2form (decisions M)) l"
        by (simp add: InvariantImpliedLiteralsWeakerVariant InvariantImpliedLiterals_def)
      with \<open>l el (elements M)\<close>
      have "formulaEntailsLiteral (F @ val2form (decisions M)) l"
        by simp
      with \<open>model valuation (F @ val2form (decisions M))\<close>
      have "literalTrue l valuation"
        by (simp add: formulaEntailsLiteral_def)
    } 
    hence "formulaTrue (val2form (elements M)) valuation"
      by (simp add: val2formFormulaTrue)
    with \<open>formulaTrue F valuation\<close> \<open>consistent valuation\<close>
    have "model valuation (F @ (val2form (elements M)))"
      by (auto simp add:formulaTrueAppend)
    with \<open>formulaEntailsLiteral (F @ (val2form (elements M))) literal\<close>
    have "literalTrue literal valuation"
      by (simp add: formulaEntailsLiteral_def)
  }
  thus ?thesis 
    by (simp add: formulaEntailsLiteral_def)
qed    

lemma InvariantImpliedLiteralsAndFormulaFalseThenFormulaAndDecisionsAreNotSatisfiable: 
  fixes M :: LiteralTrail and F :: Formula
  assumes "InvariantImpliedLiterals F M" and "formulaFalse F (elements M)" 
  shows "\<not> satisfiable (F @ val2form (decisions M))"
proof -
  from \<open>formulaFalse F (elements M)\<close>
  have "formulaFalse (F @ val2form (decisions M)) (elements M)"
    by (simp add: formulaFalseAppend)
  moreover
  from \<open>InvariantImpliedLiterals F M\<close>
  have "formulaEntailsValuation (F @ val2form (decisions M)) (elements M)"
    unfolding formulaEntailsValuation_def
    unfolding InvariantImpliedLiterals_def
    using InvariantImpliedLiteralsWeakerVariant[of "M" "F"]
    by simp
  ultimately
  show ?thesis
    using formulaFalseInEntailedValuationIsUnsatisfiable [of "F @ val2form (decisions M)" "elements M"]
    by simp
qed

lemma InvariantImpliedLiteralsHoldsForPrefix:
  fixes M :: LiteralTrail and prefix :: LiteralTrail and F :: Formula
  assumes "InvariantImpliedLiterals F M"  and "isPrefix prefix M" 
  shows "InvariantImpliedLiterals F prefix"
proof -
  {
    fix l :: Literal
    assume *: "l el elements prefix"

    from * \<open>isPrefix prefix M\<close>
    have "l el elements M"
      unfolding isPrefix_def
      by auto

    from * and \<open>isPrefix prefix M\<close>
    have "decisionsTo l prefix = decisionsTo l M"
      using markedElementsToPrefixElement [of "prefix" "M" "l"]
      by simp

    from \<open>InvariantImpliedLiterals F M\<close> and \<open>l el elements M\<close>
    have "formulaEntailsLiteral (F @ val2form (decisionsTo l M)) l"
      by (simp add:InvariantImpliedLiterals_def)
    with \<open>decisionsTo l prefix = decisionsTo l M\<close>
    have "formulaEntailsLiteral (F @ val2form (decisionsTo l prefix)) l"
      by simp
  } thus ?thesis
    by (auto simp add: InvariantImpliedLiterals_def)
qed


(*-------------------------   InvariantReasonClauses    ---------------------*)
text\<open>Lemmas about @{term InvariantReasonClauses}.\<close>
lemma InvariantReasonClausesHoldsForPrefix:
  fixes F::Formula and M::LiteralTrail and p::LiteralTrail
  assumes "InvariantReasonClauses F M" and "InvariantUniq M"  and
  "isPrefix p M" 
  shows "InvariantReasonClauses F p"
proof-
  from \<open>InvariantReasonClauses F M\<close>
  have *: "\<forall> literal. literal el elements M \<and> \<not> literal el decisions M \<longrightarrow> 
                    (\<exists> clause. formulaEntailsClause F clause \<and> isReason clause literal (elements M))"
    unfolding InvariantReasonClauses_def 
    by simp
  from \<open>InvariantUniq M\<close>
  have "uniq (elements M)"
    unfolding InvariantUniq_def 
    by simp
  {
    fix literal::Literal
    assume "literal el elements p" and "\<not> literal el decisions p"
      from \<open>isPrefix p M\<close> \<open>literal el (elements p)\<close>
      have "literal el (elements M)"
        by (auto simp add: isPrefix_def)
      moreover
      from \<open>isPrefix p M\<close> \<open>literal el (elements p)\<close> \<open>\<not> literal el (decisions p)\<close> \<open>uniq (elements M)\<close>
      have "\<not> literal el decisions M"
        using markedElementsTrailMemPrefixAreMarkedElementsPrefix [of "M" "p" "literal"]
        by auto
      ultimately
      obtain clause::Clause where
        "formulaEntailsClause F clause" "isReason clause literal (elements M)"
        using *
        by auto
      with \<open>literal el elements p\<close> \<open>\<not>  literal el decisions p\<close> \<open>isPrefix p M\<close>
      have "isReason clause literal (elements p)"
        using isReasonHoldsInPrefix[of "literal" "elements p" "elements M" "clause"]
        by (simp add:isPrefixElements)
      with \<open>formulaEntailsClause F clause\<close>
      have "\<exists> clause. formulaEntailsClause F clause \<and> isReason clause literal (elements p)"
        by auto
  }
  thus ?thesis
    unfolding InvariantReasonClauses_def
    by auto
qed

lemma InvariantReasonClausesHoldsForPrefixElements:
  fixes F::Formula and M::LiteralTrail and p::LiteralTrail
  assumes "InvariantReasonClauses F p" and
  "isPrefix p M" and
  "literal el (elements p)" and "\<not> literal el decisions M"
  shows "\<exists> clause. formulaEntailsClause F clause \<and> isReason clause literal (elements M)"
proof -
  from \<open>isPrefix p M\<close> \<open>\<not> literal el (decisions M)\<close>
  have "\<not> literal el (decisions p)"
    using markedElementsPrefixAreMarkedElementsTrail[of "p" "M" "literal"]
    by auto

  from \<open>InvariantReasonClauses F p\<close> \<open>literal el (elements p)\<close> \<open>\<not> literal el (decisions p)\<close> obtain clause :: Clause
    where "formulaEntailsClause F clause" "isReason clause literal (elements p)"
    unfolding InvariantReasonClauses_def
    by auto
  with \<open>isPrefix p M\<close>
  have "isReason clause literal (elements M)"
    using isReasonAppend [of "clause" "literal" "elements p"]
    by (auto simp add: isPrefix_def)
  with \<open>formulaEntailsClause F clause\<close>
  show ?thesis
    by auto
qed

(*----------------------------------------------------------------------*)
(*           V E R I F I C A T I O N     L E M M A S                    *)
(*----------------------------------------------------------------------*)
subsubsection\<open>Transition rules preserve invariants\<close>

text\<open>In this section it will be proved that the different DPLL-based
transition rules preserves given invariants. Rules are implicitly given
in their most general form. Explicit definition of transition rules will be
done in theories that describe specific solvers.\<close>

(************************************************************************)
(*                       A P P L Y    D E C I D E                       *)
(************************************************************************)
text\<open>$Decide$ transition rule.\<close>
lemma InvariantUniqAfterDecide: 
  fixes M :: LiteralTrail and literal :: Literal and M' :: LiteralTrail
  assumes "InvariantUniq M" and 
  "var literal \<notin> vars (elements M)" and
  "M' = M @ [(literal, True)]"
  shows "InvariantUniq M'"
proof -
  from \<open>InvariantUniq M\<close>
  have "uniq (elements M)"
    unfolding InvariantUniq_def 
    .
  {
    assume "\<not> uniq (elements M')"
    with \<open>uniq (elements M)\<close> \<open>M' = M @ [(literal, True)]\<close>
    have "literal el (elements M)"
      using uniqButlastNotUniqListImpliesLastMemButlast [of "elements M'"]
      by auto
    hence "var literal \<in> vars (elements M)"
      using valuationContainsItsLiteralsVariable [of "literal" "elements M"]
      by simp
    with \<open>var literal \<notin> vars (elements M)\<close>
    have "False"
      by simp
  }
  thus ?thesis
    unfolding InvariantUniq_def
    by auto
qed

lemma InvariantImpliedLiteralsAfterDecide: 
  fixes F :: Formula and M :: LiteralTrail and literal :: Literal and M' :: LiteralTrail
  assumes "InvariantImpliedLiterals F M" and
  "var literal \<notin> vars (elements M)" and
  "M' = M @ [(literal, True)]"
  shows "InvariantImpliedLiterals F M'"
proof -
  {
    fix l :: Literal
    assume "l el elements M'"
    have "formulaEntailsLiteral (F @ val2form (decisionsTo l M')) l"
    proof (cases "l el elements M")
      case True
      with \<open>M' = M @ [(literal, True)]\<close>
      have "decisionsTo l M' = decisionsTo l M"
        by (simp add: markedElementsToAppend)
      with \<open>InvariantImpliedLiterals F M\<close> \<open>l el elements M\<close>
      show ?thesis
        by (simp add: InvariantImpliedLiterals_def)
    next
      case False
      with \<open>l el elements M'\<close> and \<open>M' = M @ [(literal, True)]\<close>
      have "l = literal"
        by (auto split: if_split_asm)
      have "clauseEntailsLiteral [literal] literal" 
        by (simp add: clauseEntailsLiteral_def)
      moreover
      have "[literal] el (F @ val2form (decisions M) @ [[literal]])"
        by simp
      moreover
      {
        have "isDecision (last (M @ [(literal, True)]))"
          by simp
        moreover
        from \<open>var literal \<notin> vars (elements M)\<close>
        have "\<not> literal el (elements M)"
          using valuationContainsItsLiteralsVariable[of "literal" "elements M"]
          by auto
        ultimately
        have "decisionsTo literal (M @ [(literal, True)])  = ((decisions M) @ [literal])"
          using lastTrailElementMarkedImpliesMarkedElementsToLastElementAreAllMarkedElements [of "M @ [(literal, True)]"]
          by (simp add:markedElementsAppend)
      }
      ultimately
      show ?thesis
         using \<open>M' = M @ [(literal, True)]\<close> \<open>l = literal\<close> 
           clauseEntailsLiteralThenFormulaEntailsLiteral [of "[literal]" "F @ val2form (decisions M) @ [[literal]]" "literal"] 
         by (simp add:val2formAppend)
    qed
  }
  thus ?thesis
    by (simp add:InvariantImpliedLiterals_def)
qed

lemma InvariantVarsMAfterDecide: 
  fixes F :: Formula and F0 :: Formula and M :: LiteralTrail and literal :: Literal and M' :: LiteralTrail
  assumes "InvariantVarsM M F0 Vbl" and 
  "var literal \<in> Vbl" and 
  "M' = M @ [(literal, True)]"
  shows "InvariantVarsM M' F0 Vbl"
proof -
  from \<open>InvariantVarsM M F0 Vbl\<close>
  have "vars (elements M) \<subseteq> vars F0 \<union> Vbl"
    by (simp only:InvariantVarsM_def)
  from \<open>M' = M @ [(literal, True)]\<close>
  have "vars (elements M') = vars (elements (M @ [(literal, True)]))"
    by simp
  also have "... = vars (elements M @ [literal])"
    by simp
  also have "... = vars (elements M) \<union>  vars [literal]"
    using varsAppendClauses [of "elements M" "[literal]"]
    by simp
  finally
  show ?thesis
    using \<open>vars (elements M) \<subseteq> (vars F0) \<union> Vbl\<close> \<open>var literal \<in> Vbl\<close>
    unfolding InvariantVarsM_def
    by auto
qed

lemma InvariantConsistentAfterDecide: 
  fixes M :: LiteralTrail and literal :: Literal and M' :: LiteralTrail
  assumes "InvariantConsistent M" and 
  "var literal \<notin> vars (elements M)" and
  "M' = M @ [(literal, True)]"
  shows "InvariantConsistent M'"
proof -
  from \<open>InvariantConsistent M\<close>
  have "consistent (elements M)"
    unfolding InvariantConsistent_def 
    .
  {
    assume "inconsistent (elements M')"
    with \<open>M' = M @ [(literal, True)]\<close>
    have "inconsistent (elements M) \<or> inconsistent [literal] \<or> (\<exists> l. literalTrue l (elements M) \<and> literalFalse l [literal])"
      using inconsistentAppend [of "elements M" "[literal]"]
      by simp
    with \<open>consistent (elements M)\<close> obtain l :: Literal 
      where "literalTrue l (elements M)" and "literalFalse l [literal]"
      by auto
    hence "(opposite l) = literal"
      by auto
    hence "var literal = var l"
      by auto
    with \<open>literalTrue l (elements M)\<close>
    have "var l \<in> vars (elements M)"
      using valuationContainsItsLiteralsVariable [of "l" "elements M"]
      by simp
    with \<open>var literal = var l\<close> \<open>var literal \<notin> vars (elements M)\<close>
    have "False"
      by simp
  }
  thus ?thesis
    unfolding InvariantConsistent_def
    by auto
qed

lemma InvariantReasonClausesAfterDecide:
  fixes F :: Formula and M :: LiteralTrail and M' :: LiteralTrail
  assumes "InvariantReasonClauses F M" and "InvariantUniq M" and
  "M' = M @ [(literal, True)]"
  shows "InvariantReasonClauses F M'"
proof -
  {
    fix literal' :: Literal
    assume "literal' el elements M'" and "\<not> literal' el decisions M'"
    
    have "\<exists> clause. formulaEntailsClause F clause \<and> isReason clause literal' (elements M')"
    proof (cases "literal' el elements M")
      case True
      with assms \<open>\<not> literal' el decisions M'\<close> obtain clause::Clause
        where "formulaEntailsClause F clause \<and> isReason clause literal' (elements M')"
        using InvariantReasonClausesHoldsForPrefixElements [of "F" "M" "M'" "literal'"]
        by (auto simp add:isPrefix_def)
      thus ?thesis
        by auto
    next
      case False
      with \<open>M' = M @ [(literal, True)]\<close> \<open>literal' el elements M'\<close>
      have "literal = literal'"
        by (simp split: if_split_asm)
      with \<open>M' = M @ [(literal, True)]\<close> 
      have "literal' el decisions M'"
        using markedElementIsMarkedTrue[of "literal" "M'"]
        by simp
      with \<open>\<not> literal' el decisions M'\<close>
      have "False"
        by simp
      thus ?thesis
        by simp
    qed
  }
  thus ?thesis
    unfolding InvariantReasonClauses_def
    by auto
qed

lemma InvariantCFalseAfterDecide:
  fixes conflictFlag::bool and M::LiteralTrail and C::Clause
  assumes "InvariantCFalse conflictFlag M C" and "M' = M @ [(literal, True)]"
  shows "InvariantCFalse conflictFlag M' C"
  unfolding InvariantCFalse_def
proof
  assume "conflictFlag"
  show "clauseFalse C (elements M')"
  proof -
    from \<open>InvariantCFalse conflictFlag M C\<close>
    have "conflictFlag \<longrightarrow> clauseFalse C (elements M)"
      unfolding InvariantCFalse_def 
      .
    with \<open>conflictFlag\<close>
    have "clauseFalse C (elements M)"
      by simp
    with \<open>M' = M @ [(literal, True)]\<close>
    show ?thesis
      by (simp add:clauseFalseAppendValuation)
  qed
qed

(************************************************************************)
(*             A P P L Y    U N I T   P R O P A G A T E                 *)
(************************************************************************)
text\<open>$UnitPropagate$ transition rule.\<close>

lemma InvariantImpliedLiteralsHoldsForUnitLiteral:
  fixes M :: LiteralTrail and F :: Formula and uClause :: Clause and uLiteral :: Literal
  assumes "InvariantImpliedLiterals F M" and
  "formulaEntailsClause F uClause" and "isUnitClause uClause uLiteral (elements M)" and
  "M' = M @ [(uLiteral, False)]"
  shows "formulaEntailsLiteral (F @ val2form (decisionsTo uLiteral M')) uLiteral"
proof-
  have "decisionsTo uLiteral M' = decisions M"
  proof -
    from \<open>isUnitClause uClause uLiteral (elements M)\<close>
    have "\<not> uLiteral el (elements M)"
      by (simp add: isUnitClause_def)
    with \<open>M' = M @ [(uLiteral, False)]\<close>
    show ?thesis
      using markedElementsToAppend[of "uLiteral" "M" "[(uLiteral, False)]"]
      unfolding markedElementsTo_def
      by simp
  qed
  moreover
  from \<open>formulaEntailsClause F uClause\<close> \<open>isUnitClause uClause uLiteral (elements M)\<close> 
  have "formulaEntailsLiteral (F @ val2form (elements M)) uLiteral"
    using unitLiteralIsEntailed [of "uClause" "uLiteral" "elements M" "F"]
    by simp
  with \<open>InvariantImpliedLiterals F M\<close>
  have "formulaEntailsLiteral (F @ val2form (decisions M)) uLiteral"
    by (simp add: InvariantImpliedLiteralsAndElementsEntailLiteralThenDecisionsEntailLiteral)
  ultimately
  show ?thesis
    by simp
qed

lemma InvariantImpliedLiteralsAfterUnitPropagate:
  fixes M :: LiteralTrail and F :: Formula and uClause :: Clause and uLiteral :: Literal
  assumes "InvariantImpliedLiterals F M" and
  "formulaEntailsClause F uClause" and "isUnitClause uClause uLiteral (elements M)" and
  "M' = M @ [(uLiteral, False)]"
  shows "InvariantImpliedLiterals F M'"
proof -
  {
    fix l :: Literal
    assume "l el (elements M')"
    have "formulaEntailsLiteral (F @ val2form (decisionsTo l M')) l"
    proof (cases "l el elements M")
      case True
      with \<open>InvariantImpliedLiterals F M\<close>
      have "formulaEntailsLiteral (F @ val2form (decisionsTo l M)) l"
        by (simp add:InvariantImpliedLiterals_def)
      moreover
      from \<open>M' = M @ [(uLiteral, False)]\<close>
      have "(isPrefix M M')"
        by (simp add:isPrefix_def)
      with True
      have "decisionsTo l M' = decisionsTo l M"
        by (simp add: markedElementsToPrefixElement)
      ultimately
      show ?thesis
        by simp
    next
      case False
      with \<open>l el (elements M')\<close> \<open>M' = M @ [(uLiteral, False)]\<close>
      have "l = uLiteral"
        by (auto split: if_split_asm)
      moreover
      from assms
      have "formulaEntailsLiteral (F @ val2form (decisionsTo uLiteral M')) uLiteral"
        using InvariantImpliedLiteralsHoldsForUnitLiteral [of "F" "M" "uClause" "uLiteral" "M'"]
        by simp
      ultimately
      show ?thesis
        by simp
    qed
  }
  thus ?thesis
    by (simp add:InvariantImpliedLiterals_def)
qed

lemma InvariantVarsMAfterUnitPropagate: 
  fixes F :: Formula and F0 :: Formula and M :: LiteralTrail and uClause :: Clause and uLiteral :: Literal and M' :: LiteralTrail
  assumes "InvariantVarsM M F0 Vbl" and
  "var uLiteral \<in> vars F0 \<union> Vbl" and
  "M' = M @ [(uLiteral, False)]"
  shows "InvariantVarsM M' F0 Vbl"
proof -
  from \<open>InvariantVarsM M F0 Vbl\<close>
  have "vars (elements M) \<subseteq>  vars F0 \<union> Vbl"
    unfolding InvariantVarsM_def 
    .
  thus ?thesis
    unfolding InvariantVarsM_def
    using \<open>var uLiteral \<in> vars F0 \<union> Vbl\<close>
    using \<open>M' = M @ [(uLiteral, False)]\<close>
      varsAppendClauses [of "elements M" "[uLiteral]"]
    by auto
qed

lemma InvariantConsistentAfterUnitPropagate:
  fixes M :: LiteralTrail and F :: Formula and M' :: LiteralTrail and uClause :: Clause and uLiteral :: Literal
  assumes "InvariantConsistent M" and
  "isUnitClause uClause uLiteral (elements M)" and
  "M' = M @ [(uLiteral, False)]"
  shows "InvariantConsistent M'"
proof -
  from \<open>InvariantConsistent M\<close>
  have "consistent (elements M)"
    unfolding InvariantConsistent_def 
    .
  from \<open>isUnitClause uClause uLiteral (elements M)\<close>
  have "\<not> literalFalse uLiteral (elements M)"
    unfolding isUnitClause_def
    by simp
  {
    assume "inconsistent (elements M')"
    with \<open>M' = M @ [(uLiteral, False)]\<close>
    have "inconsistent (elements M) \<or> inconsistent [unitLiteral] \<or> (\<exists> l. literalTrue l (elements M) \<and> literalFalse l [uLiteral])"
      using inconsistentAppend [of "elements M" "[uLiteral]"]
      by simp
    with \<open>consistent (elements M)\<close> obtain literal::Literal
      where "literalTrue literal (elements M)" and "literalFalse literal [uLiteral]"
      by auto
    hence "literal = opposite uLiteral"
      by auto
    with \<open>literalTrue literal (elements M)\<close> \<open>\<not> literalFalse uLiteral (elements M)\<close>
    have False
      by simp
  } thus ?thesis
    unfolding InvariantConsistent_def
    by auto
qed

lemma InvariantUniqAfterUnitPropagate:
  fixes M :: LiteralTrail and F :: Formula and M' :: LiteralTrail and uClause :: Clause and uLiteral :: Literal
  assumes "InvariantUniq M" and
  "isUnitClause uClause uLiteral (elements M)" and
  "M' = M @ [(uLiteral, False)]"
  shows "InvariantUniq M'"
proof-
  from \<open>InvariantUniq M\<close>
  have "uniq (elements M)"
    unfolding InvariantUniq_def 
    .
  moreover
  from \<open>isUnitClause uClause uLiteral (elements M)\<close>
  have "\<not> literalTrue uLiteral (elements M)"
    unfolding isUnitClause_def
    by simp
  ultimately
  show ?thesis
    using \<open>M' = M @ [(uLiteral, False)]\<close> uniqAppendElement[of "elements M" "uLiteral"]
    unfolding InvariantUniq_def
    by simp
qed

lemma InvariantReasonClausesAfterUnitPropagate:
  fixes M :: LiteralTrail and F :: Formula and M' :: LiteralTrail and uClause :: Clause and uLiteral :: Literal
  assumes "InvariantReasonClauses F M" and
  "formulaEntailsClause F uClause" and "isUnitClause uClause uLiteral (elements M)" and
  "M' = M @ [(uLiteral, False)]"
  shows "InvariantReasonClauses F M'"
proof -
  from \<open>InvariantReasonClauses F M\<close>
  have *: "(\<forall> literal. (literal el (elements M)) \<and> \<not> (literal el (decisions M)) \<longrightarrow> 
    (\<exists> clause. formulaEntailsClause F clause \<and> (isReason clause literal (elements M))))"
    unfolding InvariantReasonClauses_def 
    by simp
  {
    fix literal::Literal
    assume "literal el elements M'" "\<not> literal el decisions M'"
    have "\<exists> clause. formulaEntailsClause F clause \<and> isReason clause literal (elements M')" 
    proof (cases "literal el elements M")
      case True
      with assms \<open>\<not> literal el decisions M'\<close> obtain clause::Clause
        where "formulaEntailsClause F clause \<and> isReason clause literal (elements M')"
        using InvariantReasonClausesHoldsForPrefixElements [of "F" "M" "M'" "literal"]
        by (auto simp add:isPrefix_def)
      thus ?thesis
        by auto
    next
      case False
      with \<open>literal el (elements M')\<close> \<open>M' = M @ [(uLiteral, False)]\<close>
      have "literal = uLiteral"
        by simp
      with \<open>M' = M @ [(uLiteral, False)]\<close> \<open>isUnitClause uClause uLiteral (elements M)\<close> \<open>formulaEntailsClause F uClause\<close>
      show ?thesis
        using isUnitClauseIsReason [of "uClause" "uLiteral" "elements M"]
        by auto
    qed 
  } thus ?thesis
    unfolding InvariantReasonClauses_def
    by simp
qed

lemma InvariantCFalseAfterUnitPropagate:
  fixes M :: LiteralTrail and F :: Formula and M' :: LiteralTrail and uClause :: Clause and uLiteral :: Literal
  assumes "InvariantCFalse conflictFlag M C" and
  "M' = M @ [(uLiteral, False)]"
  shows "InvariantCFalse conflictFlag M' C"
proof-
  from \<open>InvariantCFalse conflictFlag M C\<close> 
  have *: "conflictFlag \<longrightarrow> clauseFalse C (elements M)"
    unfolding InvariantCFalse_def 
    .
  {
    assume "conflictFlag" 
    with \<open>M' = M @ [(uLiteral, False)]\<close> * 
    have "clauseFalse C (elements M')"
      by (simp add:clauseFalseAppendValuation)
  }
  thus ?thesis
    unfolding InvariantCFalse_def
    by simp
qed

(************************************************************************)
(*                   A P P L Y    B A C K T R A C K                     *)
(************************************************************************)
text\<open>$Backtrack$ transition rule.\<close>
lemma InvariantImpliedLiteralsAfterBacktrack:
  fixes F::Formula and M::LiteralTrail
  assumes "InvariantImpliedLiterals F M" and "InvariantUniq M" and "InvariantConsistent M" and 
  "decisions M \<noteq> []" and "formulaFalse F (elements M)"
  "M' = (prefixBeforeLastDecision M) @ [(opposite (lastDecision M), False)]"
  shows "InvariantImpliedLiterals F M'"
proof -
  have "isPrefix (prefixBeforeLastDecision M) M"
    by (simp add: isPrefixPrefixBeforeLastMarked)
  {
    fix l'::Literal
    assume "l' el (elements M')"
    let ?p = "(prefixBeforeLastDecision M)"
    let ?l = "lastDecision M"
    have "formulaEntailsLiteral (F @ val2form (decisionsTo l' M')) l'"
    proof (cases "l' el (elements ?p)")
      case True
      with \<open>isPrefix ?p M\<close>
      have "l' el (elements M)"
        using prefixElementsAreTrailElements[of "?p" "M"]
        by auto

      with \<open>InvariantImpliedLiterals F M\<close> 
      have "formulaEntailsLiteral (F @ val2form (decisionsTo l' M)) l'"
        unfolding InvariantImpliedLiterals_def
        by simp
      moreover
      from \<open>M' = ?p @ [(opposite ?l, False)]\<close> True \<open>isPrefix ?p M\<close>
      have "(decisionsTo l' M') = (decisionsTo l' M)"
        using prefixToElementToPrefixElement[of "?p" "M" "l'"]
        unfolding markedElementsTo_def
        by (auto simp add: prefixToElementAppend)
      ultimately
      show ?thesis
        by auto
    next
      case False
      with \<open>l' el (elements M')\<close> and \<open>M' = ?p @ [(opposite ?l, False)]\<close>
      have "?l = (opposite l')"
        by (auto split: if_split_asm)
      hence "l' = (opposite ?l)"
        by simp

      from \<open>InvariantUniq M\<close> and \<open>markedElements M \<noteq> []\<close>
      have "(decisionsTo ?l M) = (decisions M)"
        unfolding InvariantUniq_def
        using markedElementsToLastMarkedAreAllMarkedElements
        by auto
      moreover
      from \<open>decisions M \<noteq> []\<close> 
      have "?l el (elements M)"
        by (simp add: lastMarkedIsMarkedElement markedElementsAreElements)
      with \<open>InvariantConsistent M\<close> 
      have "\<not> (opposite ?l) el (elements M)"
        unfolding InvariantConsistent_def
        by (simp add: inconsistentCharacterization)
      with \<open>isPrefix ?p M\<close>
      have "\<not> (opposite ?l) el (elements ?p)"
        using prefixElementsAreTrailElements[of "?p" "M"]
        by auto
      with \<open>M' = ?p @ [(opposite ?l, False)]\<close> 
      have "decisionsTo (opposite ?l) M' = decisions ?p"
        using markedElementsToAppend [of "opposite ?l" "?p" "[(opposite ?l, False)]"]
        unfolding markedElementsTo_def
        by simp
      moreover
      from \<open>InvariantUniq M\<close> \<open>decisions M \<noteq> []\<close>
      have "\<not> ?l el (elements ?p)"
        unfolding InvariantUniq_def
        using lastMarkedNotInPrefixBeforeLastMarked[of "M"]
        by simp
      hence "\<not> ?l el (decisions ?p)"
        by (auto simp add: markedElementsAreElements)
      hence "(removeAll ?l (decisions ?p)) = (decisions ?p)"
        by (simp add: removeAll_id)
      hence "(removeAll ?l ((decisions ?p) @ [?l])) = (decisions ?p)"
        by simp
      from \<open>decisions M \<noteq> []\<close> False \<open>l' = (opposite ?l)\<close>
      have "(decisions ?p) @ [?l] = (decisions M)"
        using markedElementsAreElementsBeforeLastDecisionAndLastDecision[of "M"]
        by simp
      with \<open>(removeAll ?l ((decisions ?p) @ [?l])) = (decisions ?p)\<close>
      have "(decisions ?p) = (removeAll ?l (decisions M))"
        by simp
      moreover
      from \<open>formulaFalse F (elements M)\<close> \<open>InvariantImpliedLiterals F M\<close>
      have "\<not> satisfiable (F @ (val2form (decisions M)))"
        using InvariantImpliedLiteralsAndFormulaFalseThenFormulaAndDecisionsAreNotSatisfiable[of "F" "M"]
        by simp

      from \<open>decisions M \<noteq> []\<close> 
      have "?l el (decisions M)"
        unfolding lastMarked_def
        by simp
      hence "[?l] el val2form (decisions M)"
        using val2FormEl[of "?l" "(decisions M)"]
        by simp
      with \<open>\<not> satisfiable (F @ (val2form (decisions M)))\<close>
      have "formulaEntailsLiteral (removeAll [?l] (F @ val2form (decisions M))) (opposite ?l)"
        using unsatisfiableFormulaWithSingleLiteralClause[of "F @ val2form (decisions M)" "lastDecision M"]
        by auto
      ultimately
      show ?thesis
        using \<open>l' = (opposite ?l)\<close>
        using formulaEntailsLiteralRemoveAllAppend[of "[?l]" "F" "val2form (removeAll ?l (decisions M))" "opposite ?l"]
        by (auto simp add: val2FormRemoveAll)
    qed
  }
  thus ?thesis
    unfolding InvariantImpliedLiterals_def
    by auto
qed

lemma InvariantConsistentAfterBacktrack:
  fixes F::Formula and M::LiteralTrail
  assumes "InvariantUniq M" and "InvariantConsistent M" and
  "decisions M \<noteq> []" and 
  "M' = (prefixBeforeLastDecision M) @ [(opposite (lastDecision M), False)]"
  shows "InvariantConsistent M'"
proof-
  from \<open>decisions M \<noteq> []\<close> \<open>InvariantUniq M\<close>
  have "\<not> lastDecision M el elements (prefixBeforeLastDecision M)" 
    unfolding InvariantUniq_def
    using lastMarkedNotInPrefixBeforeLastMarked
    by simp
  moreover
  from \<open>InvariantConsistent M\<close> 
  have "consistent (elements (prefixBeforeLastDecision M))"
    unfolding InvariantConsistent_def
    using isPrefixPrefixBeforeLastMarked[of "M"]
    using isPrefixElements[of "prefixBeforeLastDecision M" "M"]
    using consistentPrefix[of "elements (prefixBeforeLastDecision M)" "elements M"]
    by simp
  ultimately 
  show ?thesis
    unfolding InvariantConsistent_def 
    using \<open>M' = (prefixBeforeLastDecision M) @ [(opposite (lastDecision M), False)]\<close>
    using inconsistentAppend[of "elements (prefixBeforeLastDecision M)" "[opposite (lastDecision M)]"]
    by (auto split: if_split_asm)
qed

lemma InvariantUniqAfterBacktrack:
  fixes F::Formula and M::LiteralTrail
  assumes "InvariantUniq M" and "InvariantConsistent M" and
  "decisions M \<noteq> []" and
  "M' = (prefixBeforeLastDecision M) @ [(opposite (lastDecision M), False)]"
  shows "InvariantUniq M'"
proof-
  from \<open>InvariantUniq M\<close>
  have "uniq (elements (prefixBeforeLastDecision M))"
    unfolding InvariantUniq_def
    using isPrefixPrefixBeforeLastMarked[of "M"]
    using isPrefixElements[of "prefixBeforeLastDecision M" "M"]
    using uniqListImpliesUniqPrefix
    by simp
  moreover
  from \<open>decisions M \<noteq> []\<close>
  have "lastDecision M el (elements M)"
    using lastMarkedIsMarkedElement[of "M"]
    using markedElementsAreElements[of "lastDecision M" "M"]
    by simp
  with \<open>InvariantConsistent M\<close>
  have "\<not> opposite (lastDecision M) el (elements M)"
    unfolding InvariantConsistent_def
    using inconsistentCharacterization
    by simp
  hence "\<not> opposite (lastDecision M) el (elements (prefixBeforeLastDecision M))"
    using isPrefixPrefixBeforeLastMarked[of "M"]
    using isPrefixElements[of "prefixBeforeLastDecision M" "M"]
    using prefixIsSubset[of "elements (prefixBeforeLastDecision M)" "elements M"]
    by auto
  ultimately
  show ?thesis
    using 
      \<open>M' = (prefixBeforeLastDecision M) @ [(opposite (lastDecision M), False)]\<close>
      uniqAppendElement[of "elements (prefixBeforeLastDecision M)" "opposite (lastDecision M)"]
    unfolding InvariantUniq_def
    by simp
qed

lemma InvariantVarsMAfterBacktrack:
  fixes F::Formula and M::LiteralTrail
  assumes "InvariantVarsM M F0 Vbl"
  "decisions M \<noteq> []" and
  "M' = (prefixBeforeLastDecision M) @ [(opposite (lastDecision M), False)]"
  shows "InvariantVarsM M' F0 Vbl"
proof-
  from \<open>decisions M \<noteq> []\<close>
  have "lastDecision M el (elements M)"
    using lastMarkedIsMarkedElement[of "M"]
    using markedElementsAreElements[of "lastDecision M" "M"]
    by simp
  hence "var (lastDecision M) \<in> vars (elements M)"
    using valuationContainsItsLiteralsVariable[of "lastDecision M" "elements M"]
    by simp
  moreover
  have "vars (elements (prefixBeforeLastDecision M)) \<subseteq> vars (elements M)"
    using isPrefixPrefixBeforeLastMarked[of "M"]
    using isPrefixElements[of "prefixBeforeLastDecision M" "M"]
    using varsPrefixValuation[of "elements (prefixBeforeLastDecision M)" "elements M"]
    by auto
  ultimately
  show ?thesis
    using assms
    using varsAppendValuation[of "elements (prefixBeforeLastDecision M)" "[opposite (lastDecision M)]"]
    unfolding InvariantVarsM_def
    by auto
qed


(************************************************************************)
(*                     A P P L Y    B A C K J U M P                     *)
(************************************************************************)
text\<open>$Backjump$ transition rule.\<close>

lemma InvariantImpliedLiteralsAfterBackjump:
  fixes F::Formula and M::LiteralTrail and p::LiteralTrail and bClause::Clause and bLiteral::Literal
  assumes "InvariantImpliedLiterals F M" and
  "isPrefix p M" and "formulaEntailsClause F bClause" and "isUnitClause bClause bLiteral (elements p)" and
  "M' = p @ [(bLiteral, False)]"
  shows "InvariantImpliedLiterals F M'"
proof -
  from \<open>InvariantImpliedLiterals F M\<close> \<open>isPrefix p M\<close> 
  have "InvariantImpliedLiterals F p"
    using InvariantImpliedLiteralsHoldsForPrefix [of "F" "M" "p"]
    by simp

  with assms
  show ?thesis
    using InvariantImpliedLiteralsAfterUnitPropagate [of "F" "p" "bClause" "bLiteral" "M'"]
    by simp
qed

lemma InvariantVarsMAfterBackjump:
  fixes F::Formula and M::LiteralTrail and p::LiteralTrail and bClause::Clause and bLiteral::Literal
  assumes "InvariantVarsM M F0 Vbl" and
  "isPrefix p M" and "var bLiteral \<in> vars F0 \<union> Vbl" and
  "M' = p @ [(bLiteral, False)]"
  shows "InvariantVarsM M' F0 Vbl"
proof -
  from \<open>InvariantVarsM M F0 Vbl\<close>
  have "vars (elements M) \<subseteq> vars F0 \<union> Vbl"
    unfolding InvariantVarsM_def
    . 
  moreover
  from \<open>isPrefix p M\<close>
  have "vars (elements p) \<subseteq> vars (elements M)"
    using varsPrefixValuation [of "elements p" "elements M"]
    by (simp add: isPrefixElements)
  ultimately
  have "vars (elements p) \<subseteq> vars F0 \<union> Vbl"
    by simp

  with \<open>vars (elements p) \<subseteq> vars F0 \<union> Vbl\<close> assms
  show ?thesis
    using InvariantVarsMAfterUnitPropagate[of  "p" "F0" "Vbl" "bLiteral" "M'"]
    unfolding InvariantVarsM_def
    by simp
qed

lemma InvariantConsistentAfterBackjump:
  fixes F::Formula and M::LiteralTrail and p::LiteralTrail and bClause::Clause and bLiteral::Literal
  assumes "InvariantConsistent M" and
  "isPrefix p M" and "isUnitClause bClause bLiteral (elements p)" and
  "M' = p @ [(bLiteral, False)]"
  shows "InvariantConsistent M'"
proof-
  from \<open>InvariantConsistent M\<close>
  have "consistent (elements M)"
    unfolding InvariantConsistent_def
    .
  with \<open>isPrefix p M\<close>
  have "consistent (elements p)"
    using consistentPrefix [of "elements p" "elements M"]
    by (simp add: isPrefixElements)
  
  with assms
  show ?thesis
    using InvariantConsistentAfterUnitPropagate [of "p" "bClause" "bLiteral" "M'"]
    unfolding InvariantConsistent_def
    by simp
qed

lemma InvariantUniqAfterBackjump:
  fixes F::Formula and M::LiteralTrail and p::LiteralTrail and bClause::Clause and bLiteral::Literal
  assumes "InvariantUniq M" and
  "isPrefix p M"  and "isUnitClause bClause bLiteral (elements p)" and
  "M' = p @ [(bLiteral, False)]" 
  shows "InvariantUniq M'"
proof -
  from \<open>InvariantUniq M\<close>
  have "uniq (elements M)"
    unfolding InvariantUniq_def
    .
  with \<open>isPrefix p M\<close>
  have "uniq (elements p)"
    using uniqElementsTrailImpliesUniqElementsPrefix [of "p" "M"]
    by simp
  with assms
  show ?thesis
    using InvariantUniqAfterUnitPropagate[of "p" "bClause" "bLiteral" "M'"]
    unfolding InvariantUniq_def
    by simp
qed


lemma InvariantReasonClausesAfterBackjump:
  fixes F::Formula and M::LiteralTrail and p::LiteralTrail and bClause::Clause and bLiteral::Literal
  assumes "InvariantReasonClauses F M" and "InvariantUniq M"  and
  "isPrefix p M"  and "isUnitClause bClause bLiteral (elements p)" and "formulaEntailsClause F bClause" and
  "M' = p @ [(bLiteral, False)]"
  shows "InvariantReasonClauses F M'"
proof -
  from \<open>InvariantReasonClauses F M\<close> \<open>InvariantUniq M\<close> \<open>isPrefix p M\<close>
  have "InvariantReasonClauses F p"
    by (rule InvariantReasonClausesHoldsForPrefix)
  with assms
  show ?thesis
    using InvariantReasonClausesAfterUnitPropagate [of "F" "p" "bClause" "bLiteral" "M'"]
    by simp
qed

(************************************************************************)
(*                       A P P L Y    L E A R N                         *)
(************************************************************************)
text\<open>$Learn$ transition rule.\<close>

lemma InvariantImpliedLiteralsAfterLearn: 
  fixes F :: Formula and F' :: Formula and M :: LiteralTrail and C :: Clause
  assumes "InvariantImpliedLiterals F M" and
  "F' = F @ [C]"
  shows "InvariantImpliedLiterals F' M"
proof -
  from \<open>InvariantImpliedLiterals F M\<close> 
  have *: "\<forall> l. l el (elements M) \<longrightarrow> formulaEntailsLiteral (F @ val2form (decisionsTo l M)) l"
    unfolding InvariantImpliedLiterals_def
    .
  {
    fix literal :: Literal
    assume "literal el (elements M)"
    with * 
    have "formulaEntailsLiteral (F @ val2form (decisionsTo literal M)) literal"
      by simp
    hence "formulaEntailsLiteral (F @ [C] @ val2form (decisionsTo literal M)) literal"
    proof-
      have "\<forall> clause::Clause. clause el (F @ val2form (decisionsTo literal M)) \<longrightarrow> clause el (F @ [C] @ val2form (decisionsTo literal M))"
      proof-
        {
          fix clause :: Clause
          have "clause el (F @ val2form (decisionsTo literal M)) \<longrightarrow> clause el (F @ [C] @ val2form (decisionsTo literal M))"
          proof
            assume "clause el (F @ val2form (decisionsTo literal M))"
            thus "clause el (F @ [C] @ val2form (decisionsTo literal M))"
              by auto
          qed
        } thus ?thesis
          by auto
      qed
      with \<open>formulaEntailsLiteral (F @ val2form (decisionsTo literal M)) literal\<close>
      show ?thesis
        by (rule formulaEntailsLiteralSubset)
    qed
  }
  thus ?thesis
    unfolding InvariantImpliedLiterals_def
    using \<open>F' = F @ [C]\<close>
    by auto
qed

lemma InvariantReasonClausesAfterLearn:
  fixes F :: Formula and F' :: Formula and M :: LiteralTrail and C :: Clause
  assumes "InvariantReasonClauses F M" and
  "formulaEntailsClause F C" and
  "F' = F @ [C]"
  shows "InvariantReasonClauses F' M"
proof -
  {
    fix literal :: Literal
    assume "literal el elements M \<and> \<not> literal el decisions M"
    with \<open>InvariantReasonClauses F M\<close> obtain clause::Clause
      where "formulaEntailsClause F clause" "isReason clause literal (elements M)"
      unfolding InvariantReasonClauses_def
      by auto
    from \<open>formulaEntailsClause F clause\<close> \<open>F' = F @ [C]\<close>
    have "formulaEntailsClause F' clause"
      by (simp add:formulaEntailsClauseAppend)
    with \<open>isReason clause literal (elements M)\<close>
    have "\<exists> clause. formulaEntailsClause F' clause \<and> isReason clause literal (elements M)"
      by auto
  } thus ?thesis
    unfolding InvariantReasonClauses_def
    by simp
qed

lemma InvariantVarsFAfterLearn:
  fixes F0 :: Formula and F :: Formula and F' :: Formula and C :: Clause
  assumes "InvariantVarsF F F0 Vbl" and 
  "vars C \<subseteq> (vars F0) \<union> Vbl" and
  "F' = F @ [C]"
  shows "InvariantVarsF F' F0 Vbl"
using assms
using varsAppendFormulae[of "F" "[C]"]
unfolding InvariantVarsF_def
by auto
  

lemma InvariantEquivalentAfterLearn: 
  fixes F0 :: Formula and F :: Formula and F' :: Formula and C :: Clause
  assumes "InvariantEquivalent F0 F" and 
  "formulaEntailsClause F C" and
  "F' = F @ [C]"
  shows "InvariantEquivalent F0 F'"
proof-
  from \<open>InvariantEquivalent F0 F\<close>
  have "equivalentFormulae F0 F"
    unfolding InvariantEquivalent_def
    .
  with \<open>formulaEntailsClause F C\<close> \<open>F' = F @ [C]\<close>
  have "equivalentFormulae F0 (F @ [C])"
    using extendEquivalentFormulaWithEntailedClause [of "F0" "F" "C"]
    by simp
  thus ?thesis
    unfolding InvariantEquivalent_def
    using \<open>F' = F @ [C]\<close>
    by simp
qed

lemma InvariantCEntailedAfterLearn:
  fixes F0 :: Formula and F :: Formula and F' :: Formula and C :: Clause
  assumes "InvariantCEntailed conflictFlag F C" and
  "F' = F @ [C]"
  shows "InvariantCEntailed conflictFlag F' C"
using assms
unfolding InvariantCEntailed_def
by (auto simp add:formulaEntailsClauseAppend)

(************************************************************************)
(*                     A P P L Y    E X P L A I N                       *)
(************************************************************************)
text\<open>$Explain$ transition rule.\<close>

lemma InvariantCFalseAfterExplain: 
  fixes conflictFlag::bool and M::LiteralTrail and C::Clause and literal :: Literal
  assumes "InvariantCFalse conflictFlag M C" and
  "opposite literal el C" and "isReason reason literal (elements M)" and
  "C' = resolve C reason (opposite literal)"
  shows "InvariantCFalse conflictFlag M C'"
unfolding InvariantCFalse_def
proof
  assume "conflictFlag"
  with \<open>InvariantCFalse conflictFlag M C\<close>
  have "clauseFalse C (elements M)"
    unfolding InvariantCFalse_def
    by simp
  hence "clauseFalse (removeAll (opposite literal) C) (elements M)"
    by (simp add: clauseFalseIffAllLiteralsAreFalse)
  moreover
  from \<open>isReason reason literal (elements M)\<close>
  have "clauseFalse (removeAll literal reason) (elements M)"
    unfolding isReason_def
    by simp
  ultimately 
  show "clauseFalse C' (elements M)"
    using \<open>C' = resolve C reason (opposite literal)\<close>
    resolveFalseClauses [of "opposite literal" "C" "elements M" "reason"]
    by simp
qed

lemma InvariantCEntailedAfterExplain: 
  fixes conflictFlag::bool and M::LiteralTrail and C::Clause and literal :: Literal and reason :: Clause
  assumes "InvariantCEntailed conflictFlag F C" and
  "formulaEntailsClause F reason" and "C' = (resolve C reason (opposite l))"
  shows "InvariantCEntailed conflictFlag F C'"
unfolding InvariantCEntailed_def
proof
  assume "conflictFlag"
  with \<open>InvariantCEntailed conflictFlag F C\<close>
  have "formulaEntailsClause F C"
    unfolding InvariantCEntailed_def
    by simp
  with \<open>formulaEntailsClause F reason\<close>
  show "formulaEntailsClause F C'"
    using \<open>C' = (resolve C reason (opposite l))\<close>
    by (simp add:formulaEntailsResolvent)
qed


(************************************************************************)
(*                     A P P L Y    C O N F L I C T                     *)
(************************************************************************)
text\<open>$Conflict$ transition rule.\<close>

lemma invariantCFalseAfterConflict:
  fixes conflictFlag::bool and conflictFlag'::bool and M::LiteralTrail and F :: Formula and clause :: Clause and C' :: Clause
  assumes "conflictFlag = False" and
  "formulaFalse F (elements M)" and "clause el F" "clauseFalse clause (elements M)" and
  "C' = clause" and "conflictFlag' = True"
  shows "InvariantCFalse conflictFlag' M C'"
unfolding InvariantCFalse_def
proof
  from \<open>conflictFlag' = True\<close>
  show "clauseFalse C' (elements M)"
    using \<open>clauseFalse clause (elements M)\<close> \<open>C' = clause\<close>
    by simp
qed
  
lemma invariantCEntailedAfterConflict:
  fixes conflictFlag::bool and conflictFlag'::bool and M::LiteralTrail and F :: Formula and clause :: Clause and C' :: Clause
  assumes "conflictFlag = False" and
  "formulaFalse F (elements M)" and "clause el F" and "clauseFalse clause (elements M)" and
  "C' = clause" and "conflictFlag' = True"
  shows "InvariantCEntailed conflictFlag' F C'"
unfolding InvariantCEntailed_def
proof
  from \<open>conflictFlag' = True\<close>
  show "formulaEntailsClause F C'"
    using \<open>clause el F\<close> \<open>C' = clause\<close>
    by (simp add:formulaEntailsItsClauses)
qed


(************************************************************************)
(*                   U N S A T     R E P O R T                          *)
(************************************************************************)
text\<open>UNSAT report\<close>

lemma unsatReport: 
  fixes F :: Formula and M :: LiteralTrail and F0 :: Formula
  assumes "InvariantImpliedLiterals F M" and "InvariantEquivalent F0 F" and
  "decisions M = []" and "formulaFalse F (elements M)"
  shows "\<not> satisfiable F0"
proof-
  have "formulaEntailsValuation F (elements M)"
  proof-
    {
      fix literal::Literal
      assume "literal el (elements M)"
      from \<open>decisions M = []\<close>
      have "decisionsTo literal M = []"
        by (simp add:markedElementsEmptyImpliesMarkedElementsToEmpty)
      with \<open>literal el (elements M)\<close> \<open>InvariantImpliedLiterals F M\<close>
      have "formulaEntailsLiteral F literal"
        unfolding InvariantImpliedLiterals_def
        by auto
    }
    thus ?thesis
      unfolding formulaEntailsValuation_def
      by simp
  qed
  with \<open>formulaFalse F (elements M)\<close>
  have "\<not> satisfiable F"
    by (simp add:formulaFalseInEntailedValuationIsUnsatisfiable)
  with \<open>InvariantEquivalent F0 F\<close>
  show ?thesis
    unfolding InvariantEquivalent_def
    by (simp add:satisfiableEquivalent)
qed

lemma unsatReportExtensiveExplain:
  fixes F :: Formula and M :: LiteralTrail and F0 :: Formula and C :: Clause and conflictFlag :: bool
  assumes "InvariantEquivalent F0 F" and "InvariantCEntailed conflictFlag F C" and
  "conflictFlag" and "C = []"
  shows "\<not> satisfiable F0"
proof-
  from \<open>conflictFlag\<close> \<open>InvariantCEntailed conflictFlag F C\<close>
  have "formulaEntailsClause F C"
    unfolding InvariantCEntailed_def
    by simp
  with \<open>C=[]\<close>
  have "\<not> satisfiable F"
    by (simp add:formulaUnsatIffImpliesEmptyClause)
  with \<open>InvariantEquivalent F0 F\<close>
  show ?thesis
    unfolding InvariantEquivalent_def
    by (simp add:satisfiableEquivalent)
qed

(************************************************************************)
(*                       S A T     R E P O R T                          *)
(************************************************************************)
text\<open>SAT Report\<close>

lemma satReport:
  fixes F0 :: Formula and F :: Formula and M::LiteralTrail
  assumes "vars F0 \<subseteq> Vbl" and "InvariantVarsF F F0 Vbl" and "InvariantConsistent M" and "InvariantEquivalent F0 F" and
  "\<not> formulaFalse F (elements M)" and "vars (elements M) \<supseteq> Vbl"
  shows "model (elements M) F0"
proof-
  from \<open>InvariantConsistent M\<close>
  have "consistent (elements M)"
    unfolding InvariantConsistent_def
    .
  moreover
  from \<open>InvariantVarsF F F0 Vbl\<close> 
  have "vars F \<subseteq> vars F0 \<union> Vbl"
    unfolding InvariantVarsF_def
    .
  with \<open>vars F0 \<subseteq> Vbl\<close> 
  have "vars F \<subseteq> Vbl"
    by auto
  with \<open>vars (elements M) \<supseteq> Vbl\<close>
  have "vars F \<subseteq> vars (elements M)"
    by simp
  hence "formulaTrue F (elements M) \<or> formulaFalse F (elements M)"
    by (simp add:totalValuationForFormulaDefinesItsValue)
  with \<open>\<not> formulaFalse F (elements M)\<close>
  have "formulaTrue F (elements M)"
    by simp
  ultimately
  have "model (elements M) F"
    by simp
  with \<open>InvariantEquivalent F0 F\<close>
  show ?thesis
    unfolding InvariantEquivalent_def
    unfolding equivalentFormulae_def
    by auto
qed


(******************************************************************************)
subsection\<open>Different characterizations of backjumping\<close>
(******************************************************************************)
text\<open>In this section, different characterization of applicability of
backjumping will be given.\<close>

text\<open>The clause satisfies the @{term "Unique Implication Point (UIP)"} condition
  if the level of all its literals is stricly lower then the level of its last asserted literal\<close>
definition
"isUIP l c M ==
  isLastAssertedLiteral (opposite l) (oppositeLiteralList c)(elements M)  \<and> 
  (\<forall> l'. l' el c \<and> l' \<noteq> l \<longrightarrow> elementLevel (opposite l') M < elementLevel (opposite l) M)"

text\<open>@{term "Backjump level"} is a nonegative integer such that it is stricly 
  lower than the level of the last asserted literal of a clause, and greater or 
  equal then levels of all its other literals.\<close>
definition
"isBackjumpLevel level l c M == 
  isLastAssertedLiteral (opposite l) (oppositeLiteralList c)(elements M)  \<and> 
  0 \<le> level \<and> level < elementLevel (opposite l) M \<and>
  (\<forall> l'. l' el c \<and> l' \<noteq> l \<longrightarrow> elementLevel (opposite l') M \<le> level)"

lemma lastAssertedLiteralHasHighestElementLevel: 
  fixes literal :: Literal and clause :: Clause and M :: LiteralTrail
  assumes "isLastAssertedLiteral literal clause (elements M)" and "uniq (elements M)"
  shows "\<forall> l'. l' el clause \<and> l' el elements M \<longrightarrow> elementLevel l' M <= elementLevel literal M"
proof -
  {
    fix l' :: Literal
    assume "l' el clause" "l' el elements M"
    hence "elementLevel l' M <= elementLevel literal M"
    proof (cases "l' = literal")
      case True
      thus ?thesis
        by simp
    next
      case False
      from \<open>isLastAssertedLiteral literal clause (elements M)\<close> 
      have "literalTrue literal (elements M)" 
        "\<forall> l. l el clause \<and> l \<noteq> literal \<longrightarrow> \<not>  precedes literal l (elements M)"
        by (auto simp add:isLastAssertedLiteral_def)
      with \<open>l' el clause\<close> False 
      have "\<not> precedes literal l' (elements M)"
        by simp
      with False \<open>l' el (elements M)\<close> \<open>literalTrue literal (elements M)\<close>
      have "precedes l' literal (elements M)"
        using precedesTotalOrder [of "l'"  "elements M" "literal"]
        by simp
      with \<open>uniq (elements M)\<close>
      show ?thesis
        using elementLevelPrecedesLeq [of "l'" "literal" "M"]
        by auto
    qed
  }
  thus ?thesis 
    by simp
qed

text\<open>When backjump clause contains only a single literal, then the backjump level is 0.\<close>
(* additional assumption: (elementLevel l M) > 0 *)
lemma backjumpLevelZero:
  fixes M :: LiteralTrail and C :: Clause and l :: Literal
  assumes 
  "isLastAssertedLiteral (opposite l) (oppositeLiteralList C) (elements M)" and
  "elementLevel (opposite l) M > 0" and
  "set C = {l}"
  shows
  "isBackjumpLevel 0 l C M"
proof-
  have "\<forall> l'. l' el C \<and> l' \<noteq> l \<longrightarrow> elementLevel (opposite l') M \<le> 0"
  proof-
    {
      fix l'::Literal
      assume "l' el C \<and> l' \<noteq> l"
      hence "False"
        using \<open>set C = {l}\<close>
        by auto
    } thus ?thesis
      by auto
  qed
  with \<open>elementLevel (opposite l) M > 0\<close>
    \<open>isLastAssertedLiteral (opposite l) (oppositeLiteralList C) (elements M)\<close>
  show ?thesis
    unfolding isBackjumpLevel_def
    by auto
qed

text\<open>When backjump clause contains more than one literal, then the level of the 
  second last asserted literal can be taken as a backjump level.\<close>
lemma backjumpLevelLastLast:
  fixes M :: LiteralTrail and C :: Clause and l :: Literal
  assumes 
  "isUIP l C M" and
  "uniq (elements M)" and
  "clauseFalse C (elements M)" and
  "isLastAssertedLiteral (opposite ll) (removeAll (opposite l) (oppositeLiteralList C)) (elements M)"
  shows
  "isBackjumpLevel (elementLevel (opposite ll) M) l C M"
proof-
  from \<open>isUIP l C M\<close> 
  have "isLastAssertedLiteral (opposite l) (oppositeLiteralList C) (elements M)"
    unfolding isUIP_def
    by simp

  from \<open>isLastAssertedLiteral (opposite ll) (removeAll (opposite l) (oppositeLiteralList C)) (elements M)\<close>
  have "literalTrue (opposite ll) (elements M)" "(opposite ll) el (removeAll (opposite l) (oppositeLiteralList C))"
    unfolding isLastAssertedLiteral_def
    by auto

  have "\<forall> l'. l' el (oppositeLiteralList C) \<longrightarrow> literalTrue l' (elements M)"
  proof-
    {
      fix l'::Literal
      assume "l' el oppositeLiteralList C"
      hence "opposite l' el C"
        using literalElListIffOppositeLiteralElOppositeLiteralList[of "opposite l'" "C"]
        by simp
      with \<open>clauseFalse C (elements M)\<close>
      have "literalTrue l' (elements M)"
        by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
    }
    thus ?thesis
      by simp
  qed

  have "\<forall> l'. l' el C \<and> l' \<noteq> l  \<longrightarrow> 
    elementLevel (opposite l') M <= elementLevel (opposite ll) M"
  proof-
    {
      fix l' :: Literal
      assume "l' el C \<and> l' \<noteq> l"
      hence "(opposite l') el (oppositeLiteralList C)" "opposite l' \<noteq> opposite l"
        using literalElListIffOppositeLiteralElOppositeLiteralList
        by auto
      hence "opposite l' el (removeAll (opposite l) (oppositeLiteralList C))"
        by simp
      
      from \<open>opposite l' el (oppositeLiteralList C)\<close>
        \<open>\<forall> l'. l' el (oppositeLiteralList C) \<longrightarrow> literalTrue l' (elements M)\<close>
      have "literalTrue (opposite l') (elements M)"
        by simp

      with \<open>opposite l' el (removeAll (opposite l) (oppositeLiteralList C))\<close> 
        \<open>isLastAssertedLiteral (opposite ll) (removeAll (opposite l) (oppositeLiteralList C)) (elements M)\<close>
        \<open>uniq (elements M)\<close>
      have "elementLevel (opposite l') M <= elementLevel (opposite ll) M"
        using lastAssertedLiteralHasHighestElementLevel[of "opposite ll" "removeAll (opposite l) (oppositeLiteralList C)" "M"]
        by auto
    }
    thus ?thesis
      by simp
  qed
  moreover
  from \<open>literalTrue (opposite ll) (elements M)\<close>
  have "elementLevel (opposite ll) M \<ge> 0"
    by simp
  moreover 
  from \<open>(opposite ll) el (removeAll (opposite l) (oppositeLiteralList C))\<close>
  have "ll el C" and "ll \<noteq> l"
    using literalElListIffOppositeLiteralElOppositeLiteralList[of "ll" "C"]
    by auto
  from \<open>isUIP l C M\<close> 
  have "\<forall> l'. l' el C \<and> l' \<noteq> l \<longrightarrow> elementLevel (opposite l') M < elementLevel (opposite l) M"
    unfolding isUIP_def
    by simp
  with \<open>ll el C\<close> \<open>ll \<noteq> l\<close>
  have "elementLevel (opposite ll) M < elementLevel (opposite l) M"
    by simp
  ultimately
  show ?thesis
    using \<open>isLastAssertedLiteral (opposite l) (oppositeLiteralList C) (elements M)\<close>
    unfolding isBackjumpLevel_def
    by simp
qed

text\<open>if UIP is reached then there exists correct backjump level.\<close>
(* additional assumption: (elementLevel l M) > 0 *)
lemma isUIPExistsBackjumpLevel:
  fixes M :: LiteralTrail and c :: Clause and l :: Literal
  assumes 
  "clauseFalse c (elements M)" and
  "isUIP l c M" and
  "uniq (elements M)" and
  "elementLevel (opposite l) M > 0"
  shows
  "\<exists> level. (isBackjumpLevel level l c M)"
proof-
  from \<open>isUIP l c M\<close>
  have "isLastAssertedLiteral (opposite l) (oppositeLiteralList c) (elements M)"
    unfolding isUIP_def
    by simp
  show ?thesis
  proof (cases "set c = {l}")
    case True
    with \<open>elementLevel (opposite l) M > 0\<close> \<open>isLastAssertedLiteral (opposite l) (oppositeLiteralList c) (elements M)\<close>
    have "isBackjumpLevel 0 l c M"
      using backjumpLevelZero[of "l" "c" "M"]
      by auto
    thus ?thesis
      by auto
  next
    case False
    have "\<exists> literal. isLastAssertedLiteral literal (removeAll (opposite l) (oppositeLiteralList c)) (elements M)"
    proof-
      let ?ll = "getLastAssertedLiteral (oppositeLiteralList (removeAll l c)) (elements M)"
      
      from \<open>clauseFalse c (elements M)\<close>
      have "clauseFalse (removeAll l c) (elements M)"
        by (simp add:clauseFalseRemove)
      moreover
      have "removeAll l c \<noteq> []"
      proof-
        have "(set c) \<subseteq> {l} \<union> set (removeAll l c)"
          by auto
        
        from \<open>isLastAssertedLiteral (opposite l) (oppositeLiteralList c) (elements M)\<close> 
        have "(opposite l) el oppositeLiteralList c"
          unfolding isLastAssertedLiteral_def
          by simp
        hence "l el c"
          using literalElListIffOppositeLiteralElOppositeLiteralList[of "l" "c"]
          by simp
        hence "l \<in> set c"
          by simp
        {
          assume "\<not> ?thesis"
          hence "set (removeAll l c) = {}"
            by simp
          with \<open>(set c) \<subseteq> {l} \<union> set (removeAll l c)\<close>
          have "set c \<subseteq> {l}"
            by simp
          with \<open>l \<in> set c\<close>
          have "set c = {l}"
            by auto
          with False
          have "False"
            by simp
        }
        thus ?thesis
          by auto
      qed
      ultimately
      have "isLastAssertedLiteral ?ll (oppositeLiteralList (removeAll l c)) (elements M)"
        using \<open>uniq (elements M)\<close>
        using getLastAssertedLiteralCharacterization [of "removeAll l c" "elements M"] 
        by simp
      hence "isLastAssertedLiteral ?ll (removeAll (opposite l) (oppositeLiteralList c)) (elements M)"
        using oppositeLiteralListRemove[of "l" "c"]
        by simp
      thus ?thesis
        by auto
    qed
    then obtain ll::Literal where "isLastAssertedLiteral ll (removeAll (opposite l) (oppositeLiteralList c)) (elements M)"
      by auto
  
    with \<open>uniq (elements M)\<close> \<open>clauseFalse c (elements M)\<close> \<open>isUIP l c M\<close> 
    have "isBackjumpLevel (elementLevel ll M) l c M"
      using backjumpLevelLastLast[of "l" "c" "M" "opposite ll"]
      by auto
    thus ?thesis
      by auto
  qed
qed

text\<open>Backjump level condition ensures that the backjump clause is
unit in the prefix to backjump level.\<close>
lemma isBackjumpLevelEnsuresIsUnitInPrefix: 
  fixes M :: LiteralTrail and conflictFlag :: bool and c :: Clause and l :: Literal
  assumes "consistent (elements M)" and "uniq (elements M)" and
  "clauseFalse c (elements M)" and "isBackjumpLevel level l c M"
  shows "isUnitClause c l (elements (prefixToLevel level M))"
proof -
  from \<open>isBackjumpLevel level l c M\<close> 
  have "isLastAssertedLiteral (opposite l) (oppositeLiteralList c)(elements M)"
    "0 \<le> level"   "level < elementLevel (opposite l) M" and
    *: "\<forall> l'. l' el c \<and> l' \<noteq> l \<longrightarrow> elementLevel (opposite l') M \<le> level"
    unfolding isBackjumpLevel_def
    by auto

  from \<open>isLastAssertedLiteral (opposite l)(oppositeLiteralList c) (elements M)\<close>
  have "l el c" "literalTrue (opposite l) (elements M)"
    using isLastAssertedCharacterization [of "opposite l" "c" "elements M"]
    by auto

  have "\<not> literalFalse l (elements (prefixToLevel level M))"
    using \<open>level < elementLevel (opposite l) M\<close> \<open>0 <= level\<close> \<open>uniq (elements M)\<close>
    by (simp add: literalNotInEarlierLevelsThanItsLevel)
  moreover
  have "\<not> literalTrue l (elements (prefixToLevel level M))" 
  proof -
    from \<open>consistent (elements M)\<close> \<open>literalTrue (opposite l) (elements M)\<close>
    have "\<not> literalFalse (opposite l) (elements M)"
      by (auto simp add:inconsistentCharacterization)
    thus ?thesis
      using isPrefixPrefixToLevel[of "level" "M"]
        prefixElementsAreTrailElements[of "prefixToLevel level M" "M"]
      unfolding prefixToLevel_def
      by auto
  qed
  moreover
  have "\<forall> l'. l' el c \<and> l' \<noteq> l \<longrightarrow> literalFalse l' (elements (prefixToLevel level M))"
  proof -
  {
    fix l' :: Literal
    assume "l' el c" "l' \<noteq> l"

    from \<open>l' el c\<close> \<open>clauseFalse c (elements M)\<close>
    have "literalFalse l' (elements M)"
      by (simp add:clauseFalseIffAllLiteralsAreFalse)

    have "literalFalse l' (elements (prefixToLevel level M))"
    proof -
      from \<open>l' el c\<close> \<open>l' \<noteq> l\<close>
      have "elementLevel (opposite l') M <= level"
        using *
        by auto

      thus ?thesis
        using \<open>literalFalse l' (elements M)\<close> 
          \<open>0 <= level\<close>
          elementLevelLtLevelImpliesMemberPrefixToLevel[of "opposite l'" "M" "level"]
        by simp
    qed
  } thus ?thesis
    by auto
  qed
  ultimately
  show ?thesis
    using \<open>l el c\<close>
    unfolding isUnitClause_def
    by simp
qed

text\<open>Backjump level is minimal if there is no smaller level which
       satisfies the backjump level condition. The following definition gives
       operative characterization of this notion.\<close>
definition 
"isMinimalBackjumpLevel level l c M ==
     isBackjumpLevel level l c M \<and> 
     (if set c \<noteq> {l} then 
         (\<exists> ll. ll el c \<and> elementLevel (opposite ll) M = level) 
      else 
         level = 0
     )"

lemma isMinimalBackjumpLevelCharacterization:
assumes
"isUIP l c M"
"clauseFalse c (elements M)"
"uniq (elements M)"
shows
"isMinimalBackjumpLevel level l c M = 
  (isBackjumpLevel level l c M \<and> 
   (\<forall> level'. level' < level \<longrightarrow> \<not> isBackjumpLevel level' l c M))" (is "?lhs = ?rhs")
proof
  assume "?lhs"
  show "?rhs"
  proof (cases "set c = {l}")
    case True
    thus ?thesis
      using \<open>?lhs\<close>
      unfolding isMinimalBackjumpLevel_def
      by auto
  next
    case False
    with \<open>?lhs\<close>
    obtain ll 
      where "ll el c" "elementLevel (opposite ll) M = level" "isBackjumpLevel level l c M"
      unfolding isMinimalBackjumpLevel_def
      by auto
    have "l \<noteq> ll"
      using \<open>isMinimalBackjumpLevel level l c M\<close>
      using \<open>elementLevel (opposite ll) M = level\<close>
      unfolding isMinimalBackjumpLevel_def
      unfolding isBackjumpLevel_def
      by auto
    
    show ?thesis
      using \<open>isBackjumpLevel level l c M\<close>
      using \<open>elementLevel (opposite ll) M = level\<close>
      using \<open>ll el c\<close> \<open>l \<noteq> ll\<close> 
      unfolding isBackjumpLevel_def
      by force
  qed
next
  assume "?rhs"
  show "?lhs"
  proof (cases "set c = {l}")
    case True
    thus ?thesis
      using \<open>?rhs\<close>
      using backjumpLevelZero[of "l" "c" "M"]
      unfolding isMinimalBackjumpLevel_def
      unfolding isBackjumpLevel_def
      by auto
  next
    case False
    from \<open>?rhs\<close>
    have "l el c"
      unfolding isBackjumpLevel_def
      using literalElListIffOppositeLiteralElOppositeLiteralList[of "l" "c"]
      unfolding isLastAssertedLiteral_def
      by simp

    let ?oll = "getLastAssertedLiteral (removeAll (opposite l) (oppositeLiteralList c)) (elements M)"

    have "clauseFalse (removeAll l c) (elements M)"
      using \<open>clauseFalse c (elements M)\<close>
      by (simp add: clauseFalseIffAllLiteralsAreFalse)
    moreover
    have "removeAll l c \<noteq> []"
    proof-
      {
        assume "\<not> ?thesis"
        hence "set (removeAll l c) = {}"
          by simp
        hence "set c \<subseteq> {l}"
          by simp
        hence False
          using \<open>set c \<noteq> {l}\<close>
          using \<open>l el c\<close>
          by auto
      } thus ?thesis
        by auto
    qed
    ultimately
    have "isLastAssertedLiteral ?oll (removeAll (opposite l) (oppositeLiteralList c)) (elements M)"
      using \<open>uniq (elements M)\<close>
      using getLastAssertedLiteralCharacterization[of "removeAll l c" "elements M"]
      using oppositeLiteralListRemove[of "l" "c"]
      by simp
    hence  "isBackjumpLevel  (elementLevel ?oll M) l c M"
      using assms
      using backjumpLevelLastLast[of "l" "c" "M" "opposite ?oll"]
      by auto

    have "?oll el (removeAll (opposite l) (oppositeLiteralList c))"
      using \<open>isLastAssertedLiteral ?oll (removeAll (opposite l) (oppositeLiteralList c)) (elements M)\<close>
      unfolding isLastAssertedLiteral_def
      by simp
    hence "?oll el (oppositeLiteralList c)" "?oll \<noteq> opposite l"
      by auto
    hence "opposite ?oll el c"
      using literalElListIffOppositeLiteralElOppositeLiteralList[of "?oll" "oppositeLiteralList c"]
      by simp
    from \<open>?oll \<noteq> opposite l\<close>
    have "opposite ?oll \<noteq> l"
      using oppositeSymmetry[of "?oll" "l"]
      by simp

    have "elementLevel ?oll M \<ge> level"
    proof-
      {
        assume "elementLevel ?oll M < level"
        hence "\<not> isBackjumpLevel  (elementLevel ?oll M) l c M"
          using \<open>?rhs\<close>
          by simp
        with \<open>isBackjumpLevel  (elementLevel ?oll M) l c M\<close>
        have False
          by simp
      } thus ?thesis
        by force
    qed
    moreover
    from \<open>?rhs\<close>
    have "elementLevel ?oll M \<le> level"
      using \<open>opposite ?oll el c\<close>
      using \<open>opposite ?oll \<noteq> l\<close>
      unfolding isBackjumpLevel_def
      by auto
    ultimately
    have "elementLevel ?oll M = level"
      by simp
    show ?thesis
      using \<open>opposite ?oll el c\<close>
      using \<open>elementLevel ?oll M = level\<close>
      using \<open>?rhs\<close>
      using \<open>set c \<noteq> {l}\<close>
      unfolding isMinimalBackjumpLevel_def
      by (auto simp del: set_removeAll)
  qed
qed

lemma isMinimalBackjumpLevelEnsuresIsNotUnitBeforePrefix:
  fixes M :: LiteralTrail and conflictFlag :: bool and c :: Clause and l :: Literal
  assumes "consistent (elements M)" and "uniq (elements M)" and 
  "clauseFalse c (elements M)" "isMinimalBackjumpLevel level l c M" and
  "level' < level"
  shows "\<not> (\<exists> l'. isUnitClause c l' (elements (prefixToLevel level' M)))"
proof-
  from \<open>isMinimalBackjumpLevel level l c M\<close>
  have "isUnitClause c l (elements (prefixToLevel level M))"
    using assms
    using isBackjumpLevelEnsuresIsUnitInPrefix[of "M" "c" "level" "l"]
    unfolding isMinimalBackjumpLevel_def
    by simp
  hence "\<not> literalFalse l (elements (prefixToLevel level M))"
    unfolding isUnitClause_def
    by auto
  hence "\<not> literalFalse  l (elements M) \<or> elementLevel (opposite l) M > level"
    using elementLevelLtLevelImpliesMemberPrefixToLevel[of "l" "M" "level"]
    using elementLevelLtLevelImpliesMemberPrefixToLevel[of "opposite l" "M" "level"]
    by (force)+

  have "\<not> literalFalse l (elements (prefixToLevel level' M))"
  proof (cases "\<not> literalFalse l (elements M)")
    case True
    thus ?thesis
      using prefixIsSubset[of "elements (prefixToLevel level' M)" "elements M"]
      using isPrefixPrefixToLevel[of "level'" "M"]
      using isPrefixElements[of "prefixToLevel level' M" "M"]
      by auto
  next
    case False
    with \<open>\<not> literalFalse l (elements M) \<or> elementLevel (opposite l) M > level\<close>
    have "level < elementLevel (opposite l) M"
      by simp
    thus ?thesis
      using prefixToLevelElementsElementLevel[of "opposite l" "level'" "M"]
      using \<open>level' < level\<close>
      by auto
  qed

  show ?thesis
  proof (cases "set c \<noteq> {l}")
    case True
    from \<open>isMinimalBackjumpLevel level l c M\<close>
    obtain ll 
      where "ll el c" "elementLevel (opposite ll) M = level"
      using \<open>set c \<noteq> {l}\<close>
      unfolding isMinimalBackjumpLevel_def
      by auto
    hence "\<not> literalFalse ll (elements (prefixToLevel level' M))"
      using literalNotInEarlierLevelsThanItsLevel[of "level'" "opposite ll" "M"]
      using \<open>level' < level\<close>
      by simp

    have "l \<noteq> ll"
      using \<open>isMinimalBackjumpLevel level l c M\<close>
      using \<open>elementLevel (opposite ll) M = level\<close>
      unfolding isMinimalBackjumpLevel_def
      unfolding isBackjumpLevel_def
      by auto
    
    {
      assume "\<not> ?thesis"
      then obtain l'
        where "isUnitClause c l' (elements (prefixToLevel level' M))"
        by auto
      have "False"
      proof (cases "l = l'")
        case True
        thus ?thesis
          using \<open>l \<noteq> ll\<close> \<open>ll el c\<close>
          using \<open>\<not> literalFalse ll (elements (prefixToLevel level' M))\<close>
          using \<open>isUnitClause c l' (elements (prefixToLevel level' M))\<close>
          unfolding isUnitClause_def
          by auto
      next
        case False
        have "l el c"
          using \<open>isMinimalBackjumpLevel level l c M\<close>
          unfolding isMinimalBackjumpLevel_def
          unfolding isBackjumpLevel_def
          unfolding isLastAssertedLiteral_def
          using literalElListIffOppositeLiteralElOppositeLiteralList[of "l" "c"]
          by simp
        thus ?thesis
          using False
          using \<open>\<not> literalFalse l (elements (prefixToLevel level' M))\<close>
          using \<open>isUnitClause c l' (elements (prefixToLevel level' M))\<close>
          unfolding isUnitClause_def
          by auto
      qed
    } thus ?thesis
      by auto
  next
    case False
    with \<open>isMinimalBackjumpLevel level l c M\<close>
    have "level = 0"
      unfolding isMinimalBackjumpLevel_def
      by simp
    with \<open>level' < level\<close>
    show ?thesis
      by simp
  qed
qed

text\<open>If all literals in a clause are decision literals, then UIP is reached.\<close>
lemma allDecisionsThenUIP:
  fixes M :: LiteralTrail and c:: Clause
  assumes "(uniq (elements M))" and
  "\<forall> l'. l' el c \<longrightarrow> (opposite l') el (decisions M)"
  "isLastAssertedLiteral (opposite l) (oppositeLiteralList c) (elements M)"
  shows "isUIP l c M"
proof-
  from \<open>isLastAssertedLiteral (opposite l) (oppositeLiteralList c) (elements M)\<close>
  have "l el c" "(opposite l) el (elements M)"
    and *: "\<forall>l'. l' el (oppositeLiteralList c) \<and> l' \<noteq> opposite l \<longrightarrow> \<not> precedes (opposite l) l' (elements M)"
    unfolding isLastAssertedLiteral_def
    using "literalElListIffOppositeLiteralElOppositeLiteralList"
    by auto
  with \<open>\<forall> l'. l' el c \<longrightarrow> (opposite l') el (decisions M)\<close>
  have "(opposite l) el (decisions M)"
    by simp
  {
    fix l' :: Literal
    assume "l' el c" "l' \<noteq> l"
    hence "opposite l' el (oppositeLiteralList c)" and "opposite l' \<noteq> opposite l"
      using literalElListIffOppositeLiteralElOppositeLiteralList[of "l'" "c"]
      by auto
    with * 
    have "\<not> precedes (opposite l) (opposite l') (elements M)"
      by simp

    from \<open>l' el c\<close> \<open>\<forall> l. l el c \<longrightarrow> (opposite l) el (decisions M)\<close>
    have "(opposite l') el (decisions M)"
      by auto
    hence "(opposite l') el (elements M)"
      by (simp add:markedElementsAreElements)

    from \<open>(opposite l) el (elements M)\<close> \<open>(opposite l') el (elements M)\<close> \<open>l' \<noteq> l\<close> 
      \<open>\<not> precedes (opposite l) (opposite l') (elements M)\<close> 
    have "precedes (opposite l') (opposite l) (elements M)"
      using precedesTotalOrder [of "opposite l" "elements M" "opposite l'"]
      by simp
    with \<open>uniq (elements M)\<close>
    have "elementLevel (opposite l') M <= elementLevel (opposite l) M"
      by (auto simp add:elementLevelPrecedesLeq)
    moreover
    from \<open>uniq (elements M)\<close> \<open>(opposite l) el (decisions M)\<close> \<open>(opposite l') el (decisions M)\<close> \<open>l' \<noteq> l\<close>
    have "elementLevel (opposite l) M \<noteq> elementLevel (opposite l') M"
      using differentMarkedElementsHaveDifferentLevels[of "M" "opposite l" "opposite l'"]
      by simp
    ultimately
    have "elementLevel (opposite l') M < elementLevel (opposite l) M"
      by simp
  }
  thus ?thesis
    using \<open>isLastAssertedLiteral (opposite l) (oppositeLiteralList c) (elements M)\<close>
    unfolding isUIP_def
    by simp
qed

text\<open>If last asserted literal of a clause is a decision literal, then UIP is reached.\<close>
lemma lastDecisionThenUIP:
  fixes M :: LiteralTrail and c:: Clause
  assumes "(uniq (elements M))" and
  "(opposite l) el (decisions M)"
  "clauseFalse c (elements M)"
  "isLastAssertedLiteral (opposite l) (oppositeLiteralList c) (elements M)"
  shows "isUIP l c M"
proof-
  from \<open>isLastAssertedLiteral (opposite l) (oppositeLiteralList c) (elements M)\<close>
  have "l el c" "(opposite l) el (elements M)"
    and *: "\<forall>l'. l' el (oppositeLiteralList c) \<and> l' \<noteq> opposite l \<longrightarrow> \<not> precedes (opposite l) l' (elements M)"
    unfolding isLastAssertedLiteral_def
    using "literalElListIffOppositeLiteralElOppositeLiteralList"
    by auto
  {
    fix l' :: Literal
    assume "l' el c" "l' \<noteq> l"
    hence "opposite l' el (oppositeLiteralList c)" and "opposite l' \<noteq> opposite l"
      using literalElListIffOppositeLiteralElOppositeLiteralList[of "l'" "c"]
      by auto
    with * 
    have "\<not> precedes (opposite l) (opposite l') (elements M)"
      by simp

    have "(opposite l') el (elements M)"
      using \<open>l' el c\<close> \<open>clauseFalse c (elements M)\<close>
      by (simp add: clauseFalseIffAllLiteralsAreFalse)

    from \<open>(opposite l) el (elements M)\<close> \<open>(opposite l') el (elements M)\<close> \<open>l' \<noteq> l\<close> 
      \<open>\<not> precedes (opposite l) (opposite l') (elements M)\<close> 
    have "precedes (opposite l') (opposite l) (elements M)"
      using precedesTotalOrder [of "opposite l" "elements M" "opposite l'"]
      by simp

    hence "elementLevel (opposite l') M < elementLevel (opposite l) M"
      using elementLevelPrecedesMarkedElementLt[of "M" "opposite l'" "opposite l"]
      using \<open>uniq (elements M)\<close>
      using \<open>opposite l el (decisions M)\<close>
      using \<open>l' \<noteq> l\<close>
      by simp
  }
  thus ?thesis
    using \<open>isLastAssertedLiteral (opposite l) (oppositeLiteralList c) (elements M)\<close>
    unfolding SatSolverVerification.isUIP_def
    by simp
qed

text\<open>If all literals in a clause are decision literals, then there
exists a backjump level for that clause.\<close>
lemma allDecisionsThenExistsBackjumpLevel:
  fixes M :: LiteralTrail and c:: Clause
  assumes "(uniq (elements M))" and
  "\<forall> l'. l' el c \<longrightarrow> (opposite l') el (decisions M)"
  "isLastAssertedLiteral (opposite l) (oppositeLiteralList c) (elements M)"
  shows "\<exists> level. (isBackjumpLevel level l c M)"
proof-
  from assms 
  have "isUIP l c M"
    using allDecisionsThenUIP
    by simp
  moreover
  from \<open>isLastAssertedLiteral (opposite l) (oppositeLiteralList c) (elements M)\<close>
  have "l el c"
    unfolding isLastAssertedLiteral_def
    using literalElListIffOppositeLiteralElOppositeLiteralList
    by simp
  with \<open>\<forall> l'. l' el c \<longrightarrow> (opposite l') el (decisions M)\<close>
  have "(opposite l) el (decisions M)"
    by simp
  hence "elementLevel (opposite l) M > 0"
    using \<open>uniq (elements M)\<close>
      elementLevelMarkedGeq1[of "M" "opposite l"]
    by auto
  moreover
  have "clauseFalse c (elements M)"
  proof-
    {
      fix l'::Literal
      assume "l' el c"
      with \<open>\<forall> l'. l' el c \<longrightarrow> (opposite l') el (decisions M)\<close>
      have "(opposite l') el (decisions M)"
        by simp
      hence "literalFalse l' (elements M)"
        using markedElementsAreElements
        by simp
    }
    thus ?thesis
      using clauseFalseIffAllLiteralsAreFalse
      by simp
  qed
  ultimately
  show ?thesis
    using \<open>uniq (elements M)\<close>
    using isUIPExistsBackjumpLevel
    by simp
qed

text\<open>$Explain$ is applicable to each non-decision literal in a clause.\<close>
lemma explainApplicableToEachNonDecision:
  fixes F :: Formula and M :: LiteralTrail and conflictFlag :: bool and C :: Clause and literal :: Literal
  assumes "InvariantReasonClauses F M" and "InvariantCFalse conflictFlag M C" and
  "conflictFlag = True" and "opposite literal el C" and "\<not> literal el (decisions M)"
  shows "\<exists> clause. formulaEntailsClause F clause \<and> isReason clause literal (elements M)"
proof-
  from \<open>conflictFlag = True\<close> \<open>InvariantCFalse conflictFlag M C\<close>
  have "clauseFalse C (elements M)"
    unfolding InvariantCFalse_def
    by simp
  with \<open>opposite literal el C\<close>
  have "literalTrue literal (elements M)"
    by (auto simp add:clauseFalseIffAllLiteralsAreFalse)
  with \<open>\<not> literal el (decisions M)\<close> \<open>InvariantReasonClauses F M\<close>
  show ?thesis
    unfolding InvariantReasonClauses_def
    by auto
qed


(**************************************************************************)
(*                          T E R M I N A T I O N                         *)
(**************************************************************************)
subsection\<open>Termination\<close>
text\<open>In this section different ordering relations will be defined. These 
  well-founded orderings will be the basic building blocks of termination 
  orderings that will prove the termination of the SAT solving procedures\<close>
  

text\<open>First we prove a simple lemma about acyclic orderings.\<close>
lemma transIrreflexiveOrderingIsAcyclic:
  assumes "trans r" and "\<forall> x. (x, x) \<notin> r"
  shows "acyclic r"
proof (rule acyclicI)
  {
    assume "\<exists> x. (x, x) \<in> r^+"
    then obtain x where "(x, x) \<in> r^+"
      by auto
    moreover
    from \<open>trans r\<close>
    have "r^+ = r"
      by (rule trancl_id)
    ultimately
    have "(x, x) \<in> r"
      by simp
    with \<open>\<forall> x. (x, x) \<notin> r\<close>
    have False
      by simp
  }
  thus "\<forall> x. (x, x) \<notin> r^+"
    by auto
qed


 
(*-----------------------------------------------------------------------*)
subsubsection\<open>Trail ordering\<close>
(*-----------------------------------------------------------------------*)

text\<open>We define a lexicographic ordering of trails, based on the
number of literals on the different decision levels. It will be used
for transition rules that change the trail, i.e., for $Decide$,
$UnitPropagate$, $Backjump$ and $Backtrack$ transition rules.\<close>

definition
"decisionLess = {(l1::('a*bool), l2::('a*bool)). isDecision l1 \<and> \<not> isDecision l2}"
definition
"lexLess = {(M1::'a Trail, M2::'a Trail). (M2, M1) \<in> lexord decisionLess}"


text\<open>Following several lemmas will help prove that application of
some DPLL-based transition rules decreases the trail in the @{term
lexLess} ordering.\<close>

lemma lexLessAppend:
  assumes "b \<noteq> []" 
  shows "(a @ b, a) \<in> lexLess"
proof-
  from \<open>b \<noteq> []\<close>
  have "\<exists> aa list. b = aa # list"
    by (simp add: neq_Nil_conv)
  then obtain aa::"'a \<times> bool" and list :: "'a Trail"
    where "b = aa # list"
    by auto
  thus ?thesis
    unfolding lexLess_def
    unfolding lexord_def
    by simp
qed

lemma lexLessBackjump:
  assumes "p = prefixToLevel level a" and "level >= 0" and "level < currentLevel a" 
  shows "(p @ [(x, False)], a) \<in> lexLess"
proof-
  from assms
  have "\<exists> rest. prefixToLevel level a @ rest = a \<and> rest \<noteq> [] \<and> isDecision (hd rest)"
    using isProperPrefixPrefixToLevel
    by auto
  with \<open>p = prefixToLevel level a\<close> 
  obtain rest 
    where "p @ rest = a \<and> rest \<noteq> [] \<and> isDecision (hd rest)"
    by auto
  thus ?thesis
    unfolding lexLess_def
    using lexord_append_left_rightI[of "hd rest" "(x, False)" "decisionLess" "p" "tl rest" "[]"]
    unfolding decisionLess_def
    by simp
qed

lemma lexLessBacktrack:
  assumes "p = prefixBeforeLastDecision a" "decisions a \<noteq> []"
  shows "(p @ [(x, False)], a) \<in> lexLess"
using assms
using prefixBeforeLastMarkedIsPrefixBeforeLastLevel[of "a"]
using lexLessBackjump[of "p" "currentLevel a - 1" "a"]
unfolding currentLevel_def
by auto


text\<open>The following several lemmas prover that @{term lexLess} is
acyclic. This property will play an important role in building a
well-founded ordering based on @{term lexLess}.\<close>
lemma transDecisionLess:
  shows "trans decisionLess"
proof-
  {
    fix x::"('a*bool)" and y::"('a*bool)" and z::"('a*bool)"
    assume "(x, y) \<in> decisionLess" 
    hence "\<not> isDecision y"
      unfolding decisionLess_def
      by simp
    moreover 
    assume "(y, z) \<in> decisionLess"
    hence "isDecision y"
      unfolding decisionLess_def
      by simp
    ultimately
    have False
      by simp
    hence "(x, z) \<in> decisionLess"
      by simp
  }
  thus ?thesis
    unfolding trans_def
    by blast
qed


lemma translexLess: 
  shows "trans lexLess"
proof- 
  {
    fix x :: "'a Trail" and y :: "'a Trail" and z :: "'a Trail"
    assume "(x, y) \<in> lexLess" and "(y, z) \<in> lexLess"
    hence "(x, z) \<in> lexLess"
      using lexord_trans transDecisionLess
      unfolding lexLess_def
      by simp
  }
  thus ?thesis
    unfolding trans_def
    by blast
qed

lemma irreflexiveDecisionLess:
  shows "(x, x) \<notin> decisionLess"
unfolding decisionLess_def
by simp

lemma irreflexiveLexLess: 
  shows "(x, x) \<notin> lexLess"
using lexord_irreflexive[of "decisionLess" "x"] irreflexiveDecisionLess
unfolding lexLess_def
by auto

lemma acyclicLexLess:
  shows "acyclic lexLess"
proof (rule transIrreflexiveOrderingIsAcyclic)
  show "trans lexLess"
    using translexLess
    .
  show "\<forall> x. (x, x) \<notin> lexLess"
    using irreflexiveLexLess
    by auto
qed

text\<open>The @{term lexLess} ordering is not well-founded. In order to
  get a well-founded ordering, we restrict the @{term lexLess}
  ordering to cosistent and uniq trails with fixed variable set.\<close>
definition "lexLessRestricted (Vbl::Variable set) == {(M1, M2). 
  vars (elements M1) \<subseteq> Vbl \<and> consistent (elements M1) \<and> uniq (elements M1) \<and>
  vars (elements M2) \<subseteq> Vbl \<and> consistent (elements M2) \<and> uniq (elements M2) \<and>
  (M1, M2) \<in> lexLess}"

text\<open>First we show that the set of those trails is finite.\<close>
lemma finiteVarsClause:
  fixes c :: Clause
  shows "finite (vars c)"
by (induct c) auto

lemma finiteVarsFormula:
  fixes F :: Formula
  shows "finite (vars F)"
proof (induct F)
  case (Cons c F)
  thus ?case
    using finiteVarsClause[of "c"]
    by simp
qed simp

lemma finiteListDecompose:
  shows "finite {(a, b). l = a @ b}"
proof (induct l)
  case Nil
  thus ?case
    by simp
next
  case (Cons x l')
  thus ?case
  proof-
    let "?S l" = "{(a, b). l = a @ b}"
    let "?S' x l'" = "{(a', b). a' = [] \<and> b = (x # l') \<or> 
                                (\<exists> a. a' = x # a \<and> (a, b) \<in> (?S l'))}"
    have "?S (x # l') = ?S' x l'"
    proof
      show "?S (x # l') \<subseteq> ?S' x l'"
      proof
        fix k
        assume "k \<in> ?S (x # l')"
        then obtain a and b
          where "k = (a, b)" "x # l' = a @ b"
          by auto
        then obtain a' where "a' = x # a"
          by auto
        from \<open>k = (a, b)\<close> \<open>x # l' = a @ b\<close> 
        show "k \<in> ?S' x l'"
          using SimpleLevi[of "a" "b" "x" "l'"]
          by auto
      qed
    next
      show "?S' x l' \<subseteq> ?S (x # l')"
      proof
        fix k
        assume "k \<in> ?S' x l'"
        then obtain a' and b where 
          "k = (a', b)" "a' = [] \<and> b = x # l' \<or> (\<exists> a . a' = x # a \<and> (a, b) \<in> ?S l')"
          by auto
        moreover
        {
          assume "a' = []" "b = x # l'"
          with \<open>k = (a', b)\<close>
          have "k \<in> ?S (x # l')"
            by simp
        }
        moreover
        {
          assume "\<exists> a. a' = x # a \<and> (a, b) \<in> ?S l'"
          then obtain a where
            "a' = x # a \<and> (a, b) \<in> ?S l'"
            by auto
          with \<open>k = (a', b)\<close>
          have "k \<in> ?S (x # l')"
            by auto
        }
        ultimately
        show "k \<in> ?S (x # l')"
          by auto
      qed
    qed
    moreover
    have "?S' x l' = 
      {(a', b). a' = [] \<and> b = x # l'} \<union> {(a', b). \<exists> a. a' = x # a \<and> (a, b) \<in> ?S l'}"
      by auto
    moreover
    have "finite {(a', b). \<exists> a. a' = x # a \<and> (a, b) \<in> ?S l'}"
    proof-
      let ?h = "\<lambda> (a, b). (x # a, b)"
      have "{(a', b). \<exists> a. a' = x # a \<and>  (a, b) \<in> ?S l'} = ?h ` {(a, b).  l' = a @ b}"
        by auto
      thus ?thesis
        using Cons(1)
        by auto
    qed
    moreover 
    have "finite {(a', b). a' = [] \<and> b = x # l'}"
      by auto
    ultimately
    show ?thesis
      by auto
  qed
qed

lemma finiteListDecomposeSet:
  fixes L :: "'a list set"
  assumes "finite L"
  shows "finite {(a, b). \<exists> l. l \<in> L \<and> l = a @ b}"
proof-
  have "{(a, b). \<exists> l. l \<in> L \<and> l = a @ b} = (\<Union> l \<in> L. {(a, b). l = a @ b})"
    by auto
  moreover
  have "finite (\<Union> l \<in> L. {(a, b). l = a @ b})"
  proof (rule finite_UN_I)
    from \<open>finite L\<close>
    show "finite L" 
      .
  next
    fix l
    assume "l \<in> L"
    show "finite {(a, b). l = a @ b}"
      by (rule finiteListDecompose)
  qed
  ultimately
  show ?thesis
    by simp
qed

lemma finiteUniqAndConsistentTrailsWithGivenVariableSet: 
  fixes V :: "Variable set"
  assumes "finite V"
  shows "finite {(M::LiteralTrail). vars (elements M) = V \<and> uniq (elements M) \<and> consistent (elements M)}"
        (is "finite (?trails V)")
using assms
proof induct
  case empty
  thus ?case
  proof-
    have "?trails {} = {M. M = []}" (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
      proof
        fix M::LiteralTrail
        assume "M \<in> ?lhs"
        hence "M = []"
          by (induct M) auto
        thus "M \<in> ?rhs"
          by simp
      qed
    next
      show "?rhs \<subseteq> ?lhs"
      proof
        fix M::LiteralTrail
        assume "M \<in> ?rhs"
        hence "M = []"
          by simp
        thus "M \<in> ?lhs"
          by (induct M) auto
      qed
    qed
    moreover
    have "finite {M. M = []}"
      by auto
    ultimately
    show ?thesis
      by auto
  qed
next
  case (insert v V')
  thus ?case
  proof-
    let "?trails' V'" = "{(M::LiteralTrail). \<exists> M' l d M''. 
                                M = M' @ [(l, d)] @ M'' \<and>
                                M' @ M'' \<in> (?trails V') \<and>
                                l \<in> {Pos v, Neg v} \<and>
                                d \<in> {True, False}}"
    have "?trails (insert v V') = ?trails' V'"
      (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
      proof
        fix M::LiteralTrail
        assume "M \<in> ?lhs"
        hence "vars (elements M) = insert v V'" "uniq (elements M)" "consistent (elements M)"
          by auto
        hence "v \<in> vars (elements M)"
          by simp
        hence "\<exists> l. l el elements M \<and> var l = v"
          by (induct M) auto
        then obtain l where "l el elements M" "var l = v"
          by auto
        hence "\<exists> M' M'' d. M = M' @ [(l, d)] @ M''"
        proof (induct M)
          case (Cons m M1)
          thus ?case
          proof (cases "l = (element m)")
            case True
            then obtain d where "m = (l, d)"
              using eitherMarkedOrNotMarkedElement[of "m"]
              by auto
            hence "m # M1 = [] @ [(l, d)] @ M1"
              by simp
            then obtain M' M'' d where "m # M1 = M' @ [(l, d)] @ M''"
              ..
            thus ?thesis
              by auto
          next
            case False
            with \<open>l el elements (m # M1)\<close>
            have "l el elements M1"
              by simp
            with Cons(1) \<open>var l = v\<close>
            obtain M1' M'' d where "M1 = M1' @ [(l, d)] @ M''"
              by auto
            hence "m # M1 = (m # M1') @ [(l, d)] @ M''"
              by simp
            then obtain M' M'' d where "m # M1 = M' @ [(l, d)] @ M''"
              ..
            thus ?thesis
              by auto
          qed
        qed simp
        then obtain M' M'' d where "M = M' @ [(l, d)] @ M''"
          by auto
        moreover
        from \<open>var l = v\<close>
        have "l : {Pos v, Neg v}"
          by (cases l) auto
        moreover
        have *: "vars (elements (M' @ M'')) = vars (elements M') \<union> vars (elements M'')"
          using varsAppendClauses[of "elements M'" "elements M''"]
          by simp
        from \<open>M = M' @ [(l, d)] @ M''\<close> \<open>var l = v\<close>
        have **: "vars (elements M) = (vars (elements M')) \<union> {v} \<union> (vars (elements M''))"
          using varsAppendClauses[of "elements M'" "elements ([(l, d)] @ M'')"]
          using varsAppendClauses[of "elements [(l, d)]" "elements M''"]
          by simp
        have ***: "vars (elements M) = vars (elements (M' @ M'')) \<union> {v}"
          using * **
          by simp
        have "M' @ M'' \<in> (?trails V')"
        proof-
          from \<open>uniq (elements M)\<close> \<open>M = M' @ [(l, d)] @ M''\<close>
          have "uniq (elements (M' @ M''))"
            by (auto iff: uniqAppendIff)
          moreover
          have "consistent (elements (M' @ M''))"
          proof-
            {
              assume "\<not> consistent (elements (M' @ M''))"
              then obtain l' where "literalTrue l' (elements (M' @ M''))" "literalFalse l' (elements (M' @ M''))"
                by (auto simp add:inconsistentCharacterization)
              with \<open>M = M' @ [(l, d)] @ M''\<close>
              have "literalTrue l' (elements M)" "literalFalse l' (elements M)"
                by auto
              hence "\<not> consistent (elements M)"
                by (auto simp add: inconsistentCharacterization)
              with \<open>consistent (elements M)\<close>
              have False
                by simp
            }
            thus ?thesis
              by auto
          qed
          moreover
          have "v \<notin> vars (elements (M' @ M''))"
          proof-
            {
              assume "v \<in> vars (elements (M' @ M''))"
              with *
              have "v \<in> vars (elements M') \<or> v \<in> vars (elements M'')"
                by simp
              moreover
              {
                assume "v \<in> (vars (elements M'))"
                hence "\<exists> l. var l = v \<and> l el elements M'"
                  by (induct M') auto
                then obtain l' where "var l' = v" "l' el elements M'"
                  by auto
                from \<open>var l = v\<close> \<open>var l' = v\<close>
                have "l = l' \<or> opposite l = l'"
                  using literalsWithSameVariableAreEqualOrOpposite[of "l" "l'"]
                  by simp
                moreover
                {
                  assume "l = l'"
                  with \<open>l' el elements M'\<close> \<open>M = M' @ [(l, d)] @ M''\<close>
                  have "\<not> uniq (elements M)"
                    by (auto iff: uniqAppendIff)
                  with \<open>uniq (elements M)\<close>
                  have False
                    by simp
                }
                moreover
                {
                  assume "opposite l = l'"
                  have "\<not> consistent (elements M)"
                  proof-
                    from \<open>l' el elements M'\<close> \<open>M = M' @ [(l, d)] @ M''\<close>
                    have "literalTrue l' (elements M)"
                      by simp
                    moreover
                    from \<open>l' el elements M'\<close> \<open>opposite l = l'\<close> \<open>M = M' @ [(l, d)] @ M''\<close>
                    have "literalFalse l' (elements M)"
                      by simp
                    ultimately
                    show ?thesis
                      by (auto simp add: inconsistentCharacterization)
                  qed
                  with \<open>consistent (elements M)\<close>
                  have False
                    by simp
                }
                ultimately
                have False
                  by auto
              }
              moreover
              {
                assume "v \<in> (vars (elements M''))"
                hence "\<exists> l. var l = v \<and> l el elements M''"
                  by (induct M'') auto
                then obtain l' where "var l' = v" "l' el (elements M'')"
                  by auto
                from \<open>var l = v\<close> \<open>var l' = v\<close>
                have "l = l' \<or> opposite l = l'"
                  using literalsWithSameVariableAreEqualOrOpposite[of "l" "l'"]
                  by simp
                moreover
                {
                  assume "l = l'"
                  with \<open>l' el elements M''\<close> \<open>M = M' @ [(l, d)] @ M''\<close>
                  have "\<not> uniq (elements M)"
                    by (auto iff: uniqAppendIff)
                  with \<open>uniq (elements M)\<close>
                  have False
                    by simp
                }
                moreover
                {
                  assume "opposite l = l'"
                  have "\<not> consistent (elements M)"
                  proof-
                    from \<open>l' el elements M''\<close> \<open>M = M' @ [(l, d)] @ M''\<close>
                    have "literalTrue l' (elements M)"
                      by simp
                    moreover
                    from \<open>l' el elements M''\<close> \<open>opposite l = l'\<close> \<open>M = M' @ [(l, d)] @ M''\<close>
                    have "literalFalse l' (elements M)"
                      by simp
                    ultimately
                    show ?thesis
                      by (auto simp add: inconsistentCharacterization)
                  qed
                  with \<open>consistent (elements M)\<close>
                  have False
                    by simp
                }
                ultimately
                have False
                  by auto
              }
              ultimately
              have False
                by auto
            }
            thus ?thesis
              by auto
          qed
          from 
            * ** ***
            \<open>v \<notin> vars (elements (M' @ M''))\<close> 
            \<open>vars (elements M) = insert v V'\<close> 
            \<open>\<not> v \<in> V'\<close>
          have "vars (elements (M' @ M'')) = V'"
            by (auto simp del: vars_clause_def)
          ultimately
          show ?thesis
            by simp
        qed
        ultimately
        show "M \<in> ?rhs"
          by auto
      qed
    next
      show "?rhs \<subseteq> ?lhs"
      proof
        fix M :: LiteralTrail
        assume "M \<in> ?rhs"
        then obtain M' M'' l d where 
          "M = M' @ [(l, d)] @ M''"
          "vars (elements (M' @ M'')) = V'" 
          "uniq (elements (M' @ M''))" "consistent (elements (M' @ M''))" "l \<in> {Pos v, Neg v}"
          by auto
        from \<open>l \<in> {Pos v, Neg v}\<close>
        have "var l = v"
          by auto
        have *: "vars (elements (M' @ M'')) = vars (elements M') \<union> vars (elements M'')"
          using varsAppendClauses[of "elements M'" "elements M''"]
          by simp
        from \<open>var l = v\<close> \<open>M = M' @ [(l, d)] @ M''\<close> 
        have **: "vars (elements M) = vars (elements M') \<union> {v} \<union> vars (elements M'')"
          using varsAppendClauses[of "elements M'" "elements ([(l, d)] @ M'')"]
          using varsAppendClauses[of "elements [(l, d)]" "elements M''"]
          by simp
        from * ** \<open>vars (elements (M' @ M'')) = V'\<close>
        have "vars (elements M) = insert v V'"
          by (auto simp del: vars_clause_def)
        moreover
        from *
          \<open>var l = v\<close> 
          \<open>v \<notin> V'\<close> 
          \<open>vars (elements (M' @ M'')) = V'\<close> 
        have "var l \<notin> vars (elements M')" "var l \<notin> vars (elements M'')"
          by auto
        from \<open>var l \<notin> vars (elements M')\<close>
        have "\<not> literalTrue l (elements M')" "\<not> literalFalse l (elements M')"
          using valuationContainsItsLiteralsVariable[of "l" "elements M'"]
          using valuationContainsItsLiteralsVariable[of "opposite l" "elements M'"]
          by auto
        from \<open>var l \<notin> vars (elements M'')\<close>
        have "\<not> literalTrue l (elements M'')" "\<not> literalFalse l (elements M'')"
          using valuationContainsItsLiteralsVariable[of "l" "elements M''"]
          using valuationContainsItsLiteralsVariable[of "opposite l" "elements M''"]
          by auto
        have "uniq (elements M)"
          using \<open>M = M' @ [(l, d)] @ M''\<close> \<open>uniq (elements (M' @ M''))\<close>
            \<open>\<not> literalTrue l (elements M'')\<close> \<open>\<not> literalFalse l (elements M'')\<close>
            \<open>\<not> literalTrue l (elements M')\<close> \<open>\<not> literalFalse l (elements M')\<close>
          by (auto iff: uniqAppendIff)
        moreover
        have "consistent (elements M)"
        proof-
          {
            assume "\<not> consistent (elements M)"
            then obtain l' where "literalTrue l' (elements M)" "literalFalse l' (elements M)"
              by (auto simp add: inconsistentCharacterization)
            have False 
            proof (cases "l' = l")
              case True
              with \<open>literalFalse l' (elements M)\<close> \<open>M = M' @ [(l, d)] @ M''\<close> 
              have "literalFalse l' (elements (M' @ M''))"
                using oppositeIsDifferentFromLiteral[of "l"]
                by (auto split: if_split_asm)
              with \<open>\<not> literalFalse l (elements M')\<close> \<open>\<not> literalFalse l (elements M'')\<close> \<open>l' = l\<close>
              show ?thesis
                by auto
            next
              case False
              with \<open>literalTrue l' (elements M)\<close> \<open>M = M' @ [(l, d)] @ M''\<close> 
              have "literalTrue l' (elements (M' @ M''))"
                by (auto split: if_split_asm)
              with \<open>consistent (elements (M' @ M''))\<close>
              have "\<not> literalFalse l' (elements (M' @ M''))"
                by (auto simp add: inconsistentCharacterization)
              with \<open>literalFalse l' (elements M)\<close> \<open>M = M' @ [(l, d)] @ M''\<close> 
              have "opposite l' = l"
                by (auto split: if_split_asm)
              with \<open>var l = v\<close>
              have "var l' = v"
                by auto
              with \<open>literalTrue l' (elements (M' @ M''))\<close> \<open>vars (elements (M' @ M'')) = V'\<close>
              have "v \<in> V'"
                using valuationContainsItsLiteralsVariable[of "l'" "elements (M' @ M'')"]
                by simp
              with \<open>v \<notin> V'\<close>
              show ?thesis
                by simp
            qed
          }
          thus ?thesis
            by auto
        qed
        ultimately
        show "M \<in> ?lhs"
          by auto
      qed
    qed
    moreover
    let ?f = "\<lambda> ((M', M''), l, d). M' @ [(l, d)] @ M''"
    let ?Mset = "{(M', M''). M' @ M'' \<in> ?trails V'}"
    let ?lSet = "{Pos v, Neg v}"
    let ?dSet = "{True, False}"
    have "?trails' V' = ?f ` (?Mset \<times> ?lSet \<times> ?dSet)" (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
      proof
        fix M :: LiteralTrail
        assume "M \<in> ?lhs"
        then obtain M' M'' l d
          where P: "M = M' @ [(l, d)] @ M''" "M' @ M'' \<in> (?trails V')" "l \<in> {Pos v, Neg v}" "d \<in> {True, False}"
          by auto
        show "M \<in> ?rhs"
        proof
          from P
          show "M = ?f ((M', M''), l, d)"
            by simp
        next
          from P
          show "((M', M''), l, d) \<in> ?Mset \<times> ?lSet \<times> ?dSet"
            by auto
        qed
      qed
    next
      show "?rhs \<subseteq> ?lhs"
      proof
        fix M::LiteralTrail
        assume "M \<in> ?rhs"
        then obtain p l d where P: "M = ?f (p, l, d)" "p \<in> ?Mset" "l \<in> ?lSet" "d \<in> ?dSet"
          by auto
        from \<open>p \<in> ?Mset\<close>
        obtain M' M'' where "M' @ M'' \<in> ?trails V'"
          by auto
        thus "M \<in> ?lhs"
          using P
          by auto
      qed
    qed
    moreover
    have "?Mset = {(M', M''). \<exists> l. l \<in> ?trails V' \<and> l = M' @ M''}"
      by auto
    hence "finite ?Mset"
      using insert(3)
      using finiteListDecomposeSet[of "?trails V'"]
      by simp
    ultimately
    show ?thesis
      by auto
  qed
qed

lemma finiteUniqAndConsistentTrailsWithGivenVariableSuperset: 
  fixes V :: "Variable set"
  assumes "finite V"
  shows "finite {(M::LiteralTrail). vars (elements M) \<subseteq> V \<and> uniq (elements M) \<and> consistent (elements M)}" (is "finite (?trails V)")
proof-
  have "{M. vars (elements M) \<subseteq> V \<and> uniq (elements M) \<and> consistent (elements M)} = 
    (\<Union> v \<in> Pow V.{M. vars (elements M) = v \<and> uniq (elements M) \<and> consistent (elements M)})"
    by auto
  moreover
  have "finite (\<Union> v \<in> Pow V.{M. vars (elements M) = v \<and> uniq (elements M) \<and> consistent (elements M)})"
  proof (rule finite_UN_I)
    from \<open>finite V\<close>
    show "finite (Pow V)"
      by simp
  next
    fix v
    assume "v \<in> Pow V"
    with \<open>finite V\<close>
    have "finite v"
      by (auto simp add: finite_subset)
    thus "finite {M. vars (elements M) = v \<and> uniq (elements M) \<and> consistent (elements M)}"
      using finiteUniqAndConsistentTrailsWithGivenVariableSet[of "v"]
      by simp
  qed
  ultimately
  show ?thesis
    by simp
qed

text\<open>Since the restricted ordering is acyclic and its domain is
finite, it has to be well-founded.\<close>
lemma wfLexLessRestricted:
  assumes "finite Vbl"
  shows "wf (lexLessRestricted Vbl)"
proof (rule finite_acyclic_wf)
  show "finite (lexLessRestricted Vbl)"
  proof-
    let ?X = "{(M1, M2). 
      consistent (elements M1) \<and> uniq (elements M1) \<and> vars (elements M1) \<subseteq> Vbl \<and>
      consistent (elements M2) \<and> uniq (elements M2) \<and> vars (elements M2) \<subseteq> Vbl}"
    let ?Y = "{M. vars (elements M) \<subseteq> Vbl \<and> uniq (elements M) \<and> consistent (elements M)}"
    have "?X = ?Y \<times> ?Y"
      by auto
    moreover
    have "finite ?Y"
      using finiteUniqAndConsistentTrailsWithGivenVariableSuperset[of "Vbl"]
        \<open>finite Vbl\<close>
      by auto
    ultimately
    have "finite ?X"
      by simp
    moreover
    have "lexLessRestricted Vbl \<subseteq> ?X"
      unfolding lexLessRestricted_def
      by auto
    ultimately
    show ?thesis
      by (simp add: finite_subset)
  qed
next
  show "acyclic (lexLessRestricted Vbl)"
  proof-
    {
      assume "\<not> ?thesis"
      then obtain x where "(x, x) \<in> (lexLessRestricted Vbl)^+"
        unfolding acyclic_def
        by auto
      have "lexLessRestricted Vbl \<subseteq> lexLess"
        unfolding lexLessRestricted_def
        by auto
      have "(lexLessRestricted Vbl)^+ \<subseteq> lexLess^+"
      proof
        fix a
        assume "a \<in> (lexLessRestricted Vbl)^+"
        with \<open>lexLessRestricted Vbl \<subseteq> lexLess\<close>
        show "a \<in> lexLess^+"
          using trancl_mono[of "a" "lexLessRestricted Vbl" "lexLess"]
          by blast
      qed
      with \<open>(x, x) \<in> (lexLessRestricted Vbl)^+\<close>
      have "(x, x) \<in> lexLess^+"
        by auto
      moreover
      have "trans lexLess"
        using translexLess
        .
      hence "lexLess^+ = lexLess"
        by (rule trancl_id)
      ultimately
      have "(x, x) \<in> lexLess"
        by auto
      with irreflexiveLexLess[of "x"]
      have False
        by simp
    }
    thus ?thesis
      by auto
  qed
qed

text\<open>@{term lexLessRestricted} is also transitive.\<close>
lemma transLexLessRestricted:
  shows "trans (lexLessRestricted Vbl)"
proof-
  {
    fix x::LiteralTrail and y::LiteralTrail and z::LiteralTrail
    assume "(x, y) \<in> lexLessRestricted Vbl" "(y, z) \<in> lexLessRestricted Vbl"
    hence "(x, z) \<in> lexLessRestricted Vbl"
      unfolding lexLessRestricted_def
      using translexLess
      unfolding trans_def
      by auto
  }
  thus ?thesis
    unfolding trans_def
    by blast
qed


(*-----------------------------------------------------------------------*)
subsubsection\<open>Conflict clause ordering\<close>
(*-----------------------------------------------------------------------*)

text\<open>The ordering of conflict clauses is the multiset ordering induced by the ordering of elements in the trail.
Since, resolution operator is defined so that it removes all occurrences of clashing literal, it is also neccessary 
to remove duplicate literals before comparison.\<close>

definition
"multLess M = inv_image  (mult (precedesOrder (elements M))) (\<lambda> x. mset (remdups (oppositeLiteralList x)))"

text\<open>The following lemma will help prove that application of the
$Explain$ DPLL transition rule decreases the conflict clause in the
@{term multLess} ordering.\<close>
lemma multLessResolve:
  assumes 
  "opposite l el C" and
  "isReason reason l (elements M)"
  shows
  "(resolve C reason (opposite l), C) \<in> multLess  M"
proof-
  let ?X = "mset (remdups (oppositeLiteralList C))"
  let ?Y = "mset (remdups (oppositeLiteralList (resolve C reason (opposite l))))"
  let ?ord = "precedesOrder (elements M)"
  have "(?Y, ?X) \<in> (mult1 ?ord)"
  proof-
    let ?Z = "mset (remdups (oppositeLiteralList (removeAll (opposite l) C)))"
    let ?W = "mset (remdups (oppositeLiteralList (removeAll l (list_diff reason C))))"
    let ?a = "l"
    from \<open>(opposite l) el C\<close>
    have "?X = ?Z + {#?a#}"
      using removeAll_multiset[of "remdups (oppositeLiteralList C)" "l"]
      using oppositeLiteralListRemove[of "opposite l" "C"]
      using literalElListIffOppositeLiteralElOppositeLiteralList[of "l" "oppositeLiteralList C"]
      by auto
    moreover
    have "?Y = ?Z + ?W" 
    proof-
      have "list_diff (oppositeLiteralList (removeAll l reason)) (oppositeLiteralList (removeAll (opposite l) C)) = 
        oppositeLiteralList (removeAll l (list_diff reason C))"
      proof-
        from \<open>isReason reason l (elements M)\<close>
        have "opposite l \<notin> set (removeAll l reason)"
          unfolding isReason_def
          by auto
        
        hence "list_diff (removeAll l reason) (removeAll (opposite l) C) = list_diff (removeAll l reason) C"
          using listDiffRemoveAllNonMember[of "opposite l" "removeAll l reason" "C"]
          by simp
        thus ?thesis
          unfolding oppositeLiteralList_def
          using listDiffMap[of "opposite" "removeAll l reason" "removeAll (opposite l) C"]
          by auto
      qed
      thus ?thesis
        unfolding resolve_def
        using remdupsAppendMultiSet[of "oppositeLiteralList (removeAll (opposite l) C)" "oppositeLiteralList (removeAll l reason)"]
        unfolding oppositeLiteralList_def
        by auto
    qed
    moreover
    have "\<forall> b. b \<in># ?W \<longrightarrow> (b, ?a) \<in> ?ord"
    proof-
      {
        fix b
        assume "b \<in># ?W"
        hence "opposite b \<in> set (removeAll l reason)"
        proof-
          from \<open>b \<in># ?W\<close> 
          have "b el remdups (oppositeLiteralList (removeAll l (list_diff reason C)))"
            by simp
          hence "opposite b el removeAll l (list_diff reason C)"
            using literalElListIffOppositeLiteralElOppositeLiteralList[of "opposite b" "removeAll l (list_diff reason C)"]
            by auto
          hence "opposite b el list_diff (removeAll l reason) C"
            by simp
          thus ?thesis
            using listDiffIff[of "opposite b" "removeAll l reason" "C"]
            by simp
        qed
        with \<open>isReason reason l (elements M)\<close>
        have "precedes b l (elements M)" "b \<noteq> l"
          unfolding isReason_def
          unfolding precedes_def
          by auto
        hence "(b, ?a) \<in> ?ord"
          unfolding precedesOrder_def
          by simp
      }
      thus ?thesis
        by auto
    qed
    ultimately
    have "\<exists> a M0 K. ?X = M0 + {#a#} \<and> ?Y = M0 + K \<and> (\<forall>b. b \<in># K \<longrightarrow> (b, a) \<in> ?ord)"
      by blast
    thus ?thesis
      unfolding mult1_def
      by auto
  qed
  hence "(?Y, ?X) \<in> (mult1 ?ord)\<^sup>+"
    by simp
  thus ?thesis
    unfolding multLess_def
    unfolding mult_def
    unfolding inv_image_def
    by auto
qed

lemma multLessListDiff:
assumes 
  "(a, b) \<in> multLess M"
shows
  "(list_diff a x, b) \<in> multLess M"
proof-
  let ?pOrd = "precedesOrder (elements M)"
  let ?f = "\<lambda> l. remdups (map opposite l)"
  have "trans ?pOrd"
    using transPrecedesOrder[of "elements M"]
    by simp

  have  "(mset (?f a), mset (?f b)) \<in> mult ?pOrd"
    using assms
    unfolding multLess_def
    unfolding oppositeLiteralList_def
    by simp
  moreover
  have "multiset_le (mset (list_diff (?f a) (?f x)))
                    (mset (?f a))
                    ?pOrd"
    using \<open>trans ?pOrd\<close>
    using multisetLeListDiff[of "?pOrd" "?f a" "?f x"]
    by simp
  ultimately
  have "(mset (list_diff (?f a) (?f x)), mset (?f b)) \<in> mult ?pOrd"
    unfolding multiset_le_def
    unfolding mult_def
    by auto

  thus ?thesis
    unfolding multLess_def
    unfolding oppositeLiteralList_def
    by (simp add: listDiffMap remdupsListDiff)
qed

lemma multLessRemdups:
assumes 
  "(a, b) \<in> multLess M"
shows
  "(remdups a, remdups b) \<in> multLess M \<and> 
   (remdups a, b) \<in> multLess M \<and> 
   (a, remdups b) \<in> multLess M"
proof-
  {
    fix l
    have "remdups (map opposite l) = remdups (map opposite (remdups l))"
      by (induct l) auto
  }
  thus ?thesis
    using assms
    unfolding multLess_def
    unfolding oppositeLiteralList_def
    by simp
qed

text\<open>Now we show that @{term multLess} is well-founded.\<close>
lemma wfMultLess: 
  shows "wf (multLess M)"
proof-
  have "wf (precedesOrder (elements M))"
    by (simp add: wellFoundedPrecedesOrder)
  hence "wf (mult (precedesOrder (elements M)))"
    by (simp add: wf_mult)
  thus ?thesis
    unfolding multLess_def
    using wf_inv_image[of "(mult (precedesOrder (elements M)))"]
    by auto
qed


(*-----------------------------------------------------------------------*)
subsubsection\<open>ConflictFlag ordering\<close>
(*-----------------------------------------------------------------------*)

text\<open>A trivial ordering on Booleans. It will be used for the
$Conflict$ transition rule.\<close>
definition
  "boolLess = {(True, False)}"

text\<open>We show that it is well-founded\<close>
lemma transBoolLess:
  shows "trans boolLess"
proof-
  {
    fix x::bool and y::bool and z::bool
    assume "(x, y) \<in> boolLess"
    hence "x = True" "y = False"
      unfolding boolLess_def
      by auto
    assume "(y, z) \<in> boolLess"
    hence "y = True" "z = False"
      unfolding boolLess_def
      by auto
    from \<open>y = False\<close> \<open>y = True\<close>
    have False
      by simp
    hence "(x, z) \<in> boolLess"
      by simp
  }
  thus ?thesis
    unfolding trans_def
    by blast
qed

lemma wfBoolLess:
  shows "wf boolLess"
proof (rule finite_acyclic_wf)
  show "finite boolLess"
    unfolding boolLess_def
    by simp
next
  have "boolLess^+ = boolLess"
    using transBoolLess
    by simp
  thus "acyclic boolLess"
    unfolding boolLess_def
    unfolding acyclic_def
    by auto
qed


(*-----------------------------------------------------------------------*)
subsubsection\<open>Formulae ordering\<close>
(*-----------------------------------------------------------------------*)

text\<open>A partial ordering of formulae, based on a membersip of a
single fixed clause. This ordering will be used for the $Learn$
transtion rule.\<close>
definition "learnLess (C::Clause) == {((F1::Formula), (F2::Formula)). C el F1 \<and> \<not> C el F2}"

text\<open>We show that it is well founded\<close>
lemma wfLearnLess:
  fixes C::Clause
  shows "wf (learnLess C)"
unfolding wf_eq_minimal
proof-
    show "\<forall>Q F. F \<in> Q \<longrightarrow> (\<exists>Fmin\<in>Q. \<forall>F'. (F', Fmin) \<in> learnLess C \<longrightarrow> F' \<notin> Q)"
    proof-
      {
        fix F::Formula and Q::"Formula set"
        assume "F \<in> Q"
        have "\<exists>Fmin\<in>Q. \<forall>F'. (F', Fmin) \<in> learnLess C \<longrightarrow> F' \<notin> Q"
        proof (cases "\<exists> Fc \<in> Q. C el Fc")
          case True
          then obtain Fc where "Fc \<in> Q" "C el Fc"
            by auto
          have "\<forall>F'. (F', Fc) \<in> learnLess C \<longrightarrow> F' \<notin> Q"
          proof
            fix F'
            show "(F', Fc) \<in> learnLess C \<longrightarrow> F' \<notin> Q"
            proof
              assume "(F', Fc) \<in> learnLess C"
              hence "\<not> C el Fc"
                unfolding learnLess_def
                by auto
              with \<open>C el Fc\<close> have False
                by simp
              thus "F' \<notin> Q"
                by simp
            qed
          qed
          with \<open>Fc \<in> Q\<close>
          show ?thesis
            by auto
        next
          case False
          have "\<forall>F'. (F', F) \<in> learnLess C \<longrightarrow> F' \<notin> Q"
          proof
            fix F'
            show "(F', F) \<in> learnLess C \<longrightarrow> F' \<notin> Q"
            proof
              assume "(F', F) \<in> learnLess C"
              hence "C el F'"
                unfolding learnLess_def
                by simp
              with False
              show "F' \<notin> Q"
                by auto
            qed
          qed
          with \<open>F \<in> Q\<close> 
          show ?thesis
            by auto
        qed
      }
      thus ?thesis
        by auto
    qed
qed

(*-----------------------------------------------------------------------*)
subsubsection\<open>Properties of well-founded relations.\<close>
(*-----------------------------------------------------------------------*)
lemma wellFoundedEmbed: 
  fixes rel :: "('a \<times> 'a) set" and rel' :: "('a \<times> 'a) set"
  assumes "\<forall> x y. (x, y) \<in> rel \<longrightarrow> (x, y) \<in> rel'" and "wf rel'"
  shows "wf rel"
unfolding wf_eq_minimal
proof-
  show "\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>zmin\<in>Q. \<forall>z. (z, zmin) \<in> rel \<longrightarrow> z \<notin> Q)"
  proof-
    {
      fix x::"'a" and Q::"'a set"
      assume "x \<in> Q"
      have "\<exists>zmin\<in>Q. \<forall>z. (z, zmin) \<in> rel \<longrightarrow> z \<notin> Q"
      proof-
        from \<open>wf rel'\<close> \<open>x \<in> Q\<close>
        obtain zmin::"'a"
          where "zmin \<in> Q" and "\<forall>z. (z, zmin) \<in> rel' \<longrightarrow> z \<notin> Q"
          unfolding wf_eq_minimal
          by auto
        {
          fix z::"'a"
          assume "(z, zmin) \<in> rel"
          have "z \<notin> Q"
          proof-
            from \<open>\<forall> x y. (x, y) \<in> rel \<longrightarrow> (x, y) \<in> rel'\<close> \<open>(z, zmin) \<in> rel\<close>
            have "(z, zmin) \<in> rel'"
              by simp
            with \<open>\<forall>z. (z, zmin) \<in> rel' \<longrightarrow> z \<notin> Q\<close>
            show ?thesis
              by simp
          qed
        }
        with \<open>zmin \<in> Q\<close>
        show ?thesis
          by auto
      qed
    }
    thus ?thesis
      by auto
  qed
qed

end
