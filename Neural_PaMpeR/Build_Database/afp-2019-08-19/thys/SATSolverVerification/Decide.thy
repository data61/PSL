(*    Title:              SatSolverVerification/Decide.thy
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

theory Decide
imports AssertLiteral
begin

(******************************************************************************)
(*          A P P L Y     D E C I D E                                         *)
(******************************************************************************)   

lemma applyDecideEffect:
assumes 
  "\<not> vars(elements (getM state)) \<supseteq> Vbl" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
shows 
  "let literal = selectLiteral state Vbl in 
   let state' = applyDecide state Vbl in 
          var literal \<notin> vars (elements (getM state)) \<and> 
          var literal \<in> Vbl \<and> 
          getM state' = getM state @ [(literal, True)] \<and> 
          getF state' = getF state"
using assms
using selectLiteral_def[of "Vbl" "state"]
unfolding applyDecide_def
using assertLiteralEffect[of "state" "selectLiteral state Vbl" "True"]
by (simp add: Let_def)

lemma InvariantConsistentAfterApplyDecide:
assumes 
  "\<not> vars(elements (getM state)) \<supseteq> Vbl" and
  "InvariantConsistent (getM state)" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
shows
  "let state' = applyDecide state Vbl in
         InvariantConsistent (getM state')"
using assms
using applyDecideEffect[of "Vbl" "state"]
using InvariantConsistentAfterDecide[of "getM state" "selectLiteral state Vbl" "getM (applyDecide state Vbl)"]
by (simp add: Let_def)


lemma InvariantUniqAfterApplyDecide:
assumes 
  "\<not> vars(elements (getM state)) \<supseteq> Vbl" and
  "InvariantUniq (getM state)" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
shows
  "let state' = applyDecide state Vbl in
         InvariantUniq (getM state')"
using assms
using applyDecideEffect[of "Vbl" "state"]
using InvariantUniqAfterDecide[of "getM state" "selectLiteral state Vbl" "getM (applyDecide state Vbl)"]
by (simp add: Let_def)

lemma InvariantQCharacterizationAfterApplyDecide:
assumes 
  "\<not> vars(elements (getM state)) \<supseteq> Vbl" and

  "InvariantConsistent (getM state)" and
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantWatchListsUniq (getWatchList state)"
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"

  "getQ state = []"
shows
  "let state' = applyDecide state Vbl in
     InvariantQCharacterization (getConflictFlag state') (getQ state') (getF state') (getM state')"
proof-
  let ?state' = "applyDecide state Vbl"
  let ?literal = "selectLiteral state Vbl"
  have "getM ?state' = getM state @ [(?literal, True)]"
    using assms
    using applyDecideEffect[of "Vbl" "state"]
    by (simp add: Let_def)
  hence "InvariantConsistent (getM state @ [(?literal, True)])"
    using InvariantConsistentAfterApplyDecide[of "Vbl" "state"]
    using assms
    by (simp add: Let_def)
  thus ?thesis
    using assms
    using InvariantQCharacterizationAfterAssertLiteralNotInQ[of "state" "?literal" "True"]
    unfolding applyDecide_def
    by simp
qed

lemma InvariantEquivalentZLAfterApplyDecide:
assumes
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantEquivalentZL (getF state) (getM state) F0"
shows
  "let state' = applyDecide state Vbl in
     InvariantEquivalentZL (getF state') (getM state') F0"
proof-
  let ?state' = "applyDecide state Vbl"
  let ?l = "selectLiteral state Vbl"

  have "getM ?state' = getM state @ [(?l, True)]"
    "getF ?state' = getF state"
    unfolding applyDecide_def
    using assertLiteralEffect[of "state" "?l" "True"]
    using assms
    by (auto simp only: Let_def)
  have "prefixToLevel 0 (getM ?state') = prefixToLevel 0 (getM state)"
  proof (cases "currentLevel (getM state) > 0")
    case True
    thus ?thesis
      using prefixToLevelAppend[of "0" "getM state" "[(?l, True)]"]
      using \<open>getM ?state' = getM state @ [(?l, True)]\<close>
      by auto
  next
    case False
    hence "prefixToLevel 0 (getM state @ [(?l, True)]) = 
             getM state @ (prefixToLevel_aux [(?l, True)] 0 (currentLevel (getM state)))"
      using prefixToLevelAppend[of "0" "getM state" "[(?l, True)]"]
      by simp
    hence "prefixToLevel 0 (getM state @ [(?l, True)]) = getM state"
      by simp
    thus ?thesis
      using \<open>getM ?state' = getM state @ [(?l, True)]\<close>
      using currentLevelZeroTrailEqualsItsPrefixToLevelZero[of "getM state"]
      using False
      by simp
  qed
  thus ?thesis
    using \<open>InvariantEquivalentZL (getF state) (getM state) F0\<close>
    unfolding InvariantEquivalentZL_def
    using \<open>getF ?state' = getF state\<close>
    by simp
qed


lemma InvariantGetReasonIsReasonAfterApplyDecide:
assumes
  "\<not> vars (elements (getM state)) \<supseteq> Vbl"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchListsUniq (getWatchList state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))"
  "getQ state = []"
shows
  "let state' = applyDecide state Vbl in 
    InvariantGetReasonIsReason (getReason state') (getF state') (getM state') (set (getQ state'))"
proof-
  let ?l = "selectLiteral state Vbl"
  let ?stateM = "state \<lparr> getM := getM state @ [(?l, True)] \<rparr>"
  have "InvariantGetReasonIsReason (getReason ?stateM) (getF ?stateM) (getM ?stateM) (set (getQ ?stateM))"
  proof-
    {
      fix l::Literal
      assume *: "l el (elements (getM ?stateM))" "\<not> l el (decisions (getM ?stateM))" "elementLevel l (getM ?stateM) > 0"
      have "\<exists> reason. getReason ?stateM l = Some reason \<and>
        0 \<le> reason \<and> reason < length (getF ?stateM) \<and>
        isReason (getF ?stateM ! reason) l (elements (getM ?stateM))"
      proof (cases "l el (elements (getM state))")
        case True
        moreover
        hence "\<not> l el (decisions (getM state))"
          using *
          by (simp add: markedElementsAppend)
        moreover
        have "elementLevel l (getM state) > 0"
        proof-
          {
            assume "\<not> ?thesis"
            with *
            have "l = ?l"
              using True
              using elementLevelAppend[of "l" "getM state" "[(?l, True)]"]
              by simp
            hence "var ?l \<in> vars (elements (getM state))"
              using True
              using valuationContainsItsLiteralsVariable[of "l" "elements (getM state)"]
              by simp
            hence False
              using \<open>\<not> vars (elements (getM state)) \<supseteq> Vbl\<close>
              using selectLiteral_def[of "Vbl" "state"]
              by auto
          } thus ?thesis
            by auto
        qed
        ultimately
        obtain reason
          where "getReason state l = Some reason \<and>
          0 \<le> reason \<and> reason < length (getF state) \<and>
          isReason (getF state ! reason) l (elements (getM state))"
          using \<open>InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))\<close>
          unfolding InvariantGetReasonIsReason_def
          by auto
        thus ?thesis
          using isReasonAppend[of "nth (getF ?stateM) reason" "l" "elements (getM state)" "[?l]"]
          by auto
      next
        case False
        hence "l = ?l"
          using *
          by auto
        hence "l el (decisions (getM ?stateM))"
          using markedElementIsMarkedTrue[of "l" "getM ?stateM"]
          by auto
        with *
        have False
          by auto
        thus ?thesis
          by simp
      qed
    }
    thus ?thesis
      using \<open>getQ state = []\<close>
      unfolding InvariantGetReasonIsReason_def
      by auto
  qed
  thus ?thesis
    using assms
    using InvariantGetReasonIsReasonAfterNotifyWatches[of "?stateM" "getWatchList ?stateM (opposite ?l)"
      "opposite ?l" "getM state" "True" "{}" "[]"]
    unfolding applyDecide_def
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding InvariantWatchListsUniq_def
    using \<open>getQ state = []\<close>
    by (simp add: Let_def)
qed

lemma InvariantsVarsAfterApplyDecide:
assumes
  "\<not> vars (elements (getM state)) \<supseteq> Vbl"
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantWatchListsUniq (getWatchList state)"
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"

  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
  "getQ state = []"
shows
  "let state' = applyDecide state Vbl in 
     InvariantVarsM (getM state') F0 Vbl \<and> 
     InvariantVarsF (getF state') F0 Vbl \<and> 
     InvariantVarsQ (getQ state') F0 Vbl"
proof-
  let ?state' = "applyDecide state Vbl"
  let ?l = "selectLiteral state Vbl"

  have "InvariantVarsM (getM ?state') F0 Vbl" "InvariantVarsF (getF ?state') F0 Vbl"
    using assms
    using applyDecideEffect[of "Vbl" "state"]
    using varsAppendValuation[of "elements (getM state)" "[?l]"]
    unfolding InvariantVarsM_def
    by (auto simp add: Let_def)
  moreover
  have "InvariantVarsQ (getQ ?state') F0 Vbl"
    using InvariantVarsQAfterAssertLiteral[of "state" "?l" "True" "F0" "Vbl"]
    using assms
    using InvariantConsistentAfterApplyDecide[of "Vbl" "state"]
    using InvariantUniqAfterApplyDecide[of "Vbl" "state"]
    using assertLiteralEffect[of "state" "?l" "True"]
    unfolding applyDecide_def
    unfolding InvariantVarsQ_def
    by (simp add: Let_def)
  ultimately
  show ?thesis
    by (simp add: Let_def)
qed

end
