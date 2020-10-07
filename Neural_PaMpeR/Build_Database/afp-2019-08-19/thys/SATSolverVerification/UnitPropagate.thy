theory UnitPropagate
imports AssertLiteral
begin
(*********************************************************************************)
(*    A P P L Y    U N I T    P R O P A G A T E                                  *)
(*********************************************************************************)

lemma applyUnitPropagateEffect:
assumes
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"

  "\<not> (getConflictFlag state)"
  "getQ state \<noteq> []"
shows
  "let uLiteral = hd (getQ state) in
   let state' = applyUnitPropagate state in
      \<exists> uClause. formulaEntailsClause (getF state) uClause \<and> 
                 isUnitClause uClause uLiteral (elements (getM state)) \<and> 
                 (getM state') = (getM state) @ [(uLiteral, False)]"
proof-
  let ?uLiteral = "hd (getQ state)"
  obtain uClause
    where "uClause el (getF state)" "isUnitClause uClause ?uLiteral (elements (getM state))"
    using assms
    unfolding InvariantQCharacterization_def
    by force
  thus ?thesis
    using assms
    using assertLiteralEffect[of "state" "?uLiteral" "False"]
    unfolding applyUnitPropagate_def
    using formulaEntailsItsClauses[of "uClause" "getF state"]
    by (auto simp add: Let_def )
qed

lemma InvariantConsistentAfterApplyUnitPropagate:
assumes
  "InvariantConsistent (getM state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "getQ state \<noteq> []"
  "\<not> (getConflictFlag state)"
shows
  "let state' = applyUnitPropagate state in
     InvariantConsistent (getM state')
  "
proof-
  let ?uLiteral = "hd (getQ state)"
  let ?state' = "applyUnitPropagate state"
  obtain uClause 
    where "isUnitClause uClause ?uLiteral (elements (getM state))" and
    "(getM ?state') = (getM state) @ [(?uLiteral, False)]"
    using assms
    using applyUnitPropagateEffect[of "state"]
    by (auto simp add: Let_def)
  thus ?thesis
    using assms
    using InvariantConsistentAfterUnitPropagate[of "getM state" "uClause" "?uLiteral" "getM ?state'"]
    by (auto simp add: Let_def)
qed

lemma InvariantUniqAfterApplyUnitPropagate:
assumes
  "InvariantUniq (getM state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "getQ state \<noteq> []"
  "\<not> (getConflictFlag state)"
shows
  "let state' = applyUnitPropagate state in
     InvariantUniq (getM state')
  "
proof-
  let ?uLiteral = "hd (getQ state)"
  let ?state' = "applyUnitPropagate state"
  obtain uClause 
    where "isUnitClause uClause ?uLiteral (elements (getM state))" and
    "(getM ?state') = (getM state) @ [(?uLiteral, False)]"
    using assms
    using applyUnitPropagateEffect[of "state"]
    by (auto simp add: Let_def)
  thus ?thesis
    using assms
    using InvariantUniqAfterUnitPropagate[of "getM state" "uClause" "?uLiteral" "getM ?state'"]
    by (auto simp add: Let_def)
qed

lemma InvariantWatchCharacterizationAfterApplyUnitPropagate:
assumes
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "(getQ state) \<noteq> []"
  "\<not> (getConflictFlag state)"
shows
  "let state' = applyUnitPropagate state in
        InvariantWatchCharacterization (getF state') (getWatch1 state') (getWatch2 state') (getM state')"
proof-
  let ?uLiteral = "hd (getQ state)"
  let ?state' = "assertLiteral ?uLiteral False state"
  let ?state'' = "applyUnitPropagate state"
  have "InvariantConsistent (getM ?state')"
    using assms
    using InvariantConsistentAfterApplyUnitPropagate[of "state"]
    unfolding applyUnitPropagate_def
    by (auto simp add: Let_def)
  moreover
  have "InvariantUniq (getM ?state')"
    using assms
    using InvariantUniqAfterApplyUnitPropagate[of "state"]
    unfolding applyUnitPropagate_def
    by (auto simp add: Let_def)
  ultimately
  show ?thesis
    using assms
    using InvariantWatchCharacterizationAfterAssertLiteral[of "state" "?uLiteral" "False"]
    using assertLiteralEffect
    unfolding applyUnitPropagate_def
    by (simp add: Let_def)
qed

lemma InvariantConflictFlagCharacterizationAfterApplyUnitPropagate:
assumes
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "\<not> getConflictFlag state"
  "getQ state \<noteq> []"
shows
  "let state' = (applyUnitPropagate state) in
      InvariantConflictFlagCharacterization (getConflictFlag state') (getF state') (getM state')"
proof-
  let ?uLiteral = "hd (getQ state)"
  let ?state' = "assertLiteral ?uLiteral False state"
  let ?state'' = "applyUnitPropagate state"
  have "InvariantConsistent (getM ?state')"
    using assms
    using InvariantConsistentAfterApplyUnitPropagate[of "state"]
    unfolding applyUnitPropagate_def
    by (auto simp add: Let_def)
  moreover
  have "InvariantUniq (getM ?state')"
    using assms
    using InvariantUniqAfterApplyUnitPropagate[of "state"]
    unfolding applyUnitPropagate_def
    by (auto simp add: Let_def)
  ultimately
  show ?thesis
    using assms
    using InvariantConflictFlagCharacterizationAfterAssertLiteral[of "state" "?uLiteral" "False"]
    using assertLiteralEffect
    unfolding applyUnitPropagate_def
    by (simp add: Let_def)
qed


lemma InvariantConflictClauseCharacterizationAfterApplyUnitPropagate:
assumes
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchListsUniq (getWatchList state)"
  "\<not> getConflictFlag state"
shows
   "let state' = applyUnitPropagate state in
    InvariantConflictClauseCharacterization (getConflictFlag state') (getConflictClause state') (getF state') (getM state')"
using assms
using InvariantConflictClauseCharacterizationAfterAssertLiteral[of "state" "hd (getQ state)" "False"]
unfolding applyUnitPropagate_def
unfolding InvariantWatchesEl_def
unfolding InvariantWatchListsContainOnlyClausesFromF_def
unfolding InvariantWatchListsCharacterization_def
unfolding InvariantWatchListsUniq_def
unfolding InvariantConflictClauseCharacterization_def
by (simp add: Let_def)
  
lemma InvariantQCharacterizationAfterApplyUnitPropagate:
assumes
  "InvariantConsistent (getM state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantUniqQ (getQ state)"
  "(getQ state) \<noteq> []"
  "\<not> (getConflictFlag state)"
shows
  "let state'' = applyUnitPropagate state in
     InvariantQCharacterization (getConflictFlag state'') (getQ state'') (getF state'') (getM state'')"
proof-
  let ?uLiteral = "hd (getQ state)"
  let ?state' = "assertLiteral ?uLiteral False state"
  let ?state'' = "applyUnitPropagate state"
  have "InvariantConsistent (getM ?state')"
    using assms
    using InvariantConsistentAfterApplyUnitPropagate[of "state"]
    unfolding applyUnitPropagate_def
    by (auto simp add: Let_def)
  hence "InvariantQCharacterization (getConflictFlag ?state') (removeAll ?uLiteral (getQ ?state')) (getF ?state') (getM ?state')"
    using assms
    using InvariantQCharacterizationAfterAssertLiteral[of "state" "?uLiteral" "False"]
    using assertLiteralEffect[of "state" "?uLiteral" "False"]
    by (simp add: Let_def)
  moreover
  have "InvariantUniqQ (getQ ?state')"
    using assms
    using InvariantUniqQAfterAssertLiteral[of "state" "?uLiteral" "False"]
    by (simp add: Let_def)

  have "?uLiteral = (hd (getQ ?state'))"
  proof-
    obtain s 
      where "(getQ state) @ s = getQ ?state'"
      using assms
      using assertLiteralEffect[of "state" "?uLiteral" "False"]
      unfolding isPrefix_def
      by auto
    hence "getQ ?state' = (getQ state) @ s"
      by (rule sym)
    thus ?thesis
      using \<open>getQ state \<noteq> []\<close>
      using hd_append[of "getQ state" "s"]
      by auto
  qed
    
  hence "set (getQ ?state'') = set (removeAll ?uLiteral (getQ ?state'))"
    using assms
    using \<open>InvariantUniqQ (getQ ?state')\<close>
    unfolding InvariantUniqQ_def
    using uniqHeadTailSet[of "getQ ?state'"]
    unfolding applyUnitPropagate_def
    by (simp add: Let_def)
  ultimately
  show ?thesis
    unfolding InvariantQCharacterization_def
    unfolding applyUnitPropagate_def
    by (simp add: Let_def)
qed


lemma InvariantUniqQAfterApplyUnitPropagate:
assumes
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantUniqQ (getQ state)"
  "getQ state \<noteq> []"
shows
  "let state'' = applyUnitPropagate state in
      InvariantUniqQ (getQ state'')"
proof-
  let ?uLiteral = "hd (getQ state)"
  let ?state' = "assertLiteral ?uLiteral False state"
  let ?state'' = "applyUnitPropagate state"
  have "InvariantUniqQ (getQ ?state')"
    using assms
    using InvariantUniqQAfterAssertLiteral[of "state" "?uLiteral" "False"]
    by (simp add: Let_def)
  moreover
  obtain s 
    where "getQ state @ s = getQ ?state'"
    using assms
    using assertLiteralEffect[of "state" "?uLiteral" "False"]
    unfolding isPrefix_def
    by auto
  hence "getQ ?state' = getQ state @ s"
    by (rule sym)
  with \<open>getQ state \<noteq> []\<close>
  have "getQ ?state' \<noteq> []"
    by simp
  ultimately
  show ?thesis
    using \<open>getQ state \<noteq> []\<close>
    unfolding InvariantUniqQ_def
    unfolding applyUnitPropagate_def
    using hd_Cons_tl[of "getQ ?state'"]
    using uniqAppendIff[of "[hd (getQ ?state')]" "tl (getQ ?state')"]
    by (simp add: Let_def)
qed

lemma InvariantNoDecisionsWhenConflictNorUnitAfterUnitPropagate:
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantNoDecisionsWhenConflict (getF state) (getM state) (currentLevel (getM state))"
  "InvariantNoDecisionsWhenUnit (getF state) (getM state) (currentLevel (getM state))"
shows
  "let state' = applyUnitPropagate state in
     InvariantNoDecisionsWhenConflict (getF state') (getM state') (currentLevel (getM state')) \<and> 
     InvariantNoDecisionsWhenUnit (getF state') (getM state') (currentLevel (getM state'))"
using assms
unfolding applyUnitPropagate_def
using InvariantsNoDecisionsWhenConflictNorUnitAfterAssertLiteral[of "state" "False" "hd (getQ state)"]
unfolding InvariantNoDecisionsWhenConflict_def
by (simp add: Let_def)


lemma InvariantGetReasonIsReasonAfterApplyUnitPropagate:
assumes
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)" and
  "InvariantUniqQ (getQ state)" and
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))" and
  "getQ state \<noteq> []" and
  "\<not> getConflictFlag state" 
shows
  "let state' = applyUnitPropagate state in 
     InvariantGetReasonIsReason (getReason state') (getF state') (getM state') (set (getQ state'))"
proof-
  let ?state0 = "state \<lparr> getM := getM state @ [(hd (getQ state), False)]\<rparr>"
  let ?state' = "assertLiteral (hd (getQ state)) False state"
  let ?state'' = "applyUnitPropagate state"

  have "InvariantGetReasonIsReason (getReason ?state0) (getF ?state0) (getM ?state0) (set (removeAll (hd (getQ ?state0)) (getQ ?state0)))"
  proof-

    {
      fix l::Literal
      assume *: "l el (elements (getM ?state0)) \<and> \<not> l el (decisions (getM ?state0)) \<and> elementLevel l (getM ?state0) > 0"
      hence "\<exists> reason. getReason ?state0 l = Some reason \<and> 0 \<le> reason \<and> reason < length (getF ?state0) \<and> 
               isReason (nth (getF ?state0) reason) l (elements (getM ?state0))"
      proof (cases "l el (elements (getM state))")
        case True
        from * 
        have "\<not> l el (decisions (getM state))"
          by (auto simp add: markedElementsAppend)
        from *
        have "elementLevel l (getM state) > 0"
          using elementLevelAppend[of "l" "getM state" "[(hd (getQ state), False)]"]
          using \<open>l el (elements (getM state))\<close>
          by simp
        show ?thesis
          using \<open>InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))\<close>
          using \<open>l el (elements (getM state))\<close>
          using \<open>\<not> l el (decisions (getM state))\<close>
          using \<open>elementLevel l (getM state) > 0\<close>
          unfolding InvariantGetReasonIsReason_def
          by (auto simp add: isReasonAppend)
      next
        case False
        with * 
        have "l = hd (getQ state)"
          by simp

        have "currentLevel (getM ?state0) > 0"
          using *
          using elementLevelLeqCurrentLevel[of "l" "getM ?state0"]
          by auto
        hence "currentLevel (getM state) > 0"
          unfolding currentLevel_def
          by (simp add: markedElementsAppend)
        moreover
        have "hd (getQ ?state0) el (getQ state)"
          using \<open>getQ state \<noteq> []\<close>
          by simp
        ultimately
        obtain reason
          where "getReason state (hd (getQ state)) = Some reason" "0 \<le> reason \<and> reason < length (getF state)"
          "isUnitClause (nth (getF state) reason) (hd (getQ state)) (elements (getM state)) \<or> 
           clauseFalse (nth (getF state) reason) (elements (getM state))" 
          using \<open>InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))\<close>
          unfolding InvariantGetReasonIsReason_def
          by auto
        hence "isUnitClause (nth (getF state) reason) (hd (getQ state)) (elements (getM state))"
          using \<open>\<not> getConflictFlag state\<close>
          using \<open>InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)\<close>
          unfolding InvariantConflictFlagCharacterization_def
          using nth_mem[of "reason" "getF state"]
          using formulaFalseIffContainsFalseClause[of "getF state" "elements (getM state)"]
          by simp
        thus ?thesis
          using \<open>getReason state (hd (getQ state)) = Some reason\<close> \<open>0 \<le> reason \<and> reason < length (getF state)\<close>
          using isUnitClauseIsReason[of "nth (getF state) reason" "hd (getQ state)" "elements (getM state)" "[hd (getQ state)]"]
          using \<open>l = hd (getQ state)\<close>
          by simp
     qed
    }
    moreover
    {
      fix literal::Literal
      assume "currentLevel (getM ?state0) > 0"
      hence "currentLevel (getM state) > 0"
        unfolding currentLevel_def
        by (simp add: markedElementsAppend)

      assume"literal el removeAll (hd (getQ ?state0)) (getQ ?state0)"
      hence "literal \<noteq> hd (getQ state)" "literal el getQ state"
        by auto
      
      then obtain reason
        where "getReason state literal = Some reason" "0 \<le> reason \<and> reason < length (getF state)" and
        *: "isUnitClause (nth (getF state) reason) literal (elements (getM state)) \<or> 
            clauseFalse (nth (getF state) reason) (elements (getM state))"
        using \<open>currentLevel (getM state) > 0\<close>
        using \<open>InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))\<close>
        unfolding InvariantGetReasonIsReason_def
        by auto
      hence "\<exists> reason. getReason ?state0 literal = Some reason \<and> 0 \<le> reason \<and> reason < length (getF ?state0) \<and> 
              (isUnitClause (nth (getF ?state0) reason) literal (elements (getM ?state0)) \<or> 
               clauseFalse (nth (getF ?state0) reason) (elements (getM ?state0)))"
      proof (cases "isUnitClause (nth (getF state) reason) literal (elements (getM state))")
        case True
        show ?thesis
        proof (cases "opposite literal = hd (getQ state)")
          case True
          thus ?thesis
            using \<open>isUnitClause (nth (getF state) reason) literal (elements (getM state))\<close>
            using \<open>getReason state literal = Some reason\<close>
            using \<open>literal \<noteq> hd (getQ state)\<close>
            using \<open>0 \<le> reason \<and> reason < length (getF state)\<close>
            unfolding isUnitClause_def
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
        next
          case False
          thus ?thesis
            using \<open>isUnitClause (nth (getF state) reason) literal (elements (getM state))\<close>
            using \<open>getReason state literal = Some reason\<close>
            using \<open>literal \<noteq> hd (getQ state)\<close>
            using \<open>0 \<le> reason \<and> reason < length (getF state)\<close>
            unfolding isUnitClause_def
            by auto
        qed
      next
        case False
        with * 
        have "clauseFalse (nth (getF state) reason) (elements (getM state))"
          by simp
        thus ?thesis
          using \<open>getReason state literal = Some reason\<close>
          using \<open>0 \<le> reason \<and> reason < length (getF state)\<close>
          using clauseFalseAppendValuation[of "nth (getF state) reason" "elements (getM state)" "[hd (getQ state)]"]
          by auto
      qed
    }
    ultimately
    show ?thesis
      unfolding InvariantGetReasonIsReason_def
      by auto
  qed

  hence "InvariantGetReasonIsReason (getReason ?state') (getF ?state') (getM ?state') (set (removeAll (hd (getQ state)) (getQ state)) \<union> (set (getQ ?state') - set (getQ state)))"
    using assms
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    using InvariantGetReasonIsReasonAfterNotifyWatches[of  
      "?state0" "getWatchList ?state0 (opposite (hd (getQ state)))"  "opposite (hd (getQ state))" "getM state" "False"
      "set (removeAll (hd (getQ ?state0)) (getQ ?state0))" "[]"]
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantWatchListsUniq_def
    by (auto simp add: Let_def)

  obtain s 
    where "getQ state @ s = getQ ?state'"
    using assms
    using assertLiteralEffect[of "state" "hd (getQ state)" "False"]
    unfolding isPrefix_def
    by auto
  hence "getQ ?state' = getQ state @ s"
    by simp
  hence "hd (getQ ?state') = hd (getQ state)"
    using hd_append2[of "getQ state" "s"]
    using \<open>getQ state \<noteq> []\<close>
    by simp

  have " set (removeAll (hd (getQ state)) (getQ state)) \<union> (set (getQ ?state') - set (getQ state)) = 
         set (removeAll (hd (getQ state)) (getQ ?state'))"
    using \<open>getQ ?state' = getQ state @ s\<close>
    using \<open>getQ state \<noteq> []\<close>
    by auto

  have "uniq (getQ ?state')"
    using assms
    using InvariantUniqQAfterAssertLiteral[of "state" "hd (getQ state)" "False"]
    unfolding InvariantUniqQ_def
    by (simp add: Let_def)
  
  have "set (getQ ?state'') = set (removeAll (hd (getQ state)) (getQ ?state'))"
    using \<open>uniq (getQ ?state')\<close>
    using \<open>hd (getQ ?state') = hd (getQ state)\<close>
    using uniqHeadTailSet[of "getQ ?state'"]
    unfolding applyUnitPropagate_def
    by (simp add: Let_def)

  thus ?thesis
    using \<open>InvariantGetReasonIsReason (getReason ?state') (getF ?state') (getM ?state') (set (removeAll (hd (getQ state)) (getQ state)) \<union> (set (getQ ?state') - set (getQ state)))\<close>
    using \<open>set (getQ ?state'') = set (removeAll (hd (getQ state)) (getQ ?state'))\<close>
    using \<open>set (removeAll (hd (getQ state)) (getQ state)) \<union> (set (getQ ?state') - set (getQ state)) = 
         set (removeAll (hd (getQ state)) (getQ ?state'))\<close>
    unfolding applyUnitPropagate_def
    by (simp add: Let_def)
qed

lemma InvariantEquivalentZLAfterApplyUnitPropagate:
assumes 
  "InvariantEquivalentZL (getF state) (getM state) Phi"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"

  "\<not> (getConflictFlag state)"
  "getQ state \<noteq> []"
shows
  "let state' = applyUnitPropagate state in
      InvariantEquivalentZL (getF state') (getM state') Phi
  "
proof-
  let ?uLiteral = "hd (getQ state)"
  let ?state' = "applyUnitPropagate state"
  let ?FM = "getF state @ val2form (elements (prefixToLevel 0 (getM state)))"
  let ?FM' = "getF ?state' @ val2form (elements (prefixToLevel 0 (getM ?state')))"


  obtain uClause 
    where "formulaEntailsClause (getF state) uClause" and 
    "isUnitClause uClause ?uLiteral (elements (getM state))" and
    "(getM ?state') = (getM state) @ [(?uLiteral, False)]"
    "(getF ?state') = (getF state)"
    using assms
    using applyUnitPropagateEffect[of "state"]
    unfolding applyUnitPropagate_def
    using assertLiteralEffect
    by (auto simp add: Let_def)
  note * = this

  show ?thesis
  proof (cases "currentLevel (getM state) = 0")
    case True
    hence "getM state = prefixToLevel 0 (getM state)"
      by (rule currentLevelZeroTrailEqualsItsPrefixToLevelZero)

    
    have "?FM' = ?FM @ [[?uLiteral]]"
      using *
      using \<open>(getM ?state') = (getM state) @ [(?uLiteral, False)]\<close>
      using prefixToLevelAppend[of "0" "getM state" "[(?uLiteral, False)]"]
      using \<open>currentLevel (getM state) = 0\<close>
      using \<open>getM state = prefixToLevel 0 (getM state)\<close>
      by (auto simp add: val2formAppend)

    have "formulaEntailsLiteral ?FM ?uLiteral"
      using *
      using unitLiteralIsEntailed [of "uClause" "?uLiteral" "elements (getM state)" "(getF state)"]
      using \<open>InvariantEquivalentZL (getF state) (getM state) Phi\<close>
      using \<open>getM state = prefixToLevel 0 (getM state)\<close>
      unfolding InvariantEquivalentZL_def
      by simp
    hence "formulaEntailsClause ?FM [?uLiteral]"
      unfolding formulaEntailsLiteral_def
      unfolding formulaEntailsClause_def
      by (auto simp add: clauseTrueIffContainsTrueLiteral)

    show ?thesis
      using \<open>InvariantEquivalentZL (getF state) (getM state) Phi\<close>
      using \<open>?FM' = ?FM @ [[?uLiteral]]\<close>
      using \<open>formulaEntailsClause ?FM [?uLiteral]\<close>
      unfolding InvariantEquivalentZL_def
      using extendEquivalentFormulaWithEntailedClause[of "Phi" "?FM" "[?uLiteral]"]
      by (simp add: equivalentFormulaeSymmetry)
  next
    case False
    hence "?FM = ?FM'"
      using *
      using prefixToLevelAppend[of "0" "getM state" "[(?uLiteral, False)]"]
      by (simp add: Let_def)
    thus ?thesis
      using \<open>InvariantEquivalentZL (getF state) (getM state) Phi\<close>
      unfolding InvariantEquivalentZL_def
      by (simp add: Let_def)
  qed
qed


lemma InvariantVarsQTl:
assumes
  "InvariantVarsQ Q F0 Vbl"
  "Q \<noteq> []"
shows
  "InvariantVarsQ (tl Q) F0 Vbl"
proof-
  have "InvariantVarsQ ((hd Q) # (tl Q)) F0 Vbl"
    using assms
    by simp
  hence "{var (hd Q)} \<union> vars (tl Q) \<subseteq> vars F0 \<union> Vbl"
    unfolding InvariantVarsQ_def
    by simp
  thus ?thesis
    unfolding InvariantVarsQ_def
    by simp
qed

lemma InvariantsVarsAfterApplyUnitPropagate:
assumes
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)" and
  "InvariantQCharacterization False (getQ state) (getF state) (getM state)" and
  "getQ state \<noteq> []"
  "\<not> getConflictFlag state"
  "InvariantVarsM (getM state) F0 Vbl" and
  "InvariantVarsQ (getQ state) F0 Vbl" and
  "InvariantVarsF (getF state) F0 Vbl"
shows
  "let state' = applyUnitPropagate state in
     InvariantVarsM (getM state') F0 Vbl \<and> 
     InvariantVarsQ (getQ state') F0 Vbl"
proof-
  let ?state' = "assertLiteral (hd (getQ state)) False state"
  let ?state'' = "applyUnitPropagate state"
  have "InvariantVarsQ (getQ ?state') F0 Vbl"
    using assms
    using InvariantConsistentAfterApplyUnitPropagate[of "state"]
    using InvariantUniqAfterApplyUnitPropagate[of "state"]
    using InvariantVarsQAfterAssertLiteral[of "state" "hd (getQ state)" "False" "F0" "Vbl"]
    using assertLiteralEffect[of "state" "hd (getQ state)" "False"]
    unfolding applyUnitPropagate_def
    by (simp add: Let_def)
  moreover
  have "(getQ ?state') \<noteq> []"
    using assms
    using assertLiteralEffect[of "state" "hd (getQ state)" "False"]
    using \<open>getQ state \<noteq> []\<close>
    unfolding isPrefix_def
    by auto
  ultimately
  have "InvariantVarsQ (getQ ?state'') F0 Vbl"
    unfolding applyUnitPropagate_def
    using InvariantVarsQTl[of "getQ ?state'" F0 Vbl]
    by (simp add: Let_def)
  moreover
  have "var (hd (getQ state)) \<in> vars F0 \<union> Vbl"
    using \<open>getQ state \<noteq> []\<close>
    using \<open>InvariantVarsQ (getQ state) F0 Vbl\<close>
    using hd_in_set[of "getQ state"]
    using clauseContainsItsLiteralsVariable[of "hd (getQ state)" "getQ state"]
    unfolding InvariantVarsQ_def
    by auto
  hence "InvariantVarsM (getM ?state'') F0 Vbl"
    using assms
    using assertLiteralEffect[of "state" "hd (getQ state)" "False"]
    using varsAppendValuation[of "elements (getM state)" "[hd (getQ state)]"]
    unfolding applyUnitPropagate_def
    unfolding InvariantVarsM_def
    by (simp add: Let_def)
  ultimately
  show ?thesis
    by (simp add: Let_def)
qed


(*********************************************************************************)
(*   E X H A U S T I V E   U N I T   P R O P A G A T E                           *)
(*********************************************************************************)

definition "lexLessState (Vbl::Variable set) == {(state1, state2). 
  (getM state1, getM state2) \<in> lexLessRestricted Vbl}"

lemma exhaustiveUnitPropagateTermination:
fixes
  state::State and Vbl::"Variable set"
assumes 
  "InvariantUniq (getM state)"
  "InvariantConsistent (getM state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantUniqQ (getQ state)"
  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsQ (getQ state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
  "finite Vbl"
shows
  "exhaustiveUnitPropagate_dom state"
using assms
proof (induct rule: wf_induct[of "lexLessState (vars F0 \<union> Vbl)"])
  case 1
  show ?case
    unfolding wf_eq_minimal
  proof-
    show "\<forall>Q (state::State). state \<in> Q \<longrightarrow> (\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> lexLessState (vars F0 \<union> Vbl) \<longrightarrow> state' \<notin> Q)"
    proof-
      {
        fix Q :: "State set" and state :: State
        assume "state \<in> Q"
        let ?Q1 = "{M::LiteralTrail. \<exists> state. state \<in> Q \<and> (getM state) = M}"
        from \<open>state \<in> Q\<close>
        have "getM state \<in> ?Q1"
          by auto
        have "wf (lexLessRestricted (vars F0 \<union> Vbl))"
          using \<open>finite Vbl\<close>
          using finiteVarsFormula[of "F0"]
          using  wfLexLessRestricted[of "vars F0 \<union> Vbl"]
          by simp
        with \<open>getM state \<in> ?Q1\<close>
        obtain Mmin where "Mmin \<in> ?Q1" "\<forall>M'. (M', Mmin) \<in> lexLessRestricted (vars F0 \<union> Vbl) \<longrightarrow> M' \<notin> ?Q1"
          unfolding wf_eq_minimal
          apply (erule_tac x="?Q1" in allE)
          apply (erule_tac x="getM state" in allE)
          by auto 
        from \<open>Mmin \<in> ?Q1\<close> obtain stateMin
          where "stateMin \<in> Q" "(getM stateMin) = Mmin"
          by auto
        have "\<forall>state'. (state', stateMin) \<in> lexLessState (vars F0 \<union> Vbl) \<longrightarrow> state' \<notin> Q"
        proof
          fix state'
          show "(state', stateMin) \<in> lexLessState (vars F0 \<union> Vbl) \<longrightarrow> state' \<notin> Q"
          proof
            assume "(state', stateMin) \<in> lexLessState (vars F0 \<union> Vbl)"
            hence "(getM state', getM stateMin) \<in> lexLessRestricted (vars F0 \<union> Vbl)"
              unfolding lexLessState_def
              by auto
            from \<open>\<forall>M'. (M', Mmin) \<in> lexLessRestricted (vars F0 \<union> Vbl) \<longrightarrow> M' \<notin> ?Q1\<close>
              \<open>(getM state', getM stateMin) \<in> lexLessRestricted (vars F0 \<union> Vbl)\<close> \<open>getM stateMin = Mmin\<close>
            have "getM state' \<notin> ?Q1"
              by simp
            with \<open>getM stateMin = Mmin\<close>
            show "state' \<notin> Q"
              by auto
          qed
        qed
        with \<open>stateMin \<in> Q\<close>
        have "\<exists> stateMin \<in> Q. (\<forall>state'. (state', stateMin) \<in> lexLessState (vars F0 \<union> Vbl) \<longrightarrow> state' \<notin> Q)"
          by auto
      }
      thus ?thesis
        by auto
    qed
  qed
next
  case (2 state')
  note ih = this
  show ?case
  proof (cases "getQ state' = [] \<or> getConflictFlag state'")
    case False
    let ?state'' = "applyUnitPropagate state'"

    have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')" and
      "InvariantWatchListsUniq (getWatchList ?state'')" and
      "InvariantWatchListsCharacterization (getWatchList ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and
      "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      using ih
      using WatchInvariantsAfterAssertLiteral[of "state'" "hd (getQ state')" "False"]
      unfolding applyUnitPropagate_def
      by (auto simp add: Let_def)
    moreover
    have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') (getM ?state'')"
      using ih
      using InvariantWatchCharacterizationAfterApplyUnitPropagate[of "state'"]
      unfolding InvariantQCharacterization_def
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantQCharacterization (getConflictFlag ?state'') (getQ ?state'') (getF ?state'') (getM ?state'')"
      using ih
      using InvariantQCharacterizationAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantConflictFlagCharacterization (getConflictFlag ?state'') (getF ?state'') (getM ?state'')"
      using ih
      using InvariantConflictFlagCharacterizationAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantUniqQ (getQ ?state'')"
      using ih
      using InvariantUniqQAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantConsistent (getM ?state'')"
      using ih
      using InvariantConsistentAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantUniq (getM ?state'')"
      using ih
      using InvariantUniqAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantVarsM (getM ?state'') F0 Vbl" "InvariantVarsQ (getQ ?state'') F0 Vbl"
      using ih
      using \<open>\<not> (getQ state' = [] \<or> getConflictFlag state')\<close>
      using InvariantsVarsAfterApplyUnitPropagate[of "state'" "F0" "Vbl"]
      by (auto simp add: Let_def)
    moreover
    have "InvariantVarsF (getF ?state'') F0 Vbl"
      unfolding applyUnitPropagate_def
      using assertLiteralEffect[of "state'" "hd (getQ state')" "False"]
      using ih
      by (simp add: Let_def)
    moreover
    have "(?state'', state') \<in> lexLessState (vars F0 \<union> Vbl)"
    proof-
      have "getM ?state'' = getM state' @ [(hd (getQ state'), False)]"
        unfolding applyUnitPropagate_def
        using ih
        using assertLiteralEffect[of "state'" "hd (getQ state')" "False"]
        by (simp add: Let_def)
      thus ?thesis
        unfolding lexLessState_def
        unfolding lexLessRestricted_def
        using lexLessAppend[of "[(hd (getQ state'), False)]" "getM state'"]
        using \<open>InvariantConsistent (getM ?state'')\<close>
        unfolding InvariantConsistent_def
        using \<open>InvariantConsistent (getM state')\<close>
        unfolding InvariantConsistent_def
        using \<open>InvariantUniq (getM ?state'')\<close>
        unfolding InvariantUniq_def
        using \<open>InvariantUniq (getM state')\<close>
        unfolding InvariantUniq_def
        using \<open>InvariantVarsM (getM ?state'') F0 Vbl\<close>
        using \<open>InvariantVarsM (getM state') F0 Vbl\<close>
        unfolding InvariantVarsM_def
        by simp
    qed
    ultimately
    have "exhaustiveUnitPropagate_dom ?state''"
      using ih
      by auto
    thus ?thesis
      using exhaustiveUnitPropagate_dom.intros[of "state'"]
      using False
      by simp
  next
    case True
    show ?thesis
      apply (rule exhaustiveUnitPropagate_dom.intros)
      using True
      by simp
  qed  
qed

lemma exhaustiveUnitPropagatePreservedVariables:
assumes
  "exhaustiveUnitPropagate_dom state"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
shows
  "let state' = exhaustiveUnitPropagate state in 
       (getSATFlag state') = (getSATFlag state)"
using assms
proof (induct state rule: exhaustiveUnitPropagate_dom.induct)
  case (step state')
  note ih = this
  show ?case
  proof (cases "(getConflictFlag state') \<or> (getQ state') = []")
    case True
    with exhaustiveUnitPropagate.simps[of "state'"]
    have "exhaustiveUnitPropagate state' = state'"
      by simp
    thus ?thesis
      by (simp only: Let_def)
  next
    case False
    let ?state'' = "applyUnitPropagate state'"

    have "exhaustiveUnitPropagate state' = exhaustiveUnitPropagate ?state''"
      using exhaustiveUnitPropagate.simps[of "state'"]
      using False
      by simp
    moreover
    have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')" and
      "InvariantWatchListsUniq (getWatchList ?state'')" and
      "InvariantWatchListsCharacterization (getWatchList ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and
      "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      using ih
      using WatchInvariantsAfterAssertLiteral[of "state'" "hd (getQ state')" "False"]
      unfolding applyUnitPropagate_def
      by (auto simp add: Let_def)
    moreover
    have "getSATFlag ?state'' = getSATFlag state'"
      unfolding applyUnitPropagate_def
      using assertLiteralEffect[of "state'" "hd (getQ state')" "False"]
      using ih
      by (simp add: Let_def)
    ultimately
    show ?thesis
      using ih
      using False
      by (simp add: Let_def)
  qed
qed

lemma exhaustiveUnitPropagatePreservesCurrentLevel:
assumes
  "exhaustiveUnitPropagate_dom state"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
shows
  "let state' = exhaustiveUnitPropagate state in 
       currentLevel (getM state') = currentLevel (getM state)"
using assms
proof (induct state rule: exhaustiveUnitPropagate_dom.induct)
  case (step state')
  note ih = this
  show ?case
  proof (cases "(getConflictFlag state') \<or> (getQ state') = []")
    case True
    with exhaustiveUnitPropagate.simps[of "state'"]
    have "exhaustiveUnitPropagate state' = state'"
      by simp
    thus ?thesis
      by (simp only: Let_def)
  next
    case False
    let ?state'' = "applyUnitPropagate state'"

    have "exhaustiveUnitPropagate state' = exhaustiveUnitPropagate ?state''"
      using exhaustiveUnitPropagate.simps[of "state'"]
      using False
      by simp
    moreover
    have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')" and
      "InvariantWatchListsUniq (getWatchList ?state'')" and
      "InvariantWatchListsCharacterization (getWatchList ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and
      "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      using ih
      using WatchInvariantsAfterAssertLiteral[of "state'" "hd (getQ state')" "False"]
      unfolding applyUnitPropagate_def
      by (auto simp add: Let_def)
    moreover
    have "currentLevel (getM state') = currentLevel (getM ?state'')"
      unfolding applyUnitPropagate_def
      using assertLiteralEffect[of "state'" "hd (getQ state')" "False"]
      using ih
      unfolding currentLevel_def
      by (simp add: Let_def markedElementsAppend)
    ultimately
    show ?thesis
      using ih
      using False
      by (simp add: Let_def)
  qed
qed


lemma InvariantsAfterExhaustiveUnitPropagate:
assumes
  "exhaustiveUnitPropagate_dom state"
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantUniqQ (getQ state)"
  "InvariantVarsQ (getQ state) F0 Vbl"
  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
shows
  "let state' = exhaustiveUnitPropagate state in 
       InvariantConsistent (getM state') \<and> 
       InvariantUniq (getM state') \<and> 
       InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state') \<and> 
       InvariantWatchListsUniq (getWatchList state') \<and> 
       InvariantWatchListsCharacterization (getWatchList state') (getWatch1 state') (getWatch2 state') \<and> 
       InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state') \<and> 
       InvariantWatchesDiffer (getF state') (getWatch1 state') (getWatch2 state') \<and> 
       InvariantWatchCharacterization (getF state') (getWatch1 state') (getWatch2 state') (getM state') \<and> 
       InvariantConflictFlagCharacterization (getConflictFlag state') (getF state') (getM state') \<and> 
       InvariantQCharacterization (getConflictFlag state') (getQ state') (getF state') (getM state') \<and> 
       InvariantUniqQ (getQ state') \<and> 
       InvariantVarsQ (getQ state') F0 Vbl \<and> 
       InvariantVarsM (getM state') F0 Vbl \<and> 
       InvariantVarsF (getF state') F0 Vbl
"
using assms
proof (induct state rule: exhaustiveUnitPropagate_dom.induct)
  case (step state')
  note ih = this
  show ?case
  proof (cases "(getConflictFlag state') \<or> (getQ state') = []")
    case True
    with exhaustiveUnitPropagate.simps[of "state'"]
    have "exhaustiveUnitPropagate state' = state'"
      by simp
    thus ?thesis
      using ih
      by (auto simp only: Let_def)
  next
    case False
    let ?state'' = "applyUnitPropagate state'"

    have "exhaustiveUnitPropagate state' = exhaustiveUnitPropagate ?state''"
      using exhaustiveUnitPropagate.simps[of "state'"]
      using False
      by simp
    moreover
    have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')" and
      "InvariantWatchListsUniq (getWatchList ?state'')" and
      "InvariantWatchListsCharacterization (getWatchList ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and
      "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      using ih
      using WatchInvariantsAfterAssertLiteral[of "state'" "hd (getQ state')" "False"]
      unfolding applyUnitPropagate_def
      by (auto simp add: Let_def)
    moreover
    have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') (getM ?state'')"
      using ih
      using InvariantWatchCharacterizationAfterApplyUnitPropagate[of "state'"]
      unfolding InvariantQCharacterization_def
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantQCharacterization (getConflictFlag ?state'') (getQ ?state'') (getF ?state'') (getM ?state'')"
      using ih
      using InvariantQCharacterizationAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantConflictFlagCharacterization (getConflictFlag ?state'') (getF ?state'') (getM ?state'')"
      using ih
      using InvariantConflictFlagCharacterizationAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantUniqQ (getQ ?state'')"
      using ih
      using InvariantUniqQAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantConsistent (getM ?state'')"
      using ih
      using InvariantConsistentAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantUniq (getM ?state'')"
      using ih
      using InvariantUniqAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantVarsM (getM ?state'') F0 Vbl" "InvariantVarsQ (getQ ?state'') F0 Vbl"
      using ih
      using \<open>\<not> (getConflictFlag state' \<or> getQ state' = [])\<close>
      using InvariantsVarsAfterApplyUnitPropagate[of "state'" "F0" "Vbl"]
      by (auto simp add: Let_def)
    moreover
    have "InvariantVarsF (getF ?state'') F0 Vbl"
      unfolding applyUnitPropagate_def
      using assertLiteralEffect[of "state'" "hd (getQ state')" "False"]
      using ih
      by (simp add: Let_def)
    ultimately
    show ?thesis
      using ih
      using False
      by (simp add: Let_def)
  qed
qed

lemma InvariantConflictClauseCharacterizationAfterExhaustivePropagate:
assumes
  "exhaustiveUnitPropagate_dom state"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)"
shows
  "let state' = exhaustiveUnitPropagate state in
   InvariantConflictClauseCharacterization (getConflictFlag state') (getConflictClause state') (getF state') (getM state')"
using assms
proof (induct state rule: exhaustiveUnitPropagate_dom.induct)
  case (step state')
  note ih = this
  show ?case
  proof (cases "(getConflictFlag state') \<or> (getQ state') = []")
    case True
    with exhaustiveUnitPropagate.simps[of "state'"]
    have "exhaustiveUnitPropagate state' = state'"
      by simp
    thus ?thesis
      using ih
      by (auto simp only: Let_def)
  next
    case False
    let ?state'' = "applyUnitPropagate state'"

    have "exhaustiveUnitPropagate state' = exhaustiveUnitPropagate ?state''"
      using exhaustiveUnitPropagate.simps[of "state'"]
      using False
      by simp
    moreover
    have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')" and
      "InvariantWatchListsUniq (getWatchList ?state'')" and
      "InvariantWatchListsCharacterization (getWatchList ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and
      "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      using ih(2) ih(3) ih(4) ih(5) ih(6) ih(7)
      using WatchInvariantsAfterAssertLiteral[of "state'" "hd (getQ state')" "False"]
      unfolding applyUnitPropagate_def
      by (auto simp add: Let_def)
    moreover
    have "InvariantConflictClauseCharacterization (getConflictFlag ?state'') (getConflictClause ?state'') (getF ?state'') (getM ?state'')"
      using ih(2) ih(3) ih(4) ih(5) ih(6)
      using \<open>\<not> (getConflictFlag state' \<or> getQ state' = [])\<close>
      using InvariantConflictClauseCharacterizationAfterApplyUnitPropagate[of "state'"]
      by (auto simp add: Let_def)
    ultimately
    show ?thesis
      using ih(1) ih(2)
      using False
      by (simp only: Let_def) (blast)
  qed
qed

lemma InvariantsNoDecisionsWhenConflictNorUnitAfterExhaustivePropagate:
assumes
  "exhaustiveUnitPropagate_dom state"
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantUniqQ (getQ state)"
  "InvariantNoDecisionsWhenConflict (getF state) (getM state) (currentLevel (getM state))"
  "InvariantNoDecisionsWhenUnit (getF state) (getM state) (currentLevel (getM state))"
shows
  "let state' = exhaustiveUnitPropagate state in
       InvariantNoDecisionsWhenConflict (getF state') (getM state') (currentLevel (getM state')) \<and> 
       InvariantNoDecisionsWhenUnit (getF state') (getM state') (currentLevel (getM state'))"
using assms
proof (induct state rule: exhaustiveUnitPropagate_dom.induct)
  case (step state')
  note ih = this
  show ?case
  proof (cases "(getConflictFlag state') \<or> (getQ state') = []")
    case True
    with exhaustiveUnitPropagate.simps[of "state'"]
    have "exhaustiveUnitPropagate state' = state'"
      by simp
    thus ?thesis
      using ih
      by (auto simp only: Let_def)
  next
    case False
    let ?state'' = "applyUnitPropagate state'"

    have "exhaustiveUnitPropagate state' = exhaustiveUnitPropagate ?state''"
      using exhaustiveUnitPropagate.simps[of "state'"]
      using False
      by simp
    moreover
    have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')" and
      "InvariantWatchListsUniq (getWatchList ?state'')" and
      "InvariantWatchListsCharacterization (getWatchList ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and
      "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      using ih(5) ih(6) ih(7) ih(8) ih(9)
      using WatchInvariantsAfterAssertLiteral[of "state'" "hd (getQ state')" "False"]
      unfolding applyUnitPropagate_def
      by (auto simp add: Let_def)
    moreover
    have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') (getM ?state'')"
      using ih
      using InvariantWatchCharacterizationAfterApplyUnitPropagate[of "state'"]
      unfolding InvariantQCharacterization_def
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantQCharacterization (getConflictFlag ?state'') (getQ ?state'') (getF ?state'') (getM ?state'')"
      using ih
      using InvariantQCharacterizationAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantConflictFlagCharacterization (getConflictFlag ?state'') (getF ?state'') (getM ?state'')"
      using ih
      using InvariantConflictFlagCharacterizationAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantUniqQ (getQ ?state'')"
      using ih
      using InvariantUniqQAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantConsistent (getM ?state'')"
      using ih
      using InvariantConsistentAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantUniq (getM ?state'')"
      using ih
      using InvariantUniqAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantNoDecisionsWhenUnit (getF ?state'') (getM ?state'') (currentLevel (getM ?state''))"
         "InvariantNoDecisionsWhenConflict (getF ?state'') (getM ?state'') (currentLevel (getM ?state''))"
      using ih(5) ih(8) ih(11) ih(12) ih(14) ih(15)
      using InvariantNoDecisionsWhenConflictNorUnitAfterUnitPropagate[of "state'"]
      by (auto simp add: Let_def)
    ultimately
    show ?thesis
      using ih(1) ih(2)
      using False
      by (simp add: Let_def)
  qed
qed


lemma InvariantGetReasonIsReasonAfterExhaustiveUnitPropagate:
assumes
  "exhaustiveUnitPropagate_dom state"
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantUniqQ (getQ state)" and
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))"
shows
  "let state' = exhaustiveUnitPropagate state in 
       InvariantGetReasonIsReason (getReason state') (getF state') (getM state') (set (getQ state'))"
using assms
proof (induct state rule: exhaustiveUnitPropagate_dom.induct)
  case (step state')
  note ih = this
  show ?case
  proof (cases "(getConflictFlag state') \<or> (getQ state') = []")
    case True
    with exhaustiveUnitPropagate.simps[of "state'"]
    have "exhaustiveUnitPropagate state' = state'"
      by simp
    thus ?thesis
      using ih
      by (auto simp only: Let_def)
  next
    case False
    let ?state'' = "applyUnitPropagate state'"

    have "exhaustiveUnitPropagate state' = exhaustiveUnitPropagate ?state''"
      using exhaustiveUnitPropagate.simps[of "state'"]
      using False
      by simp
    moreover
    have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')" and
      "InvariantWatchListsUniq (getWatchList ?state'')" and
      "InvariantWatchListsCharacterization (getWatchList ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and
      "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      using ih
      using WatchInvariantsAfterAssertLiteral[of "state'" "hd (getQ state')" "False"]
      unfolding applyUnitPropagate_def
      by (auto simp add: Let_def)
    moreover
    have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') (getM ?state'')"
      using ih
      using InvariantWatchCharacterizationAfterApplyUnitPropagate[of "state'"]
      unfolding InvariantQCharacterization_def
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantQCharacterization (getConflictFlag ?state'') (getQ ?state'') (getF ?state'') (getM ?state'')"
      using ih
      using InvariantQCharacterizationAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantConflictFlagCharacterization (getConflictFlag ?state'') (getF ?state'') (getM ?state'')"
      using ih
      using InvariantConflictFlagCharacterizationAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantUniqQ (getQ ?state'')"
      using ih
      using InvariantUniqQAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantConsistent (getM ?state'')"
      using ih
      using InvariantConsistentAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantUniq (getM ?state'')"
      using ih
      using InvariantUniqAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantGetReasonIsReason (getReason ?state'') (getF ?state'') (getM ?state'') (set (getQ ?state''))"
      using ih
      using InvariantGetReasonIsReasonAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    ultimately
    show ?thesis
      using ih
      using False
      by (simp add: Let_def)
  qed
qed


lemma InvariantEquivalentZLAfterExhaustiveUnitPropagate:
assumes
  "exhaustiveUnitPropagate_dom state"
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantEquivalentZL (getF state) (getM state) Phi"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantUniqQ (getQ state)"
shows
  "let state' = exhaustiveUnitPropagate state in 
      InvariantEquivalentZL (getF state') (getM state') Phi
  "
using assms
proof (induct state rule: exhaustiveUnitPropagate_dom.induct)
  case (step state')
  note ih = this
  show ?case
  proof (cases "(getConflictFlag state') \<or> (getQ state') = []")
    case True
    with exhaustiveUnitPropagate.simps[of "state'"]
    have "exhaustiveUnitPropagate state' = state'"
      by simp
    thus ?thesis
      using ih
      by (simp only: Let_def)
  next
    case False
    let ?state'' = "applyUnitPropagate state'"

    have "exhaustiveUnitPropagate state' = exhaustiveUnitPropagate ?state''"
      using exhaustiveUnitPropagate.simps[of "state'"]
      using False
      by simp
    moreover
    have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')" and
      "InvariantWatchListsUniq (getWatchList ?state'')" and
      "InvariantWatchListsCharacterization (getWatchList ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and
      "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      using ih
      using WatchInvariantsAfterAssertLiteral[of "state'" "hd (getQ state')" "False"]
      unfolding applyUnitPropagate_def
      by (auto simp add: Let_def)
    moreover
    have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') (getM ?state'')"
      using ih
      using InvariantWatchCharacterizationAfterApplyUnitPropagate[of "state'"]
      unfolding InvariantQCharacterization_def
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantQCharacterization (getConflictFlag ?state'') (getQ ?state'') (getF ?state'') (getM ?state'')"
      using ih
      using InvariantQCharacterizationAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantConflictFlagCharacterization (getConflictFlag ?state'') (getF ?state'') (getM ?state'')"
      using ih
      using InvariantConflictFlagCharacterizationAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantUniqQ (getQ ?state'')"
      using ih
      using InvariantUniqQAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantConsistent (getM ?state'')"
      using ih
      using InvariantConsistentAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantUniq (getM ?state'')"
      using ih
      using InvariantUniqAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantEquivalentZL (getF ?state'') (getM ?state'') Phi"
      using ih
      using InvariantEquivalentZLAfterApplyUnitPropagate[of "state'" "Phi"]
      using False
      by (simp add: Let_def)
    moreover
    have "currentLevel (getM state') = currentLevel (getM ?state'')"
      unfolding applyUnitPropagate_def
      using assertLiteralEffect[of "state'" "hd (getQ state')" "False"]
      using ih
      unfolding currentLevel_def
      by (simp add: Let_def markedElementsAppend)
    ultimately
    show ?thesis
      using ih
      using False
      by (auto simp only: Let_def)
  qed
qed

lemma conflictFlagOrQEmptyAfterExhaustiveUnitPropagate:
assumes
"exhaustiveUnitPropagate_dom state"
shows
"let state' = exhaustiveUnitPropagate state in
    (getConflictFlag state') \<or> (getQ state' = [])"
using assms
proof (induct state rule: exhaustiveUnitPropagate_dom.induct)
  case (step state')
  note ih = this
  show ?case
  proof (cases "(getConflictFlag state') \<or> (getQ state') = []")
    case True
    with exhaustiveUnitPropagate.simps[of "state'"]
    have "exhaustiveUnitPropagate state' = state'"
      by simp
    thus ?thesis
      using True
      by (simp only: Let_def)
  next
    case False
    let ?state'' = "applyUnitPropagate state'"

    have "exhaustiveUnitPropagate state' = exhaustiveUnitPropagate ?state''"
      using exhaustiveUnitPropagate.simps[of "state'"]
      using False
      by simp
    thus ?thesis
      using ih
      using False
      by (simp add: Let_def)
  qed
qed

end
