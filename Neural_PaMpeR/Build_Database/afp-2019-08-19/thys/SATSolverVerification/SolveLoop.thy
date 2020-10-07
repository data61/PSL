(*    Title:              SatSolverVerification/SolveLoop.thy
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

theory SolveLoop
imports UnitPropagate ConflictAnalysis Decide
begin


(******************************************************************************)
(*          S O L V E   L O O P   B O D Y                                     *)
(******************************************************************************)

lemma soundnessForUNSAT:
assumes 
  "equivalentFormulae (F @ val2form M) F0"
  "formulaFalse F M"
shows
  "\<not> satisfiable F0"
proof-
  have "formulaEntailsValuation (F @ val2form M) M"
    using val2formIsEntailed[of "F" "M" "[]"]
    by simp
  moreover
  have "formulaFalse (F @ val2form M) M"
    using \<open>formulaFalse F M\<close>
    by (simp add: formulaFalseAppend)
  ultimately
  have "\<not> satisfiable (F @ val2form M)"
    using formulaFalseInEntailedValuationIsUnsatisfiable[of "F @ val2form M" "M"]
    by simp
  thus ?thesis
    using \<open>equivalentFormulae (F @ val2form M) F0\<close>
    by (simp add: satisfiableEquivalent)
qed

lemma soundnessForSat:
  fixes F0 :: Formula and F :: Formula and M::LiteralTrail
  assumes "vars F0 \<subseteq> Vbl" and "InvariantVarsF F F0 Vbl" and "InvariantConsistent M" and "InvariantEquivalentZL F M F0" and
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
  moreover
  obtain s
    where "elements (prefixToLevel 0 M) @ s = elements M"
    using isPrefixPrefixToLevel[of "0" "M"]
    using isPrefixElements[of "prefixToLevel 0 M" "M"]
    unfolding isPrefix_def
    by auto
  hence "elements M = elements (prefixToLevel 0 M) @ s"
    by (rule sym)
  hence "formulaTrue (val2form (elements (prefixToLevel 0 M))) (elements M)"
    using val2formFormulaTrue[of "elements (prefixToLevel 0 M)" "elements M"]
    by auto
  hence "model (elements M) (val2form (elements (prefixToLevel 0 M)))"
    using \<open>consistent (elements M)\<close>
    by simp
  ultimately
  show ?thesis
    using \<open>InvariantEquivalentZL F M F0\<close>
    unfolding InvariantEquivalentZL_def
    unfolding equivalentFormulae_def
    using formulaTrueAppend[of "F" "val2form (elements (prefixToLevel 0 M))" "elements M"]
    by auto
qed

definition
"satFlagLessState = {(state1::State, state2::State). (getSATFlag state1) \<noteq> UNDEF \<and> (getSATFlag state2) = UNDEF}"


lemma wellFoundedSatFlagLessState:
  shows "wf satFlagLessState"
  unfolding wf_eq_minimal
proof-
  show "\<forall>Q state. state \<in> Q \<longrightarrow> (\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix state::State and Q::"State set"
      assume "state \<in> Q"
      have "\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q"
      proof (cases "\<exists> stateDef \<in> Q. (getSATFlag stateDef) \<noteq> UNDEF")
        case True
        then obtain stateDef where "stateDef \<in> Q" "(getSATFlag stateDef) \<noteq> UNDEF"
          by auto
        have "\<forall>state'. (state', stateDef) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q"
        proof
          fix state'
          show "(state', stateDef) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q"
          proof
            assume "(state', stateDef) \<in> satFlagLessState"
            hence "getSATFlag stateDef = UNDEF"
              unfolding satFlagLessState_def
              by auto
            with \<open>getSATFlag stateDef \<noteq> UNDEF\<close> have False
              by simp
            thus "state' \<notin> Q"
              by simp
          qed
        qed
        with \<open>stateDef \<in> Q\<close>
        show ?thesis
          by auto
      next
        case False
        have "\<forall>state'. (state', state) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q"
        proof
          fix state'
          show "(state', state) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q"
          proof
            assume "(state', state) \<in> satFlagLessState"
            hence "getSATFlag state' \<noteq> UNDEF"
              unfolding satFlagLessState_def
              by simp
            with False
            show "state' \<notin> Q"
              by auto
          qed
        qed
        with \<open>state \<in> Q\<close> 
        show ?thesis
          by auto
      qed
    }
    thus ?thesis
      by auto
  qed
qed

definition
"lexLessState1 Vbl = {(state1::State, state2::State). 
     getSATFlag state1 = UNDEF \<and> getSATFlag state2 = UNDEF \<and>
     (getM state1, getM state2) \<in> lexLessRestricted Vbl
}"

lemma wellFoundedLexLessState1:
assumes
  "finite Vbl"
shows
  "wf (lexLessState1 Vbl)"
unfolding wf_eq_minimal
proof-
  show "\<forall>Q state. state \<in> Q \<longrightarrow> (\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix Q :: "State set" and state :: State
      assume "state \<in> Q"
      let ?Q1 = "{M::LiteralTrail. \<exists> state. state \<in> Q \<and> getSATFlag state = UNDEF \<and> (getM state) = M}"
      have "\<exists> stateMin \<in> Q. (\<forall>state'. (state', stateMin) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q)"
      proof (cases "?Q1 \<noteq> {}")
        case True
        then obtain M::LiteralTrail
          where "M \<in> ?Q1"
          by auto
        then obtain MMin::LiteralTrail
          where "MMin \<in> ?Q1" "\<forall>M'. (M', MMin) \<in> lexLessRestricted Vbl \<longrightarrow> M' \<notin> ?Q1"
          using wfLexLessRestricted[of "Vbl"] \<open>finite Vbl\<close>
          unfolding wf_eq_minimal
          apply simp
          apply (erule_tac x="?Q1" in allE)
          by auto
        from \<open>MMin \<in> ?Q1\<close> obtain stateMin
          where "stateMin \<in> Q" "(getM stateMin) = MMin" "getSATFlag stateMin = UNDEF"
          by auto
        have "\<forall>state'. (state', stateMin) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q"
        proof
          fix state'
          show "(state', stateMin) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q"
          proof
            assume "(state', stateMin) \<in> lexLessState1 Vbl"
            hence "getSATFlag state' = UNDEF" "(getM state', getM stateMin) \<in> lexLessRestricted Vbl"
              unfolding lexLessState1_def
              by auto
            hence "getM state' \<notin> ?Q1"
              using \<open>\<forall>M'. (M', MMin) \<in> lexLessRestricted Vbl \<longrightarrow> M' \<notin> ?Q1\<close>
              using \<open>(getM stateMin) = MMin\<close>
              by auto
            thus "state' \<notin> Q"
              using \<open>getSATFlag state' = UNDEF\<close>
              by auto
          qed
        qed
        thus ?thesis
          using \<open>stateMin \<in> Q\<close>
          by auto
      next
        case False
        have "\<forall>state'. (state', state) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q"
        proof
          fix state'
          show "(state', state) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q"
          proof
            assume "(state', state) \<in> lexLessState1 Vbl"
            hence "getSATFlag state = UNDEF"
              unfolding lexLessState1_def
              by simp
            hence "(getM state) \<in> ?Q1"
              using \<open>state \<in> Q\<close>
              by auto
            hence False
              using False
              by auto
            thus "state' \<notin> Q"
              by simp
          qed
        qed
        thus ?thesis
          using \<open>state \<in> Q\<close>
          by auto
      qed
    }
    thus ?thesis
      by auto
  qed
qed

definition 
"terminationLessState1 Vbl = {(state1::State, state2::State). 
  (state1, state2) \<in> satFlagLessState \<or> 
  (state1, state2) \<in> lexLessState1 Vbl}"

lemma wellFoundedTerminationLessState1:
  assumes "finite Vbl"
  shows "wf (terminationLessState1 Vbl)"
unfolding wf_eq_minimal
proof-
  show "\<forall> Q state. state \<in> Q \<longrightarrow> (\<exists> stateMin \<in> Q. \<forall> state'. (state', stateMin) \<in> terminationLessState1 Vbl \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix Q::"State set"
      fix state::"State"
      assume "state \<in> Q"
      have "\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> terminationLessState1 Vbl \<longrightarrow> state' \<notin> Q"
      proof-
        obtain state0
          where "state0 \<in> Q" "\<forall>state'. (state', state0) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q"
          using wellFoundedSatFlagLessState
          unfolding wf_eq_minimal
          using \<open>state \<in> Q\<close>
          by auto
        show ?thesis
        proof (cases "getSATFlag state0 = UNDEF")
          case False
          hence "\<forall>state'. (state', state0) \<in> terminationLessState1 Vbl \<longrightarrow> state' \<notin> Q"
            using \<open>\<forall>state'. (state', state0) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q\<close>
            unfolding terminationLessState1_def
            unfolding lexLessState1_def
            by simp
          thus ?thesis
            using \<open>state0 \<in> Q\<close>
            by auto
        next
          case True
          then obtain state1
            where "state1 \<in> Q" "\<forall>state'. (state', state1) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q"
            using \<open>finite Vbl\<close>
            using \<open>state \<in> Q\<close>
            using wellFoundedLexLessState1[of "Vbl"]
            unfolding wf_eq_minimal
            by auto

          have "\<forall>state'. (state', state1) \<in> terminationLessState1 Vbl \<longrightarrow> state' \<notin> Q"
            using \<open>\<forall>state'. (state', state1) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q\<close>
            unfolding terminationLessState1_def
            using \<open>\<forall>state'. (state', state0) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q\<close>
            using True
            unfolding satFlagLessState_def
            by simp
          thus ?thesis
            using \<open>state1 \<in> Q\<close>
            by auto
        qed
      qed
    }
    thus ?thesis
      by auto
  qed
qed

lemma transTerminationLessState1:
  "trans (terminationLessState1 Vbl)"
proof-
  {
    fix x::State and y::State and z::State
    assume "(x, y) \<in> terminationLessState1 Vbl" "(y, z) \<in> terminationLessState1 Vbl"
    have "(x, z) \<in> terminationLessState1 Vbl"
    proof (cases "(x, y) \<in> satFlagLessState")
      case True
      hence "getSATFlag x \<noteq> UNDEF" "getSATFlag y = UNDEF"
        unfolding satFlagLessState_def
        by auto
      hence "getSATFlag z = UNDEF"
        using \<open>(y, z) \<in> terminationLessState1 Vbl\<close>
        unfolding terminationLessState1_def
        unfolding satFlagLessState_def
        unfolding lexLessState1_def
        by auto
      thus ?thesis
        using \<open>getSATFlag x \<noteq> UNDEF\<close>
        unfolding terminationLessState1_def
        unfolding satFlagLessState_def
        by simp
    next
      case False
      with \<open>(x, y) \<in> terminationLessState1 Vbl\<close>
      have "getSATFlag x = UNDEF" "getSATFlag y = UNDEF" "(getM x, getM y) \<in> lexLessRestricted Vbl"
        unfolding terminationLessState1_def
        unfolding lexLessState1_def
        by auto
      hence "getSATFlag z = UNDEF" "(getM y, getM z) \<in> lexLessRestricted Vbl"
        using \<open>(y, z) \<in> terminationLessState1 Vbl\<close>
        unfolding terminationLessState1_def
        unfolding satFlagLessState_def
        unfolding lexLessState1_def
        by auto
      thus ?thesis
        using \<open>getSATFlag x = UNDEF\<close> 
        using \<open>(getM x, getM y) \<in> lexLessRestricted Vbl\<close>
        using transLexLessRestricted[of "Vbl"]
        unfolding trans_def
        unfolding terminationLessState1_def
        unfolding satFlagLessState_def
        unfolding lexLessState1_def
        by blast
    qed
  }
  thus ?thesis
    unfolding trans_def
    by blast
qed

lemma transTerminationLessState1I:
assumes 
  "(x, y) \<in> terminationLessState1 Vbl"
  "(y, z) \<in> terminationLessState1 Vbl"
shows
  "(x, z) \<in> terminationLessState1 Vbl"
using assms
using transTerminationLessState1[of "Vbl"]
unfolding trans_def
by blast


lemma TerminationLessAfterExhaustiveUnitPropagate:
assumes
  "exhaustiveUnitPropagate_dom state"
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
  "getSATFlag state = UNDEF"
shows
"let state' = exhaustiveUnitPropagate state in
    state' = state \<or> (state', state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
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
      by (simp add: Let_def)
  next
    case False
    let ?state'' = "applyUnitPropagate state'"

    have "exhaustiveUnitPropagate state' = exhaustiveUnitPropagate ?state''"
      using exhaustiveUnitPropagate.simps[of "state'"]
      using False
      by simp
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
      using False
      using InvariantsVarsAfterApplyUnitPropagate[of "state'" "F0" "Vbl"]
      by (auto simp add: Let_def)
    moreover
    have "InvariantVarsF (getF ?state'') F0 Vbl"
      unfolding applyUnitPropagate_def
      using assertLiteralEffect[of "state'" "hd (getQ state')" "False"]
      using ih
      by (simp add: Let_def)
    moreover
    have "getSATFlag ?state'' = UNDEF"
      unfolding applyUnitPropagate_def
      using \<open>InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state')\<close>
      using \<open>InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state')\<close>
      using \<open>getSATFlag state' = UNDEF\<close>
      using assertLiteralEffect[of "state'" "hd (getQ state')" "False"]
      by (simp add: Let_def)
    ultimately
    have *: "exhaustiveUnitPropagate state' = applyUnitPropagate state' \<or> 
            (exhaustiveUnitPropagate state', applyUnitPropagate state') \<in> terminationLessState1 (vars F0 \<union> Vbl)"
      using ih
      using False
      using \<open>exhaustiveUnitPropagate state' = exhaustiveUnitPropagate ?state''\<close>
      by (simp add: Let_def)
    moreover
    have "(?state'', state') \<in> terminationLessState1 (vars F0 \<union> Vbl)"
      using applyUnitPropagateEffect[of "state'"]
      using lexLessAppend[of "[(hd (getQ state'), False)]" "getM state'"]
      using False
      using \<open>InvariantUniq (getM state')\<close>
      using \<open>InvariantConsistent (getM state')\<close>
      using \<open>InvariantVarsM (getM state') F0 Vbl\<close>
      using \<open>InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state')\<close>
      using \<open>InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state')\<close>
      using \<open>InvariantQCharacterization (getConflictFlag state') (getQ state') (getF state') (getM state')\<close>
      using \<open>InvariantUniq (getM ?state'')\<close>
      using \<open>InvariantConsistent (getM ?state'')\<close>
      using \<open>InvariantVarsM (getM ?state'') F0 Vbl\<close>
      using \<open>getSATFlag state' = UNDEF\<close>
      using \<open>getSATFlag ?state'' = UNDEF\<close>
      unfolding terminationLessState1_def
      unfolding lexLessState1_def
      unfolding lexLessRestricted_def
      unfolding InvariantUniq_def
      unfolding InvariantConsistent_def
      unfolding InvariantVarsM_def
      by (auto simp add: Let_def)
    ultimately
    show ?thesis
      using transTerminationLessState1I[of "exhaustiveUnitPropagate state'" "applyUnitPropagate state'" "vars F0 \<union> Vbl" "state'"]
      by (auto simp add: Let_def)
  qed
qed


lemma InvariantsAfterSolveLoopBody:
assumes
  "getSATFlag state = UNDEF"
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantUniqQ (getQ state)" and
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)" and
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)" and
  "InvariantNoDecisionsWhenConflict (getF state) (getM state) (currentLevel (getM state))" and
  "InvariantNoDecisionsWhenUnit (getF state) (getM state) (currentLevel (getM state))" and
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))" and
  "InvariantEquivalentZL (getF state) (getM state) F0'" and
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)" and
  "finite Vbl"
  "vars F0' \<subseteq> vars F0"
  "vars F0 \<subseteq> Vbl"
  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsQ (getQ state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
shows
  "let state' = solve_loop_body state Vbl in
    (InvariantConsistent (getM state') \<and> 
     InvariantUniq (getM state') \<and> 
     InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state') \<and> 
     InvariantWatchesDiffer (getF state') (getWatch1 state') (getWatch2 state') \<and> 
     InvariantWatchCharacterization (getF state') (getWatch1 state') (getWatch2 state') (getM state') \<and> 
     InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state') \<and> 
     InvariantWatchListsUniq (getWatchList state') \<and> 
     InvariantWatchListsCharacterization (getWatchList state') (getWatch1 state') (getWatch2 state') \<and> 
     InvariantQCharacterization (getConflictFlag state') (getQ state') (getF state') (getM state') \<and> 
     InvariantConflictFlagCharacterization (getConflictFlag state') (getF state') (getM state') \<and> 
     InvariantConflictClauseCharacterization (getConflictFlag state') (getConflictClause state') (getF state') (getM state') \<and> 
     InvariantUniqQ (getQ state')) \<and> 
    (InvariantNoDecisionsWhenConflict (getF state') (getM state') (currentLevel (getM state')) \<and> 
     InvariantNoDecisionsWhenUnit (getF state') (getM state') (currentLevel (getM state'))) \<and>
     InvariantEquivalentZL (getF state') (getM state') F0' \<and>  
     InvariantGetReasonIsReason (getReason state') (getF state') (getM state') (set (getQ state')) \<and> 
     InvariantVarsM (getM state') F0 Vbl \<and> 
     InvariantVarsQ (getQ state') F0 Vbl \<and> 
     InvariantVarsF (getF state') F0 Vbl \<and> 
     (state', state) \<in> terminationLessState1 (vars F0 \<union> Vbl) \<and> 
    ((getSATFlag state' = FALSE \<longrightarrow> \<not> satisfiable F0') \<and> 
     (getSATFlag state' = TRUE  \<longrightarrow> satisfiable F0'))" 
     (is "let state' = solve_loop_body state Vbl in ?inv' state' \<and> ?inv'' state' \<and> _ ")
proof-
  let ?state_up = "exhaustiveUnitPropagate state"

  have "exhaustiveUnitPropagate_dom state"
    using exhaustiveUnitPropagateTermination[of "state" "F0" "Vbl"]
    using assms
    by simp

  have "?inv' ?state_up"
    using assms
    using \<open>exhaustiveUnitPropagate_dom state\<close>
    using InvariantsAfterExhaustiveUnitPropagate[of "state"]
    using InvariantConflictClauseCharacterizationAfterExhaustivePropagate[of "state"]
    by (simp add: Let_def)
  have "?inv'' ?state_up"
    using assms
    using \<open>exhaustiveUnitPropagate_dom state\<close>
    using InvariantsNoDecisionsWhenConflictNorUnitAfterExhaustivePropagate[of "state"]
    by (simp add: Let_def)
  have "InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'"
    using assms
    using \<open>exhaustiveUnitPropagate_dom state\<close>
    using InvariantEquivalentZLAfterExhaustiveUnitPropagate[of "state"]
    by (simp add: Let_def)
  have "InvariantGetReasonIsReason (getReason ?state_up) (getF ?state_up) (getM ?state_up) (set (getQ ?state_up))"
    using assms
    using \<open>exhaustiveUnitPropagate_dom state\<close>
    using InvariantGetReasonIsReasonAfterExhaustiveUnitPropagate[of "state"]
    by (simp add: Let_def)
  have "getSATFlag ?state_up = getSATFlag state"
    using exhaustiveUnitPropagatePreservedVariables[of "state"]
    using assms
    using \<open>exhaustiveUnitPropagate_dom state\<close>
    by (simp add: Let_def)
  have "getConflictFlag ?state_up \<or> getQ ?state_up = []"
    using conflictFlagOrQEmptyAfterExhaustiveUnitPropagate[of "state"]
    using \<open>exhaustiveUnitPropagate_dom state\<close>
    by (simp add: Let_def)
  have "InvariantVarsM (getM ?state_up) F0 Vbl" 
       "InvariantVarsQ (getQ ?state_up) F0 Vbl"
       "InvariantVarsF (getF ?state_up) F0 Vbl"
    using assms
    using \<open>exhaustiveUnitPropagate_dom state\<close>
    using InvariantsAfterExhaustiveUnitPropagate[of "state" "F0" "Vbl"]
    by (auto simp add: Let_def)

  have "?state_up = state \<or> (?state_up, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
    using assms
    using TerminationLessAfterExhaustiveUnitPropagate[of "state"]
    using \<open>exhaustiveUnitPropagate_dom state\<close>
    by (simp add: Let_def)
  
  show ?thesis
  proof(cases "getConflictFlag ?state_up")
    case True
    show ?thesis
    proof (cases "currentLevel (getM ?state_up) = 0")
      case True
      hence "prefixToLevel 0 (getM ?state_up) = (getM ?state_up)"
        using currentLevelZeroTrailEqualsItsPrefixToLevelZero[of "getM ?state_up"]
        by simp
      moreover
      have "formulaFalse (getF ?state_up) (elements (getM ?state_up))"
        using \<open>getConflictFlag ?state_up\<close>
        using \<open>?inv' ?state_up\<close>
        unfolding InvariantConflictFlagCharacterization_def
        by simp
      ultimately
      have "\<not> satisfiable F0'"
        using \<open>InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'\<close>
        unfolding InvariantEquivalentZL_def
        using soundnessForUNSAT[of "getF ?state_up" "elements (getM ?state_up)" "F0'"]
        by simp
      moreover
      let ?state' = "?state_up \<lparr> getSATFlag := FALSE \<rparr>"
      have "(?state', state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
        unfolding terminationLessState1_def
        unfolding satFlagLessState_def
        using \<open>getSATFlag state = UNDEF\<close>
        by simp
      ultimately
      show ?thesis
        using \<open>?inv' ?state_up\<close>
        using \<open>?inv'' ?state_up\<close>
        using \<open>InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'\<close>
        using \<open>InvariantGetReasonIsReason (getReason ?state_up) (getF ?state_up)  (getM ?state_up) (set (getQ ?state_up))\<close>
        using \<open>InvariantVarsM (getM ?state_up) F0 Vbl\<close>
        using \<open>InvariantVarsQ (getQ ?state_up) F0 Vbl\<close>
        using \<open>InvariantVarsF (getF ?state_up) F0 Vbl\<close>
        using \<open>getConflictFlag ?state_up\<close>
        using \<open>currentLevel (getM ?state_up) = 0\<close>
        unfolding solve_loop_body_def
        by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof-
          (* APPLY CONFICT *)
        let ?state_c = "applyConflict ?state_up"

        have "?inv' ?state_c" 
          "?inv'' ?state_c"
          "getConflictFlag ?state_c"
          "InvariantEquivalentZL (getF ?state_c) (getM ?state_c) F0'"
          "currentLevel (getM ?state_c) > 0"
          using \<open>?inv' ?state_up\<close> \<open>?inv'' ?state_up\<close>
          using \<open>getConflictFlag ?state_up\<close>
          using \<open>InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'\<close>
          using \<open>currentLevel (getM ?state_up) \<noteq> 0\<close>
          unfolding applyConflict_def
          unfolding setConflictAnalysisClause_def
          by (auto simp add: Let_def findLastAssertedLiteral_def countCurrentLevelLiterals_def)

        have "InvariantCFalse (getConflictFlag ?state_c) (getM ?state_c) (getC ?state_c)"
             "InvariantCEntailed (getConflictFlag ?state_c) F0' (getC ?state_c)"
             "InvariantClCharacterization (getCl ?state_c) (getC ?state_c) (getM ?state_c)"
             "InvariantCnCharacterization (getCn ?state_c) (getC ?state_c) (getM ?state_c)"
             "InvariantClCurrentLevel (getCl ?state_c) (getM ?state_c)"
             "InvariantUniqC (getC ?state_c)"
          using \<open>getConflictFlag ?state_up\<close>
          using \<open>currentLevel (getM ?state_up) \<noteq> 0\<close>
          using \<open>?inv' ?state_up\<close>
          using \<open>?inv'' ?state_up\<close>
          using \<open>InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'\<close>
          using InvariantsClAfterApplyConflict[of "?state_up"]
          by (auto simp only: Let_def)

        have "getSATFlag ?state_c = getSATFlag state"
          using \<open>getSATFlag ?state_up = getSATFlag state\<close>
          unfolding applyConflict_def
          unfolding setConflictAnalysisClause_def
          by (simp add: Let_def findLastAssertedLiteral_def countCurrentLevelLiterals_def)

        have "getReason ?state_c = getReason ?state_up"
          "getF ?state_c = getF ?state_up"
          "getM ?state_c = getM ?state_up"
          "getQ ?state_c = getQ ?state_up"
          unfolding applyConflict_def
          unfolding setConflictAnalysisClause_def
          by (auto simp add: Let_def findLastAssertedLiteral_def countCurrentLevelLiterals_def)
        hence "InvariantGetReasonIsReason (getReason ?state_c) (getF ?state_c) (getM ?state_c) (set (getQ ?state_c))"
          "InvariantVarsM (getM ?state_c) F0 Vbl" 
          "InvariantVarsQ (getQ ?state_c) F0 Vbl"
          "InvariantVarsF (getF ?state_c) F0 Vbl"         
          using \<open>InvariantGetReasonIsReason (getReason ?state_up) (getF ?state_up) (getM ?state_up) (set (getQ ?state_up))\<close>
          using \<open>InvariantVarsM (getM ?state_up) F0 Vbl\<close>
          using \<open>InvariantVarsQ (getQ ?state_up) F0 Vbl\<close>
          using \<open>InvariantVarsF (getF ?state_up) F0 Vbl\<close>
          by auto


        have "getM ?state_c = getM state \<or> (?state_c, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
          using \<open>?state_up = state \<or> (?state_up, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)\<close>
          using \<open>getM ?state_c = getM ?state_up\<close>
          using \<open>getSATFlag ?state_c = getSATFlag state\<close>
          using \<open>InvariantUniq (getM state)\<close>
          using \<open>InvariantConsistent (getM state)\<close>
          using \<open>InvariantVarsM (getM state) F0 Vbl\<close>
          using \<open>?inv' ?state_up\<close>
          using \<open>InvariantVarsM (getM ?state_up) F0 Vbl\<close>
          using \<open>getSATFlag ?state_up = getSATFlag state\<close>
          using \<open>getSATFlag state = UNDEF\<close>
          unfolding InvariantConsistent_def
          unfolding InvariantUniq_def
          unfolding InvariantVarsM_def
          unfolding terminationLessState1_def
          unfolding satFlagLessState_def
          unfolding lexLessState1_def
          unfolding lexLessRestricted_def
          by auto


          (*    APPLY EXPLAIN UIP    *)
          
        let ?state_euip = "applyExplainUIP ?state_c"
        let ?l' = "getCl ?state_euip"

        have "applyExplainUIP_dom ?state_c"
          using ApplyExplainUIPTermination[of "?state_c" "F0'"]
          using \<open>getConflictFlag ?state_c\<close>
          using \<open>InvariantEquivalentZL (getF ?state_c) (getM ?state_c) F0'\<close>
          using \<open>currentLevel (getM ?state_c) > 0\<close>
          using \<open>?inv' ?state_c\<close>
          using \<open>InvariantCFalse (getConflictFlag ?state_c) (getM ?state_c) (getC ?state_c)\<close>
          using \<open>InvariantCEntailed (getConflictFlag ?state_c) F0' (getC ?state_c)\<close>
          using \<open>InvariantClCharacterization (getCl ?state_c) (getC ?state_c) (getM ?state_c)\<close>
          using \<open>InvariantCnCharacterization (getCn ?state_c) (getC ?state_c) (getM ?state_c)\<close>
          using \<open>InvariantClCurrentLevel (getCl ?state_c) (getM ?state_c)\<close>
          using \<open>InvariantGetReasonIsReason (getReason ?state_c) (getF ?state_c) (getM ?state_c) (set (getQ ?state_c))\<close>
          by simp
        
        
        have "?inv' ?state_euip" "?inv'' ?state_euip"
          using \<open>?inv' ?state_c\<close> \<open>?inv'' ?state_c\<close>
          using \<open>applyExplainUIP_dom ?state_c\<close>
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          by (auto simp add: Let_def)

        have "InvariantCFalse (getConflictFlag ?state_euip) (getM ?state_euip) (getC ?state_euip)"
          "InvariantCEntailed (getConflictFlag ?state_euip) F0' (getC ?state_euip)"
          "InvariantClCharacterization (getCl ?state_euip) (getC ?state_euip) (getM ?state_euip)"
          "InvariantCnCharacterization (getCn ?state_euip) (getC ?state_euip) (getM ?state_euip)"
          "InvariantClCurrentLevel (getCl ?state_euip) (getM ?state_euip)"
          "InvariantUniqC (getC ?state_euip)"
          using \<open>?inv' ?state_c\<close>
          using \<open>InvariantCFalse (getConflictFlag ?state_c) (getM ?state_c) (getC ?state_c)\<close>
          using \<open>InvariantCEntailed (getConflictFlag ?state_c) F0' (getC ?state_c)\<close>
          using \<open>InvariantClCharacterization (getCl ?state_c) (getC ?state_c) (getM ?state_c)\<close>
          using \<open>InvariantCnCharacterization (getCn ?state_c) (getC ?state_c) (getM ?state_c)\<close>
          using \<open>InvariantClCurrentLevel (getCl ?state_c) (getM ?state_c)\<close>
          using \<open>InvariantEquivalentZL (getF ?state_c) (getM ?state_c) F0'\<close>
          using \<open>InvariantUniqC (getC ?state_c)\<close>
          using \<open>getConflictFlag ?state_c\<close>
          using \<open>currentLevel (getM ?state_c) > 0\<close>
          using \<open>InvariantGetReasonIsReason (getReason ?state_c) (getF ?state_c) (getM ?state_c) (set (getQ ?state_c))\<close>
          using \<open>applyExplainUIP_dom ?state_c\<close>
          using InvariantsClAfterExplainUIP[of "?state_c" "F0'"]
          by (auto simp only: Let_def)

        have "InvariantEquivalentZL (getF ?state_euip) (getM ?state_euip) F0'"
          using \<open>InvariantEquivalentZL (getF ?state_c) (getM ?state_c) F0'\<close>
          using \<open>applyExplainUIP_dom ?state_c\<close>
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          by (simp only: Let_def)

        have "InvariantGetReasonIsReason (getReason ?state_euip) (getF ?state_euip) (getM ?state_euip) (set (getQ ?state_euip))"
          using \<open>InvariantGetReasonIsReason (getReason ?state_c) (getF ?state_c) (getM ?state_c) (set (getQ ?state_c))\<close>
          using \<open>applyExplainUIP_dom ?state_c\<close>
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          by (simp only: Let_def)

        have "getConflictFlag ?state_euip"
          using \<open>getConflictFlag ?state_c\<close>
          using \<open>applyExplainUIP_dom ?state_c\<close>
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          by (simp add: Let_def)

        hence "getSATFlag ?state_euip = getSATFlag state"
          using \<open>getSATFlag ?state_c = getSATFlag state\<close>
          using \<open>applyExplainUIP_dom ?state_c\<close>
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          by (simp add: Let_def)

        have "isUIP (opposite (getCl ?state_euip)) (getC ?state_euip) (getM ?state_euip)"
          using \<open>applyExplainUIP_dom ?state_c\<close>
          using \<open>?inv' ?state_c\<close>
          using \<open>InvariantCFalse (getConflictFlag ?state_c) (getM ?state_c) (getC ?state_c)\<close>
          using \<open>InvariantCEntailed (getConflictFlag ?state_c) F0' (getC ?state_c)\<close>
          using \<open>InvariantClCharacterization (getCl ?state_c) (getC ?state_c) (getM ?state_c)\<close>
          using \<open>InvariantCnCharacterization (getCn ?state_c) (getC ?state_c) (getM ?state_c)\<close>
          using \<open>InvariantClCurrentLevel (getCl ?state_c) (getM ?state_c)\<close>
          using \<open>InvariantGetReasonIsReason (getReason ?state_c) (getF ?state_c) (getM ?state_c) (set (getQ ?state_c))\<close>
          using \<open>InvariantEquivalentZL (getF ?state_c) (getM ?state_c) F0'\<close>
          using \<open>getConflictFlag ?state_c\<close>
          using \<open>currentLevel (getM ?state_c) > 0\<close>
          using isUIPApplyExplainUIP[of "?state_c"]
          by (simp add: Let_def)

        have "currentLevel (getM ?state_euip) > 0"
          using \<open>applyExplainUIP_dom ?state_c\<close>
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          using \<open>currentLevel (getM ?state_c) > 0\<close>
          by (simp add: Let_def)

        have "InvariantVarsM (getM ?state_euip) F0 Vbl" 
             "InvariantVarsQ (getQ ?state_euip) F0 Vbl"
             "InvariantVarsF (getF ?state_euip) F0 Vbl"
          using \<open>InvariantVarsM (getM ?state_c) F0 Vbl\<close>
          using \<open>InvariantVarsQ (getQ ?state_c) F0 Vbl\<close>
          using \<open>InvariantVarsF (getF ?state_c) F0 Vbl\<close>
          using \<open>applyExplainUIP_dom ?state_c\<close>
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          by (auto simp add: Let_def)

        have "getM ?state_euip = getM state \<or> (?state_euip, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
          using \<open>getM ?state_c = getM state \<or> (?state_c, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)\<close>
          using \<open>applyExplainUIP_dom ?state_c\<close>
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          unfolding terminationLessState1_def
          unfolding satFlagLessState_def
          unfolding lexLessState1_def
          unfolding lexLessRestricted_def
          by (simp add: Let_def)

            (*    APPLY LEARN    *)
        let ?state_l = "applyLearn ?state_euip"
        let ?l'' = "getCl ?state_l"

        have $: "getM ?state_l = getM ?state_euip \<and> 
                 getQ ?state_l = getQ ?state_euip \<and> 
                 getC ?state_l = getC ?state_euip \<and> 
                 getCl ?state_l = getCl ?state_euip \<and>
                 getConflictFlag ?state_l = getConflictFlag ?state_euip \<and> 
                 getConflictClause ?state_l = getConflictClause ?state_euip \<and> 
                 getF ?state_l = (if getC ?state_euip = [opposite ?l'] then 
                                     getF ?state_euip 
                                  else 
                                     (getF ?state_euip @ [getC ?state_euip])
                                 )"
          using applyLearnPreservedVariables[of "?state_euip"]
          by (simp add: Let_def)

        have "?inv' ?state_l"
        proof-
          have "InvariantConflictFlagCharacterization (getConflictFlag ?state_l) (getF ?state_l) (getM ?state_l)"
            using \<open>?inv' ?state_euip\<close>
            using \<open>getConflictFlag ?state_euip\<close>
            using InvariantConflictFlagCharacterizationAfterApplyLearn[of "?state_euip"]
            by (simp add: Let_def)
          moreover
          hence "InvariantQCharacterization (getConflictFlag ?state_l) (getQ ?state_l) (getF ?state_l) (getM ?state_l)"
            using \<open>?inv' ?state_euip\<close>
            using \<open>getConflictFlag ?state_euip\<close>
            using InvariantQCharacterizationAfterApplyLearn[of "?state_euip"]
            by (simp add: Let_def)
          moreover
          have "InvariantUniqQ (getQ ?state_l)"
            using \<open>?inv' ?state_euip\<close>
            using InvariantUniqQAfterApplyLearn[of "?state_euip"]
            by (simp add: Let_def)
          moreover
          have "InvariantConflictClauseCharacterization (getConflictFlag ?state_l) (getConflictClause ?state_l) (getF ?state_l) (getM ?state_l)"
            using \<open>?inv' ?state_euip\<close>
            using \<open>getConflictFlag ?state_euip\<close>
            using InvariantConflictClauseCharacterizationAfterApplyLearn[of "?state_euip"]
            by (simp only: Let_def)
          ultimately
          show ?thesis
            using \<open>?inv' ?state_euip\<close>
            using \<open>getConflictFlag ?state_euip\<close>
            using \<open>InvariantUniqC (getC ?state_euip)\<close>
            using \<open>InvariantCFalse (getConflictFlag ?state_euip) (getM ?state_euip) (getC ?state_euip)\<close>
            using \<open>InvariantClCharacterization (getCl ?state_euip) (getC ?state_euip) (getM ?state_euip)\<close>
            using \<open>isUIP (opposite (getCl ?state_euip)) (getC ?state_euip) (getM ?state_euip)\<close>
            using WatchInvariantsAfterApplyLearn[of "?state_euip"]
            using $
            by (auto simp only: Let_def)
        qed

        have "InvariantNoDecisionsWhenConflict (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))"
             "InvariantNoDecisionsWhenUnit (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))"
             "InvariantNoDecisionsWhenConflict [getC ?state_euip] (getM ?state_l) (getBackjumpLevel ?state_l)"
             "InvariantNoDecisionsWhenUnit [getC ?state_euip] (getM ?state_l) (getBackjumpLevel ?state_l)"
          using InvariantNoDecisionsWhenConflictNorUnitAfterApplyLearn[of "?state_euip"]
          using \<open>?inv' ?state_euip\<close>
          using \<open>?inv'' ?state_euip\<close>
          using \<open>getConflictFlag ?state_euip\<close>
          using \<open>InvariantUniqC (getC ?state_euip)\<close>
          using \<open>InvariantCFalse (getConflictFlag ?state_euip) (getM ?state_euip) (getC ?state_euip)\<close>
          using \<open>InvariantClCharacterization (getCl ?state_euip) (getC ?state_euip) (getM ?state_euip)\<close>
          using \<open>InvariantClCurrentLevel (getCl ?state_euip) (getM ?state_euip)\<close>
          using \<open>isUIP (opposite (getCl ?state_euip)) (getC ?state_euip) (getM ?state_euip)\<close>
          using \<open>currentLevel (getM ?state_euip) > 0\<close>
          by (auto simp only: Let_def)
        

        have "isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)"
          using \<open>isUIP (opposite (getCl ?state_euip)) (getC ?state_euip) (getM ?state_euip)\<close>
          using $
          by simp

        have "InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)"
          using \<open>InvariantClCurrentLevel (getCl ?state_euip) (getM ?state_euip)\<close>
          using $
          by simp

        have "InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)"
          using \<open>InvariantCEntailed (getConflictFlag ?state_euip) F0' (getC ?state_euip)\<close>
          using $
          unfolding InvariantCEntailed_def
          by simp

        have "InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)"
          using \<open>InvariantCFalse (getConflictFlag ?state_euip) (getM ?state_euip) (getC ?state_euip)\<close>
          using $
          by simp

        have "InvariantUniqC (getC ?state_l)"
          using \<open>InvariantUniqC (getC ?state_euip)\<close>
          using $
          by simp

        have "InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)"
          using \<open>InvariantClCharacterization (getCl ?state_euip) (getC ?state_euip) (getM ?state_euip)\<close>
          unfolding applyLearn_def
          unfolding setWatch1_def
          unfolding setWatch2_def
          by (auto simp add:Let_def)

        have "InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)"
          using \<open>InvariantClCharacterization (getCl ?state_euip) (getC ?state_euip) (getM ?state_euip)\<close>
            \<open>InvariantUniqC (getC ?state_euip)\<close>
            \<open>InvariantCFalse (getConflictFlag ?state_euip) (getM ?state_euip) (getC ?state_euip)\<close>
            \<open>getConflictFlag ?state_euip\<close>
            \<open>?inv' ?state_euip\<close>
          using InvariantCllCharacterizationAfterApplyLearn[of "?state_euip"]
          by (simp add: Let_def)

        have "InvariantEquivalentZL (getF ?state_l) (getM ?state_l) F0'"
          using \<open>InvariantEquivalentZL (getF ?state_euip) (getM ?state_euip) F0'\<close>
          using \<open>getConflictFlag ?state_euip\<close>
          using InvariantEquivalentZLAfterApplyLearn[of "?state_euip" "F0'"]
          using \<open>InvariantCEntailed (getConflictFlag ?state_euip) F0' (getC ?state_euip)\<close>
          by (simp add: Let_def)

        have "InvariantGetReasonIsReason (getReason ?state_l) (getF ?state_l) (getM ?state_l) (set (getQ ?state_l))"
          using \<open>InvariantGetReasonIsReason (getReason ?state_euip) (getF ?state_euip) (getM ?state_euip) (set (getQ ?state_euip))\<close>
          using InvariantGetReasonIsReasonAfterApplyLearn[of "?state_euip"]
          by (simp only: Let_def)

        have "InvariantVarsM (getM ?state_l) F0 Vbl" 
          "InvariantVarsQ (getQ ?state_l) F0 Vbl"
          "InvariantVarsF (getF ?state_l) F0 Vbl"
          using \<open>InvariantVarsM (getM ?state_euip) F0 Vbl\<close>
          using \<open>InvariantVarsQ (getQ ?state_euip) F0 Vbl\<close>
          using \<open>InvariantVarsF (getF ?state_euip) F0 Vbl\<close>
          using $
          using \<open>InvariantCFalse (getConflictFlag ?state_euip) (getM ?state_euip) (getC ?state_euip)\<close> 
          using \<open>getConflictFlag ?state_euip\<close>
          using InvariantVarsFAfterApplyLearn[of "?state_euip" "F0" "Vbl"]
          by auto

        have "getConflictFlag ?state_l"
          using \<open>getConflictFlag ?state_euip\<close>
          using $
          by simp

        have "getSATFlag ?state_l = getSATFlag state"
          using \<open>getSATFlag ?state_euip = getSATFlag state\<close>
          unfolding applyLearn_def
          unfolding setWatch2_def
          unfolding setWatch1_def
          by (simp add: Let_def)


        have "currentLevel (getM ?state_l) > 0"
          using \<open>currentLevel (getM ?state_euip) > 0\<close>
          using $
          by simp

        have "getM ?state_l = getM state \<or> (?state_l, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
        proof (cases "getM ?state_euip = getM state")
          case True
          thus ?thesis
            using $
            by simp
        next
          case False
          with \<open>getM ?state_euip = getM state \<or> (?state_euip, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)\<close>
          have "(?state_euip, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
            by simp
          hence "(?state_l, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
            using $
            using \<open>getSATFlag ?state_l = getSATFlag state\<close>
            using \<open>getSATFlag ?state_euip = getSATFlag state\<close>
            unfolding terminationLessState1_def
            unfolding satFlagLessState_def
            unfolding lexLessState1_def
            unfolding lexLessRestricted_def
            by (simp add: Let_def)
          thus ?thesis
            by simp
        qed

      (*    APPLY BACKJUMP    *)
        let ?state_bj = "applyBackjump ?state_l"
        
        have "?inv' ?state_bj \<and> 
           InvariantVarsM (getM ?state_bj) F0 Vbl \<and> 
           InvariantVarsQ (getQ ?state_bj) F0 Vbl \<and> 
           InvariantVarsF (getF ?state_bj) F0 Vbl"
        proof (cases "getC ?state_l = [opposite ?l'']")
          case True
          thus ?thesis
            using WatchInvariantsAfterApplyBackjump[of "?state_l" "F0'"]
            using InvariantUniqAfterApplyBackjump[of "?state_l" "F0'"]
            using InvariantConsistentAfterApplyBackjump[of "?state_l" "F0'"]
            using invariantQCharacterizationAfterApplyBackjump_1[of "?state_l" "F0'"]
            using InvariantConflictFlagCharacterizationAfterApplyBackjump_1[of "?state_l" "F0'"]
            using InvariantUniqQAfterApplyBackjump[of "?state_l"]
            using InvariantConflictClauseCharacterizationAfterApplyBackjump[of "?state_l"]
            using InvariantsVarsAfterApplyBackjump[of "?state_l" "F0'" "F0" "Vbl"]
            using \<open>?inv' ?state_l\<close>
            using \<open>getConflictFlag ?state_l\<close>
            using \<open>InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)\<close>
            using \<open>InvariantUniqC (getC ?state_l)\<close>
            using \<open>InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)\<close>
            using \<open>InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)\<close>
            using \<open>InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)\<close>
            using \<open>InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)\<close>
            using \<open>isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)\<close>
            using \<open>currentLevel (getM ?state_l) > 0\<close>
            using \<open>InvariantNoDecisionsWhenConflict (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))\<close>
            using \<open>InvariantNoDecisionsWhenUnit (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))\<close>
            using \<open>InvariantEquivalentZL (getF ?state_l) (getM ?state_l) F0'\<close>
            using \<open>InvariantVarsM (getM ?state_l) F0 Vbl\<close>
            using \<open>InvariantVarsQ (getQ ?state_l) F0 Vbl\<close>
            using \<open>InvariantVarsF (getF ?state_l) F0 Vbl\<close>
            using \<open>vars F0' \<subseteq> vars F0\<close>
            using $
            by (simp add: Let_def)
        next
          case False
          thus ?thesis
            using WatchInvariantsAfterApplyBackjump[of "?state_l" "F0'"]
            using InvariantUniqAfterApplyBackjump[of "?state_l" "F0'"]
            using InvariantConsistentAfterApplyBackjump[of "?state_l" "F0'"]
            using invariantQCharacterizationAfterApplyBackjump_2[of "?state_l" "F0'"]
            using InvariantConflictFlagCharacterizationAfterApplyBackjump_2[of "?state_l" "F0'"]
            using InvariantUniqQAfterApplyBackjump[of "?state_l"]
            using InvariantConflictClauseCharacterizationAfterApplyBackjump[of "?state_l"]
            using InvariantsVarsAfterApplyBackjump[of "?state_l" "F0'" "F0" "Vbl"]
            using \<open>?inv' ?state_l\<close>
            using \<open>getConflictFlag ?state_l\<close>
            using \<open>InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)\<close>
            using \<open>InvariantUniqC (getC ?state_l)\<close>
            using \<open>InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)\<close>
            using \<open>InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)\<close>
            using \<open>InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)\<close>
            using \<open>InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)\<close>
            using \<open>isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)\<close>
            using \<open>currentLevel (getM ?state_l) > 0\<close>
            using \<open>InvariantNoDecisionsWhenConflict (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))\<close>
            using \<open>InvariantNoDecisionsWhenUnit (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))\<close>
            using \<open>InvariantNoDecisionsWhenConflict [getC ?state_euip] (getM ?state_l) (getBackjumpLevel ?state_l)\<close>
            using \<open>InvariantNoDecisionsWhenUnit [getC ?state_euip] (getM ?state_l) (getBackjumpLevel ?state_l)\<close>
            using $
            using \<open>InvariantEquivalentZL (getF ?state_l) (getM ?state_l) F0'\<close>
            using \<open>InvariantVarsM (getM ?state_l) F0 Vbl\<close>
            using \<open>InvariantVarsQ (getQ ?state_l) F0 Vbl\<close>
            using \<open>InvariantVarsF (getF ?state_l) F0 Vbl\<close>
            using \<open>vars F0' \<subseteq> vars F0\<close>
            by (simp add: Let_def)
        qed

        have "?inv'' ?state_bj"
        proof (cases "getC ?state_l = [opposite ?l'']")
          case True
          thus ?thesis
            using InvariantsNoDecisionsWhenConflictNorUnitAfterApplyBackjump_1[of "?state_l" "F0'"]
            using \<open>?inv' ?state_l\<close>
            using \<open>getConflictFlag ?state_l\<close>
            using \<open>InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)\<close>
            using \<open>InvariantUniqC (getC ?state_l)\<close>
            using \<open>InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)\<close>
            using \<open>InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)\<close>
            using \<open>InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)\<close>
            using \<open>InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)\<close>
            using \<open>isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)\<close>
            using \<open>currentLevel (getM ?state_l) > 0\<close>
            using \<open>InvariantNoDecisionsWhenConflict (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))\<close>
            using \<open>InvariantNoDecisionsWhenUnit (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))\<close>
            using $
            by (simp add: Let_def)
        next
          case False
          thus ?thesis
            using InvariantsNoDecisionsWhenConflictNorUnitAfterApplyBackjump_2[of "?state_l"]
            using \<open>?inv' ?state_l\<close>
            using \<open>getConflictFlag ?state_l\<close>
            using \<open>InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)\<close>
            using \<open>InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)\<close>
            using \<open>InvariantUniqC (getC ?state_l)\<close>
            using \<open>InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)\<close>
            using \<open>InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)\<close>
            using \<open>InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)\<close>
            using \<open>isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)\<close>
            using \<open>currentLevel (getM ?state_l) > 0\<close>
            using \<open>InvariantNoDecisionsWhenConflict (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))\<close>
            using \<open>InvariantNoDecisionsWhenUnit (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))\<close>
            using \<open>InvariantNoDecisionsWhenConflict [getC ?state_euip] (getM ?state_l) (getBackjumpLevel ?state_l)\<close>
            using \<open>InvariantNoDecisionsWhenUnit [getC ?state_euip] (getM ?state_l) (getBackjumpLevel ?state_l)\<close>
            using $
            by (simp add: Let_def)
        qed

        

        have "getBackjumpLevel ?state_l > 0 \<longrightarrow> (getF ?state_l) \<noteq> [] \<and> (last (getF ?state_l) = (getC ?state_l))"
        proof (cases "getC ?state_l = [opposite ?l'']")
          case True
          thus ?thesis
            unfolding getBackjumpLevel_def
            by simp
        next
          case False
          thus ?thesis
            using $
            by simp
        qed
        hence "InvariantGetReasonIsReason (getReason ?state_bj) (getF ?state_bj) (getM ?state_bj) (set (getQ ?state_bj))"
          using \<open>InvariantGetReasonIsReason (getReason ?state_l) (getF ?state_l) (getM ?state_l) (set (getQ ?state_l))\<close>
          using \<open>?inv' ?state_l\<close>
          using \<open>getConflictFlag ?state_l\<close>
          using \<open>isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)\<close>
          using \<open>InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)\<close>
          using \<open>InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)\<close>
          using \<open>InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)\<close>
          using \<open>InvariantUniqC (getC ?state_l)\<close>
          using \<open>InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)\<close>
          using \<open>InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)\<close>
          using \<open>currentLevel (getM ?state_l) > 0\<close>
          using InvariantGetReasonIsReasonAfterApplyBackjump[of "?state_l" "F0'"]
          by (simp only: Let_def)

        have "InvariantEquivalentZL (getF ?state_bj) (getM ?state_bj) F0'"
          using \<open>InvariantEquivalentZL (getF ?state_l) (getM ?state_l) F0'\<close>
          using \<open>?inv' ?state_l\<close>
          using \<open>getConflictFlag ?state_l\<close>
          using \<open>isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)\<close>
          using \<open>InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)\<close>
          using \<open>InvariantUniqC (getC ?state_l)\<close>
          using \<open>InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)\<close>
          using \<open>InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)\<close>
          using \<open>InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)\<close>
          using \<open>InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)\<close>
          using InvariantEquivalentZLAfterApplyBackjump[of "?state_l" "F0'"]
          using \<open>currentLevel (getM ?state_l) > 0\<close>
          by (simp only: Let_def)


        have "getSATFlag ?state_bj = getSATFlag state"
          using \<open>getSATFlag ?state_l = getSATFlag state\<close>
          using \<open>?inv' ?state_l\<close>
          using applyBackjumpPreservedVariables[of "?state_l"]
          by (simp only: Let_def)

        let ?level = "getBackjumpLevel ?state_l"
        let ?prefix = "prefixToLevel ?level (getM ?state_l)"
        let ?l = "opposite (getCl ?state_l)"

        have "isMinimalBackjumpLevel (getBackjumpLevel ?state_l) (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)"
          using isMinimalBackjumpLevelGetBackjumpLevel[of "?state_l"]
          using \<open>?inv' ?state_l\<close>
          using \<open>InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)\<close>
          using \<open>InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)\<close>
          using \<open>InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)\<close>
          using \<open>InvariantUniqC (getC ?state_l)\<close>
          using \<open>InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)\<close>
          using \<open>InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)\<close>
          using \<open>isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)\<close>
          using \<open>getConflictFlag ?state_l\<close>
          using \<open>currentLevel (getM ?state_l) > 0\<close>
          by (simp add: Let_def)
        hence "getBackjumpLevel ?state_l < elementLevel (getCl ?state_l) (getM ?state_l)"
          unfolding isMinimalBackjumpLevel_def
          unfolding isBackjumpLevel_def
          by simp
        hence "getBackjumpLevel ?state_l < currentLevel (getM ?state_l)"
          using elementLevelLeqCurrentLevel[of "getCl ?state_l" "getM ?state_l"]
          by simp
        hence "(?state_bj, ?state_l) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
          using applyBackjumpEffect[of "?state_l" "F0'"]
          using \<open>?inv' ?state_l\<close>
          using \<open>getConflictFlag ?state_l\<close>
          using \<open>isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)\<close>
          using \<open>InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)\<close>
          using \<open>InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)\<close>
          using \<open>InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)\<close>
          using \<open>InvariantUniqC (getC ?state_l)\<close>
          using \<open>InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)\<close>
          using \<open>InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)\<close>
          using \<open>currentLevel (getM ?state_l) > 0\<close>
          using lexLessBackjump[of "?prefix" "?level" "getM ?state_l" "?l"]
          using \<open>getSATFlag ?state_bj = getSATFlag state\<close>
          using \<open>getSATFlag ?state_l = getSATFlag state\<close>
          using \<open>getSATFlag state = UNDEF\<close>
          using \<open>?inv' ?state_l\<close>
          using \<open>InvariantVarsM (getM ?state_l) F0 Vbl\<close>
          using \<open>?inv' ?state_bj \<and> InvariantVarsM (getM ?state_bj) F0 Vbl \<and> 
           InvariantVarsQ (getQ ?state_bj) F0 Vbl \<and> 
           InvariantVarsF (getF ?state_bj) F0 Vbl\<close>
          unfolding InvariantConsistent_def
          unfolding InvariantUniq_def
          unfolding InvariantVarsM_def
          unfolding terminationLessState1_def
          unfolding satFlagLessState_def
          unfolding lexLessState1_def
          unfolding lexLessRestricted_def
          by (simp add: Let_def)
        hence "(?state_bj, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
          using \<open>getM ?state_l = getM state \<or> (?state_l, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)\<close>
          using \<open>getSATFlag state = UNDEF\<close>
          using \<open>getSATFlag ?state_bj = getSATFlag state\<close>
          using \<open>getSATFlag ?state_l = getSATFlag state\<close>
          using transTerminationLessState1I[of "?state_bj" "?state_l" "vars F0 \<union> Vbl" "state"]
          unfolding terminationLessState1_def
          unfolding satFlagLessState_def
          unfolding lexLessState1_def
          unfolding lexLessRestricted_def
          by auto

        show ?thesis
          using \<open>?inv' ?state_bj \<and> InvariantVarsM (getM ?state_bj) F0 Vbl \<and> 
           InvariantVarsQ (getQ ?state_bj) F0 Vbl \<and> 
           InvariantVarsF (getF ?state_bj) F0 Vbl\<close>
          using \<open>?inv'' ?state_bj\<close>
          using \<open>InvariantEquivalentZL (getF ?state_bj) (getM ?state_bj) F0'\<close>
          using \<open>InvariantGetReasonIsReason (getReason ?state_bj) (getF ?state_bj) (getM ?state_bj) (set (getQ ?state_bj))\<close>
          using \<open>getSATFlag state = UNDEF\<close>
          using \<open>getSATFlag ?state_bj = getSATFlag state\<close>
          using \<open>getConflictFlag ?state_up\<close>
          using \<open>currentLevel (getM ?state_up) \<noteq> 0\<close>
          using \<open>(?state_bj, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)\<close>
          unfolding solve_loop_body_def
          by (auto simp add: Let_def)
      qed
    qed
  next
    case False
    show ?thesis
    proof (cases "vars (elements (getM ?state_up)) \<supseteq> Vbl")
      case True
      hence "satisfiable F0'"
        using soundnessForSat[of "F0'" "Vbl" "getF ?state_up" "getM ?state_up"]
        using \<open>InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'\<close>
        using \<open>?inv' ?state_up\<close>
        using \<open>InvariantVarsF (getF ?state_up) F0 Vbl\<close>
        using \<open>\<not> getConflictFlag ?state_up\<close>
        using \<open>vars F0 \<subseteq> Vbl\<close>
        using \<open>vars F0' \<subseteq> vars F0\<close>
        using True
        unfolding InvariantConflictFlagCharacterization_def
        unfolding satisfiable_def
        unfolding InvariantVarsF_def
        by blast
      moreover
      let ?state' = "?state_up \<lparr> getSATFlag := TRUE \<rparr>"
      have "(?state', state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
        using \<open>getSATFlag state = UNDEF\<close>
        unfolding terminationLessState1_def
        unfolding satFlagLessState_def
        by simp
      ultimately
      show ?thesis
        using \<open>vars (elements (getM ?state_up)) \<supseteq> Vbl\<close>
        using \<open>?inv' ?state_up\<close>
        using \<open>?inv'' ?state_up\<close>
        using \<open>InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'\<close>
        using \<open>InvariantGetReasonIsReason (getReason ?state_up) (getF ?state_up)  (getM ?state_up) (set (getQ ?state_up))\<close>
        using \<open>InvariantVarsM (getM ?state_up) F0 Vbl\<close>
        using \<open>InvariantVarsQ (getQ ?state_up) F0 Vbl\<close>
        using \<open>InvariantVarsF (getF ?state_up) F0 Vbl\<close>
        using \<open>\<not> getConflictFlag ?state_up\<close>
        unfolding solve_loop_body_def
        by (simp add: Let_def)
    next
      case False
      let ?literal = "selectLiteral ?state_up Vbl"
      let ?state_d = "applyDecide ?state_up Vbl"
      
      have "InvariantConsistent (getM ?state_d)"
        using InvariantConsistentAfterApplyDecide [of "Vbl" "?state_up"]
        using False
        using \<open>?inv' ?state_up\<close>
        by (simp add: Let_def)
      moreover
      have "InvariantUniq (getM ?state_d)"
        using InvariantUniqAfterApplyDecide [of "Vbl" "?state_up"]
        using False
        using \<open>?inv' ?state_up\<close>
        by (simp add: Let_def)
      moreover
      have "InvariantQCharacterization (getConflictFlag ?state_d) (getQ ?state_d) (getF ?state_d) (getM ?state_d)"
        using InvariantQCharacterizationAfterApplyDecide [of "Vbl" "?state_up"]
        using False
        using \<open>?inv' ?state_up\<close>
        using \<open>\<not> getConflictFlag ?state_up\<close>
        using \<open>exhaustiveUnitPropagate_dom state\<close>
        using conflictFlagOrQEmptyAfterExhaustiveUnitPropagate[of "state"]
        by (simp add: Let_def)
      moreover
      have "InvariantConflictFlagCharacterization (getConflictFlag ?state_d) (getF ?state_d) (getM ?state_d)"
        using \<open>InvariantConsistent (getM ?state_d)\<close>
        using \<open>InvariantUniq (getM ?state_d)\<close>
        using InvariantConflictFlagCharacterizationAfterAssertLiteral[of "?state_up" "?literal" "True"]
        using \<open>?inv' ?state_up\<close>
        using assertLiteralEffect
        unfolding applyDecide_def
        by (simp only: Let_def)
      moreover
      have "InvariantConflictClauseCharacterization (getConflictFlag ?state_d) (getConflictClause ?state_d) (getF ?state_d) (getM ?state_d)"
        using InvariantConflictClauseCharacterizationAfterAssertLiteral[of "?state_up" "?literal" "True"]
        using \<open>?inv' ?state_up\<close>
        using assertLiteralEffect
        unfolding applyDecide_def
        by (simp only: Let_def)
      moreover
      have "InvariantNoDecisionsWhenConflict (getF ?state_d) (getM ?state_d) (currentLevel (getM ?state_d))"
        "InvariantNoDecisionsWhenUnit (getF ?state_d) (getM ?state_d) (currentLevel (getM ?state_d))"
        using \<open>exhaustiveUnitPropagate_dom state\<close>
        using conflictFlagOrQEmptyAfterExhaustiveUnitPropagate[of "state"]
        using \<open>\<not> getConflictFlag ?state_up\<close> 
        using \<open>?inv' ?state_up\<close>
        using \<open>?inv'' ?state_up\<close>
        using InvariantsNoDecisionsWhenConflictNorUnitAfterAssertLiteral[of "?state_up" "True" "?literal"]
        unfolding applyDecide_def
        by (auto simp add: Let_def)
      moreover
      have "InvariantEquivalentZL (getF ?state_d) (getM ?state_d) F0'"
        using InvariantEquivalentZLAfterApplyDecide[of "?state_up" "F0'" "Vbl"]
        using \<open>?inv' ?state_up\<close>
        using \<open>InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'\<close>
        by (simp add: Let_def)
      moreover
      have "InvariantGetReasonIsReason (getReason ?state_d) (getF ?state_d) (getM ?state_d) (set (getQ ?state_d))"
        using InvariantGetReasonIsReasonAfterApplyDecide[of "Vbl" "?state_up"]
        using \<open>?inv' ?state_up\<close>
        using \<open>InvariantGetReasonIsReason (getReason ?state_up) (getF ?state_up) (getM ?state_up) (set (getQ ?state_up))\<close>
        using False
        using \<open>\<not> getConflictFlag ?state_up\<close> 
        using \<open>getConflictFlag ?state_up \<or> getQ ?state_up = []\<close>
        by (simp add: Let_def)
      moreover
      have "getSATFlag ?state_d = getSATFlag state"
        unfolding applyDecide_def
        using \<open>getSATFlag ?state_up = getSATFlag state\<close>
        using assertLiteralEffect[of "?state_up" "selectLiteral ?state_up Vbl" "True"]
        using \<open>?inv' ?state_up\<close>
        by (simp only: Let_def)
      moreover
      have "InvariantVarsM (getM ?state_d) F0 Vbl"
        "InvariantVarsF (getF ?state_d) F0 Vbl"
        "InvariantVarsQ (getQ ?state_d) F0 Vbl"
        using InvariantsVarsAfterApplyDecide[of "Vbl" "?state_up"]
        using False
        using \<open>?inv' ?state_up\<close>
        using \<open>\<not> getConflictFlag ?state_up\<close>
        using \<open>getConflictFlag ?state_up \<or> getQ ?state_up = []\<close>
        using \<open>InvariantVarsM (getM ?state_up) F0 Vbl\<close>
        using \<open>InvariantVarsQ (getQ ?state_up) F0 Vbl\<close>
        using \<open>InvariantVarsF (getF ?state_up) F0 Vbl\<close>
        by (auto simp only: Let_def)
      moreover
      have "(?state_d, ?state_up) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
        using \<open>getSATFlag ?state_up = getSATFlag state\<close>
        using assertLiteralEffect[of "?state_up" "selectLiteral ?state_up Vbl" "True"]
        using \<open>?inv' ?state_up\<close>
        using \<open>InvariantVarsM (getM state) F0 Vbl\<close>
        using \<open>InvariantVarsM (getM ?state_up) F0 Vbl\<close>
        using \<open>InvariantVarsM (getM ?state_d) F0 Vbl\<close>
        using \<open>getSATFlag state = UNDEF\<close>
        using \<open>?inv' ?state_up\<close>
        using \<open>InvariantConsistent (getM ?state_d)\<close>
        using \<open>InvariantUniq (getM ?state_d)\<close>
        using lexLessAppend[of "[(selectLiteral ?state_up Vbl, True)]""getM ?state_up"]
        unfolding applyDecide_def
        unfolding terminationLessState1_def
        unfolding lexLessState1_def
        unfolding lexLessRestricted_def
        unfolding InvariantVarsM_def
        unfolding InvariantUniq_def
        unfolding InvariantConsistent_def
        by (simp add: Let_def)
      hence "(?state_d, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
        using \<open>?state_up = state \<or> (?state_up, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)\<close>
        using transTerminationLessState1I[of "?state_d" "?state_up" "vars F0 \<union> Vbl" "state"]
        by auto
      ultimately
      show ?thesis
        using \<open>?inv' ?state_up\<close>
        using \<open>getSATFlag state = UNDEF\<close>
        using \<open>\<not> getConflictFlag ?state_up\<close>
        using False
        using WatchInvariantsAfterAssertLiteral[of "?state_up" "?literal" "True"]
        using InvariantWatchCharacterizationAfterAssertLiteral[of "?state_up" "?literal" "True"]
        using InvariantUniqQAfterAssertLiteral[of "?state_up" "?literal" "True"]
        using assertLiteralEffect[of "?state_up" "?literal" "True"]
        unfolding solve_loop_body_def
        unfolding applyDecide_def
        unfolding selectLiteral_def
        by (simp add: Let_def)
    qed
  qed
qed


(*****************************************************************************)
(*        S O L V E    L O O P                                               *)
(*****************************************************************************)

lemma SolveLoopTermination:
assumes
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantUniqQ (getQ state)" and
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)" and
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)" and
  "InvariantNoDecisionsWhenConflict (getF state) (getM state) (currentLevel (getM state))" and
  "InvariantNoDecisionsWhenUnit (getF state) (getM state) (currentLevel (getM state))" and
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))" and
  "getSATFlag state = UNDEF \<longrightarrow> InvariantEquivalentZL (getF state) (getM state) F0'" and
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)" and
  "finite Vbl"
  "vars F0' \<subseteq> vars F0"
  "vars F0 \<subseteq> Vbl"
  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsQ (getQ state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
shows
  "solve_loop_dom state Vbl"
using assms
proof (induct rule: wf_induct[of "terminationLessState1 (vars F0 \<union> Vbl)"])
  case 1
  thus ?case
    using \<open>finite Vbl\<close>
    using finiteVarsFormula[of "F0"]
    using wellFoundedTerminationLessState1[of "vars F0 \<union> Vbl"]
    by simp
next
  case (2 state')
  note ih = this
  show ?case
  proof (cases "getSATFlag state' = UNDEF")
    case False
    show ?thesis
      apply (rule solve_loop_dom.intros)
      using False
      by simp
  next
    case True
    let ?state'' = "solve_loop_body state' Vbl"
    have
      "InvariantConsistent (getM ?state'')"
      "InvariantUniq (getM ?state'')"
      "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and 
      "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and 
      "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') (getM ?state'')" and 
      "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')" and
      "InvariantWatchListsUniq (getWatchList ?state'')" and
      "InvariantWatchListsCharacterization (getWatchList ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and
      "InvariantUniqQ (getQ ?state'')" and
      "InvariantQCharacterization (getConflictFlag ?state'') (getQ ?state'') (getF ?state'') (getM ?state'')" and
      "InvariantConflictFlagCharacterization (getConflictFlag ?state'') (getF ?state'') (getM ?state'')" and
      "InvariantNoDecisionsWhenConflict (getF ?state'') (getM ?state'') (currentLevel (getM ?state''))" and
      "InvariantNoDecisionsWhenUnit (getF ?state'') (getM ?state'') (currentLevel (getM ?state''))" and
      "InvariantConflictClauseCharacterization (getConflictFlag ?state'') (getConflictClause ?state'') (getF ?state'') (getM ?state'')"
      "InvariantGetReasonIsReason (getReason ?state'') (getF ?state'') (getM ?state'') (set (getQ ?state''))"
      "InvariantEquivalentZL (getF ?state'') (getM ?state'') F0'"
      "InvariantVarsM (getM ?state'') F0 Vbl"
      "InvariantVarsQ (getQ ?state'') F0 Vbl"
      "InvariantVarsF (getF ?state'') F0 Vbl"
      "getSATFlag ?state'' = FALSE \<longrightarrow> \<not> satisfiable F0'"
      "getSATFlag ?state'' = TRUE  \<longrightarrow> satisfiable F0'"
      "(?state'', state') \<in> terminationLessState1 (vars F0 \<union> Vbl)"
     using InvariantsAfterSolveLoopBody[of "state'" "F0'" "Vbl" "F0"]
     using ih(2) ih(3) ih(4) ih(5) ih(6) ih(7) ih(8) ih(9) ih(10) ih(11) ih(12) ih(13) ih(14) ih(15)
           ih(16) ih(17) ih(18) ih(19) ih(20) ih(21) ih(22) ih(23)
     using True
     by (auto simp only: Let_def)
   hence "solve_loop_dom ?state'' Vbl"
     using ih
     by auto
   thus ?thesis
     using solve_loop_dom.intros[of "state'" "Vbl"]
     using True
     by simp
 qed
qed


lemma SATFlagAfterSolveLoop:
assumes
  "solve_loop_dom state Vbl"
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantUniqQ (getQ state)" and
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)" and
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)" and
  "InvariantNoDecisionsWhenConflict (getF state) (getM state) (currentLevel (getM state))" and
  "InvariantNoDecisionsWhenUnit (getF state) (getM state) (currentLevel (getM state))" and
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))" and
  "getSATFlag state = UNDEF \<longrightarrow> InvariantEquivalentZL (getF state) (getM state) F0'" and
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)"
  "getSATFlag state = FALSE \<longrightarrow> \<not> satisfiable F0'"
  "getSATFlag state = TRUE  \<longrightarrow> satisfiable F0'"
  "finite Vbl"
  "vars F0' \<subseteq> vars F0"
  "vars F0 \<subseteq> Vbl"
  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
  "InvariantVarsQ (getQ state) F0 Vbl"
shows
  "let state' = solve_loop state Vbl in 
         (getSATFlag state' = FALSE \<and> \<not> satisfiable F0') \<or> (getSATFlag state' = TRUE  \<and> satisfiable F0')"
using assms
proof (induct state Vbl rule: solve_loop_dom.induct)
  case (step state' Vbl)
  note ih = this
  show ?case
  proof (cases "getSATFlag state' = UNDEF")
    case False
    with solve_loop.simps[of "state'"]
    have "solve_loop state' Vbl = state'"
      by simp
    thus ?thesis
      using False
      using ih(19) ih(20)
      using ExtendedBool.nchotomy
      by (auto simp add: Let_def)
  next
    case True
    let ?state'' = "solve_loop_body state' Vbl"
    have "solve_loop state' Vbl = solve_loop ?state'' Vbl"
      using solve_loop.simps[of "state'"]
      using True
      by (simp add: Let_def)
    moreover
    have "InvariantEquivalentZL (getF state') (getM state') F0'"
      using True
      using ih(17)
      by simp
    hence
      "InvariantConsistent (getM ?state'')"
      "InvariantUniq (getM ?state'')"
      "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and 
      "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and 
      "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') (getM ?state'')" and 
      "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')" and
      "InvariantWatchListsUniq (getWatchList ?state'')" and
      "InvariantWatchListsCharacterization (getWatchList ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and
      "InvariantUniqQ (getQ ?state'')" and
      "InvariantQCharacterization (getConflictFlag ?state'') (getQ ?state'') (getF ?state'') (getM ?state'')" and
      "InvariantConflictFlagCharacterization (getConflictFlag ?state'') (getF ?state'') (getM ?state'')" and
      "InvariantNoDecisionsWhenConflict (getF ?state'') (getM ?state'') (currentLevel (getM ?state''))" and
      "InvariantNoDecisionsWhenUnit (getF ?state'') (getM ?state'') (currentLevel (getM ?state''))" and
      "InvariantConflictClauseCharacterization (getConflictFlag ?state'') (getConflictClause ?state'') (getF ?state'') (getM ?state'')"
      "InvariantGetReasonIsReason (getReason ?state'') (getF ?state'') (getM ?state'') (set (getQ ?state''))"
      "InvariantEquivalentZL (getF ?state'') (getM ?state'') F0'"
      "InvariantVarsM (getM ?state'') F0 Vbl"
      "InvariantVarsQ (getQ ?state'') F0 Vbl"
      "InvariantVarsF (getF ?state'') F0 Vbl"
      "getSATFlag ?state'' = FALSE \<longrightarrow> \<not> satisfiable F0'"
      "getSATFlag ?state'' = TRUE  \<longrightarrow> satisfiable F0'"
      using ih(1) ih(3) ih(4) ih(5) ih(6) ih(7) ih(8) ih(9) ih(10) ih(11) ih(12) ih(13) ih(14)
            ih(15) ih(16) ih(18) ih(21) ih(22) ih(23) ih(24) ih(25) ih(26)
      using InvariantsAfterSolveLoopBody[of "state'" "F0'" "Vbl" "F0"]
      using True
      by (auto simp only: Let_def)
    ultimately
    show ?thesis
      using True
      using ih(2)
      using ih(21)
      using ih(22)
      using ih(23)
      by (simp add: Let_def)
  qed
qed

      

end
