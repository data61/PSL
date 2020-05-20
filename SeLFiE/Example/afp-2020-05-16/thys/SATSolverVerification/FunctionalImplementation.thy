theory FunctionalImplementation
imports Initialization SolveLoop
begin

(******************************************************************************)
subsection\<open>Total correctness theorem\<close>
(******************************************************************************)

theorem correctness:
shows 
"(solve F0 = TRUE \<and> satisfiable F0) \<or> (solve F0 = FALSE \<and> \<not> satisfiable F0)"
proof-
  let ?istate = "initialize F0 initialState"
  let ?F0' = "filter (\<lambda> c. \<not> clauseTautology c) F0"
  have
  "InvariantConsistent (getM ?istate)"
  "InvariantUniq (getM ?istate)"
  "InvariantWatchesEl (getF ?istate) (getWatch1 ?istate) (getWatch2 ?istate)" and 
  "InvariantWatchesDiffer (getF ?istate) (getWatch1 ?istate) (getWatch2 ?istate)" and 
  "InvariantWatchCharacterization (getF ?istate) (getWatch1 ?istate) (getWatch2 ?istate) (getM ?istate)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?istate) (getF ?istate)" and
  "InvariantWatchListsUniq (getWatchList ?istate)" and
  "InvariantWatchListsCharacterization (getWatchList ?istate) (getWatch1 ?istate) (getWatch2 ?istate)" and
  "InvariantUniqQ (getQ ?istate)" and
  "InvariantQCharacterization (getConflictFlag ?istate) (getQ ?istate) (getF ?istate) (getM ?istate)" and
  "InvariantConflictFlagCharacterization (getConflictFlag ?istate) (getF ?istate) (getM ?istate)" and
  "InvariantNoDecisionsWhenConflict (getF ?istate) (getM ?istate) (currentLevel (getM ?istate))" and
  "InvariantNoDecisionsWhenUnit (getF ?istate) (getM ?istate) (currentLevel (getM ?istate))" and
  "InvariantGetReasonIsReason (getReason ?istate) (getF ?istate) (getM ?istate) (set (getQ ?istate))" and
  "InvariantConflictClauseCharacterization (getConflictFlag ?istate) (getConflictClause ?istate) (getF ?istate) (getM ?istate)"
  "InvariantVarsM (getM ?istate) F0 (vars F0)"
  "InvariantVarsQ (getQ ?istate) F0 (vars F0)"
  "InvariantVarsF (getF ?istate) F0 (vars F0)"
  "getSATFlag ?istate = UNDEF \<longrightarrow> InvariantEquivalentZL (getF ?istate) (getM ?istate) ?F0'" and
  "getSATFlag ?istate = FALSE \<longrightarrow> \<not> satisfiable ?F0'"
  "getSATFlag ?istate = TRUE  \<longrightarrow> satisfiable F0"
    using InvariantsAfterInitialization[of "F0"]
    using InvariantEquivalentZLAfterInitialization[of "F0"]
    unfolding InvariantVarsM_def
    unfolding InvariantVarsF_def
    unfolding InvariantVarsQ_def
    by (auto simp add: Let_def)
  moreover
  hence "solve_loop_dom ?istate (vars F0)"
    using SolveLoopTermination[of "?istate" "?F0'" "vars F0" "F0"]
    using finiteVarsFormula[of "F0"]
    using varsSubsetFormula[of "?F0'" "F0"]
    by auto
  ultimately
  show ?thesis
    using finiteVarsFormula[of "F0"]
    using SATFlagAfterSolveLoop[of "?istate" "vars F0" "?F0'" "F0"]
    using satisfiableFilterTautologies[of "F0"]
    unfolding solve_def
    using varsSubsetFormula[of "?F0'" "F0"]
    by (auto simp add: Let_def)
qed

end
