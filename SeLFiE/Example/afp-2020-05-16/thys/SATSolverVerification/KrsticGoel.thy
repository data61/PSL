(*    Title:              SatSolverVerification/KrsticGoel.thy
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

section\<open>Transition system of Krsti\' c and Goel.\<close>
theory KrsticGoel
imports SatSolverVerification
begin

text\<open>This theory formalizes the transition rule system given by
Krsti\' c and Goel in \cite{KrsticGoel}. Some rules of the system are 
generalized a bit, so that the system can model some more general solvers 
(e.g., SMT solvers).\<close>

(******************************************************************************)
subsection\<open>Specification\<close>
(******************************************************************************)

record State = 
"getF" :: Formula
"getM" :: LiteralTrail
"getConflictFlag" :: bool
"getC" :: Clause

definition
appliedDecide:: "State \<Rightarrow> State \<Rightarrow> Variable set \<Rightarrow> bool"
where
"appliedDecide stateA stateB decisionVars == 
  \<exists> l. 
        (var l) \<in> decisionVars \<and> 
        \<not> l el (elements (getM stateA)) \<and> 
        \<not> opposite l el (elements (getM stateA)) \<and>

        getF stateB = getF stateA \<and>
        getM stateB = getM stateA @ [(l, True)] \<and> 
        getConflictFlag stateB = getConflictFlag stateA \<and>
        getC stateB = getC stateA
"
definition
applicableDecide :: "State \<Rightarrow> Variable set \<Rightarrow> bool"
where
"applicableDecide state decisionVars == \<exists> state'. appliedDecide state state' decisionVars"

text\<open>Notice that the given UnitPropagate description is weaker than
in original \cite{KrsticGoel} paper. Namely, propagation can be done
over a clause that is not a member of the formula, but is entailed by
it. The condition imposed on the variable of the unit literal is
necessary to ensure the termination.\<close>
definition
appliedUnitPropagate :: "State \<Rightarrow> State \<Rightarrow> Formula \<Rightarrow> Variable set \<Rightarrow> bool"
where
"appliedUnitPropagate stateA stateB F0 decisionVars == 
  \<exists> (uc::Clause) (ul::Literal). 
        formulaEntailsClause (getF stateA) uc \<and> 
        (var ul) \<in> decisionVars \<union> vars F0 \<and>
        isUnitClause uc ul (elements (getM stateA))  \<and>

       getF stateB = getF stateA \<and>
       getM stateB = getM stateA @ [(ul, False)] \<and> 
       getConflictFlag stateB = getConflictFlag stateA \<and>
       getC stateB = getC stateA
"
definition
applicableUnitPropagate :: "State \<Rightarrow> Formula \<Rightarrow> Variable set \<Rightarrow> bool"
where
"applicableUnitPropagate state F0 decisionVars == \<exists> state'. appliedUnitPropagate state state' F0 decisionVars"

text\<open>Notice, also, that $Conflict$ can be performed for a clause
that is not a member of the formula.\<close>
definition
appliedConflict :: "State \<Rightarrow> State \<Rightarrow> bool"
where
"appliedConflict stateA stateB == 
  \<exists> clause. 
       getConflictFlag stateA = False \<and>
       formulaEntailsClause (getF stateA) clause \<and> 
       clauseFalse clause (elements (getM stateA)) \<and> 

       getF stateB = getF stateA \<and>
       getM stateB = getM stateA \<and> 
       getConflictFlag stateB = True  \<and>
       getC stateB = clause
  "
definition
applicableConflict :: "State \<Rightarrow> bool"
where
"applicableConflict state == \<exists> state'. appliedConflict state state'"

text\<open>Notice, also, that the explanation can be done over a reason clause that is
not a member of the formula, but is only entailed by it.\<close>
definition
appliedExplain :: "State \<Rightarrow> State \<Rightarrow> bool"
where
"appliedExplain stateA stateB == 
   \<exists> l reason. 
       getConflictFlag stateA = True \<and>  
       l el getC stateA \<and> 
       formulaEntailsClause (getF stateA) reason \<and> 
       isReason reason (opposite l) (elements (getM stateA)) \<and> 

       getF stateB = getF stateA \<and>
       getM stateB = getM stateA \<and> 
       getConflictFlag stateB = True \<and>
       getC stateB = resolve (getC stateA) reason l
   "
definition
applicableExplain :: "State \<Rightarrow> bool"
where
"applicableExplain state == \<exists> state'. appliedExplain state state'"


definition
appliedLearn :: "State \<Rightarrow> State \<Rightarrow> bool"
where
"appliedLearn stateA stateB == 
       getConflictFlag stateA = True \<and> 
       \<not> getC stateA el getF stateA \<and>

       getF stateB = getF stateA @ [getC stateA] \<and>
       getM stateB = getM stateA \<and> 
       getConflictFlag stateB = True \<and>
       getC stateB = getC stateA
"
definition
applicableLearn :: "State \<Rightarrow> bool"
where
"applicableLearn state == \<exists> state'. appliedLearn state state'"

text\<open>Since unit propagation can be done over non-member clauses, it is not required that the conflict clause
is learned before the $Backjump$ is applied.\<close>
definition
appliedBackjump :: "State \<Rightarrow> State \<Rightarrow> bool"
where
"appliedBackjump stateA stateB == 
  \<exists> l level. 
       getConflictFlag stateA = True \<and> 
       isBackjumpLevel level l (getC stateA) (getM stateA) \<and>

       getF stateB = getF stateA \<and>
       getM stateB = prefixToLevel level (getM stateA) @ [(l, False)] \<and>
       getConflictFlag stateB = False \<and>
       getC stateB = []
  "
definition
applicableBackjump :: "State \<Rightarrow> bool"
where
"applicableBackjump state == \<exists> state'. appliedBackjump state state'"

text\<open>Solving starts with the initial formula, the empty trail and in non conflicting state.\<close>
definition
isInitialState :: "State \<Rightarrow> Formula \<Rightarrow> bool"
where
"isInitialState state F0 == 
      getF state = F0 \<and>
      getM state = [] \<and>
      getConflictFlag state = False \<and>
      getC state = []"

text\<open>Transitions are preformed only by using given rules.\<close>
definition
transition :: "State \<Rightarrow> State \<Rightarrow> Formula \<Rightarrow> Variable set \<Rightarrow> bool"
where
"transition stateA stateB F0 decisionVars== 
     appliedDecide        stateA stateB decisionVars \<or> 
     appliedUnitPropagate stateA stateB F0 decisionVars \<or> 
     appliedConflict      stateA stateB \<or> 
     appliedExplain       stateA stateB \<or>
     appliedLearn         stateA stateB \<or>
     appliedBackjump      stateA stateB "

text\<open>Transition relation is obtained by applying transition rules
iteratively. It is defined using a reflexive-transitive closure.\<close>
definition
"transitionRelation F0 decisionVars == ({(stateA, stateB). transition stateA stateB F0 decisionVars})^*"

text\<open>Final state is one in which no rules apply\<close>
definition
isFinalState :: "State \<Rightarrow> Formula \<Rightarrow> Variable set \<Rightarrow> bool"
where
"isFinalState state F0 decisionVars == \<not> (\<exists> state'. transition state state' F0 decisionVars)"


text\<open>The following several lemmas establish conditions for applicability of different rules.\<close>
lemma applicableDecideCharacterization:
  fixes stateA::State
  shows "applicableDecide stateA decisionVars = 
  (\<exists> l. 
        (var l) \<in> decisionVars \<and> 
        \<not> l el (elements (getM stateA)) \<and> 
        \<not> opposite l el (elements (getM stateA))) 
  " (is "?lhs = ?rhs")
proof
  assume ?rhs
  then obtain l where 
    *: "(var l) \<in> decisionVars" "\<not> l el (elements (getM stateA))" "\<not> opposite l el (elements (getM stateA))"
    unfolding applicableDecide_def
    by auto
  let ?stateB = "stateA\<lparr> getM := (getM stateA) @ [(l, True)] \<rparr>"
  from * have "appliedDecide stateA ?stateB decisionVars"
    unfolding appliedDecide_def
    by auto
  thus ?lhs
    unfolding applicableDecide_def
    by auto
next
  assume ?lhs
  then obtain stateB l
    where "(var l) \<in> decisionVars" "\<not> l el (elements (getM stateA))"
    "\<not> opposite l el (elements (getM stateA))"
    unfolding applicableDecide_def
    unfolding appliedDecide_def
    by auto
  thus ?rhs
    by auto
qed

lemma applicableUnitPropagateCharacterization:
  fixes stateA::State and F0::Formula
  shows "applicableUnitPropagate stateA F0 decisionVars = 
  (\<exists> (uc::Clause) (ul::Literal). 
        formulaEntailsClause (getF stateA) uc \<and> 
        (var ul) \<in> decisionVars \<union> vars F0 \<and>
        isUnitClause uc ul (elements (getM stateA)))
  " (is "?lhs = ?rhs")
proof
  assume "?rhs"
  then obtain ul uc 
    where *: 
    "formulaEntailsClause (getF stateA) uc"
    "(var ul) \<in> decisionVars \<union> vars F0"
    "isUnitClause uc ul (elements (getM stateA))"
    unfolding applicableUnitPropagate_def
    by auto
  let ?stateB = "stateA\<lparr> getM := getM stateA @ [(ul, False)] \<rparr>"
  from * have "appliedUnitPropagate stateA ?stateB F0 decisionVars" 
    unfolding appliedUnitPropagate_def
    by auto
  thus ?lhs
    unfolding applicableUnitPropagate_def
    by auto
next
  assume ?lhs
  then obtain stateB uc ul
    where
     "formulaEntailsClause (getF stateA) uc"
    "(var ul) \<in> decisionVars \<union> vars F0"
    "isUnitClause uc ul (elements (getM stateA))"
    unfolding applicableUnitPropagate_def
    unfolding appliedUnitPropagate_def
    by auto
  thus ?rhs
    by auto
qed


lemma applicableBackjumpCharacterization:
  fixes stateA::State
  shows "applicableBackjump stateA = 
     (\<exists> l level. 
         getConflictFlag stateA = True \<and> 
         isBackjumpLevel level l (getC stateA) (getM stateA)
     )" (is "?lhs = ?rhs")
proof
  assume "?rhs"
  then obtain l level
    where *: 
    "getConflictFlag stateA = True"
    "isBackjumpLevel level l (getC stateA) (getM stateA)"
    unfolding applicableBackjump_def
    by auto
  let ?stateB = "stateA\<lparr> getM := prefixToLevel level (getM stateA) @ [(l, False)], 
                         getConflictFlag := False, 
                         getC := [] \<rparr>"
  from * have "appliedBackjump stateA ?stateB"
    unfolding appliedBackjump_def
    by auto
  thus "?lhs"
    unfolding applicableBackjump_def
    by auto
next
  assume "?lhs"
  then obtain stateB l level
    where  "getConflictFlag stateA = True"
    "isBackjumpLevel level l (getC stateA) (getM stateA)"
    unfolding applicableBackjump_def
    unfolding appliedBackjump_def
    by auto
  thus "?rhs"
    by auto
qed

lemma applicableExplainCharacterization:
  fixes stateA::State
  shows "applicableExplain stateA = 
  (\<exists> l reason. 
       getConflictFlag stateA = True \<and>  
       l el getC stateA \<and> 
       formulaEntailsClause (getF stateA) reason \<and> 
       isReason reason (opposite l) (elements (getM stateA))
  )
  " (is "?lhs = ?rhs")
proof
  assume "?rhs"
  then obtain l reason
    where *: 
    "getConflictFlag stateA = True"
    "l el (getC stateA)" "formulaEntailsClause (getF stateA) reason"
    "isReason reason (opposite l) (elements (getM stateA))"
    unfolding applicableExplain_def
    by auto
  let ?stateB = "stateA\<lparr> getC := resolve (getC stateA) reason l \<rparr>"
  from * have "appliedExplain stateA ?stateB"
    unfolding appliedExplain_def
    by auto
  thus "?lhs"
    unfolding applicableExplain_def
    by auto
next
  assume "?lhs"
  then obtain stateB l reason
    where
    "getConflictFlag stateA = True"
    "l el getC stateA" "formulaEntailsClause (getF stateA) reason"
    "isReason reason (opposite l) (elements (getM stateA))"
    unfolding applicableExplain_def
    unfolding appliedExplain_def
    by auto
  thus "?rhs"
    by auto
qed

lemma applicableConflictCharacterization:
  fixes stateA::State
  shows "applicableConflict stateA = 
    (\<exists> clause. 
       getConflictFlag stateA = False \<and>
       formulaEntailsClause (getF stateA) clause \<and> 
       clauseFalse clause (elements (getM stateA)))" (is "?lhs = ?rhs")
proof
  assume "?rhs"
  then obtain clause
    where *: 
    "getConflictFlag stateA = False" "formulaEntailsClause (getF stateA) clause" "clauseFalse clause (elements (getM stateA))"
    unfolding applicableConflict_def
    by auto
  let ?stateB = "stateA\<lparr> getC := clause, 
                         getConflictFlag := True \<rparr>"
  from * have "appliedConflict stateA ?stateB"
    unfolding appliedConflict_def
    by auto
  thus "?lhs"
    unfolding applicableConflict_def
    by auto
next
  assume "?lhs"
  then obtain stateB clause
    where
    "getConflictFlag stateA = False"
    "formulaEntailsClause (getF stateA) clause"
    "clauseFalse clause (elements (getM stateA))"
    unfolding applicableConflict_def
    unfolding appliedConflict_def
    by auto
  thus "?rhs"
    by auto
qed

lemma applicableLearnCharacterization:
  fixes stateA::State
  shows "applicableLearn stateA = 
           (getConflictFlag stateA = True \<and> 
           \<not> getC stateA el getF stateA)" (is "?lhs = ?rhs")
proof
  assume "?rhs"
  hence *: "getConflictFlag stateA = True" "\<not> getC stateA el getF stateA"
    unfolding applicableLearn_def
    by auto
  let ?stateB = "stateA\<lparr> getF := getF stateA @ [getC stateA]\<rparr>"
  from * have "appliedLearn stateA ?stateB"
    unfolding appliedLearn_def
    by auto
  thus "?lhs"
    unfolding applicableLearn_def
    by auto
next
  assume "?lhs"
  then obtain stateB
    where
    "getConflictFlag stateA = True" "\<not> (getC stateA) el (getF stateA)"
    unfolding applicableLearn_def
    unfolding appliedLearn_def
    by auto
  thus "?rhs"
    by auto
qed

text\<open>Final states are the ones where no rule is applicable.\<close>
lemma finalStateNonApplicable: 
  fixes state::State
  shows "isFinalState state F0 decisionVars = 
          (\<not> applicableDecide state decisionVars \<and> 
           \<not> applicableUnitPropagate state F0 decisionVars \<and> 
           \<not> applicableBackjump state \<and> 
           \<not> applicableLearn state \<and> 
           \<not> applicableConflict state \<and> 
           \<not> applicableExplain state)"
unfolding isFinalState_def
unfolding transition_def
unfolding applicableDecide_def
unfolding applicableUnitPropagate_def
unfolding applicableBackjump_def
unfolding applicableLearn_def
unfolding applicableConflict_def
unfolding applicableExplain_def
by auto

(******************************************************************************)
subsection\<open>Invariants\<close>
(******************************************************************************)
text\<open>Invariants that are relevant for the rest of correctness proof.\<close>
definition
invariantsHoldInState :: "State \<Rightarrow> Formula \<Rightarrow> Variable set \<Rightarrow> bool"
where
"invariantsHoldInState state F0 decisionVars == 
    InvariantVarsM (getM state) F0 decisionVars  \<and>
    InvariantVarsF (getF state) F0 decisionVars  \<and>
    InvariantConsistent (getM state) \<and>
    InvariantUniq (getM state) \<and> 
    InvariantReasonClauses (getF state) (getM state) \<and>
    InvariantEquivalent F0 (getF state) \<and>
    InvariantCFalse (getConflictFlag state) (getM state) (getC state) \<and>
    InvariantCEntailed (getConflictFlag state) (getF state) (getC state)
"

text\<open>Invariants hold in initial states\<close>
lemma invariantsHoldInInitialState:
  fixes state :: State and F0 :: Formula
  assumes "isInitialState state F0" 
  shows "invariantsHoldInState state F0 decisionVars"
using assms
by (auto simp add:
  isInitialState_def 
  invariantsHoldInState_def 
  InvariantVarsM_def
  InvariantVarsF_def
  InvariantConsistent_def
  InvariantUniq_def
  InvariantReasonClauses_def
  InvariantEquivalent_def equivalentFormulae_def
  InvariantCFalse_def
  InvariantCEntailed_def
)

text\<open>Valid transitions preserve invariants.\<close>
lemma transitionsPreserveInvariants: 
  fixes stateA::State and stateB::State
  assumes "transition stateA stateB F0 decisionVars" and 
  "invariantsHoldInState stateA F0 decisionVars"
  shows "invariantsHoldInState stateB F0 decisionVars"
proof-
    from \<open>invariantsHoldInState stateA F0 decisionVars\<close>
    have 
      "InvariantVarsM (getM stateA) F0 decisionVars" and
      "InvariantVarsF (getF stateA) F0 decisionVars" and
      "InvariantConsistent (getM stateA)" and
      "InvariantUniq (getM stateA)" and
      "InvariantReasonClauses (getF stateA) (getM stateA)" and
      "InvariantEquivalent F0 (getF stateA)" and
      "InvariantCFalse (getConflictFlag stateA) (getM stateA) (getC stateA)" and
      "InvariantCEntailed (getConflictFlag stateA) (getF stateA) (getC stateA)"
      unfolding invariantsHoldInState_def
      by auto
  {
    assume "appliedDecide stateA stateB decisionVars"
    then obtain l::Literal where
      "(var l) \<in> decisionVars"
      "\<not> literalTrue l (elements (getM stateA))"
      "\<not> literalFalse l (elements (getM stateA))"
      "getM stateB = getM stateA @ [(l, True)]"
      "getF stateB = getF stateA"
      "getConflictFlag stateB = getConflictFlag stateA"
      "getC stateB = getC stateA"
      unfolding appliedDecide_def
      by auto

    from \<open>\<not> literalTrue l (elements (getM stateA))\<close> \<open>\<not> literalFalse l (elements (getM stateA))\<close> 
    have *: "var l \<notin> vars (elements (getM stateA))"
      using variableDefinedImpliesLiteralDefined[of "l" "elements (getM stateA)"]
      by simp

    have "InvariantVarsM (getM stateB) F0 decisionVars"
      using \<open>getF stateB = getF stateA\<close>
        \<open>getM stateB = getM stateA @ [(l, True)]\<close> 
        \<open>InvariantVarsM (getM stateA) F0 decisionVars\<close>
        \<open>var l \<in> decisionVars\<close>
        InvariantVarsMAfterDecide [of "getM stateA" "F0" "decisionVars" "l" "getM stateB"]
      by simp
    moreover
    have "InvariantVarsF (getF stateB) F0 decisionVars"
      using \<open>getF stateB = getF stateA\<close>
        \<open>InvariantVarsF (getF stateA) F0 decisionVars\<close>
      by simp
    moreover
    have "InvariantConsistent (getM stateB)"
      using \<open>getM stateB = getM stateA @ [(l, True)]\<close> 
        \<open>InvariantConsistent (getM stateA)\<close>
        \<open>var l \<notin> vars (elements (getM stateA))\<close>
        InvariantConsistentAfterDecide[of "getM stateA" "l" "getM stateB"]
      by simp
    moreover
    have "InvariantUniq (getM stateB)"
      using \<open>getM stateB = getM stateA @ [(l, True)]\<close> 
        \<open>InvariantUniq (getM stateA)\<close>
        \<open>var l \<notin> vars (elements (getM stateA))\<close>
        InvariantUniqAfterDecide[of "getM stateA" "l" "getM stateB"]
      by simp
    moreover
    have "InvariantReasonClauses (getF stateB) (getM stateB)"
      using \<open>getF stateB = getF stateA\<close>
        \<open>getM stateB = getM stateA @ [(l, True)]\<close> 
        \<open>InvariantUniq (getM stateA)\<close>
        \<open>InvariantReasonClauses (getF stateA) (getM stateA)\<close>
      using InvariantReasonClausesAfterDecide[of "getF stateA" "getM stateA" "getM stateB" "l"]
      by simp
    moreover
    have "InvariantEquivalent F0 (getF stateB)"
      using \<open>getF stateB = getF stateA\<close>
      \<open>InvariantEquivalent F0 (getF stateA)\<close>
      by simp
    moreover
    have "InvariantCFalse (getConflictFlag stateB) (getM stateB) (getC stateB)"
      using \<open>getM stateB = getM stateA @ [(l, True)]\<close> 
        \<open>getConflictFlag stateB = getConflictFlag stateA\<close>
        \<open>getC stateB = getC stateA\<close>
        \<open>InvariantCFalse (getConflictFlag stateA) (getM stateA) (getC stateA)\<close>
        InvariantCFalseAfterDecide[of "getConflictFlag stateA" "getM stateA" "getC stateA" "getM stateB" "l"]
      by simp
    moreover 
    have "InvariantCEntailed (getConflictFlag stateB) (getF stateB) (getC stateB)"
      using \<open>getF stateB = getF stateA\<close>
        \<open>getConflictFlag stateB = getConflictFlag stateA\<close>
        \<open>getC stateB = getC stateA\<close>
        \<open>InvariantCEntailed (getConflictFlag stateA) (getF stateA) (getC stateA)\<close>
      by simp
    ultimately
    have ?thesis
      unfolding invariantsHoldInState_def
      by auto
  }
  moreover
  {
    assume "appliedUnitPropagate stateA stateB F0 decisionVars"
    then obtain uc::Clause and ul::Literal where 
      "formulaEntailsClause (getF stateA) uc"
      "(var ul) \<in> decisionVars \<union> vars F0" 
      "isUnitClause uc ul (elements (getM stateA))"
      "getF stateB = getF stateA"
      "getM stateB = getM stateA @ [(ul, False)]"
      "getConflictFlag stateB = getConflictFlag stateA"
      "getC stateB = getC stateA"
      unfolding appliedUnitPropagate_def
      by auto

    from \<open>isUnitClause uc ul (elements (getM stateA))\<close>
    have "ul el uc"
      unfolding isUnitClause_def
      by simp

    from \<open>var ul \<in> decisionVars \<union> vars F0\<close>
    have "InvariantVarsM (getM stateB) F0 decisionVars"
      using \<open>getF stateB = getF stateA\<close> 
        \<open>InvariantVarsM (getM stateA) F0 decisionVars\<close>
        \<open>getM stateB = getM stateA @ [(ul, False)]\<close>
        InvariantVarsMAfterUnitPropagate[of "getM stateA" "F0" "decisionVars" "ul" "getM stateB"]
      by auto
    moreover
    have "InvariantVarsF (getF stateB) F0 decisionVars"
      using \<open>getF stateB = getF stateA\<close>
        \<open>InvariantVarsF (getF stateA) F0 decisionVars\<close>
      by simp
    moreover
    have "InvariantConsistent (getM stateB)"
      using \<open>InvariantConsistent (getM stateA)\<close>
        \<open>isUnitClause uc ul (elements (getM stateA))\<close>
        \<open>getM stateB = getM stateA @ [(ul, False)]\<close>
        InvariantConsistentAfterUnitPropagate [of "getM stateA" "uc" "ul" "getM stateB"]
      by simp
    moreover
    have "InvariantUniq (getM stateB)"
      using \<open>InvariantUniq (getM stateA)\<close>
        \<open>isUnitClause uc ul (elements (getM stateA))\<close>
        \<open>getM stateB = getM stateA @ [(ul, False)]\<close>
        InvariantUniqAfterUnitPropagate [of "getM stateA" "uc" "ul" "getM stateB"]
      by simp
    moreover
    have "InvariantReasonClauses (getF stateB) (getM stateB)"
      using \<open>getF stateB = getF stateA\<close> 
        \<open>InvariantReasonClauses (getF stateA) (getM stateA)\<close>
        \<open>isUnitClause uc ul (elements (getM stateA))\<close>
        \<open>getM stateB = getM stateA @ [(ul, False)]\<close>
        \<open>formulaEntailsClause (getF stateA) uc\<close>
        InvariantReasonClausesAfterUnitPropagate[of "getF stateA" "getM stateA" "uc" "ul" "getM stateB"]
      by simp
    moreover
    have "InvariantEquivalent F0 (getF stateB)"
      using \<open>getF stateB = getF stateA\<close> 
      \<open>InvariantEquivalent F0 (getF stateA)\<close>
      by simp
    moreover 
    have "InvariantCFalse (getConflictFlag stateB) (getM stateB) (getC stateB)"
      using \<open>getM stateB = getM stateA @ [(ul, False)]\<close> 
        \<open>getConflictFlag stateB = getConflictFlag stateA\<close>
        \<open>getC stateB = getC stateA\<close>
        \<open>InvariantCFalse (getConflictFlag stateA) (getM stateA) (getC stateA)\<close>
        InvariantCFalseAfterUnitPropagate[of "getConflictFlag stateA" "getM stateA" "getC stateA" "getM stateB" "ul"]
      by simp
    moreover 
    have "InvariantCEntailed (getConflictFlag stateB) (getF stateB) (getC stateB)"
      using \<open>getF stateB = getF stateA\<close> 
        \<open>getConflictFlag stateB = getConflictFlag stateA\<close>
        \<open>getC stateB = getC stateA\<close>
        \<open>InvariantCEntailed (getConflictFlag stateA) (getF stateA) (getC stateA)\<close>
      by simp
    ultimately
    have ?thesis
      unfolding invariantsHoldInState_def
      by auto
  }
  moreover
  {
    assume "appliedConflict stateA stateB"
    then obtain clause::Clause where
      "getConflictFlag stateA = False"
      "formulaEntailsClause (getF stateA) clause"
      "clauseFalse clause (elements (getM stateA))"
      "getF stateB = getF stateA"
      "getM stateB = getM stateA"
      "getConflictFlag stateB = True"
      "getC stateB = clause"
    unfolding appliedConflict_def
    by auto
  
    have "InvariantVarsM (getM stateB) F0 decisionVars"
      using \<open>InvariantVarsM (getM stateA) F0 decisionVars\<close>
        \<open>getM stateB = getM stateA\<close>
      by simp
    moreover
    have "InvariantVarsF (getF stateB) F0 decisionVars"
      using \<open>InvariantVarsF (getF stateA) F0 decisionVars\<close>
        \<open>getF stateB = getF stateA\<close>
      by simp
    moreover
    have "InvariantConsistent (getM stateB)"
      using \<open>InvariantConsistent (getM stateA)\<close>
        \<open>getM stateB = getM stateA\<close>
      by simp
    moreover
    have "InvariantUniq (getM stateB)"
      using \<open>InvariantUniq (getM stateA)\<close>
        \<open>getM stateB = getM stateA\<close>
      by simp
    moreover
    have "InvariantReasonClauses (getF stateB) (getM stateB)"
      using \<open>InvariantReasonClauses (getF stateA) (getM stateA)\<close>
        \<open>getF stateB = getF stateA\<close>
        \<open>getM stateB = getM stateA\<close>
      by simp
    moreover
    have "InvariantEquivalent F0 (getF stateB)"
      using \<open>InvariantEquivalent F0 (getF stateA)\<close>
        \<open>getF stateB = getF stateA\<close>
      by simp
    moreover 
    have "InvariantCFalse (getConflictFlag stateB) (getM stateB) (getC stateB)"
      using
      \<open>clauseFalse clause (elements (getM stateA))\<close>
      \<open>getM stateB = getM stateA\<close>
      \<open>getConflictFlag stateB = True\<close>
      \<open>getC stateB = clause\<close>
      unfolding InvariantCFalse_def
      by simp
    moreover 
    have "InvariantCEntailed (getConflictFlag stateB) (getF stateB) (getC stateB)"
      unfolding InvariantCEntailed_def
      using
      \<open>getConflictFlag stateB = True\<close>
      \<open>formulaEntailsClause (getF stateA) clause\<close>
      \<open>getF stateB = getF stateA\<close>
      \<open>getC stateB = clause\<close>
      by simp
    ultimately
    have ?thesis
      unfolding invariantsHoldInState_def
      by auto
  }
  moreover
  {
    assume "appliedExplain stateA stateB"
    then obtain l::Literal and reason::Clause where
        "getConflictFlag stateA = True"
        "l el getC stateA"
        "formulaEntailsClause (getF stateA) reason"
        "isReason reason (opposite l) (elements (getM stateA))"
        "getF stateB = getF stateA"
        "getM stateB = getM stateA"
        "getConflictFlag stateB = True"
        "getC stateB = resolve (getC stateA) reason l"
      unfolding appliedExplain_def
      by auto

    have "InvariantVarsM (getM stateB) F0 decisionVars"
      using \<open>InvariantVarsM (getM stateA) F0 decisionVars\<close>
        \<open>getM stateB = getM stateA\<close>
      by simp
    moreover
    have "InvariantVarsF (getF stateB) F0 decisionVars"
      using \<open>InvariantVarsF (getF stateA) F0 decisionVars\<close>
        \<open>getF stateB = getF stateA\<close>
      by simp
    moreover
    have "InvariantConsistent (getM stateB)"
      using 
        \<open>getM stateB = getM stateA\<close>
        \<open>InvariantConsistent (getM stateA)\<close>
      by simp
    moreover
    have "InvariantUniq (getM stateB)"
      using 
        \<open>getM stateB = getM stateA\<close>
        \<open>InvariantUniq (getM stateA)\<close>
      by simp
    moreover
    have "InvariantReasonClauses (getF stateB) (getM stateB)"
      using 
        \<open>getF stateB = getF stateA\<close>
        \<open>getM stateB = getM stateA\<close>
        \<open>InvariantReasonClauses (getF stateA) (getM stateA)\<close>
      by simp
    moreover
    have "InvariantEquivalent F0 (getF stateB)"
      using 
        \<open>getF stateB = getF stateA\<close>
        \<open>InvariantEquivalent F0 (getF stateA)\<close>
      by simp
    moreover 
    have "InvariantCFalse (getConflictFlag stateB) (getM stateB) (getC stateB)"
      using 
        \<open>InvariantCFalse (getConflictFlag stateA) (getM stateA) (getC stateA)\<close>
        \<open>l el getC stateA\<close>
        \<open>isReason reason (opposite l) (elements (getM stateA))\<close>
        \<open>getM stateB = getM stateA\<close>
        \<open>getC stateB = resolve (getC stateA) reason l\<close>
        \<open>getConflictFlag stateA = True\<close>
        \<open>getConflictFlag stateB = True\<close>
        InvariantCFalseAfterExplain[of "getConflictFlag stateA" "getM stateA" "getC stateA" "opposite l" "reason" "getC stateB"]
      by simp
    moreover 
    have "InvariantCEntailed (getConflictFlag stateB) (getF stateB) (getC stateB)"
      using 
        \<open>InvariantCEntailed (getConflictFlag stateA) (getF stateA) (getC stateA)\<close>
        \<open>l el getC stateA\<close>
        \<open>isReason reason (opposite l) (elements (getM stateA))\<close>
        \<open>getF stateB = getF stateA\<close>
        \<open>getC stateB = resolve (getC stateA) reason l\<close>
        \<open>getConflictFlag stateA = True\<close>
        \<open>getConflictFlag stateB = True\<close>
        \<open>formulaEntailsClause (getF stateA) reason\<close>
        InvariantCEntailedAfterExplain[of "getConflictFlag stateA" "getF stateA" "getC stateA" "reason" "getC stateB" "opposite l"]
      by simp
    moreover 
    ultimately
    have ?thesis
      unfolding invariantsHoldInState_def
      by auto
  }
  moreover
  {
    assume "appliedLearn stateA stateB"
    hence
      "getConflictFlag stateA = True"
      "\<not>  getC stateA el getF stateA"
      "getF stateB = getF stateA @ [getC stateA]"
      "getM stateB = getM stateA"
      "getConflictFlag stateB = True"
      "getC stateB = getC stateA"
      unfolding appliedLearn_def
      by auto
    
    from \<open>getConflictFlag stateA = True\<close> \<open>InvariantCEntailed (getConflictFlag stateA) (getF stateA) (getC stateA)\<close> 
    have "formulaEntailsClause (getF stateA) (getC stateA)"
      unfolding InvariantCEntailed_def
      by simp

    have "InvariantVarsM (getM stateB) F0 decisionVars"
      using \<open>InvariantVarsM (getM stateA) F0 decisionVars\<close>
        \<open>getM stateB = getM stateA\<close>
      by simp
    moreover
    from \<open>InvariantCFalse (getConflictFlag stateA) (getM stateA) (getC stateA)\<close> \<open>getConflictFlag stateA = True\<close>
    have "clauseFalse (getC stateA) (elements (getM stateA))"
      unfolding InvariantCFalse_def
      by simp
    with \<open>InvariantVarsM (getM stateA) F0 decisionVars\<close>
    have "(vars (getC stateA)) \<subseteq> vars F0 \<union> decisionVars"
        unfolding InvariantVarsM_def
        using valuationContainsItsFalseClausesVariables[of "getC stateA" "elements (getM stateA)"]
        by simp
    hence "InvariantVarsF (getF stateB) F0 decisionVars"
      using \<open>getF stateB = getF stateA @ [getC stateA]\<close>
        \<open>InvariantVarsF (getF stateA) F0 decisionVars\<close>
        InvariantVarsFAfterLearn [of "getF stateA" "F0" "decisionVars" "getC stateA" "getF stateB"]
      by simp
    moreover
    have "InvariantConsistent (getM stateB)"
      using \<open>InvariantConsistent (getM stateA)\<close>
        \<open>getM stateB = getM stateA\<close>
      by simp
    moreover
    have "InvariantUniq (getM stateB)"
      using \<open>InvariantUniq (getM stateA)\<close>
        \<open>getM stateB = getM stateA\<close>
      by simp
    moreover
    have "InvariantReasonClauses (getF stateB) (getM stateB)"
      using
        \<open>InvariantReasonClauses (getF stateA) (getM stateA)\<close>
        \<open>formulaEntailsClause (getF stateA) (getC stateA)\<close>
        \<open>getF stateB = getF stateA @ [getC stateA]\<close>
        \<open>getM stateB = getM stateA\<close>
        InvariantReasonClausesAfterLearn[of "getF stateA" "getM stateA" "getC stateA" "getF stateB"]
      by simp
    moreover
    have "InvariantEquivalent F0 (getF stateB)"
      using
        \<open>InvariantEquivalent F0 (getF stateA)\<close>
        \<open>formulaEntailsClause (getF stateA) (getC stateA)\<close>
        \<open>getF stateB = getF stateA @ [getC stateA]\<close>
        InvariantEquivalentAfterLearn[of "F0" "getF stateA" "getC stateA" "getF stateB"]
      by simp
    moreover 
    have "InvariantCFalse (getConflictFlag stateB) (getM stateB) (getC stateB)"
      using \<open>InvariantCFalse (getConflictFlag stateA) (getM stateA) (getC stateA)\<close>
        \<open>getM stateB = getM stateA\<close>
        \<open>getConflictFlag stateA = True\<close>
        \<open>getConflictFlag stateB = True\<close>
        \<open>getM stateB = getM stateA\<close>
        \<open>getC stateB = getC stateA\<close>
      by simp
    moreover 
    have "InvariantCEntailed (getConflictFlag stateB) (getF stateB) (getC stateB)"
      using
        \<open>InvariantCEntailed (getConflictFlag stateA) (getF stateA) (getC stateA)\<close>
        \<open>formulaEntailsClause (getF stateA) (getC stateA)\<close>
        \<open>getF stateB = getF stateA @ [getC stateA]\<close>
        \<open>getConflictFlag stateA = True\<close>
        \<open>getConflictFlag stateB = True\<close>
        \<open>getC stateB = getC stateA\<close>
        InvariantCEntailedAfterLearn[of "getConflictFlag stateA" "getF stateA" "getC stateA" "getF stateB"]
      by simp
    ultimately
    have ?thesis
      unfolding invariantsHoldInState_def
      by auto
  }
  moreover
  {
    assume "appliedBackjump stateA stateB"
    then obtain l::Literal and level::nat
      where 
      "getConflictFlag stateA = True"
      "isBackjumpLevel level l (getC stateA) (getM stateA)"
      "getF stateB = getF stateA"
      "getM stateB = prefixToLevel level (getM stateA) @ [(l, False)]"
      "getConflictFlag stateB = False"
      "getC stateB = []"
      unfolding appliedBackjump_def
      by auto
    with \<open>InvariantConsistent (getM stateA)\<close> \<open>InvariantUniq (getM stateA)\<close>
      \<open>InvariantCFalse (getConflictFlag stateA) (getM stateA) (getC stateA)\<close>
    have "isUnitClause (getC stateA) l (elements (prefixToLevel level (getM stateA)))"
      unfolding InvariantUniq_def
      unfolding InvariantConsistent_def
      unfolding InvariantCFalse_def
      using isBackjumpLevelEnsuresIsUnitInPrefix[of "getM stateA" "getC stateA" "level" "l"]
      by simp
    
    from \<open>getConflictFlag stateA = True\<close> \<open>InvariantCEntailed (getConflictFlag stateA) (getF stateA) (getC stateA)\<close>
    have "formulaEntailsClause (getF stateA) (getC stateA)"
      unfolding InvariantCEntailed_def
      by simp

    from \<open>isBackjumpLevel level l (getC stateA) (getM stateA)\<close>
    have "isLastAssertedLiteral (opposite l) (oppositeLiteralList (getC stateA)) (elements (getM stateA))"
      unfolding isBackjumpLevel_def
      by simp
    hence "l el getC stateA"
      unfolding isLastAssertedLiteral_def
      using literalElListIffOppositeLiteralElOppositeLiteralList[of "l" "getC stateA"]
      by simp

    have "isPrefix (prefixToLevel level (getM stateA)) (getM stateA)"
      by (simp add:isPrefixPrefixToLevel)

    from \<open>getConflictFlag stateA = True\<close> \<open>InvariantCEntailed (getConflictFlag stateA) (getF stateA) (getC stateA)\<close> 
    have "formulaEntailsClause (getF stateA) (getC stateA)"
      unfolding InvariantCEntailed_def
      by simp

    from \<open>getConflictFlag stateA = True\<close> \<open>InvariantCFalse (getConflictFlag stateA) (getM stateA) (getC stateA)\<close> 
    have "clauseFalse (getC stateA) (elements (getM stateA))"
      unfolding InvariantCFalse_def
      by simp
    hence "vars (getC stateA) \<subseteq> vars (elements (getM stateA))"
      using valuationContainsItsFalseClausesVariables[of "getC stateA" "elements (getM stateA)"]
      by simp
    moreover
    from \<open>l el getC stateA\<close>
    have "var l \<in> vars (getC stateA)"
      using clauseContainsItsLiteralsVariable[of "l" "getC stateA"]
      by simp
    ultimately
    have "var l \<in> vars F0 \<union> decisionVars"
      using \<open>InvariantVarsM (getM stateA) F0 decisionVars\<close>
      unfolding InvariantVarsM_def
      by auto
    
    have "InvariantVarsM (getM stateB) F0 decisionVars"
      using \<open>InvariantVarsM (getM stateA) F0 decisionVars\<close>
        \<open>isUnitClause (getC stateA) l (elements (prefixToLevel level (getM stateA)))\<close>
        \<open>isPrefix (prefixToLevel level (getM stateA)) (getM stateA)\<close>
        \<open>var l \<in> vars F0 \<union> decisionVars\<close>
        \<open>formulaEntailsClause (getF stateA) (getC stateA)\<close>
        \<open>getF stateB = getF stateA\<close>
        \<open>getM stateB = prefixToLevel level (getM stateA) @ [(l, False)]\<close>
        InvariantVarsMAfterBackjump[of "getM stateA" "F0" "decisionVars" "prefixToLevel level (getM stateA)" "l" "getM stateB"]
      by simp
    moreover
    have "InvariantVarsF (getF stateB) F0 decisionVars"
      using \<open>InvariantVarsF (getF stateA) F0 decisionVars\<close>
        \<open>getF stateB = getF stateA\<close>
      by simp
    moreover
    have "InvariantConsistent (getM stateB)"
      using \<open>InvariantConsistent (getM stateA)\<close>
        \<open>isUnitClause (getC stateA) l (elements (prefixToLevel level (getM stateA)))\<close>
        \<open>isPrefix (prefixToLevel level (getM stateA)) (getM stateA)\<close>
        \<open>getM stateB = prefixToLevel level (getM stateA) @ [(l, False)]\<close>
        InvariantConsistentAfterBackjump[of "getM stateA" "prefixToLevel level (getM stateA)" "getC stateA" "l" "getM stateB"]
      by simp
    moreover
    have "InvariantUniq (getM stateB)"
      using \<open>InvariantUniq (getM stateA)\<close>
        \<open>isUnitClause (getC stateA) l (elements (prefixToLevel level (getM stateA)))\<close>
        \<open>isPrefix (prefixToLevel level (getM stateA)) (getM stateA)\<close>
        \<open>getM stateB = prefixToLevel level (getM stateA) @ [(l, False)]\<close>
        InvariantUniqAfterBackjump[of "getM stateA" "prefixToLevel level (getM stateA)" "getC stateA" "l" "getM stateB"]
      by simp
    moreover
    have "InvariantReasonClauses (getF stateB) (getM stateB)"
      using \<open>InvariantUniq (getM stateA)\<close> \<open>InvariantReasonClauses (getF stateA) (getM stateA)\<close>
        \<open>isUnitClause (getC stateA) l (elements (prefixToLevel level (getM stateA)))\<close>
        \<open>isPrefix (prefixToLevel level (getM stateA)) (getM stateA)\<close>
        \<open>formulaEntailsClause (getF stateA) (getC stateA)\<close>
        \<open>getF stateB = getF stateA\<close>
        \<open>getM stateB = prefixToLevel level (getM stateA) @ [(l, False)]\<close>
        InvariantReasonClausesAfterBackjump[of "getF stateA" "getM stateA"
        "prefixToLevel level (getM stateA)" "getC stateA"  "l" "getM stateB"]
      by simp
    moreover
    have "InvariantEquivalent F0 (getF stateB)"
      using
      \<open>InvariantEquivalent F0 (getF stateA)\<close>
      \<open>getF stateB = getF stateA\<close>
      by simp
    moreover 
    have "InvariantCFalse (getConflictFlag stateB) (getM stateB) (getC stateB)"
      using \<open>getConflictFlag stateB = False\<close>
      unfolding InvariantCFalse_def
      by simp
    moreover 
    have "InvariantCEntailed (getConflictFlag stateB) (getF stateB) (getC stateB)"
      using \<open>getConflictFlag stateB = False\<close>
      unfolding InvariantCEntailed_def
      by simp
    moreover
    ultimately
    have ?thesis
      unfolding invariantsHoldInState_def
      by auto
  }
  ultimately
  show ?thesis
    using \<open>transition stateA stateB F0 decisionVars\<close>
    unfolding transition_def
    by auto
qed

text\<open>The consequence is that invariants hold in all valid runs.\<close>
lemma invariantsHoldInValidRuns: 
  fixes F0 :: Formula and decisionVars :: "Variable set"
  assumes "invariantsHoldInState stateA F0 decisionVars" and
  "(stateA, stateB) \<in> transitionRelation F0 decisionVars"
  shows "invariantsHoldInState stateB F0 decisionVars"
using assms
using transitionsPreserveInvariants
using rtrancl_induct[of "stateA" "stateB" 
  "{(stateA, stateB). transition stateA stateB F0 decisionVars}" "\<lambda> x. invariantsHoldInState x F0 decisionVars"]
unfolding transitionRelation_def
by auto

lemma invariantsHoldInValidRunsFromInitialState:
  fixes F0 :: Formula and decisionVars :: "Variable set"
  assumes "isInitialState state0 F0" 
  and "(state0, state) \<in> transitionRelation F0 decisionVars"
  shows "invariantsHoldInState state F0 decisionVars"
proof-
  from \<open>isInitialState state0 F0\<close>
  have "invariantsHoldInState state0 F0 decisionVars"
    by (simp add:invariantsHoldInInitialState)
  with assms
  show ?thesis
    using invariantsHoldInValidRuns [of "state0"  "F0" "decisionVars" "state"]
    by simp
qed

text\<open>
 In the following text we will show that there are two kinds of states:
 \begin{enumerate}
  \item \textit{UNSAT} states where @{term "getConflictFlag state = True"}
  and @{term "getC state = []"}. 
  \item \textit{SAT} states where @{term "getConflictFlag state = False"}, 
  @{term "\<not> formulaFalse F0 (elements (getM state))"} and 
  @{term "vars (elements (getM state)) \<supseteq> decisionVars"}. 
 \end{enumerate}
  
 The soundness theorems claim that if \textit{UNSAT} state is reached
 the formula is unsatisfiable and if \textit{SAT} state is reached,
 the formula is satisfiable.

 Completeness theorems claim that every final state is either
 \textit{UNSAT} or \textit{SAT}. A consequence of this and soundness
 theorems, is that if formula is unsatisfiable the solver will finish
 in an \textit{UNSAT} state, and if the formula is satisfiable the
 solver will finish in a \textit{SAT} state.
\<close>


(******************************************************************************)
subsection\<open>Soundness\<close>
(******************************************************************************)

theorem soundnessForUNSAT:
  fixes F0 :: Formula and decisionVars :: "Variable set" and state0 :: State and state :: State
  assumes
  "isInitialState state0 F0" and
  "(state0, state) \<in> transitionRelation F0 decisionVars"

  "getConflictFlag state = True" and
  "getC state = []"
  shows "\<not> satisfiable F0"
proof-
  from \<open>isInitialState state0 F0\<close> \<open>(state0, state) \<in> transitionRelation F0 decisionVars\<close>
  have "invariantsHoldInState state F0 decisionVars" 
    using invariantsHoldInValidRunsFromInitialState
    by simp
  hence 
    "InvariantEquivalent F0 (getF state)"
    "InvariantCEntailed (getConflictFlag state) (getF state) (getC state)"
    unfolding invariantsHoldInState_def
    by auto
  with \<open>getConflictFlag state = True\<close> \<open>getC state = []\<close>
  show ?thesis
    by (simp add:unsatReportExtensiveExplain)
qed

theorem soundnessForSAT:
  fixes F0 :: Formula and decisionVars :: "Variable set" and state0 :: State and state :: State
  assumes 
  "vars F0 \<subseteq> decisionVars" and

  "isInitialState state0 F0" and
  "(state0, state) \<in> transitionRelation F0 decisionVars" and

  "getConflictFlag state = False"
  "\<not> formulaFalse (getF state) (elements (getM state))"
  "vars (elements (getM state)) \<supseteq> decisionVars"  
  shows 
  "model (elements (getM state)) F0"
proof-
  from \<open>isInitialState state0 F0\<close> \<open>(state0, state) \<in> transitionRelation F0 decisionVars\<close>
  have "invariantsHoldInState state F0 decisionVars" 
    using invariantsHoldInValidRunsFromInitialState
    by simp
  hence 
    "InvariantConsistent (getM state)" 
    "InvariantEquivalent F0 (getF state)"
    "InvariantVarsF (getF state) F0 decisionVars"
    unfolding invariantsHoldInState_def
    by auto
  with assms
  show ?thesis
  using satReport[of "F0" "decisionVars" "getF state" "getM state"]
  by simp
qed



(**************************************************************************)
(*                          T E R M I N A T I O N                         *)
(**************************************************************************)
subsection\<open>Termination\<close>
text\<open>We now define a termination ordering which is a lexicographic combination
of @{term lexLessRestricted} trail ordering, @{term boolLess} conflict flag ordering, 
@{term multLess} conflict clause ordering and @{term learnLess} formula ordering. 
This ordering will be central in termination proof.\<close>

definition "lexLessState (F0::Formula) decisionVars == {((stateA::State), (stateB::State)).
  (getM stateA, getM stateB) \<in> lexLessRestricted (vars F0 \<union> decisionVars)}"
definition "boolLessState == {((stateA::State), (stateB::State)).
  getM stateA = getM stateB \<and>
  (getConflictFlag stateA, getConflictFlag stateB) \<in> boolLess}"
definition "multLessState == {((stateA::State), (stateB::State)).
  getM stateA = getM stateB \<and>
  getConflictFlag stateA = getConflictFlag stateB \<and>
  (getC stateA, getC stateB) \<in> multLess (getM stateA)}"
definition "learnLessState == {((stateA::State), (stateB::State)).
  getM stateA = getM stateB \<and>
  getConflictFlag stateA = getConflictFlag stateB \<and>
  getC stateA = getC stateB \<and>
  (getF stateA, getF stateB) \<in> learnLess (getC stateA)}"

definition "terminationLess F0 decisionVars == {((stateA::State), (stateB::State)).
  (stateA,stateB) \<in> lexLessState F0 decisionVars \<or>
  (stateA,stateB) \<in> boolLessState   \<or>
  (stateA,stateB) \<in> multLessState   \<or>
  (stateA,stateB) \<in> learnLessState}"

text\<open>We want to show that every valid transition decreases a state
  with respect to the constructed termination ordering.\<close>

text\<open>First we show that $Decide$, $UnitPropagate$ and $Backjump$ rule
decrease the trail with respect to the restricted trail ordering
@{term lexLessRestricted}. Invariants ensure that trails are indeed
uniq, consistent and with finite variable sets.\<close>
lemma trailIsDecreasedByDeciedUnitPropagateAndBackjump:
  fixes stateA::State and stateB::State
  assumes "invariantsHoldInState stateA F0 decisionVars" and
  "appliedDecide stateA stateB decisionVars \<or> appliedUnitPropagate stateA stateB F0 decisionVars \<or> appliedBackjump stateA stateB"
  shows "(getM stateB, getM stateA) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
proof-
  from \<open>appliedDecide stateA stateB decisionVars \<or> appliedUnitPropagate stateA stateB F0 decisionVars \<or> appliedBackjump stateA stateB\<close>
    \<open>invariantsHoldInState stateA F0 decisionVars\<close> 
  have "invariantsHoldInState stateB F0 decisionVars"
      using transitionsPreserveInvariants
      unfolding transition_def
      by auto
    from \<open>invariantsHoldInState stateA F0 decisionVars\<close> 
    have *: "uniq (elements (getM stateA))" "consistent (elements (getM stateA))" "vars (elements (getM stateA)) \<subseteq> vars F0 \<union> decisionVars"
      unfolding invariantsHoldInState_def
      unfolding InvariantVarsM_def
      unfolding InvariantConsistent_def
      unfolding InvariantUniq_def
      by auto
    from \<open>invariantsHoldInState stateB F0 decisionVars\<close> 
    have **: "uniq (elements (getM stateB))" "consistent (elements (getM stateB))" "vars (elements (getM stateB)) \<subseteq> vars F0 \<union> decisionVars"
      unfolding invariantsHoldInState_def
      unfolding InvariantVarsM_def
      unfolding InvariantConsistent_def
      unfolding InvariantUniq_def
      by auto
  {
    assume "appliedDecide stateA stateB decisionVars"
    hence "(getM stateB, getM stateA) \<in> lexLess"
      unfolding appliedDecide_def
      by (auto simp add:lexLessAppend)
    with * ** 
    have "((getM stateB), (getM stateA)) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
      unfolding lexLessRestricted_def
      by auto
  }
  moreover
  {
    assume "appliedUnitPropagate stateA stateB F0 decisionVars"
    hence "(getM stateB, getM stateA) \<in> lexLess"
      unfolding appliedUnitPropagate_def
      by (auto simp add:lexLessAppend)
    with * ** 
    have "(getM stateB, getM stateA) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
      unfolding lexLessRestricted_def
      by auto
  }
  moreover
  {
    assume "appliedBackjump stateA stateB"
    then obtain l::Literal and level::nat
      where 
      "getConflictFlag stateA = True"
      "isBackjumpLevel level l (getC stateA) (getM stateA)"
      "getF stateB = getF stateA"
      "getM stateB = prefixToLevel level (getM stateA) @ [(l, False)]"
      "getConflictFlag stateB = False"
      "getC stateB = []"
      unfolding appliedBackjump_def
      by auto
    
    from \<open>isBackjumpLevel level l (getC stateA) (getM stateA)\<close>
    have "isLastAssertedLiteral (opposite l) (oppositeLiteralList (getC stateA)) (elements (getM stateA))"
      unfolding isBackjumpLevel_def
      by simp
    hence "(opposite l) el elements (getM stateA)"
      unfolding isLastAssertedLiteral_def
      by simp
    hence "elementLevel (opposite l) (getM stateA) <= currentLevel (getM stateA)"
      by (simp add: elementLevelLeqCurrentLevel)
    moreover
    from \<open>isBackjumpLevel level l (getC stateA) (getM stateA)\<close>
    have "0 \<le> level" and "level < elementLevel (opposite l) (getM stateA)" 
      unfolding isBackjumpLevel_def 
      using \<open>isLastAssertedLiteral (opposite l) (oppositeLiteralList (getC stateA)) (elements (getM stateA))\<close>
      by auto
    ultimately 
    have "level < currentLevel (getM stateA)" 
      by simp
    with \<open>0 \<le> level\<close> \<open>getM stateB = prefixToLevel level (getM stateA) @ [(l, False)]\<close>
    have "(getM stateB, getM stateA) \<in> lexLess"
      by (simp add:lexLessBackjump)
    with * ** 
    have "(getM stateB, getM stateA) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
      unfolding lexLessRestricted_def
      by auto
  }
  ultimately
  show ?thesis
    using assms
    by auto
qed

text\<open>Next we show that $Conflict$ decreases the conflict flag in the @{term boolLess} ordering.\<close>
lemma conflictFlagIsDecreasedByConflict:
  fixes stateA::State and stateB::State
  assumes "appliedConflict stateA stateB"
  shows "getM stateA = getM stateB" and "(getConflictFlag stateB, getConflictFlag stateA) \<in> boolLess"
using assms
unfolding appliedConflict_def
unfolding boolLess_def
by auto

text\<open>Next we show that $Explain$ decreases the conflict clause with
respect to the @{term multLess} clause ordering.\<close>
lemma conflictClauseIsDecreasedByExplain:
  fixes stateA::State and stateB::State
  assumes "appliedExplain stateA stateB"
  shows 
  "getM stateA = getM stateB" and 
  "getConflictFlag stateA = getConflictFlag stateB" and 
  "(getC stateB, getC stateA) \<in> multLess (getM stateA)"
proof-
  from \<open>appliedExplain stateA stateB\<close>
  obtain l::Literal and reason::Clause where
    "getConflictFlag stateA = True"
    "l el (getC stateA)"
    "isReason reason (opposite l) (elements (getM stateA))"
    "getF stateB = getF stateA"
    "getM stateB = getM stateA"
    "getConflictFlag stateB = True"
    "getC stateB = resolve (getC stateA) reason l"
    unfolding appliedExplain_def
    by auto
  thus "getM stateA = getM stateB" "getConflictFlag stateA = getConflictFlag stateB" "(getC stateB, getC stateA) \<in> multLess (getM stateA)"
    using multLessResolve[of "opposite l" "getC stateA" "reason" "getM stateA"]
    by auto
qed


text\<open>Finally, we show that $Learn$ decreases the formula in the @{term learnLess} formula ordering.\<close>
lemma formulaIsDecreasedByLearn:
  fixes stateA::State and stateB::State
  assumes "appliedLearn stateA stateB"
  shows 
  "getM stateA = getM stateB" and 
  "getConflictFlag stateA = getConflictFlag stateB" and 
  "getC stateA = getC stateB" and 
  "(getF stateB, getF stateA) \<in> learnLess (getC stateA)"
proof-
  from \<open>appliedLearn stateA stateB\<close>
  have
      "getConflictFlag stateA = True"
      "\<not> getC stateA el getF stateA"
      "getF stateB = getF stateA @ [getC stateA]"
      "getM stateB = getM stateA"
      "getConflictFlag stateB = True"
      "getC stateB = getC stateA"
    unfolding appliedLearn_def
    by auto
  thus 
    "getM stateA = getM stateB"
    "getConflictFlag stateA = getConflictFlag stateB"
    "getC stateA = getC stateB"
    "(getF stateB, getF stateA) \<in> learnLess (getC stateA)"
    unfolding learnLess_def
    by auto
qed


text\<open>Now we can prove that every rule application decreases a state
with respect to the constructed termination ordering.\<close>
lemma stateIsDecreasedByValidTransitions:
  fixes stateA::State and stateB::State
  assumes "invariantsHoldInState stateA F0 decisionVars" and "transition stateA stateB F0 decisionVars"
  shows "(stateB, stateA) \<in> terminationLess F0 decisionVars"
proof-
  {
    assume "appliedDecide stateA stateB decisionVars \<or> appliedUnitPropagate stateA stateB F0 decisionVars \<or> appliedBackjump stateA stateB"
    with \<open>invariantsHoldInState stateA F0 decisionVars\<close>
    have "(getM stateB, getM stateA) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
      using trailIsDecreasedByDeciedUnitPropagateAndBackjump
      by simp
    hence "(stateB, stateA) \<in> lexLessState F0 decisionVars"
      unfolding lexLessState_def
      by simp
    hence "(stateB, stateA) \<in> terminationLess F0 decisionVars"
      unfolding terminationLess_def
      by simp
  }
  moreover
  {
    assume "appliedConflict stateA stateB"
    hence "getM stateA = getM stateB" "(getConflictFlag stateB, getConflictFlag stateA) \<in> boolLess"
      using conflictFlagIsDecreasedByConflict
      by auto
    hence "(stateB, stateA) \<in> boolLessState"
      unfolding boolLessState_def
      by simp
    hence "(stateB, stateA) \<in> terminationLess F0 decisionVars"
      unfolding terminationLess_def
      by simp
  }
  moreover
  {
    assume "appliedExplain stateA stateB"
    hence "getM stateA = getM stateB"
      "getConflictFlag stateA = getConflictFlag stateB"
      "(getC stateB, getC stateA) \<in> multLess (getM stateA)"
      using conflictClauseIsDecreasedByExplain
      by auto
    hence "(stateB, stateA) \<in> multLessState"
      unfolding multLessState_def
      unfolding multLess_def
      by simp
    hence "(stateB, stateA) \<in> terminationLess F0 decisionVars"
      unfolding terminationLess_def
      by simp
  }
  moreover
  {
    assume "appliedLearn stateA stateB"
    hence 
      "getM stateA = getM stateB"
      "getConflictFlag stateA = getConflictFlag stateB"
      "getC stateA = getC stateB"
      "(getF stateB, getF stateA) \<in> learnLess (getC stateA)"
      using formulaIsDecreasedByLearn
      by auto
    hence "(stateB, stateA) \<in> learnLessState"
      unfolding learnLessState_def
      by simp
    hence "(stateB, stateA) \<in> terminationLess F0 decisionVars"
      unfolding terminationLess_def
      by simp
  }
  ultimately
  show ?thesis
    using \<open>transition stateA stateB F0 decisionVars\<close>
    unfolding transition_def
    by auto
qed

text\<open>The minimal states with respect to the termination ordering are
  final i.e., no further transition rules are applicable.\<close>
definition 
"isMinimalState stateMin F0 decisionVars == (\<forall> state::State. (state, stateMin) \<notin> terminationLess F0 decisionVars)"

lemma minimalStatesAreFinal:
  fixes stateA::State
  assumes
  "invariantsHoldInState state F0 decisionVars" and "isMinimalState state F0 decisionVars"
  shows "isFinalState state F0 decisionVars"
proof-
  {
    assume "\<not> ?thesis"
    then obtain state'::State 
      where "transition state state' F0 decisionVars"
      unfolding isFinalState_def
      by auto
    with \<open>invariantsHoldInState state F0 decisionVars\<close> 
    have "(state', state) \<in> terminationLess F0 decisionVars"
      using stateIsDecreasedByValidTransitions[of "state" "F0" "decisionVars" "state'"]
      unfolding transition_def
      by auto
    with \<open>isMinimalState state F0 decisionVars\<close> 
    have False
      unfolding isMinimalState_def
      by auto
  }
  thus ?thesis
    by auto
qed


text\<open>We now prove that termination ordering is well founded. We
start with several auxiliary lemmas, one for each component of the termination ordering.\<close>
lemma wfLexLessState: 
  fixes decisionVars :: "Variable set" and F0 :: Formula
  assumes "finite decisionVars"
  shows "wf (lexLessState F0 decisionVars)"
unfolding wf_eq_minimal
proof-
  show "\<forall>Q state. state \<in> Q \<longrightarrow> (\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> lexLessState F0 decisionVars \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix Q :: "State set" and state :: State
      assume "state \<in> Q"
      let ?Q1 = "{M::LiteralTrail. \<exists> state. state \<in> Q \<and> (getM state) = M}"
      from \<open>state \<in> Q\<close>
      have "getM state \<in> ?Q1"
        by auto
      from \<open>finite decisionVars\<close> 
      have "finite (vars F0 \<union> decisionVars)"
        using finiteVarsFormula[of "F0"]
        by simp
      hence "wf (lexLessRestricted (vars F0 \<union> decisionVars))"
      using  wfLexLessRestricted[of "vars F0 \<union> decisionVars"]
      by simp
    with \<open>getM state \<in> ?Q1\<close>
      obtain Mmin where "Mmin \<in> ?Q1" "\<forall>M'. (M', Mmin) \<in> lexLessRestricted (vars F0 \<union> decisionVars) \<longrightarrow> M' \<notin> ?Q1"
        unfolding wf_eq_minimal
        apply (erule_tac x="?Q1" in allE)
        apply (erule_tac x="getM state" in allE)
        by auto 
      from \<open>Mmin \<in> ?Q1\<close> obtain stateMin
        where "stateMin \<in> Q" "(getM stateMin) = Mmin"
        by auto
      have "\<forall>state'. (state', stateMin) \<in> lexLessState F0 decisionVars \<longrightarrow> state' \<notin> Q"
      proof
        fix state'
        show "(state', stateMin) \<in> lexLessState F0 decisionVars \<longrightarrow> state' \<notin> Q"
        proof
          assume "(state', stateMin) \<in> lexLessState F0 decisionVars"
          hence "(getM state', getM stateMin) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
            unfolding lexLessState_def
            by auto
          from \<open>\<forall>M'. (M', Mmin) \<in> lexLessRestricted (vars F0 \<union>  decisionVars) \<longrightarrow> M' \<notin> ?Q1\<close>
            \<open>(getM state', getM stateMin) \<in> lexLessRestricted (vars F0 \<union> decisionVars)\<close> \<open>getM stateMin = Mmin\<close>
          have "getM state' \<notin> ?Q1"
            by simp
          with \<open>getM stateMin = Mmin\<close>
          show "state' \<notin> Q"
            by auto
        qed
      qed
      with \<open>stateMin \<in> Q\<close>
      have "\<exists> stateMin \<in> Q. (\<forall>state'. (state', stateMin) \<in> lexLessState F0 decisionVars \<longrightarrow> state' \<notin> Q)"
        by auto
    }
    thus ?thesis
      by auto
  qed
qed
     
lemma wfBoolLessState: 
  shows "wf boolLessState"
unfolding wf_eq_minimal
proof-
  show "\<forall>Q state. state \<in> Q \<longrightarrow> (\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> boolLessState \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix Q :: "State set" and state :: State
      assume "state \<in> Q"
      let ?M = "(getM state)"
      let ?Q1 = "{b::bool. \<exists> state. state \<in> Q \<and> (getM state) = ?M \<and> (getConflictFlag state) = b}"
      from \<open>state \<in> Q\<close> 
      have "getConflictFlag state \<in> ?Q1"
        by auto
      with wfBoolLess
      obtain bMin where "bMin \<in> ?Q1" "\<forall>b'. (b', bMin) \<in> boolLess \<longrightarrow> b' \<notin> ?Q1"
        unfolding wf_eq_minimal
        apply (erule_tac x="?Q1" in allE)
        apply (erule_tac x="getConflictFlag state" in allE)
        by auto
      from \<open>bMin \<in> ?Q1\<close> obtain stateMin
        where "stateMin \<in> Q" "(getM stateMin) = ?M" "getConflictFlag stateMin = bMin"
        by auto
      have "\<forall>state'. (state', stateMin) \<in> boolLessState \<longrightarrow> state' \<notin> Q"
      proof
        fix state'
        show "(state', stateMin) \<in> boolLessState \<longrightarrow> state' \<notin> Q"
        proof
          assume "(state', stateMin) \<in> boolLessState"
          with \<open>getM stateMin = ?M\<close> 
          have "getM state' = getM stateMin" "(getConflictFlag state', getConflictFlag stateMin) \<in> boolLess"
            unfolding boolLessState_def
            by auto
          from \<open>\<forall>b'. (b', bMin) \<in> boolLess \<longrightarrow> b' \<notin> ?Q1\<close> 
            \<open>(getConflictFlag state', getConflictFlag stateMin) \<in> boolLess\<close> \<open>getConflictFlag stateMin = bMin\<close>
          have "getConflictFlag state' \<notin> ?Q1"
            by simp
          with \<open>getM state' = getM stateMin\<close> \<open>getM stateMin = ?M\<close>
          show "state' \<notin> Q"
            by auto
        qed
      qed
      with \<open>stateMin \<in> Q\<close> 
      have "\<exists> stateMin \<in> Q. (\<forall>state'. (state', stateMin) \<in> boolLessState \<longrightarrow> state' \<notin> Q)"
        by auto
    }
    thus ?thesis
      by auto
  qed
qed

lemma wfMultLessState:
  shows "wf multLessState"
  unfolding wf_eq_minimal
proof-
  show "\<forall>Q state. state \<in> Q \<longrightarrow> (\<exists> stateMin \<in> Q. \<forall>state'. (state', stateMin) \<in> multLessState \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix Q :: "State set" and state :: State
      assume "state \<in> Q"
      let ?M = "(getM state)"
      let ?Q1 = "{C::Clause. \<exists> state. state \<in> Q \<and> (getM state) = ?M \<and> (getC state) = C}"
      from \<open>state \<in> Q\<close> 
      have "getC state \<in> ?Q1"
        by auto   
      with wfMultLess[of "?M"]
      obtain Cmin where "Cmin \<in> ?Q1" "\<forall>C'. (C', Cmin) \<in> multLess ?M \<longrightarrow> C' \<notin> ?Q1"
        unfolding wf_eq_minimal
        apply (erule_tac x="?Q1" in allE)
        apply (erule_tac x="getC state" in allE)
        by auto
      from \<open>Cmin \<in> ?Q1\<close> obtain stateMin
        where "stateMin \<in> Q" "(getM stateMin) = ?M" "getC stateMin = Cmin"
        by auto
      have "\<forall>state'. (state', stateMin) \<in> multLessState \<longrightarrow> state' \<notin> Q"
      proof
        fix state'
        show "(state', stateMin) \<in> multLessState \<longrightarrow> state' \<notin> Q"
        proof
          assume "(state', stateMin) \<in> multLessState"
          with \<open>getM stateMin = ?M\<close>
          have "getM state' = getM stateMin" "(getC state', getC stateMin) \<in> multLess ?M"
            unfolding multLessState_def
            by auto
          from \<open>\<forall>C'. (C', Cmin) \<in> multLess ?M \<longrightarrow> C' \<notin> ?Q1\<close>
            \<open>(getC state', getC stateMin) \<in> multLess ?M\<close> \<open>getC stateMin = Cmin\<close>
          have "getC state' \<notin> ?Q1"
            by simp
          with \<open>getM state' = getM stateMin\<close> \<open>getM stateMin = ?M\<close>
          show "state' \<notin> Q"
            by auto
        qed
      qed
      with \<open>stateMin \<in> Q\<close> 
      have "\<exists> stateMin \<in> Q. (\<forall>state'. (state', stateMin) \<in> multLessState \<longrightarrow> state' \<notin> Q)"
        by auto
    }
    thus ?thesis
      by auto
  qed
qed

lemma wfLearnLessState:
  shows "wf learnLessState"
  unfolding wf_eq_minimal
proof-
  show "\<forall>Q state. state \<in> Q \<longrightarrow> (\<exists> stateMin \<in> Q. \<forall>state'. (state', stateMin) \<in> learnLessState \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix Q :: "State set" and state :: State
      assume "state \<in> Q"
      let ?M = "(getM state)"
      let ?C = "(getC state)"
      let ?conflictFlag = "(getConflictFlag state)"
      let ?Q1 = "{F::Formula. \<exists> state. state \<in> Q \<and> 
        (getM state) = ?M \<and>  (getConflictFlag state) = ?conflictFlag \<and> (getC state) = ?C \<and> (getF state) = F}"
      from \<open>state \<in> Q\<close> 
      have "getF state \<in> ?Q1"
        by auto      
      with wfLearnLess[of "?C"]
      obtain Fmin where "Fmin \<in> ?Q1" "\<forall>F'. (F', Fmin) \<in> learnLess ?C \<longrightarrow> F' \<notin> ?Q1"
        unfolding wf_eq_minimal
        apply (erule_tac x="?Q1" in allE)
        apply (erule_tac x="getF state" in allE)
        by auto
      from \<open>Fmin \<in> ?Q1\<close> obtain stateMin
        where "stateMin \<in> Q" "(getM stateMin) = ?M" "getC stateMin = ?C" "getConflictFlag stateMin = ?conflictFlag" "getF stateMin = Fmin"
        by auto
      have "\<forall>state'. (state', stateMin) \<in> learnLessState \<longrightarrow> state' \<notin> Q"
      proof
        fix state'
        show "(state', stateMin) \<in> learnLessState \<longrightarrow> state' \<notin> Q"
        proof
          assume "(state', stateMin) \<in> learnLessState"
          with \<open>getM stateMin = ?M\<close> \<open>getC stateMin = ?C\<close> \<open>getConflictFlag stateMin = ?conflictFlag\<close>
          have "getM state' = getM stateMin" "getC state' = getC stateMin" 
            "getConflictFlag state' = getConflictFlag stateMin" "(getF state', getF stateMin) \<in> learnLess ?C"
            unfolding learnLessState_def
            by auto
          from \<open>\<forall>F'. (F', Fmin) \<in> learnLess ?C \<longrightarrow> F' \<notin> ?Q1\<close>
            \<open>(getF state', getF stateMin) \<in> learnLess ?C\<close> \<open>getF stateMin = Fmin\<close>
          have "getF state' \<notin> ?Q1"
            by simp
          with \<open>getM state' = getM stateMin\<close> \<open>getC state' = getC stateMin\<close> \<open>getConflictFlag state' = getConflictFlag stateMin\<close>
            \<open>getM stateMin = ?M\<close> \<open>getC stateMin = ?C\<close> \<open>getConflictFlag stateMin = ?conflictFlag\<close> \<open>getF stateMin = Fmin\<close>
          show "state' \<notin> Q"
            by auto
        qed
      qed
      with \<open>stateMin \<in> Q\<close> 
      have "\<exists> stateMin \<in> Q. (\<forall>state'. (state', stateMin) \<in> learnLessState \<longrightarrow> state' \<notin> Q)"
        by auto
    }
    thus ?thesis
      by auto
  qed
qed

text\<open>Now we can prove the following key lemma which shows that the
termination ordering is well founded.\<close>
lemma wfTerminationLess:
  fixes decisionVars::"Variable set" and F0::"Formula"
  assumes "finite decisionVars"
  shows "wf (terminationLess F0 decisionVars)"
  unfolding wf_eq_minimal
proof-
  show "\<forall>Q state. state \<in> Q \<longrightarrow> (\<exists> stateMin \<in> Q. \<forall>state'. (state', stateMin) \<in> terminationLess F0 decisionVars \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix Q::"State set"
      fix state::State
      assume "state \<in> Q"

      from \<open>finite decisionVars\<close>
      have "wf (lexLessState F0 decisionVars)"
        using wfLexLessState[of "decisionVars" "F0"]
        by simp

      with \<open>state \<in> Q\<close> obtain state0
        where "state0 \<in> Q" "\<forall>state'. (state', state0) \<in> lexLessState F0 decisionVars \<longrightarrow> state' \<notin> Q"
        unfolding wf_eq_minimal
        by auto
      let ?Q0 = "{state. state \<in> Q \<and> (getM state) = (getM state0)}"
      from \<open>state0 \<in> Q\<close>
      have "state0 \<in> ?Q0"
        by simp
      have "wf boolLessState"
        using wfBoolLessState
        .
      with \<open>state0 \<in> Q\<close> obtain state1
        where "state1 \<in> ?Q0" "\<forall>state'. (state', state1) \<in> boolLessState \<longrightarrow> state' \<notin> ?Q0"
        unfolding wf_eq_minimal
        apply (erule_tac x="?Q0" in allE)
        apply (erule_tac x="state0" in allE)
        by auto
      let ?Q1 = "{state. state \<in> Q \<and> getM state = getM state0 \<and> getConflictFlag state = getConflictFlag state1}"
      from \<open>state1 \<in> ?Q0\<close>
      have "state1 \<in> ?Q1"
        by simp
      have "wf multLessState"
        using wfMultLessState
        .
      with \<open>state1 \<in> ?Q1\<close> obtain state2
        where "state2 \<in> ?Q1" "\<forall>state'. (state', state2) \<in> multLessState \<longrightarrow> state' \<notin> ?Q1"
        unfolding wf_eq_minimal
        apply (erule_tac x="?Q1" in allE)
        apply (erule_tac x="state1" in allE)
        by auto
      let ?Q2 = "{state. state \<in> Q \<and> getM state = getM state0 \<and> 
        getConflictFlag state = getConflictFlag state1 \<and>  getC state = getC state2}"
      from \<open>state2 \<in> ?Q1\<close>
      have "state2 \<in> ?Q2"
        by simp
      have "wf learnLessState"
        using wfLearnLessState
        .
      with \<open>state2 \<in> ?Q2\<close> obtain state3
        where "state3 \<in> ?Q2" "\<forall>state'. (state', state3) \<in> learnLessState \<longrightarrow> state' \<notin> ?Q2"
        unfolding wf_eq_minimal
        apply (erule_tac x="?Q2" in allE)
        apply (erule_tac x="state2" in allE)
        by auto
      from \<open>state3 \<in> ?Q2\<close>
      have "state3 \<in> Q"
        by simp
      from \<open>state1 \<in> ?Q0\<close>
      have "getM state1 = getM state0"
        by simp
      from \<open>state2 \<in> ?Q1\<close>
      have "getM state2 = getM state0" "getConflictFlag state2 = getConflictFlag state1"
        by auto
      from \<open>state3 \<in> ?Q2\<close>
      have "getM state3 = getM state0" "getConflictFlag state3 = getConflictFlag state1" "getC state3 = getC state2"
        by auto
      let ?stateMin = state3
      have "\<forall>state'. (state', ?stateMin) \<in> terminationLess F0 decisionVars \<longrightarrow> state' \<notin> Q"
      proof
        fix state'
        show "(state', ?stateMin) \<in> terminationLess F0 decisionVars \<longrightarrow> state' \<notin> Q"
        proof
          assume "(state', ?stateMin) \<in> terminationLess F0 decisionVars"
          hence 
            "(state', ?stateMin) \<in> lexLessState F0 decisionVars \<or>
            (state', ?stateMin) \<in> boolLessState \<or>
            (state', ?stateMin) \<in> multLessState \<or>
            (state', ?stateMin) \<in> learnLessState"
            unfolding terminationLess_def
            by auto
          moreover
          {
            assume "(state', ?stateMin) \<in> lexLessState F0 decisionVars"
            with \<open>getM state3 = getM state0\<close>
            have "(state', state0) \<in> lexLessState F0 decisionVars"
              unfolding lexLessState_def
              by simp
            with \<open>\<forall>state'. (state', state0) \<in> lexLessState F0 decisionVars \<longrightarrow> state' \<notin> Q\<close>
            have "state' \<notin> Q"
              by simp
          }
          moreover
          {
            assume "(state', ?stateMin) \<in> boolLessState"
            from \<open>?stateMin \<in> ?Q2\<close>
              \<open>getM state1 = getM state0\<close>
            have "getConflictFlag state3 = getConflictFlag state1" "getM state3 = getM state1"
              by auto
            with \<open>(state', ?stateMin) \<in> boolLessState\<close>
            have "(state', state1) \<in> boolLessState"
              unfolding boolLessState_def
              by simp
            with \<open>\<forall>state'. (state', state1) \<in> boolLessState \<longrightarrow> state' \<notin> ?Q0\<close>
            have "state' \<notin> ?Q0"
              by simp
            from \<open>(state', state1) \<in> boolLessState\<close> \<open>getM state1 = getM state0\<close>
            have "getM state' = getM state0"
              unfolding boolLessState_def
              by auto
            with \<open>state' \<notin> ?Q0\<close>
            have "state' \<notin> Q"
              by simp
          }
          moreover
          {
            assume "(state', ?stateMin) \<in> multLessState"
            from \<open>?stateMin \<in> ?Q2\<close> 
              \<open>getM state1 = getM state0\<close> \<open>getM state2 = getM state0\<close>
              \<open>getConflictFlag state2 = getConflictFlag state1\<close>
            have "getC state3 = getC state2" "getConflictFlag state3 = getConflictFlag state2" "getM state3 = getM state2"
              by auto
            with \<open>(state', ?stateMin) \<in> multLessState\<close>
            have "(state', state2) \<in> multLessState"
              unfolding multLessState_def
              by auto
            with \<open>\<forall>state'. (state', state2) \<in> multLessState \<longrightarrow> state' \<notin> ?Q1\<close>
            have "state' \<notin> ?Q1"
              by simp
            from \<open>(state', state2) \<in> multLessState\<close> \<open>getM state2 = getM state0\<close> \<open>getConflictFlag state2 = getConflictFlag state1\<close>
            have "getM state' = getM state0" "getConflictFlag state' = getConflictFlag state1"
              unfolding multLessState_def
              by auto
            with \<open>state' \<notin> ?Q1\<close>
            have "state' \<notin> Q"
              by simp
          }
          moreover
          {
            assume "(state', ?stateMin) \<in> learnLessState"
            with \<open>\<forall>state'. (state', ?stateMin) \<in> learnLessState \<longrightarrow> state' \<notin> ?Q2\<close>
            have "state' \<notin> ?Q2"
              by simp
            from \<open>(state', ?stateMin) \<in> learnLessState\<close>
              \<open>getM state3 = getM state0\<close> \<open>getConflictFlag state3 = getConflictFlag state1\<close> \<open>getC state3 = getC state2\<close>
            have "getM state' = getM state0" "getConflictFlag state' = getConflictFlag state1" "getC state' = getC state2"
              unfolding learnLessState_def
              by auto
            with \<open>state' \<notin> ?Q2\<close>
            have "state' \<notin> Q"
              by simp
          }
          ultimately
          show "state' \<notin> Q"
            by auto
        qed
      qed
      with \<open>?stateMin \<in> Q\<close> have "(\<exists> stateMin \<in> Q. \<forall>state'. (state', stateMin) \<in> terminationLess F0 decisionVars \<longrightarrow> state' \<notin> Q)"
        by auto
    }
    thus ?thesis
      by simp
  qed
qed


text\<open>Using the termination ordering we show that the transition
 relation is well founded on states reachable from initial state.\<close>
(*----------------------------------------------------------------------------*)
theorem wfTransitionRelation:
  fixes decisionVars :: "Variable set" and F0 :: "Formula"
  assumes "finite decisionVars" and "isInitialState state0 F0"
  shows "wf {(stateB, stateA). 
             (state0, stateA) \<in> transitionRelation F0 decisionVars \<and> (transition stateA stateB F0 decisionVars)}"
(*----------------------------------------------------------------------------*)
proof-
  let ?rel = "{(stateB, stateA). 
                  (state0, stateA) \<in> transitionRelation F0 decisionVars \<and> (transition stateA stateB F0 decisionVars)}"
  let ?rel'= "terminationLess F0 decisionVars"

  have "\<forall>x y. (x, y) \<in> ?rel \<longrightarrow> (x, y) \<in> ?rel'"
  proof-
    {
      fix stateA::State and stateB::State
      assume "(stateB, stateA) \<in> ?rel"
      hence "(stateB, stateA) \<in> ?rel'"
        using \<open>isInitialState state0 F0\<close>
        using invariantsHoldInValidRunsFromInitialState[of "state0" "F0" "stateA" "decisionVars"]
        using stateIsDecreasedByValidTransitions[of "stateA" "F0" "decisionVars" "stateB"]
        by simp
    }
    thus ?thesis
      by simp
  qed
  moreover 
  have "wf ?rel'"
    using \<open>finite decisionVars\<close>
    by (rule wfTerminationLess)
  ultimately
  show ?thesis
    using wellFoundedEmbed[of "?rel" "?rel'"]
    by simp
qed


text\<open>We will now give two corollaries of the previous theorem. First
  is a weak termination result that shows that there is a terminating
  run from every intial state to the final one.\<close>
corollary 
  fixes decisionVars :: "Variable set" and F0 :: "Formula" and state0 :: "State"
  assumes "finite decisionVars" and "isInitialState state0 F0"
  shows "\<exists> state. (state0, state) \<in> transitionRelation F0 decisionVars \<and> isFinalState state F0 decisionVars"
proof-
  {
    assume "\<not> ?thesis"
    let ?Q = "{state. (state0, state) \<in> transitionRelation F0 decisionVars}"
    let ?rel = "{(stateB, stateA). (state0, stateA) \<in> transitionRelation F0 decisionVars \<and>
                         transition stateA stateB F0 decisionVars}"
    have "state0 \<in> ?Q"
      unfolding transitionRelation_def
      by simp
    hence "\<exists> state. state \<in> ?Q"
      by auto

    from assms 
    have "wf ?rel"
      using wfTransitionRelation[of "decisionVars" "state0" "F0"]
      by auto
    hence "\<forall> Q. (\<exists> x. x \<in> Q) \<longrightarrow> (\<exists> stateMin \<in> Q. \<forall> state. (state, stateMin) \<in> ?rel \<longrightarrow> state \<notin> Q)"
      unfolding wf_eq_minimal
      by simp
    hence " (\<exists> x. x \<in> ?Q) \<longrightarrow> (\<exists> stateMin \<in> ?Q. \<forall> state. (state, stateMin) \<in> ?rel \<longrightarrow> state \<notin> ?Q)"
      by rule
    with \<open>\<exists> state. state \<in> ?Q\<close>
    have "\<exists> stateMin \<in> ?Q. \<forall> state. (state, stateMin) \<in> ?rel \<longrightarrow> state \<notin> ?Q"
      by simp
    then obtain stateMin
      where "stateMin \<in> ?Q" and "\<forall> state. (state, stateMin) \<in> ?rel \<longrightarrow> state \<notin> ?Q"
      by auto
    
    from \<open>stateMin \<in> ?Q\<close> 
    have "(state0, stateMin) \<in> transitionRelation F0 decisionVars"
      by simp
    with \<open>\<not> ?thesis\<close>
    have "\<not> isFinalState stateMin F0 decisionVars"
      by simp
    then obtain state'::State
      where "transition stateMin state' F0 decisionVars"
      unfolding isFinalState_def
      by auto
    have "(state', stateMin) \<in> ?rel"
      using \<open>(state0, stateMin) \<in> transitionRelation F0 decisionVars\<close>
            \<open>transition stateMin state' F0 decisionVars\<close>
      by simp
    with \<open>\<forall> state. (state, stateMin) \<in> ?rel \<longrightarrow> state \<notin> ?Q\<close>
    have "state' \<notin> ?Q"
      by force
    moreover
    from \<open>(state0, stateMin) \<in> transitionRelation F0 decisionVars\<close> \<open>transition stateMin state' F0 decisionVars\<close>
    have "state' \<in> ?Q"
      unfolding transitionRelation_def
      using rtrancl_into_rtrancl[of "state0" "stateMin" "{(stateA, stateB). transition stateA stateB F0 decisionVars}" "state'"]
      by simp
    ultimately
    have False
      by simp
  }
  thus ?thesis
    by auto
qed

text\<open>Now we prove the final strong termination result which states
that there cannot be infinite chains of transitions. If there is an
infinite transition chain that starts from an initial state, its
elements would for a set that would contain initial state and for
every element of that set there would be another element of that set
that is directly reachable from it. We show that no such set exists.\<close>
corollary noInfiniteTransitionChains:
  fixes F0::Formula and decisionVars::"Variable set"
  assumes "finite decisionVars"
  shows "\<not> (\<exists> Q::(State set). \<exists> state0 \<in> Q. isInitialState state0 F0 \<and> 
                              (\<forall> state \<in> Q. (\<exists> state' \<in> Q. transition state state' F0 decisionVars))
            )"
proof-
  {
  assume "\<not> ?thesis"
  then obtain Q::"State set" and state0::"State"
    where "isInitialState state0 F0" "state0 \<in> Q"
          "\<forall> state \<in> Q. (\<exists> state' \<in> Q. transition state state' F0 decisionVars)"
    by auto
  let ?rel = "{(stateB, stateA). (state0, stateA) \<in> transitionRelation F0 decisionVars \<and>
                         transition stateA stateB F0 decisionVars}"
  from \<open>finite decisionVars\<close> \<open>isInitialState state0 F0\<close>
  have "wf ?rel"
    using wfTransitionRelation
    by simp
  hence wfmin: "\<forall>Q x. x \<in> Q \<longrightarrow>
         (\<exists>z\<in>Q. \<forall>y. (y, z) \<in> ?rel \<longrightarrow> y \<notin> Q)"
    unfolding wf_eq_minimal 
    by simp
  let ?Q = "{state \<in> Q. (state0, state) \<in> transitionRelation F0 decisionVars}"
  from \<open>state0 \<in> Q\<close>
  have "state0 \<in> ?Q"
    unfolding transitionRelation_def
    by simp
  with wfmin
  obtain stateMin::State
    where "stateMin \<in> ?Q" and "\<forall>y. (y, stateMin) \<in> ?rel \<longrightarrow> y \<notin> ?Q"
    apply (erule_tac x="?Q" in allE)
    by auto

  from \<open>stateMin \<in> ?Q\<close>
  have "stateMin \<in> Q" "(state0, stateMin) \<in> transitionRelation F0 decisionVars"
    by auto
  with \<open>\<forall> state \<in> Q. (\<exists> state' \<in> Q. transition state state' F0 decisionVars)\<close>
  obtain state'::State
    where "state' \<in> Q" "transition stateMin state' F0 decisionVars"
    by auto

  with \<open>(state0, stateMin) \<in> transitionRelation F0 decisionVars\<close>
  have "(state', stateMin) \<in> ?rel"
    by simp
  with \<open>\<forall>y. (y, stateMin) \<in> ?rel \<longrightarrow> y \<notin> ?Q\<close>
  have "state' \<notin> ?Q"
    by force
  
  from \<open>state' \<in> Q\<close> \<open>(state0, stateMin) \<in> transitionRelation F0 decisionVars\<close>
    \<open>transition stateMin state' F0 decisionVars\<close>
  have "state' \<in> ?Q"
    unfolding transitionRelation_def
    using rtrancl_into_rtrancl[of "state0" "stateMin" "{(stateA, stateB). transition stateA stateB F0 decisionVars}" "state'"]
    by simp
  with \<open>state' \<notin> ?Q\<close>
  have False
    by simp
  }
  thus ?thesis
    by force
qed


(*----------------------------------------------------------------------------*)
subsection\<open>Completeness\<close>
(*----------------------------------------------------------------------------*)
text\<open>In this section we will first show that each final state is
either \textit{SAT} or \textit{UNSAT} state.\<close>


lemma finalNonConflictState: 
  fixes state::State and FO :: Formula
  assumes 
  "getConflictFlag state = False" and
  "\<not> applicableDecide state decisionVars"  and
  "\<not> applicableConflict state"
  shows "\<not> formulaFalse (getF state) (elements (getM state))" and 
  "vars (elements (getM state)) \<supseteq> decisionVars"
proof-
  from \<open>\<not> applicableConflict state\<close> \<open>getConflictFlag state = False\<close>
  show "\<not> formulaFalse (getF state) (elements (getM state))"
    unfolding applicableConflictCharacterization
    by (auto simp add:formulaFalseIffContainsFalseClause formulaEntailsItsClauses)
  show "vars (elements (getM state)) \<supseteq> decisionVars"
  proof
    fix x :: Variable
    let ?l = "Pos x"
    assume "x \<in> decisionVars"
    hence "var ?l = x" and "var ?l \<in> decisionVars" and "var (opposite ?l) \<in> decisionVars"
      by auto
    with \<open>\<not> applicableDecide state decisionVars\<close> 
    have "literalTrue ?l (elements (getM state)) \<or> literalFalse ?l (elements (getM state))"
      unfolding applicableDecideCharacterization
      by force
    with \<open>var ?l = x\<close>
    show "x \<in> vars (elements (getM state))"
      using valuationContainsItsLiteralsVariable[of "?l" "elements (getM state)"]
      using valuationContainsItsLiteralsVariable[of "opposite ?l" "elements (getM state)"]
      by auto
  qed
qed

lemma finalConflictingState: 
  fixes state :: State
  assumes 
  "InvariantUniq (getM state)" and
  "InvariantReasonClauses (getF state) (getM state)" and
  "InvariantCFalse (getConflictFlag state) (getM state) (getC state)" and
  "\<not> applicableExplain state" and
  "\<not> applicableBackjump state" and
  "getConflictFlag state"
  shows
  "getC state = []"
proof (cases "\<forall> l. l el getC state \<longrightarrow> opposite l el decisions (getM state)")
  case True
  {
    assume "getC state \<noteq> []"
    let ?l = "getLastAssertedLiteral (oppositeLiteralList (getC state)) (elements (getM state))"

    from \<open>InvariantUniq (getM state)\<close>
    have "uniq (elements (getM state))"
      unfolding InvariantUniq_def
      .
   
    from \<open>getConflictFlag state\<close> \<open>InvariantCFalse (getConflictFlag state) (getM state) (getC state)\<close>
    have "clauseFalse (getC state) (elements (getM state))"
      unfolding InvariantCFalse_def
      by simp

    with \<open>getC state \<noteq> []\<close>
    \<open>InvariantUniq (getM state)\<close>
    have "isLastAssertedLiteral ?l (oppositeLiteralList (getC state)) (elements (getM state))"
      unfolding InvariantUniq_def
      using getLastAssertedLiteralCharacterization
      by simp

    with True \<open>uniq (elements (getM state))\<close>
    have "\<exists> level. (isBackjumpLevel level (opposite ?l) (getC state) (getM state))"
      using allDecisionsThenExistsBackjumpLevel [of "getM state" "getC state" "opposite ?l"]
      by simp
    then
    obtain level::nat where
      "isBackjumpLevel level (opposite ?l) (getC state) (getM state)"
      by auto
    with \<open>getConflictFlag state\<close>
    have "applicableBackjump state"
      unfolding applicableBackjumpCharacterization
      by auto
    with \<open>\<not> applicableBackjump state\<close>
    have False
      by simp
  }
  thus ?thesis
    by auto
next
  case False
  then obtain literal::Literal where "literal el getC state" "\<not> opposite literal el decisions (getM state)"
    by auto
  with \<open>InvariantReasonClauses (getF state) (getM state)\<close> \<open>InvariantCFalse (getConflictFlag state) (getM state) (getC state)\<close> \<open>getConflictFlag state\<close>
  have "\<exists> c. formulaEntailsClause (getF state) c \<and> isReason c (opposite literal) (elements (getM state))"
    using explainApplicableToEachNonDecision[of "getF state" "getM state" "getConflictFlag state" "getC state" "opposite literal"]
    by auto
  then obtain c::Clause 
    where "formulaEntailsClause (getF state) c" "isReason c (opposite literal) (elements (getM state))"
    by auto
  with \<open>\<not> applicableExplain state\<close> \<open>getConflictFlag state\<close> \<open>literal el (getC state)\<close>
  have "False"
    unfolding applicableExplainCharacterization
    by auto
  thus ?thesis
    by simp
qed
  
lemma finalStateCharacterizationLemma:
  fixes state :: State
  assumes 
  "InvariantUniq (getM state)" and
  "InvariantReasonClauses (getF state) (getM state)" and
  "InvariantCFalse (getConflictFlag state) (getM state) (getC state)" and
  "\<not> applicableDecide state decisionVars"  and
  "\<not> applicableConflict state"
  "\<not> applicableExplain state" and
  "\<not> applicableBackjump state"
  shows
  "(getConflictFlag state = False \<and> 
           \<not>formulaFalse (getF state) (elements (getM state)) \<and> 
           vars (elements (getM state)) \<supseteq> decisionVars) \<or> 
   (getConflictFlag state = True \<and> 
           getC state = [])"
proof (cases "getConflictFlag state")
  case True
  hence "getC state = []"
    using assms
    using finalConflictingState
    by auto
  with True 
  show ?thesis
    by simp
next
  case False
  hence "\<not>formulaFalse (getF state) (elements (getM state))" and "vars (elements (getM state)) \<supseteq> decisionVars"
    using assms
    using finalNonConflictState
    by auto
  with False
  show ?thesis
    by simp
qed

(*----------------------------------------------------------------------------*)
theorem finalStateCharacterization:
  fixes F0 :: Formula and decisionVars :: "Variable set" and state0 :: State and state :: State
  assumes 
  "isInitialState state0 F0" and
  "(state0, state) \<in> transitionRelation F0 decisionVars" and
  "isFinalState state F0 decisionVars"
  shows 
  "(getConflictFlag state = False \<and> 
      \<not>formulaFalse (getF state) (elements (getM state)) \<and> 
      vars (elements (getM state)) \<supseteq> decisionVars) \<or> 
   (getConflictFlag state = True \<and> 
      getC state = [])"
(*----------------------------------------------------------------------------*)
proof-
  from \<open>isInitialState state0 F0\<close> \<open>(state0, state) \<in> transitionRelation F0 decisionVars\<close>
  have "invariantsHoldInState state F0 decisionVars"
    using invariantsHoldInValidRunsFromInitialState
    by simp
  hence 
    *: "InvariantUniq (getM state)" 
    "InvariantReasonClauses (getF state) (getM state)" 
    "InvariantCFalse (getConflictFlag state) (getM state) (getC state)"
    unfolding invariantsHoldInState_def
    by auto

  from \<open>isFinalState state F0 decisionVars\<close> 
  have **: 
    "\<not> applicableDecide state decisionVars"
    "\<not> applicableConflict state"
    "\<not> applicableExplain  state" 
    "\<not> applicableLearn state" 
    "\<not> applicableBackjump state" 
    unfolding finalStateNonApplicable
    by auto

  from * **
  show ?thesis
    using finalStateCharacterizationLemma[of "state" "decisionVars"]
    by simp
qed

text\<open>Completeness theorems are easy consequences of this characterization and 
 soundness.\<close>
(*----------------------------------------------------------------------------*)
theorem completenessForSAT: 
  fixes F0 :: Formula and decisionVars :: "Variable set" and state0 :: State and state :: State
  assumes 
  "satisfiable F0" and 

  "isInitialState state0 F0" and
  "(state0, state) \<in> transitionRelation F0 decisionVars" and
  "isFinalState state F0 decisionVars"

  shows "getConflictFlag state = False \<and> \<not>formulaFalse (getF state) (elements (getM state)) \<and> 
               vars (elements (getM state)) \<supseteq> decisionVars"
(*----------------------------------------------------------------------------*)
proof-
  from assms
  have *: "(getConflictFlag state = False \<and> 
               \<not>formulaFalse (getF state) (elements (getM state)) \<and> 
               vars (elements (getM state)) \<supseteq> decisionVars) \<or> 
           (getConflictFlag state = True \<and> 
               getC state = [])"
    using finalStateCharacterization[of "state0" "F0" "state" "decisionVars"]
    by auto
  {
    assume "\<not> (getConflictFlag state = False)"
    with * 
    have "getConflictFlag state = True" "getC state = []"
      by auto
    with assms
      have "\<not> satisfiable F0"
      using soundnessForUNSAT
      by simp
    with \<open>satisfiable F0\<close>
    have False
      by simp
  }
  with * show ?thesis
    by auto
qed

(************************************************************************)
theorem completenessForUNSAT: 
  fixes F0 :: Formula and decisionVars :: "Variable set" and state0 :: State and state :: State
  assumes 
  "vars F0 \<subseteq> decisionVars" and

  "\<not> satisfiable F0" and

  "isInitialState state0 F0" and
  "(state0, state) \<in> transitionRelation F0 decisionVars" and
  "isFinalState state F0 decisionVars"

  shows 
  "getConflictFlag state = True \<and> getC state = []"
(************************************************************************)
proof-
  from assms
  have *: "(getConflictFlag state = False \<and> 
               \<not>formulaFalse (getF state) (elements (getM state)) \<and> 
               vars (elements (getM state)) \<supseteq> decisionVars) \<or> 
           (getConflictFlag state = True \<and> 
               getC state = [])"
    using finalStateCharacterization[of "state0" "F0" "state" "decisionVars"]
    by auto
  {
    assume "\<not> getConflictFlag state = True"
    with *
    have "getConflictFlag state = False \<and> \<not>formulaFalse (getF state) (elements (getM state)) \<and> vars (elements (getM state)) \<supseteq> decisionVars"
      by simp
    with assms
    have "satisfiable F0"
      using soundnessForSAT[of "F0" "decisionVars" "state0" "state"]
      unfolding satisfiable_def
      by auto
    with \<open>\<not> satisfiable F0\<close>
    have False
      by simp
  }
  with * show ?thesis
    by auto
qed

(************************************************************************)
theorem partialCorrectness: 
  fixes F0 :: Formula and decisionVars :: "Variable set" and state0 :: State and state :: State
  assumes 
  "vars F0 \<subseteq> decisionVars" and  

  "isInitialState state0 F0" and
  "(state0, state) \<in> transitionRelation F0 decisionVars" and
  "isFinalState state F0 decisionVars"

  shows 
  "satisfiable F0 = (\<not> getConflictFlag state)"
(************************************************************************)
using assms
using completenessForUNSAT[of "F0" "decisionVars" "state0" "state"]
using completenessForSAT[of "F0" "state0" "state" "decisionVars"]
by auto

end
