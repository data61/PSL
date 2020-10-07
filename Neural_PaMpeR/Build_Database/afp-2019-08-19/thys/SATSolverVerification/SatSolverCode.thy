(*    Title:              SatSolverVerification/SatSolverCode.thy
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

section\<open>Functional implementation of a SAT solver with Two Watch literal propagation.\<close>
theory SatSolverCode
imports SatSolverVerification "HOL-Library.Code_Target_Numeral"
begin

(******************************************************************************)
subsection\<open>Specification\<close>
(******************************************************************************)

lemma [code_unfold]:
  fixes literal :: Literal and clause :: Clause
  shows "literal el clause = List.member clause literal"
  by (auto simp add: member_def)

datatype ExtendedBool = TRUE | FALSE | UNDEF

record State = 
  \<comment> \<open>Satisfiability flag: UNDEF, TRUE or FALSE\<close>
"getSATFlag" :: ExtendedBool
  \<comment> \<open>Formula\<close> 
"getF"       :: Formula      
  \<comment> \<open>Assertion Trail\<close>
"getM"       :: LiteralTrail 
  \<comment> \<open>Conflict flag\<close>
"getConflictFlag"   :: bool   \<comment> \<open>raised iff M falsifies F\<close>
  \<comment> \<open>Conflict clause index\<close> 
"getConflictClause" :: nat    \<comment> \<open>corresponding clause from F is false in M\<close>
  \<comment> \<open>Unit propagation queue\<close>
"getQ" :: "Literal list"      
  \<comment> \<open>Unit propagation graph\<close>
"getReason" :: "Literal \<Rightarrow> nat option" \<comment> \<open>index of a clause that is a reason for propagation of a literal\<close>
  \<comment> \<open>Two-watch literal scheme\<close>
  \<comment> \<open>clause indices instead of clauses are used\<close>
"getWatch1" :: "nat \<Rightarrow> Literal option"  \<comment> \<open>First watch of a clause\<close>
"getWatch2" :: "nat \<Rightarrow> Literal option"  \<comment> \<open>Second watch of a clause\<close>
"getWatchList" :: "Literal \<Rightarrow> nat list" \<comment> \<open>Watch list of a given literal\<close>
  \<comment> \<open>Conflict analysis data structures\<close>
"getC"   :: Clause             \<comment> \<open>Conflict analysis clause - always false in M\<close>
"getCl"  :: Literal            \<comment> \<open>Last asserted literal in (opposite getC)\<close>
"getCll" :: Literal            \<comment> \<open>Second last asserted literal in (opposite getC)\<close>
"getCn"  :: nat                \<comment> \<open>Number of literals of (opposite getC) on the (currentLevel M)\<close>

definition
setWatch1 :: "nat \<Rightarrow> Literal \<Rightarrow> State \<Rightarrow> State"
where
"setWatch1 clause literal state =
    state\<lparr> getWatch1 := (getWatch1 state)(clause := Some literal), 
           getWatchList := (getWatchList state)(literal := clause # (getWatchList state literal)) 
         \<rparr>
"
declare setWatch1_def[code_unfold]

definition
setWatch2 :: "nat \<Rightarrow> Literal \<Rightarrow> State \<Rightarrow> State"
where
"setWatch2 clause literal state =
    state\<lparr> getWatch2 := (getWatch2 state)(clause := Some literal),
           getWatchList := (getWatchList state)(literal := clause # (getWatchList state literal)) 
         \<rparr>
"
declare setWatch2_def[code_unfold]


definition
swapWatches :: "nat \<Rightarrow> State \<Rightarrow> State"
where
"swapWatches clause state ==
    state\<lparr> getWatch1 := (getWatch1 state)(clause := (getWatch2 state clause)),
           getWatch2 := (getWatch2 state)(clause := (getWatch1 state clause))
         \<rparr>
"
declare swapWatches_def[code_unfold]

primrec getNonWatchedUnfalsifiedLiteral :: "Clause \<Rightarrow> Literal \<Rightarrow> Literal \<Rightarrow> LiteralTrail \<Rightarrow> Literal option"
where
"getNonWatchedUnfalsifiedLiteral [] w1 w2 M = None" |
"getNonWatchedUnfalsifiedLiteral (literal # clause) w1 w2 M = 
    (if literal \<noteq> w1 \<and> 
        literal \<noteq> w2 \<and> 
        \<not> (literalFalse literal (elements M)) then
            Some literal
     else
            getNonWatchedUnfalsifiedLiteral clause w1 w2 M
    )
"

definition
setReason :: "Literal \<Rightarrow> nat \<Rightarrow> State \<Rightarrow> State"
where
"setReason literal clause state = 
    state\<lparr> getReason := (getReason state)(literal := Some clause) \<rparr>
"
declare setReason_def[code_unfold]

primrec notifyWatches_loop::"Literal \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> State \<Rightarrow> State"
where
"notifyWatches_loop literal [] newWl state = state\<lparr> getWatchList := (getWatchList state)(literal := newWl) \<rparr>" |
"notifyWatches_loop literal (clause # list') newWl state = 
    (let state' = (if Some literal = (getWatch1 state clause) then 
                       (swapWatches clause state) 
                   else 
                       state) in
    case (getWatch1 state' clause) of 
        None \<Rightarrow> state
    |   Some w1 \<Rightarrow> (
    case (getWatch2 state' clause) of 
        None \<Rightarrow> state
    |   Some w2 \<Rightarrow> 
    (if (literalTrue w1 (elements (getM state'))) then
        notifyWatches_loop literal list' (clause # newWl) state'
     else
        (case (getNonWatchedUnfalsifiedLiteral (nth (getF state') clause) w1 w2 (getM state')) of 
            Some l' \<Rightarrow> 
                notifyWatches_loop literal list' newWl (setWatch2 clause l' state')
          | None \<Rightarrow> 
                (if (literalFalse w1 (elements (getM state'))) then
                    let state'' = (state'\<lparr> getConflictFlag := True, getConflictClause := clause \<rparr>) in
                    notifyWatches_loop literal list' (clause # newWl) state''
                else
                    let state'' = state'\<lparr> getQ := (if w1 el (getQ state') then 
                                                      (getQ state') 
                                                  else 
                                                      (getQ state') @ [w1] 
                                                  )
                                        \<rparr> in
                   let state''' = (setReason w1 clause state'') in
                   notifyWatches_loop literal list' (clause # newWl) state'''
                )
        )
    )
    )
    )
"

definition
notifyWatches :: "Literal \<Rightarrow> State \<Rightarrow> State"
where
"notifyWatches literal state ==
    notifyWatches_loop literal (getWatchList state literal) [] state
"
declare notifyWatches_def[code_unfold]


definition
assertLiteral :: "Literal \<Rightarrow> bool \<Rightarrow> State \<Rightarrow> State"
where
"assertLiteral literal decision state ==
    let state' = (state\<lparr> getM := (getM state) @ [(literal, decision)] \<rparr>) in
    notifyWatches (opposite literal) state'
"


definition
applyUnitPropagate :: "State \<Rightarrow> State"
where
"applyUnitPropagate state =
    (let state' = (assertLiteral (hd (getQ state)) False state) in
    state'\<lparr> getQ := tl (getQ state')\<rparr>)
"

partial_function (tailrec)
exhaustiveUnitPropagate :: "State \<Rightarrow> State"
where
exhaustiveUnitPropagate_unfold[code]:
"exhaustiveUnitPropagate state =
    (if (getConflictFlag state) \<or> (getQ state) = [] then 
        state 
    else 
        exhaustiveUnitPropagate (applyUnitPropagate state)
    )
"

inductive
exhaustiveUnitPropagate_dom :: "State \<Rightarrow> bool"
where
step: "(\<not> getConflictFlag state \<Longrightarrow> getQ state \<noteq> []
   \<Longrightarrow> exhaustiveUnitPropagate_dom (applyUnitPropagate state))
   \<Longrightarrow> exhaustiveUnitPropagate_dom state"


definition
addClause :: "Clause \<Rightarrow> State \<Rightarrow> State"
where
"addClause clause state =
    (let clause' = (remdups (removeFalseLiterals clause (elements (getM state)))) in 
    (if (clauseTrue clause' (elements (getM state))) then 
        state
    else (if clause'=[] then 
        state\<lparr> getSATFlag := FALSE \<rparr>
    else (if (length clause' = 1) then 
        let state' = (assertLiteral (hd clause') False state) in
        exhaustiveUnitPropagate state'
    else (if (clauseTautology clause') then 
        state
    else
        let clauseIndex = length (getF state) in
        let state'   = state\<lparr> getF := (getF state) @ [clause']\<rparr> in
        let state''  = setWatch1 clauseIndex (nth clause' 0) state' in
        let state''' = setWatch2 clauseIndex (nth clause' 1) state'' in
        state'''
   )))
 ))"


definition
initialState :: "State"
where
"initialState =
    \<lparr> getSATFlag = UNDEF,
      getF = [], 
      getM = [], 
      getConflictFlag = False,
      getConflictClause = 0, 
      getQ = [],
      getReason = \<lambda> l. None,
      getWatch1 = \<lambda> c. None, 
      getWatch2 = \<lambda> c. None,
      getWatchList = \<lambda> l. [],
      getC = [],
      getCl = (Pos 0), 
      getCll = (Pos 0), 
      getCn = 0
    \<rparr>
"

primrec initialize :: "Formula \<Rightarrow> State \<Rightarrow> State"
where
"initialize [] state = state" |
"initialize (clause # formula) state = initialize formula (addClause clause state)"

definition 
findLastAssertedLiteral :: "State \<Rightarrow> State"
where
"findLastAssertedLiteral state = 
   state \<lparr> getCl := getLastAssertedLiteral (oppositeLiteralList (getC state)) (elements (getM state)) \<rparr>"

definition
countCurrentLevelLiterals :: "State \<Rightarrow> State"
where
"countCurrentLevelLiterals state = 
   (let cl = currentLevel (getM state) in 
        state \<lparr> getCn := length (filter (\<lambda> l. elementLevel (opposite l) (getM state) = cl) (getC state)) \<rparr>)"

definition setConflictAnalysisClause :: "Clause \<Rightarrow> State \<Rightarrow> State" 
where 
"setConflictAnalysisClause clause state = 
  (let oppM0 = oppositeLiteralList (elements (prefixToLevel 0 (getM state))) in 
   let state' = state (| getC := remdups (list_diff clause oppM0) |) in 
     countCurrentLevelLiterals (findLastAssertedLiteral state')
  )"
 
definition
applyConflict :: "State \<Rightarrow> State"
where
"applyConflict state = 
   (let conflictClause = (nth (getF state) (getConflictClause state)) in
    setConflictAnalysisClause conflictClause state)"

definition
applyExplain :: "Literal \<Rightarrow> State \<Rightarrow> State"
where
"applyExplain literal state =
    (case (getReason state literal) of
        None \<Rightarrow> 
            state
    |   Some reason \<Rightarrow> 
            let res = resolve (getC state) (nth (getF state) reason) (opposite literal) in 
            setConflictAnalysisClause res state
        
    )
"

partial_function (tailrec)
applyExplainUIP :: "State \<Rightarrow> State"
where
applyExplainUIP_unfold:
"applyExplainUIP state = 
    (if (getCn state = 1) then 
         state
     else
         applyExplainUIP (applyExplain (getCl state) state)
    )
"

inductive
applyExplainUIP_dom :: "State \<Rightarrow> bool"
where
step:
"(getCn state \<noteq> 1
    \<Longrightarrow> applyExplainUIP_dom (applyExplain (getCl state) state))
  \<Longrightarrow> applyExplainUIP_dom state
"

definition
applyLearn :: "State \<Rightarrow> State"
where
"applyLearn state =
        (if getC state = [opposite (getCl state)] then
            state
         else
            let state' = state\<lparr> getF := (getF state) @ [getC state] \<rparr> in
            let l  = (getCl state) in
            let ll = (getLastAssertedLiteral (removeAll l (oppositeLiteralList (getC state))) (elements (getM state))) in
            let clauseIndex = length (getF state) in
            let state''  = setWatch1 clauseIndex (opposite l) state' in
            let state''' = setWatch2 clauseIndex (opposite ll) state'' in
            state'''\<lparr> getCll := ll \<rparr>
        )
"

definition
getBackjumpLevel :: "State \<Rightarrow> nat"
where
"getBackjumpLevel state ==
    (if getC state = [opposite (getCl state)] then 
        0 
     else
        elementLevel (getCll state) (getM state)
     )
"

definition
applyBackjump :: "State \<Rightarrow> State"
where
"applyBackjump state =
    (let l = (getCl state) in
     let level = getBackjumpLevel state in
     let state' = state\<lparr> getConflictFlag := False, getQ := [], getM := (prefixToLevel level (getM state))\<rparr> in
     let state'' = (if level > 0 then setReason (opposite l) (length (getF state) - 1) state' else state') in
     assertLiteral (opposite l) False state''
    )
"

axiomatization selectLiteral :: "State \<Rightarrow> Variable set \<Rightarrow> Literal"
where
selectLiteral_def:
"Vbl - vars (elements (getM state)) \<noteq> {} \<longrightarrow> 
    var (selectLiteral state Vbl) \<in> (Vbl - vars (elements (getM state)))"

definition
applyDecide :: "State \<Rightarrow> Variable set \<Rightarrow> State"
where
"applyDecide state Vbl =
    assertLiteral (selectLiteral state Vbl) True state
"

definition
solve_loop_body :: "State \<Rightarrow> Variable set \<Rightarrow> State"
where
"solve_loop_body state Vbl = 
    (let state' = exhaustiveUnitPropagate state in
    (if (getConflictFlag state') then
        (if (currentLevel (getM state')) = 0 then
            state'\<lparr> getSATFlag := FALSE \<rparr>
         else
            (applyBackjump
            (applyLearn
            (applyExplainUIP 
            (applyConflict
                state'
            )
            )
            )
            )
         )
     else
        (if (vars (elements (getM state')) \<supseteq> Vbl) then
            state'\<lparr> getSATFlag := TRUE \<rparr>
         else
            applyDecide state' Vbl
        )
    )
    )
"


partial_function (tailrec) 
solve_loop :: "State \<Rightarrow> Variable set \<Rightarrow> State"
where
solve_loop_unfold: 
"solve_loop state Vbl = 
    (if (getSATFlag state) \<noteq> UNDEF then
        state
     else 
        let state' = solve_loop_body state Vbl in
        solve_loop state' Vbl
    )
"

inductive
solve_loop_dom :: "State \<Rightarrow> Variable set \<Rightarrow> bool"
where
step:
"(getSATFlag state = UNDEF
    \<Longrightarrow> solve_loop_dom (solve_loop_body state Vbl) Vbl)
  \<Longrightarrow> solve_loop_dom state Vbl"

definition solve::"Formula \<Rightarrow> ExtendedBool"
where
"solve F0 = 
    (getSATFlag 
        (solve_loop 
            (initialize F0 initialState) (vars F0)
        )
    )
"

(* 
code_modulename SML
  Nat Numbers
  Int Numbers
  Ring_and_Field Numbers

code_modulename OCaml
  Nat Numbers
  Int Numbers
  Ring_and_Field Numbers

export_code solve in OCaml file "code/solve.ML"
                  in SML file "code/solve.ocaml
                  in Haskell file "code/"
*)

(******************************************************************************)
(*      I N V A R I A N T S                                                   *)
(******************************************************************************)

definition
InvariantWatchListsContainOnlyClausesFromF :: "(Literal \<Rightarrow> nat list) \<Rightarrow> Formula \<Rightarrow> bool"
where
"InvariantWatchListsContainOnlyClausesFromF Wl F = 
    (\<forall> (l::Literal) (c::nat). c \<in>  set (Wl l) \<longrightarrow> 0 \<le> c \<and> c < length F)
"

definition
InvariantWatchListsUniq :: "(Literal \<Rightarrow> nat list) \<Rightarrow> bool"
where
"InvariantWatchListsUniq Wl =
    (\<forall> l. uniq (Wl l))
"

definition
InvariantWatchListsCharacterization :: "(Literal \<Rightarrow> nat list) \<Rightarrow> (nat \<Rightarrow> Literal option) \<Rightarrow> (nat \<Rightarrow> Literal option) \<Rightarrow> bool"
where
"InvariantWatchListsCharacterization Wl w1 w2 = 
    (\<forall> (c::nat) (l::Literal). c \<in> set (Wl l) = (Some l = (w1 c) \<or> Some l = (w2 c)))
"

definition
InvariantWatchesEl :: "Formula \<Rightarrow> (nat \<Rightarrow> Literal option) \<Rightarrow> (nat \<Rightarrow> Literal option) \<Rightarrow> bool"
where
"InvariantWatchesEl formula watch1 watch2 == 
    \<forall> (clause::nat). 0 \<le> clause \<and> clause < length formula \<longrightarrow> 
        (\<exists> (w1::Literal) (w2::Literal). watch1 clause = Some w1 \<and> watch2 clause = Some w2 \<and> 
             w1 el (nth formula clause) \<and> w2 el (nth formula clause))
"

definition
InvariantWatchesDiffer :: "Formula \<Rightarrow> (nat \<Rightarrow> Literal option) \<Rightarrow> (nat \<Rightarrow> Literal option) \<Rightarrow> bool"
where
"InvariantWatchesDiffer formula watch1 watch2 == 
    \<forall> (clause::nat). 0 \<le> clause \<and> clause < length formula \<longrightarrow> watch1 clause \<noteq> watch2 clause
"

definition
watchCharacterizationCondition::"Literal \<Rightarrow> Literal \<Rightarrow> LiteralTrail \<Rightarrow> Clause \<Rightarrow> bool"
where
"watchCharacterizationCondition w1 w2 M clause = 
    (literalFalse w1 (elements M) \<longrightarrow> 
        ( (\<exists> l. l el clause \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite w1) M) \<or>
          (\<forall> l. l el clause \<and> l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow> 
                literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite w1) M)
          )
    )
"

definition
InvariantWatchCharacterization::"Formula \<Rightarrow> (nat \<Rightarrow> Literal option) \<Rightarrow> (nat \<Rightarrow> Literal option) \<Rightarrow> LiteralTrail \<Rightarrow> bool"
where
"InvariantWatchCharacterization F watch1 watch2 M =
    (\<forall> c w1 w2. (0 \<le> c \<and> c < length F \<and> Some w1 = watch1 c \<and> Some w2 = watch2 c) \<longrightarrow> 
          watchCharacterizationCondition w1 w2 M (nth F c) \<and> 
          watchCharacterizationCondition w2 w1 M (nth F c)
    )
"

definition
InvariantQCharacterization :: "bool \<Rightarrow> Literal list \<Rightarrow> Formula \<Rightarrow> LiteralTrail \<Rightarrow> bool"
where
"InvariantQCharacterization conflictFlag Q F M ==
   \<not> conflictFlag \<longrightarrow> (\<forall> (l::Literal). l el Q = (\<exists> (c::Clause). c el F \<and> isUnitClause c l (elements M)))
"

definition
InvariantUniqQ :: "Literal list \<Rightarrow> bool"
where
"InvariantUniqQ Q = 
    uniq Q
"

definition
InvariantConflictFlagCharacterization :: "bool \<Rightarrow> Formula \<Rightarrow> LiteralTrail \<Rightarrow> bool"
where
"InvariantConflictFlagCharacterization conflictFlag F M ==
    conflictFlag = formulaFalse F (elements M)
"

definition
InvariantNoDecisionsWhenConflict :: "Formula \<Rightarrow> LiteralTrail \<Rightarrow> nat \<Rightarrow> bool"
where
"InvariantNoDecisionsWhenConflict F M level= 
    (\<forall> level'. level' < level \<longrightarrow> 
              \<not> formulaFalse F (elements (prefixToLevel level' M))
    )
"

definition
InvariantNoDecisionsWhenUnit :: "Formula \<Rightarrow> LiteralTrail \<Rightarrow> nat \<Rightarrow> bool"
where
"InvariantNoDecisionsWhenUnit F M level = 
    (\<forall> level'. level' < level \<longrightarrow> 
              \<not> (\<exists> clause literal. clause el F \<and>
                                   isUnitClause clause literal (elements (prefixToLevel level' M)))
    )
"

definition InvariantEquivalentZL :: "Formula \<Rightarrow> LiteralTrail \<Rightarrow> Formula \<Rightarrow> bool"
where
"InvariantEquivalentZL F M F0 = 
    equivalentFormulae (F @ val2form (elements (prefixToLevel 0 M))) F0
"

definition
InvariantGetReasonIsReason :: "(Literal \<Rightarrow> nat option) \<Rightarrow> Formula \<Rightarrow> LiteralTrail \<Rightarrow> Literal set \<Rightarrow> bool"
where
"InvariantGetReasonIsReason GetReason F M Q == 
     \<forall> literal. (literal el (elements M) \<and> \<not> literal el (decisions M) \<and> elementLevel literal M > 0 \<longrightarrow> 
                   (\<exists> (reason::nat). (GetReason literal) = Some reason \<and> 0 \<le> reason \<and> reason < length F \<and> 
                         isReason (nth F reason) literal (elements M)
                   )
                 ) \<and> 
                (currentLevel M > 0 \<and> literal \<in> Q \<longrightarrow> 
                   (\<exists> (reason::nat). (GetReason literal) = Some reason \<and> 0 \<le> reason \<and> reason < length F \<and> 
                         (isUnitClause (nth F reason) literal (elements M) \<or> clauseFalse (nth F reason) (elements M))
                   )
                 )
"

definition
InvariantConflictClauseCharacterization :: "bool \<Rightarrow> nat \<Rightarrow> Formula \<Rightarrow> LiteralTrail \<Rightarrow> bool"
where
"InvariantConflictClauseCharacterization conflictFlag conflictClause F M  ==
         conflictFlag \<longrightarrow> (conflictClause < length F \<and> 
                           clauseFalse (nth F conflictClause) (elements M))"

definition
InvariantClCharacterization :: "Literal \<Rightarrow> Clause \<Rightarrow> LiteralTrail \<Rightarrow> bool" 
where
"InvariantClCharacterization Cl C M == 
  isLastAssertedLiteral Cl (oppositeLiteralList C) (elements M)"

definition
InvariantCllCharacterization :: "Literal \<Rightarrow> Literal \<Rightarrow> Clause \<Rightarrow> LiteralTrail \<Rightarrow> bool" 
where
"InvariantCllCharacterization Cl Cll C M == 
  set C \<noteq> {opposite Cl} \<longrightarrow> 
      isLastAssertedLiteral Cll (removeAll Cl (oppositeLiteralList C)) (elements M)"

definition
InvariantClCurrentLevel :: "Literal \<Rightarrow> LiteralTrail \<Rightarrow> bool"
where
"InvariantClCurrentLevel Cl M == 
  elementLevel Cl M = currentLevel M"

definition
InvariantCnCharacterization :: "nat \<Rightarrow> Clause \<Rightarrow> LiteralTrail \<Rightarrow> bool"
where
"InvariantCnCharacterization Cn C M == 
  Cn = length (filter (\<lambda> l. elementLevel (opposite l) M = currentLevel M) (remdups C))
"

definition
InvariantUniqC :: "Clause \<Rightarrow> bool"
where
"InvariantUniqC clause = uniq clause"

definition
InvariantVarsQ :: "Literal list \<Rightarrow> Formula \<Rightarrow> Variable set \<Rightarrow> bool"
where
"InvariantVarsQ Q F0 Vbl ==
  vars Q \<subseteq> vars F0 \<union> Vbl"

(******************************************************************************)

end
