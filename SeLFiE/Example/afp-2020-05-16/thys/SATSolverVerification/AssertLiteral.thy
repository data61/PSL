(*    Title:              SatSolverVerification/AssertLiteral.thy
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

theory AssertLiteral
imports SatSolverCode
begin

(*****************************************************************************)
(*   G E T   N O N   W A T C H E D  U N F A L S I F I E D   L I T E R A L    *)
(*****************************************************************************)

lemma getNonWatchedUnfalsifiedLiteralSomeCharacterization:
fixes clause :: Clause and w1 :: Literal and w2 :: Literal and M :: LiteralTrail and l :: Literal
assumes 
  "getNonWatchedUnfalsifiedLiteral clause w1 w2 M = Some l"
shows 
  "l el clause" "l \<noteq> w1" "l \<noteq> w2" "\<not> literalFalse l (elements M)"
using assms
by (induct clause) (auto split: if_split_asm)

lemma getNonWatchedUnfalsifiedLiteralNoneCharacterization:
fixes clause :: Clause and w1 :: Literal and w2 :: Literal and M :: LiteralTrail
assumes 
  "getNonWatchedUnfalsifiedLiteral clause w1 w2 M = None"
shows 
  "\<forall> l. l el clause \<and> l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow> literalFalse l (elements M)"
using assms
by (induct clause) (auto split: if_split_asm)

(*****************************************************************************)
(*   S W A P   W A T C H E S                                                 *)
(*****************************************************************************)

lemma swapWatchesEffect:
fixes clause::nat and state::State and clause'::nat
shows
  "getWatch1 (swapWatches clause state) clause' = (if clause = clause' then getWatch2 state clause' else getWatch1 state clause')" and
  "getWatch2 (swapWatches clause state) clause' = (if clause = clause' then getWatch1 state clause' else getWatch2 state clause')"
unfolding swapWatches_def
by auto

(*****************************************************************************)
(*    N O T I F Y    W A T C H E S                                           *)
(*****************************************************************************)

lemma notifyWatchesLoopPreservedVariables:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)"
shows
  "let state' = (notifyWatches_loop literal Wl newWl state) in
   (getM state') = (getM state) \<and> 
   (getF state') = (getF state) \<and> 
   (getSATFlag state') = (getSATFlag state) \<and> 
   isPrefix (getQ state) (getQ state')
  " 
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    unfolding isPrefix_def
    by simp
next
  case (Cons clause Wl')
  from \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)\<close>
  have "0 \<le> clause \<and> clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getM ?state' = getM state \<and> 
        getF ?state' = getF state \<and> 
        getSATFlag ?state' = getSATFlag state \<and> 
        getQ ?state' = getQ state
        "
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(3)
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>Some literal = getWatch1 state clause\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getSATFlag ?state'' = getSATFlag state \<and> 
          getQ ?state'' = getQ state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(3)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getSATFlag ?state'' = getSATFlag state \<and> 
            getQ ?state'' = getQ state"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state \<and> 
            getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            unfolding isPrefix_def
            by (auto simp add: Let_def split: if_split_asm)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons
        using \<open>\<not> Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state')) clause"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state')) clause\<close>
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getSATFlag ?state'' = getSATFlag state \<and> 
          getQ ?state'' = getQ state"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''"]
          using Cons(3)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>\<not> Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state \<and> 
            getQ ?state'' = getQ state"
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state \<and>
            getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])"
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            unfolding isPrefix_def
            by (auto simp add: Let_def split: if_split_asm)
        qed
      qed
    qed
  qed
qed


lemma notifyWatchesStartQIreleveant:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF stateA) (getWatch1 stateA) (getWatch2 stateA)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF stateA)" and
  "getM stateA = getM stateB" and
  "getF stateA = getF stateB" and
  "getWatch1 stateA = getWatch1 stateB" and
  "getWatch2 stateA = getWatch2 stateB" and
  "getConflictFlag stateA = getConflictFlag stateB" and
  "getSATFlag stateA = getSATFlag stateB"
shows
  "let state' = (notifyWatches_loop literal Wl newWl stateA) in
   let state'' = (notifyWatches_loop literal Wl newWl stateB) in
     (getM state') = (getM state'') \<and> 
     (getF state') = (getF state'') \<and> 
     (getSATFlag state') = (getSATFlag state'') \<and> 
     (getConflictFlag state') = (getConflictFlag state'')
  " 
using assms
proof (induct Wl arbitrary: newWl stateA stateB)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  from \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF stateA)\<close>
  have "0 \<le> clause \<and> clause < length (getF stateA)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 stateA clause = Some wa" and "getWatch2 stateA clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 stateA clause")
    case True
    hence "Some literal = getWatch1 stateB clause"
      using \<open>getWatch1 stateA = getWatch1 stateB\<close>
      by simp

    let ?state'A = "swapWatches clause stateA"
    let ?state'B = "swapWatches clause stateB"

    have 
      "getM ?state'A = getM ?state'B"
      "getF ?state'A = getF ?state'B"
      "getWatch1 ?state'A = getWatch1 ?state'B"
      "getWatch2 ?state'A = getWatch2 ?state'B"
      "getConflictFlag ?state'A = getConflictFlag ?state'B"
      "getSATFlag ?state'A = getSATFlag ?state'B"
      using Cons
      unfolding swapWatches_def
      by auto

    let ?w1 = wb
    have "getWatch1 ?state'A clause = Some ?w1"
      using \<open>getWatch2 stateA clause = Some wb\<close>
      unfolding swapWatches_def
      by auto
    hence "getWatch1 ?state'B clause = Some ?w1"
      using \<open>getWatch1 ?state'A = getWatch1 ?state'B\<close>
      by simp
    let ?w2 = wa
    have "getWatch2 ?state'A clause = Some ?w2"
      using \<open>getWatch1 stateA clause = Some wa\<close>
      unfolding swapWatches_def
      by auto    
    hence "getWatch2 ?state'B clause = Some ?w2"
      using \<open>getWatch2 ?state'A = getWatch2 ?state'B\<close>
      by simp

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'A))")
      case True
      hence "literalTrue ?w1 (elements (getM ?state'B))"
        using \<open>getM ?state'A = getM ?state'B\<close>
        by simp
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state'A) (getWatch1 ?state'A) (getWatch2 ?state'A)"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getM ?state'A = getM stateA \<and> 
        getF ?state'A = getF stateA \<and> 
        getSATFlag ?state'A = getSATFlag stateA \<and> 
        getQ ?state'A = getQ stateA
        "
        unfolding swapWatches_def
        by simp
      moreover
      have "getM ?state'B = getM stateB \<and> 
        getF ?state'B = getF stateB \<and> 
        getSATFlag ?state'B = getSATFlag stateB \<and> 
        getQ ?state'B = getQ stateB
        "
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'A" "?state'B" "clause # newWl"]
        using \<open>getM ?state'A = getM ?state'B\<close>
        using \<open>getF ?state'A = getF ?state'B\<close>
        using \<open>getWatch1 ?state'A = getWatch1 ?state'B\<close>
        using \<open>getWatch2 ?state'A = getWatch2 ?state'B\<close>
        using \<open>getConflictFlag ?state'A = getConflictFlag ?state'B\<close>
        using \<open>getSATFlag ?state'A = getSATFlag ?state'B\<close>
        using Cons(3)
        using \<open>getWatch1 ?state'A clause = Some ?w1\<close>
        using \<open>getWatch2 ?state'A clause = Some ?w2\<close>
        using \<open>getWatch1 ?state'B clause = Some ?w1\<close>
        using \<open>getWatch2 ?state'B clause = Some ?w2\<close>
        using \<open>Some literal = getWatch1 stateA clause\<close>
        using \<open>Some literal = getWatch1 stateB clause\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'A))\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'B))\<close>
        by (simp add:Let_def)
    next
      case False
      hence "\<not> literalTrue ?w1 (elements (getM ?state'B))"
        using \<open>getM ?state'A = getM ?state'B\<close>
        by simp
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A)")
        case (Some l')
        hence "getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = Some l'"
          using \<open>getF ?state'A = getF ?state'B\<close>
          using \<open>getM ?state'A = getM ?state'B\<close>
          by simp

        have "l' el (nth (getF ?state'A) clause)"
          using Some
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp
        hence "l' el (nth (getF ?state'B) clause)"
          using \<open>getF ?state'A = getF ?state'B\<close>
          by simp


        let ?state''A = "setWatch2 clause l' ?state'A"
        let ?state''B = "setWatch2 clause l' ?state'B"

        have 
          "getM ?state''A = getM ?state''B"
          "getF ?state''A = getF ?state''B"
          "getWatch1 ?state''A = getWatch1 ?state''B"
          "getWatch2 ?state''A = getWatch2 ?state''B"
          "getConflictFlag ?state''A = getConflictFlag ?state''B"
          "getSATFlag ?state''A = getSATFlag ?state''B"
          using Cons
          unfolding setWatch2_def
          unfolding swapWatches_def
          by auto


        from Cons(2)
        have "InvariantWatchesEl (getF ?state''A) (getWatch1 ?state''A) (getWatch2 ?state''A)"
          using \<open>l' el (nth (getF ?state'A) clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state''A = getM stateA \<and>
          getF ?state''A = getF stateA \<and> 
          getSATFlag ?state''A = getSATFlag stateA \<and> 
          getQ ?state''A = getQ stateA"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state''B = getM stateB \<and> 
          getF ?state''B = getF stateB \<and> 
          getSATFlag ?state''B = getSATFlag stateB \<and> 
          getQ ?state''B = getQ stateB
          "
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''A" "?state''B" "newWl"]
          using \<open>getM ?state''A = getM ?state''B\<close>
          using \<open>getF ?state''A = getF ?state''B\<close>
          using \<open>getWatch1 ?state''A = getWatch1 ?state''B\<close>
          using \<open>getWatch2 ?state''A = getWatch2 ?state''B\<close>
          using \<open>getConflictFlag ?state''A = getConflictFlag ?state''B\<close>
          using \<open>getSATFlag ?state''A = getSATFlag ?state''B\<close>
          using Cons(3)
          using \<open>getWatch1 ?state'A clause = Some ?w1\<close>
          using \<open>getWatch2 ?state'A clause = Some ?w2\<close>
          using \<open>getWatch1 ?state'B clause = Some ?w1\<close>
          using \<open>getWatch2 ?state'B clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 stateA clause\<close>
          using \<open>Some literal = getWatch1 stateB clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'A))\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'B))\<close>
          using \<open>getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A) = Some l'\<close>
          using \<open>getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = Some l'\<close>
          by (simp add:Let_def)
      next
        case None
        hence "getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = None"
          using \<open>getF ?state'A = getF ?state'B\<close> \<open>getM ?state'A = getM ?state'B\<close>
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'A))")
          case True
          hence "literalFalse ?w1 (elements (getM ?state'B))"
            using \<open>getM ?state'A = getM ?state'B\<close>
            by simp

          let ?state''A = "?state'A\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          let ?state''B = "?state'B\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          have 
            "getM ?state''A = getM ?state''B"
            "getF ?state''A = getF ?state''B"
            "getWatch1 ?state''A = getWatch1 ?state''B"
            "getWatch2 ?state''A = getWatch2 ?state''B"
            "getConflictFlag ?state''A = getConflictFlag ?state''B"
            "getSATFlag ?state''A = getSATFlag ?state''B"
            using Cons
            unfolding swapWatches_def
            by auto
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state''A) (getWatch1 ?state''A) (getWatch2 ?state''A)"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getM ?state''A = getM stateA \<and>
          getF ?state''A = getF stateA \<and> 
          getSATFlag ?state''A = getSATFlag stateA \<and> 
            getQ ?state''A = getQ stateA"
            unfolding swapWatches_def
            by simp
          moreover
          have "getM ?state''B = getM stateB \<and>
          getF ?state''B = getF stateB \<and> 
          getSATFlag ?state''B = getSATFlag stateB \<and> 
            getQ ?state''B = getQ stateB"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons(4) Cons(5)
            using Cons(1)[of "?state''A" "?state''B" "clause # newWl"]
            using \<open>getM ?state''A = getM ?state''B\<close>
            using \<open>getF ?state''A = getF ?state''B\<close>
            using \<open>getWatch1 ?state''A = getWatch1 ?state''B\<close>
            using \<open>getWatch2 ?state''A = getWatch2 ?state''B\<close>
            using \<open>getConflictFlag ?state''A = getConflictFlag ?state''B\<close>
            using \<open>getSATFlag ?state''A = getSATFlag ?state''B\<close>
            using Cons(3)
            using \<open>getWatch1 ?state'A clause = Some ?w1\<close>
            using \<open>getWatch2 ?state'A clause = Some ?w2\<close>
            using \<open>getWatch1 ?state'B clause = Some ?w1\<close>
            using \<open>getWatch2 ?state'B clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 stateA clause\<close>
            using \<open>Some literal = getWatch1 stateB clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'A))\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'B))\<close>
            using \<open>getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A) = None\<close>
            using \<open>getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = None\<close>
            using \<open>literalFalse ?w1 (elements (getM ?state'A))\<close>
            using \<open>literalFalse ?w1 (elements (getM ?state'B))\<close>
            by (simp add:Let_def)
        next
          case False
          hence "\<not> literalFalse ?w1 (elements (getM ?state'B))"
            using \<open>getM ?state'A = getM ?state'B\<close>
            by simp
          let ?state''A = "setReason ?w1 clause (?state'A\<lparr>getQ := (if ?w1 el (getQ ?state'A) then (getQ ?state'A) else (getQ ?state'A) @ [?w1])\<rparr>)"
          let ?state''B = "setReason ?w1 clause (?state'B\<lparr>getQ := (if ?w1 el (getQ ?state'B) then (getQ ?state'B) else (getQ ?state'B) @ [?w1])\<rparr>)"
          
          have 
            "getM ?state''A = getM ?state''B"
            "getF ?state''A = getF ?state''B"
            "getWatch1 ?state''A = getWatch1 ?state''B"
            "getWatch2 ?state''A = getWatch2 ?state''B"
            "getConflictFlag ?state''A = getConflictFlag ?state''B"
            "getSATFlag ?state''A = getSATFlag ?state''B"
            using Cons
            unfolding setReason_def
            unfolding swapWatches_def
            by auto

          from Cons(2)
          have "InvariantWatchesEl (getF ?state''A) (getWatch1 ?state''A) (getWatch2 ?state''A)"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state''A = getM stateA \<and>
            getF ?state''A = getF stateA \<and> 
            getSATFlag ?state''A = getSATFlag stateA \<and> 
            getQ ?state''A = (if ?w1 el (getQ stateA) then (getQ stateA) else (getQ stateA) @ [?w1])"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state''B = getM stateB \<and>
            getF ?state''B = getF stateB \<and> 
            getSATFlag ?state''B = getSATFlag stateB \<and> 
            getQ ?state''B = (if ?w1 el (getQ stateB) then (getQ stateB) else (getQ stateB) @ [?w1])"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          ultimately
          show ?thesis
            using Cons(4) Cons(5)
            using Cons(1)[of "?state''A" "?state''B" "clause # newWl"]
            using \<open>getM ?state''A = getM ?state''B\<close>
            using \<open>getF ?state''A = getF ?state''B\<close>
            using \<open>getWatch1 ?state''A = getWatch1 ?state''B\<close>
            using \<open>getWatch2 ?state''A = getWatch2 ?state''B\<close>
            using \<open>getConflictFlag ?state''A = getConflictFlag ?state''B\<close>
            using \<open>getSATFlag ?state''A = getSATFlag ?state''B\<close>
            using Cons(3)
            using \<open>getWatch1 ?state'A clause = Some ?w1\<close>
            using \<open>getWatch2 ?state'A clause = Some ?w2\<close>
            using \<open>getWatch1 ?state'B clause = Some ?w1\<close>
            using \<open>getWatch2 ?state'B clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 stateA clause\<close>
            using \<open>Some literal = getWatch1 stateB clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'A))\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'B))\<close>
            using \<open>getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A) = None\<close>
            using \<open>getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = None\<close>
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'A))\<close>
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'B))\<close>
            by (simp add:Let_def)
        qed
      qed
    qed
  next
    case False
    hence "Some literal \<noteq> getWatch1 stateB clause"
      using Cons
      by simp

    let ?state'A = stateA
    let ?state'B = stateB

    have 
      "getM ?state'A = getM ?state'B"
      "getF ?state'A = getF ?state'B"
      "getWatch1 ?state'A = getWatch1 ?state'B"
      "getWatch2 ?state'A = getWatch2 ?state'B"
      "getConflictFlag ?state'A = getConflictFlag ?state'B"
      "getSATFlag ?state'A = getSATFlag ?state'B"
      using Cons
      by auto

    let ?w1 = wa
    have "getWatch1 ?state'A clause = Some ?w1"
      using \<open>getWatch1 stateA clause = Some wa\<close>
      by auto
    hence "getWatch1 ?state'B clause = Some ?w1"
      using Cons
      by simp
    let ?w2 = wb
    have "getWatch2 ?state'A clause = Some ?w2"
      using \<open>getWatch2 stateA clause = Some wb\<close>
      by auto
    hence "getWatch2 ?state'B clause = Some ?w2"
      using Cons
      by simp

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'A))")
      case True
      hence "literalTrue ?w1 (elements (getM ?state'B))"
        using Cons
        by simp

      show ?thesis
        using Cons(1)[of "?state'A" "?state'B" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6) Cons(7) Cons(8) Cons(9)
        using \<open>\<not> Some literal = getWatch1 stateA clause\<close>
        using \<open>\<not> Some literal = getWatch1 stateB clause\<close>
        using \<open>getWatch1 ?state'A clause = Some ?w1\<close>
        using \<open>getWatch1 ?state'B clause = Some ?w1\<close>
        using \<open>getWatch2 ?state'A clause = Some ?w2\<close>
        using \<open>getWatch2 ?state'B clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'A))\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'B))\<close>
        by (simp add:Let_def)
    next
      case False
      hence "\<not> literalTrue ?w1 (elements (getM ?state'B))"
        using \<open>getM ?state'A = getM ?state'B\<close>
        by simp
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A)")
        case (Some l')
        hence "getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = Some l'"
          using \<open>getF ?state'A = getF ?state'B\<close>
          using \<open>getM ?state'A = getM ?state'B\<close>
          by simp

        have "l' el (nth (getF ?state'A) clause)"
          using Some
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp
        hence "l' el (nth (getF ?state'B) clause)"
          using \<open>getF ?state'A = getF ?state'B\<close>
          by simp

        let ?state''A = "setWatch2 clause l' ?state'A"
        let ?state''B = "setWatch2 clause l' ?state'B"

        have 
          "getM ?state''A = getM ?state''B"
          "getF ?state''A = getF ?state''B"
          "getWatch1 ?state''A = getWatch1 ?state''B"
          "getWatch2 ?state''A = getWatch2 ?state''B"
          "getConflictFlag ?state''A = getConflictFlag ?state''B"
          "getSATFlag ?state''A = getSATFlag ?state''B"
          using Cons
          unfolding setWatch2_def
          by auto


        from Cons(2)
        have "InvariantWatchesEl (getF ?state''A) (getWatch1 ?state''A) (getWatch2 ?state''A)"
          using \<open>l' el (nth (getF ?state'A) clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state''A = getM stateA \<and>
          getF ?state''A = getF stateA \<and> 
          getSATFlag ?state''A = getSATFlag stateA \<and> 
          getQ ?state''A = getQ stateA"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''A" "?state''B" "newWl"]
          using \<open>getM ?state''A = getM ?state''B\<close>
          using \<open>getF ?state''A = getF ?state''B\<close>
          using \<open>getWatch1 ?state''A = getWatch1 ?state''B\<close>
          using \<open>getWatch2 ?state''A = getWatch2 ?state''B\<close>
          using \<open>getConflictFlag ?state''A = getConflictFlag ?state''B\<close>
          using \<open>getSATFlag ?state''A = getSATFlag ?state''B\<close>
          using Cons(3)
          using \<open>getWatch1 ?state'A clause = Some ?w1\<close>
          using \<open>getWatch2 ?state'A clause = Some ?w2\<close>
          using \<open>getWatch1 ?state'B clause = Some ?w1\<close>
          using \<open>getWatch2 ?state'B clause = Some ?w2\<close>
          using \<open>\<not> Some literal = getWatch1 stateA clause\<close>
          using \<open>\<not> Some literal = getWatch1 stateB clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'A))\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'B))\<close>
          using \<open>getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A) = Some l'\<close>
          using \<open>getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = Some l'\<close>
          by (simp add:Let_def)
      next
        case None
        hence "getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = None"
          using \<open>getF ?state'A = getF ?state'B\<close> \<open>getM ?state'A = getM ?state'B\<close>
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'A))")
          case True
          hence "literalFalse ?w1 (elements (getM ?state'B))"
            using \<open>getM ?state'A = getM ?state'B\<close>
            by simp

          let ?state''A = "?state'A\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          let ?state''B = "?state'B\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          have 
            "getM ?state''A = getM ?state''B"
            "getF ?state''A = getF ?state''B"
            "getWatch1 ?state''A = getWatch1 ?state''B"
            "getWatch2 ?state''A = getWatch2 ?state''B"
            "getConflictFlag ?state''A = getConflictFlag ?state''B"
            "getSATFlag ?state''A = getSATFlag ?state''B"
            using Cons
            by auto
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state''A) (getWatch1 ?state''A) (getWatch2 ?state''A)"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getM ?state''A = getM stateA \<and>
          getF ?state''A = getF stateA \<and> 
          getSATFlag ?state''A = getSATFlag stateA \<and> 
            getQ ?state''A = getQ stateA"
            by simp
          ultimately
          show ?thesis
            using Cons(4) Cons(5)
            using Cons(1)[of "?state''A" "?state''B" "clause # newWl"]
            using \<open>getM ?state''A = getM ?state''B\<close>
            using \<open>getF ?state''A = getF ?state''B\<close>
            using \<open>getWatch1 ?state''A = getWatch1 ?state''B\<close>
            using \<open>getWatch2 ?state''A = getWatch2 ?state''B\<close>
            using \<open>getConflictFlag ?state''A = getConflictFlag ?state''B\<close>
            using \<open>getSATFlag ?state''A = getSATFlag ?state''B\<close>
            using Cons(3)
            using \<open>getWatch1 ?state'A clause = Some ?w1\<close>
            using \<open>getWatch2 ?state'A clause = Some ?w2\<close>
            using \<open>getWatch1 ?state'B clause = Some ?w1\<close>
            using \<open>getWatch2 ?state'B clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 stateA clause\<close>
            using \<open>\<not> Some literal = getWatch1 stateB clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'A))\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'B))\<close>
            using \<open>getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A) = None\<close>
            using \<open>getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = None\<close>
            using \<open>literalFalse ?w1 (elements (getM ?state'A))\<close>
            using \<open>literalFalse ?w1 (elements (getM ?state'B))\<close>
            by (simp add:Let_def)
        next
          case False
          hence "\<not> literalFalse ?w1 (elements (getM ?state'B))"
            using \<open>getM ?state'A = getM ?state'B\<close>
            by simp
          let ?state''A = "setReason ?w1 clause (?state'A\<lparr>getQ := (if ?w1 el (getQ ?state'A) then (getQ ?state'A) else (getQ ?state'A) @ [?w1])\<rparr>)"
          let ?state''B = "setReason ?w1 clause (?state'B\<lparr>getQ := (if ?w1 el (getQ ?state'B) then (getQ ?state'B) else (getQ ?state'B) @ [?w1])\<rparr>)"
          
          have 
            "getM ?state''A = getM ?state''B"
            "getF ?state''A = getF ?state''B"
            "getWatch1 ?state''A = getWatch1 ?state''B"
            "getWatch2 ?state''A = getWatch2 ?state''B"
            "getConflictFlag ?state''A = getConflictFlag ?state''B"
            "getSATFlag ?state''A = getSATFlag ?state''B"
            using Cons
            unfolding setReason_def
            by auto

          from Cons(2)
          have "InvariantWatchesEl (getF ?state''A) (getWatch1 ?state''A) (getWatch2 ?state''A)"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state''A = getM stateA \<and>
            getF ?state''A = getF stateA \<and> 
            getSATFlag ?state''A = getSATFlag stateA \<and> 
            getQ ?state''A = (if ?w1 el (getQ stateA) then (getQ stateA) else (getQ stateA) @ [?w1])"
            unfolding setReason_def
            by auto
          ultimately
          show ?thesis
            using Cons(4) Cons(5)
            using Cons(1)[of "?state''A" "?state''B" "clause # newWl"]
            using \<open>getM ?state''A = getM ?state''B\<close>
            using \<open>getF ?state''A = getF ?state''B\<close>
            using \<open>getWatch1 ?state''A = getWatch1 ?state''B\<close>
            using \<open>getWatch2 ?state''A = getWatch2 ?state''B\<close>
            using \<open>getConflictFlag ?state''A = getConflictFlag ?state''B\<close>
            using \<open>getSATFlag ?state''A = getSATFlag ?state''B\<close>
            using Cons(3)
            using \<open>getWatch1 ?state'A clause = Some ?w1\<close>
            using \<open>getWatch2 ?state'A clause = Some ?w2\<close>
            using \<open>getWatch1 ?state'B clause = Some ?w1\<close>
            using \<open>getWatch2 ?state'B clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 stateA clause\<close>
            using \<open>\<not> Some literal = getWatch1 stateB clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'A))\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'B))\<close>
            using \<open>getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A) = None\<close>
            using \<open>getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = None\<close>
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'A))\<close>
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'B))\<close>
            by (simp add:Let_def)
        qed
      qed
    qed
  qed
qed

lemma notifyWatchesLoopPreservedWatches:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)"
shows
  "let state' = (notifyWatches_loop literal Wl newWl state) in
     \<forall> c. c \<notin> set Wl \<longrightarrow> (getWatch1 state' c) = (getWatch1 state c) \<and> (getWatch2 state' c) = (getWatch2 state c)
  " 
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  from \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)\<close>
  have "0 \<le> clause \<and> clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getM ?state' = getM state \<and> 
        getF ?state' = getF state"
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(3)
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>Some literal = getWatch1 state clause\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        apply (simp add:Let_def)
        unfolding swapWatches_def
        by simp
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(3)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          apply (simp add: Let_def)
          unfolding setWatch2_def
          unfolding swapWatches_def
          by simp
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            apply (simp add: Let_def)
            unfolding swapWatches_def
            by simp
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            apply (simp add: Let_def)
            unfolding setReason_def
            unfolding swapWatches_def
            by simp
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons
        using \<open>\<not> Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state')) clause"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state')) clause\<close>
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''"]
          using Cons(3)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>\<not> Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          apply (simp add: Let_def)
          unfolding setWatch2_def
          by simp
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state"
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state"
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            apply (simp add: Let_def)
            unfolding setReason_def
            by simp
        qed
      qed
    qed
  qed
qed

lemma InvariantWatchesElNotifyWatchesLoop:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)"
shows
  "let state' = (notifyWatches_loop literal Wl newWl state) in
     InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state')"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  from \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)\<close>
  have "0 \<le> clause" and "clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True

      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getF ?state' = getF state"
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons
        using \<open>Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getF ?state'' = getF state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons
        using \<open>\<not> Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getF ?state'' = getF state"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>\<not> Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            by simp
          ultimately
          show ?thesis
            using Cons
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding setReason_def
            by simp       
          ultimately
          show ?thesis
            using Cons
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        qed
      qed
    qed
  qed
qed

lemma InvariantWatchesDifferNotifyWatchesLoop:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)"
shows
  "let state' = (notifyWatches_loop literal Wl newWl state) in
     InvariantWatchesDiffer (getF state') (getWatch1 state') (getWatch2 state')"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  from \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)\<close>
  have "0 \<le> clause" and "clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True

      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(3)
      have "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesDiffer_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getF ?state' = getF state"
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(4)
        using \<open>Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "l' \<noteq> literal" "l' \<noteq> ?w1" "l' \<noteq> ?w2"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          unfolding swapWatches_def
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' \<noteq> ?w1\<close>
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          unfolding InvariantWatchesDiffer_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getF ?state'' = getF state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto       
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons
        using \<open>\<not> Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "l' \<noteq> ?w1" "l' \<noteq> ?w2"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          unfolding swapWatches_def
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' \<noteq> ?w1\<close>
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          unfolding InvariantWatchesDiffer_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getF ?state'' = getF state"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>\<not> Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            by simp
          ultimately
          show ?thesis
            using Cons
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding setReason_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding setReason_def
            by simp       
          ultimately
          show ?thesis
            using Cons
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        qed
      qed
    qed
  qed
qed


lemma InvariantWatchListsContainOnlyClausesFromFNotifyWatchesLoop:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<or> c \<in> set newWl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)"
shows
  "let state' = (notifyWatches_loop literal Wl newWl state) in
     InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state')"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    by simp
next
  case (Cons clause Wl')
  from \<open>\<forall>c. c \<in> set (clause # Wl') \<or> c \<in> set newWl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)\<close>
  have "0 \<le> clause" and "clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True

      from Cons(2)
      have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state') (getF ?state')"
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(3)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "(getF state) = (getF ?state')"
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons
        using \<open>Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')"
          using \<open>clause < length (getF state)\<close>
          unfolding InvariantWatchListsContainOnlyClausesFromF_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "(getF state) = (getF ?state'')"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')"
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover 
          have "(getF state) = (getF ?state'')"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "(getF state) = (getF ?state'')"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons
        using \<open>\<not> Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')"
          using \<open>clause < length (getF state)\<close>
          unfolding setWatch2_def
          unfolding InvariantWatchListsContainOnlyClausesFromF_def
          by auto
        moreover 
        from Cons(3)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "(getF state) = (getF ?state'')"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>\<not> Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            by simp
          ultimately
          show ?thesis
            using Cons
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')"
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        qed
      qed
    qed
  qed
qed

lemma InvariantWatchListsCharacterizationNotifyWatchesLoop:
  fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
  assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchListsUniq (getWatchList state)"
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)"
  "\<forall> (c::nat) (l::Literal). l \<noteq> literal \<longrightarrow>
             (c \<in> set (getWatchList state l)) = (Some l = getWatch1 state c \<or> Some l = getWatch2 state c)"
  "\<forall> (c::nat). (c \<in> set newWl \<or> c \<in> set Wl) = (Some literal = (getWatch1 state c) \<or> Some literal = (getWatch2 state c))"
  "set Wl \<inter> set newWl = {}"
  "uniq Wl"
  "uniq newWl"
  shows
  "let state' = (notifyWatches_loop literal Wl newWl state) in
     InvariantWatchListsCharacterization (getWatchList state') (getWatch1 state') (getWatch2 state') \<and>
     InvariantWatchListsUniq (getWatchList state')"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantWatchListsUniq_def
    by simp
next
  case (Cons clause Wl')
  from \<open>uniq (clause # Wl')\<close>
  have "clause \<notin> set Wl'"
    by (simp add:uniqAppendIff)

  have "set Wl' \<inter> set (clause # newWl) = {}"
    using Cons(8)
    using \<open>clause \<notin> set Wl'\<close>
    by simp

  have "uniq Wl'"
    using Cons(9)
    using uniqAppendIff
    by simp
  
  have "uniq (clause # newWl)"
    using Cons(10) Cons(8)
    using uniqAppendIff
    by force

  from \<open>\<forall>c. c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)\<close>
  have "0 \<le> clause" and "clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(3)
      have "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesDiffer_def
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(4)
      have "InvariantWatchListsUniq (getWatchList ?state')"
        unfolding InvariantWatchListsUniq_def
        unfolding swapWatches_def
        by auto
      moreover
      have "(getF ?state') = (getF state)" and "(getWatchList ?state') = (getWatchList state)"
        unfolding swapWatches_def
        by auto
      moreover 
      have "\<forall>c l. l \<noteq> literal \<longrightarrow>
        (c \<in> set (getWatchList ?state' l)) =
        (Some l = getWatch1 ?state' c \<or> Some l = getWatch2 ?state' c)"
        using Cons(6)
        using \<open>(getWatchList ?state') = (getWatchList state)\<close>
        using swapWatchesEffect
        by auto
      moreover 
      have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
        (Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c)"
        using Cons(7)
        using swapWatchesEffect
        by auto
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(5)
        using \<open>Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>uniq Wl'\<close>
        using \<open>uniq (clause # newWl)\<close>
        using \<open>set Wl' \<inter> set (clause # newWl) = {}\<close>
        by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "l' \<noteq> literal" "l' \<noteq> ?w1" "l' \<noteq> ?w2"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          unfolding swapWatches_def
          by auto
        
        let ?state'' = "setWatch2 clause l' ?state'"
        
        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>l' \<noteq> ?w1\<close>
          unfolding InvariantWatchesDiffer_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        moreover
        have "clause \<notin> set (getWatchList state l')"
          using \<open>l' \<noteq> literal\<close>
          using \<open>l' \<noteq> ?w1\<close> \<open>l' \<noteq> ?w2\<close>
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using Cons(6)
          unfolding swapWatches_def
          by simp
        with Cons(4)
        have "InvariantWatchListsUniq (getWatchList ?state'')"
          unfolding InvariantWatchListsUniq_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          using uniqAppendIff
          by force
        moreover
        have "(getF ?state'') = (getF state)" and 
          "(getWatchList ?state'') = (getWatchList state)(l' := clause # (getWatchList state l'))"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover 
        have "\<forall>c l. l \<noteq> literal \<longrightarrow>
          (c \<in> set (getWatchList ?state'' l)) =
          (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
        proof-
          {
            fix c::nat and l::Literal
            assume "l \<noteq> literal"
            have "(c \<in> set (getWatchList ?state'' l)) = (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
            proof (cases "c = clause")
              case True
              show ?thesis
              proof (cases "l = l'")
                case True
                thus ?thesis
                  using \<open>c = clause\<close>
                  unfolding setWatch2_def
                  by simp
              next
                case False
                show ?thesis
                  using Cons(6)
                  using \<open>(getWatchList ?state'') = (getWatchList state)(l' := clause # (getWatchList state l'))\<close>
                  using \<open>l \<noteq> l'\<close>
                  using \<open>l \<noteq> literal\<close>
                  using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                  using \<open>getWatch2 ?state' clause = Some ?w2\<close>
                  using \<open>Some literal = getWatch1 state clause\<close>
                  using \<open>c = clause\<close>
                  using swapWatchesEffect
                  unfolding swapWatches_def
                  unfolding setWatch2_def
                  by simp
              qed
            next
              case False
              thus ?thesis
                using Cons(6)
                using \<open>l \<noteq> literal\<close>
                using \<open>(getWatchList ?state'') = (getWatchList state)(l' := clause # (getWatchList state l'))\<close>
                using \<open>c \<noteq> clause\<close>
                unfolding setWatch2_def
                using swapWatchesEffect[of "clause" "state" "c"]
                by auto
            qed
          }
          thus ?thesis
            by simp
        qed
        moreover
        have "\<forall>c. (c \<in> set newWl \<or> c \<in> set Wl') =
          (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
        proof-
          show ?thesis
          proof
            fix c :: nat
            show "(c \<in> set newWl \<or> c \<in> set Wl') =
              (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
            proof
              assume "c \<in> set newWl \<or> c \<in> set Wl'"
              show "Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
              proof-
                from \<open>c \<in> set newWl \<or> c \<in> set Wl'\<close>
                have "Some literal = getWatch1 state c \<or> Some literal = getWatch2 state c"
                  using Cons(7)
                  by auto
                
                from Cons(8) \<open>clause \<notin> set Wl'\<close> \<open>c \<in> set newWl \<or> c \<in> set Wl'\<close>
                have "c \<noteq> clause"
                  by auto
                
                show ?thesis
                  using \<open>Some literal = getWatch1 state c \<or> Some literal = getWatch2 state c\<close>
                  using \<open>c \<noteq> clause\<close>
                  using swapWatchesEffect
                  unfolding setWatch2_def
                  by simp
              qed
            next
              assume "Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
              show "c \<in> set newWl \<or> c \<in> set Wl'"
              proof-
                have "Some literal \<noteq> getWatch1 ?state'' clause \<and>  Some literal \<noteq> getWatch2 ?state'' clause"
                  using \<open>l' \<noteq> literal\<close>
                  using \<open>clause < length (getF state)\<close>
                  using \<open>InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)\<close>
                  using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                  using \<open>getWatch2 ?state' clause = Some ?w2\<close>
                  using \<open>Some literal = getWatch1 state clause\<close>
                  unfolding InvariantWatchesDiffer_def
                  unfolding setWatch2_def
                  unfolding swapWatches_def
                  by auto
                thus ?thesis
                  using \<open>Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c\<close>
                  using Cons(7)
                  using swapWatchesEffect
                  unfolding setWatch2_def
                  by (auto split: if_split_asm)
              qed
            qed
          qed
        qed
        moreover
        have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
          (Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c)"
          using Cons(7)
          using swapWatchesEffect
          by auto
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(5)
          using \<open>uniq Wl'\<close>
          using \<open>uniq newWl\<close>
          using \<open>set Wl' \<inter> set (clause # newWl) = {}\<close>
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          by (simp add: Let_def fun_upd_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchListsUniq (getWatchList ?state'')"
            unfolding InvariantWatchListsUniq_def
            unfolding swapWatches_def
            by auto
          moreover 
          have "(getF state) = (getF ?state'')" and "(getWatchList state) = (getWatchList ?state'')" 
            unfolding swapWatches_def
            by auto
          moreover
          have "\<forall>c l. l \<noteq> literal \<longrightarrow>
            (c \<in> set (getWatchList ?state'' l)) =
            (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
            using Cons(6)
            using \<open>(getWatchList state) = (getWatchList ?state'')\<close>
            using swapWatchesEffect
            by auto
          moreover 
          have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
            (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
            using Cons(7)
            using swapWatchesEffect
            by auto
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(5)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            using \<open>uniq (clause # newWl)\<close>
            using \<open>set Wl' \<inter> set (clause # newWl) = {}\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchListsUniq (getWatchList ?state'')"
            unfolding InvariantWatchListsUniq_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover 
          have "(getF state) = (getF ?state'')" and "(getWatchList state) = (getWatchList ?state'')" 
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "\<forall>c l. l \<noteq> literal \<longrightarrow>
            (c \<in> set (getWatchList ?state'' l)) =
            (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
            using Cons(6)
            using \<open>(getWatchList state) = (getWatchList ?state'')\<close>
            using swapWatchesEffect
            unfolding setReason_def
            by auto
          moreover 
          have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
            (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
            using Cons(7)
            using swapWatchesEffect
            unfolding setReason_def
            by auto
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(5)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            using \<open>uniq (clause # newWl)\<close>
            using \<open>set Wl' \<inter> set (clause # newWl) = {}\<close>
            by (simp add: Let_def)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto    

    have "Some literal = getWatch2 state clause"
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using \<open>Some literal \<noteq> getWatch1 state clause\<close>
      using Cons(7)
      by force

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      from Cons(7) have
        "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
        (Some literal = getWatch1 state c \<or> Some literal = getWatch2 state c)"
        by auto
      thus ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6)
        using \<open>\<not> Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>uniq (clause # newWl)\<close>
        using \<open>uniq Wl'\<close>
        using \<open>set Wl' \<inter> set (clause # newWl) = {}\<close>
        by simp
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "l' \<noteq> literal" "l' \<noteq> ?w1" "l' \<noteq> ?w2"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          using \<open>Some literal = getWatch2 state clause\<close>
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>l' \<noteq> ?w1\<close>
          unfolding InvariantWatchesDiffer_def
          unfolding setWatch2_def
          by simp
        moreover
        have "clause \<notin> set (getWatchList state l')"
          using \<open>l' \<noteq> literal\<close>
          using \<open>l' \<noteq> ?w1\<close> \<open>l' \<noteq> ?w2\<close>
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using Cons(6)
          by simp
        with Cons(4)
        have "InvariantWatchListsUniq (getWatchList ?state'')"
          unfolding InvariantWatchListsUniq_def
          unfolding setWatch2_def
          using uniqAppendIff
          by force
        moreover
        have "(getF ?state'') = (getF state)" and 
          "(getWatchList ?state'') = (getWatchList state)(l' := clause # (getWatchList state l'))"
          unfolding setWatch2_def
          by auto
        moreover 
        have "\<forall>c l. l \<noteq> literal \<longrightarrow>
          (c \<in> set (getWatchList ?state'' l)) =
          (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
        proof-
          {
            fix c::nat and l::Literal
            assume "l \<noteq> literal"
            have "(c \<in> set (getWatchList ?state'' l)) = (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
            proof (cases "c = clause")
              case True
              show ?thesis
              proof (cases "l = l'")
                case True
                thus ?thesis
                  using \<open>c = clause\<close>
                  unfolding setWatch2_def
                  by simp
              next
                case False
                show ?thesis
                  using Cons(6)
                  using \<open>(getWatchList ?state'') = (getWatchList state)(l' := clause # (getWatchList state l'))\<close>
                  using \<open>l \<noteq> l'\<close>
                  using \<open>l \<noteq> literal\<close>
                  using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                  using \<open>getWatch2 ?state' clause = Some ?w2\<close>
                  using \<open>Some literal = getWatch2 state clause\<close>
                  using \<open>c = clause\<close>
                  unfolding setWatch2_def
                  by simp
              qed
            next
              case False
              thus ?thesis
                using Cons(6)
                using \<open>l \<noteq> literal\<close>
                using \<open>(getWatchList ?state'') = (getWatchList state)(l' := clause # (getWatchList state l'))\<close>
                using \<open>c \<noteq> clause\<close>
                unfolding setWatch2_def
                by auto
            qed
          }
          thus ?thesis
            by simp
        qed
        moreover
        have "\<forall>c. (c \<in> set newWl \<or> c \<in> set Wl') =
          (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
        proof-
          show ?thesis
          proof
            fix c :: nat
            show "(c \<in> set newWl \<or> c \<in> set Wl') =
              (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
            proof
              assume "c \<in> set newWl \<or> c \<in> set Wl'"
              show "Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
              proof-
                from \<open>c \<in> set newWl \<or> c \<in> set Wl'\<close>
                have "Some literal = getWatch1 state c \<or> Some literal = getWatch2 state c"
                  using Cons(7)
                  by auto
                
                from Cons(8) \<open>clause \<notin> set Wl'\<close> \<open>c \<in> set newWl \<or> c \<in> set Wl'\<close>
                have "c \<noteq> clause"
                  by auto
                
                show ?thesis
                  using \<open>Some literal = getWatch1 state c \<or> Some literal = getWatch2 state c\<close>
                  using \<open>c \<noteq> clause\<close>
                  unfolding setWatch2_def
                  by simp
              qed
            next
              assume "Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
              show "c \<in> set newWl \<or> c \<in> set Wl'"
              proof-
                have "Some literal \<noteq> getWatch1 ?state'' clause \<and>  Some literal \<noteq> getWatch2 ?state'' clause"
                  using \<open>l' \<noteq> literal\<close>
                  using \<open>clause < length (getF state)\<close>
                  using \<open>InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)\<close>
                  using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                  using \<open>getWatch2 ?state' clause = Some ?w2\<close>
                  using \<open>Some literal = getWatch2 state clause\<close>
                  unfolding InvariantWatchesDiffer_def
                  unfolding setWatch2_def
                  by auto
                thus ?thesis
                  using \<open>Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c\<close>
                  using Cons(7)
                  unfolding setWatch2_def
                  by (auto split: if_split_asm)
              qed
            qed
          qed
        qed
        moreover
        have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
          (Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c)"
          using Cons(7)
          by auto
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(5)
          using \<open>uniq Wl'\<close>
          using \<open>uniq newWl\<close>
          using \<open>set Wl' \<inter> set (clause # newWl) = {}\<close>
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>\<not> Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          by (simp add: Let_def fun_upd_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchListsUniq (getWatchList ?state'')"
            unfolding InvariantWatchListsUniq_def
            by auto
          moreover 
          have "(getF state) = (getF ?state'')"
            by auto
          moreover
          have "\<forall>c l. l \<noteq> literal \<longrightarrow>
            (c \<in> set (getWatchList ?state'' l)) =
            (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
            using Cons(6)
            by simp
          moreover 
          have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
            (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
            using Cons(7)
            by auto
          ultimately
          have "let state' = notifyWatches_loop literal Wl' (clause # newWl) ?state'' in 
                      InvariantWatchListsCharacterization (getWatchList state') (getWatch1 state') (getWatch2 state') \<and>
                      InvariantWatchListsUniq (getWatchList state')"
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(5)
            using \<open>uniq Wl'\<close>
            using \<open>uniq (clause # newWl)\<close>
            using \<open>set Wl' \<inter> set (clause # newWl) = {}\<close>
            apply (simp only: Let_def)
            by (simp (no_asm_use)) (simp)
          thus ?thesis
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal \<noteq>  getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"


          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchListsUniq (getWatchList ?state'')"
            unfolding InvariantWatchListsUniq_def
            unfolding setReason_def
            by auto
          moreover 
          have "(getF state) = (getF ?state'')"
            unfolding setReason_def
            by auto
          moreover
          have "\<forall>c l. l \<noteq> literal \<longrightarrow>
            (c \<in> set (getWatchList ?state'' l)) =
            (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
            using Cons(6)
            unfolding setReason_def
            by auto
          moreover 
          have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
            (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
            using Cons(7)
            unfolding setReason_def
            by auto
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(5)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            using \<open>uniq (clause # newWl)\<close>
            using \<open>set Wl' \<inter> set (clause # newWl) = {}\<close>
            by (simp add: Let_def)
        qed
      qed
    qed
  qed
qed

lemma NotifyWatchesLoopWatchCharacterizationEffect:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantConsistent (getM state)" and
  "InvariantUniq (getM state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) M"
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)" and
  "getM state = M @ [(opposite literal, decision)]"
  "uniq Wl"
  "\<forall>  (c::nat). c \<in> set Wl \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)"

shows
  "let state' = notifyWatches_loop literal Wl newWl state in
     \<forall> (c::nat). c \<in> set Wl \<longrightarrow> (\<forall> w1 w2.(Some w1 = (getWatch1 state' c) \<and> Some w2 = (getWatch2 state' c)) \<longrightarrow> 
      (watchCharacterizationCondition w1 w2 (getM state') (nth (getF state') c)  \<and> 
       watchCharacterizationCondition w2 w1 (getM state') (nth (getF state') c))
     )"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  from \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)\<close>
  have "0 \<le> clause \<and> clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  have "uniq Wl'" "clause \<notin> set Wl'"
    using Cons(9)
    by (auto simp add: uniqAppendIff)
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto
    with True have
      "?w2 = literal"
      unfolding swapWatches_def
      by simp

    from \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close>
    have "?w1 el (nth (getF state) clause)" "?w2 el (nth (getF state) clause)"
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto

    from \<open>InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)\<close>
    have "?w1 \<noteq> ?w2"
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
      unfolding InvariantWatchesDiffer_def
      unfolding swapWatches_def
      by auto

    have "\<not> literalFalse ?w2 (elements M)"
      using \<open>?w2 = literal\<close>
      using Cons(5)
      using Cons(8)
      unfolding InvariantUniq_def
      by (simp add: uniqAppendIff)

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True

      let ?fState = "notifyWatches_loop literal Wl' (clause # newWl) ?state'"

      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(3)
      have "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesDiffer_def
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(4)
      have "InvariantConsistent (getM ?state')"
        unfolding InvariantConsistent_def
        unfolding swapWatches_def
        by simp
      moreover
      from Cons(5)
      have "InvariantUniq (getM ?state')"
        unfolding InvariantUniq_def
        unfolding swapWatches_def
        by simp
      moreover
      from Cons(6)
      have "InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') M"
        unfolding swapWatches_def
        unfolding InvariantWatchCharacterization_def
        unfolding watchCharacterizationCondition_def
        by simp
      moreover
      have "getM ?state' = getM state"
        "getF ?state' = getF state"
        unfolding swapWatches_def
        by auto
      moreover 
      have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state' c)  \<or> Some literal = (getWatch2 ?state' c)"
        using Cons(10)
        unfolding swapWatches_def
        by auto
      moreover
      have "getWatch1 ?fState clause = getWatch1 ?state' clause \<and> getWatch2 ?fState clause = getWatch2 ?state' clause"
        using \<open>clause \<notin> set Wl'\<close>
        using \<open>InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')\<close> \<open>getF ?state' = getF state\<close>
        using Cons(7)
        using notifyWatchesLoopPreservedWatches[of "?state'" "Wl'" "literal" "clause # newWl" ]
        by (simp add: Let_def)
      moreover
      have "watchCharacterizationCondition ?w1 ?w2 (getM ?fState) (getF ?fState ! clause) \<and>
            watchCharacterizationCondition ?w2 ?w1 (getM ?fState) (getF ?fState ! clause)"
      proof-
        have "(getM ?fState) = (getM state) \<and> (getF ?fState = getF state)"
          using notifyWatchesLoopPreservedVariables[of "?state'" "Wl'" "literal" "clause # newWl"]
          using \<open>InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')\<close> \<open>getF ?state' = getF state\<close>
          using Cons(7)
          unfolding swapWatches_def
          by (simp add: Let_def)
        moreover
        have "\<not> literalFalse ?w1 (elements M)"
          using \<open>literalTrue ?w1 (elements (getM ?state'))\<close> \<open>?w1 \<noteq> ?w2\<close> \<open>?w2 = literal\<close>
          using Cons(4) Cons(8)
          unfolding InvariantConsistent_def
          unfolding swapWatches_def
          by (auto simp add: inconsistentCharacterization)
        moreover 
        have "elementLevel (opposite ?w2) (getM ?state') = currentLevel (getM ?state')"
          using \<open>?w2 = literal\<close>
          using Cons(5) Cons(8)
          unfolding InvariantUniq_def
          unfolding swapWatches_def
          by (auto simp add: uniqAppendIff elementOnCurrentLevel)
        ultimately
        show ?thesis
          using \<open>getWatch1 ?fState clause = getWatch1 ?state' clause \<and> getWatch2 ?fState clause = getWatch2 ?state' clause\<close>
          using \<open>?w2 = literal\<close> \<open>?w1 \<noteq> ?w2\<close>
          using \<open>?w1 el (nth (getF state) clause)\<close>
          using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
          unfolding watchCharacterizationCondition_def
          using elementLevelLeqCurrentLevel[of "?w1" "getM ?state'"]
          using notifyWatchesLoopPreservedVariables[of "?state'" "Wl'" "literal" "clause # newWl"]
          using \<open>InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')\<close> \<open>getF ?state' = getF state\<close>
          using Cons(7) 
          using Cons(8)
          unfolding swapWatches_def
          by (auto simp add: Let_def)
      qed
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(7) Cons(8)
        using \<open>uniq Wl'\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>Some literal = getWatch1 state clause\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "l' \<noteq> ?w1" "l' \<noteq> ?w2" "\<not> literalFalse l' (elements (getM ?state'))"
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"
        let ?fState = "notifyWatches_loop literal Wl' newWl ?state''"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' \<noteq> ?w1\<close>
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          unfolding InvariantWatchesDiffer_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(4)
        have "InvariantConsistent (getM ?state'')"
          unfolding InvariantConsistent_def
          unfolding setWatch2_def
          unfolding swapWatches_def
          by simp
        moreover
        from Cons(5)
        have "InvariantUniq (getM ?state'')"
          unfolding InvariantUniq_def
          unfolding setWatch2_def
          unfolding swapWatches_def
          by simp
        moreover
        have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
        proof-
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww1 (elements M)"
              
            have "(\<exists>l. l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww1) M) \<or>
                  (\<forall>l. l el ((getF ?state'') ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                       literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww1) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(6)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding swapWatches_def
                unfolding setWatch2_def
                by simp
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
              
              have "\<not> (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(8)
                using \<open>l' \<noteq> ?w1\<close> and \<open>l' \<noteq> ?w2\<close> \<open>l' el (nth (getF ?state') clause)\<close>
                using \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
                using a and b
                using \<open>c = clause\<close>
                unfolding swapWatches_def
                unfolding setWatch2_def
                by auto
              moreover
              have "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> 
                elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(6)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>[THEN sym]
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                using \<open>literalFalse ww1 (elements M)\<close>
                using \<open>ww1 = ?w1\<close>
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
              ultimately
              show ?thesis
                using \<open>ww1 = ?w1\<close>
                using \<open>c = clause\<close>
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
            qed
          }
          moreover 
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww2 (elements M)"
            
            have "(\<exists>l. l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww2) M) \<or>
                  (\<forall>l. l el ((getF ?state'') ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                       literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww2) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(6)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding swapWatches_def
                unfolding setWatch2_def
                by auto
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
              with \<open>\<not> literalFalse l' (elements (getM ?state'))\<close> b
                Cons(8)
              have False
                unfolding swapWatches_def
                by simp
              thus ?thesis
                by simp
            qed
          }
          ultimately
          show ?thesis
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by blast
        qed
        moreover 
        have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
          using Cons(10)
          using \<open>clause \<notin> set Wl'\<close>
          using swapWatchesEffect[of "clause" "state"]
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state"
          "getF ?state'' = getF state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getWatch1 ?state'' clause = Some ?w1" "getWatch2 ?state'' clause = Some l'"
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        hence "getWatch1 ?fState clause = getWatch1 ?state'' clause \<and> getWatch2 ?fState clause = Some l'"
          using \<open>clause \<notin> set Wl'\<close>
          using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
          using Cons(7)
          using notifyWatchesLoopPreservedWatches[of "?state''" "Wl'" "literal" "newWl"]
          by (simp add: Let_def)
        moreover
        have "watchCharacterizationCondition ?w1 l' (getM ?fState) (getF ?fState ! clause) \<and>
          watchCharacterizationCondition l' ?w1 (getM ?fState) (getF ?fState ! clause)"
        proof-
          have "(getM ?fState) = (getM state)" "(getF ?fState) = (getF state)"
            using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "newWl"]
            using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
            using Cons(7)
            unfolding setWatch2_def
            unfolding swapWatches_def
            by (auto simp add: Let_def)
          
          have "literalFalse ?w1 (elements M) \<longrightarrow> 
            (\<exists> l. l el (nth (getF ?state'') clause) \<and> literalTrue l (elements M) \<and>  elementLevel l M \<le> elementLevel (opposite ?w1) M)"
          proof
            assume "literalFalse ?w1 (elements M)"
            show "\<exists> l. l el (nth (getF ?state'') clause) \<and> literalTrue l (elements M) \<and>  elementLevel l M \<le> elementLevel (opposite ?w1) M"
            proof-
              have "\<not> (\<forall> l. l el (nth (getF state) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using \<open>l' el (nth (getF ?state') clause)\<close> \<open>l' \<noteq> ?w1\<close> \<open>l' \<noteq> ?w2\<close> \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
                using Cons(8)
                unfolding swapWatches_def
                by auto

              from \<open>literalFalse ?w1 (elements M)\<close> Cons(6)
              have
                "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                 (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
                      literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ?w1) M)"
                using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>[THEN sym]
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding swapWatches_def
                by simp
              with \<open>\<not> (\<forall> l. l el (nth (getF state) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))\<close>
              have "\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M"
                by auto
              thus ?thesis
                unfolding setWatch2_def
                unfolding swapWatches_def
                by simp
            qed
          qed
          
          have "watchCharacterizationCondition l' ?w1 (getM ?fState) (getF ?fState ! clause)"
            using \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
            using \<open>getM ?fState = getM state\<close> 
            unfolding swapWatches_def
            unfolding watchCharacterizationCondition_def
            by simp
          moreover
          have "watchCharacterizationCondition ?w1 l' (getM ?fState) (getF ?fState ! clause)"
          proof (cases "literalFalse ?w1 (elements (getM ?fState))")
            case True
            hence "literalFalse ?w1 (elements M)"
              using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "newWl"]
              using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
              using Cons(7) Cons(8)
              using \<open>?w1 \<noteq> ?w2\<close> \<open>?w2 = literal\<close>
              unfolding setWatch2_def
              unfolding swapWatches_def
              by (simp add: Let_def)
            with \<open>literalFalse ?w1 (elements M) \<longrightarrow> 
              (\<exists> l. l el (nth (getF ?state'') clause) \<and> literalTrue l (elements M) \<and>  elementLevel l M \<le> elementLevel (opposite ?w1) M)\<close>
            obtain l::Literal
              where "l el (nth (getF ?state'') clause)" and 
              "literalTrue l (elements M)" and 
              "elementLevel l M \<le> elementLevel (opposite ?w1) M"
              by auto
            hence "elementLevel l (getM state) \<le> elementLevel (opposite ?w1) (getM state)"
              using Cons(8)
              using \<open>literalTrue l (elements M)\<close> \<open>literalFalse ?w1 (elements M)\<close>
              using elementLevelAppend[of "l" "M" "[(opposite literal, decision)]"]
              using elementLevelAppend[of "opposite ?w1" "M" "[(opposite literal, decision)]"]
              by auto
            thus ?thesis
              using \<open>l el (nth (getF ?state'') clause)\<close> \<open>literalTrue l (elements M)\<close>
              using \<open>getM ?fState = getM state\<close> \<open>getF ?fState = getF state\<close> \<open>getM ?state'' = getM state\<close> \<open>getF ?state'' = getF state\<close>
              using Cons(8)
              unfolding watchCharacterizationCondition_def
              by auto
          next
            case False
            thus ?thesis
              unfolding watchCharacterizationCondition_def
              by simp
          qed
          ultimately
          show ?thesis
            by simp
        qed
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(7) Cons(8)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using \<open>getWatch1 ?state'' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state'' clause = Some l'\<close>
          using Some
          using \<open>uniq Wl'\<close>
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          let ?fState = "notifyWatches_loop literal Wl' (clause # newWl) ?state''"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state')"
            unfolding InvariantConsistent_def
            unfolding swapWatches_def
            by simp
          moreover
          from Cons(5)
          have "InvariantUniq (getM ?state')"
            unfolding InvariantUniq_def
            unfolding swapWatches_def
            by simp
          moreover
          from Cons(6)
          have "InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') M"
            unfolding swapWatches_def
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by simp
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(10)
            using \<open>clause \<notin> set Wl'\<close>
            using swapWatchesEffect[of "clause" "state"]
            by simp
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            unfolding swapWatches_def
            by auto
          moreover
          have "getWatch1 ?fState clause = getWatch1 ?state'' clause \<and> getWatch2 ?fState clause = getWatch2 ?state'' clause"
            using \<open>clause \<notin> set Wl'\<close>
            using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
            using Cons(7)
            using notifyWatchesLoopPreservedWatches[of "?state''" "Wl'" "literal" "clause # newWl" ]
            by (simp add: Let_def)
          moreover
          have "literalFalse ?w1 (elements M)"
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
              \<open>?w1 \<noteq> ?w2\<close> \<open>?w2 = literal\<close> Cons(8)
            unfolding swapWatches_def
            by auto

          have "\<not> literalTrue ?w2 (elements M)"
            using Cons(4)
            using Cons(8)
            using \<open>?w2 = literal\<close>
            using inconsistentCharacterization[of "elements M @ [opposite literal]"]
            unfolding InvariantConsistent_def
            by force

          have *: "\<forall> l. l el (nth (getF state) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
            literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ?w1) M"
          proof-
            have "\<not> (\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements M))"
            proof
              assume "\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements M)"
              show "False"
              proof-
                from \<open>\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements M)\<close>
                obtain l 
                  where "l el (nth (getF state) clause)" "literalTrue l (elements M)"
                  by auto
                hence "l \<noteq> ?w1" "l \<noteq> ?w2"
                  using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
                  using \<open>\<not> literalTrue ?w2 (elements M)\<close>
                  unfolding swapWatches_def
                  using Cons(8)
                  by auto
                with \<open>l el (nth (getF state) clause)\<close>
                have "literalFalse l (elements (getM ?state'))"
                  using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                  using \<open>getWatch2 ?state' clause = Some ?w2\<close>
                  using None
                  using getNonWatchedUnfalsifiedLiteralNoneCharacterization[of "nth (getF ?state') clause" "?w1" "?w2" "getM ?state'"]
                  unfolding swapWatches_def
                  by simp
                with \<open>l \<noteq> ?w2\<close> \<open>?w2 = literal\<close> Cons(8)
                have "literalFalse l (elements M)"
                  unfolding swapWatches_def
                  by simp
                with Cons(4) \<open>literalTrue l (elements M)\<close>
                show ?thesis
                  unfolding InvariantConsistent_def
                  using Cons(8)
                  by (auto simp add: inconsistentCharacterization)
              qed
            qed
            with \<open>InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) M\<close>
            show ?thesis
              unfolding InvariantWatchCharacterization_def
              using \<open>literalFalse ?w1 (elements M)\<close>
              using \<open>getWatch1 ?state' clause = Some ?w1\<close>[THEN sym]
              using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
              using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
              unfolding watchCharacterizationCondition_def
              unfolding swapWatches_def
              by (simp) (blast)
          qed
          
          have **: "\<forall> l. l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
                      literalFalse l (elements (getM ?state'')) \<and> 
                      elementLevel (opposite l) (getM ?state'') \<le> elementLevel (opposite ?w1) (getM ?state'')"
          proof-
            {

              fix l::Literal
              assume "l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2"


              have "literalFalse l (elements (getM ?state'')) \<and> 
                    elementLevel (opposite l) (getM ?state'') \<le> elementLevel (opposite ?w1) (getM ?state'')"
              proof-
                from * \<open>l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2\<close>
                have "literalFalse l (elements M)" "elementLevel (opposite l) M \<le> elementLevel (opposite ?w1) M"
                  unfolding swapWatches_def
                  by auto
                thus ?thesis
                  using elementLevelAppend[of "opposite l" "M" "[(opposite literal, decision)]"]
                  using \<open>literalFalse ?w1 (elements M)\<close>
                  using elementLevelAppend[of "opposite ?w1" "M" "[(opposite literal, decision)]"]
                  using Cons(8)
                  unfolding swapWatches_def
                  by simp
              qed
            }
            thus ?thesis
              by simp
          qed

          have "(getM ?fState) = (getM state)" "(getF ?fState) = (getF state)"
            using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "clause # newWl"]
            using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
            using Cons(7)
            unfolding swapWatches_def
            by (auto simp add: Let_def)
          hence "\<forall> l. l el (nth (getF ?fState) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
                      literalFalse l (elements (getM ?fState)) \<and> 
                      elementLevel (opposite l) (getM ?fState) \<le> elementLevel (opposite ?w1) (getM ?fState)"
            using **
            using \<open>getM ?state'' = getM state\<close>
            using \<open>getF ?state'' = getF state\<close>
            by simp
          moreover
          have "\<forall> l. literalFalse l (elements (getM ?fState)) \<longrightarrow> 
                     elementLevel (opposite l) (getM ?fState) \<le> elementLevel (opposite ?w2) (getM ?fState)"
          proof-
            have "elementLevel (opposite ?w2) (getM ?fState) = currentLevel (getM ?fState)"
              using Cons(8)
              using \<open>(getM ?fState) = (getM state)\<close>
              using \<open>\<not> literalFalse ?w2 (elements M)\<close>
              using \<open>?w2 = literal\<close>
              using elementOnCurrentLevel[of "opposite ?w2" "M" "decision"]
              by simp
            thus ?thesis
              by (simp add: elementLevelLeqCurrentLevel)
          qed
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(7) Cons(8)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            unfolding watchCharacterizationCondition_def
            by (simp add: Let_def)
        next
          case False

          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          let ?fState = "notifyWatches_loop literal Wl' (clause # newWl) ?state''"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding setReason_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state'')"
            unfolding InvariantConsistent_def
            unfolding setReason_def
            unfolding swapWatches_def
            by simp
          moreover
          from Cons(5)
          have "InvariantUniq (getM ?state'')"
            unfolding InvariantUniq_def
            unfolding setReason_def
            unfolding swapWatches_def
            by simp
          moreover
          from Cons(6)
          have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
            unfolding swapWatches_def
            unfolding setReason_def
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by simp
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(10)
            using \<open>clause \<notin> set Wl'\<close>
            using swapWatchesEffect[of "clause" "state"]
            unfolding setReason_def
            by simp
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            unfolding setReason_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getWatch1 ?state'' clause = Some ?w1" "getWatch2 ?state'' clause = Some ?w2"
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            unfolding setReason_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getWatch1 ?fState clause = Some ?w1" "getWatch2 ?fState clause = Some ?w2"
            using \<open>getWatch1 ?state'' clause = Some ?w1\<close> \<open>getWatch2 ?state'' clause = Some ?w2\<close>
            using \<open>clause \<notin> set Wl'\<close>
            using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
            using Cons(7)
            using notifyWatchesLoopPreservedWatches[of "?state''" "Wl'" "literal" "clause # newWl" ]
            by (auto simp add: Let_def)
          moreover
          have "(getM ?fState) = (getM state)" "(getF ?fState) = (getF state)"
            using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "clause # newWl"]
            using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
            using Cons(7)
            unfolding setReason_def
            unfolding swapWatches_def
            by (auto simp add: Let_def)
          ultimately 
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> (\<forall>w1 w2. Some w1 = getWatch1 ?fState c \<and> Some w2 = getWatch2 ?fState c \<longrightarrow>
               watchCharacterizationCondition w1 w2 (getM ?fState) (getF ?fState ! c) \<and>
               watchCharacterizationCondition w2 w1 (getM ?fState) (getF ?fState ! c))" and
               "?fState = notifyWatches_loop literal (clause # Wl') newWl state"
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(7) Cons(8)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            by (auto simp add: Let_def)
          moreover
          have *: "\<forall> l. l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state''))"
            using None
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using getNonWatchedUnfalsifiedLiteralNoneCharacterization[of "nth (getF ?state') clause" "?w1" "?w2" "getM ?state'"]
            using Cons(8)
            unfolding setReason_def
            unfolding swapWatches_def
            by auto

          have**: "\<forall> l. l el (nth (getF ?fState) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?fState))"
            using \<open>(getM ?fState) = (getM state)\<close> \<open>(getF ?fState) = (getF state)\<close>
            using *
            using \<open>getM ?state'' = getM state\<close>
            using \<open>getF ?state'' = getF state\<close>
            unfolding swapWatches_def
            by auto

          have ***: "\<forall> l. literalFalse l (elements (getM ?fState)) \<longrightarrow> 
                     elementLevel (opposite l) (getM ?fState) \<le> elementLevel (opposite ?w2) (getM ?fState)"
          proof-
            have "elementLevel (opposite ?w2) (getM ?fState) = currentLevel (getM ?fState)"
              using Cons(8)
              using \<open>(getM ?fState) = (getM state)\<close>
              using \<open>\<not> literalFalse ?w2 (elements M)\<close>
              using \<open>?w2 = literal\<close>
              using elementOnCurrentLevel[of "opposite ?w2" "M" "decision"]
              by simp
            thus ?thesis
              by (simp add: elementLevelLeqCurrentLevel)
          qed

          have "(\<forall>w1 w2. Some w1 = getWatch1 ?fState clause \<and> Some w2 = getWatch2 ?fState clause \<longrightarrow>
            watchCharacterizationCondition w1 w2 (getM ?fState) (getF ?fState ! clause) \<and>
            watchCharacterizationCondition w2 w1 (getM ?fState) (getF ?fState ! clause))"
          proof-
            {
              fix w1 w2
              assume "Some w1 = getWatch1 ?fState clause \<and> Some w2 = getWatch2 ?fState clause"
              hence "w1 = ?w1" "w2 = ?w2"
                using \<open>getWatch1 ?fState clause = Some ?w1\<close>
                using \<open>getWatch2 ?fState clause = Some ?w2\<close>
                by auto
              hence "watchCharacterizationCondition w1 w2 (getM ?fState) (getF ?fState ! clause) \<and>
                watchCharacterizationCondition w2 w1 (getM ?fState) (getF ?fState ! clause)"
                unfolding watchCharacterizationCondition_def
                using ** ***
                unfolding watchCharacterizationCondition_def
                using \<open>(getM ?fState) = (getM state)\<close> \<open>(getF ?fState) = (getF state)\<close>
                using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
                unfolding swapWatches_def
                by simp
            }
            thus ?thesis
              by auto
          qed
          ultimately
          show ?thesis
            by simp
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch1 state clause = Some wa\<close>
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch2 state clause = Some wb\<close>
      by auto
    
    from \<open>\<not> Some literal = getWatch1 state clause\<close>
      \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)\<close>
    have "Some literal = getWatch2 state clause"
      by auto
    hence "?w2 = literal"
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      by simp
    hence "literalFalse ?w2 (elements (getM state))"
      using Cons(8)
      by simp

    from \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close>
    have "?w1 el (nth (getF state) clause)" "?w2 el (nth (getF state) clause)"
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
      unfolding InvariantWatchesEl_def
      by auto

    from \<open>InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)\<close>
    have "?w1 \<noteq> ?w2"
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
      unfolding InvariantWatchesDiffer_def
      by auto

    have "\<not> literalFalse ?w2 (elements M)"
      using \<open>?w2 = literal\<close>
      using Cons(5)
      using Cons(8)
      unfolding InvariantUniq_def
      by (simp add: uniqAppendIff)

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True

      let ?fState = "notifyWatches_loop literal Wl' (clause # newWl) ?state'"

      have "getWatch1 ?fState clause = getWatch1 ?state' clause \<and> getWatch2 ?fState clause = getWatch2 ?state' clause"
        using \<open>clause \<notin> set Wl'\<close>
        using Cons(2) 
        using Cons(7)
        using notifyWatchesLoopPreservedWatches[of "?state'" "Wl'" "literal" "clause # newWl" ]
        by (simp add: Let_def)
      moreover
      have "watchCharacterizationCondition ?w1 ?w2 (getM ?fState) (getF ?fState ! clause) \<and>
            watchCharacterizationCondition ?w2 ?w1 (getM ?fState) (getF ?fState ! clause)"
      proof-
        have "(getM ?fState) = (getM state) \<and> (getF ?fState = getF state)"
          using notifyWatchesLoopPreservedVariables[of "?state'" "Wl'" "literal" "clause # newWl"]
          using Cons(2)
          using Cons(7)
          by (simp add: Let_def)
        moreover
        have "\<not> literalFalse ?w1 (elements M)"
          using \<open>literalTrue ?w1 (elements (getM ?state'))\<close> \<open>?w1 \<noteq> ?w2\<close> \<open>?w2 = literal\<close>
          using Cons(4) Cons(8)
          unfolding InvariantConsistent_def
          by (auto simp add: inconsistentCharacterization)
        moreover 
        have "elementLevel (opposite ?w2) (getM ?state') = currentLevel (getM ?state')"
          using \<open>?w2 = literal\<close>
          using Cons(5) Cons(8)
          unfolding InvariantUniq_def
          by (auto simp add: uniqAppendIff elementOnCurrentLevel)
        ultimately
        show ?thesis
          using \<open>getWatch1 ?fState clause = getWatch1 ?state' clause \<and> getWatch2 ?fState clause = getWatch2 ?state' clause\<close>
          using \<open>?w2 = literal\<close> \<open>?w1 \<noteq> ?w2\<close>
          using \<open>?w1 el (nth (getF state) clause)\<close>
          using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
          unfolding watchCharacterizationCondition_def
          using elementLevelLeqCurrentLevel[of "?w1" "getM ?state'"]
          using notifyWatchesLoopPreservedVariables[of "?state'" "Wl'" "literal" "clause # newWl"]
          using \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close> 
          using Cons(7) 
          using Cons(8)
          by (auto simp add: Let_def)
      qed
      ultimately
      show ?thesis
        using assms
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6) Cons(7) Cons(8) Cons(9) Cons(10)
        using \<open>uniq Wl'\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>Some literal = getWatch2 state clause\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>?w1 \<noteq> ?w2\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "l' \<noteq> ?w1" "l' \<noteq> ?w2" "\<not> literalFalse l' (elements (getM ?state'))"
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"
        let ?fState = "notifyWatches_loop literal Wl' newWl ?state''"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' \<noteq> ?w1\<close>
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          unfolding InvariantWatchesDiffer_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(4)
        have "InvariantConsistent (getM ?state'')"
          unfolding InvariantConsistent_def
          unfolding setWatch2_def
          by simp
        moreover
        from Cons(5)
        have "InvariantUniq (getM ?state'')"
          unfolding InvariantUniq_def
          unfolding setWatch2_def
          by simp
        moreover
        have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
        proof-
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww1 (elements M)"
              
            have "(\<exists>l. l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww1) M) \<or>
                  (\<forall>l. l el ((getF ?state'') ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                        literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww1) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(6)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding setWatch2_def
                by simp
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                unfolding setWatch2_def
                by auto
              
              have "\<not> (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(8)
                using \<open>l' \<noteq> ?w1\<close> and \<open>l' \<noteq> ?w2\<close> \<open>l' el (nth (getF ?state') clause)\<close>
                using \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
                using a and b
                using \<open>c = clause\<close>
                unfolding setWatch2_def
                by auto
              moreover
              have "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> 
                elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(6)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>[THEN sym]
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                using \<open>literalFalse ww1 (elements M)\<close>
                using \<open>ww1 = ?w1\<close>
                unfolding setWatch2_def
                by auto
              ultimately
              show ?thesis
                using \<open>ww1 = ?w1\<close>
                using \<open>c = clause\<close>
                unfolding setWatch2_def
                by auto
            qed
          }
          moreover 
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww2 (elements M)"
            
            have "(\<exists>l. l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww2) M) \<or>
                  (\<forall>l. l el ((getF ?state'') ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                       literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww2) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(6)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding setWatch2_def
                by auto
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                unfolding setWatch2_def
                by auto
              with \<open>\<not> literalFalse l' (elements (getM ?state'))\<close> b
                Cons(8)
              have False
                by simp
              thus ?thesis
                by simp
            qed
          }
          ultimately
          show ?thesis
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by blast
        qed
        moreover
        have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
          using Cons(10)
          using \<open>clause \<notin> set Wl'\<close>
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state"
          "getF ?state'' = getF state"
          unfolding setWatch2_def
          by auto
        moreover
        have "getWatch1 ?state'' clause = Some ?w1" "getWatch2 ?state'' clause = Some l'"
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          unfolding setWatch2_def
          by auto
        hence "getWatch1 ?fState clause = getWatch1 ?state'' clause \<and> getWatch2 ?fState clause = Some l'"
          using \<open>clause \<notin> set Wl'\<close>
          using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
          using Cons(7)
          using notifyWatchesLoopPreservedWatches[of "?state''" "Wl'" "literal" "newWl"]
          by (simp add: Let_def)
        moreover
        have "watchCharacterizationCondition ?w1 l' (getM ?fState) (getF ?fState ! clause) \<and>
          watchCharacterizationCondition l' ?w1 (getM ?fState) (getF ?fState ! clause)"
        proof-
          have "(getM ?fState) = (getM state)" "(getF ?fState) = (getF state)"
            using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "newWl"]
            using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
            using Cons(7)
            unfolding setWatch2_def
            by (auto simp add: Let_def)
          
          have "literalFalse ?w1 (elements M) \<longrightarrow> 
            (\<exists> l. l el (nth (getF ?state'') clause) \<and> literalTrue l (elements M) \<and>  elementLevel l M \<le> elementLevel (opposite ?w1) M)"
          proof
            assume "literalFalse ?w1 (elements M)"
            show "\<exists> l. l el (nth (getF ?state'') clause) \<and> literalTrue l (elements M) \<and>  elementLevel l M \<le> elementLevel (opposite ?w1) M"
            proof-
              have "\<not> (\<forall> l. l el (nth (getF state) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using \<open>l' el (nth (getF ?state') clause)\<close> \<open>l' \<noteq> ?w1\<close> \<open>l' \<noteq> ?w2\<close> \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
                using Cons(8)
                unfolding swapWatches_def
                by auto

              from \<open>literalFalse ?w1 (elements M)\<close> Cons(6)
              have
                "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                 (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
                      literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ?w1) M)"
                using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>[THEN sym]
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                by simp
              with \<open>\<not> (\<forall> l. l el (nth (getF state) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))\<close>
              have "\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M"
                by auto
              thus ?thesis
                unfolding setWatch2_def
                by simp
            qed
          qed
          moreover
          have "watchCharacterizationCondition l' ?w1 (getM ?fState) (getF ?fState ! clause)"
            using \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
            using \<open>getM ?fState = getM state\<close> 
            unfolding watchCharacterizationCondition_def
            by simp
          moreover
          have "watchCharacterizationCondition ?w1 l' (getM ?fState) (getF ?fState ! clause)"
          proof (cases "literalFalse ?w1 (elements (getM ?fState))")
            case True
            hence "literalFalse ?w1 (elements M)"
              using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "newWl"]
              using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
              using Cons(7) Cons(8)
              using \<open>?w1 \<noteq> ?w2\<close> \<open>?w2 = literal\<close>
              unfolding setWatch2_def
              by (simp add: Let_def)
            with \<open>literalFalse ?w1 (elements M) \<longrightarrow> 
              (\<exists> l. l el (nth (getF ?state'') clause) \<and> literalTrue l (elements M) \<and>  elementLevel l M \<le> elementLevel (opposite ?w1) M)\<close>
            obtain l::Literal
              where "l el (nth (getF ?state'') clause)" and 
              "literalTrue l (elements M)" and 
              "elementLevel l M \<le> elementLevel (opposite ?w1) M"
              by auto
            hence "elementLevel l (getM state) \<le> elementLevel (opposite ?w1) (getM state)"
              using Cons(8)
              using \<open>literalTrue l (elements M)\<close> \<open>literalFalse ?w1 (elements M)\<close>
              using elementLevelAppend[of "l" "M" "[(opposite literal, decision)]"]
              using elementLevelAppend[of "opposite ?w1" "M" "[(opposite literal, decision)]"]
              by auto
            thus ?thesis
              using \<open>l el (nth (getF ?state'') clause)\<close> \<open>literalTrue l (elements M)\<close>
              using \<open>getM ?fState = getM state\<close> \<open>getF ?fState = getF state\<close> \<open>getM ?state'' = getM state\<close> \<open>getF ?state'' = getF state\<close>
              using Cons(8)
              unfolding watchCharacterizationCondition_def
              by auto
          next
            case False
            thus ?thesis
              unfolding watchCharacterizationCondition_def
              by simp
          qed
          ultimately
          show ?thesis
            by simp
        qed
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(7) Cons(8)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch2 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using \<open>getWatch1 ?state'' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state'' clause = Some l'\<close>
          using Some
          using \<open>uniq Wl'\<close>
          using \<open>?w1 \<noteq> ?w2\<close>
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          let ?fState = "notifyWatches_loop literal Wl' (clause # newWl) ?state''"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
            unfolding InvariantWatchesDiffer_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state')"
            unfolding InvariantConsistent_def
            by simp
          moreover
          from Cons(5)
          have "InvariantUniq (getM ?state')"
            unfolding InvariantUniq_def
            by simp
          moreover
          from Cons(6)
          have "InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') M"
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by simp
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(10)
            using \<open>clause \<notin> set Wl'\<close>
            by simp
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            by auto
          moreover
          have "getWatch1 ?fState clause = getWatch1 ?state'' clause \<and> getWatch2 ?fState clause = getWatch2 ?state'' clause"
            using \<open>clause \<notin> set Wl'\<close>
            using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
            using Cons(7)
            using notifyWatchesLoopPreservedWatches[of "?state''" "Wl'" "literal" "clause # newWl" ]
            by (simp add: Let_def)
          moreover
          have "literalFalse ?w1 (elements M)"
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
              \<open>?w1 \<noteq> ?w2\<close> \<open>?w2 = literal\<close> Cons(8)
            by auto

          have "\<not> literalTrue ?w2 (elements M)"
            using Cons(4)
            using Cons(8)
            using \<open>?w2 = literal\<close>
            using inconsistentCharacterization[of "elements M @ [opposite literal]"]
            unfolding InvariantConsistent_def
            by force

          have *: "\<forall> l. l el (nth (getF state) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
            literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ?w1) M"
          proof-
            have "\<not> (\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements M))"
            proof
              assume "\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements M)"
              show "False"
              proof-
                from \<open>\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements M)\<close>
                obtain l 
                  where "l el (nth (getF state) clause)" "literalTrue l (elements M)"
                  by auto
                hence "l \<noteq> ?w1" "l \<noteq> ?w2"
                  using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
                  using \<open>\<not> literalTrue ?w2 (elements M)\<close>
                  using Cons(8)
                  by auto
                with \<open>l el (nth (getF state) clause)\<close>
                have "literalFalse l (elements (getM ?state'))"
                  using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                  using \<open>getWatch2 ?state' clause = Some ?w2\<close>
                  using None
                  using getNonWatchedUnfalsifiedLiteralNoneCharacterization[of "nth (getF ?state') clause" "?w1" "?w2" "getM ?state'"]
                  by simp
                with \<open>l \<noteq> ?w2\<close> \<open>?w2 = literal\<close> Cons(8)
                have "literalFalse l (elements M)"
                  by simp
                with Cons(4) \<open>literalTrue l (elements M)\<close>
                show ?thesis
                  unfolding InvariantConsistent_def
                  using Cons(8)
                  by (auto simp add: inconsistentCharacterization)
              qed
            qed
            with \<open>InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) M\<close>
            show ?thesis
              unfolding InvariantWatchCharacterization_def
              using \<open>literalFalse ?w1 (elements M)\<close>
              using \<open>getWatch1 ?state' clause = Some ?w1\<close>[THEN sym]
              using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
              using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
              unfolding watchCharacterizationCondition_def
              by (simp) (blast)
          qed
          
          have **: "\<forall> l. l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
                      literalFalse l (elements (getM ?state'')) \<and> 
                      elementLevel (opposite l) (getM ?state'') \<le> elementLevel (opposite ?w1) (getM ?state'')"
          proof-
            {

              fix l::Literal
              assume "l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2"


              have "literalFalse l (elements (getM ?state'')) \<and> 
                    elementLevel (opposite l) (getM ?state'') \<le> elementLevel (opposite ?w1) (getM ?state'')"
              proof-
                from * \<open>l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2\<close>
                have "literalFalse l (elements M)" "elementLevel (opposite l) M \<le> elementLevel (opposite ?w1) M"
                  by auto
                thus ?thesis
                  using elementLevelAppend[of "opposite l" "M" "[(opposite literal, decision)]"]
                  using \<open>literalFalse ?w1 (elements M)\<close>
                  using elementLevelAppend[of "opposite ?w1" "M" "[(opposite literal, decision)]"]
                  using Cons(8)
                  by simp
              qed
            }
            thus ?thesis
              by simp
          qed

          have "(getM ?fState) = (getM state)" "(getF ?fState) = (getF state)"
            using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "clause # newWl"]
            using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
            using Cons(7)
            by (auto simp add: Let_def)
          hence "\<forall> l. l el (nth (getF ?fState) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
                      literalFalse l (elements (getM ?fState)) \<and> 
                      elementLevel (opposite l) (getM ?fState) \<le> elementLevel (opposite ?w1) (getM ?fState)"
            using **
            using \<open>getM ?state'' = getM state\<close>
            using \<open>getF ?state'' = getF state\<close>
            by simp
          moreover
          have "\<forall> l. literalFalse l (elements (getM ?fState)) \<longrightarrow> 
                     elementLevel (opposite l) (getM ?fState) \<le> elementLevel (opposite ?w2) (getM ?fState)"
          proof-
            have "elementLevel (opposite ?w2) (getM ?fState) = currentLevel (getM ?fState)"
              using Cons(8)
              using \<open>(getM ?fState) = (getM state)\<close>
              using \<open>\<not> literalFalse ?w2 (elements M)\<close>
              using \<open>?w2 = literal\<close>
              using elementOnCurrentLevel[of "opposite ?w2" "M" "decision"]
              by simp
            thus ?thesis
              by (simp add: elementLevelLeqCurrentLevel)
          qed
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(7) Cons(8)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch2 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            using \<open>?w1 \<noteq> ?w2\<close>
            unfolding watchCharacterizationCondition_def
            by (simp add: Let_def)
        next
          case False

          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          let ?fState = "notifyWatches_loop literal Wl' (clause # newWl) ?state''"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state'')"
            unfolding InvariantConsistent_def
            unfolding setReason_def
            by simp
          moreover
          from Cons(5)
          have "InvariantUniq (getM ?state'')"
            unfolding InvariantUniq_def
            unfolding setReason_def
            by simp
          moreover
          from Cons(6)
          have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
            unfolding setReason_def
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by simp
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(10)
            using \<open>clause \<notin> set Wl'\<close>
            unfolding setReason_def
            by simp
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            unfolding setReason_def
            by auto
          moreover
          have "getWatch1 ?state'' clause = Some ?w1" "getWatch2 ?state'' clause = Some ?w2"
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            unfolding setReason_def
            by auto
          moreover
          have "getWatch1 ?fState clause = Some ?w1" "getWatch2 ?fState clause = Some ?w2"
            using \<open>getWatch1 ?state'' clause = Some ?w1\<close> \<open>getWatch2 ?state'' clause = Some ?w2\<close>
            using \<open>clause \<notin> set Wl'\<close>
            using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
            using Cons(7)
            using notifyWatchesLoopPreservedWatches[of "?state''" "Wl'" "literal" "clause # newWl" ]
            by (auto simp add: Let_def)
          moreover
          have "(getM ?fState) = (getM state)" "(getF ?fState) = (getF state)"
            using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "clause # newWl"]
            using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close> \<open>getF ?state'' = getF state\<close>
            using Cons(7)
            unfolding setReason_def
            by (auto simp add: Let_def)
          ultimately 
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> (\<forall>w1 w2. Some w1 = getWatch1 ?fState c \<and> Some w2 = getWatch2 ?fState c \<longrightarrow>
               watchCharacterizationCondition w1 w2 (getM ?fState) (getF ?fState ! c) \<and>
               watchCharacterizationCondition w2 w1 (getM ?fState) (getF ?fState ! c))" and
               "?fState = notifyWatches_loop literal (clause # Wl') newWl state"
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(7) Cons(8)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch2 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            by (auto simp add: Let_def)
          moreover
          have *: "\<forall> l. l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state''))"
            using None
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using getNonWatchedUnfalsifiedLiteralNoneCharacterization[of "nth (getF ?state') clause" "?w1" "?w2" "getM ?state'"]
            using Cons(8)
            unfolding setReason_def
            by auto

          have**: "\<forall> l. l el (nth (getF ?fState) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?fState))"
            using \<open>(getM ?fState) = (getM state)\<close> \<open>(getF ?fState) = (getF state)\<close>
            using *
            using \<open>getM ?state'' = getM state\<close>
            using \<open>getF ?state'' = getF state\<close>
            by auto

          have ***: "\<forall> l. literalFalse l (elements (getM ?fState)) \<longrightarrow> 
                     elementLevel (opposite l) (getM ?fState) \<le> elementLevel (opposite ?w2) (getM ?fState)"
          proof-
            have "elementLevel (opposite ?w2) (getM ?fState) = currentLevel (getM ?fState)"
              using Cons(8)
              using \<open>(getM ?fState) = (getM state)\<close>
              using \<open>\<not> literalFalse ?w2 (elements M)\<close>
              using \<open>?w2 = literal\<close>
              using elementOnCurrentLevel[of "opposite ?w2" "M" "decision"]
              by simp
            thus ?thesis
              by (simp add: elementLevelLeqCurrentLevel)
          qed

          have "(\<forall>w1 w2. Some w1 = getWatch1 ?fState clause \<and> Some w2 = getWatch2 ?fState clause \<longrightarrow>
            watchCharacterizationCondition w1 w2 (getM ?fState) (getF ?fState ! clause) \<and>
            watchCharacterizationCondition w2 w1 (getM ?fState) (getF ?fState ! clause))"
          proof-
            {
              fix w1 w2
              assume "Some w1 = getWatch1 ?fState clause \<and> Some w2 = getWatch2 ?fState clause"
              hence "w1 = ?w1" "w2 = ?w2"
                using \<open>getWatch1 ?fState clause = Some ?w1\<close>
                using \<open>getWatch2 ?fState clause = Some ?w2\<close>
                by auto
              hence "watchCharacterizationCondition w1 w2 (getM ?fState) (getF ?fState ! clause) \<and>
                watchCharacterizationCondition w2 w1 (getM ?fState) (getF ?fState ! clause)"
                unfolding watchCharacterizationCondition_def
                using ** ***
                unfolding watchCharacterizationCondition_def
                using \<open>(getM ?fState) = (getM state)\<close> \<open>(getF ?fState) = (getF state)\<close>
                using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
                by simp
            }
            thus ?thesis
              by auto
          qed
          ultimately
          show ?thesis
            by simp
        qed
      qed
    qed
  qed
qed
  

lemma NotifyWatchesLoopConflictFlagEffect:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)" and
  "InvariantConsistent (getM state)"
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)"
  "literalFalse literal (elements (getM state))"
  "uniq Wl"
shows
  "let state' = notifyWatches_loop literal Wl newWl state in
     getConflictFlag state' = 
        (getConflictFlag state \<or> 
         (\<exists> clause. clause \<in> set Wl \<and> clauseFalse (nth (getF state) clause) (elements (getM state))))"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  
  from \<open>uniq (clause # Wl')\<close>
  have "uniq Wl'" and "clause \<notin> set Wl'"
    by (auto simp add: uniqAppendIff)

  from \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)\<close>
  have "0 \<le> clause" "clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto

    from \<open>Some literal = getWatch1 state clause\<close>
      \<open>getWatch2 ?state' clause = Some ?w2\<close>
    \<open>literalFalse literal (elements (getM state))\<close>
    have "literalFalse ?w2 (elements (getM state))"
      unfolding swapWatches_def
      by simp

    from \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close>
    have "?w1 el (nth (getF state) clause)"
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using \<open>clause < length (getF state)\<close>
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getF ?state' = getF state \<and> 
        getM ?state' = getM state \<and> 
        getConflictFlag ?state' = getConflictFlag state
        "
        unfolding swapWatches_def
        by simp
      moreover
      have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c"
        using Cons(5)
        unfolding swapWatches_def
        by auto
      moreover
      have "\<not> clauseFalse (nth (getF state) clause) (elements (getM state))"
        using \<open>?w1 el (nth (getF state) clause)\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>InvariantConsistent (getM state)\<close>
        unfolding InvariantConsistent_def
        unfolding swapWatches_def
          by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(3) Cons(4) Cons(6)
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>Some literal = getWatch1 state clause\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>uniq Wl'\<close>
        by (auto simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "\<not> literalFalse l' (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(4)
        have "InvariantConsistent (getM ?state'')"
          unfolding setWatch2_def
          unfolding swapWatches_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getConflictFlag ?state'' = getConflictFlag state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        moreover
        have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
          using Cons(5)
          using \<open>clause \<notin> set Wl'\<close>
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "\<not> clauseFalse (nth (getF state) clause) (elements (getM state))"
          using \<open>l' el (nth (getF ?state') clause)\<close> 
          using \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
          using \<open>InvariantConsistent (getM state)\<close>
          unfolding InvariantConsistent_def
          unfolding swapWatches_def
          by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(3) Cons(4) Cons(6)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using \<open>uniq Wl'\<close>
          using Some
          by (auto simp add: Let_def)
      next
        case None
        hence "\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralNoneCharacterization
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state'')"
            unfolding setWatch2_def
            unfolding swapWatches_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getSATFlag ?state'' = getSATFlag state"
            unfolding swapWatches_def
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(5)
            using \<open>clause \<notin> set Wl'\<close>
            unfolding swapWatches_def
            unfolding setWatch2_def
            by auto
          moreover
          have "clauseFalse (nth (getF state) clause) (elements (getM state))"
            using \<open>\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))\<close>
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>literalFalse ?w2 (elements (getM state))\<close>
            unfolding swapWatches_def
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3) Cons(4) Cons(6)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            by (auto simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state'')"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(5)
            using \<open>clause \<notin> set Wl'\<close>
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "\<not> clauseFalse (nth (getF state) clause) (elements (getM state))"
            using \<open>?w1 el (nth (getF state) clause)\<close>
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>InvariantConsistent (getM state)\<close>
            unfolding InvariantConsistent_def
          unfolding swapWatches_def
          by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)      
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3) Cons(4) Cons(6)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            apply (simp add: Let_def)
            unfolding setReason_def
            unfolding swapWatches_def
            by auto
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto

    from \<open>\<not> Some literal = getWatch1 state clause\<close>
      \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)\<close>
    have "Some literal = getWatch2 state clause"
      by auto
    hence "literalFalse ?w2 (elements (getM state))"
      using 
      \<open>getWatch2 ?state' clause = Some ?w2\<close>
      \<open>literalFalse literal (elements (getM state))\<close>
      by simp

    from \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close>
    have "?w1 el (nth (getF state) clause)"
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using \<open>clause < length (getF state)\<close>
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto
    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True

      have "\<not> clauseFalse (nth (getF state) clause) (elements (getM state))"
        using \<open>?w1 el (nth (getF state) clause)\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>InvariantConsistent (getM state)\<close>
        unfolding InvariantConsistent_def
        unfolding swapWatches_def
        by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)

      thus ?thesis
        using True
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6)
        using \<open>\<not> Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>uniq Wl'\<close>
        by (auto simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "\<not> literalFalse l' (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(4)
        have "InvariantConsistent (getM ?state'')"
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getConflictFlag ?state'' = getConflictFlag state"
          unfolding setWatch2_def
          by simp
        moreover
        have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
          using Cons(5)
          using \<open>clause \<notin> set Wl'\<close>
          unfolding setWatch2_def
          by auto
        moreover
        have "\<not> clauseFalse (nth (getF state) clause) (elements (getM state))"
          using \<open>l' el (nth (getF ?state') clause)\<close> 
          using \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
          using \<open>InvariantConsistent (getM state)\<close>
          unfolding InvariantConsistent_def
          by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(3) Cons(4) Cons(6)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>\<not> Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using \<open>uniq Wl'\<close>
          using Some
          by (auto simp add: Let_def)
      next
        case None
        hence "\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralNoneCharacterization
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state'')"
            unfolding setWatch2_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getSATFlag ?state'' = getSATFlag state"
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(5)
            using \<open>clause \<notin> set Wl'\<close>
            unfolding setWatch2_def
            by auto
          moreover
          have "clauseFalse (nth (getF state) clause) (elements (getM state))"
            using \<open>\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))\<close>
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>literalFalse ?w2 (elements (getM state))\<close>
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3) Cons(4) Cons(6)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            by (auto simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state'')"
            unfolding setReason_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state"
            unfolding setReason_def
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(5)
            using \<open>clause \<notin> set Wl'\<close>
            unfolding setReason_def
            by auto
          moreover
          have "\<not> clauseFalse (nth (getF state) clause) (elements (getM state))"
            using \<open>?w1 el (nth (getF state) clause)\<close>
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>InvariantConsistent (getM state)\<close>
            unfolding InvariantConsistent_def
          by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)      
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3) Cons(4) Cons(6)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            apply (simp add: Let_def)
            unfolding setReason_def
            by auto
        qed
      qed
    qed
  qed
qed


lemma NotifyWatchesLoopQEffect:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State
assumes 
  "(getM state) = M @ [(opposite literal, decision)]" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)" and
  "InvariantConsistent (getM state)" and
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)" and
  "uniq Wl" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) M"
shows
  "let state' = notifyWatches_loop literal Wl newWl state in
      ((\<forall> l. l \<in> (set (getQ state') - set (getQ state)) \<longrightarrow> 
            (\<exists> clause. (clause el (getF state) \<and>
                        literal el clause \<and>
                        (isUnitClause clause l (elements (getM state)))))) \<and>
      (\<forall> clause. clause \<in> set Wl \<longrightarrow> 
          (\<forall> l. (isUnitClause (nth (getF state) clause) l (elements (getM state))) \<longrightarrow> 
                     l \<in> (set (getQ state')))))" 
  (is "let state' = notifyWatches_loop literal Wl newWl state in (?Cond1 state' state \<and> ?Cond2 Wl state' state)")
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  
  from \<open>uniq (clause # Wl')\<close>
  have "uniq Wl'" and "clause \<notin> set Wl'"
    by (auto simp add: uniqAppendIff)

  from \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)\<close>
  have "0 \<le> clause" "clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto

  from \<open>0 \<le> clause\<close> \<open>clause < length (getF state)\<close>
  have "(nth (getF state) clause) el (getF state)"
    by simp

  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto

    have "?w2 = literal"
      using \<open>Some literal = getWatch1 state clause\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      unfolding swapWatches_def
      by simp
      
    hence "literalFalse ?w2 (elements (getM state))"
      using \<open>(getM state) = M @ [(opposite literal, decision)]\<close>
      by simp

    from \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close>
    have "?w1 el (nth (getF state) clause)" "?w2 el (nth (getF state) clause)"
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using \<open>clause < length (getF state)\<close>
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto

    from \<open>InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)\<close>
    have "?w1 \<noteq> ?w2"
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using \<open>clause < length (getF state)\<close>
      unfolding InvariantWatchesDiffer_def
      unfolding swapWatches_def
      by auto

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(3)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(4)
      have "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesDiffer_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getF ?state' = getF state \<and> 
        getM ?state' = getM state \<and> 
        getQ ?state' = getQ state \<and> 
        getConflictFlag ?state' = getConflictFlag state
        "
        unfolding swapWatches_def
        by simp
      moreover
      have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c"
        using Cons(7)
        unfolding swapWatches_def
        by auto
      moreover
      have "InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') M"
        using Cons(9)
        unfolding swapWatches_def
        unfolding InvariantWatchCharacterization_def
        by auto
      moreover
      have "\<not> (\<exists> l. isUnitClause (nth (getF state) clause) l (elements (getM state)))"
        using \<open>?w1 el (nth (getF state) clause)\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>InvariantConsistent (getM state)\<close>
        unfolding InvariantConsistent_def
        unfolding swapWatches_def
          by (auto simp add: isUnitClause_def inconsistentCharacterization)
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(5) Cons(6)
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>Some literal = getWatch1 state clause\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>uniq Wl'\<close>
        by ( simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "\<not> literalFalse l' (elements (getM ?state'))" "l' \<noteq> ?w1" "l' \<noteq> ?w2"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(3)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(4)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' \<noteq> ?w1\<close>
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          unfolding InvariantWatchesDiffer_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(6)
        have "InvariantConsistent (getM ?state'')"
          unfolding setWatch2_def
          unfolding swapWatches_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state \<and> 
          getConflictFlag ?state'' = getConflictFlag state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        moreover
        have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
          using Cons(7)
          using \<open>clause \<notin> set Wl'\<close>
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
        proof-
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww1 (elements M)"
              
            have "(\<exists>l. l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww1) M) \<or>
                  (\<forall>l. l el ((getF ?state'') ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                       literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww1) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(9)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding swapWatches_def
                unfolding setWatch2_def
                by simp
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
              
              have "\<not> (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(2)
                using \<open>l' \<noteq> ?w1\<close> and \<open>l' \<noteq> ?w2\<close> \<open>l' el (nth (getF ?state') clause)\<close>
                using \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
                using a and b
                using \<open>c = clause\<close>
                unfolding swapWatches_def
                unfolding setWatch2_def
                by auto
              moreover
              have "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> 
                elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(9)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                using \<open>clause < length (getF state)\<close>
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>[THEN sym]
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                using \<open>literalFalse ww1 (elements M)\<close>
                using \<open>ww1 = ?w1\<close>
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
              ultimately
              show ?thesis
                using \<open>ww1 = ?w1\<close>
                using \<open>c = clause\<close>
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
            qed
          }
          moreover 
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww2 (elements M)"
            
            have "(\<exists>l. l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww2) M) \<or>
                  (\<forall>l. l el ((getF ?state'') ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                       literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww2) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(9)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding swapWatches_def
                unfolding setWatch2_def
                by auto
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
              with \<open>\<not> literalFalse l' (elements (getM ?state'))\<close> b
                Cons(2)
              have False
                unfolding swapWatches_def
                by simp
              thus ?thesis
                by simp
            qed
          }
          ultimately
          show ?thesis
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by blast
        qed
        moreover
        have "\<not> (\<exists> l. isUnitClause (nth (getF state) clause) l (elements (getM state)))"
          (* Depends on the watch characterization invariant *)
        proof-
          {
            assume "\<not> ?thesis"
            then obtain l
              where "isUnitClause (nth (getF state) clause) l (elements (getM state))"
              by auto
            with \<open>l' el (nth (getF ?state') clause)\<close> \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
            have "l = l'"
              unfolding isUnitClause_def
              unfolding swapWatches_def
              by auto
            with \<open>l' \<noteq> ?w1\<close> have
              "literalFalse ?w1 (elements (getM ?state'))"
              using \<open>isUnitClause (nth (getF state) clause) l (elements (getM state))\<close>
              using \<open>?w1 el (nth (getF state) clause)\<close>
              unfolding isUnitClause_def
              unfolding swapWatches_def
              by simp
            with \<open>?w1 \<noteq> ?w2\<close> \<open>?w2 = literal\<close>
            Cons(2)
            have "literalFalse ?w1 (elements M)"
              unfolding swapWatches_def
              by simp

            from \<open>isUnitClause (nth (getF state) clause) l (elements (getM state))\<close>
              Cons(6)
            have "\<not> (\<exists> l. (l el (nth (getF state) clause) \<and> literalTrue l (elements (getM state))))"
              using containsTrueNotUnit[of _ "(nth (getF state) clause)" "elements (getM state)"]
              unfolding InvariantConsistent_def
              by auto

            from \<open>InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) M\<close>
            \<open>clause < length (getF state)\<close>
              \<open>literalFalse ?w1 (elements M)\<close> 
              \<open>getWatch1 ?state' clause = Some ?w1\<close> [THEN sym]
              \<open>getWatch2 ?state' clause = Some ?w2\<close> [THEN sym]
            have "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                  (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
              unfolding InvariantWatchCharacterization_def
              unfolding watchCharacterizationCondition_def
              unfolding swapWatches_def
              by auto
            with \<open>\<not> (\<exists> l. (l el (nth (getF state) clause) \<and> literalTrue l (elements (getM state))))\<close>
            Cons(2)
            have "(\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
              by auto
            with \<open>l' el (getF ?state' ! clause)\<close> \<open>l' \<noteq> ?w1\<close> \<open>l' \<noteq> ?w2\<close> \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
            Cons(2)
            have False
              unfolding swapWatches_def
              by simp
          }
          thus ?thesis
            by auto
        qed
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(2) Cons(5) Cons(6)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using \<open>uniq Wl'\<close>
          using Some
          by (simp add: Let_def)
      next
        case None
        hence "\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralNoneCharacterization
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(6)
          have "InvariantConsistent (getM ?state'')"
            unfolding swapWatches_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state \<and> 
          getSATFlag ?state'' = getSATFlag state"
            unfolding swapWatches_def
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(7)
            using \<open>clause \<notin> set Wl'\<close>
            unfolding swapWatches_def
            by auto
          moreover
          have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
            using Cons(9)
            unfolding swapWatches_def
            unfolding InvariantWatchCharacterization_def
            by auto
          moreover
          have "clauseFalse (nth (getF state) clause) (elements (getM state))"
            using \<open>\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))\<close>
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>literalFalse ?w2 (elements (getM state))\<close>
            unfolding swapWatches_def
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          hence "\<not> (\<exists> l. isUnitClause (nth (getF state) clause) l (elements (getM state)))"
            unfolding isUnitClause_def
            by (simp add: clauseFalseIffAllLiteralsAreFalse)
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(2) Cons(5) Cons(6)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(6)
          have "InvariantConsistent (getM ?state'')"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state \<and> 
            getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state @ [?w1]))"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(7)
            using \<open>clause \<notin> set Wl'\<close>
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
            using Cons(9)
            unfolding swapWatches_def
            unfolding setReason_def
            unfolding InvariantWatchCharacterization_def
            by auto
          ultimately
          have "let state' = notifyWatches_loop literal Wl' (clause # newWl) ?state'' in 
                   ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''"
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(2) Cons(5)
            using \<open>uniq Wl'\<close>
            by (simp add: Let_def)
          moreover
          have "notifyWatches_loop literal Wl' (clause # newWl) ?state'' = notifyWatches_loop literal (clause # Wl') newWl state"
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
          ultimately 
          have "let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                   ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''"
            by simp

          have "isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))"
            using \<open>\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))\<close>
            using \<open>?w1 el (nth (getF state) clause)\<close>
            using \<open>?w2 el (nth (getF state) clause)\<close>
            using \<open>literalFalse ?w2 (elements (getM state))\<close>
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            unfolding swapWatches_def
            unfolding isUnitClause_def
            by auto

          show ?thesis
          proof-
            {
              fix l::Literal
              assume "let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                l \<in> set (getQ state') - set (getQ state)"
              have "\<exists>clause. clause el (getF state) \<and> literal el clause \<and> isUnitClause clause l (elements (getM state))"
              proof (cases "l \<noteq> ?w1")
                case True
                hence "let state' = notifyWatches_loop literal (clause # Wl') newWl state in 
                   l \<in> set (getQ state') - set (getQ ?state'')"
                  using \<open>let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                    l \<in> set (getQ state') - set (getQ state)\<close>
                  unfolding setReason_def
                  unfolding swapWatches_def
                  by (simp add:Let_def)
                with \<open>let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                  ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''\<close>
                show ?thesis
                  unfolding setReason_def
                  unfolding swapWatches_def
                  by (simp add:Let_def del: notifyWatches_loop.simps)
              next
                case False
                thus ?thesis
                  using \<open>(nth (getF state) clause) el (getF state)\<close>
                        \<open>?w2 = literal\<close>
                        \<open>?w2 el (nth (getF state) clause)\<close>
                        \<open>isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))\<close>
                  by (auto simp add:Let_def)
              qed
            } 
            hence "let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                ?Cond1 state' state"
              by simp
            moreover
            {
              fix c
              assume "c \<in> set (clause # Wl')"
              have "let state' = notifyWatches_loop literal (clause # Wl') newWl state in 
                \<forall> l. isUnitClause (nth (getF state) c) l (elements (getM state)) \<longrightarrow> l \<in> set (getQ state')"
              proof (cases "c = clause")
                case True
                {
                  fix l::Literal
                  assume "isUnitClause (nth (getF state) c) l (elements (getM state))"
                  with \<open>isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))\<close> \<open>c = clause\<close>
                  have "l = ?w1"
                    unfolding isUnitClause_def
                    by auto
                  have "isPrefix (getQ ?state'') (getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state''))"
                    using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close>
                    using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "clause # newWl"]
                    using Cons(5)
                    unfolding swapWatches_def
                    unfolding setReason_def
                    by (simp add: Let_def)
                  hence "set (getQ ?state'') \<subseteq> set (getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state''))"
                    using prefixIsSubset[of "getQ ?state''" "getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state'')"]
                    by auto
                  hence "l \<in> set (getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state''))"
                    using \<open>l = ?w1\<close>
                    unfolding swapWatches_def
                    unfolding setReason_def
                  by auto
              } 
              thus ?thesis
                using \<open>notifyWatches_loop literal Wl' (clause # newWl) ?state'' = notifyWatches_loop literal (clause # Wl') newWl state\<close>
                by (simp add:Let_def)
            next
                case False
                hence "c \<in> set Wl'"
                  using \<open>c \<in> set (clause # Wl')\<close>
                  by simp
                {
                  fix l::Literal
                  assume "isUnitClause (nth (getF state) c) l (elements (getM state))"
                  hence "isUnitClause (nth (getF ?state'') c) l (elements (getM ?state''))"
                    unfolding setReason_def
                    unfolding swapWatches_def
                    by simp
                  with \<open>let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                    ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''\<close>
                    \<open>c \<in> set Wl'\<close>
                  have "let state' = notifyWatches_loop literal (clause # Wl') newWl state in l \<in> set (getQ state')"
                    by (simp add:Let_def)
                }
                thus ?thesis
                  by (simp add:Let_def)
              qed
            }
            hence "?Cond2 (clause # Wl') (notifyWatches_loop literal (clause # Wl') newWl state) state"
              by (simp add: Let_def)
            ultimately
            show ?thesis
              by (simp add:Let_def)
          qed
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto


    from \<open>\<not> Some literal = getWatch1 state clause\<close>
      \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)\<close>
    have "Some literal = getWatch2 state clause"
      by auto
    hence "?w2 = literal"
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      by simp
    hence "literalFalse ?w2 (elements (getM state))"
      using Cons(2)
      by simp

    from \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close>
    have "?w1 el (nth (getF state) clause)" "?w2 el (nth (getF state) clause)"
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using \<open>clause < length (getF state)\<close>
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto

    from \<open>InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)\<close>
    have "?w1 \<noteq> ?w2"
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using \<open>clause < length (getF state)\<close>
      unfolding InvariantWatchesDiffer_def
      unfolding swapWatches_def
      by auto
    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      have "\<not> (\<exists> l. isUnitClause (nth (getF state) clause) l (elements (getM state)))"
        using \<open>?w1 el (nth (getF state) clause)\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>InvariantConsistent (getM state)\<close>
        unfolding InvariantConsistent_def
        by (auto simp add: isUnitClause_def inconsistentCharacterization)
      thus ?thesis
        using True
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6) Cons(7) Cons(8) Cons(9)
        using \<open>\<not> Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>uniq Wl'\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "\<not> literalFalse l' (elements (getM ?state'))" "l' \<noteq> ?w1" "l' \<noteq> ?w2"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(3)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(4)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' \<noteq> ?w1\<close>
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          unfolding InvariantWatchesDiffer_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(6)
        have "InvariantConsistent (getM ?state'')"
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state \<and> 
          getConflictFlag ?state'' = getConflictFlag state"
          unfolding setWatch2_def
          by simp
        moreover
        have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
          using Cons(7)
          using \<open>clause \<notin> set Wl'\<close>
          unfolding setWatch2_def
          by auto
        moreover
        have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
        proof-
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww1 (elements M)"
              
            have "(\<exists>l.  l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww1) M) \<or>
              (\<forall>l. l el (getF ?state'' ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                   literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww1) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(9)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding setWatch2_def
                by auto
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                unfolding setWatch2_def
                by auto
              
              have "\<not> (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using \<open>l' \<noteq> ?w1\<close> and \<open>l' \<noteq> ?w2\<close> \<open>l' el (nth (getF ?state') clause)\<close>
                using \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
                using Cons(2)
                using a and b
                using \<open>c = clause\<close>
                unfolding setWatch2_def
                by auto
              moreover
              have "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                    (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(9)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                using \<open>clause < length (getF state)\<close>
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>[THEN sym]
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                using \<open>literalFalse ww1 (elements M)\<close>
                using \<open>ww1 = ?w1\<close>
                unfolding setWatch2_def
                by auto
              ultimately
              show ?thesis
                using \<open>ww1 = ?w1\<close>
                using \<open>c = clause\<close>
                unfolding setWatch2_def
                by auto
            qed
          }
          moreover 
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww2 (elements M)"
            
            have "(\<exists>l.  l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww2) M) \<or>
              (\<forall>l. l el (getF ?state'' ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                   literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww2) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(9)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding setWatch2_def
                by auto
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using \<open>getWatch1 ?state' clause = Some ?w1\<close>
                using \<open>getWatch2 ?state' clause = Some ?w2\<close>[THEN sym]
                unfolding setWatch2_def
                by auto
              with \<open>\<not> literalFalse l' (elements (getM ?state'))\<close> b
              Cons(2)
              have False
                unfolding setWatch2_def
                by simp
              thus ?thesis
                by simp
            qed
          }
          ultimately
          show ?thesis
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by blast
        qed
        moreover
        have "\<not> (\<exists> l. isUnitClause (nth (getF state) clause) l (elements (getM state)))"
          (* Depends on the watch characterization invariant *)
        proof-
          {
            assume "\<not> ?thesis"
            then obtain l
              where "isUnitClause (nth (getF state) clause) l (elements (getM state))"
              by auto
            with \<open>l' el (nth (getF ?state') clause)\<close> \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
            have "l = l'"
              unfolding isUnitClause_def
              by auto
            with \<open>l' \<noteq> ?w1\<close> have
              "literalFalse ?w1 (elements (getM ?state'))"
              using \<open>isUnitClause (nth (getF state) clause) l (elements (getM state))\<close>
              using \<open>?w1 el (nth (getF state) clause)\<close>
              unfolding isUnitClause_def
              by simp
            with \<open>?w1 \<noteq> ?w2\<close> \<open>?w2 = literal\<close>
            Cons(2)
            have "literalFalse ?w1 (elements M)"
              by simp

            from \<open>isUnitClause (nth (getF state) clause) l (elements (getM state))\<close>
              Cons(6)
            have "\<not> (\<exists> l. (l el (nth (getF state) clause) \<and> literalTrue l (elements (getM state))))"
              using containsTrueNotUnit[of _ "(nth (getF state) clause)" "elements (getM state)"]
              unfolding InvariantConsistent_def
              by auto

            from \<open>InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) M\<close>
            \<open>clause < length (getF state)\<close>
              \<open>literalFalse ?w1 (elements M)\<close> 
              \<open>getWatch1 ?state' clause = Some ?w1\<close> [THEN sym]
              \<open>getWatch2 ?state' clause = Some ?w2\<close> [THEN sym]
            have "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                  (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
              unfolding InvariantWatchCharacterization_def
              unfolding watchCharacterizationCondition_def
              unfolding swapWatches_def
              by auto
            with \<open>\<not> (\<exists> l. (l el (nth (getF state) clause) \<and> literalTrue l (elements (getM state))))\<close>
            Cons(2)
            have "(\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
              by auto
            with \<open>l' el (getF ?state' ! clause)\<close> \<open>l' \<noteq> ?w1\<close> \<open>l' \<noteq> ?w2\<close> \<open>\<not> literalFalse l' (elements (getM ?state'))\<close>
            Cons(2)
            have False
              unfolding swapWatches_def
              by simp
          }
          thus ?thesis
            by auto
        qed
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(2) Cons(5) Cons(7)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>\<not> Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using \<open>uniq Wl'\<close>
          using Some
          by (simp add: Let_def)
      next
        case None
        hence "\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralNoneCharacterization
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            by auto
          moreover
          from Cons(6)
          have "InvariantConsistent (getM ?state'')"
            unfolding setWatch2_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getSATFlag ?state'' = getSATFlag state"
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(7)
            using \<open>clause \<notin> set Wl'\<close>
            unfolding setWatch2_def
            by auto
          moreover
          have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
            using Cons(9)
            unfolding InvariantWatchCharacterization_def
            by auto
          moreover
          have "clauseFalse (nth (getF state) clause) (elements (getM state))"
            using \<open>\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))\<close>
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>literalFalse ?w2 (elements (getM state))\<close>
            unfolding swapWatches_def
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          hence "\<not> (\<exists> l. isUnitClause (nth (getF state) clause) l (elements (getM state)))"
            unfolding isUnitClause_def
            by (simp add: clauseFalseIffAllLiteralsAreFalse)
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(2) Cons(5) Cons(7)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(6)
          have "InvariantConsistent (getM ?state'')"
            unfolding setReason_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state"
            unfolding setReason_def
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(7)
            using \<open>clause \<notin> set Wl'\<close>
            unfolding setReason_def
            by auto
          moreover
          have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
            using Cons(9)
            unfolding InvariantWatchCharacterization_def
            unfolding setReason_def
            by auto
          ultimately
          have "let state' = notifyWatches_loop literal Wl' (clause # newWl) ?state'' in 
                   ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''"
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(2) Cons(5) Cons(6) Cons(7)
            using \<open>uniq Wl'\<close>
            by (simp add: Let_def)
          moreover
          have "notifyWatches_loop literal Wl' (clause # newWl) ?state'' = notifyWatches_loop literal (clause # Wl') newWl state"
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
          ultimately 
          have "let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                   ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''"
            by simp

          have "isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))"
            using \<open>\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))\<close>
            using \<open>?w1 el (nth (getF state) clause)\<close>
            using \<open>?w2 el (nth (getF state) clause)\<close>
            using \<open>literalFalse ?w2 (elements (getM state))\<close>
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            unfolding swapWatches_def
            unfolding isUnitClause_def
            by auto

          show ?thesis
          proof-
            {
              fix l::Literal
              assume "let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                l \<in> set (getQ state') - set (getQ state)"
              have "\<exists>clause. clause el (getF state) \<and> literal el clause \<and> isUnitClause clause l (elements (getM state))"
              proof (cases "l \<noteq> ?w1")
                case True
                hence "let state' = notifyWatches_loop literal (clause # Wl') newWl state in 
                   l \<in> set (getQ state') - set (getQ ?state'')"
                  using \<open>let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                    l \<in> set (getQ state') - set (getQ state)\<close>
                  unfolding setReason_def
                  unfolding swapWatches_def
                  by (simp add:Let_def)
                with \<open>let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                  ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''\<close>
                show ?thesis
                  unfolding setReason_def
                  unfolding swapWatches_def
                  by (simp add:Let_def del: notifyWatches_loop.simps)
              next
                case False
                thus ?thesis
                  using \<open>(nth (getF state) clause) el (getF state)\<close> \<open>isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))\<close>
                        \<open>?w2 = literal\<close>
                        \<open>?w2 el (nth (getF state) clause)\<close>
                  by (auto simp add:Let_def)
              qed
            } 
            hence "let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                ?Cond1 state' state"
              by simp
            moreover
            {
              fix c
              assume "c \<in> set (clause # Wl')"
              have "let state' = notifyWatches_loop literal (clause # Wl') newWl state in 
                \<forall> l. isUnitClause (nth (getF state) c) l (elements (getM state)) \<longrightarrow> l \<in> set (getQ state')"
              proof (cases "c = clause")
                case True
                {
                  fix l::Literal
                  assume "isUnitClause (nth (getF state) c) l (elements (getM state))"
                  with \<open>isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))\<close> \<open>c = clause\<close>
                  have "l = ?w1"
                    unfolding isUnitClause_def
                    by auto
                  have "isPrefix (getQ ?state'') (getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state''))"
                    using \<open>InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')\<close>
                    using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "clause # newWl"]
                    using Cons(5)
                    unfolding swapWatches_def
                    unfolding setReason_def
                    by (simp add: Let_def)
                  hence "set (getQ ?state'') \<subseteq> set (getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state''))"
                    using prefixIsSubset[of "getQ ?state''" "getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state'')"]
                    by auto
                  hence "l \<in> set (getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state''))"
                    using \<open>l = ?w1\<close>
                    unfolding swapWatches_def
                    unfolding setReason_def
                  by auto
              } 
              thus ?thesis
                using \<open>notifyWatches_loop literal Wl' (clause # newWl) ?state'' = notifyWatches_loop literal (clause # Wl') newWl state\<close>
                by (simp add:Let_def)
            next
                case False
                hence "c \<in> set Wl'"
                  using \<open>c \<in> set (clause # Wl')\<close>
                  by simp
                {
                  fix l::Literal
                  assume "isUnitClause (nth (getF state) c) l (elements (getM state))"
                  hence "isUnitClause (nth (getF ?state'') c) l (elements (getM ?state''))"
                    unfolding setReason_def
                    unfolding swapWatches_def
                    by simp
                  with \<open>let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                    ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''\<close>
                    \<open>c \<in> set Wl'\<close>
                  have "let state' = notifyWatches_loop literal (clause # Wl') newWl state in l \<in> set (getQ state')"
                    by (simp add:Let_def)
                }
                thus ?thesis
                  by (simp add:Let_def)
              qed
            }
            hence "?Cond2 (clause # Wl') (notifyWatches_loop literal (clause # Wl') newWl state) state"
              by (simp add: Let_def)
            ultimately
            show ?thesis
              by (simp add:Let_def)
          qed
        qed
      qed
    qed
  qed
qed

lemma InvariantUniqQAfterNotifyWatchesLoop:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)" and
  "InvariantUniqQ (getQ state)"
shows
  "let state' = notifyWatches_loop literal Wl newWl state in
       InvariantUniqQ (getQ state')
  " 
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  from \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)\<close>
  have "0 \<le> clause \<and> clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getM ?state' = getM state \<and> 
        getF ?state' = getF state \<and> 
        getQ ?state' = getQ state
        "
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(3) Cons(4)
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>Some literal = getWatch1 state clause\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(3) Cons(4)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
            getQ ?state'' = getQ state"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3) Cons(4)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            "getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "uniq (getQ ?state'')"
            using Cons(4)
            using \<open>getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])\<close>
            unfolding InvariantUniqQ_def
            by (simp add: uniqAppendIff)
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            unfolding isPrefix_def
            unfolding InvariantUniqQ_def
            by (simp add: Let_def split: if_split_asm)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch1 state clause = Some wa\<close>
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch2 state clause = Some wb\<close>
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons
        using \<open>\<not> Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state')) clause"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state')) clause\<close>
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''"]
          using Cons(3) Cons(4)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>\<not> Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getQ ?state'' = getQ state"
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3) Cons(4)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            "getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])"
            unfolding setReason_def
            by auto
          moreover
          have "uniq (getQ ?state'')"
            using Cons(4)
            using \<open>getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])\<close>
            unfolding InvariantUniqQ_def
            by (simp add: uniqAppendIff)
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            unfolding isPrefix_def
            unfolding InvariantUniqQ_def
            by (simp add: Let_def split: if_split_asm)
        qed
      qed
    qed
  qed
qed

lemma InvariantConflictClauseCharacterizationAfterNotifyWatches:
assumes 
  "(getM state) = M @ [(opposite literal, decision)]" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)" and
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)" and
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)"
  "uniq Wl"
shows 
  "let state' = (notifyWatches_loop literal Wl newWl state) in
   InvariantConflictClauseCharacterization (getConflictFlag state') (getConflictClause state') (getF state') (getM state')"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')

  from \<open>uniq (clause # Wl')\<close>
  have "clause \<notin> set Wl'" "uniq Wl'"
    by (auto simp add:uniqAppendIff)

  from \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)\<close>
  have "0 \<le> clause \<and> clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto

    with True have
      "?w2 = literal"
      unfolding swapWatches_def
      by simp
    hence "literalFalse ?w2 (elements (getM state))"
      using Cons(2)
      by simp

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(3)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c"
        using Cons(5)
        unfolding swapWatches_def
        by auto
      moreover
      have "getM ?state' = getM state \<and> 
        getF ?state' = getF state \<and> 
        getConflictFlag ?state' = getConflictFlag state \<and> 
        getConflictClause ?state' = getConflictClause state
        "
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(4) Cons(6) Cons(7)
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>Some literal = getWatch1 state clause\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>uniq Wl'\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(3)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
          using Cons(5)
          using \<open>clause \<notin> set Wl'\<close>
          using swapWatchesEffect[of "clause" "state"]
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getConflictFlag ?state'' = getConflictFlag state \<and> 
          getConflictClause ?state'' = getConflictClause state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(2) Cons(4) Cons(6) Cons(7)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          using \<open>uniq Wl'\<close>
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getConflictFlag ?state'' \<and> 
            getConflictClause ?state'' = clause"
            unfolding swapWatches_def
            by simp
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(5)
            using \<open>clause \<notin> set Wl'\<close>
            using swapWatchesEffect[of "clause" "state"]
            by simp
          moreover
          have "\<forall> l. l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state''))"
            using None
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using getNonWatchedUnfalsifiedLiteralNoneCharacterization[of "nth (getF ?state') clause" "?w1" "?w2" "getM ?state'"]
            unfolding setReason_def
            unfolding swapWatches_def
            by auto

          hence "clauseFalse (nth (getF state) clause) (elements (getM state))"
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>literalFalse ?w2 (elements (getM state))\<close>
            unfolding swapWatches_def
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          moreover
          have "(nth (getF state) clause) el (getF state)"
            using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
            using nth_mem[of "clause" "getF state"]
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(2) Cons(4) Cons(6) Cons(7)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
            unfolding InvariantConflictClauseCharacterization_def
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            "getConflictFlag ?state'' = getConflictFlag state"
            "getConflictClause ?state'' = getConflictClause state"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(5)
            using \<open>clause \<notin> set Wl'\<close>
            using swapWatchesEffect[of "clause" "state"]
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(2) Cons(4) Cons(6) Cons(7)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            by (simp add: Let_def)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch1 state clause = Some wa\<close>
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch2 state clause = Some wb\<close>
      by auto

    from \<open>\<not> Some literal = getWatch1 state clause\<close>
      \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)\<close>
    have "Some literal = getWatch2 state clause"
      by auto
    hence "?w2 = literal"
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      by simp
    hence "literalFalse ?w2 (elements (getM state))"
      using Cons(2)
      by simp

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6) Cons(7)
        using \<open>\<not> Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>uniq Wl'\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state')) clause"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(3)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state')) clause\<close>
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state \<and> 
          getConflictFlag ?state'' = getConflictFlag state \<and> 
          getConflictClause ?state'' = getConflictClause state"
          unfolding setWatch2_def
          by simp
        moreover
        have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
          using Cons(5)
          using \<open>clause \<notin> set Wl'\<close>
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(2) Cons(4) Cons(6) Cons(7)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>\<not> Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          using \<open>uniq Wl'\<close>
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getQ ?state'' = getQ state \<and> 
            getConflictFlag ?state'' \<and> 
            getConflictClause ?state'' = clause"
            by simp
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(5)
            using \<open>clause \<notin> set Wl'\<close>
            by simp
          moreover
          have "\<forall> l. l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state''))"
            using None
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using getNonWatchedUnfalsifiedLiteralNoneCharacterization[of "nth (getF ?state') clause" "?w1" "?w2" "getM ?state'"]
            unfolding setReason_def
            by auto
          hence "clauseFalse (nth (getF state) clause) (elements (getM state))"
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>literalFalse ?w2 (elements (getM state))\<close>
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          moreover
          have "(nth (getF state) clause) el (getF state)"
            using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
            using nth_mem[of "clause" "getF state"]
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(2) Cons(4) Cons(6) Cons(7)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
            unfolding InvariantConflictClauseCharacterization_def
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            "getConflictFlag ?state'' = getConflictFlag state"
            "getConflictClause ?state'' = getConflictClause state"
            unfolding setReason_def
            by auto
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(5)
            using \<open>clause \<notin> set Wl'\<close>
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(2) Cons(4) Cons(6) Cons(7)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            by (simp add: Let_def)
        qed
      qed
    qed
  qed
qed

lemma InvariantGetReasonIsReasonQSubset:
  assumes "Q \<subseteq> Q'" and
  "InvariantGetReasonIsReason GetReason F M Q'"
  shows
  "InvariantGetReasonIsReason GetReason F M Q"
using assms
unfolding InvariantGetReasonIsReason_def
by auto

lemma InvariantGetReasonIsReasonAfterNotifyWatches:
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)" and
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)" and
  "uniq Wl"
  "getM state = M @ [(opposite literal, decision)]"
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) Q"
shows
  "let state' = notifyWatches_loop literal Wl newWl state in
   let Q' = Q \<union> (set (getQ state') - set (getQ state)) in
     InvariantGetReasonIsReason (getReason state') (getF state') (getM state') Q'"
using assms
proof (induct Wl arbitrary: newWl state Q)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')

  from \<open>uniq (clause # Wl')\<close>
  have "clause \<notin> set Wl'" "uniq Wl'"
    by (auto simp add:uniqAppendIff)

  from \<open>\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)\<close>
  have "0 \<le> clause \<and> clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch2 state clause = Some wb\<close>
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch1 state clause = Some wa\<close>
      unfolding swapWatches_def
      by auto
    with True have
      "?w2 = literal"
      unfolding swapWatches_def
      by simp
    hence "literalFalse ?w2 (elements (getM state))"
      using Cons(6)
      by simp

    from \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close>
    have "?w1 el (nth (getF state) clause)" "?w2 el (nth (getF state) clause)"
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto 
      moreover
      have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c"
        using Cons(4)
        unfolding swapWatches_def
        by auto
      moreover
      have "getM ?state' = getM state \<and> 
        getF ?state' = getF state \<and> 
        getQ ?state' = getQ state \<and> 
        getReason ?state' = getReason state
        "
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "Q" "clause # newWl"]
        using Cons(3) Cons(6) Cons(7)
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>Some literal = getWatch1 state clause\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>uniq Wl'\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state') clause)\<close>
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
          using Cons(4)
          using \<open>clause \<notin> set Wl'\<close>
          using swapWatchesEffect[of "clause" "state"]
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state \<and> 
          getReason ?state'' = getReason state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "Q" "newWl"]
          using Cons(3) Cons(6) Cons(7)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using Some
          using \<open>uniq Wl'\<close>
          by (simp add: Let_def)
      next
        case None
        hence "\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralNoneCharacterization
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(4)
            unfolding swapWatches_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getQ ?state'' = getQ state \<and> 
            getReason ?state'' = getReason state"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "Q""clause # newWl"]
            using Cons(3) Cons(6) Cons(7)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          let ?state0 = "notifyWatches_loop literal Wl' (clause # newWl) ?state''"


          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            "getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])"
            "getReason ?state'' = (getReason state)(?w1 := Some clause)"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          hence "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(4)
            using \<open>clause \<notin> set Wl'\<close>
            using swapWatchesEffect[of "clause" "state"]
            unfolding setReason_def
            by simp
          moreover
          have "isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))"
            using \<open>\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))\<close>
            using \<open>?w1 el (nth (getF state) clause)\<close>
            using \<open>?w2 el (nth (getF state) clause)\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>literalFalse ?w2 (elements (getM state))\<close>
            unfolding swapWatches_def
            unfolding isUnitClause_def
            by auto
          hence "InvariantGetReasonIsReason (getReason ?state'') (getF ?state'') (getM ?state'') (Q \<union> {?w1})"
            using Cons(7)
            using \<open>getM ?state'' = getM state\<close>
            using \<open>getF ?state'' = getF state\<close>
            using \<open>getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])\<close>
            using \<open>getReason ?state'' = (getReason state)(?w1 := Some clause)\<close>
            using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using \<open>isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))\<close>
            unfolding swapWatches_def
            unfolding InvariantGetReasonIsReason_def
            by auto
          moreover
          have "(\<lambda>a. if a = ?w1 then Some clause else getReason state a) = getReason ?state''"
            unfolding setReason_def
            unfolding swapWatches_def
            by (auto simp add: fun_upd_def)
          ultimately
          have "InvariantGetReasonIsReason (getReason ?state0) (getF ?state0) (getM ?state0) 
                  (Q \<union> (set (getQ ?state0) - set (getQ ?state'')) \<union> {?w1})"
            using Cons(1)[of "?state''" "Q \<union> {?w1}" "clause # newWl"]
            using Cons(3) Cons(6) Cons(7)
            using \<open>uniq Wl'\<close>
            by (simp add: Let_def split: if_split_asm)
          moreover
          have "(Q \<union> (set (getQ ?state0) - set (getQ state))) \<subseteq> (Q \<union> (set (getQ ?state0) - set (getQ ?state'')) \<union> {?w1})"
            using \<open>getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])\<close>
            unfolding swapWatches_def
            by auto
          ultimately
          have "InvariantGetReasonIsReason (getReason ?state0) (getF ?state0) (getM ?state0) 
                  (Q \<union> (set (getQ ?state0) - set (getQ state)))"
            using InvariantGetReasonIsReasonQSubset[of "Q \<union> (set (getQ ?state0) - set (getQ state))" 
              "Q \<union> (set (getQ ?state0) - set (getQ ?state'')) \<union> {?w1}" "getReason ?state0" "getF ?state0" "getM ?state0"]
            by simp
          moreover
          have "notifyWatches_loop literal (clause # Wl') newWl state = ?state0"
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            by (simp add: Let_def)
          ultimately
          show ?thesis
            by simp
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using \<open>getWatch1 state clause = Some wa\<close>
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using \<open>getWatch2 state clause = Some wb\<close>
      by auto

    have "?w2 = literal"
      using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using Cons(4)
      using False
      by simp

    hence "literalFalse ?w2 (elements (getM state))"
      using Cons(6)
      by simp

    from \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close>
    have "?w1 el (nth (getF state) clause)" "?w2 el (nth (getF state) clause)"
      using \<open>getWatch1 ?state' clause = Some ?w1\<close>
      using \<open>getWatch2 ?state' clause = Some ?w2\<close>
      using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons(1)[of "state" "Q" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6) Cons(7)
        using \<open>\<not> Some literal = getWatch1 state clause\<close>
        using \<open>getWatch1 ?state' clause = Some ?w1\<close>
        using \<open>getWatch2 ?state' clause = Some ?w2\<close>
        using \<open>literalTrue ?w1 (elements (getM ?state'))\<close>
        using \<open>uniq Wl'\<close>
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state')) clause"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using \<open>l' el (nth (getF ?state')) clause\<close>
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
          using Cons(4)
          using \<open>clause \<notin> set Wl'\<close>
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state \<and> 
          getReason ?state'' = getReason state"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''"]
          using Cons(3) Cons(6) Cons(7)
          using \<open>getWatch1 ?state' clause = Some ?w1\<close>
          using \<open>getWatch2 ?state' clause = Some ?w2\<close>
          using \<open>\<not> Some literal = getWatch1 state clause\<close>
          using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
          using \<open>uniq Wl'\<close>
          using Some
          by (simp add: Let_def)
      next
        case None
        hence "\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralNoneCharacterization
          by simp

        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(4)
            using \<open>clause \<notin> set Wl'\<close>
            unfolding setWatch2_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getQ ?state'' = getQ state \<and> 
            getReason ?state'' = getReason state"
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3) Cons(6) Cons(7)
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          let ?state0 = "notifyWatches_loop literal Wl' (clause # newWl) ?state''"


          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            "getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])"
            "getReason ?state'' = (getReason state)(?w1 := Some clause)"
            unfolding setReason_def
            by auto
          moreover
          hence "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(4)
            using \<open>clause \<notin> set Wl'\<close>
            unfolding setReason_def
            by simp
          moreover
          have "isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))"
            using \<open>\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))\<close>
            using \<open>?w1 el (nth (getF state) clause)\<close>
            using \<open>?w2 el (nth (getF state) clause)\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>literalFalse ?w2 (elements (getM state))\<close>
            unfolding isUnitClause_def
            by auto
          hence "InvariantGetReasonIsReason (getReason ?state'') (getF ?state'') (getM ?state'') (Q \<union> {?w1})"
            using Cons(7)
            using \<open>getM ?state'' = getM state\<close>
            using \<open>getF ?state'' = getF state\<close>
            using \<open>getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])\<close>
            using \<open>getReason ?state'' = (getReason state)(?w1 := Some clause)\<close>
            using \<open>0 \<le> clause \<and> clause < length (getF state)\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using \<open>isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))\<close>
            unfolding InvariantGetReasonIsReason_def
            by auto
          moreover
          have "(\<lambda>a. if a = ?w1 then Some clause else getReason state a) = getReason ?state''"
            unfolding setReason_def
            by (auto simp add: fun_upd_def)
          ultimately
          have "InvariantGetReasonIsReason (getReason ?state0) (getF ?state0) (getM ?state0) 
                  (Q \<union> (set (getQ ?state0) - set (getQ ?state'')) \<union> {?w1})"
            using Cons(1)[of "?state''" "Q \<union> {?w1}" "clause # newWl"]
            using Cons(3) Cons(6) Cons(7)
            using \<open>uniq Wl'\<close>
            by (simp add: Let_def split: if_split_asm)
          moreover
          have "(Q \<union> (set (getQ ?state0) - set (getQ state))) \<subseteq> (Q \<union> (set (getQ ?state0) - set (getQ ?state'')) \<union> {?w1})"
            using \<open>getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])\<close>
            by auto
          ultimately
          have "InvariantGetReasonIsReason (getReason ?state0) (getF ?state0) (getM ?state0) 
                  (Q \<union> (set (getQ ?state0) - set (getQ state)))"
            using InvariantGetReasonIsReasonQSubset[of "Q \<union> (set (getQ ?state0) - set (getQ state))" 
              "Q \<union> (set (getQ ?state0) - set (getQ ?state'')) \<union> {?w1}" "getReason ?state0" "getF ?state0" "getM ?state0"]
            by simp
          moreover
          have "notifyWatches_loop literal (clause # Wl') newWl state = ?state0"
            using \<open>getWatch1 ?state' clause = Some ?w1\<close>
            using \<open>getWatch2 ?state' clause = Some ?w2\<close>
            using \<open>\<not> Some literal = getWatch1 state clause\<close>
            using \<open>\<not> literalTrue ?w1 (elements (getM ?state'))\<close>
            using None
            using \<open>\<not> literalFalse ?w1 (elements (getM ?state'))\<close>
            using \<open>uniq Wl'\<close>
            by (simp add: Let_def)
          ultimately
          show ?thesis
            by simp
        qed
      qed
    qed
  qed
qed


(****************************************************************************)
(*  A S S E R T   L I T E R A L                                             *)
(****************************************************************************)

lemma assertLiteralEffect:
fixes state::State and l::Literal and d::bool
assumes 
"InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
"InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
shows
"(getM (assertLiteral l d state)) = (getM state) @ [(l, d)]" and 
"(getF (assertLiteral l d state)) = (getF state)" and
"(getSATFlag (assertLiteral l d state)) = (getSATFlag state)" and
"isPrefix (getQ state) (getQ (assertLiteral l d state))"
using assms
unfolding assertLiteral_def
unfolding notifyWatches_def
unfolding InvariantWatchListsContainOnlyClausesFromF_def
using notifyWatchesLoopPreservedVariables[of "(state\<lparr>getM := getM state @ [(l, d)]\<rparr>)" "getWatchList (state\<lparr>getM := getM state @ [(l, d)]\<rparr>) (opposite l)"]
by (auto simp add: Let_def)

lemma WatchInvariantsAfterAssertLiteral:
assumes
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
shows
  "let state' = (assertLiteral literal decision state) in
     InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state') \<and> 
     InvariantWatchListsUniq (getWatchList state') \<and> 
     InvariantWatchListsCharacterization (getWatchList state') (getWatch1 state') (getWatch2 state') \<and> 
     InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state') \<and> 
     InvariantWatchesDiffer (getF state') (getWatch1 state') (getWatch2 state')
"
using assms
unfolding assertLiteral_def
unfolding notifyWatches_def
using InvariantWatchesElNotifyWatchesLoop[of "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>" "getWatchList state (opposite literal)" "opposite literal" "[]"]
using InvariantWatchesDifferNotifyWatchesLoop[of "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>" "getWatchList state (opposite literal)" "opposite literal" "[]"]
using InvariantWatchListsContainOnlyClausesFromFNotifyWatchesLoop[of "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>" "getWatchList state (opposite literal)" "[]" "opposite literal"]
using InvariantWatchListsCharacterizationNotifyWatchesLoop[of "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>" "(getWatchList (state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>) (opposite literal))" "opposite literal" "[]"]
unfolding InvariantWatchListsContainOnlyClausesFromF_def
unfolding InvariantWatchListsCharacterization_def
unfolding InvariantWatchListsUniq_def
by (auto simp add: Let_def)


lemma InvariantWatchCharacterizationAfterAssertLiteral:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])" and
  "InvariantUniq ((getM state) @ [(literal, decision)])" and
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
shows
  "let state' = (assertLiteral literal decision state) in
      InvariantWatchCharacterization (getF state') (getWatch1 state') (getWatch2 state') (getM state')"
proof-
  let ?state = "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
  let ?state' = "assertLiteral literal decision state"
  have *: "\<forall>c. c \<in> set (getWatchList ?state (opposite literal)) \<longrightarrow>
            (\<forall>w1 w2. Some w1 = getWatch1 ?state' c \<and> Some w2 = getWatch2 ?state' c \<longrightarrow>
                     watchCharacterizationCondition w1 w2 (getM ?state') (getF ?state' ! c) \<and>
                     watchCharacterizationCondition w2 w1 (getM ?state') (getF ?state' ! c))"
    using assms
    using NotifyWatchesLoopWatchCharacterizationEffect[of "?state" "getM state" "getWatchList ?state (opposite literal)" "opposite literal" "decision" "[]"]
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding InvariantWatchListsUniq_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    by (simp add: Let_def)
  {
    fix c
    assume "0 \<le> c" and "c < length (getF ?state')"
    fix w1::Literal and w2::Literal
    assume "Some w1 = getWatch1 ?state' c" "Some w2 = getWatch2 ?state' c"
    have "watchCharacterizationCondition w1 w2 (getM ?state') (getF ?state' ! c) \<and>
          watchCharacterizationCondition w2 w1 (getM ?state') (getF ?state' ! c)"
    proof (cases "c \<in> set (getWatchList ?state (opposite literal))")
      case True
      thus ?thesis
        using *
        using \<open>Some w1 = getWatch1 ?state' c\<close> \<open>Some w2 = getWatch2 ?state' c\<close>
        by auto
    next
      case False
      hence "Some (opposite literal) \<noteq> getWatch1 state c" and "Some (opposite literal) \<noteq> getWatch2 state c"
        using \<open>InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)\<close>
        unfolding InvariantWatchListsCharacterization_def
        by auto
      moreover
      from assms False
      have "getWatch1 ?state' c = getWatch1 state c" and "getWatch2 ?state' c = getWatch2 state c"
        using notifyWatchesLoopPreservedWatches[of "?state" "getWatchList ?state (opposite literal)" "opposite literal" "[]"]
        using False
        unfolding assertLiteral_def
        unfolding notifyWatches_def
        unfolding InvariantWatchListsContainOnlyClausesFromF_def
        by (auto simp add: Let_def)
      ultimately
      have "w1 \<noteq> opposite literal" "w2 \<noteq> opposite literal"
        using \<open>Some w1 = getWatch1 ?state' c\<close> and \<open>Some w2 = getWatch2 ?state' c\<close>
        by auto

      have "watchCharacterizationCondition w1 w2 (getM state) (getF state ! c)" and
           "watchCharacterizationCondition w2 w1 (getM state) (getF state ! c)"
        using \<open>InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)\<close>
        using \<open>Some w1 = getWatch1 ?state' c\<close> and \<open>Some w2 = getWatch2 ?state' c\<close>
        using \<open>getWatch1 ?state' c = getWatch1 state c\<close> and \<open>getWatch2 ?state' c = getWatch2 state c\<close>
        unfolding InvariantWatchCharacterization_def
        using \<open>c < length (getF ?state')\<close>
        using assms
        using assertLiteralEffect[of "state" "literal" "decision"]
        by auto

      have "watchCharacterizationCondition w1 w2 (getM ?state') ((getF ?state') ! c)"
      proof-
        {
          assume "literalFalse w1 (elements (getM ?state'))"
            with \<open>w1 \<noteq> opposite literal\<close>
            have "literalFalse w1 (elements (getM state))"
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            by simp
          with \<open>watchCharacterizationCondition w1 w2 (getM state) (getF state ! c)\<close>
          have "(\<exists> l. l el ((getF state) ! c) \<and> literalTrue l (elements (getM state))
            \<and> elementLevel l (getM state) \<le> elementLevel (opposite w1) (getM state)) \<or> 
            (\<forall>l. l el (getF state ! c) \<and> l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow>
            literalFalse l (elements (getM state)) \<and> 
            elementLevel (opposite l) (getM state) \<le> elementLevel (opposite w1) (getM state))" (is "?a state \<or> ?b state")
            unfolding watchCharacterizationCondition_def
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            using \<open>w1 \<noteq> opposite literal\<close>
            by simp
          have "?a ?state' \<or> ?b ?state'"
          proof (cases "?b state")
            case True
            show ?thesis
            proof-
              {
                fix l
                assume "l el (nth (getF ?state') c)" "l \<noteq> w1" "l \<noteq> w2"
                have "literalFalse l (elements (getM ?state')) \<and> 
                      elementLevel (opposite l) (getM ?state') \<le> elementLevel (opposite w1) (getM ?state')"
                proof-
                  from True \<open>l el (nth (getF ?state') c)\<close> \<open>l \<noteq> w1\<close> \<open>l \<noteq> w2\<close>
                  have "literalFalse l (elements (getM state))"
                    "elementLevel (opposite l) (getM state) \<le> elementLevel (opposite w1) (getM state)"
                    using assms 
                    using assertLiteralEffect[of "state" "literal" "decision"]
                    by auto
                  thus ?thesis
                    using \<open>literalFalse w1 (elements (getM state))\<close>
                    using elementLevelAppend[of "opposite w1" "getM state" "[(literal, decision)]"]
                    using elementLevelAppend[of "opposite l" "getM state" "[(literal, decision)]"]
                    using assms 
                    using assertLiteralEffect[of "state" "literal" "decision"]
                    by auto
                qed
              }
              thus ?thesis
                by simp
            qed
          next
            case False
            with \<open>?a state \<or> ?b state\<close>
            obtain l::Literal
              where "l el (getF state ! c)" "literalTrue l (elements (getM state))" 
              "elementLevel l (getM state) \<le> elementLevel (opposite w1) (getM state)"
              by auto
            
            from \<open>w1 \<noteq> opposite literal\<close>
              \<open>literalFalse w1 (elements (getM ?state'))\<close>
            have "elementLevel (opposite w1) ((getM state) @ [(literal, decision)]) = elementLevel (opposite w1) (getM state)"
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              unfolding elementLevel_def
              by (simp add: markedElementsToAppend)
            moreover
            from \<open>literalTrue l (elements (getM state))\<close>
            have "elementLevel l ((getM state) @ [(literal, decision)]) = elementLevel l (getM state)"
              unfolding elementLevel_def
              by (simp add: markedElementsToAppend)
            ultimately
            have "elementLevel l ((getM state) @ [(literal, decision)]) \<le> elementLevel (opposite w1) ((getM state) @ [(literal, decision)])"
              using \<open>elementLevel l (getM state) \<le> elementLevel (opposite w1) (getM state)\<close>
              by simp
            thus ?thesis
              using \<open>l el (getF state ! c)\<close> \<open>literalTrue l (elements (getM state))\<close>
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              by auto
          qed
        }
        thus ?thesis
          unfolding watchCharacterizationCondition_def
          by auto
      qed
      moreover
      have "watchCharacterizationCondition w2 w1 (getM ?state') ((getF ?state') ! c)"
      proof-
        {
          assume "literalFalse w2 (elements (getM ?state'))"
            with \<open>w2 \<noteq> opposite literal\<close>
            have "literalFalse w2 (elements (getM state))"
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            by simp
          with \<open>watchCharacterizationCondition w2 w1 (getM state) (getF state ! c)\<close>
          have "(\<exists> l. l el ((getF state) ! c) \<and> literalTrue l (elements (getM state))
            \<and> elementLevel l (getM state) \<le> elementLevel (opposite w2) (getM state)) \<or> 
            (\<forall>l. l el (getF state ! c) \<and> l \<noteq> w2 \<and> l \<noteq> w1 \<longrightarrow>
            literalFalse l (elements (getM state)) \<and> 
            elementLevel (opposite l) (getM state) \<le> elementLevel (opposite w2) (getM state))" (is "?a state \<or> ?b state")
            unfolding watchCharacterizationCondition_def
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            using \<open>w2 \<noteq> opposite literal\<close>
            by simp
          have "?a ?state' \<or> ?b ?state'"
          proof (cases "?b state")
            case True
            show ?thesis
            proof-
              {
                fix l
                assume "l el (nth (getF ?state') c)" "l \<noteq> w1" "l \<noteq> w2"
                have "literalFalse l (elements (getM ?state')) \<and> 
                      elementLevel (opposite l) (getM ?state') \<le> elementLevel (opposite w2) (getM ?state')"
                proof-
                  from True \<open>l el (nth (getF ?state') c)\<close> \<open>l \<noteq> w1\<close> \<open>l \<noteq> w2\<close>
                  have "literalFalse l (elements (getM state))"
                    "elementLevel (opposite l) (getM state) \<le> elementLevel (opposite w2) (getM state)"
                    using assms 
                    using assertLiteralEffect[of "state" "literal" "decision"]
                    by auto
                  thus ?thesis
                    using \<open>literalFalse w2 (elements (getM state))\<close>
                    using elementLevelAppend[of "opposite w2" "getM state" "[(literal, decision)]"]
                    using elementLevelAppend[of "opposite l" "getM state" "[(literal, decision)]"]
                    using assms 
                    using assertLiteralEffect[of "state" "literal" "decision"]
                    by auto
                qed
              }
              thus ?thesis
                by simp
            qed
          next
            case False
            with \<open>?a state \<or> ?b state\<close>
            obtain l::Literal
              where "l el (getF state ! c)" "literalTrue l (elements (getM state))" 
              "elementLevel l (getM state) \<le> elementLevel (opposite w2) (getM state)"
              by auto
            
            from \<open>w2 \<noteq> opposite literal\<close>
              \<open>literalFalse w2 (elements (getM ?state'))\<close>
            have "elementLevel (opposite w2) ((getM state) @ [(literal, decision)]) = elementLevel (opposite w2) (getM state)"
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              unfolding elementLevel_def
              by (simp add: markedElementsToAppend)
            moreover
            from \<open>literalTrue l (elements (getM state))\<close>
            have "elementLevel l ((getM state) @ [(literal, decision)]) = elementLevel l (getM state)"
              unfolding elementLevel_def
              by (simp add: markedElementsToAppend)
            ultimately
            have "elementLevel l ((getM state) @ [(literal, decision)]) \<le> elementLevel (opposite w2) ((getM state) @ [(literal, decision)])"
              using \<open>elementLevel l (getM state) \<le> elementLevel (opposite w2) (getM state)\<close>
              by simp
            thus ?thesis
              using \<open>l el (getF state ! c)\<close> \<open>literalTrue l (elements (getM state))\<close>
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              by auto
          qed
        }
        thus ?thesis
          unfolding watchCharacterizationCondition_def
          by auto
      qed
      ultimately
      show ?thesis
        by simp
    qed
  }
  thus ?thesis
    unfolding InvariantWatchCharacterization_def
    by (simp add: Let_def)
qed


lemma assertLiteralConflictFlagEffect:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantUniq ((getM state) @ [(literal, decision)])"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantWatchListsUniq (getWatchList state)"
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
shows
"let state' = assertLiteral literal decision state in
    getConflictFlag state' = (getConflictFlag state \<or> 
                                 (\<exists> clause. clause el (getF state) \<and> 
                                            opposite literal el clause \<and> 
                                            clauseFalse clause ((elements (getM state)) @ [literal])))"
proof-
  let ?state = "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
  let ?state' = "assertLiteral literal decision state"

  have "getConflictFlag ?state' = (getConflictFlag state \<or> 
          (\<exists> clause. clause \<in> set (getWatchList ?state (opposite literal)) \<and> 
                     clauseFalse (nth (getF ?state) clause) (elements (getM ?state))))"
    using NotifyWatchesLoopConflictFlagEffect[of "?state" 
      "getWatchList ?state (opposite literal)"
      "opposite literal" "[]"]
    using \<open>InvariantConsistent ((getM state) @ [(literal, decision)])\<close>
    using \<open>InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)\<close>
    using \<open>InvariantWatchListsUniq (getWatchList state)\<close>
    using \<open>InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)\<close>
    using \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close>
    unfolding InvariantWatchListsUniq_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    by (simp add: Let_def)
  moreover
  have "(\<exists> clause. clause \<in> set (getWatchList ?state (opposite literal)) \<and> 
                     clauseFalse (nth (getF ?state) clause) (elements (getM ?state))) = 
        (\<exists> clause. clause el (getF state) \<and> 
                     opposite literal el clause \<and> 
                     clauseFalse clause ((elements (getM state)) @ [literal]))" (is "?lhs = ?rhs")
  proof
    assume "?lhs"
    then obtain clause
      where "clause \<in> set (getWatchList ?state (opposite literal))" 
      "clauseFalse (nth (getF ?state) clause) (elements (getM ?state))"
      by auto

    have "getWatch1 ?state clause = Some (opposite literal) \<or> getWatch2 ?state clause = Some (opposite literal)"
      "clause < length (getF ?state)"
      "\<exists> w1 w2. getWatch1 ?state clause = Some w1 \<and> getWatch2 ?state clause = Some w2 \<and> 
      w1 el (nth (getF ?state) clause) \<and> w2 el (nth (getF ?state) clause)"
      using \<open>clause \<in> set (getWatchList ?state (opposite literal))\<close>
      using assms
      unfolding InvariantWatchListsContainOnlyClausesFromF_def
      unfolding InvariantWatchesEl_def
      unfolding InvariantWatchListsCharacterization_def
      by auto
    hence "(nth (getF ?state) clause) el (getF ?state)"
      "opposite literal el (nth (getF ?state) clause)"
      using nth_mem[of "clause" "getF ?state"]
      by auto
    thus "?rhs"
      using \<open>clauseFalse (nth (getF ?state) clause) (elements (getM ?state))\<close>
      by auto
  next
    assume "?rhs"
    then obtain clause
      where "clause el (getF ?state)" 
      "opposite literal el clause"
      "clauseFalse clause ((elements (getM state)) @ [literal])"
      by auto
    then obtain ci
      where "clause = (nth (getF ?state) ci)" "ci < length (getF ?state)"
      by (auto simp add: in_set_conv_nth)
    moreover
    from \<open>ci < length (getF ?state)\<close>
    obtain w1 w2
      where "getWatch1 state ci = Some w1" "getWatch2 state ci = Some w2" 
      "w1 el (nth (getF state) ci)" "w2 el (nth (getF state) ci)"
      using assms
      unfolding InvariantWatchesEl_def
      by auto
    have " getWatch1 state ci = Some (opposite literal) \<or> getWatch2 state ci = Some (opposite literal)"
    proof-
      {
        assume "\<not> ?thesis"
        with \<open>clauseFalse clause ((elements (getM state)) @ [literal])\<close>
          \<open>clause = (nth (getF ?state) ci)\<close>
          \<open>getWatch1 state ci = Some w1\<close> \<open>getWatch2 state ci = Some w2\<close>
          \<open>w1 el (nth (getF state) ci)\<close> \<open>w2 el (nth (getF state) ci)\<close>
        have "literalFalse w1 (elements (getM state))" "literalFalse w2 (elements (getM state))"
          by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
        

        
        from \<open>InvariantConsistent ((getM state) @ [(literal, decision)])\<close>
        \<open>clauseFalse clause ((elements (getM state)) @ [literal])\<close>
        have "\<not> (\<exists> l. l el clause \<and> literalTrue l (elements (getM state)))"
          unfolding InvariantConsistent_def
          by (auto simp add: inconsistentCharacterization clauseFalseIffAllLiteralsAreFalse)


        from \<open>InvariantUniq ((getM state) @ [(literal, decision)])\<close>
        have "\<not> literalTrue literal (elements (getM state))"
          unfolding InvariantUniq_def
          by (auto simp add: uniqAppendIff)
        
        from \<open>InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)\<close>
          \<open>literalFalse w1 (elements (getM state))\<close> \<open>literalFalse w2 (elements (getM state))\<close>
          \<open>\<not> (\<exists> l. l el clause \<and> literalTrue l (elements (getM state)))\<close>
          \<open>getWatch1 state ci = Some w1\<close>[THEN sym] 
          \<open>getWatch2 state ci = Some w2\<close>[THEN sym]
          \<open>ci < length (getF ?state)\<close>
          \<open>clause = (nth (getF ?state) ci)\<close>
        have "\<forall> l. l el clause \<and> l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow> literalFalse l (elements (getM state))"
          unfolding InvariantWatchCharacterization_def
          unfolding watchCharacterizationCondition_def
          by auto
        hence "literalTrue literal (elements (getM state))"
          using \<open>\<not> (getWatch1 state ci = Some (opposite literal) \<or> getWatch2 state ci = Some (opposite literal))\<close>
          using \<open>opposite literal el clause\<close>
          using \<open>getWatch1 state ci = Some w1\<close>
          using \<open>getWatch2 state ci = Some w2\<close>
          by auto
        with \<open>\<not> literalTrue literal (elements (getM state))\<close>
        have False
          by simp
      }
      thus ?thesis
        by auto
    qed
    ultimately
    show "?lhs"
      using assms
      using \<open>clauseFalse clause ((elements (getM state)) @ [literal])\<close>
      unfolding InvariantWatchListsCharacterization_def
      by force
  qed
  ultimately
  show ?thesis
    by auto
qed

lemma InvariantConflictFlagCharacterizationAfterAssertLiteral:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
shows
  "let state' = (assertLiteral literal decision state) in
      InvariantConflictFlagCharacterization (getConflictFlag state') (getF state') (getM state')"
proof-
  let ?state = "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
  let ?state' = "assertLiteral literal decision state"

  have *:"getConflictFlag ?state' = (getConflictFlag state \<or> 
          (\<exists> clause. clause \<in> set (getWatchList ?state (opposite literal)) \<and> 
                     clauseFalse (nth (getF ?state) clause) (elements (getM ?state))))"
    using NotifyWatchesLoopConflictFlagEffect[of "?state" 
      "getWatchList ?state (opposite literal)"
      "opposite literal" "[]"]
    using \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close>
    using \<open>InvariantConsistent ((getM state) @ [(literal, decision)])\<close>
    using \<open>InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)\<close>
    using \<open>InvariantWatchListsUniq (getWatchList state)\<close>
    using \<open>InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)\<close>
    unfolding InvariantWatchListsUniq_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    by (simp add: Let_def)

  hence "getConflictFlag state \<longrightarrow> getConflictFlag ?state'"
    by simp

  show ?thesis
  proof (cases "getConflictFlag state")
    case True
    thus ?thesis
      using \<open>InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)\<close>
      using assertLiteralEffect[of "state" "literal" "decision"]
      using \<open>getConflictFlag state \<longrightarrow> getConflictFlag ?state'\<close>
      using assms
      unfolding InvariantConflictFlagCharacterization_def
      by (auto simp add: Let_def formulaFalseAppendValuation)
  next
    case False
    
    hence "\<not> formulaFalse (getF state) (elements (getM state))"
      using \<open>InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)\<close>
      unfolding InvariantConflictFlagCharacterization_def
      by simp

    have **: "\<forall> clause. clause \<notin> set (getWatchList ?state (opposite literal)) \<and> 
                          0 \<le> clause \<and> clause < length (getF ?state) \<longrightarrow> 
                          \<not> clauseFalse (nth (getF ?state) clause) (elements (getM ?state))"
    proof-
      {
        fix clause
        assume "clause \<notin> set (getWatchList ?state (opposite literal))" and
          "0 \<le> clause \<and> clause < length (getF ?state)"

        from \<open>0 \<le> clause \<and> clause < length (getF ?state)\<close>
        obtain w1::Literal and w2::Literal
          where "getWatch1 ?state clause = Some w1" and
                "getWatch2 ?state clause = Some w2" and
                "w1 el (nth (getF ?state) clause)" and
                "w2 el (nth (getF ?state) clause)"
          using \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close>
          unfolding InvariantWatchesEl_def
          by auto

        have "\<not> clauseFalse (nth (getF ?state) clause) (elements (getM ?state))" 
        proof-
          from \<open>clause \<notin> set (getWatchList ?state (opposite literal))\<close>
          have "w1 \<noteq> opposite literal" and
               "w2 \<noteq> opposite literal"
            using \<open>InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)\<close>
            using \<open>getWatch1 ?state clause = Some w1\<close> and \<open>getWatch2 ?state clause = Some w2\<close>
            unfolding InvariantWatchListsCharacterization_def
            by auto

          from \<open>\<not> formulaFalse (getF state) (elements (getM state))\<close>
          have "\<not> clauseFalse (nth (getF ?state) clause) (elements (getM state))"
            using  \<open>0 \<le> clause \<and> clause < length (getF ?state)\<close>
            by (simp add: formulaFalseIffContainsFalseClause)
        
          
          show ?thesis
          proof (cases "literalFalse w1 (elements (getM state)) \<or> literalFalse w2 (elements (getM state))")
            case True
            (* Depends on the watch characterization invariant *)
            with \<open>InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)\<close>
            have $: "(\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements (getM state))) \<or> 
                  (\<forall> l. l el (nth (getF state) clause) \<and> 
                         l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow> literalFalse l (elements (getM state)))
              "
              using \<open>getWatch1 ?state clause = Some w1\<close>[THEN sym]
              using \<open>getWatch2 ?state clause = Some w2\<close>[THEN sym]
              using \<open>0 \<le> clause \<and> clause < length (getF ?state)\<close>
              unfolding InvariantWatchCharacterization_def
              unfolding watchCharacterizationCondition_def
              by auto

            thus ?thesis
            proof (cases "\<forall> l. l el (nth (getF state) clause) \<and> 
                            l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow> literalFalse l (elements (getM state))")
              case True
              have "\<not> literalFalse w1 (elements (getM state)) \<or> \<not> literalFalse w2 (elements (getM state))"
              proof-
                from \<open>\<not> clauseFalse (nth (getF ?state) clause) (elements (getM state))\<close>
                obtain l::Literal
                  where "l el (nth (getF ?state) clause)" and "\<not> literalFalse l (elements (getM state))"
                  by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
                with True
                show ?thesis
                  by auto
              qed
              hence "\<not> literalFalse w1 (elements (getM ?state)) \<or> \<not> literalFalse w2 (elements (getM ?state))"
                using \<open>w1 \<noteq> opposite literal\<close> and \<open>w2 \<noteq> opposite literal\<close>
                by auto
              thus ?thesis
                using \<open>w1 el (nth (getF ?state) clause)\<close> \<open>w2 el (nth (getF ?state) clause)\<close>
                by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
            next
              case False
              then obtain l::Literal
              where "l el (nth (getF state) clause)" and "literalTrue l (elements (getM state))"
                using $
                by auto
              thus ?thesis
                using \<open>InvariantConsistent ((getM state) @ [(literal, decision)])\<close>
                unfolding InvariantConsistent_def
                by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)
            qed
          next
            case False
            thus ?thesis
              using \<open>w1 el (nth (getF ?state) clause)\<close> and
                \<open>w1 \<noteq> opposite literal\<close>
              by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          qed
        qed
      } thus ?thesis
        by simp
    qed

    show ?thesis
    proof (cases "getConflictFlag ?state'")
      case True
      from \<open>\<not> getConflictFlag state\<close> \<open>getConflictFlag ?state'\<close>
      obtain clause::nat
        where
        "clause \<in> set (getWatchList ?state (opposite literal))" and
         "clauseFalse (nth (getF ?state) clause) (elements (getM ?state))"
        using *
        by auto
      from \<open>InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)\<close>
        \<open>clause \<in> set (getWatchList ?state (opposite literal))\<close>
      have "(nth (getF ?state) clause) el (getF ?state)"
        unfolding InvariantWatchListsContainOnlyClausesFromF_def
        using nth_mem
        by simp
      with \<open>clauseFalse (nth (getF ?state) clause) (elements (getM ?state))\<close> 
      have "formulaFalse (getF ?state) (elements (getM ?state))"
        by (auto simp add: Let_def formulaFalseIffContainsFalseClause)  
      thus ?thesis
        using \<open>\<not> getConflictFlag state\<close> \<open>getConflictFlag ?state'\<close>
        unfolding InvariantConflictFlagCharacterization_def
        using assms
        using assertLiteralEffect[of "state" "literal" "decision"]
        by (simp add: Let_def)
    next
      case False
      hence "\<forall> clause::nat. clause \<in> set (getWatchList ?state (opposite literal)) \<longrightarrow> 
        \<not> clauseFalse (nth (getF ?state) clause) (elements (getM ?state))"
        using *
        by auto
      with **
      have "\<forall> clause. 0 \<le> clause \<and> clause < length (getF ?state) \<longrightarrow> 
                          \<not> clauseFalse (nth (getF ?state) clause) (elements (getM ?state))"
        by auto
      hence "\<not> formulaFalse (getF ?state) (elements (getM ?state))"
        by (auto simp add:set_conv_nth formulaFalseIffContainsFalseClause)
      thus ?thesis
        using \<open>\<not> getConflictFlag state\<close> \<open>\<not> getConflictFlag ?state'\<close>
        using assms
        unfolding InvariantConflictFlagCharacterization_def
        by (auto simp add: Let_def assertLiteralEffect)
    qed
  qed
qed

lemma InvariantConflictClauseCharacterizationAfterAssertLiteral:
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchListsUniq (getWatchList state)"
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)"
shows 
  "let state' = assertLiteral literal decision state in
   InvariantConflictClauseCharacterization (getConflictFlag state') (getConflictClause state') (getF state') (getM state')"
proof-
  let ?state0 = "state\<lparr> getM := getM state @ [(literal, decision)]\<rparr>"
  show ?thesis
    using assms
    using InvariantConflictClauseCharacterizationAfterNotifyWatches[of "?state0" "getM state" "opposite literal" "decision" 
    "getWatchList ?state0 (opposite literal)" "[]"]
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    unfolding InvariantWatchListsUniq_def
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantConflictClauseCharacterization_def
    by (simp add: Let_def clauseFalseAppendValuation)
qed

lemma assertLiteralQEffect:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantUniq ((getM state) @ [(literal, decision)])"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantWatchListsUniq (getWatchList state)"
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
shows
"let state' = assertLiteral literal decision state in
    set (getQ state') = set (getQ state) \<union> 
           { ul. (\<exists> uc. uc el (getF state) \<and> 
                        opposite literal el uc \<and> 
                        isUnitClause uc ul ((elements (getM state)) @ [literal])) }" 
   (is "let state' = assertLiteral literal decision state in
    set (getQ state') = set (getQ state) \<union> ?ulSet")
proof-
    let ?state' = "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
    let ?state'' = "assertLiteral literal decision state"
    
    have "set (getQ ?state'') - set (getQ state) \<subseteq> ?ulSet"
      unfolding assertLiteral_def
      unfolding notifyWatches_def
      using assms
      using NotifyWatchesLoopQEffect[of "?state'" "getM state" "opposite literal" "decision" "getWatchList ?state' (opposite literal)" "[]"]
      unfolding InvariantWatchListsCharacterization_def
      unfolding InvariantWatchListsUniq_def
      unfolding InvariantWatchListsContainOnlyClausesFromF_def
      using set_conv_nth[of "getF state"]
      by (auto simp add: Let_def)
    moreover
    have "?ulSet \<subseteq> set (getQ ?state'')"
    proof
      fix ul
      assume "ul \<in> ?ulSet"
      then obtain uc
        where "uc el (getF state)" "opposite literal el uc" "isUnitClause uc ul ((elements (getM state)) @ [literal])"
        by auto
      then obtain uci
        where "uc = (nth (getF state) uci)" "uci < length (getF state)"
        using set_conv_nth[of "getF state"]
        by auto
      let ?w1 = "getWatch1 state uci"
      let ?w2 = "getWatch2 state uci"

      have "?w1 = Some (opposite literal) \<or> ?w2 = Some (opposite literal)"
      proof-
        {
          assume "\<not> ?thesis"
          
          from \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close>
          obtain wl1 wl2
            where "?w1 = Some wl1" "?w2 = Some wl2" "wl1 el (getF state ! uci)" "wl2 el (getF state ! uci)"
            unfolding InvariantWatchesEl_def
            using \<open>uci < length (getF state)\<close>
            by force

          with \<open>InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)\<close>
          have "watchCharacterizationCondition wl1 wl2 (getM state) (getF state ! uci)"
               "watchCharacterizationCondition wl2 wl1 (getM state) (getF state ! uci)"
            using \<open>uci < length (getF state)\<close>
            unfolding InvariantWatchCharacterization_def
            by auto

          from \<open>isUnitClause uc ul ((elements (getM state)) @ [literal])\<close>
          have "\<not> (\<exists> l. l el uc \<and> (literalTrue l ((elements (getM state)) @ [literal])))"
            using containsTrueNotUnit
            using \<open>InvariantConsistent ((getM state) @ [(literal, decision)])\<close>
            unfolding InvariantConsistent_def
            by auto
          
          from \<open>InvariantUniq ((getM state) @ [(literal, decision)])\<close>
          have "\<not> literal el (elements (getM state))"
            unfolding InvariantUniq_def
            by (simp add: uniqAppendIff)
        
          from \<open>\<not> ?thesis\<close> 
            \<open>?w1 = Some wl1\<close> \<open>?w2 = Some wl2\<close>
          have "wl1 \<noteq> opposite literal" "wl2 \<noteq> opposite literal"
            by auto

          from \<open>InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)\<close>
          have "wl1 \<noteq> wl2"
            using \<open>?w1 = Some wl1\<close> \<open>?w2 = Some wl2\<close>
            unfolding InvariantWatchesDiffer_def
            using \<open>uci < length (getF state)\<close>
            by auto
          
          have "literalFalse wl1 (elements (getM state)) \<or> literalFalse wl2 (elements (getM state))"
          proof (cases "ul = wl1")
            case True
            with \<open>wl1 \<noteq> wl2\<close>
            have "ul \<noteq> wl2"
              by simp
            with \<open>isUnitClause uc ul ((elements (getM state)) @ [literal])\<close>
              \<open>wl2 \<noteq> opposite literal\<close> \<open>wl2 el (getF state ! uci)\<close>
              \<open>uc = (getF state ! uci)\<close>
            show ?thesis
              unfolding isUnitClause_def
              by auto
          next
            case False
            with \<open>isUnitClause uc ul ((elements (getM state)) @ [literal])\<close>
              \<open>wl1 \<noteq> opposite literal\<close> \<open>wl1 el (getF state ! uci)\<close>
              \<open>uc = (getF state ! uci)\<close>
            show ?thesis
              unfolding isUnitClause_def
              by auto
          qed

          with  \<open>watchCharacterizationCondition wl1 wl2 (getM state) (getF state ! uci)\<close>
            \<open>watchCharacterizationCondition wl2 wl1 (getM state) (getF state ! uci)\<close>
            \<open>\<not> (\<exists> l. l el uc \<and> (literalTrue l ((elements (getM state)) @ [literal])))\<close>
            \<open>uc = (getF state ! uci)\<close>
            \<open>?w1 = Some wl1\<close> \<open>?w2 = Some wl2\<close>
          have "\<forall> l. l el uc \<and> l \<noteq> wl1 \<and> l \<noteq> wl2 \<longrightarrow> literalFalse l (elements (getM state))"
            unfolding watchCharacterizationCondition_def
            by auto
          with \<open>wl1 \<noteq> opposite literal\<close> \<open>wl2 \<noteq> opposite literal\<close> \<open>opposite literal el uc\<close>
          have "literalTrue literal (elements (getM state))"
            by auto
          with \<open>\<not> literal el (elements (getM state))\<close>
          have False
            by simp
        } thus ?thesis
          by auto
      qed
      with \<open>InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)\<close>
      have "uci \<in> set (getWatchList state (opposite literal))"
        unfolding InvariantWatchListsCharacterization_def
        by auto

      thus "ul \<in> set (getQ ?state'')"
        using \<open>uc el (getF state)\<close> 
        using \<open>isUnitClause uc ul ((elements (getM state)) @ [literal])\<close>
        using \<open>uc = (getF state ! uci)\<close>
        unfolding assertLiteral_def
        unfolding notifyWatches_def
        using assms
        using NotifyWatchesLoopQEffect[of "?state'" "getM state" "opposite literal" "decision" "getWatchList ?state' (opposite literal)" "[]"]
        unfolding InvariantWatchListsCharacterization_def
        unfolding InvariantWatchListsUniq_def
        unfolding InvariantWatchListsContainOnlyClausesFromF_def
        by (auto simp add: Let_def)
    qed
    moreover
    have "set (getQ state) \<subseteq> set (getQ ?state'')"
      using assms
      using assertLiteralEffect[of "state" "literal" "decision"]
      using prefixIsSubset[of "getQ state" "getQ ?state''"]
      by simp
    ultimately
    show ?thesis
      by (auto simp add: Let_def)
qed


lemma InvariantQCharacterizationAfterAssertLiteral:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
shows
  "let state' = (assertLiteral literal decision state) in
      InvariantQCharacterization (getConflictFlag state') (removeAll literal (getQ state')) (getF state') (getM state')"
proof-
  let ?state = "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
  let ?state' = "assertLiteral literal decision state"

  have *:"\<forall>l. l \<in> set (getQ ?state') - set (getQ ?state) \<longrightarrow>
            (\<exists>clause. clause el (getF ?state) \<and> isUnitClause clause l (elements (getM ?state)))"
    using NotifyWatchesLoopQEffect[of "?state" "getM state" "opposite literal" "decision"   "getWatchList ?state (opposite literal)" "[]"]
    using assms
    unfolding InvariantWatchListsUniq_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding InvariantWatchCharacterization_def
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    by (auto simp add: Let_def)

  have **: "\<forall> clause. clause \<in> set (getWatchList ?state (opposite literal)) \<longrightarrow> 
              (\<forall> l. (isUnitClause (nth (getF ?state) clause) l (elements (getM ?state))) \<longrightarrow> 
                      l \<in> (set (getQ ?state')))"
    using NotifyWatchesLoopQEffect[of "?state" "getM state" "opposite literal" "decision" "getWatchList ?state (opposite literal)" "[]"]
    using assms
    unfolding InvariantWatchListsUniq_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding InvariantWatchCharacterization_def
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    by (simp add: Let_def)

  have "getConflictFlag state \<longrightarrow> getConflictFlag ?state'"
  proof-
    have "getConflictFlag ?state' = (getConflictFlag state \<or> 
            (\<exists> clause. clause \<in> set (getWatchList ?state (opposite literal)) \<and> 
                       clauseFalse (nth (getF ?state) clause) (elements (getM ?state))))"
      using NotifyWatchesLoopConflictFlagEffect[of "?state" 
        "getWatchList ?state (opposite literal)"
        "opposite literal" "[]"]
      using assms
      unfolding InvariantWatchListsUniq_def
      unfolding InvariantWatchListsCharacterization_def
      unfolding InvariantWatchListsContainOnlyClausesFromF_def
      unfolding assertLiteral_def
      unfolding notifyWatches_def
      by (simp add: Let_def)
    thus ?thesis
      by simp
  qed

  {
    assume "\<not> getConflictFlag ?state'"
    with \<open>getConflictFlag state \<longrightarrow> getConflictFlag ?state'\<close>
    have "\<not> getConflictFlag state"
      by simp

    have "\<forall>l. l el (removeAll literal (getQ ?state')) =
             (\<exists>c. c el (getF ?state') \<and> isUnitClause c l (elements (getM ?state')))"
    proof
      fix l::Literal
      show "l el (removeAll literal (getQ ?state')) =
             (\<exists>c. c el (getF ?state') \<and> isUnitClause c l (elements (getM ?state')))"
      proof
        assume "l el (removeAll literal (getQ ?state'))"
        hence "l el (getQ ?state')" "l \<noteq> literal"
          by auto
        show "\<exists>c. c el (getF ?state') \<and> isUnitClause c l (elements (getM ?state'))"
        proof (cases "l el (getQ state)")
          case True
        
          from \<open>\<not> getConflictFlag state\<close>
            \<open>InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)\<close>
            \<open>l el (getQ state)\<close>
          obtain c::Clause
            where "c el (getF state)" "isUnitClause c l (elements (getM state))"
            unfolding InvariantQCharacterization_def
            by auto

          show ?thesis
          proof (cases "l \<noteq> opposite literal")
            case True
            hence "opposite l \<noteq> literal"
              by auto
            
            from \<open>isUnitClause c l (elements (getM state))\<close>
              \<open>opposite l \<noteq> literal\<close> \<open>l \<noteq> literal\<close>
            have "isUnitClause c l ((elements (getM state) @ [literal]))"
              using isUnitClauseAppendValuation[of "c" "l" "elements (getM state)" "literal"]
              by simp
            thus ?thesis
              using assms
              using \<open>c el (getF state)\<close>
              using assertLiteralEffect[of "state" "literal" "decision"]
              by auto
          next
            case False
            hence "opposite l = literal"
              by simp

            from \<open>isUnitClause c l (elements (getM state))\<close>
            have "clauseFalse c (elements (getM ?state'))"
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              using unitBecomesFalse[of "c" "l" "elements (getM state)"]
              using \<open>opposite l = literal\<close>
              by simp
            with \<open>c el (getF state)\<close>
            have "formulaFalse (getF state) (elements (getM ?state'))"
              by (auto simp add: formulaFalseIffContainsFalseClause)
                
            from assms
            have "InvariantConflictFlagCharacterization (getConflictFlag ?state') (getF ?state') (getM ?state')"
              using InvariantConflictFlagCharacterizationAfterAssertLiteral
              by (simp add: Let_def)
            with \<open>formulaFalse (getF state) (elements (getM ?state'))\<close>
            have "getConflictFlag ?state'"
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              unfolding InvariantConflictFlagCharacterization_def
              by auto
            with \<open>\<not> getConflictFlag ?state'\<close>
            show ?thesis
              by simp
          qed
        next
          case False
          then obtain c::Clause
            where "c el (getF ?state') \<and> isUnitClause c l (elements (getM ?state'))"
            using *
            using \<open>l el (getQ ?state')\<close>
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            by auto
          thus ?thesis
            using formulaEntailsItsClauses[of "c" "getF ?state'"]
            by auto
          qed
      next
        assume "\<exists>c. c el (getF ?state') \<and> isUnitClause c l (elements (getM ?state'))"
        then obtain c::Clause
          where "c el (getF ?state')" "isUnitClause c l (elements (getM ?state'))"
          by auto
        then obtain ci::nat
          where "0 \<le> ci" "ci < length (getF ?state')" "c = (nth (getF ?state') ci)"
          using set_conv_nth[of "getF ?state'"]
          by auto
        then obtain w1::Literal and w2::Literal
          where "getWatch1 state ci = Some w1" and "getWatch2 state ci = Some w2" and 
          "w1 el c" and "w2 el c"
          using \<open>InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)\<close> 
          using \<open>c = (nth (getF ?state') ci)\<close>
          unfolding InvariantWatchesEl_def
          using assms
          using assertLiteralEffect[of "state" "literal" "decision"]
          by auto
        hence "w1 \<noteq> w2"
          using \<open>ci < length (getF ?state')\<close>
          using \<open>InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)\<close>
          unfolding InvariantWatchesDiffer_def
          using assms
          using assertLiteralEffect[of "state" "literal" "decision"]
          by auto

        show "l el (removeAll literal (getQ ?state'))"
        proof (cases "isUnitClause c l (elements (getM state))")
          case True
          with \<open>InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)\<close>
            \<open>\<not> getConflictFlag state\<close>
            \<open>c el (getF ?state')\<close> 
          have "l el (getQ state)"
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            unfolding InvariantQCharacterization_def
            by auto
          have "isPrefix (getQ state) (getQ ?state')"
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            by simp
          then obtain Q' 
            where "(getQ state) @ Q' = (getQ ?state')"
            unfolding isPrefix_def
            by auto
          have "l el (getQ ?state')"
            using \<open>l el (getQ state)\<close>
            \<open>(getQ state) @ Q' = (getQ ?state')\<close>[THEN sym]
            by simp
          moreover
          have "l \<noteq> literal"
            using \<open>isUnitClause c l (elements (getM ?state'))\<close>
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            unfolding isUnitClause_def
            by simp
          ultimately
          show ?thesis
            by auto
        next
          case False
            (* The clause was not unit in M but it became unit in M' *)
          thus ?thesis
          proof (cases "ci \<in> set (getWatchList ?state (opposite literal))")
            case True
            with ** 
              \<open>isUnitClause c l (elements (getM ?state'))\<close>
              \<open>c = (nth (getF ?state') ci)\<close>
            have "l \<in> set (getQ ?state')"
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              by simp
            moreover
            have "l \<noteq> literal"
              using \<open>isUnitClause c l (elements (getM ?state'))\<close>
              unfolding isUnitClause_def
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              by simp
            ultimately
            show ?thesis
              by simp
          next
            case False
            with \<open>InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)\<close>
            have "w1 \<noteq> opposite literal" "w2 \<noteq> opposite literal"
              using \<open>getWatch1 state ci = Some w1\<close> and \<open>getWatch2 state ci = Some w2\<close>
              unfolding InvariantWatchListsCharacterization_def
              by auto
            have "literalFalse w1 (elements (getM state)) \<or> literalFalse w2 (elements (getM state))"
            proof-
              {
                assume "\<not> ?thesis"
                hence "\<not> literalFalse w1 (elements (getM ?state'))" "\<not> literalFalse w2 (elements (getM ?state'))"
                  using \<open>w1 \<noteq> opposite literal\<close> and \<open>w2 \<noteq> opposite literal\<close>
                  using assms
                  using assertLiteralEffect[of "state" "literal" "decision"]
                  by auto
                with \<open>w1 \<noteq> w2\<close> \<open>w1 el c\<close> \<open>w2 el c\<close>
                have  "\<not> isUnitClause c l (elements (getM ?state'))"
                  unfolding isUnitClause_def
                  by auto
              }
              with \<open>isUnitClause c l (elements (getM ?state'))\<close>
              show ?thesis
                by auto
            qed
                (* Depends on the watch characterization invariant *)
            with \<open>InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)\<close>
            have $: "(\<exists> l. l el c \<and> literalTrue l (elements (getM state))) \<or> 
                     (\<forall> l. l el c \<and> 
                         l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow> literalFalse l (elements (getM state)))
              "
              using \<open>ci < length (getF ?state')\<close>
              using \<open>c = (nth (getF ?state') ci)\<close>
              using \<open>getWatch1 state ci = Some w1\<close>[THEN sym] and \<open>getWatch2 state ci = Some w2\<close>[THEN sym]
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              unfolding InvariantWatchCharacterization_def
              unfolding watchCharacterizationCondition_def
              by auto
            thus ?thesis
            proof(cases "\<forall> l. l el c \<and> l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow> literalFalse l (elements (getM state))")
              case True
              with \<open>isUnitClause c l (elements (getM ?state'))\<close>
              have "literalFalse w1 (elements (getM state)) \<longrightarrow> 
                      \<not> literalFalse w2 (elements (getM state)) \<and> \<not> literalTrue w2 (elements (getM state)) \<and> l = w2"
                   "literalFalse w2 (elements (getM state)) \<longrightarrow> 
                      \<not> literalFalse w1 (elements (getM state)) \<and> \<not> literalTrue w1 (elements (getM state)) \<and> l = w1"
                unfolding isUnitClause_def
                using assms
                using assertLiteralEffect[of "state" "literal" "decision"]
                by auto
              
              with \<open>literalFalse w1 (elements (getM state)) \<or> literalFalse w2 (elements (getM state))\<close>
              have "(literalFalse w1 (elements (getM state)) \<and> \<not> literalFalse w2 (elements (getM state)) \<and> \<not> literalTrue w2 (elements (getM state)) \<and> l = w2) \<or> 
                    (literalFalse w2 (elements (getM state)) \<and> \<not> literalFalse w1 (elements (getM state)) \<and> \<not> literalTrue w1 (elements (getM state)) \<and> l = w1)"
                by blast
              hence "isUnitClause c l (elements (getM state))"
                using \<open>w1 el c\<close> \<open>w2 el c\<close> True
                unfolding isUnitClause_def
                by auto
              thus ?thesis
                using \<open>\<not> isUnitClause c l (elements (getM state))\<close>
                by simp
            next
              case False
              then obtain l'::Literal where 
                "l' el c" "literalTrue l' (elements (getM state))"
                using $
                by auto
              hence "literalTrue l' (elements (getM ?state'))"
                using assms
                using assertLiteralEffect[of "state" "literal" "decision"]
                by auto
              
              from \<open>InvariantConsistent ((getM state) @ [(literal, decision)])\<close>
                \<open>l' el c\<close> \<open>literalTrue l' (elements (getM ?state'))\<close>
              show ?thesis
                using containsTrueNotUnit[of "l'" "c" "elements (getM ?state')"]
                using \<open>isUnitClause c l (elements (getM ?state'))\<close>
                using assms
                using assertLiteralEffect[of "state" "literal" "decision"]
                unfolding InvariantConsistent_def
                by auto
            qed
          qed
        qed
      qed
    qed
  }
  thus ?thesis
    unfolding InvariantQCharacterization_def
    by simp
qed

lemma AssertLiteralStartQIreleveant:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
shows
  "let state' = (assertLiteral literal decision (state\<lparr> getQ := Q' \<rparr>)) in
   let state'' = (assertLiteral literal decision (state\<lparr> getQ := Q'' \<rparr>)) in
   (getM state') = (getM state'') \<and> 
   (getF state') = (getF state'') \<and> 
   (getSATFlag state') = (getSATFlag state'') \<and> 
   (getConflictFlag state') = (getConflictFlag state'')
  " 
using assms
unfolding assertLiteral_def
unfolding notifyWatches_def
unfolding InvariantWatchListsContainOnlyClausesFromF_def
using notifyWatchesStartQIreleveant[of 
"state\<lparr> getQ := Q', getM := getM state @ [(literal, decision)] \<rparr>"
"getWatchList (state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>) (opposite literal)" 
"state\<lparr> getQ := Q'', getM := getM state @ [(literal, decision)] \<rparr>" 
"opposite literal" "[]"]
by (simp add: Let_def)

lemma assertedLiteralIsNotUnit:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
shows
  "let state' = assertLiteral literal decision state in
      \<not> literal \<in> (set (getQ state') - set(getQ state))"
proof-
  {
    let ?state = "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
    let ?state' = "assertLiteral literal decision state"

    assume "\<not> ?thesis"
    
    have *:"\<forall>l. l \<in> set (getQ ?state') - set (getQ ?state) \<longrightarrow>
            (\<exists>clause. clause el (getF ?state) \<and> isUnitClause clause l (elements (getM ?state)))"
      using NotifyWatchesLoopQEffect[of "?state" "getM state" "opposite literal" "decision"   "getWatchList ?state (opposite literal)" "[]"]
      using assms
      unfolding InvariantWatchListsUniq_def
      unfolding InvariantWatchListsCharacterization_def
      unfolding InvariantWatchListsContainOnlyClausesFromF_def
      unfolding InvariantWatchCharacterization_def
      unfolding assertLiteral_def
      unfolding notifyWatches_def
      by (auto simp add: Let_def)
    with \<open>\<not> ?thesis\<close>
    obtain clause
      where "isUnitClause clause literal (elements (getM ?state))"
      by (auto simp add: Let_def)
    hence "False"
      unfolding isUnitClause_def
      by simp
  }
  thus ?thesis
    by auto
qed

lemma InvariantQCharacterizationAfterAssertLiteralNotInQ:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "\<not> literal el (getQ state)"
shows
  "let state' = (assertLiteral literal decision state) in
      InvariantQCharacterization (getConflictFlag state') (getQ state') (getF state') (getM state')"
proof-
  let ?state' = "assertLiteral literal decision state"
  have "InvariantQCharacterization (getConflictFlag ?state') (removeAll literal (getQ ?state')) (getF ?state') (getM ?state')"
    using assms
    using InvariantQCharacterizationAfterAssertLiteral
    by (simp add: Let_def)
  moreover
  have "\<not> literal el (getQ ?state')"
    using assms
    using assertedLiteralIsNotUnit[of "state" "literal" "decision"]
    by (simp add: Let_def)
  hence "removeAll literal (getQ ?state') = getQ ?state'"
    using removeAll_id[of "literal" "getQ ?state'"]
    by simp
  ultimately
  show ?thesis
    by (simp add: Let_def)
qed

lemma InvariantUniqQAfterAssertLiteral:
assumes
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantUniqQ (getQ state)"
shows
  "let state' = assertLiteral literal decision state in
      InvariantUniqQ (getQ state')"
using assms
using InvariantUniqQAfterNotifyWatchesLoop[of "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
"getWatchList (state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>) (opposite literal)"
"opposite literal" "[]"]
unfolding assertLiteral_def
unfolding notifyWatches_def
unfolding InvariantWatchListsContainOnlyClausesFromF_def  
by (auto simp add: Let_def)

lemma InvariantsNoDecisionsWhenConflictNorUnitAfterAssertLiteral:
assumes
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantNoDecisionsWhenConflict (getF state) (getM state) (currentLevel (getM state))"
  "InvariantNoDecisionsWhenUnit (getF state) (getM state) (currentLevel (getM state))"
  "decision \<longrightarrow> \<not> (getConflictFlag state) \<and> (getQ state) = []"
shows
  "let state' = assertLiteral literal decision state in
       InvariantNoDecisionsWhenConflict (getF state') (getM state') (currentLevel (getM state')) \<and> 
       InvariantNoDecisionsWhenUnit (getF state') (getM state') (currentLevel (getM state'))"
proof-
  {
    let ?state' = "assertLiteral literal decision state"
    fix level
    assume "level < currentLevel (getM ?state')"
    have "\<not> formulaFalse (getF ?state') (elements (prefixToLevel level (getM ?state'))) \<and> 
          \<not> (\<exists>clause literal. clause el (getF ?state') \<and>
                isUnitClause clause literal (elements (prefixToLevel level (getM ?state'))))" 
    proof (cases "level < currentLevel (getM state)")
      case True
      hence "prefixToLevel level (getM ?state') = prefixToLevel level (getM state)"
        using assms
        using assertLiteralEffect[of "state" "literal" "decision"]
        by (auto simp add: prefixToLevelAppend)
      moreover
      have "\<not> formulaFalse (getF state) (elements (prefixToLevel level (getM state)))"
        using \<open>InvariantNoDecisionsWhenConflict (getF state) (getM state) (currentLevel (getM state))\<close>
        using \<open>level < currentLevel (getM state)\<close>
        unfolding InvariantNoDecisionsWhenConflict_def
        by simp
      moreover
      have "\<not> (\<exists>clause literal. clause el (getF state) \<and> 
                isUnitClause clause literal (elements (prefixToLevel level (getM state))))"
        using \<open>InvariantNoDecisionsWhenUnit (getF state) (getM state) (currentLevel (getM state))\<close>
        using \<open>level < currentLevel (getM state)\<close>
        unfolding InvariantNoDecisionsWhenUnit_def
        by simp
      ultimately
      show ?thesis
        using assms
        using assertLiteralEffect[of "state" "literal" "decision"]
        by auto
    next
      case False
      thus ?thesis
      proof (cases "decision")
        case False
        hence "currentLevel (getM ?state') = currentLevel (getM state)"
          using assms
          using assertLiteralEffect[of "state" "literal" "decision"]
          unfolding currentLevel_def
          by (auto simp add: markedElementsAppend)
        thus ?thesis 
          using \<open>\<not> (level < currentLevel (getM state))\<close>
          using \<open>level < currentLevel (getM ?state')\<close>
          by simp
      next
        case True
        hence "currentLevel (getM ?state') = currentLevel (getM state) + 1"
          using assms
          using assertLiteralEffect[of "state" "literal" "decision"]
          unfolding currentLevel_def
          by (auto simp add: markedElementsAppend)
        hence "level = currentLevel (getM state)"
          using \<open>\<not> (level < currentLevel (getM state))\<close>
          using \<open>level < currentLevel (getM ?state')\<close>
          by simp
        hence "prefixToLevel level (getM ?state') = (getM state)"
          using \<open>decision\<close>
          using assms
          using assertLiteralEffect[of "state" "literal" "decision"]
          using prefixToLevelAppend[of "currentLevel (getM state)" "getM state" "[(literal, True)]"]
          by auto
        thus ?thesis
          using \<open>decision\<close>
          using \<open>decision \<longrightarrow> \<not> (getConflictFlag state) \<and> (getQ state) = []\<close>
          using \<open>InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)\<close>       
          using \<open>InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)\<close>
          unfolding InvariantConflictFlagCharacterization_def
          unfolding InvariantQCharacterization_def
          using assms
          using assertLiteralEffect[of "state" "literal" "decision"]
          by simp
      qed
    qed
  } thus ?thesis
    unfolding InvariantNoDecisionsWhenConflict_def
    unfolding InvariantNoDecisionsWhenUnit_def
    by auto
qed



lemma InvariantVarsQAfterAssertLiteral:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantUniq ((getM state) @ [(literal, decision)])"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantWatchListsUniq (getWatchList state)"
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"  
  "InvariantVarsQ (getQ state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
shows  
  "let state' = assertLiteral literal decision state in
     InvariantVarsQ (getQ state') F0 Vbl"
proof-
  let ?Q' = "{ul. \<exists>uc. uc el (getF state) \<and>
                  (opposite literal) el uc \<and> isUnitClause uc ul (elements (getM state) @ [literal])}"
  let ?state' = "assertLiteral literal decision state"
  have "vars ?Q' \<subseteq> vars (getF state)"
  proof
    fix vbl::Variable
    assume "vbl \<in> vars ?Q'"
    then obtain ul::Literal
      where "ul \<in> ?Q'" "var ul = vbl"
      by auto
    then obtain uc::Clause
      where "uc el (getF state)"  "isUnitClause uc ul (elements (getM state) @ [literal])"
      by auto
    hence "vars uc \<subseteq> vars (getF state)" "var ul \<in> vars uc"
      using formulaContainsItsClausesVariables[of "uc" "getF state"]
      using clauseContainsItsLiteralsVariable[of "ul" "uc"]
      unfolding isUnitClause_def
      by auto
    thus "vbl \<in> vars (getF state)"
      using \<open>var ul = vbl\<close>
      by auto
  qed
  thus ?thesis
    using assms
    using assertLiteralQEffect[of "state" "literal" "decision"]
    using varsClauseVarsSet[of "getQ ?state'"]
    using varsClauseVarsSet[of "getQ state"]
    unfolding InvariantVarsQ_def
    unfolding InvariantVarsF_def
    by (auto simp add: Let_def)
qed

end
