(*  Title:      src/Try_Hard.thy
    Author:     Yutaka Nagashima, Data61, CSIRO

This file defines the default strategy "TryHard".
*)

theory Try_Hard
imports Main
keywords "strategy"     :: thy_decl
     and "find_proof"   :: diag
     and "try_hard"     :: diag
     and "try_hard_one" :: diag
     and "try_hard_all" :: diag
     and "try_parallel" :: diag
begin

ML_file \<open>Utils.ML\<close>
ML_file \<open>Subtool.ML\<close>
ML_file \<open>Dynamic_Tactic_Generation.ML\<close>
ML_file \<open>Constructor_Class.ML\<close>
ML_file \<open>Instantiation.ML\<close>
ML_file \<open>Monadic_Prover.ML\<close>
ML_file \<open>Parser_Combinator.ML\<close>
ML_file \<open>PSL_Parser.ML\<close>
ML_file \<open>Isar_Interface.ML\<close>

text\<open>Prevent overwriting the default basic strategies.\<close>
strategy Simp = Simp
strategy Blast = Blast
strategy Clarsimp = Clarsimp
strategy Fastforce = Fastforce
strategy Auto = Auto
strategy Induct = Induct
strategy InductTac = InductTac
strategy Rule = Rule
strategy Erule = Erule
strategy Cases = Cases
strategy Coinduction = Coinduction
strategy IsSolved = IsSolved
strategy Defer = Defer
strategy IntroClasses = IntroClasses
strategy Transfer = Transfer
strategy Normalization = Normalization
strategy Hammer = Hammer
strategy Nitpick = Nitpick
strategy Quickcheck = Quickcheck

text\<open>Small scale strategies.\<close>
strategy Auto_Solve = Thens [Auto, IsSolved]
strategy Blast_Solve = Thens [Blast, IsSolved]
strategy FF_Solve = Thens [Fastforce, IsSolved]
strategy Auto_Solve1 = Thens [Subgoal, Auto, IsSolved]
strategy Auto_Hammer = Thens [Subgoal, Auto, RepeatN(Hammer), IsSolved]
strategy Solve_One = Ors [Fastforce, Auto_Solve1, Hammer]
strategy Solve_Many = Thens [Repeat (Solve_One), IsSolved]
strategy DInduct = Dynamic (Induct)
strategy DInductTac = Dynamic (InductTac)
strategy DCoinduction = Dynamic (Coinduction)
strategy DCases = Dynamic (Cases)
strategy DCaseTac = Dynamic (CaseTac)
strategy DAuto = Dynamic (Auto)

text\<open>Defining default strategies.
They can be called by the keywords: try_hard, try_hard_one, try_hard_all, and try_parallel.
- try_hard tries to discharge at least one sub-goal.
- try_hard_one tries to discharge the first sub-goal.
- try_hard_all tries to discharge all the current sub-goals.
- try_parallel tries to discharge at least one sub-goal exploiting parallelism.
\<close>

strategy Basic =
  Ors [
       Auto_Solve,
       Blast_Solve,
       FF_Solve,
       Thens [IntroClasses, Auto_Solve],
       Thens [Transfer, Auto_Solve],
       Thens [Normalization, IsSolved],
       Thens [DInduct, Auto_Solve],
       Thens [Hammer, IsSolved],
       Thens [DCases, Auto_Solve],
       Thens [DCoinduction, Auto_Solve],
       (*Occasionally, auto reveals hidden facts.*)
       Thens [Auto, RepeatN(Hammer), IsSolved],
       Thens [DAuto, IsSolved]
       ]

strategy Advanced =
  Ors [
       Solve_Many,
       Thens [DCases, DCases, Auto_Solve],
       Thens [DCases, Solve_Many],
       Thens [IntroClasses,
              Repeat (Ors [Fastforce, Thens [Transfer, Fastforce], Solve_Many]),
              IsSolved],
       Thens [Transfer, Solve_Many],
       Thens [DInduct, Solve_Many],
       Thens [DCoinduction, Solve_Many]
       ]

strategy Try_Hard_All =
  Ors [
       Basic,
       Thens [DInductTac, Auto_Solve],
       Thens [DCaseTac, Auto_Solve],
       Advanced,
       Thens [DCaseTac, Solve_Many],
       Thens [DInductTac, Solve_Many]
       ]

strategy Try_Hard_One = Thens [Subgoal, Try_Hard_All]

(*The subgoal command occasionally makes it impossible to apply induct_tac and case_tac.*)
strategy Try_Hard =
  Ors [
       Thens [Subgoal, Basic],
       Thens [DInductTac, Auto_Solve],
       Thens [DCaseTac, Auto_Solve],
       Thens [Subgoal, Advanced],
       Thens [DCaseTac, Solve_Many],
       Thens [DInductTac, Solve_Many]
       ]

strategy PBasic =
  POrs [
       Auto_Solve,
       FF_Solve,
       Blast_Solve,
       Thens [IntroClasses, Auto_Solve],
       Thens [Transfer, Auto_Solve],
       Thens [Normalization, IsSolved],
       Thens [Hammer, IsSolved],
       Thens [DInduct, Auto_Solve],
       Thens [DCases, Auto_Solve],
       Thens [DCoinduction, Auto_Solve],
       (*Occasionally, auto reveals hidden facts.*)
       Thens [Auto, RepeatN(Hammer), IsSolved],
       Thens [DAuto, IsSolved]
       ]

strategy PAdvanced =
  POrs [
       Thens [DAuto, IsSolved],
       Thens [DCases, DCases, Auto_Solve],
       Thens [IntroClasses,
              Repeat (Ors [Fastforce, Thens [Transfer, Fastforce], Hammer]),
              IsSolved],
       Solve_Many,
       PThenOne [DCases, Solve_Many],
       Thens [Transfer, Solve_Many],
       PThenOne [DInduct, Solve_Many],
       PThenOne [DCoinduction, Solve_Many]
       ]

strategy Try_Parallel =
  POrs [
       Thens [Subgoal, PBasic],
       PThenOne [DInductTac, Auto_Solve],
       PThenOne [DCaseTac, Auto_Solve],
       Thens [Subgoal, PAdvanced],
       PThenOne [DCaseTac, Solve_Many],
       PThenOne [DInductTac, Solve_Many]
       ]

end
