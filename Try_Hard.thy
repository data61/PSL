(*  Title:      Try_Hard.thy
    Author:     Yutaka Nagashima, Data61, CSIRO

This file defines the default strategy "TryHard".
*)

theory Try_Hard
imports Main
keywords "strategy"   :: thy_decl
     and "find_proof" :: diag
     and "try_hard"   :: diag
     and "try_hard1"  :: diag
begin

ML_file "Utils.ML"
ML_file "Subtool.ML"
ML_file "Dynamic_Tactic_Generation.ML"
ML_file "Constructor_Class.ML"
ML_file "Instantiation.ML"
ML_file "Monadic_Prover.ML"
ML_file "Parser_Combinator.ML"
ML_file "PSL_Parser.ML"
ML_file "Isar_Interface.ML"

strategy TryHard =
  Ors [
       Thens [Auto, IsSolved],
       Thens [IntroClasses, Auto, IsSolved],
       Thens [Transfer, Auto, IsSolved],
       Thens [Normalization, IsSolved],
       Thens [Hammer, IsSolved],
       Thens [Dynamic (Induct), Auto, IsSolved],
       Thens [Dynamic (Cases), Auto, IsSolved],
       Thens [Dynamic (Auto), IsSolved],
       Thens [Dynamic (Coinduction), Auto, IsSolved],
       Thens [Dynamic (InductTac), Auto, IsSolved],
       Thens [Dynamic (CaseTac), Auto, IsSolved],
       Thens [Repeat (Ors [Fastforce, Hammer]), IsSolved],
       Thens [Dynamic (Cases), Repeat (Ors [Fastforce, Hammer]), IsSolved],
       Thens [IntroClasses,
              Repeat (Ors [Fastforce, Thens [Transfer, Fastforce], Hammer]),
              IsSolved],
       Thens [Transfer, Repeat (Ors [Fastforce, Hammer]), IsSolved],
       Thens [Dynamic (Induct), Repeat (Ors [Fastforce, Hammer]), IsSolved],
       Thens [Dynamic (CaseTac), Repeat (Ors [Fastforce, Hammer]), IsSolved],
       Thens [Dynamic (InductTac), Repeat (Ors [Fastforce, Hammer]), IsSolved],
       Thens [Dynamic (Coinduction), Repeat (Ors [Fastforce, Hammer]), IsSolved]
       ]

strategy TryHard1 = Thens [Subgoal, TryHard]

lemma "True" and "True"
try_hard
oops

end