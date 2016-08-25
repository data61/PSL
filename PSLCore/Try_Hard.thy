theory Try_Hard
imports Isar_Interface
begin

strategy TryHard = 
  Ors [Thens [Auto, IsSolved],
       Thens [Induct, Auto, IsSolved],
       Thens [Dynamic (Induct), Auto, IsSolved],
       Thens [Repeat (Ors [Fastforce,
                           Hammer,
                           Thens [Clarsimp, Hammer]]),
              IsSolved],
       Thens [Case, Auto, IsSolved],
       Thens [Dynamic ( Simp ), IsSolved],
       Thens [Case,
              Repeat (Ors [Hammer,
                           Fastforce,
                           Thens [Clarsimp, Hammer]]),
              IsSolved],
       Thens [Dynamic (Induct),
              Repeat (Ors [Fastforce,
                           Hammer,
                           Thens [Clarsimp, Hammer]]),
              IsSolved]
       ]
  
lemma "True" and "True"
try_hard
oops

end