theory Try_Hard 
imports Isar_Interface
begin

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

lemma "True" and "True"
try_hard
oops

end