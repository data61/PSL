theory Example_PSL
imports "PSL.PSL"
begin

strategy DInd = Thens [Dynamic (Induct), Auto, IsSolved]
strategy CDInd = Thens [Conjecture, Fastforce, Quickcheck, DInd]
strategy DInd_Or_CDInd = Ors [DInd, CDInd]


primrec itrev:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"

lemma "itrev xs [] = rev xs"
  find_proof DInd_Or_CDInd
  apply (subgoal_tac "\<And>Nil. itrev xs Nil = rev xs @ Nil")
   apply fastforce
  apply (induct xs)
   apply auto
  done 

end