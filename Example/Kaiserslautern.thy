theory Kaiserslautern
imports Smart_Isabelle.Smart_Isabelle
begin

primrec rev1::"'a list \<Rightarrow> 'a list" where
  "rev1  []      = []"
| "rev1 (x # xs) = rev1 xs @ [x]"

fun rev2::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev2  []      ys = ys"
| "rev2 (x # xs) ys = rev2 xs (x # ys)"

 theorem "rev2 xs ys = rev1 xs @ ys"
  apply(induct xs arbitrary: ys)
  apply auto done

strategy CDInd = Thens [Conjecture, Fastforce, Quickcheck,
                        Dynamic (Induct), Auto, IsSolved]

lemma assumes "True = True"
  shows "rev2 xs [] = rev1 xs"
  oops

end