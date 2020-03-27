theory Example
  imports "../PSL" "../PaMpeR/PaMpeR" "../PSL"
begin

(* DEMO1: PSL *)

fun sep::"'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sep a []       = []" |
  "sep a [x]      = [x]" |
  "sep a (x#y#zs) = x # a # sep a (y#zs)"

value "sep (1::int) [0,0,0]"

strategy DInd  = Thens [Dynamic (Induct), Auto, IsSolved]

lemma
  "map f (sep x xs) = sep (f x) (map f xs)"
  find_proof DInd




  print_methods
    (* With PaMpeR *)
  which_method
  why_method induct
  thm sep.simps(3)
  rank_method coinduction
  oops

lemma "map f (sep x xs) = sep (f x) (map f xs)"
(*
  find_proof DInd
  try_hard
*)
  oops

(* DEMO3: PGT *)
primrec rev:: "'a list \<Rightarrow> 'a list" where
  "rev []       = []"
| "rev (x # xs) = rev xs @ [x]"
primrec itrev:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys     = ys"
| "itrev (x#xs) ys = itrev xs (x#ys)"

strategy DInd  = Thens [Dynamic (Induct), Auto, IsSolved]



lemma "itrev xs [] = rev xs"
  find_proof DInd


strategy CDInd = Thens [Conjecture, Fastforce, Quickcheck, DInd]
strategy DInd_Or_CDInd = Ors [DInd, CDInd]
  find_proof DInd_Or_CDInd
  oops

end