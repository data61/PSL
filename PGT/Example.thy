theory Example
  imports "../PSL" "../PaMpeR/PaMpeR" "../PSL"
begin

(* DEMO1: PSL *)

fun sep::"'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sep a [] = []" |
  "sep a [x] = [x]" |
  "sep a (x#y#zs) = x # a # sep a (y#zs)"

(* DEMO2: PaMpeR *)
lemma
  "map f (sep x xs) = sep (f x) (map f xs)"
  (* Before PaMpeR *)
  print_methods
    (* With PaMpeR *)
  which_method
  why_method induct
  thm sep.simps(3)
  rank_method coinduction
  oops

strategy DInd = Thens [Dynamic (Induct), Auto, IsSolved]

lemma "map f (sep x xs) = sep (f x) (map f xs)"
  find_proof DInd
  try_hard
  oops

(* DEMO3: PGT *)

primrec itrev:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"

thm rev.simps

strategy CDInd = Thens [Conjecture, Fastforce, Quickcheck, DInd]
strategy DInd_Or_CDInd = Ors [DInd, CDInd]

lemma "itrev xs [] = rev xs"
(*  DInd cannot find a proof script: find_proof DInd *)
  find_proof DInd_Or_CDInd
  oops

end