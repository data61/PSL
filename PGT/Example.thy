theory Example
imports "../PSL" "../PaMpeR/PaMpeR" "../PSL"
begin

(* DEMO1: PSL *)

fun sep::"'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep a [] = []" |
"sep a [x] = [x]" |
"sep a (x#y#zs) = x # a # sep a (y#zs)"

strategy DInd = Thens [Dynamic (Induct), Auto, IsSolved]

(* The proof in the Isabelle tutorial. *)
lemma "map f (sep x xs) = sep (f x) (map f xs)"
  find_proof DInd
  oops

(* DEMO2: PaMpeR *)

lemma
 "map f (sep x xs) = sep (f x) (map f xs)"
(* The print_methods command prints out the list of methods defined in this proof context in
 * alphabetical order. *)
  print_methods
  which_method
  why_method induct
  thm sep.simps(3)
  rank_method coinduction
  oops

(* DEMO3: PGT *)

primrec itrev:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
 "itrev [] ys = ys" |
 "itrev (x#xs) ys = itrev xs (x#ys)"

strategy CDInd = Thens [Conjecture, Fastforce, Thens [Nitpick, Quickcheck], DInd]
strategy DInd_Or_CDInd = Ors [DInd, CDInd]

lemma "itrev xs [] = rev xs"
  find_proof DInd_Or_CDInd
  apply (subgoal_tac "\<And>Nil. itrev xs Nil = rev xs @ Nil")
  apply fastforce
  apply (induct xs)
  apply auto
  done

end