theory Example
imports "../PSL"
begin

primrec my_append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr "@@" 65) where
append_Nil: "[] @@ ys = ys" |
append_Cons: "(x#xs) @@ ys = x # xs @@ ys"

primrec my_rev :: "'a list \<Rightarrow> 'a list" where
"my_rev [] = []" |
"my_rev (x # xs) = my_rev xs @@ [x]"

ML{*
val goal = trm_to_thm @{context} @{term "((my_rev j) @@ k) @@ l = (my_rev j) @@ (k @@ l)"};
val cons = generalize @{context} goal;
*}
declare [[ML_print_depth=300]]

ML{* (* How to apply quickcheck to a raw thm? *)
(* No, I only apply quickcheck after applying fastforce. 
   So, I can use quickcheck as part of PSL strategies. *)
*}

strategy Generalize_Test = Thens [Generalize, Fastforce, Dynamic(InductTac), Auto, IsSolved]
strategy Generalize_Test2 = Thens [Clarsimp, IsSolved]
strategy Generalize_Test3 = Generalize

lemma "True"
  find_proof Generalize_Test2
  oops

lemma "((my_rev j) @@ k) @@ l = (my_rev j) @@ (k @@ l)"
  find_proof Generalize_Test
  apply(subgoal_tac"\<And>uu. (uu @@ k) @@ l = uu @@ k @@ l" )
   apply fastforce
  apply(induct_tac uu)
  apply auto
  done

end