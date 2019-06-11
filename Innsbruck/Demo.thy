(*  Title:      Innsbruck/Demo.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
                The definitions of sep and itrev are from Isabelle's tutorial.
*)
theory Demo
  imports Main "../PSL" "../PaMpeR/PaMpeR" "../PSL"
begin

(*** Part I ***)
lemma demo: "w ∧ x ⟹ y ∧ z ⟹ z"
  apply(erule conjE)
(*
  back
  apply assumption
  done
*)oops

fun sep::"'a ⇒ 'a list ⇒ 'a list" where
  "sep a [] = []" |
  "sep a [x] = [x]" |
  "sep a (x#y#zs) = x # a # sep a (y#zs)"

strategy DInd = Thens [Dynamic (Induct), Auto, IsSolved]

lemma "map f (sep x xs) = sep (f x) (map f xs)"
  find_proof DInd
  try_hard 
  (* Before PaMpeR *)
  print_methods
    (* With PaMpeR *)
  which_method
  why_method induct
  thm sep.simps(3)
  rank_method coinduction
  oops

primrec itrev:: "'a list ⇒ 'a list ⇒ 'a list" where
  "itrev [] ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"

strategy CDInd = Thens [Conjecture, Fastforce, Quickcheck, DInd]
strategy DInd_Or_CDInd = Ors [DInd, CDInd]

lemma "itrev xs [] = rev xs"
  find_proof DInd_Or_CDInd
  oops

(*** Part II ***)
ML‹ val tracing_returns_unit = tracing "Use @{print} and @{print_tracing} as well"; 
    val assert_for_unit_test = @{assert} (List.nth ([1,2,3], 0)= 1);
    val true_in_HOL1         = @{term "True"};
    val true_in_HOL2         = Const ("HOL.True", @{typ "bool"});
    val assert_for_unit = @{assert} (true_in_HOL1 = true_in_HOL2)›

lemma "True ∧ True"
  apply - ML_val‹(*Use ML_val within a proof.*)› by auto

(* show_tac prints out the whole proof obligation (original goal + current sub-goal) 
 * and do nothing about it. Note the use of proof context. *)
ML‹ fun show_tac (ctxt:Proof.context) (thm:thm) =
  let
    val _ = Syntax.string_of_term ctxt (Thm.full_prop_of thm)
         |> YXML.parse_body
         |> XML.content_of
         |> tracing;
  in
    Seq.single thm: thm Seq.seq
  end; 
›

lemma "w ∧ x ⟹ y ∧ z ⟹ z"
  apply(tactic ‹ show_tac @{context} ›)
  apply(erule conjE)
  back
  apply(tactic ‹ show_tac @{context} ›)
  apply assumption
  apply(tactic ‹ show_tac @{context} ›)
  done

end
