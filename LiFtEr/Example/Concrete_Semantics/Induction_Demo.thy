(*
 * This file "Induction_Demo.thy" was originally developed by Tobias Nipkow and Gerwin Klein
 * as Isabelle theory files accompanying their book "Concrete Semantics".
 * 
 * The PDF file of the book and the original Isabelle theory files are available 
 * at the following website:
 *   http://concrete-semantics.org/index.html
 *
 *)
theory Induction_Demo
  imports Main "../../LiFtEr"
begin

(* HINT FOR ONLINE DEMO
   Start your first proof attempt with
   itrev xs [] = rev xs
   then generalize by introducing ys, and finally quantify over ys.
   Each generalization should be motivated by the previous failed
   proof attempt.
*)

 primrec rev :: "'a list \<Rightarrow> 'a list" where
  "rev []       = []" |
  "rev (x # xs) = rev xs @ [x]"


 fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev []     ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"


 lemma "itrev xs ys = rev xs @ ys"
  apply(induct xs arbitrary: ys) apply auto done

ML\<open> (* Example assertions in LiFtEr. *)
local

open LiFtEr_Util LiFtEr;
infix And Imply Is_An_Arg_Of Is_Rule_Of Is_Nth_Ind Is_In_Trm_Loc Is_In_Trm_Str;

in

(* Example 1-a *)
val all_ind_term_are_non_const_wo_syntactic_sugar =
 All_Ind (Trm 1,
   Some_Trm_Occ (Trm_Occ 1,
       Trm_Occ_Is_Of_Trm (Trm_Occ 1, Trm 1)
     And
       Not (Is_Cnst (Trm_Occ 1)))): assrt;

(* Example 1-b *)
val all_ind_term_are_non_const_with_syntactic_sugar =
 All_Ind (Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
     Not (Is_Cnst (Trm_Occ 1)))): assrt;

(* Example 2 *)
val all_ind_terms_have_an_occ_as_variable_at_bottom =
 All_Ind (Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
       Is_Atom (Trm_Occ 1)
     Imply
       Is_At_Deepest (Trm_Occ 1)));

(* Example 3 *)
val all_ind_vars_are_arguments_of_a_recursive_function =
Some_Trm (Trm 1,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    All_Ind (Trm 2,
      Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
           Is_Recursive_Cnst (Trm_Occ 1)
         And
           (Trm_Occ 2 Is_An_Arg_Of Trm_Occ 1)))));

(* Example 4 *)
val all_ind_vars_are_arguments_of_a_rec_func_where_pattern_match_is_complete =
 Not (Some_Rule (Rule 1, True))
Imply
 Some_Trm (Trm 1,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    Is_Recursive_Cnst (Trm_Occ 1)
   And
    All_Ind (Trm 2,
      Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
       Some_Numb (Numb 1,
         Pattern (Numb 1, Trm_Occ 1, All_Constr)
        And
         Is_Nth_Arg_Of (Trm_Occ 2, Numb 1, Trm_Occ 1))))));

(* Example 5 *)
val all_ind_terms_are_arguments_of_a_const_with_a_related_rule_in_order =
 Some_Rule (Rule 1, True)
Imply
 Some_Rule (Rule 1,
  Some_Trm (Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    (Rule 1 Is_Rule_Of Trm_Occ 1)
    And
    (All_Ind (Trm 2,
     (Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
       Some_Numb (Numb 1,
         Is_Nth_Arg_Of (Trm_Occ 2, Numb 1, Trm_Occ 1)
        And
        (Trm 2 Is_Nth_Ind Numb 1)))))))));

(* Example 6-a *)
val ind_is_not_arb =
All_Arb (Trm 1,
 Not (Some_Ind (Trm 2,
  Are_Same_Trm (Trm 1, Trm 2))));

(* Example 6-b *)
val vars_in_ind_terms_are_generalized =
 Some_Ind (Trm 1,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
   (All_Trm (Trm 2,
     Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
       ((Trm_Occ 2 Is_In_Trm_Loc Trm_Occ 1)
       And
        Is_Free (Trm_Occ 2))
      Imply
       Some_Arb (Trm 3,
        Are_Same_Trm (Trm 2, Trm 3)))))));

val Example6 = ind_is_not_arb And vars_in_ind_terms_are_generalized;

end;
\<close>

setup\<open> Apply_LiFtEr.update_assert "heuristic_1a" all_ind_term_are_non_const_wo_syntactic_sugar                           \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_1b" all_ind_term_are_non_const_with_syntactic_sugar                         \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_2"  all_ind_terms_have_an_occ_as_variable_at_bottom                         \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_3"  all_ind_vars_are_arguments_of_a_recursive_function                      \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_4"  all_ind_vars_are_arguments_of_a_rec_func_where_pattern_match_is_complete\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_5"  all_ind_terms_are_arguments_of_a_const_with_a_related_rule_in_order     \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_6a" ind_is_not_arb                                                          \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_6b" vars_in_ind_terms_are_generalized                                       \<close>

ML\<open> (*Arguments for the induct method to attack "itrev xs ys = rev xs @ ys". *)
local

open LiFtEr;

in

(* Official solution of induction application by Tobias Nipkow and Gerwin Klein. *)
val official_solution_for_itrev_equals_rev =
Ind_Mods
 {ons   = [Ind_On  (Print "xs")],
  arbs  = [Ind_Arb (Print "ys")],
  rules = []
  }: ind_mods;

(* An example of inappropriate combination of arguments of the induct method. *)
val bad_answer_for_itrev_equals_rev =
Ind_Mods
 {ons   = [Ind_On  (Print "itrev")],
  arbs  = [Ind_Arb (Print "ys")],
  rules = []
  }: ind_mods;

(* Alternative proof found by Yutaka Nagashima.*)
val xs_ys_rule_itrev_induct =
Ind_Mods
 {ons   = [Ind_On  (Print "xs"), Ind_On (Print "ys")],
  arbs  = [],
  rules = [Ind_Rule "itrev.induct"]
  }: ind_mods;

end;
\<close>

setup\<open> Apply_LiFtEr.update_ind_mod "induct_on_xs_arbitrary_ys"   official_solution_for_itrev_equals_rev \<close>
setup\<open> Apply_LiFtEr.update_ind_mod "induct_on_itrev_arbitrary_ys" bad_answer_for_itrev_equals_rev        \<close>
setup\<open> Apply_LiFtEr.update_ind_mod "induct_on_xs_ys_rule_itrev_induct"     xs_ys_rule_itrev_induct                                \<close>

 lemma "itrev xs ys = rev xs @ ys"
  assert_LiFtEr heuristic_1a [on["xs"],     arb["ys"],rule[]]
  assert_LiFtEr heuristic_1a [on["xs","ys"],arb[],    rule["itrev.induct"]]
(*  assert_LiFtEr heuristic_1a [on["itrev"],  arb["ys"],rule[]]*)

  test_all_LiFtErs [on["xs"],     arb["ys"],rule[]]
  test_all_LiFtErs [on["xs","ys"],arb[],    rule["itrev.induct"]]
  test_all_LiFtErs [on["itrev"],  arb["ys"],rule[]]

  assert_LiFtEr_false heuristic_1a induct_on_itrev_arbitrary_ys
  assert_LiFtEr_true  heuristic_1b induct_on_xs_arbitrary_ys
  assert_LiFtEr_false heuristic_1b induct_on_itrev_arbitrary_ys
  assert_LiFtEr_true  heuristic_2  induct_on_xs_arbitrary_ys
  assert_LiFtEr_false heuristic_2  induct_on_itrev_arbitrary_ys
  assert_LiFtEr_true  heuristic_3  induct_on_xs_arbitrary_ys
  assert_LiFtEr_false heuristic_3  induct_on_itrev_arbitrary_ys
  assert_LiFtEr_true  heuristic_3  induct_on_xs_ys_rule_itrev_induct
  assert_LiFtEr_true  heuristic_4  induct_on_xs_arbitrary_ys
  assert_LiFtEr_false heuristic_4  induct_on_itrev_arbitrary_ys
  assert_LiFtEr_true  heuristic_4  induct_on_xs_ys_rule_itrev_induct
  assert_LiFtEr_true  heuristic_5  induct_on_xs_arbitrary_ys
  assert_LiFtEr_true  heuristic_5  induct_on_itrev_arbitrary_ys (*This is a little unfortunate: heuristic_5 alone cannot detect induct_on_itrev_arbitrary_ys is inappropriate.*)
  assert_LiFtEr_true  heuristic_5  induct_on_xs_ys_rule_itrev_induct
  assert_LiFtEr_true  heuristic_6a induct_on_xs_arbitrary_ys
  assert_LiFtEr_true  heuristic_6a induct_on_itrev_arbitrary_ys (*This is a little unfortunate: heuristic_6a alone cannot detect induct_on_itrev_arbitrary_ys is inappropriate.*)
  assert_LiFtEr_true  heuristic_6a induct_on_xs_ys_rule_itrev_induct
  assert_LiFtEr_true  heuristic_6b induct_on_xs_arbitrary_ys
  assert_LiFtEr_true  heuristic_6b induct_on_itrev_arbitrary_ys (*This is a little unfortunate: heuristic_6b alone cannot detect bad_non_prf is inappropriate.*)
  assert_LiFtEr_true  heuristic_6b induct_on_xs_ys_rule_itrev_induct
  oops

(*Model proof by Nipkow et.al.*)
lemma model_prf:"itrev xs ys = rev xs @ ys"
  apply(induct xs arbitrary: ys)
   apply(auto)
  done

(*Alternative proof by Yutaka Nagashima.*)
lemma alt_prf:"itrev xs ys = rev xs @ ys"
  apply(induct xs ys rule:itrev.induct)
   apply auto
  done

subsection\<open> Computation Induction \<close>

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sep a [] = []" |
  "sep a [x] = [x]" |
  "sep a (x#y#zs) = x # a # sep a (y#zs)"

ML\<open> (*Arguments for the induct method to attack "map f (sep a xs) = sep (f a) (map f xs)". *)
local

open LiFtEr;

in

val official_solution_for_map_sep_equals_sep_map =
Ind_Mods
 {ons   = [Ind_On  (Print "a"), Ind_On  (Print "xs")],
  arbs  = [],
  rules = [Ind_Rule "sep.induct"]
  }: ind_mods;

val only_for_test =
Ind_Mods
 {ons   = [Ind_On  (Print "sep a xs")],
  arbs  = [Ind_Arb (Print "xs")],
  rules = []
  }: ind_mods;

end;
\<close>

setup\<open> Apply_LiFtEr.update_ind_mod "on_a_xs_rule_sep"   official_solution_for_map_sep_equals_sep_map \<close>
setup\<open> Apply_LiFtEr.update_ind_mod "on_sep_a_xs_arb_xs" only_for_test                                \<close>

lemma "map f (sep a xs) = sep (f a) (map f xs)"
  assert_LiFtEr_true heuristic_2  on_a_xs_rule_sep
  assert_LiFtEr_true heuristic_3  on_a_xs_rule_sep
  assert_LiFtEr_true heuristic_4  on_a_xs_rule_sep
  assert_LiFtEr_true heuristic_5  on_a_xs_rule_sep
  assert_LiFtEr_true heuristic_6b on_sep_a_xs_arb_xs
  apply(induction a xs rule: Induction_Demo.sep.induct)
    apply auto
  done

end