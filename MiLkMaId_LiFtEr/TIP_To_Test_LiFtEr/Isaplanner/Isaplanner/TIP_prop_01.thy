(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
theory TIP_prop_01
  imports "../../Test_Base" "../../../MeLoId_LiFtEr"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun take :: "Nat => 'a list => 'a list" where
  "take (Z) z = nil2"
| "take (S z2) (nil2) = nil2"
| "take (S z2) (cons2 x2 x3) = cons2 x2 (take z2 x3)"

fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) z = z"
| "drop (S z2) (nil2) = nil2"
| "drop (S z2) (cons2 x2 x3) = drop z2 x3"

ML{* (*modifiers*)
local

open LiFtEr LiFtEr_Util;
infix And Or Imply;

in

val mods_for_Isaplanner_01_01 = Ind_Mods
 {ons   = [Ind_On (Print "xs")],
  arbs  = [],
  rules = [Ind_Rule "TIP_prop_01.drop.induct"]
  }: ind_mods;

val mods_for_Isaplanner_01_02 = Ind_Mods
 {ons   = [],
  arbs  = [],
  rules = [Ind_Rule "TIP_prop_01.drop.induct"]
  }: ind_mods;

val mods_for_Isaplanner_01_03 = Ind_Mods
 {ons   = [],
  arbs  = [Ind_Arb (Print "n")],
  rules = []
  }: ind_mods;

val mods_for_Isaplanner_01_04 = Ind_Mods
 {ons   = [Ind_On (Print "xs")],
  arbs  = [],
  rules = []
  }: ind_mods;

val test_Some_Rule_n_Some_Trm_Occ_n_Is_Rule_Of =
    Some_Rule (Rule 1,
      Some_Trm_Occ (Trm_Occ 2,
        Is_Rule_Of (Rule 1, Trm_Occ 2)));

val assert_should_succeed =
  Some_Rule (Rule 1,
    Some_Trm (Trm 2,
      Some_Trm_Occ (Trm_Occ 3,
          Is_Cnst (Trm_Occ 3)
        And
          Is_Rule_Of (Rule 1, Trm_Occ 3)
        And
          Trm_Occ_Is_Of_Trm (Trm_Occ 3, Trm 2))));

val test_True      = True;
val test_Not       = Not True;
val test_Or_True   = True Or (Not True);
val test_Or_False  = (Not True) Or (Not True);
val test_Some_Ind_and_Some_Trm_Occ = Some_Ind (Trm 1, True)
(* test_Print_Is *)
val test_Print_Is =
    (Some_Trm (Trm 1,
         Print_Is (Trm 1, "TIP_prop_01.drop")))
  And
    (Some_Trm (Trm 1,
         Print_Is (Trm 1, "TIP_prop_01.take")))
  And
    (Some_Trm (Trm 1,
         Print_Is (Trm 1, "TIP_prop_01.drop n xs")))
  And
    (Not (*Print does not contain redundant parentheses.*)
      (Some_Trm (Trm 1,
           Print_Is (Trm 1, "(TIP_prop_01.drop n xs)"))))
  And
    (*For some reasons, Print uses a short name for "x".*)
    (Some_Trm (Trm 1,
         Print_Is (Trm 1, "x")))
  And
    (Some_Trm (Trm 1,
         Print_Is (Trm 1, "x (TIP_prop_01.take n xs) (TIP_prop_01.drop n xs)")))
  And
    (Some_Trm (Trm 1,
         Print_Is (Trm 1, "x (TIP_prop_01.take n xs) (TIP_prop_01.drop n xs) = xs")));

(* test_Some_Trm_Occ *)
val test_Some_Trm_Occ =
    (Some_Trm (Trm 1,
       (Some_Trm_Occ (Trm_Occ 2,
         Print_Is (Trm 1, "TIP_prop_01.drop")
       And
         Trm_Occ_Is_Of_Trm (Trm_Occ 2, Trm 1)))));

(* test_Print_Is_n_Is_Rule_Of *)
val test_Print_Is_n_Is_Rule_Of =
  (Some_Rule (Rule 1,
    (Some_Trm (Trm 2,
       (Some_Trm_Occ (Trm_Occ 3,
         Print_Is (Trm 2, "TIP_prop_01.drop")
       And
         Is_Rule_Of (Rule 1, Trm_Occ 3)))))));

val test_Some_Rule = Some_Rule (Rule 1, True);

val test_Some_Arb = Some_Arb (Trm 1, True);

end;
*}

setup{* Apply_LiFtEr.update_assert  4 LiFtEr_Assertion.sample_assert;                 *}
setup{* Apply_LiFtEr.update_assert  5 test_Some_Rule_n_Some_Trm_Occ_n_Is_Rule_Of; *}
setup{* Apply_LiFtEr.update_assert  6 test_True;                                      *}
setup{* Apply_LiFtEr.update_assert  7 test_Not;                                       *}
setup{* Apply_LiFtEr.update_assert  8 test_Or_True;                                   *}
setup{* Apply_LiFtEr.update_assert  9 test_Or_False;                                  *}
setup{* Apply_LiFtEr.update_assert  10 test_Some_Ind_and_Some_Trm_Occ;            *}
setup{* Apply_LiFtEr.update_assert  11 test_Print_Is                                  *}
setup{* Apply_LiFtEr.update_assert  12 test_Some_Trm_Occ;                         *}
setup{* Apply_LiFtEr.update_assert  13 test_Print_Is_n_Is_Rule_Of;                    *}
setup{* Apply_LiFtEr.update_assert  14 test_Some_Rule;                                *}
setup{* Apply_LiFtEr.update_assert  15 test_Some_Arb;                                 *}

setup{* Apply_LiFtEr.update_ind_mod 3 mods_for_Isaplanner_01_01; *}
setup{* Apply_LiFtEr.update_ind_mod 4 mods_for_Isaplanner_01_02; *}
setup{* Apply_LiFtEr.update_ind_mod 5 mods_for_Isaplanner_01_03; *}
setup{* Apply_LiFtEr.update_ind_mod 6 mods_for_Isaplanner_01_04; *}

theorem property0 :
  "((x (take n xs) (drop n xs)) = xs)"
(*
  test_LiFtEr_true  1 3
  test_LiFtEr_true  4 3
*)
  test_LiFtEr_true  5 3
  test_LiFtEr_true  6 3
  test_LiFtEr_false 7 3
  test_LiFtEr_true  8 3
  test_LiFtEr_false 9 3
  test_LiFtEr_true  10 3
  test_LiFtEr_true  11 3
  test_LiFtEr_true  12 3
  test_LiFtEr_true  13 3
  test_LiFtEr_false 14 5
  test_LiFtEr_true  14 4
  test_LiFtEr_true  15 6
(*  test_LiFtEr_false 15 5 TODO: FIXME*)
  apply (induct xs rule: TIP_prop_01.drop.induct)
  apply auto
  done

end
