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

structure LU = LiFtEr_Util;
open LiFtEr;
infix And Or Imply;

in

val mods_for_Isaplanner_01 = LU.Ind_Mods
 {ons   = [LU.Ind_On (LU.Print "xs")],
  arbs  = [],
  rules = [LU.Ind_Rule "TIP_prop_01.drop.induct"]
  }: LU.ind_mods;

val assert_should_fail =
    Some_Rule (Rule 1,
      Some_Sub_Trm_Occ (Sub_Trm_Occ 2,
        Is_Rule_Of (Rule 1, Sub_Trm_Occ 2)));

val assert_should_succeed =
Some_Rule (Rule 1,
  Some_Sub_Trm (Sub_Trm 2,
    Some_Sub_Trm_Occ (Sub_Trm_Occ 3,
        Is_Cnst (Sub_Trm_Occ 3)
      And
        Is_Rule_Of (Rule 1, Sub_Trm_Occ 3)
      And
        Trm_Occ_Is_Of_Trm (Sub_Trm_Occ 3, Sub_Trm 2))));

val test_Print_Is =
  Some_Rule (Rule 1,
    Some_Sub_Trm (Sub_Trm 2,
      Some_Sub_Trm_Occ (Sub_Trm_Occ 3,
(*
        Print_Is (Sub_Trm 2, "TIP_prop_01.drop")
      And
*)
        Is_Rule_Of (Rule 1, Sub_Trm_Occ 3))));

val test_True      = True;
val test_Not       = Not True;
val test_Or_True   = True Or (Not True);
val test_Or_False  = (Not True) Or (Not True);
val test_Some_Ind_and_Some_Sub_Trm_Occ =
  Some_Ind (Sub_Trm 1, True)
(*
    Some_Sub_Trm_Occ (Sub_Trm_Occ 2,
      True));
*)
end;
*}

setup{* Apply_LiFtEr.update_assert  4 LiFtEr_Assertion.sample_assert;      *}
setup{* Apply_LiFtEr.update_assert  5 assert_should_fail;                  *}
setup{* Apply_LiFtEr.update_assert  6 test_True;                           *}
setup{* Apply_LiFtEr.update_assert  7 test_Not;                            *}
setup{* Apply_LiFtEr.update_assert  8 test_Or_True;                        *}
setup{* Apply_LiFtEr.update_assert  9 test_Or_False;                       *}
setup{* Apply_LiFtEr.update_assert  10 test_Some_Ind_and_Some_Sub_Trm_Occ; *}


setup{* Apply_LiFtEr.update_ind_mod 3 sample_induct_args1;            *}


theorem property0 :
  "((x (take n xs) (drop n xs)) = xs)"
(*
  test_LiFtEr_true  1 3
  test_LiFtEr_true  4 3
*)
  test_LiFtEr_false 5 3
  test_LiFtEr_true  6 3
  test_LiFtEr_false 7 3
  test_LiFtEr_true  8 3
  test_LiFtEr_false 9 3
  test_LiFtEr_true  10 3
  apply (induct xs rule: TIP_prop_01.drop.induct)
  apply auto
  done

end
