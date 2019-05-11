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
structure L = LiFtEr;

in

val mods_for_Isaplanner_01 = LU.Ind_Mods
 {ons   = [LU.Ind_On (LU.Print "xs")],
  arbs  = [],
  rules = [LU.Ind_Rule "TIP_prop_01.drop.induct"]
  }: LU.ind_mods;

end;
*}

theorem property0 :
  "((x (take n xs) (drop n xs)) = xs)"
  apply (induct xs rule: TIP_prop_01.drop.induct)
  apply auto
  done

end
