(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Assertion_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

LiFtEr:   Logical Feature Extractor.
*)

(*** LiFtEr_Assertion ***)
structure LiFtEr_Assertion =
struct

type assertions = (int * LiFtEr.assrt) list;
fun register_assertions (asserts: assertions) = map (uncurry Apply_LiFtEr.update_assert) asserts;

open LiFtEr LiFtEr_Util;
infix
  And
  Or
  Imply
  Is_In_Trm_Loc
  Is_In_Trm_Str
  Is_Nth_Ind
  Is_In_Trm_Loc
  Is_In_Trm_Str
  Is_Typ
  Is_More_Than
  Is_Const_Of_Name
  Is_Printed_As
  Is_At_Depth
  Is_An_Arg_Of;

(*** assertions to judge induction variables regardless of arbitrary or rule ***)

(** location with regards to pattern matching of ancestoral nodes **)

(** location with regards to (first subgoal / chained facts, premise / coclusion) **)

(* in terms of meta-implication: any ind_var - some ind_var_occ *)

(* in terms of meta-implication: any ind_var - any ind_var_occ *)

(** location with regards to depth **)

(* in terms of depth of a function: *)

(* in terms of depth of an induction variable *)

(*** assertions to judge rule regardless of induction variables or arbitrary ***)

(** location with regards to (first subgoal / chained facts, premise / coclusion) (one const.induct - some const_occ - location) **)

(*** assertions to judge induction variables and arbitrary ***)

(*** assertions to judge induction variables and rule ***)

(** (const_occ - ind_var - part) **)

(** (ind_var - const_occ - part) **)

(*** assertions to judge arbitrary and rule ***)

(** (const_occ - arb_var - part) **)

(** (arb_var - const_occ - part) **)

(*** constants defined in the standard library ***)

end;