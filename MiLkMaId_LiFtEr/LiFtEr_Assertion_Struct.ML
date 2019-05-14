(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Assertion_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

LiFtEr:   Logical Feature Extractor.
*)

(*** LiFtEr_Assertion ***)
structure LiFtEr_Assertion =
struct

type assertions = (int * LiFtEr.assrt) list;
fun register_assertions (asserts: assertions) = map (uncurry Apply_LiFtEr.update_assert) asserts;

structure LU = LiFtEr_Util;
structure L  = LiFtEr;

infix And;
val op And = L.And

val sample_assert =
 L.All_Ind (L.Trm 1,
   L.Some_Trm_Occ (L.Trm_Occ 2,
       L.Trm_Occ_Is_Of_Trm (L.Trm_Occ 2, L.Trm 1)
     And
       L.Is_Atom (L.Trm_Occ 2))): L.assrt;

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