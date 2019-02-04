(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Util_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Helper functions for LiFtEr.
*)
(*** LIFTER_UTIL ***)
signature LIFTER_UTIL =
sig

type path = ints;

(** patterns **)
datatype left_pttrn        = PVar          | PData_Const_WO_Param | PData_Const_W_Param;
datatype which_call        = All_Rec_Calls | Some_Rec_Call;
(* portion
 * Whole: If the whole nth parameter of "f" appears as an argument of (some/all) recursive call(s) of "f" in the definition of "f".
 * Part:  If a part of nth parameter of "f" appears as an argument of (some/all) recursive call(s) of "f" in the definition of "f".
 *)
datatype portion           = Whole of which_call | Part of which_call;
(* at which position:
 * Same_Arg_Position: If the nth parameter of "f" appears as (part of) the nth argument of (some/all) recursive call(s) of "f" in the definition of "f".
 * Diff_Arg_Position: If the nth parameter of "f" appears as (part of) of an argument of (some/all) recursive call(s) of "f" in the definition of "f". *)
datatype at_which_position = Same_Arg_Position of which_call | Diff_Arg_Position of which_call;
type     recursive         = {portion : portion, which_call : which_call, at_which_position : at_which_position};
datatype right_pttrn                  = If | Case | Recursive of recursive;
type     right_pttrns                 = right_pttrn list;
datatype pttrn_of_a_param_in_a_clause = Pttrn_Atom    of left_pttrn * right_pttrns;
type     pttrn_of_a_clause            = pttrn_of_a_param_in_a_clause Matrix.row;
type     pttrn_of_clauses             = pttrn_of_a_clause            Matrix.column;
type     pttrn_of_a_const             = pttrn_of_a_param_in_a_clause Matrix.column_of_rows_matrix;

val get_pttrn_of_nth_params_mth_clause: pttrn_of_a_const -> int (*nth*) -> int (*mth*) -> pttrn_of_a_param_in_a_clause option;

(* command *)
datatype command = Definition | Fun | Function | Inductive | Primrec | Unknown;

datatype hol_typ = Fun_Typ | List_Typ | Nat_Typ | Int_Typ | Set_Typ (*TODO:| Rec_Typ*);(*commonly used HOL types*)

(* print: the printed format of a sub-tree in the syntax tree of a term. *)
datatype print = Print of string;
val dest_print           : print -> string;
val is_subprint_of       : print -> print -> bool;
val same_prints          : print -> print -> bool;
val ctxt_n_print_to_cname: Proof.context -> print -> string option;

(* modifiers for the induct method *)
datatype induct_on   = Ind_On      of print;
datatype induct_arb  = Ind_Arb     of print;
datatype induct_rule = Ind_Rule    of string;
datatype ind_mods    = Ind_Mods    of {ons: induct_on list, arbs: induct_arb list, rules: induct_rule};

val dest_induct_on  : induct_on   -> print;
val dest_induct_arb : induct_arb  -> print;
val dest_induct_rule: induct_rule -> string;

end;