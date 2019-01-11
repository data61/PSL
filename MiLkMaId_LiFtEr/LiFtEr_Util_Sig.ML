(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Util_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Helper functions for LiFtEr.
*)
signature LIFTER_UTIL =
sig

type path = ints;

(** patterns **)
datatype left_pttrn        = Var                 | Data_Const_WO_Param | Data_Const_W_Param;
datatype which_call        = All_Rec_Calls       | Some_Rec_Call;
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
datatype pttrn_of_a_param_in_a_clause = Pttrn_Atom    of left_pttrn * (right_pttrns list);
datatype pttrn_of_a_clause            = Pttrn_Clause  of pttrn_of_a_param_in_a_clause list;
datatype pttrn_of_clauses             = Pttrn_Clauses of pttrn_of_a_clause list;

val get_pttrn_of_nth_params_mth_clause: pttrn_of_clauses -> int (*nth*) -> int (*mth*) -> pttrn_of_a_param_in_a_clause;

(* matrix? 'a matrix (= 'a list list) provides more generality.
 * But we only have to tackle this problem for now. So we do not have the necessity for generalization. *)
datatype command = Definition | Fun | Function | Inductive | Primrec | Unknown;

end;