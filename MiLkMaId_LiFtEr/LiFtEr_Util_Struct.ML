(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Util_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Helper functions for LiFtEr.
*)
(*** LiFtEr_Util ***)
structure LiFtEr_Util: LIFTER_UTIL =
struct

type path = ints;

(* patterns *)
datatype left_pttrn        = PVar                | PData_Const_WO_Param | PData_Const_W_Param;
datatype which_call        = All_Rec_Calls       | Some_Rec_Call;
(* portion
 * Whole: If the whole nth parameter of "f" appears as an argument of (some/all) recursive call(s) of "f" in the definition of "f".
 * Part:  If a part of nth parameter of "f" appears as an argument of (some/all) recursive call(s) of "f" in the definition of "f".
 *)
datatype portion           = Whole of which_call | Part of which_call;
(* at which position:
 * Same_Arg_Position: If the nth parameter of "f" appears as (part of) the nth argument of (some/all) recursive call(s) of "f" in the definition of "f".
 * Diff_Arg_Position: If the nth parameter of "f" appears as (part of) of an argument of (some/all) recursive call(s) of "f" in the definition of "f". *)
datatype at_which_position            = Same_Arg_Position of which_call | Diff_Arg_Position of which_call;
type     recursive                    = {portion : portion, which_call : which_call, at_which_position : at_which_position};
datatype right_pttrn                  = If | Case | Recursive of recursive;
type     right_pttrns                 = right_pttrn list;
datatype pttrn_of_a_param_in_a_clause = Pttrn_Atom    of left_pttrn * right_pttrns;
type     pttrn_of_a_clause            = pttrn_of_a_param_in_a_clause Matrix.row;
type     pttrn_of_clauses             = pttrn_of_a_clause            Matrix.column;
type     pttrn_of_a_const             = pttrn_of_a_param_in_a_clause Matrix.column_of_rows_matrix;

fun get_pttrn_of_nth_params_mth_clause (pttrn:pttrn_of_a_const) (mth_param:int) (nth_clause:int) =
  let
    val param = Matrix.crmatrix_to_element_at_mth_row_nth_column pttrn mth_param nth_clause;
  in
    param:pttrn_of_a_param_in_a_clause option
  end;

datatype command = Definition | Fun | Function | Inductive | Primrec | Unknown;
datatype hol_typ = Fun_Typ | List_Typ | Nat_Typ | Int_Typ | Set_Typ (*TODO:| Rec_Typ*);(*commonly used HOL types*)
datatype print   = Print of string;

fun dest_print (Print str) = str;
fun is_subprint_of (Print p1) (Print p2) = String.isSubstring p1 p2;
fun same_prints    (Print p1) (Print p2) = p1 = p2;
fun ctxt_n_print_to_cname  (ctxt:Proof.context) (print:print) =
  let
    val trm_option = try dest_print print >>= try (Syntax.read_term ctxt): term   option;
    val trm_cname  = trm_option >>= try Term.dest_Const <$> fst          : string option;
  in
    trm_cname
  end;

datatype induct_on   = Ind_On      of print;
datatype induct_arb  = Ind_Arb     of print;
datatype induct_rule = Ind_Rule    of string;
datatype ind_mods    = Ind_Mods    of {ons: induct_on list, arbs: induct_arb list, rules: induct_rule};

fun dest_induct_on   (Ind_On print)    = print;
fun dest_induct_arb  (Ind_Arb print)   = print;
fun dest_induct_rule (Ind_Rule string) = string;

end;