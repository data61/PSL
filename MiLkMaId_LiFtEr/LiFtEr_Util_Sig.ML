(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Util_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Helper functions for LiFtEr.
*)

(*** PATTERN ***)
signature PATTERN =
sig

(* command *)
datatype command                        = Definition | Fun | Function | Inductive | Primrec | Unknown;
val get_command                         : Proof.context -> string -> command;

(* pattern *)
datatype hol_typ                        = Fun_Typ | List_Typ | Nat_Typ | Int_Typ | Set_Typ (*TODO:| Rec_Typ*);(*commonly used HOL types*)
datatype left_pattern                   = Only_Var | Data_Constructor_WO_Var | Data_Constructor_W_Var;
datatype pattern_of_a_param_in_a_clause = Pattern_Of_Atom    of left_pattern (*TODO: right_pattern*);
datatype pattern_of_a_param             = Pattern_Of_A_Param of pattern_of_a_param_in_a_clause Matrix.column;
datatype pattern_matrix                 = Pattern_Matrix     of pattern_of_a_param_in_a_clause Matrix.row_of_columns_matrix;
datatype pattern_of_a_const(*TODO:term?*) = Pattern_Of_A_Const of
                                          {(*hol_typ*)
                                           matrix : pattern_of_a_param_in_a_clause Matrix.row_of_columns_matrix};

val mk_parameter_matrix_for_fun       : Proof.context -> string -> pattern_matrix;
val mk_parameter_matrix_for_function  : Proof.context -> string -> pattern_matrix;
val mk_parameter_matrix_for_inductive : Proof.context -> string -> pattern_matrix;
val mk_parameter_matrix_for_primrec   : Proof.context -> string -> pattern_matrix;
val mk_parameter_matrix: Proof.context -> string -> pattern_matrix;

val ctxt_n_name_to_patterns_of_each_param: Proof.context -> string -> pattern_of_a_param list;

val is_nth_all_Only_Var              : Proof.context -> string -> int -> bool;
val is_nth_all_Data_Constructor_W_Var: Proof.context -> string -> int -> bool;

end;

(*** LIFTER_UTIL ***)
signature LIFTER_UTIL =
sig

type     path  = ints;
(* print: the printed format of a sub-tree in the syntax tree of a term. *)
datatype print = Print of string;

end;

(*** TEST_LIFTER ***)
signature TEST_LIFTER =
sig

include LIFTER_UTIL;

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

signature LIFTER_UTIL_AFTER_FEB =
sig

datatype left_pattern                   = Only_Var | Data_Constructor_WO_Var | Data_Constructor_W_Var;
datatype at_which_position_in_rec_call  = Same_Arg_Pos      | Diff_Arg_Pos;
datatype is_the_entire_arg_in_rec_call  = Is_The_Entire_Arg | Is_Not_The_Entire_Arg;
datatype is_in_recurisve_call           = Recursion of at_which_position_in_rec_call * is_the_entire_arg_in_rec_call;
type     is_in_recurisve_calls          = is_in_recurisve_call list; 
datatype is_in_if_condition             = Is_In_If_Condition   | Is_Not_In_If_Condition;
datatype is_in_case_condition           = Is_In_Case_Condition | Is_Not_In_Case_Condition;
datatype right_occ_pattern              = Right_Occ_Pattern  of {in_if:is_in_if_condition, in_case:is_in_case_condition, in_recs: is_in_recurisve_calls};
datatype right_pattern                  = Right_Pattern      of right_occ_pattern list;
datatype pattern_of_a_param_in_a_clause = Pattern_Of_Atom    of left_pattern * right_pattern;
datatype pattern_of_a_param             = Pattern_Of_A_Param of pattern_of_a_param_in_a_clause Matrix.column; 
datatype pattern_of_a_const             = Pattern_Of_A_Const of pattern_of_a_param_in_a_clause Matrix.row_of_columns_matrix;

end;