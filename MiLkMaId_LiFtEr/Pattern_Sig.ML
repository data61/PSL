(*  Title:      PSL/MiLkMaId_LiFtEr/Pattern_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

ML types and operations to describe patterns of constant definitions in Isabelle/HOL.
*)

(*** PATTERN ***)
signature PATTERN =
sig

(** type and operation about command **)
datatype command                        = Definition | Fun | Function | Inductive | Primrec | Unknown;
val get_command                         : Proof.context -> string -> command;

(** pattern **)
datatype hol_typ                        = Fun_Typ | List_Typ | Nat_Typ | Int_Typ | Set_Typ (*TODO:| Rec_Typ*);(*commonly used HOL types*)

(* type: pattern of the left-hand side of the definition *)
datatype left_pattern                   = Only_Var | Data_Constructor_WO_Var | Data_Constructor_W_Var | Unknown_Left;

(* type: pattern of the right-hand side of the definition *)
datatype at_which_position_in_rec_call  = Same_Arg_Pos      | Diff_Arg_Pos;
datatype is_the_entire_arg_in_rec_call  = Is_The_Entire_Arg | Is_Not_The_Entire_Arg;
datatype is_in_recurisve_call           = Recursion of at_which_position_in_rec_call * is_the_entire_arg_in_rec_call;
type     is_in_recurisve_calls          = is_in_recurisve_call list;
datatype is_in_if_condition             = Is_In_If_Condition   | Is_Not_In_If_Condition;
datatype is_in_case_condition           = Is_In_Case_Condition | Is_Not_In_Case_Condition;
datatype right_occ_pattern              = Right_Occ_Pattern  of {in_if:is_in_if_condition, in_case:is_in_case_condition, in_recs: is_in_recurisve_calls};
datatype right_pattern                  = Right_Pattern      of right_occ_pattern list;

(* type: pattern of each constant *)
datatype pattern_of_a_param_in_a_clause = Pattern_Of_Atom    of left_pattern (*TODO: right_pattern*);
datatype pattern_of_a_param             = Pattern_Of_A_Param of pattern_of_a_param_in_a_clause Matrix.row;
datatype pattern_matrix                 = Pattern_Matrix     of pattern_of_a_param_in_a_clause Matrix.column_of_rows_matrix;
datatype pattern_of_a_const(*TODO:term?*) = Pattern_Of_A_Const of
                                          {(*TODO:hol_typ*)
                                           matrix    : pattern_matrix,
                                           recursive:  bool};

(* type: mk_parameter_matrix *)
type mk_pattern_matrix = Proof.context -> string -> pattern_matrix;

(* operation: mk_parameter_matrix *)
val mk_pattern_matrix_for_fun       : mk_pattern_matrix;
val mk_pattern_matrix_for_function  : mk_pattern_matrix;
val mk_pattern_matrix_for_inductive : mk_pattern_matrix;
val mk_pattern_matrix_for_primrec   : mk_pattern_matrix;
val mk_pattern_matrix               : mk_pattern_matrix;

val has_recursive_simp_or_psimp_about_const_name: Proof.context -> string -> bool;
val ctxt_n_cname_to_pattern_of_a_const          : Proof.context -> string -> pattern_of_a_const;

(** assertion **)
(* assertion on the nth argument *)
val ctxt_n_name_to_patterns_of_each_param  : Proof.context -> string -> pattern_of_a_param list;
val is_nth_all_Only_Var                    : Proof.context -> string -> int -> bool;
val is_nth_all_Data_Constructor_W_Var      : Proof.context -> string -> int -> bool;
val is_nth_all_Data_Constructor_WO_Var     : Proof.context -> string -> int -> bool;
val is_nth_all_Data_Constructor_W_or_WO_Var: Proof.context -> string -> int -> bool;

end;