(*  Title:      PSL/MiLkMaId_LiFtEr/Pattern_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

ML types and operations to describe patterns of constant definitions in Isabelle/HOL.
*)

(*** Pattern ***)
structure Pattern:PATTERN =
struct

open Matrix;
structure IU = Isabelle_Utils;

(** type: command **)
datatype command  = Definition | Fun | Function | Inductive | Primrec | Unknown;

(** operation: command **)
fun has_rule_with_suffix (ctxt:Proof.context) (cnst_name:string) (suffix:string) =
  can (Proof_Context.get_thms ctxt) (cnst_name ^ "." ^ suffix);

fun has_no_rule_with_suffix (ctxt:Proof.context) (cnst_name:string) (suffix:string) =
  can (Proof_Context.get_thms ctxt) (cnst_name ^ "." ^ suffix) |> not;

(*TODO*)val suffix_for_definition = (["_def"], ["cases", "elims", "induct", "simps", "intros"]);
val suffix_for_fun =       (["cases", "elims", "induct", "pelims", "simps"], ["inducts", "intros"]);(*The "fun" keyword produces psimps.*)
val suffix_for_function =  (["cases", "pelims", "psimps"], ["elims", "simps", "intros"]);
val suffix_for_primrec =   (["simps"], ["cases", "pelims", "psimps","elims", "intros"]);
val suffix_for_inductive = (["cases", "induct", "inducts", "intros", "simps"], ["pelims", "elims"]);
(*TODO*)val suffix_for_inductive_set = suffix_for_inductive;
(* Note that the "inductive_set" keyword creates "_eq" as well. But it is computationally expensive
 * to check the existence of this sort of derived lemma because we have to use regular expression.
 * Instead of this, we should check the type of this constant. *)

type suffixes = (string list * string list);

fun check_suffix (ctxt:Proof.context) (cnst_name:string) ((haves, donts): suffixes) =
   (map (has_rule_with_suffix ctxt cnst_name) haves @  (map (has_no_rule_with_suffix ctxt cnst_name) donts))
  |> filter_out I
  |> null;

fun get_command (ctxt:Proof.context) (trm_name:string) =
  let
    val check_suffix  = check_suffix ctxt trm_name;
    val is_fun        = check_suffix suffix_for_fun;
    val is_function   = check_suffix suffix_for_function;
    val is_primrec    = check_suffix suffix_for_primrec;
    val is_inductive  = check_suffix suffix_for_inductive;
    val checks        = [is_primrec, is_fun, is_function, is_inductive]: bool list;
  in
    (if checks = [true,  false, false, false] then Primrec   else
     if checks = [false, true,  false, false] then Fun       else
     if checks = [false, false, true,  false] then Function  else
     if checks = [false, false, false, true ] then Inductive else
     Unknown)
  end;

(** type: pattern **)
datatype hol_typ                        = Fun_Typ | List_Typ | Nat_Typ | Int_Typ | Set_Typ (*TODO:| Rec_Typ*);(*commonly used HOL types*)

(* pattern of the left-hand side of the definition *)
datatype left_pattern                   = Only_Var | Data_Constructor_WO_Var | Data_Constructor_W_Var | Unknown_Left;

(* pattern of the right-hand side of the definition *)
datatype at_which_position_in_rec_call  = Same_Arg_Pos      | Diff_Arg_Pos;
datatype is_the_entire_arg_in_rec_call  = Is_The_Entire_Arg | Is_Not_The_Entire_Arg;
datatype is_in_recurisve_call           = Recursion of at_which_position_in_rec_call * is_the_entire_arg_in_rec_call;
type     is_in_recurisve_calls          = is_in_recurisve_call list;
datatype is_in_if_condition             = Is_In_If_Condition   | Is_Not_In_If_Condition;
datatype is_in_case_condition           = Is_In_Case_Condition | Is_Not_In_Case_Condition;
datatype right_occ_pattern              = Right_Occ_Pattern  of {in_if:is_in_if_condition, in_case:is_in_case_condition, in_recs: is_in_recurisve_calls};
datatype right_pattern                  = Right_Pattern      of right_occ_pattern list;

(* pattern of each constant *)
datatype pattern_of_a_param_in_a_clause = Pattern_Of_Atom of left_pattern (*TODO: right_pattern*);
datatype pattern_of_a_param             = Pattern_Of_A_Param of pattern_of_a_param_in_a_clause Matrix.row;
datatype pattern_matrix                 = Pattern_Matrix of pattern_of_a_param_in_a_clause Matrix.column_of_rows_matrix;
datatype pattern_of_a_const(*TODO:term?*)= Pattern_Of_A_Const of
                                          {(*TODO:hol_typ*)
                                           matrix: pattern_matrix};

(** operation: assertion **)

(* is_head_Const *)
fun is_head_Const (Const _)  = true
 |  is_head_Const (trm1 $ _) = is_head_Const trm1
 |  is_head_Const _          = false

(* trm_to_left_pattern *)
fun trm_to_left_pattern (Var _)   = Only_Var
  | trm_to_left_pattern (Const _) = Data_Constructor_WO_Var
  | trm_to_left_pattern (_ $ _)   = Data_Constructor_W_Var
  | trm_to_left_pattern  _        = Unknown_Left;

(*TODO: rename are_var_of_const' and are_var_of_const.*)
fun are_var_of_const' (acc:left_pattern list) (trm1 $ trm2:term) = are_var_of_const' (trm_to_left_pattern trm2 :: acc) trm1
 |  are_var_of_const' (acc:left_pattern list) (trm:term)         = trm_to_left_pattern trm :: acc;

val are_var_of_const = are_var_of_const' []: term -> left_pattern list;

(* get_left *)
fun get_left (trm:term): term option =
    try HOLogic.dest_Trueprop trm
>>= try HOLogic.dest_eq
>>= try fst;

(* get_many *)
fun get_many (ctxt:Proof.context) (name:string) (getter:term -> term option) : term list =
   try (Proof_Context.get_thms ctxt) name
|> these
|> map Thm.prop_of
|> map getter
|> Utils.somes;

(* get_lefts *)
fun get_lefts (ctxt:Proof.context) (name:string) = get_many ctxt name get_left: term list;

(* terms_to_pattern_matrix *)
fun terms_to_pattern_matrix (terms:terms) = terms
 |> map are_var_of_const
 |> map List.tl
 |> Matrix.matrix_to_column_of_rows_matrix
 |> Matrix.map_crmatrix Pattern_Of_Atom
 |> Pattern_Matrix;
(*
 |> Matrix.matrix_to_row_of_columns_matrix
 |> Matrix.map_rcmatrix Pattern_Of_Atom
 |> Pattern_Matrix;
*)

(* type: mk_parameter_matrix *)
type mk_pattern_matrix = Proof.context -> string -> pattern_matrix;

(* mk_pattern_matrix_for_function *)
fun mk_pattern_matrix_for_function (ctxt:Proof.context) (cname:string) =
   try (Proof_Context.get_thms ctxt) (cname ^ ".psimps") |> these
|> map Thm.prop_of
|> map Logic.strip_imp_concl
|> map get_left
|> Utils.somes
|> terms_to_pattern_matrix;

(* mk_pattern_matrix_for_primrec *)
fun mk_pattern_matrix_for_primrec (ctxt:Proof.context) (cname:string) =
   get_lefts ctxt (cname ^ ".simps")
|> terms_to_pattern_matrix;

(* mk_pattern_matrix_for_fun *)
fun mk_pattern_matrix_for_fun (ctxt:Proof.context) (cname:string) = mk_pattern_matrix_for_primrec ctxt cname;

(* mk_pattern_matrix_for_induct *)
fun mk_pattern_matrix_for_inductive (ctxt:Proof.context) (cname:string) =
   try (Proof_Context.get_thms ctxt) (cname ^ ".intros") |> these
|> map Thm.prop_of
|> map Logic.strip_imp_concl
|> map HOLogic.dest_Trueprop
|> terms_to_pattern_matrix;

(* mk_pattern_matrix *)
fun mk_pattern_matrix (ctxt:Proof.context) (cname:string) =
  let
    val command = get_command ctxt cname: command;
    val result = case command of
        Primrec   => mk_pattern_matrix_for_primrec   ctxt cname
      | Fun       => mk_pattern_matrix_for_fun       ctxt cname
      | Function  => mk_pattern_matrix_for_function  ctxt cname
      | Inductive => mk_pattern_matrix_for_inductive ctxt cname
      | _(*TODO*) => (Matrix.empty_crmatrix |> Matrix.map_crmatrix Pattern_Of_Atom |> Pattern_Matrix)
  in
    result: pattern_matrix
  end;

datatype recursive_or_inductive_clause  = Rec_Or_Ind  of bool;
datatype recursive_or_inductive_clauses = Rec_Or_Inds of recursive_or_inductive_clause column;
(*TODO*)

fun ctxt_n_cname_to_rec_or_inds_option (ctxt:Proof.context) (cname:string) =
  let
    (*TODO*)
  in
    undefined
  end;

fun has_recursive_simp_or_psimp_about_const_name (ctxt:Proof.context) (cname:string) =
  let
    val command = get_command ctxt cname: command;
    val result = case command of
        Primrec   => IU.has_recursive_simp_about_const_name  ctxt cname
      | Fun       => IU.has_recursive_simp_about_const_name  ctxt cname
      | Function  => IU.has_recursive_psimp_about_const_name ctxt cname
      | Inductive => IU.has_recursive_simp_about_const_name  ctxt cname
      | _ (*TODO: inductive_set*) => false
  in result end;

(* TODO: The "function" keyword produces psimp-rules instead of simp rules.
 * psimp-rules have assumptions before equations.
 * So, we cannot use Isabelle_Utils.has_recursive_simp_about_const_name.
 * We have to define has_recursive_psimp_about_const_name in Utils.ML.  *)

fun ctxt_n_cname_to_pattern_of_a_const (ctxt:Proof.context) (cname:string) =
  let
    val pattern_matrix     = mk_pattern_matrix ctxt cname                           : pattern_matrix;
    val pattern_of_a_const = Pattern_Of_A_Const
         {matrix    = pattern_matrix}: pattern_of_a_const;
  in
    pattern_of_a_const
  end;

fun ctxt_n_name_to_patterns_of_each_param (ctxt:Proof.context) (cname:string) =
  let
    val Pattern_Matrix  pattern_matrix         = mk_pattern_matrix ctxt cname;
    val Matrix.CRMatrix columns_of_each_param  = pattern_matrix;
    val Matrix.Column   patterns_of_each_param = columns_of_each_param;
  in
    map Pattern_Of_A_Param patterns_of_each_param: pattern_of_a_param list
  end;

(*TODO: re-factor these. Probably Matrix.crmatrix_to_nth_column should return an option type.*)
fun is_nth_all_Only_Var (ctxt:Proof.context) (cname:string) (n:int) =
  let
    val Pattern_Matrix crmatrix   = mk_pattern_matrix ctxt cname                           : pattern_matrix;
    val nth_column_as_list_option = try (crmatrix_to_nth_column crmatrix) n <$> dest_column;
    fun is_Only_Var (Pattern_Of_Atom Only_Var)  = true
      | is_Only_Var  _                          = false;
    val nth_param_is_all_Only_Var = nth_column_as_list_option <$> forall is_Only_Var |> Utils.is_some_true: bool;
  in
    nth_param_is_all_Only_Var: bool
  end;

fun is_nth_all_Data_Constructor_W_Var (ctxt:Proof.context) (cname:string) (n:int) =
  let
    val Pattern_Matrix crmatrix   = mk_pattern_matrix ctxt cname                           : pattern_matrix;
    val nth_column_as_list_option = try (crmatrix_to_nth_column crmatrix) n <$> dest_column;
    fun is_Data_Constructor_W_Var (Pattern_Of_Atom Data_Constructor_W_Var) = true
      | is_Data_Constructor_W_Var  _                                       = false;
    val nth_param_is_all_Only_Var = nth_column_as_list_option <$> forall is_Data_Constructor_W_Var |> Utils.is_some_true: bool;
  in
    nth_param_is_all_Only_Var: bool
  end;

fun is_nth_all_Data_Constructor_WO_Var (ctxt:Proof.context) (cname:string) (n:int) =
  let
    val Pattern_Matrix crmatrix   = mk_pattern_matrix ctxt cname                           : pattern_matrix;
    val nth_column_as_list_option = try (crmatrix_to_nth_column crmatrix) n <$> dest_column;
    fun is_Data_Constructor_W_Var (Pattern_Of_Atom Data_Constructor_WO_Var) = true
      | is_Data_Constructor_W_Var  _                                        = false;
    val nth_param_is_all_Only_Var = nth_column_as_list_option <$>  forall is_Data_Constructor_W_Var |> Utils.is_some_true: bool;
  in
    nth_param_is_all_Only_Var: bool
  end;

fun is_nth_all_Data_Constructor_W_or_WO_Var (ctxt:Proof.context) (cname:string) (n:int) =
  let
    val Pattern_Matrix crmatrix   = mk_pattern_matrix ctxt cname                           : pattern_matrix;
    val nth_column_as_list_option = try (crmatrix_to_nth_column crmatrix) n <$> dest_column;
    fun is_Data_Constructor_W_Var (Pattern_Of_Atom Data_Constructor_W_Var)  = true
      | is_Data_Constructor_W_Var (Pattern_Of_Atom Data_Constructor_WO_Var) = true
      | is_Data_Constructor_W_Var  _                                        = false;
    val nth_param_is_all_Only_Var = nth_column_as_list_option <$> forall is_Data_Constructor_W_Var |> Utils.is_some_true: bool;
  in
    nth_param_is_all_Only_Var: bool
  end;

fun is_nth_Var_n_Constructor (ctxt:Proof.context) (cname:string) (n:int) =
  not (is_nth_all_Only_Var ctxt cname n) andalso not (is_nth_all_Data_Constructor_W_or_WO_Var ctxt cname n);

end;