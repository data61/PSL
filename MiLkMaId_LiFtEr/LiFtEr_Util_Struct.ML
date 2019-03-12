(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Util_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Helper functions for LiFtEr.
*)

(*** Pattern ***)
structure Pattern:PATTERN =
struct

(** type: command **)
datatype command  = Definition | Fun | Function | Inductive | Primrec | Unknown;

(** operations: command **)
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

(** types: pattern **)
datatype hol_typ                        = Fun_Typ | List_Typ | Nat_Typ | Int_Typ | Set_Typ (*TODO:| Rec_Typ*);(*commonly used HOL types*)
datatype left_pattern                   = Only_Var | Data_Constructor_WO_Var | Data_Constructor_W_Var;
datatype pattern_of_a_param_in_a_clause = Pattern_Of_Atom of left_pattern (*TODO: right_pattern*);
datatype pattern_of_a_param             = Pattern_Of_A_Param of pattern_of_a_param_in_a_clause Matrix.column;
datatype pattern_of_a_const(*TODO:term?*)= Pattern_Of_A_Const of
                                          {(*hol_typ*)
                                           matrix : pattern_of_a_param_in_a_clause Matrix.row_of_columns_matrix};
datatype pattern_matrix                 = Pattern_Matrix of pattern_of_a_param_in_a_clause Matrix.row_of_columns_matrix;

(** operations: pattern **)

(* get_left: get left-hand-sides *)
fun get_left (trm:term) =
    try HOLogic.dest_Trueprop trm
>>= try HOLogic.dest_eq
>>= try fst

(* is_head_Const *)
fun is_head_Const (Const _)  = true
 |  is_head_Const (trm1 $ _) = is_head_Const trm1
 |  is_head_Const _          = false

(* is_var_of_const *)
(*TODO: This is not accurate. We should not ignore Data_Constructor_WO_Var. FIXME.*)
fun is_var_of_const (trm:term) = if is_head_Const trm then Data_Constructor_W_Var else Only_Var;

(*TODO: This is not accurate. We should not ignore Data_Constructor_WO_Var. *)
fun are_var_of_const' (acc:left_pattern list) (trm1 $ trm2:term) = are_var_of_const' (is_var_of_const trm2 :: acc) trm1
 |  are_var_of_const' (acc:left_pattern list) (trm:term)         = is_var_of_const trm :: acc;

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
 |> Matrix.matrix_to_row_of_columns_matrix
 |> Matrix.map_rcmatrix Pattern_Of_Atom
 |> Pattern_Matrix

(* mk_parameter_matrix_for_function *)
fun mk_parameter_matrix_for_function (ctxt:Proof.context) (cname:string) =
   try (Proof_Context.get_thms ctxt) (cname ^ ".intros") |> these
|> (fn these_list => (length these_list |> Int.toString |> tracing; these_list))
|> map Thm.prop_of
|> map Logic.strip_imp_concl
|> map get_left
|> Utils.somes
|> terms_to_pattern_matrix;

(* mk_parameter_matrix_for_primrec *)
fun mk_parameter_matrix_for_primrec (ctxt:Proof.context) (cname:string) =
   get_lefts ctxt (cname ^ ".simps")
|> terms_to_pattern_matrix;

(* mk_parameter_matrix_for_fun *)
fun mk_parameter_matrix_for_fun (ctxt:Proof.context) (cname:string) = mk_parameter_matrix_for_primrec ctxt cname;

(* How to produce parameter-matrix for constants defined with "induct". *)
(* Probably intros-rules are good target: focus on the conclusions.  *)
fun get_cncl (trm:term) =
    try Logic.strip_imp_concl trm
>>= try HOLogic.dest_Trueprop

(* mk_parameter_matrix_for_induct *)
fun mk_parameter_matrix_for_inductive (ctxt:Proof.context) (cname:string) =
   try (Proof_Context.get_thms ctxt) (cname ^ ".intros") |> these
|> map Thm.prop_of
|> map Logic.strip_imp_concl
|> map HOLogic.dest_Trueprop
|> terms_to_pattern_matrix;

(* mk_parameter_matrix *)
fun mk_parameter_matrix (ctxt:Proof.context) (cname:string) =
let
  val command = get_command ctxt cname: command;
  val result = case command of
      Primrec   => mk_parameter_matrix_for_primrec   ctxt cname
    | Fun       => mk_parameter_matrix_for_fun       ctxt cname
    | Function  => mk_parameter_matrix_for_function  ctxt cname
    | Inductive => mk_parameter_matrix_for_inductive ctxt cname
    | _(*TODO*) => (Matrix.empty_rcmatrix |> Matrix.map_rcmatrix Pattern_Of_Atom |> Pattern_Matrix)
in
  result: pattern_matrix
end;

fun ctxt_n_name_to_patterns_of_each_param (ctxt:Proof.context) (cname:string) =
let
  val Pattern_Matrix  pattern_matrix         = mk_parameter_matrix ctxt cname;
  val Matrix.RCMatrix columns_of_each_param  = pattern_matrix;
  val Matrix.Row      patterns_of_each_param = columns_of_each_param;
in
  map Pattern_Of_A_Param patterns_of_each_param: pattern_of_a_param list
end;

fun is_nth_all_Only_Var (ctxt:Proof.context) (cname:string) (n:int) =
let
  val patterns_of_each_param              = ctxt_n_name_to_patterns_of_each_param ctxt cname: pattern_of_a_param list;
  (*TODO: we should use the option type to handle exceptions.*)
  val Pattern_Of_A_Param pattern_of_nth_param = nth patterns_of_each_param n: pattern_of_a_param;
  val Matrix.Column column_of_nth_param       = pattern_of_nth_param        : pattern_of_a_param_in_a_clause Matrix.column
  fun is_Only_Var (Pattern_Of_Atom Only_Var)  = true
    | is_Only_Var  _                          = false;
  val nth_param_is_all_Only_Var = forall is_Only_Var column_of_nth_param    : bool;
in
  nth_param_is_all_Only_Var: bool
end;

(*TODO: refactor patterns_of_each_param and is_nth_all_Data_Constructor_W_Var.*)
fun is_nth_all_Data_Constructor_W_Var (ctxt:Proof.context) (cname:string) (n:int) =
let
  val patterns_of_each_param              = ctxt_n_name_to_patterns_of_each_param ctxt cname: pattern_of_a_param list;
  (*TODO: we should use the option type to handle exceptions.*)
  val Pattern_Of_A_Param pattern_of_nth_param = nth patterns_of_each_param n: pattern_of_a_param;
  val Matrix.Column column_of_nth_param       = pattern_of_nth_param        : pattern_of_a_param_in_a_clause Matrix.column
  fun is_Data_Constructor_W_Var (Pattern_Of_Atom Data_Constructor_W_Var) = true
    | is_Data_Constructor_W_Var  _                                       = false;
  val nth_param_is_all_Only_Var = forall is_Data_Constructor_W_Var column_of_nth_param : bool;
in
  nth_param_is_all_Only_Var: bool
end;

end;

(*** LiFtEr_Util ***)
structure LiFtEr_Util: LIFTER_UTIL =
struct

type     path   = ints;
(* print: the printed format of a sub-tree in the syntax tree of a term. *)
datatype print  = Print of string;
type     prints = print list;
fun same_prints (Print p1) (Print p2) = p1 = p2;
end;

(*** Test_Lifter ***)
structure Test_LiFtEr: TEST_LIFTER =
struct

open LiFtEr_Util;

fun dest_print (Print str) = str;
fun is_subprint_of (Print p1) (Print p2) = String.isSubstring p1 p2;
fun ctxt_n_print_to_cname  (ctxt:Proof.context) (print:print) =
  let
    val trm_option = try dest_print print >>= try (Syntax.read_term ctxt): term   option;
    val trm_cname  = trm_option >>= try Term.dest_Const <$> fst          : string option;
  in
    trm_cname
  end;

datatype induct_on   = Ind_On   of print;
datatype induct_arb  = Ind_Arb  of print;
datatype induct_rule = Ind_Rule of string;
datatype ind_mods    = Ind_Mods of {ons: induct_on list, arbs: induct_arb list, rules: induct_rule list};

fun dest_induct_on   (Ind_On print)    = print;
fun dest_induct_arb  (Ind_Arb print)   = print;
fun dest_induct_rule (Ind_Rule string) = string;

end;