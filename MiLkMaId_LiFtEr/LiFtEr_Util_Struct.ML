(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Util_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Helper functions for LiFtEr.
*)

(*** Pattern ***)
structure Pattern:PATTERN =
struct

(* command *)
datatype command                        = Definition | Fun | Function | Inductive | Primrec | Unknown;
datatype hol_typ                        = Fun_Typ | List_Typ | Nat_Typ | Int_Typ | Set_Typ (*TODO:| Rec_Typ*);(*commonly used HOL types*)
datatype left_pattern                   = Only_Var | Data_Constructor_WO_Var | Data_Constructor_W_Var;
datatype pattern_of_a_param_in_a_clause = Pattern_Of_Atom of left_pattern (*TODO: right_pattern*);
datatype pattern_of_a_param             = Pattern_Of_A_Param of pattern_of_a_param_in_a_clause Matrix.column;
datatype pattern_of_a_const(*TODO:term?*) = Pattern_Of_A_Const of
                                          {(*hol_typ*)
                                           matrix : pattern_of_a_param_in_a_clause Matrix.row_of_columns_matrix};

end;

(*** LiFtEr_Util ***)
structure LiFtEr_Util: LIFTER_UTIL =
struct

type     path  = ints;
(* print: the printed format of a sub-tree in the syntax tree of a term. *)
datatype print = Print of string;

end;

(*** Test_Lifter ***)
structure Test_LiFtEr: TEST_LIFTER =
struct

open LiFtEr_Util;

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