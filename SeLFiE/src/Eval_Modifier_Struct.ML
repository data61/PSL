(*  Title:      PSL/SeLFiE/src/Eval_Modifier_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Modifier: EVAL_MODIFIER =
struct

structure EQC  = Eval_Quantifier_Core;
structure FPTF = Full_Path_To_Fpunode;
structure EP   = Eval_Parameters;

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule;

datatype modifier = 
  Ind  of string
| Arb  of string
| Rule of string;

val pst_to_ind_domain = undefined: Proof.state -> modifier -> Eval_Parameters.parameters;

(* TODO: I have to have extra atomic assertions about rule.
 *       Therefore, we cannot use the fixed type Eval_Parameters.assert in Assert.
 *       We have to use a type class (= module) for assert.
 *       This means that I have to define
 *        - Eval_Bound_Struct, 
 *        - Eval_Var_Struct, and
 *        - Eval_Quantifier_Core_Struct
 *       as functors.
 *)
datatype expr =
  Var        of string
| Lambda     of string * expr
| Apply      of expr   * expr
| Literal    of Eval_Parameters.parameter
| Assert     of Eval_Parameters.assert * expr list
| All        of string * qtyp * expr
| Some       of string * qtyp * expr;

(*TODO:*)
(*convert_parameter *)

(*TODO: Double-check if I can treat a rule as a print.*)
fun convert_qtyp QFull_Path = EQC.QFull_Path
  | convert_qtyp QPrint     = EQC.QPrint
  | convert_qtyp QInd       = EQC.QPrint
  | convert_qtyp QArb       = EQC.QPrint
  | convert_qtyp QRule      = EQC.QPrint;

fun convert_expr (Var        vname                 ) = EQC.Var         vname
  | convert_expr (Lambda    (vname, subexpr)       ) = EQC.Lambda     (vname, convert_expr subexpr)
  | convert_expr (Apply      pair                  ) = EQC.Apply      (apply2 convert_expr pair)
  | convert_expr (Literal    ps                    ) = EQC.Literal     ps
  | convert_expr (Assert     (assrt, ps)           ) = EQC.Assert     (assrt, map convert_expr ps)
  | convert_expr (All        (vname, qtyp, subexpr)) = EQC.All        (vname, convert_qtyp qtyp, convert_expr subexpr)
  | convert_expr (Some       (vname, qtyp, subexpr)) = EQC.Some       (vname, convert_qtyp qtyp, convert_expr subexpr);

fun convert_result (EQC.Literal (EP.Connective connect)) = Literal (EP.Connective connect)
  | convert_result  _ =
    error "eval in Eval_Quantifier_Struct failed. Evaluation is not complete.";

fun eval pst (expr:expr) = 
  let
    val full_path_to_fpunode_table = FPTF.pst_to_full_path_to_fpunode_table pst: FPTF.full_path_to_fpunode_table;
    val print_to_paths_table       = Print_To_Full_Paths.full_path_to_fpunode_table_to_print_to_paths_table full_path_to_fpunode_table;
    val eqc_result                 = convert_expr expr |> EQC.eval full_path_to_fpunode_table print_to_paths_table
                                   : Eval_Quantifier_Core.expr;
    val result = convert_result eqc_result: expr;
  in
    result
  end;

end;