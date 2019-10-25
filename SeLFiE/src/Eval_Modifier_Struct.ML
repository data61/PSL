(*  Title:      PSL/SeLFiE/src/Eval_Modifier_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Modifier: EVAL_MODIFIER =
struct

structure EQC  = Eval_Quantifier_Core;
structure FPTF = Full_Path_To_Fpunode;
structure EP   = Eval_Parameters;
structure EE   = Eval_Expression;

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule;

datatype modifier = 
  Ind  of string
| Arb  of string
| Rule of string;

val pst_to_ind_domain = undefined: Proof.state -> modifier -> Eval_Parameters.parameters;

datatype expr =
  Var        of string
| Lambda     of string * expr
| Apply      of expr   * expr
| Literal    of EE.parameter
| Assert     of EE.assert     * expr list
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

fun convert_result (EQC.Literal ee_bool) = Literal ee_bool
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