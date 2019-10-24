(*  Title:      PSL/SeLFiE/src/Eval_Quantifier_Core_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Quantifier_Core: EVAL_QUANTIFIER_CORE =
struct

structure EV = Eval_Var;
structure EE = Eval_Expression;

datatype qtyp = QFull_Path | QPrint;(*| QNumb TODO*)

datatype expr =
  Var        of string
| Lambda     of string * expr
| Apply      of expr * expr
| Literal    of EE.parameter
| Assert     of EE.assert * expr list
| All        of string * qtyp * expr
| Some       of string * qtyp * expr;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;
type print_to_full_paths_table  = full_path list Print_Table.table;

fun convert_result (EV.Literal ee_bool) = Literal ee_bool
  | convert_result  _ = error "eval in Eval_Quantifier_Struct failed. Evaluation is not complete.";

fun eval (fpun_table:full_path_to_fpunode_table) (fps_table:print_to_full_paths_table) expr =
  let
    val all_full_paths = Full_Path_Table.keys fpun_table: full_path list;
    val all_prints     = Print_Table.keys     fps_table : LiFtEr_Util.prints;
    fun vname_n_subexpr_n_qtyp_to_apps (vname:string) (subexpr:expr) (qtyp:qtyp) =
      let
        val params = case qtyp of
          QFull_Path => map EE.Full_Path all_full_paths: EE.parameters
        | QPrint     => map EE.Print     all_prints    : EE.parameters;
        val apps = map (fn param => Apply (Lambda (vname, subexpr), Literal param)) params: expr list;
      in
        Assert (EE.Ands, apps): expr
      end;
    fun eval' (Var vname)                   = EV.eval fpun_table (EV.Var vname)
      | eval' (Lambda (vname, subexpr))     = EV.eval fpun_table (EV.Lambda (vname, eval' subexpr))
      | eval' (Apply  pair)                 = EV.eval fpun_table (EV.Apply (apply2 eval' pair))
      | eval' (Literal   ps)                = EV.eval fpun_table (EV.Literal ps)
      | eval' (Assert (assrt, ps))          = EV.eval fpun_table (EV.Assert (assrt, map eval' ps))
      | eval' (All  (vname, qtyp, subexpr)) = eval' (vname_n_subexpr_n_qtyp_to_apps vname subexpr qtyp)
      | eval' (Some (vname, qtyp, subexpr)) = eval' (Assert (EE.Not, [All (vname, qtyp, Assert (EE.Not, [subexpr]))]))
    val ev_result  = eval' expr              : Eval_Var.expr;
    val result     = convert_result ev_result: expr;
  in
    result
  end;

end;