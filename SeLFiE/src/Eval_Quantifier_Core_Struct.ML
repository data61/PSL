(*  Title:      PSL/LiFtEr/src/Eval_Quantifier_Core_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The syntax and interpreter of LiFtEr, Logical Feature Extractor for MiLkMaId.
*)
structure Eval_Quantifier_Core: EVAL_QUANTIFIER_CORE =
struct

structure EV = Eval_Var;
structure EP = Eval_Parameters;

datatype qtyp = QFull_Path | QPrint;(*| QNumb*)

datatype expr =
  Var        of string
| Lambda     of string * expr
| Apply      of expr * expr
| Connective of Eval_Connective.assert
| Literal    of Eval_Parameters.parameter
| Assert     of Eval_Parameters.assert * expr list
| All        of string * qtyp * expr
| Some       of string * qtyp * expr;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;
type print_to_full_paths_table  = full_path list Print_Table.table;

fun vname_n_lit_n_expr_to_app (vname:string) (expr:expr) (param:Eval_Parameters.parameter) =
  Apply (Lambda (vname, expr), Literal param): expr;

fun vname_n_subexpr_domain_to_apps (vname:string) (subexpr:expr) (domain:Eval_Parameters.parameters) =
  let
    val apps = map (vname_n_lit_n_expr_to_app vname subexpr) domain: expr list;
  in
    Assert (EP.Ands, apps): expr
  end;

fun eval (fpun_table:full_path_to_fpunode_table) (fps_table:print_to_full_paths_table) expr =
  let
    val all_full_paths = Full_Path_Table.keys fpun_table : full_path list;
    val all_prints     = Print_Table.keys     fps_table  : LiFtEr_Util.prints;
    fun eval' (Var vname)                            = EV.eval fpun_table (EV.Var vname)
      | eval' (Lambda (vname, subexpr))              = EV.eval fpun_table (EV.Lambda (vname, eval' subexpr))
      | eval' (Apply  pair)                          = EV.eval fpun_table (EV.Apply (apply2 eval' pair))
      | eval' (Connective c)                         = EV.eval fpun_table (EV.Connective c)
      | eval' (Literal   ps)                         = EV.eval fpun_table (EV.Literal ps)
      | eval' (Assert (assrt, ps))                   = EV.eval fpun_table (EV.Assert (assrt, map eval' ps))
      | eval' (All  (vname, QFull_Path, subexpr))    = eval' (vname_n_subexpr_domain_to_apps vname subexpr (map EP.Full_Path all_full_paths))
      | eval' (All  (vname, QPrint,     subexpr))    = eval' (vname_n_subexpr_domain_to_apps vname subexpr (map EP.Print     all_prints    ))
      | eval' (Some (vname, QFull_Path, subexpr))    = 
        eval' (Assert (EP.Not, [All (vname, QFull_Path, Assert (EP.Not, [subexpr]))]))
      | eval' (Some (vname, QPrint,     subexpr))    =
        eval' (Assert (EP.Not, [All (vname, QPrint, Assert (EP.Not, [subexpr]))]));
  in
    eval' expr |> EV.de_Connective |> Connective              
  end;

end;