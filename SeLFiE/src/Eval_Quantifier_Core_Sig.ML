(*  Title:      PSL/SeLFiE/src/Eval_Quantifier_Core_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_QUANTIFIER_CORE =
sig

datatype qtyp = QFull_Path | QPrint;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;
type print_to_full_paths_table  = full_path list Print_Table.table;

datatype expr =
  Var        of string
| Lambda     of string * expr
| Apply      of expr * expr
| Literal    of Eval_Expression.parameter
| Assert     of Eval_Expression.assert * expr list
| All        of string * qtyp * expr
| Some       of string * qtyp * expr;

val eval: full_path_to_fpunode_table -> print_to_full_paths_table -> expr -> expr;

end;