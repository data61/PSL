(*  Title:      PSL/SeLFeE/src/Eval_Var_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_VAR =
sig

datatype expr =
  Var        of string
| Lambda     of string * expr
| Apply      of expr   * expr
| Connective of Eval_Connective.assert
| Literal    of Eval_Parameters.parameter
| Assert     of Eval_Parameters.assert * expr list;

val de_Connective: expr -> Eval_Connective.assert;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;

val eval: full_path_to_fpunode_table -> expr -> expr;

end;