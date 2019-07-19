(*  Title:      PSL/SeLFeE/src/Eval_Var_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_VAR =
sig

datatype expr =
  Var        of string
| Lambda     of expr
| Apply      of expr * expr
| Connective of Eval_Connective.assert
| Atom       of Eval_Full_Path.assert;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;

val eval: full_path_to_fpunode_table -> expr -> expr;

end;