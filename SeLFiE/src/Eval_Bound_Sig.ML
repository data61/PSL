(*  Title:      PSL/SeLFeE/src/Eval_Bound_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_BOUND =
sig

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Connective of Eval_Connective.assert
| Assert     of Eval_Full_Path.assert;

val de_Connective: expr -> Eval_Connective.assert;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;

val eval: full_path_to_fpunode_table -> expr -> expr;

end;