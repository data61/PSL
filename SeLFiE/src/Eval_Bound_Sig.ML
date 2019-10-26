(*  Title:      PSL/SeLFeE/src/Eval_Bound_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_BOUND =
sig

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Literal    of Eval_Expression.parameter
| Assert     of Eval_Expression.assert * expr list;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;
type modifiers                  = Eval_Modifier.modifiers;

val eval: full_path_to_fpunode_table -> modifiers -> expr -> expr;

end;