(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Multi_Arity.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_MULTI_ARITY =
sig

type path;

datatype parameter = Path of path | Non_Path of SeLFiE_Util.non_path_parameter;

datatype expr =
  Variable of string
| Lambdas  of strings * expr
| Applies  of expr    * expr list
| Literal  of parameter
| Assert   of SeLFiE_Util.assert * expr list
| Alls     of (string * SeLFiE_Util.qtyp) list * expr
| Somes    of (string * SeLFiE_Util.qtyp) list * expr;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;