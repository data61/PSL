(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Deep.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_DEEP =
sig

type outer_path;
type inner_path;
type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;
type qtyp    = SeLFiE_Util.qtyp;

datatype outer_parameter =
  Outer_Bool    of bool
| Outer_Path    of outer_path
| Outer_Print   of print
| Outer_String  of string
| Outer_Number  of number
| Outer_Int     of int
| Outer_Command of command;

datatype inner_parameter =
  Inner_Bool    of bool
| Inner_Path    of inner_path
| Inner_Print   of print
| Inner_String  of string
| Inner_Number  of number
| Inner_Int     of int
| Inner_Command of command;

datatype outer_expression =
  Outer_Variable of string
| Outer_Lambdas  of strings * outer_expression
| Outer_Applies  of outer_expression * outer_expression list
| Outer_Literal  of outer_parameter
| Outer_Assert   of SeLFiE_Util.assert * outer_expression list
| Outer_Alls     of (string * qtyp) list * outer_expression
| Outer_Somes    of (string * qtyp) list * outer_expression
| Dive_In        of (outer_expression * inner_expression * outer_expression list)
and inner_expression =
  Inner_Variable of string
| Inner_Lambdas  of strings * inner_expression
| Inner_Applies  of inner_expression    * inner_expression list
| Inner_Literal  of inner_parameter
| Inner_Assert   of SeLFiE_Util.assert * inner_expression list
| Inner_Alls     of (string * qtyp) list * inner_expression
| Inner_Somes    of (string * qtyp) list * inner_expression
| Dive_Deeper    of (inner_expression * inner_expression * inner_expression list);

val eval_inner: Proof.state -> SeLFiE_Util.induct_arguments -> inner_expression -> term -> inner_expression;
val eval_outer: Proof.state -> SeLFiE_Util.induct_arguments -> outer_expression -> term -> outer_expression;

datatype expr = Outer of outer_expression | Inner of inner_expression;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;