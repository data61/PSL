(*  Title:      PSL/SeLFeE/src/Eval_Print.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_PRINT ***)
signature EVAL_PRINT =
sig

datatype assert =
  Are_Same_Prints  of string * string
| Is_Nth_Induct    of string * int
| Is_Nth_Arbitrary of string * int
| Is_Induct        of string
| Is_Arbitrary     of string
| Is_Rule          of string
| Is_Rule_Of       of string * string;

val eval: assert -> SeLFiE_Util.induct_arguments -> Proof.context -> Eval_Bool.assert;

end;

(*** Eval_Print ***)
structure Eval_Print: EVAL_PRINT =
struct

structure EB = Eval_Bool;
structure SU = SeLFiE_Util;
structure EN = Eval_Number;

datatype assert =
  Are_Same_Prints  of string * string
| Is_Nth_Induct    of string * int
| Is_Nth_Arbitrary of string * int
| Is_Induct        of string
| Is_Arbitrary     of string
| Is_Rule          of string
| Is_Rule_Of       of string * string;

fun split_using_period x = String.tokens (fn splitter => splitter = #".") x;

fun rule_to_const_name (ctxt:Proof.context) (rule:string) =
  try split_using_period rule 
<$> Utils.init
<$> String.concatWith "."
<$> Syntax.read_term ctxt
<$> Term.dest_Const
<$> fst
 |> Utils.the' "rule_to_const_name failed.";

infix Is_Printed_As;

fun eval' (Are_Same_Prints (prnt1, prnt2))  _                                                      _    = prnt1 = prnt2
  | eval' (Is_Nth_Induct    (print, n))    (SU.Induct_Arguments {ons,   ...}: SU.induct_arguments) _    = nth ons  n = print
  | eval' (Is_Nth_Arbitrary (print, n))    (SU.Induct_Arguments {arbs,  ...}: SU.induct_arguments) _    = nth arbs n = print
  | eval' (Is_Induct         print    )    (SU.Induct_Arguments {ons,   ...}: SU.induct_arguments) _    = member (op =) ons   print
  | eval' (Is_Arbitrary      print    )    (SU.Induct_Arguments {arbs,  ...}: SU.induct_arguments) _    = member (op =) arbs  print
  | eval' (Is_Rule           print    )    (SU.Induct_Arguments {rules, ...}: SU.induct_arguments) _    = member (op =) rules print
  | eval' (Is_Rule_Of       (rule, cname))  _                                                      ctxt = rule_to_const_name ctxt rule = cname

fun eval  assert (ind_args:SU.induct_arguments) ctxt = eval' assert ind_args ctxt |> EB.bool_to_assert;

end;