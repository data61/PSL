(*  Title:      PSL/SeLFeE/src/Eval_Print.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_PRINT ***)
signature EVAL_PRINT =
sig

datatype assert =
  Are_Same_Prints  of string * string
| Is_Subprint_Of   of string * string
| Is_Nth_Induct    of string * int
| Is_Nth_Arbitrary of string * int
| Is_Induct        of string
| Is_Arbitrary     of string
| Is_Rule          of string
| Is_Rule_Of_Print of string * string
(*node*)
| Print_Is_Cnst                     of string
| Print_Is_Free                     of string
| Print_Is_Var                      of string
| Print_Is_Bound                    of string (*corresponds to Bound in term*)
| Print_Is_Lambda                   of string (*lambda abstraction corresponding to Abs in Term*)
| Print_Is_App                      of string (*function application corresponding to $ in Term*)
| Print_Is_Defined_With             of string * Pattern.command
| Print_Takes_N_Arguments           of string * int
| Print_Takes_Less_Than_N_Arguments of string * int;

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
| Is_Subprint_Of   of string * string
| Is_Nth_Induct    of string * int
| Is_Nth_Arbitrary of string * int
| Is_Induct        of string
| Is_Arbitrary     of string
| Is_Rule          of string
| Is_Rule_Of_Print of string * string
(*node*)
| Print_Is_Cnst                     of string
| Print_Is_Free                     of string
| Print_Is_Var                      of string
| Print_Is_Bound                    of string (*corresponds to Bound in term*)
| Print_Is_Lambda                   of string (*lambda abstraction corresponding to Abs in Term*)
| Print_Is_App                      of string (*function application corresponding to $ in Term*)
| Print_Is_Defined_With             of string * Pattern.command
| Print_Takes_N_Arguments           of string * int
| Print_Takes_Less_Than_N_Arguments of string * int;

infix Is_Printed_As;

fun print_n_context_to_numb_of_arguments (print:string) (ctxt:Proof.context) =
     Syntax.read_term ctxt print
  |> Term.type_of
  |> Isabelle_Utils.count_numb_of_args_of_fun_typ: int;

fun eval' (Are_Same_Prints       (prnt1, prnt2))  _                                                     _    = prnt1 = prnt2
  | eval' (Is_Subprint_Of        (sub,   full))   _                                                     _    = String.isSubstring sub full
  | eval' (Is_Nth_Induct         (print, n))    (SU.Induct_Arguments {ons,   ...}: SU.induct_arguments) _    = nth ons  n = print
  | eval' (Is_Nth_Arbitrary      (print, n))    (SU.Induct_Arguments {arbs,  ...}: SU.induct_arguments) _    = nth arbs n = print
  | eval' (Is_Induct              print    )    (SU.Induct_Arguments {ons,   ...}: SU.induct_arguments) _    = member (op =) ons   print
  | eval' (Is_Arbitrary           print    )    (SU.Induct_Arguments {arbs,  ...}: SU.induct_arguments) _    = member (op =) arbs  print
  | eval' (Is_Rule                print    )    (SU.Induct_Arguments {rules, ...}: SU.induct_arguments) _    = member (op =) rules print
  | eval' (Is_Rule_Of_Print      (rule, cname))  _               ctxt = SU.rule_to_const_name ctxt rule = cname
  (*node*)
  | eval' (Print_Is_Cnst          print    )     _               ctxt = Syntax.read_term ctxt print |> is_Const
  | eval' (Print_Is_Free          print    )     _               ctxt = Syntax.read_term ctxt print |> is_Free
  | eval' (Print_Is_Var           print    )     _               ctxt = Syntax.read_term ctxt print |> is_Var
  | eval' (Print_Is_Bound         print    )     _               ctxt = Syntax.read_term ctxt print |> is_Bound
  | eval' (Print_Is_Lambda        print    )     _               ctxt = Syntax.read_term ctxt print |> Isabelle_Utils.is_Abs
  | eval' (Print_Is_App           print    )     _               ctxt = Syntax.read_term ctxt print |> Isabelle_Utils.is_App
  | eval' (Print_Is_Defined_With   (print, command)) _           ctxt = Pattern.get_command ctxt print = command
  | eval' (Print_Takes_N_Arguments (print, numb))    _           ctxt = numb = print_n_context_to_numb_of_arguments print ctxt
  | eval' (Print_Takes_Less_Than_N_Arguments (print, numb))    _ ctxt = numb < print_n_context_to_numb_of_arguments print ctxt;

fun eval  assert (ind_args:SU.induct_arguments) ctxt = eval' assert ind_args ctxt |> EB.bool_to_assert;

end;