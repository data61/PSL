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
| Is_Set           of string
| Is_Set_Of_Print  of string * string
(*node*)
| Print_Is_Cnst                     of string
| Print_Is_Free                     of string
| Print_Is_Var                      of string
| Print_Is_Bound                    of string (*corresponds to Bound in term*)
| Print_Is_Lambda                   of string (*lambda abstraction corresponding to Abs in Term*)
| Print_Is_App                      of string (*function application corresponding to $ in Term*)
| Print_Is_Defined_With             of string * Definition_Pattern.command
| Print_Is_Defined_With_N_Clauses   of string * int
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
| Is_Set           of string
| Is_Set_Of_Print  of string * string
(*node*)
| Print_Is_Cnst                     of string
| Print_Is_Free                     of string
| Print_Is_Var                      of string
| Print_Is_Bound                    of string (*corresponds to Bound in term*)
| Print_Is_Lambda                   of string (*lambda abstraction corresponding to Abs in Term*)
| Print_Is_App                      of string (*function application corresponding to $ in Term*)
| Print_Is_Defined_With             of string * Definition_Pattern.command
| Print_Is_Defined_With_N_Clauses   of string * int
| Print_Takes_N_Arguments           of string * int
| Print_Takes_Less_Than_N_Arguments of string * int;

infix Is_Printed_As;

fun read_term ctxt print = try (Syntax.read_term ctxt) print;

fun print_n_context_to_numb_of_arguments (print:string) (ctxt:Proof.context) =
   Syntax.read_term ctxt print
|> Term.type_of
|> Isabelle_Utils.count_numb_of_args_of_fun_typ: int;

fun print_is_nth_of (print:string) (n:int) (ons_or_arb) =
    try (nth ons_or_arb) n
<$> equal print
 |> Utils.is_some_true;

fun read_term_then_check_term (ctxt:Proof.context) (print:string) (checker: term -> bool) =
    try (Syntax.read_term ctxt) print
<$> checker
 |> Utils.is_some_true

fun get_rule_names' []                                   acc = acc
  | get_rule_names' ((SU.Ind_Rule rule_name)::ind_rules) acc = get_rule_names' ind_rules (rule_name :: acc)
  | get_rule_names' ((SU.Ind_Set  _        )::ind_rules) acc = get_rule_names' ind_rules acc;

fun get_rule_names ind_rules = get_rule_names' ind_rules [];

fun get_set_names' []                                   acc = acc
  | get_set_names' ((SU.Ind_Rule _        )::ind_rules) acc = get_set_names' ind_rules acc
  | get_set_names' ((SU.Ind_Set  set_name )::ind_rules) acc = get_set_names' ind_rules (set_name :: acc);

fun get_set_names ind_sets = (get_set_names' ind_sets [] |> map tracing; get_set_names' ind_sets []);

fun eval' (Are_Same_Prints       (prnt1, prnt2))  _                                                     _ = prnt1 = prnt2
  | eval' (Is_Subprint_Of        (sub,   full))   _                                                     _ = String.isSubstring sub full
  | eval' (Is_Nth_Induct         (print, n))    (SU.Induct_Arguments {ons,   ...}: SU.induct_arguments) _ = print_is_nth_of print n ons
  | eval' (Is_Nth_Arbitrary      (print, n))    (SU.Induct_Arguments {arbs,  ...}: SU.induct_arguments) _ = print_is_nth_of print n arbs
  | eval' (Is_Induct              print    )    (SU.Induct_Arguments {ons,   ...}: SU.induct_arguments) _ = member (op =) ons   print
  | eval' (Is_Arbitrary           print    )    (SU.Induct_Arguments {arbs,  ...}: SU.induct_arguments) _ = member (op =) arbs  print
  | eval' (Is_Rule                print    )    (SU.Induct_Arguments {rules, ...}: SU.induct_arguments) _ = member (op =) (get_rule_names rules) print
  | eval' (Is_Rule_Of_Print      (rule, cname))  _                                                   ctxt = SU.rule_to_const_name ctxt rule = cname(* orelse rule = cname*)
  | eval' (Is_Set                 print    )    (SU.Induct_Arguments {rules, ...}: SU.induct_arguments) _ = (tracing print; if member (op =) (get_set_names rules) print then (tracing ("TRUE with " ^ print); true) else (tracing ("FALSE with " ^ print); false))
  | eval' (Is_Set_Of_Print       (set,  cname))  _                                                     _  = set = cname
  (*node*)
  | eval' (Print_Is_Cnst          print    )     _               ctxt = read_term ctxt print <$> is_Const |> Utils.is_some_true
  | eval' (Print_Is_Free          print    )     _               ctxt = read_term_then_check_term ctxt print is_Free
  | eval' (Print_Is_Var           print    )     _               ctxt = read_term_then_check_term ctxt print is_Var
  | eval' (Print_Is_Bound         print    )     _               ctxt = read_term_then_check_term ctxt print is_Bound
  | eval' (Print_Is_Lambda        print    )     _               ctxt = read_term_then_check_term ctxt print Isabelle_Utils.is_Abs
  | eval' (Print_Is_App           print    )     _               ctxt = read_term_then_check_term ctxt print Isabelle_Utils.is_App
  | eval' (Print_Is_Defined_With           (print, command)) _   ctxt = Definition_Pattern.get_command ctxt print = command
  | eval' (Print_Is_Defined_With_N_Clauses (print, numb))    _   ctxt = SeLFiE_Util.ctxt_n_cname_to_number_of_defining_clauses ctxt print = numb
  | eval' (Print_Takes_N_Arguments (print, numb))    _           ctxt = numb = print_n_context_to_numb_of_arguments print ctxt
  | eval' (Print_Takes_Less_Than_N_Arguments (print, numb))  _   ctxt = numb < print_n_context_to_numb_of_arguments print ctxt;

fun eval  assert (ind_args:SU.induct_arguments) ctxt = eval' assert ind_args ctxt |> EB.bool_to_assert;

end;