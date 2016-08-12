(* This file provides the monadic parser of PSL. *)
theory PSL_Parser
imports
  Monadic_Interpreter
  "../Category/Parser_Combinator"
begin

ML{* signature PSL_PARSER =
sig
  val strategy_parser   : (string * Monadic_Interpreter.tac) Parser_Combinator.parser;
  val invocation_parser : string Parser_Combinator.parser;
end
*}

ML{* structure PSL_Parser : PSL_PARSER =
struct

open Parser_Combinator;
infix >>=; (* from Parser_Combinator *)

structure Mi = Monadic_Interpreter;

fun parse_atomic (tac:Mi.tac) (name:string) = string name >>= (K (result tac)) : Mi.tac parser;
(* prim_tac *)
val parse_clarsimp   = parse_atomic Mi.Clarsimp   "Clarsimp"   : Mi.tac parser;
val parse_simp       = parse_atomic Mi.Simp       "Simp"       : Mi.tac parser;
val parse_fastforce  = parse_atomic Mi.Fastforce  "Fastforce"  : Mi.tac parser;
val parse_auto       = parse_atomic Mi.Auto       "Auto"       : Mi.tac parser;
val parse_induct     = parse_atomic Mi.Induct     "Induct"     : Mi.tac parser;
val parse_case       = parse_atomic Mi.Case       "Case"       : Mi.tac parser;
val parse_rule       = parse_atomic Mi.Rule       "Rule"       : Mi.tac parser;
val parse_erule      = parse_atomic Mi.Erule      "Erule"      : Mi.tac parser;
(* diagnostic command *)
val parse_hammer     = parse_atomic Mi.Hammer     "Hammer"     : Mi.tac parser;
(* assertion tactic / diagnostic command *)
val parse_is_solved  = parse_atomic Mi.Is_Solved  "IsSolved"   : Mi.tac parser;
val parse_quickcheck = parse_atomic Mi.Quickcheck "Quickcheck" : Mi.tac parser;
val parse_nitpick    = parse_atomic Mi.Nitpick    "Nitpick"    : Mi.tac parser;
(* special purpose *)
val parse_defer      = parse_atomic Mi.Defer      "Defer"      : Mi.tac parser;
(* monadic tactical *)
val parse_skip       = parse_atomic Mi.Skip       "Skip"       : Mi.tac parser;
val parse_fail       = parse_atomic Mi.Fail       "Fail"       : Mi.tac parser;

val msum = List.foldr (op plus) zero;
fun parse_strategy () =
  msum 
    [parse_clarsimp,
     parse_simp,
     parse_fastforce,
     parse_auto,
     parse_induct,
     parse_case,
     parse_rule,
     parse_erule,
     parse_hammer,
     parse_is_solved,
     parse_quickcheck,
     parse_nitpick,
     parse_defer,
     parse_dclarsimp (),
     parse_dsimp (),
     parse_dfastforce (),
     parse_dinduct (),
     parse_drule (),
     parse_derule (),
     parse_skip,
     parse_fail,
     parse_seq (),
     parse_alt (),
     parse_or (),
     parse_repeat (),
     parse_repeat_n (),
     parse_solve1 ()] : Mi.tac parser

and parse_a_strategy_in_paren _ : Mi.tac parser =
  bracket
    (string "(")
    (parse_strategy ())
    (string ")")

and parse_tactical1 constr name =
  string name                       >>= (fn delayer =>
  parse_a_strategy_in_paren delayer >>= (
  result o constr))

and parse_repeat ()     = parse_tactical1 Mi.RepNB  "Repeat"  : Mi.tac parser
and parse_repeat_n ()   = parse_tactical1 Mi.RepNT  "RepeatN" : Mi.tac parser
and parse_solve1 ()     = parse_tactical1 Mi.Solve1 "Solve1"  : Mi.tac parser

and parse_dynamic constr name =
  string "Dynamic"                                             >>= (fn _ =>
  bracket (string "(") (parse_atomic constr name) (string ")") >>= (fn _ =>
  result constr))
and parse_dclarsimp ()  = parse_dynamic Mi.Para_Clarsimp  "Clarsimp"  : Mi.tac parser
and parse_dsimp ()      = parse_dynamic Mi.Para_Simp      "Simp"      : Mi.tac parser
and parse_dfastforce () = parse_dynamic Mi.Para_Fastforce "Fastforce" : Mi.tac parser
and parse_dinduct ()    = parse_dynamic Mi.Para_Induct    "Induct"    : Mi.tac parser
and parse_drule ()      = parse_dynamic Mi.Para_Rule      "Rule"      : Mi.tac parser
and parse_derule ()     = parse_dynamic Mi.Para_Erule     "ERule"     : Mi.tac parser

and parse_strategies _ : Mi.tac Seq.seq parser =
  bracket
    (string "[")
    (sepby1 (parse_strategy (), (string ",")))
    (string "]")

(* Do not remove "delayer", or you get stuck in a loop. *)
and parse_tactical constr name =
  string name              >>= (fn delayer =>
  parse_strategies delayer >>= (fn strategies : Mi.tac Seq.seq =>
  strategies |> constr |> result))

and parse_or ()  = parse_tactical Mi.Or  "Ors"   : Mi.tac parser
and parse_alt () = parse_tactical Mi.Alt "Alts"  : Mi.tac parser
and parse_seq () = parse_tactical Mi.Seq "Thens" : Mi.tac parser;

val parse_equality = string "=" |> token;

val parse_strategy_name = token word     >>= (fn str_name =>
                          parse_equality >>= K (
                          result str_name));

val strategy_parser =
  parse_strategy_name >>= (fn name =>
  parse_strategy ()   >>= (fn strategy =>
  result (name, strategy)));

val invocation_parser = token word >>= result : string parser;

end;
*}

end