(* This file provides the monadic parser of PSL. *)
theory PSL_Parser
imports
  Monadic_Interpreter
  "../Category/Parser_Combinator"
begin

ML{* signature PSL_PARSER =
sig
  val strategy_parser   : (string * Monadic_Interpreter.str) Parser_Combinator.parser;
  val invocation_parser : string Parser_Combinator.parser;
end
*}

ML{* structure PSL_Parser : PSL_PARSER =
struct

open Parser_Combinator;
infix >>=; (* from Parser_Combinator *)

structure Mi = Monadic_Interpreter;

fun parse_atomic (str:Mi.str) (name:string) = string name >>= (K (result str)) : Mi.str parser;
(* prim_str *)
val parse_clarsimp   = parse_atomic Mi.Clarsimp   "Clarsimp"   : Mi.str parser;
val parse_simp       = parse_atomic Mi.Simp       "Simp"       : Mi.str parser;
val parse_fastforce  = parse_atomic Mi.Fastforce  "Fastforce"  : Mi.str parser;
val parse_auto       = parse_atomic Mi.Auto       "Auto"       : Mi.str parser;
val parse_induct     = parse_atomic Mi.Induct     "Induct"     : Mi.str parser;
val parse_case       = parse_atomic Mi.Case       "Case"       : Mi.str parser;
val parse_rule       = parse_atomic Mi.Rule       "Rule"       : Mi.str parser;
val parse_erule      = parse_atomic Mi.Erule      "Erule"      : Mi.str parser;
(* diagnostic command *)
val parse_hammer     = parse_atomic Mi.Hammer     "Hammer"     : Mi.str parser;
(* assertion strategy / diagnostic command *)
val parse_is_solved  = parse_atomic Mi.Is_Solved  "IsSolved"   : Mi.str parser;
val parse_quickcheck = parse_atomic Mi.Quickcheck "Quickcheck" : Mi.str parser;
val parse_nitpick    = parse_atomic Mi.Nitpick    "Nitpick"    : Mi.str parser;
(* special purpose *)
val parse_defer      = parse_atomic Mi.Defer      "Defer"      : Mi.str parser;
(* monadic strategic *)
val parse_skip       = parse_atomic Mi.Skip       "Skip"       : Mi.str parser;
val parse_fail       = parse_atomic Mi.Fail       "Fail"       : Mi.str parser;

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
     parse_por (),
     parse_palt (),
     parse_repeat (),
     parse_repeat_n (),
     parse_solve1 ()] : Mi.str parser

and parse_a_strategy_in_paren _ : Mi.str parser =
  bracket
    (string "(")
    (parse_strategy ())
    (string ")")

and parse_strategic1 constr name =
  string name                       >>= (fn delayer =>
  parse_a_strategy_in_paren delayer >>= (
  result o constr))

and parse_repeat ()     = parse_strategic1 Mi.RepNB  "Repeat"  : Mi.str parser
and parse_repeat_n ()   = parse_strategic1 Mi.RepNT  "RepeatN" : Mi.str parser
and parse_solve1 ()     = parse_strategic1 Mi.Solve1 "Solve1"  : Mi.str parser

and parse_dynamic constr name =
  string "Dynamic"                                             >>= (fn _ =>
  bracket (string "(") (parse_atomic constr name) (string ")") >>= (fn _ =>
  result constr))
and parse_dclarsimp ()  = parse_dynamic Mi.Para_Clarsimp  "Clarsimp"  : Mi.str parser
and parse_dsimp ()      = parse_dynamic Mi.Para_Simp      "Simp"      : Mi.str parser
and parse_dfastforce () = parse_dynamic Mi.Para_Fastforce "Fastforce" : Mi.str parser
and parse_dinduct ()    = parse_dynamic Mi.Para_Induct    "Induct"    : Mi.str parser
and parse_drule ()      = parse_dynamic Mi.Para_Rule      "Rule"      : Mi.str parser
and parse_derule ()     = parse_dynamic Mi.Para_Erule     "ERule"     : Mi.str parser

and parse_strategies _ : Mi.str Seq.seq parser =
  bracket
    (string "[")
    (sepby1 (parse_strategy (), (string ",")))
    (string "]")

(* Do not remove "delayer", or you get stuck in a loop. *)
and parse_strategic constr name =
  string name              >>= (fn delayer =>
  parse_strategies delayer >>= (fn strategies : Mi.str Seq.seq =>
  strategies |> constr |> result))

and parse_or ()   = parse_strategic Mi.Or   "Ors"   : Mi.str parser
and parse_alt ()  = parse_strategic Mi.Alt  "Alts"  : Mi.str parser
and parse_seq ()  = parse_strategic Mi.Seq  "Thens" : Mi.str parser
and parse_por ()  = parse_strategic Mi.POr  "POrs"  : Mi.str parser
and parse_palt () = parse_strategic Mi.PAlt "PAlts" : Mi.str parser;

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