(* This file provides an interface of sledgehammer for PSL.                               *)
(* This file does not include significant code duplication with the Isabelle source code. *)
theory Dynamic_Sledgehammer
imports "Dynamic_Utils"
  "../Category/Maybe"
  "../Category/Parser_Combinator"
begin

ML{* (* hammer_meth : Proof.state Tactic_Generation.logtac; *)
structure Dynamic_Sledgehammer =
struct

type state        = Proof.state;
type text         = Method.text;
type text_range   = Method.text_range;
type ctxt         = Proof.context;
type T            = Token.T;
type ref          = Facts.ref;
type srcs         = Token.src list;
type keywords     = Keyword.keywords;
type node         = Dynamic_Utils.node;
type log          = Dynamic_Utils.log;
type 'a seq       = 'a Seq.seq;
type 'a nontac    = 'a Dynamic_Utils.nontac;
type 'a logtac    = 'a Dynamic_Utils.logtac;
type 'a stttac    = 'a Dynamic_Utils.stttac;

fun sh_output_to_sh_logtac (sh_output:string) (state:Proof.state) =
let
  (* syntax sugars *)
  val thy           = Proof.theory_of state       : theory;
  val ctxt          = Proof.context_of state      : ctxt;
  val keywords      = Thy_Header.get_keywords thy : keywords;

  (* function body *)
  val op_w_stopper  = sh_output ^ " parserStopsWithMe";
  val tokens        = Token.explode keywords Position.none op_w_stopper
                    |> filter_out (fn token:T => Token.is_kind Token.Space token) : T list;
  val is_using      = String.isPrefix "using " sh_output;
  val parse_using   = Parse.and_list1 Parse.xthms1 : (ref * srcs) list list Token.parser;
  val parse_method  = Method.parse                 : text_range Token.parser;
  val parse_one     = Scan.one (K true)            : T list -> T * T list;
  val parser        = if is_using
                      then (parse_one |-- parse_using) -- (parse_one |-- parse_method)
                      else (parse_one |-- parse_method) >> (fn x => ([], x));
  val p_get_meth    = (parse_one |-- parse_using) -- parse_one
                    : T list -> ((ref * srcs) list list * T) * T list;
  fun get_str tkns  = tkns
                    |> Utils.init (* drops "parserStopsWithMe" slowly. *)
                    |> map Token.unparse |> String.concatWith " " : string;
  val methN:string  = if   is_using
                      then p_get_meth tokens |> snd |> get_str
                      else parse_one  tokens |> snd |> get_str;
  val result        = parser tokens
                    : ((ref * srcs) list list * text_range) * T list;
  val using_raw     = (#1 o #1) result : (ref * srcs) list list;
  val text_range    = (#2 o #1) result : text_range;
  val check_text    = Method.check_text ctxt;
  val fail_trange   = (Method.Basic (K Method.fail), Position.no_range) : Method.text_range;
  val checked_range = (apfst check_text text_range handle ERROR _ => fail_trange) : text_range;
  val using_strings = using_raw |> List.concat |> map (Facts.string_of_ref o #1) handle Empty =>
                      (if Utils.debug
                       then tracing "using_strings in sh_output_to_sh_logtac failed." else ();
                       ["Failed constructing using_strings."])
                    : string list;
  val node : node   = Dynamic_Utils.Apply {using = using_strings, methN = methN, back = 0};
  (* print messages for debugging.*)
  val _ =
    let
      val app = case node of
        Dynamic_Utils.Apply app_node => app_node
      | _ => error "app in Dynamic_Sledgehammer panics.";
      fun tracing1 _ = tracing ("methN in node is " ^ #methN app);
      fun tracing2 _ = tracing "using_strings are ...";
      fun tracing3 _ = map tracing using_strings;
    in
      if Utils.debug then (tracing1 (); tracing2 (); tracing3 (); ()) else ()
    end;
    val _ = Basics.try;
  val state_w_using = Proof.using_cmd using_raw state : state;
  val timeout       = TimeLimit.timeLimit (seconds 60.0)
  val tac_results   = timeout (Proof.apply checked_range) state_w_using 
                      |> Seq.filter_results
                     (* Why Seq.try Seq.hd? Because we want to evaluate the head of   
                      * sequence strictly here to catch errors immediately.*)
                      |> Seq.try Seq.hd
                      handle THM _ => Seq.empty
                           | Empty => Seq.empty
                           | TERM _ => Seq.empty
                           | TYPE _ => Seq.empty
                           | ERROR _ => Seq.empty : state Seq.seq;
  val results_w_log = Seq.map (fn x => ([node], x)) tac_results : (log * state) Seq.seq;
in
  results_w_log : (log * state) Seq.seq
end;

fun hammer_logtac (pstate:Proof.state) =
  let
    (* syntax sugars *)
    infix <$>
    fun x <$> f            = Option.map f x;
    val valOf              = Option.valOf;
    val omap               = Option.map;
    val thy                = Proof.theory_of pstate : theory;
    val params             = Sledgehammer_Commands.default_params thy [];
    val Auto_Try           = Sledgehammer_Prover.Auto_Try;
    val fact_override      = Sledgehammer_Fact.no_fact_override;
    val run_sledgehammer   = Sledgehammer.run_sledgehammer params Auto_Try NONE 1 fact_override
                           : state -> bool * (string * string list);
    (* function body *)
    val result             = SOME (run_sledgehammer pstate)
                             handle ERROR _ =>
                             (if Utils.debug then tracing "ERROR in result/hammer_logtac" else ();
                              NONE)
                           : (bool * (string * string list)) option;
    val orig_string        = result <$> snd <$> snd <$> hd handle Empty =>
                             (if Utils.debug then tracing "Empty in orig_string/hammer_logtac" else (); 
                              NONE) : string option;
    val one_line_apply     = orig_string <$> space_explode " "
                            <$> drop 2                           (* drop "Try this:"*)
                            <$> rev <$> drop 2 <$> rev           (* drop "(0.1 ms)." and such.*)
                            <$> String.concatWith " "            : string option;
    val apply_script_cntnt = omap YXML.content_of one_line_apply : string option;
    val sh_returned        = if is_some apply_script_cntnt
                             then valOf result |> fst else false : bool;
  in
    if   sh_returned
    then
      sh_output_to_sh_logtac (valOf apply_script_cntnt) pstate
    else Seq.empty : (log * state) Seq.seq
  end;

val pstate_stttacs = Dynamic_Utils.logtac_to_stttac hammer_logtac : state stttac;

end;
*}

end