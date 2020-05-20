(*  Title:      Isar_Interface.ML
    Author:     Yutaka Nagashima, Data61, CSIRO

This file provides the Isar-level interface of PSL.
One can activate the interfaces by calling the function, "PSL_Interface.activate_isar_interface ()".
*)

(*** PSL_INTERFACE: One can define new strategies only through the Isar interface. ***)
signature PSL_INTERFACE =
sig
  val activate_isar_interface : unit -> unit;
  (* "strategy" and "try_hard_strategy" have to be exposed,
   *  so that Mirabelle can use it without exposing "lookup". *)
  type strategy;
  val try_hard_strategy       : Proof.context -> strategy option;
  val try_parallel_strategy   : Proof.context -> strategy option;
end;

(*** PSL_Interface: One can define new strategies only through the Isar interface. ***)
structure PSL_Interface : PSL_INTERFACE =
struct

structure Mp = Monadic_Prover;
structure Pc  = Parser_Combinator;

type strategy = Mp.str;

structure Data = Generic_Data
(
  type T = strategy Symtab.table;
  val empty  = Symtab.empty : T;
  val extend = I;
  val merge  = Symtab.merge (K true);
);

fun lookup ctxt = (Symtab.lookup o Data.get) (Context.Proof ctxt);
fun update k v  = Data.map (Symtab.update_new (k, v));

structure Lookup : LOOKUP =
struct
  fun get_str ctxt name =
    let
      val some_str = lookup ctxt name : Mp.str option;
      val strategy = Utils.the' (name ^ "?\nDid you really define such a strategy?\n"
        ^ "Also, you should not forget that PThenOne and PThenAll take *exactly* two sub-strategies!")
        some_str : Mp.str;
    in
      strategy
    end;
end;

structure PSL_Parser = mk_PSL_Parser(Lookup);

fun put_strategy (name:string, str:strategy) = update name str
  |> Context.theory_map
  |> Local_Theory.background_theory;

fun tokens_to_string tokens = tokens |> map Token.unparse |> String.concatWith " ";

fun string_parser_to_token_parser (symbols_parser:'a Pc.parser) = (fn (tokens:Token.T list) =>
  tokens
  |> tokens_to_string
  |> Symbol.explode
  |> symbols_parser
  |> Seq.hd
  (*This function assumes that the string_parser consumes the entire string.*)
  |> apsnd (K ([]))) : 'a Token.parser;

fun parse_strategy_def_tokens ctxt = string_parser_to_token_parser (PSL_Parser.strategy_parser ctxt)
  : (string * Mp.str) Token.parser;

val parse_and_put_strategy_def : (local_theory -> local_theory) Token.parser = fn tokens =>
  let
    fun get_token_parser ctxt = parse_strategy_def_tokens ctxt : (string * Mp.str) Token.parser;
    fun get_token_p_result ctxt = get_token_parser ctxt tokens |> fst : string * Mp.str;
    fun put_str_in_lthy (lthy:local_theory) = put_strategy (get_token_p_result lthy) lthy;
  in
  (put_str_in_lthy, [])
  end;

fun get_monad_tactic (strategy:strategy) (proof_state:Proof.state) =
  let
    val core_tac  = Mp.desugar strategy;
    val interpret = Mp.interpret;
    fun hard_timeout_in (sec:real) = Timeout.apply (seconds sec);
  in
    hard_timeout_in 60000.0
    (interpret (Mp.eval_prim, Mp.eval_para, Mp.eval_strategic, Mp.m_equal, Mp.iddfc, (5,20))
                core_tac) proof_state
  end : Proof.state Mp.monad;

type trans_trans = Toplevel.transition -> Toplevel.transition;

val strategy_invocation_parser = PSL_Parser.invocation_parser : string Pc.parser;

local

infix >>=;
val op >>= =  Parser_Combinator.>>=;

in

fun invocation_parser_to_trans_trans_parser (inv_p : string Pc.parser)
  (get_trans_trans : string -> trans_trans) =
  string_parser_to_token_parser (inv_p >>= (Pc.result o get_trans_trans)) : trans_trans Token.parser;

end;

fun get_trans_trans (strategy_name:string) =
      (((Toplevel.keep_proof:(Toplevel.state -> unit) -> trans_trans)
        (fn top =>
         let
           type log          = Dynamic_Utils.log;
           val lmap          = Seq.map;
           val context       = Toplevel.context_of top : Proof.context;
           val some_strategy = lookup context strategy_name;
           val strategy      = Utils.the' (strategy_name ^ "? You haven't defined such a strategy!")
                               some_strategy;
           val tactic        = get_monad_tactic strategy : Proof.state Mp.stttac;
           val proof_state   = Toplevel.proof_of top;
           val results'      = tactic proof_state     : Proof.state Mp.monad;
           val results       = results' []            : (log * Proof.state) Seq.seq;
           val logs          = lmap fst results       : log Seq.seq;
           val applies       = lmap Dynamic_Utils.mk_apply_script logs;
           val print         = writeln (case Seq.pull applies of
             NONE => error "empty sequence. no proof found."
           | SOME _ => Seq.hd applies);
         in
           print
         end)
       ):trans_trans);

fun activate_isar_interface _ =
  let
    val _ = Outer_Syntax.local_theory @{command_keyword strategy} "PSL strategy definition"
      parse_and_put_strategy_def;

    val _ =
      Outer_Syntax.command @{command_keyword find_proof}
        "find_proof tries to find a proof based on high level strategies provided in advance.."
        (invocation_parser_to_trans_trans_parser strategy_invocation_parser get_trans_trans);

    val _ =
      Outer_Syntax.command @{command_keyword try_hard}
       "try_hard to find efficient proof-scripts."
       (Scan.succeed (get_trans_trans "Try_Hard"))

    val _ =
      Outer_Syntax.command @{command_keyword try_hard_one}
       "try_hard to find efficient proof-scripts."
       (Scan.succeed (get_trans_trans "Try_Hard_One"))

    val _ =
      Outer_Syntax.command @{command_keyword try_hard_all}
       "try_hard to find efficient proof-scripts."
       (Scan.succeed (get_trans_trans "Try_Hard_All"))

    val _ =
      Outer_Syntax.command @{command_keyword try_parallel}
       "try_hard to find efficient proof-scripts."
       (Scan.succeed (get_trans_trans "Try_Parallel"))
  in () end;

fun try_hard_strategy     (ctxt:Proof.context) = lookup ctxt "Try_Hard";
fun try_parallel_strategy (ctxt:Proof.context) = lookup ctxt "Try_Parallel";

end;

(*** activate the Isar interface of PSL. ***)
PSL_Interface.activate_isar_interface ();