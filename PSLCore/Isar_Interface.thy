(* This file provides the Isar-level interface of PSL.
 * One can activate the interfaces by calling the functor, mk_PSL_Interface". *)
theory Isar_Interface
imports
  Monadic_Interpreter_Params
  PSL_Parser
keywords "strategy"   :: thy_decl 
     and "find_proof" :: diag
     and "try_hard"   :: diag
begin

ML{* signature PSL_INTERFACE =
sig
  val activate_isar_interface : unit -> unit;
  (* "strategy" and "try_hard_strategy" have to be exposed,
   *  so that Mirabelle can use it without exposing "lookup". *)
  type strategy;
  val try_hard_strategy       : Proof.context -> strategy option;
end;
*}

ML{* functor mk_PSL_Interface (PSL_Parser : PSL_PARSER) : PSL_INTERFACE =
struct

structure Mi  = Monadic_Interpreter;
structure Pc  = Parser_Combinator;
structure Mip = Monadic_Interpreter_Param;

type strategy = Mi.str;

structure Data = Generic_Data
(
  type T = strategy Symtab.table;
  val empty  = Symtab.empty : T;
  val extend = I;
  val merge  = Symtab.merge (K true);
);

fun lookup ctxt = (Symtab.lookup o Data.get) (Context.Proof ctxt);
fun update k v  = Data.map (Symtab.update_new (k, v));

fun put_strategy (name:string, str:strategy) = update name str
  |> Context.theory_map
  |> Local_Theory.background_theory;

val parse_strategy_def_string = PSL_Parser.strategy_parser : (string * Mi.str) Pc.parser;

fun tokens_to_string tokens = tokens |> map Token.unparse |> String.concat;

fun string_parser_to_token_parser (string_parser:'a Pc.parser) =
  (fn (tokens:Token.T list) => tokens
  |> tokens_to_string
  |> string_parser
  |> Seq.hd
  (* This function assumes that the string_parser consumes the entire string. *)
  |> apsnd (K ([]))) : 'a Token.parser;

val parse_strategy_def_tokens = string_parser_to_token_parser parse_strategy_def_string;

val parse_and_put_strategy_def : (local_theory -> local_theory) Token.parser = fn tokens =>
  tokens
  |> parse_strategy_def_tokens
  |> fst
  |> put_strategy
  |> (fn morph => (morph, []))

fun get_monad_tactic (strategy:strategy) (proof_state:Proof.state) =
  let
    val core_tac  = Mi.desugar strategy;
    val interpret = Mi.interpret;
    fun hard_timeout_in (sec:real) = TimeLimit.timeLimit (seconds sec);
  in
    hard_timeout_in 3000.0
    (interpret (Mip.eval_prim, Mip.eval_para, Mip.eval_tactical, Mip.m_equal, Mip.iddfc, (5,20))
                core_tac) proof_state
  end : Proof.state Mi.monad;

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
           val tactic        = get_monad_tactic strategy : Proof.state Mi.stttac;
           val proof_state   = Toplevel.proof_of top;
           val results'      = tactic proof_state     : Proof.state Mi.monad;
           val results       = results' []            : (log * Proof.state) Seq.seq;
           val logs          = lmap fst results       : log Seq.seq;
           val applies       = lmap Dynamic_Utils.mk_apply_script logs;
           val print         = tracing (case Seq.pull applies of
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
       (Scan.succeed (get_trans_trans "TryHard"))
  in () end;

fun try_hard_strategy (ctxt:Proof.context) = lookup ctxt "TryHard";

end;
*}

(* activate the Isar interface of PSL.  *)
ML{*  structure PSL_Interface = mk_PSL_Interface (PSL_Parser); 
PSL_Interface.activate_isar_interface ();
*}

end