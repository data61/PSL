(* This file provides utility functions that are useful to generate tactics at run-time. *)
theory Dynamic_Utils
imports
  "../Utils/Isabelle_Utils"
  "../Utils/Tactic"
  "../Utils/More_Seq"
begin

ML{* signature DYNAMIC_UTILS =
sig
  type context;
  type state;
  type src;
  type 'a seq;
  type 'a nontac   = 'a -> 'a seq;
  type node;
  type log;
  type 'a logtac   = 'a -> (log * 'a) seq;
  type 'a st_monad = log -> (log * 'a) seq;
  type 'a stttac   = 'a -> 'a st_monad;

  val check_src           : context -> src -> src;
  val checked_src_to_meth : context -> src -> Method.method;
  val str_to_tokens       : context -> string -> Token.T list;
  val get_tokens          : string -> Token.T list -> src;
  val get_meth_nm         : string -> string list -> string;
  val reform              : log * 'goal nontac -> 'goal logtac;
  val writer_to_state     : (log * 'state) seq -> 'state st_monad;
  val nontac_to_logtac    : node -> 'a nontac -> 'a logtac;
  val logtac_to_stttac    : 'a logtac -> 'a stttac;
  val log_n_nontac_to_stttac     : log * 'a nontac -> 'a stttac;
  val string_to_nontac_on_pstate : string -> state nontac;
  val string_to_stttac_on_pstate : string -> state stttac;
  val mk_apply_script            : log -> string;
end;
*}

ML{* structure Dynamic_Utils : DYNAMIC_UTILS =
struct

type context     = Proof.context;
type state       = Proof.state;
type src         = Token.src;
type 'a seq      = 'a Seq.seq;
type 'a nontac   = 'a -> 'a seq;
type node        = {using:string list, methN:string, back:int};
type log         = node list;
type 'a logtac   = 'a -> (log * 'a) seq;
type 'a st_monad = log -> (log * 'a) seq;
type 'a stttac   = 'a -> 'a st_monad;

local
fun get_token_getter_n_src_checker ctxt =
  let
    type src          = Token.src;
    type ctxt         = Proof.context;
    type meth         = Method.method;
    val thy           = Proof_Context.theory_of ctxt;
    val keywords      = Thy_Header.get_keywords thy;
    val str_to_tokens = (fn str => Token.explode keywords Position.none str |>
      filter_out (fn token:Token.T => Token.is_kind Token.Space token));
    val checker'      = Method.check_src ctxt;
    val get_method    = (Method.method ctxt, "I am dummy.");
  in
    (str_to_tokens : string -> Token.T list, (fn source => (checker' source, get_method)))
  end;

in

fun check_src ctxt src = (get_token_getter_n_src_checker ctxt |> snd) src |> fst;

fun checked_src_to_meth ctxt src = ((get_token_getter_n_src_checker ctxt |> snd) src |> snd |> fst) src ctxt;

fun str_to_tokens (ctxt:Proof.context) (str:string) : Token.T list =
  (get_token_getter_n_src_checker ctxt |> fst) str;

end;

fun get_tokens (meth_nm:string) (attributes:Token.T list) =
  Token.make_src (meth_nm, Position.none) attributes;

fun get_meth_nm (meth:string) (attributes:string list) = 
  Utils.intersperse " " (meth :: attributes) |> String.concat;

fun reform (param:('meth_str * ('goal nontac))) =
let
  val func       = snd param;
  val left       = fst param;
  fun new_func b = Seq.map (fn right => (left, right)) (func b);
in
  new_func : 'goal -> ('meth_str * 'goal) Seq.seq
end;

fun string_to_nontac_on_pstate meth_name proof_state =
  let
    val ctxt        = Proof.context_of proof_state;
    val meth        = Utils.rm_parentheses meth_name;
    fun split str   = let val strs = space_explode " " str in (hd strs, tl strs) end;
    val hd_tl       = split meth;
    val tokens      = str_to_tokens ctxt (String.concatWith " " (snd hd_tl));
    val src         = Token.make_src (fst hd_tl, Position.none) tokens;
    val checked_src = check_src ctxt src;
    val text        = Method.Source checked_src;
    val text_range  = (text, (Position.none, Position.none)) : Method.text_range;
    val results     = Proof.apply text_range proof_state handle THM _ => Seq.empty
                    :  Proof.state Seq.result Seq.seq;
    val filtered_results = Seq.filter_results results :  Proof.state Seq.seq;
  in
    filtered_results : Proof.state Seq.seq
  end;

fun writer_to_state (writerTSeq : (log * 'state) seq) (trace : log) =
  Seq.map (fn (this_step, pstate) => (trace @ this_step, pstate)) writerTSeq : (log * 'state) seq

(* nontac_to_logtac ignores (back:int) in (node:node). *)
fun nontac_to_logtac (node:node) (nontac:'a nontac) (goal:'a) : (log * 'a) seq =
    Seq.map (fn result => (node, result)) (nontac goal)
 |> Seq2.seq_number
 |> Seq.map (fn (n, ({methN = methN, using = using, ...}, result)) =>
                ([{methN = methN, using = using, back = n}], result))
  handle THM _ => Seq.empty;

fun logtac_to_stttac (logtac:'a logtac) = (fn (goal:'a) =>
  let
    val logtac_results = logtac goal;
    val state_monad    = writer_to_state logtac_results:'a st_monad;
  in
    state_monad : 'a st_monad
  end) : 'a stttac;

fun log_n_nontac_to_stttac (log:log, nontac:'a nontac) = (log, nontac)
 |> reform
 |> logtac_to_stttac
 : 'a stttac;

fun string_to_stttac_on_pstate (meth_name:string) =
  let
    val nontac         = string_to_nontac_on_pstate meth_name               : state nontac;
    val nontac_with_TO = Tactic.TIMEOUT_in 1.0  nontac                      : state nontac;
    val trace_node     = {using = [], methN = meth_name, back = 0}  : node;
    val logtac         = nontac_to_logtac trace_node nontac_with_TO         : state logtac;
    val stttac         = logtac_to_stttac logtac                            : state stttac;
  in
    stttac : state stttac
  end;

local
  fun mk_using  ([]   : string list) = ""
   |  mk_using  (using: string list) = "using " ^ String.concatWith " " using ^ " ";
  fun mk_apply methN  = "apply (" ^ methN ^ ") ";
  fun mk_backs (n:int) = replicate n "back" |> String.concatWith " " handle Subscript =>
    (tracing "mk_backs in Isabelle_Utils.thy failed. It should take 0 or a positive integer.";"");
  fun mk_apply_script1 {methN : string, using : string list, back : int} =
    mk_using using ^ mk_apply methN ^ mk_backs back ^ "\n";
in
  fun mk_apply_script (log:log) =
   (tracing ("Number of apply commands: " ^ (length log |> Int.toString));
    map mk_apply_script1 log
    |> String.concat
    |> Active.sendback_markup [Markup.padding_command]) : string;
end;

end;
*}

end