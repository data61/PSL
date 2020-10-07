(*
    File:     pratt.ML
    Author:   Manuel Eberl, TU München

    Various functions around Pratt certificates to prove primality of numbers.
*)

signature PRATT =
sig

type prime_thm_cache = (int * thm) list
type tac_config = {cache : prime_thm_cache, verbose : bool, code : bool}
datatype cert = Pratt_Node of int * int * cert list
exception INVALID_CERT of cert

val get_cert_number : cert -> int

val mk_cert : int -> cert option
val check_cert : cert -> bool
val replay_cert : prime_thm_cache -> cert -> Proof.context -> thm * prime_thm_cache
val replay_cert_code : cert -> Proof.context -> thm
val prove_prime : prime_thm_cache -> int -> Proof.context -> thm option * prime_thm_cache

val certT : typ
val termify_cert : cert -> term
val untermify_cert : term -> cert

val pretty_cert : cert -> Pretty.T
val read_cert : Input.source -> cert

val cert_cartouche : cert parser 
val tac_config_parser : tac_config parser
val tac : tac_config -> cert option -> Proof.context -> int -> tactic

val setup_valid_cert_code_conv : (Proof.context -> conv) -> Context.generic -> Context.generic

end

structure Pratt : PRATT =
struct

fun mod_exp _ 0 m = if m = 1 then 0 else 1
  | mod_exp b e m = 
      case Integer.div_mod e 2 of
        (e', 0) => mod_exp ((b * b) mod m) e' m
      | (e', _) => (b * mod_exp ((b * b) mod m) e' m) mod m

local
  fun calc_primes mode ps i n =
      if n = 0 then ps
      else if exists (fn p => i mod p = 0) ps then
        let
          val i = i + 1
          and n = if mode then n else n - 1
        in
          calc_primes mode ps i n
        end
      else
        let
          val ps = ps @ [i]
          and i = i + 1
          and n = n - 1
        in
          calc_primes mode ps i n
        end;
in
  fun primes_up_to n =
      if n < 2 then []
      else calc_primes false [2] 3 (n - 2);
end;

val small_primes = primes_up_to 100

fun factorise n =
  let
    val init = (small_primes, 101, false)
    fun get_divisor (p :: _, _, _) = p
      | get_divisor ([], k, _) = k
    fun next (_ :: ps, k, b) = (ps, k, b)
      | next ([], k, b) = ([], k + (if b then 4 else 2), not b)

    fun divide_out d n =
      let
        fun divide (n, acc) =
          if n mod d = 0 then
            divide (n div d, acc + 1)
          else
            (n, acc)
      in
        divide (n, 0)
      end
    
    fun factor st n acc =
      let
        val d = get_divisor st
      in
        if n <= 1 then
          rev acc
        else if d * d > n then
          rev ((n, 1) :: acc)
        else
          case divide_out d n of
            (n', k) => factor (next st) n' (if k = 0 then acc else (d, k) :: acc)
      end
  in
    factor init n []
  end


type prime_thm_cache = (int * thm) list

datatype cert = Pratt_Node of int * int * cert list

exception INVALID_CERT of cert

fun get_cert_number (Pratt_Node (n, _, _)) = n

fun mk_cert n =
  let
    exception PRATT
    fun cert n cache =
      if AList.defined op= cache n then
        cache
      else
        let
          fun find p lb ub =
            if ub < lb then NONE else if p lb then SOME lb else find p (lb+1) ub
          val ps = map fst (factorise (n - 1))
          fun suitable' a p = mod_exp a ((n - 1) div p) n <> 1
          fun suitable a = mod_exp a (n - 1) n = 1 andalso forall (suitable' a) ps
          val a =
            case find suitable 1 n of
              NONE => raise PRATT
            | SOME a => a
          val cache = fold cert ps cache
          val proofs = map (the o AList.lookup op= cache) ps
        in
          (n, Pratt_Node (n, a, proofs)) :: cache
        end
  in
    AList.lookup op= (cert n []) n
      handle PRATT => NONE
  end


fun prove_list_all ctxt property thms =
  let
    val thm =
      Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt property)]
        @{thm list.pred_inject(1)}
    fun prove acc [] = acc
      | prove acc (thm :: thms) = prove (@{thm list_all_ConsI} OF [thm, acc]) thms
  in
    prove thm (rev thms)
  end

fun check_prime_factors_subset 0 _ = false
  | check_prime_factors_subset n [] = n = 1
  | check_prime_factors_subset n (p :: ps) =
      if n mod p = 0 then
        check_prime_factors_subset (n div p) (p :: ps)
      else
        check_prime_factors_subset n ps

fun check_cert' (Pratt_Node (n, a, ts)) =
  let
    val ps = map get_cert_number ts
  in
    check_prime_factors_subset (n - 1) ps
    andalso forall (fn p => mod_exp a ((n - 1) div p) n <> 1) ps
    andalso mod_exp a (n - 1) n = 1
  end

fun check_cert (Pratt_Node (n, a, ts)) =
      check_cert' (Pratt_Node (n, a, ts)) andalso forall check_cert ts

fun replay_cert cache cert ctxt =
  let
    val mk_nat = HOLogic.mk_number @{typ "Nat.nat"}
    val mk_eq_thm = Thm.cterm_of ctxt #> Thm.reflexive

    fun replay (Pratt_Node (n, a, ts)) cache =
      case AList.lookup op= cache n of
        SOME thm => (thm, cache)
      | NONE =>
          let
            val _ = if check_cert' cert then () else raise INVALID_CERT cert
            val (prime_thms, cache) = fold_map replay ts cache
            val (n', a') = apply2 mk_nat (n, a)
            val prime_thm = prove_list_all ctxt @{term "prime :: nat \<Rightarrow> bool"} prime_thms

            val thm =
              (@{thm lehmers_theorem'} OF [prime_thm, mk_eq_thm a', mk_eq_thm n'])
            fun mk_thm () =
              Goal.prove ctxt [] []
                (HOLogic.mk_Trueprop (@{term "prime :: nat \<Rightarrow> bool"} $ mk_nat n))
                (fn {context = ctxt, ...} =>
                   HEADGOAL (resolve_tac ctxt [thm])
                   THEN ALLGOALS (TRY o REPEAT_ALL_NEW
                     (resolve_tac ctxt @{thms list_all_ConsI list.pred_inject(1)}))
                   THEN PARALLEL_ALLGOALS (Simplifier.simp_tac ctxt))
          in
            case try mk_thm () of
              NONE => raise THM ("replay_cert", 0, [thm])
            | SOME thm => (thm, (n, thm) :: cache)
          end
  in
    replay cert cache
  end

fun prove_prime cache n ctxt =
  case mk_cert n of
    NONE => (NONE, cache)
  | SOME cert =>
      case replay_cert cache cert ctxt of
        (thm, cache) => (SOME thm, cache)

(* datatype token *)

datatype token_kind = Nat of int | Comma | Open_Brace | Close_Brace | Space | EOF
datatype token = Token of token_kind * Position.T

fun pos_of (Token (_, pos)) = pos

fun is_space (Token (Space, _)) = true
  | is_space _ = false

fun is_eof (Token (EOF, _)) = true
  | is_eof _ = false

fun mk_eof pos = Token (EOF, pos)

fun token_kind_name (Nat _) = "natural number"
  | token_kind_name Comma = "comma"
  | token_kind_name Open_Brace = "opening curly brace"
  | token_kind_name Close_Brace = "closing curly brace"
  | token_kind_name Space = "whitespace"
  | token_kind_name EOF = "end of input"

val stopper =
  Scan.stopper (fn [] => mk_eof Position.none | toks => mk_eof (pos_of (List.last toks))) is_eof


(* tokenize *)

local

fun space_symbol ((s, _): Symbol_Pos.T) = Symbol.is_blank s andalso s <> "\n"

val scan_space =
  Scan.many1 space_symbol @@@ Scan.optional (Symbol_Pos.$$$ "\n") [] ||
  Scan.many space_symbol @@@ Symbol_Pos.$$$ "\n"

fun token kind (ss: Symbol_Pos.T list) =
  Token (kind, Position.range_position (Symbol_Pos.range ss))

val scan_token =
  Symbol_Pos.scan_nat >> (fn ss =>
    let
      val kind = Nat (#1 (Library.read_int (map #1 ss)))
      val pos = Position.range_position (Symbol_Pos.range ss)
    in Token (kind, pos) end) ||
  Symbol_Pos.$$$ "," >> token Comma ||
  Symbol_Pos.$$$ "{" >> token Open_Brace ||
  Symbol_Pos.$$$ "}" >> token Close_Brace ||
  scan_space >> token Space

val scan_all_tokens =
  Scan.repeat scan_token --|
  Symbol_Pos.!!! (fn () => "Lexical error") (Scan.ahead (Scan.one Symbol_Pos.is_eof))

in

val tokenize =
  #1 o Scan.error (Scan.finite Symbol_Pos.stopper scan_all_tokens) o Input.source_explode

end;


(* parse *)

local

type 'a parser = token list -> 'a * token list

fun err_msg expected toks () =
  let
    fun found [] = "end of input"
      | found (Token (kind, _) :: _) = token_kind_name kind
  in
    expected ^ " expected, but " ^ found toks ^ " was found"
  end

fun !!! (scan: 'a parser) =
  let
    fun get_pos [] = " (end-of-input)"
      | get_pos (tok :: _) = Position.here (pos_of tok)

    fun err (toks, msg) () =
      "Syntax error" ^ get_pos toks ^ (case msg of NONE => "" | SOME m => ": " ^ m ())
  in Scan.!! err scan end;

fun one kind =
  Scan.some (fn Token (kind', _) => if kind = kind' then SOME () else NONE)
  || Scan.fail_with (err_msg (token_kind_name kind))
val nat =
  Scan.some (fn Token (Nat n, _) => SOME n | _ => NONE)
  || Scan.fail_with (err_msg "natural number")
val comma = one Comma
val open_brace = one Open_Brace
val close_brace = one Close_Brace

fun enum1 scan = scan ::: Scan.repeat (comma |-- scan)
fun enum scan = enum1 scan || Scan.succeed []
fun list scan = !!! open_brace |-- enum scan --| !!! close_brace

fun parse toks =
  ((open_brace |-- !!! (nat --| !!! comma -- !!! nat --| !!! comma -- list parse
    --| !!! close_brace)) >> (fn ((a, b), c) => Pratt_Node (a, b, c))
  || !!! nat >> (fn a => Pratt_Node (a, 1, []))
  || Scan.fail_with (err_msg "opening curly brace or natural number")) toks

in

fun read_cert input =
  let val toks = filter_out is_space (tokenize input)
  in #1 (Scan.error (Scan.finite stopper (parse --| !!! (Scan.ahead (one EOF)))) toks) end

end

val cert_cartouche = Args.cartouche_input >> read_cert


val certT = @{typ "Pratt_Certificate.pratt_tree"}


local

val mk_nat = HOLogic.mk_number @{typ nat}
val dest_nat = snd o HOLogic.dest_number

in

fun termify_cert (Pratt_Node (n, a, ts)) =
  @{term Pratt_Node} $
    HOLogic.mk_tuple [mk_nat n, mk_nat a, HOLogic.mk_list certT (map termify_cert ts)]

fun untermify_cert (@{term Pratt_Node} $ t) = (
      case HOLogic.strip_tuple t of
        [n, a, ts] => Pratt_Node (dest_nat n, dest_nat a, map untermify_cert (HOLogic.dest_list ts))
      | _ => raise TERM ("untermify_cert", [@{term Pratt_Node} $ t]))
  | untermify_cert t = raise TERM ("untermify_cert", [t])

end


structure Data = Generic_Data
(
  type T = (Proof.context -> conv) option
  val empty : T = NONE
  val extend = I
  fun merge (_, conv) = conv
)

fun setup_valid_cert_code_conv conv ctxt =
  Data.put (SOME conv) ctxt

fun has_code_conv ctxt =
  case Data.get (Context.Proof ctxt) of
    SOME _ => true
  | _ => false

fun valid_cert_code_conv ctxt =
  case Data.get (Context.Proof ctxt) of
    SOME conv => conv ctxt
  | NONE => (fn ct => raise CTERM ("valid_cert_code_conv", [ct]))

fun replay_cert_code cert ctxt =
  let
    val goal =
      Thm.cterm_of ctxt (HOLogic.mk_Trueprop (@{term valid_pratt_tree} $ termify_cert cert))
  in
    @{thm valid_pratt_tree_imp_prime'} OF [valid_cert_code_conv ctxt goal]
  end
    handle TERM _ => raise INVALID_CERT cert
         | CTERM _ => raise INVALID_CERT cert
         | THM _ => raise INVALID_CERT cert

local
  val pretty_int = Pretty.str o string_of_int
in
fun pretty_cert (Pratt_Node (2, _, _)) = pretty_int 2
  | pretty_cert (Pratt_Node (n, a, ts)) =
      Pretty.list "{" "}"
        [pretty_int n, pretty_int a, Pretty.enum "," "{" "}" (map pretty_cert ts)]
end


type tac_config = {cache : prime_thm_cache, verbose : bool, code : bool}

exception NO_CODE

local

fun cert_err config cert =
  let
    val _ =
      if #verbose config then
        Pretty.chunks [Pretty.str "Invalid Pratt certificate:",
          Pretty.indent 2 (pretty_cert cert)]
        |> Pretty.string_of
        |> warning
      else
        ()
  in
    no_tac
  end

in

fun tac config cert ctxt i =
  let
    val cmd =
      Pretty.block ([Pretty.str "pratt"] @
        (if #code config then [Pretty.str " (", Pretty.keyword1 "code", Pretty.str ")"] else []))
    fun print_cert cert =
      [Pretty.keyword1 "by", Pretty.brk 1, Pretty.str "(", cmd, Pretty.str " ",
        Pretty.blk (2, [Pretty.cartouche (pretty_cert cert)]), Pretty.str ")"]
      |> Pretty.blk o pair 4
      |> Pretty.string_of
      |> Active.sendback_markup_command
      |> prefix "To repeat this proof with a pre-computed certificate, use:\n"
      |> Output.information

    fun not_prime_err n =
      let
        val _ = if #verbose config then warning ("Not a prime number: " ^ Int.toString n) else ()
      in
        NONE
      end

    fun certify p =
      case cert of
        SOME cert => SOME cert
      | NONE =>         
        let
          val p' = p |> HOLogic.dest_Trueprop |> dest_comb |> snd |> HOLogic.dest_number |> snd
        in
          case mk_cert p' of
            SOME cert =>
              let val _ = if #verbose config then print_cert cert else () in SOME cert end
          | NONE => not_prime_err p'
        end

    val replay =
      if #code config then
        if has_code_conv ctxt then
          replay_cert_code
        else
          let
            val _ =
              if #verbose config then
                warning
                  ("Code for Pratt certificates was not set up yet. " ^
                   "Load the theory Pratt_Certificate_Code to do this.")
              else
                ()
          in
            raise NO_CODE
          end
      else
        fst oo replay_cert (#cache config)
  in
    Subgoal.FOCUS_PARAMS (fn {concl, ...} =>
      case certify (Thm.term_of concl) of
        NONE => no_tac
      | SOME cert =>
          HEADGOAL (resolve_tac ctxt [replay cert ctxt])
    ) ctxt i
  end
    handle INVALID_CERT cert => cert_err config cert
         | NO_CODE => no_tac

end


val default_config = {verbose = true, code = false, cache = []}

local

  val silent : (tac_config -> tac_config) parser =
    Args.$$$ "silent" >>
      (K (fn {code, cache, ...} => {verbose = false, code = code, cache = cache}))
  val code : (tac_config -> tac_config) parser =
    Args.$$$ "code" >>
      (K (fn {verbose, cache, ...} => {verbose = verbose, code = true, cache = cache}))
  val option = silent || code
  val options =
    Scan.optional (Args.parens (Parse.list option) >>
      (fn fs => fold (fn f => fn g => f o g) fs I)) I
  
in

val tac_config_parser = options >> (fn f => f default_config)

end

end
