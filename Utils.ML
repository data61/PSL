(*  Title:      Utils.ML
    Author:     Yutaka Nagashima, Data61, CSIRO

This file provides utility functions that are not specific to Isabelle/HOL.
*)

(*** SEQ2 : Auxiliary functions on Seq.seq ***)
(*
  SEQ2 contains useful functions defined on Seq.seq that do not appear the Isabelle source code.
  AEQ2 does not have significant duplication with the Isabelle source code. 
*)
signature SEQ2 =
sig
  val mk_pairs   : ('a -> 'b Seq.seq) * 'c -> 'a -> 'd -> ('c * ('b * 'd)) Seq.seq;
  val map_arg    : 'a -> ('a -> 'b) Seq.seq -> 'b Seq.seq;
  val pairs      : 'a Seq.seq -> 'b Seq.seq -> ('a * 'b) Seq.seq;
  val foldr      : ('a * 'b -> 'b) -> 'b -> 'a Seq.seq -> 'b;
  val foldr1     : ('a * 'a -> 'a) ->       'a Seq.seq -> 'a;
  val seq_number : 'a Seq.seq -> (int * 'a) Seq.seq;
  val same_seq   : ('a * 'a -> bool) -> 'a Seq.seq * 'a Seq.seq -> bool;
  val powerset   : 'a Seq.seq -> 'a Seq.seq Seq.seq;
end;

(*** Seq2 : Auxiliary functions on Seq.seq ***)
structure Seq2 : SEQ2 =
struct

  fun mk_pairs ((func, logs):(('a -> 'b Seq.seq) * 'c)) goal ctxt =
    let
      val seq   = func goal
      val pairs = Seq.map (fn x => (logs, (x, ctxt))) seq
    in 
      pairs
    end;

  fun map_arg para funcs = case Seq.pull funcs of
    NONE => Seq.empty
  | SOME (func, funcs_tl) =>
      let
        fun tail _ = map_arg para funcs_tl
      in
        Seq.cons (func para) (tail ())
        handle THM _ =>   tail ()
             | Empty =>   tail ()
             | TERM _ =>  tail ()
             | TYPE _ =>  tail ()
             | ERROR _ => tail ()
      end;

  fun pairs (seq1:'a Seq.seq) (seq2:'b Seq.seq) = case Seq.pull seq1 of
    NONE        => Seq.empty
  | SOME (x,xs) => Seq.cons (pair x (Seq.hd seq2)) (pairs xs (Seq.tl seq2)) : ('a * 'b) Seq.seq;

  fun foldr f b xs = case Seq.pull xs of
    NONE         => b
  | SOME (y, ys) => f (y, foldr f b ys);

  fun foldr1 func sq = case Seq.pull sq of
    NONE   => error "Empty seq in foldr1."
  | SOME _ =>
    let
      fun itr_seq st = case Seq.pull st of
        NONE                => error "Empty seq."
      | SOME (st_hd, st_tl) => case Seq.pull st_tl of
          NONE => st_hd
        | SOME _ => func (st_hd, itr_seq  st_tl)
    in
      itr_seq sq
    end;
  
  fun seq_number (xs:'a Seq.seq) : (int * 'a) Seq.seq =
    let
      fun seq_number' (xs : 'a Seq.seq) (n:int) (ys : (int * 'a) Seq.seq) = case Seq.pull xs of
        NONE              => ys : (int * 'a) Seq.seq
      | SOME (x:'a, tail) => 
         if   n < 0 then error "seq_number' in Utils failed. negative index!"
         else seq_number' tail (n + 1) (Seq.append  ys (Seq.single (n, x)) : (int * 'a) Seq.seq);
    in
      seq_number' xs 0 Seq.empty
    end;

  (*For "same_seq test (xs, ys)" to be true, they have to be of the same length.*)
  fun same_seq (are_same : (('a * 'a) -> bool)) (xs:'a Seq.seq,  ys:'a Seq.seq):bool = case Seq.pull xs of
    NONE => (case Seq.pull ys of 
      NONE   => true
    | SOME _ => false)
  | SOME (x, _) => (case Seq.pull ys of
      NONE   => false
    | SOME (y, _) => are_same (x, y) andalso same_seq are_same (Seq.tl xs, Seq.tl ys));

  (*Starts from smaller sets.*)
  fun powerset (xs:'a Seq.seq) =
    let
      fun poset (ys, base) = case Seq.pull ys of
        NONE => Seq.single base
      | SOME (head, tail) => Seq.append (poset (tail, base)) (poset (tail, Seq.cons head base))
    in
      poset (xs, Seq.empty)
    end;
end;

(*** UTILS : Utility functions not specific to Isabelle/HOL. ***)
signature UTILS =
sig
  val flip           : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c;
  val delay          : ('a -> 'b) * 'a -> 'b;
  val map_arg        : 'a -> ('a -> 'b) list -> 'b list;
  (*map_pair and pair_to_list are useful only if the pair consists of the same type.*)
  val map_pair       : ('a -> 'b) -> 'a * 'a -> 'b * 'b;
  val pair_to_list   : 'a * 'a -> 'a list;
  val list_to_pair   : 'a list -> 'a * 'a;
  val init           : 'a list -> 'a list;
  val intersperse    : 'a -> 'a list -> 'a list;
  val is_in_paren    : string -> bool;
  val ??             : ('a -> bool) * ('a -> 'a) -> 'a -> 'a;
  val rm_parentheses_with_contents_in_the_end : string -> string;
  val rm_parentheses : string -> string;
  val remove__s      : string -> string;
  val push_to_front  : string -> string list -> string list;
  val the'           : string -> 'a option -> 'a;
  val prefix_if_nonempty : string -> string list -> string list;
  val debug          : bool; (*flag for debugging.*)
end;

(*** Utils : Utility functions not specific to Isabelle/HOL. ***)
structure Utils:UTILS =
struct            

fun flip f x y = f y x;

infix delay;
fun (f delay x) =  f x;

(*map_arg maps a parameter to a list of functions.*)
fun map_arg _      []           = []
 |  map_arg param (func::funcs) = func param :: map_arg param funcs;

fun map_pair func (a, b) = (func a, func b);

fun pair_to_list (x, y) = [x, y];

fun list_to_pair [a,b] = (a,b)
 |  list_to_pair _ = error "list_to_pair failed. The length of lsit is not two.";

fun init [] = error "init failed. empty list"
 |  init xs = take (length xs - 1) xs;

fun intersperse _   []      = []
 |  intersperse _   (x::[]) = [x]
 |  intersperse int (x::xs) = x::int::intersperse int xs

fun is_in_paren str = String.isPrefix "(" str;

fun rm_parentheses_with_contents_in_the_end str =
  let
    val tokens = Symbol.explode str;
    val parser = Scan.repeat (Scan.unless ($$ "(" ) (Scan.one Symbol.not_eof));
    val result = Scan.finite Symbol.stopper parser tokens |> fst |> String.concat;
  in
    result
  end;

infix ??;
fun ass ?? f = fn x => if ass x  then f x else x;

fun rm_parentheses str = (is_in_paren ?? unenclose) str;

fun remove__s name =
  let
    val suffix_is__ = String.isSuffix "_" name;
    val remove_     = unsuffix "_";
    val wo__s       = (suffix_is__ ? (remove__s o remove_)) name
  in
    wo__s
  end;

fun push_to_front key things = 
  filter     (String.isSubstring key) things @
  filter_out (String.isSubstring key) things;

fun the' (mssg:string)  NONE        = error mssg
 |  the' (_   :string) (SOME thing) = thing

fun prefix_if_nonempty _        [] = []
 |  prefix_if_nonempty prefixed xs = prefixed :: xs : string list;

val debug = false;

end;

(*** ISABELLE_UTILS : Utility functions specific to Isabelle/HOL. ***)
signature ISABELLE_UTILS =
sig
  val get_1st_subg                  : thm -> term option;
  val flatten_trm                   : term -> term list;
  val get_trms_in_thm               : thm -> term list;
  val get_typ_names_in_trm          : term -> string list;
  val get_const_names_in_thm        : thm -> string list;
  val get_const_names_in_1st_subg   : thm -> string list;
  val get_abs_names_in_trm          : term -> string list;
  val get_abs_names_in_thm          : thm -> string list;
  val get_abs_name_in_1st_subg      : thm -> string list;
  val get_typ_names_in_thm          : thm -> string list;
  val get_typ_names_in_1st_subg     : thm -> string list;
  val get_free_var_names_in_trms    : term list -> string list;
  val get_free_var_names_in_thm     : thm -> string list;
  val get_free_var_names_in_1st_subg: thm -> string list;
  val get_all_var_names_in_1st_subg : thm -> string list;
  val proof_state_to_thm            : Proof.state -> thm;
  val mk_proof_obligation           : Proof.context -> string -> thm;
  val TIMEOUT_in                    : real -> ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq;
  val TIMEOUT                       : ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq;
  val same_except_for_fst_prem      : thm -> thm -> bool;
  val defer                         : thm -> thm Seq.seq;
end;

(*** Isabelle_Utils : Utility functions specific to Isabelle/HOL. ***)
structure Isabelle_Utils : ISABELLE_UTILS  =
struct
fun get_1st_subg (goal:thm) = (SOME o hd) (Thm.prems_of goal) handle Empty => NONE : term option;

fun flatten_trm (trm1 $ trm2) = flat [flatten_trm trm1, flatten_trm trm2]
  | flatten_trm trm = [trm];

fun get_trms_in_thm (thm:thm) = Thm.cprop_of thm |> Thm.term_of |> flatten_trm;

fun get_const_names_in_thm thm = thm
  |> Thm.cprop_of
  |> Thm.term_of
  |> (fn subg:term => Term.add_const_names subg []);

fun get_const_names_in_1st_subg (goal:thm) = goal
  |> get_1st_subg
  |> Option.map (fn subg:term => Term.add_const_names subg [])
  |> these;

fun get_typs_in_trm (Const (_ ,T))    = [T]
 |  get_typs_in_trm (Free (_, T))     = [T]
 |  get_typs_in_trm (Var (_, T))      = [T]
 |  get_typs_in_trm (Bound _)         = []
 |  get_typs_in_trm (Abs (_, T, trm)) = T :: get_typs_in_trm trm
 |  get_typs_in_trm (trm1 $ trm2)     = get_typs_in_trm trm1 @ get_typs_in_trm trm2;

local
  fun get_typ_names' (Type (name, typs)) = name :: flat (map get_typ_names' typs)
   |  get_typ_names' (TFree (name, _))   = [name]
   |  get_typ_names' (TVar (_, _))       = [];
in
  fun get_typs_names (typs:typ list) = map get_typ_names' typs |> flat;
end;

fun get_abs_names_in_trm (Abs (name, _, trm)) =
      name :: (trm |> flatten_trm |> map get_abs_names_in_trm |> flat)
 |  get_abs_names_in_trm (trm1 $ trm2) = get_abs_names_in_trm trm1 @ get_abs_names_in_trm trm2
 |  get_abs_names_in_trm _ = [];

fun get_abs_names_in_thm thm = thm |> Thm.cprop_of |> Thm.term_of |> get_abs_names_in_trm;

fun get_abs_name_in_1st_subg (goal:thm) = goal
  |> get_1st_subg
  |> Option.map get_abs_names_in_trm
  |> these
  |> map Utils.remove__s;

fun get_typ_names_in_trm trm = trm 
  |> get_typs_in_trm
  |> get_typs_names
  |> duplicates (op =)
  |> map Utils.remove__s;

fun get_typ_names_in_thm thm = thm 
  |> get_trms_in_thm
  |> map get_typ_names_in_trm
  |> flat
  |> duplicates (op =)
  |> map Utils.remove__s;

fun get_typ_names_in_1st_subg (goal:thm) = goal
  |> get_1st_subg
  |> Option.map get_typ_names_in_trm
  |> these
  |> map Utils.remove__s;

fun get_free_var_names_in trm = if Term.is_Free trm 
  then [Term.dest_Free trm |> fst |> Utils.remove__s] else [];

fun get_free_var_names_in_trms trms = trms
  |> map get_free_var_names_in
  |> List.concat
  |> distinct (op =);

fun get_free_var_names_in_thm thm = thm
  |> get_trms_in_thm
  |> get_free_var_names_in_trms;

fun get_free_var_names_in_1st_subg (goal:thm) = goal
  |> get_1st_subg
  |> Option.map (fn subg:term => Term.add_frees subg [])
  |> Option.map (map fst)
  |> these
  |> map Utils.remove__s;

fun get_all_var_names_in_1st_subg (goal:thm) =
    Option.map (map fst o strip_all_vars) (get_1st_subg goal)
  |> these
  |> map Utils.remove__s : string list;

val proof_state_to_thm = #goal o Proof.goal;

fun mk_proof_obligation ctxt (prop_str:string) = 
  Syntax.read_prop ctxt prop_str
  |> Thm.cterm_of ctxt
  |> Thm.trivial;

local
(* SINGLE is copied from Tactical.ML, but the types are more general.*)
fun SINGLE tacf = Option.map fst o Seq.pull o tacf;

(* DETERM_TIMEOUT was originally written by Jasmin Blanchette in nitpick_util.ML.
 * This version has exception handling on top of his version.*)
fun DETERM_TIMEOUT delay tac st =
  Seq.of_list (the_list (Timeout.apply delay (fn () => SINGLE tac st) ()
   handle Timeout.TIMEOUT _ => NONE));
in

fun TIMEOUT_in real tac = DETERM_TIMEOUT (seconds real) tac;

fun TIMEOUT tac         = DETERM_TIMEOUT (seconds 0.3) tac;

end;

(*same_except_for_fst_prem checks if two thms are the same except for the first premise of the second.*)
fun same_except_for_fst_prem (goal1:thm) (goal2:thm) =
let
  (*goal1 should have one less premise.*)
  val concl1                            = Thm.concl_of goal1 : term ;
  val concl2                            = Thm.concl_of goal2 : term ;
  val eq_concl                          = Term.aconv (concl1, concl2);
  val prems1                            = Thm.prems_of goal1 : term list;
  val prems2                            = Thm.prems_of goal2 : term list ;
  val goal1_has_a_prem                  = List.null prems1 : bool ;
  fun prems1_prems2tl prems1 prems2     = prems1 ~~ List.tl prems2;
  fun prems1_equiv_prems2 prems1 prems2 = List.all (Term.aconv) (prems1_prems2tl prems1 prems2);
  fun test prems1 prems2                = eq_concl andalso prems1_equiv_prems2 prems1 prems2;
in
  if goal1_has_a_prem then test prems1 prems2 else true
end;

val defer = defer_tac 1;

end;

(*** FIND_THEOREMS2: provides an interface of find_theorem for PSL. ***)
(*
 FIND_THEOREMS2 provides an interface of find_theorem for PSL.
 FIND_THEOREMS2 does not include significant code duplication with the Isabelle source code.
*)
signature FIND_THEOREMS2 =
sig
  include FIND_THEOREMS;
  type context;
  type ref;
  type get_rules = context -> thm -> (ref * thm) list;
  type get_rule_names = context -> thm -> string list;
  val get_criterion             : string -> string -> (bool * 'a criterion) list;
  val name_to_rules             : context -> thm -> string -> string -> (ref * thm) list;
  val names_to_rules            : context -> thm -> string -> string list -> (ref * thm) list
  val get_rule_names            : get_rules -> context -> thm -> xstring list;
  val get_simp_rules            : get_rules;
  val get_induct_rules          : get_rules;
  val get_coinduction_rules     : get_rules;
  (* These get_(elim, intro, dest)_rules may not be powerful enough. *)
  val get_elim_rules            : get_rules;
  val get_intro_rules           : get_rules;
  val get_dest_rules            : get_rules;
  val get_split_rules           : get_rules;
  val get_simp_rule_names       : get_rule_names;
  val get_induct_rule_names     : get_rule_names;
  val get_coinduction_rule_names: get_rule_names;
  val get_elim_rule_names       : get_rule_names;
  val get_intro_rule_names      : get_rule_names;
  val get_dest_rule_names       : get_rule_names;
  val get_split_rule_names      : get_rule_names;
  val get_fact_names_mesh       : Proof.state -> string list;
end;

(*** Find_Theorems2: provides an interface of find_theorem for PSL. ***)
structure Find_Theorems2 : FIND_THEOREMS2 =
struct

open Find_Theorems;

type context = Proof.context;
type ref = Facts.ref;
type get_rules = context -> thm -> (ref * thm) list;
type get_rule_names = context -> thm -> string list;

fun get_criterion kind_name name = [(true, Name name), (true, Name kind_name)];

fun name_to_rules ctxt goal kind_name name =
  find_theorems ctxt (SOME goal) NONE true (get_criterion kind_name name) |> snd;

fun names_to_rules ctxt goal kind_name names = names
  |> map (name_to_rules ctxt goal kind_name)
  |> flat
  |> distinct (Thm.eq_thm o Utils.map_pair snd);

fun get_rule_names (get_rules:context -> thm -> (ref * thm) list) ctxt goal =
  let
    val related_rules          = get_rules ctxt goal;
    val related_rule_names     = map (Facts.string_of_ref o fst) related_rules;
    fun get_thm  thm_nm        = SOME (Proof_Context.get_thm  ctxt thm_nm) handle ERROR _ => NONE;
    fun get_thms thm_nm        = SOME (Proof_Context.get_thms ctxt
      (Utils.rm_parentheses_with_contents_in_the_end thm_nm)) handle ERROR _ => NONE;
    fun cannot_get_thm  thm_nm = is_none (get_thm thm_nm);
    fun cannot_get_thms thm_nm = is_none (get_thms thm_nm);
    fun cannot_get thm_nm      = cannot_get_thm thm_nm andalso cannot_get_thms thm_nm;
    val available_rule_names   = filter_out cannot_get related_rule_names;
  in
    available_rule_names
  end;

fun get_simp_rules (ctxt:context) (goal:thm) =
  let
    val const_names   = Isabelle_Utils.get_const_names_in_1st_subg goal;
    val related_rules = names_to_rules ctxt goal "" const_names;
    val simpset_thms  = ctxt |> simpset_of |> Raw_Simplifier.dest_ss |> #simps |> map snd;
    fun eq_test (thm1, (_, thm2)) = Thm.eq_thm (thm1, thm2);
    val unique_rules  = subtract eq_test simpset_thms related_rules;
  in
    unique_rules : (Facts.ref * thm) list
  end;

fun get_simp_rule_names ctxt goal = get_rule_names get_simp_rules ctxt goal : string list;

fun get_induct_rules (ctxt:context) (goal:thm) =
  let
    val const_names  = Isabelle_Utils.get_const_names_in_1st_subg goal : string list;
    val induct_rules = names_to_rules ctxt goal ".induct" const_names;
  in
    induct_rules : (Facts.ref * thm) list
  end;
fun get_induct_rule_names ctxt goal = get_rule_names get_induct_rules ctxt goal : string list;

fun get_coinduction_rules (ctxt:context) (goal:thm) =
  let
    val const_names   = Isabelle_Utils.get_const_names_in_1st_subg goal : string list;
    fun get_coinduct_rules post = names_to_rules ctxt goal post const_names;
    val coinduct_rules1 = get_coinduct_rules ".coinduct";
    val coinduct_rules2 = get_coinduct_rules ".coinduct_strong";
  in
    coinduct_rules1 @ coinduct_rules2: (Facts.ref * thm) list
  end;
fun get_coinduction_rule_names ctxt goal = get_rule_names get_coinduction_rules ctxt goal : string list;

fun get_elim_rules  ctxt goal = find_theorems ctxt (SOME goal) NONE true [(true, Elim)] |> snd;
fun get_intro_rules ctxt goal = find_theorems ctxt (SOME goal) (SOME 100) true [(true, Intro)] |> snd;
fun get_dest_rules  ctxt goal = find_theorems ctxt (SOME goal) (SOME 100) true [(true, Dest)] |> snd;
        
fun get_elim_rule_names  ctxt goal = get_rule_names get_elim_rules  ctxt goal : string list;
fun get_intro_rule_names ctxt goal = get_rule_names get_intro_rules ctxt goal : string list;
fun get_dest_rule_names  ctxt goal = get_rule_names get_dest_rules  ctxt goal : string list;

fun get_split_rules ctxt goal =
  let
    (*For split, we need to use typ_names instead of const_names.*)
    val used_typ_names = Isabelle_Utils.get_typ_names_in_1st_subg goal;
    val related_rules  = names_to_rules ctxt goal "split" used_typ_names
  in
    related_rules : (Facts.ref * thm) list
  end;

fun get_split_rule_names ctxt goal = get_rule_names get_split_rules ctxt goal;

fun get_fact_names_mesh (state: Proof.state) =
  let
    val {context: Proof.context, goal: thm, facts: thm list} = Proof.goal state;
    val (_, hyps: term list, cncl: term) = ATP_Util.strip_subgoal goal 1 context;
    val params as {provers: string list,...}: Sledgehammer_Commands.params =
      Sledgehammer_Commands.default_params (Proof.theory_of state) [];
    val keywords    = Thy_Header.get_keywords' context: Keyword.keywords;
    val rule_table  = Sledgehammer_Fact.clasimpset_rule_table_of context
      : ATP_Problem_Generate.status Termtab.table;
    val all_facts   = Sledgehammer_Fact.all_facts context true true keywords [] facts rule_table
      : Sledgehammer_Fact.raw_fact list;
    val no_override = Sledgehammer_Fact.no_fact_override: Sledgehammer_Fact.fact_override;
    val relevant_facts : (string * Sledgehammer_MaSh.fact list) list =
      Sledgehammer_MaSh.relevant_facts context params (hd provers) 1000 no_override hyps cncl all_facts;
    (*convert relevant facts into a string list*)
    val relevant_fact_names = relevant_facts |> map #2 |> flat |> map (fn x => #1 (#1 x));
  in
    relevant_fact_names : string list
  end;

end;

(*** DYNAMIC_UTILS: Utility functions useful to generate tactics at run-time. ***)
signature DYNAMIC_UTILS =
sig
  type context;
  type state;
  type src;
  type 'a seq;
  type 'a nontac   = 'a -> 'a seq;
  datatype node    = Subgoal | Done | Defer
                   | Apply of {using:string list, methN:string, back:int};
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

(*** Dynamic_Utils: Utility functions useful to generate tactics at run-time. ***)
structure Dynamic_Utils : DYNAMIC_UTILS =
struct

type context     = Proof.context;
type state       = Proof.state;
type src         = Token.src;
type 'a seq      = 'a Seq.seq;
type 'a nontac   = 'a -> 'a seq;
datatype node    = Subgoal | Done | Defer
                 | Apply of {using:string list, methN:string, back:int};
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
    val results     = Proof.apply text_range proof_state
                      handle ERROR _ => Seq.empty
                           | Empty   => Seq.empty
                           | THM _   => Seq.empty
                           | TERM _  => Seq.empty
                           | TYPE _  => Seq.empty
                    :  Proof.state Seq.result Seq.seq;
    val filtered_results = Seq.filter_results results :  Proof.state Seq.seq;
  in
    filtered_results : Proof.state Seq.seq
  end;

fun writer_to_state (writerTSeq : (log * 'state) seq) (trace : log) =
  Seq.map (fn (this_step, pstate) => (trace @ this_step, pstate)) writerTSeq : (log * 'state) seq

fun add_back (n, (Apply {methN = methN, using = using, ...}, result)) =
  ([Apply {methN = methN, using = using, back = n}], result)
  | add_back (0, (other, result)) = (tracing "add_back 0";([other], result))
  | add_back _ = (tracing "add_back in Dynamic_Utils.thy failed."; error "add_back")

fun nontac_to_logtac (node:node) (nontac:'a nontac) (goal:'a) : (log * 'a) seq = 
    Seq.map (fn result => (node, result)) (nontac goal)
 |> Seq2.seq_number
 |> Seq.map add_back
  handle ERROR _ => Seq.empty
       | Empty   => Seq.empty
       | THM _   => Seq.empty
       | TERM _  => Seq.empty
       | TYPE _  => Seq.empty;

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
    val nontac_with_TO = Isabelle_Utils.TIMEOUT_in 1.0  nontac                      : state nontac;
    val trace_node     = Apply {using = [], methN = meth_name, back = 0}    : node;
    val logtac         = nontac_to_logtac trace_node nontac_with_TO         : state logtac;
    val stttac         = logtac_to_stttac logtac                            : state stttac;
  in
    stttac : state stttac
  end;

local
  fun mk_using  ([]   : string list) = ""
   |  mk_using  (using: string list) = "using " ^ String.concatWith " " using ^ " ";
  fun mk_apply methN  = "apply (" ^ methN ^ ")";
  fun mk_backs (n:int) = replicate n "back" |> String.concatWith " " handle Subscript =>
    (tracing "mk_backs in Isabelle_Utils.thy failed. It should take 0 or a positive integer.";"");
  fun mk_apply_script1 {methN : string, using : string list, back : int} =
    mk_using using ^ mk_apply methN ^ mk_backs back ^ "\n";
  fun mk_proof_script1 (Done    : node) = "done \n"
   |  mk_proof_script1 (Subgoal : node) = "subgoal \n"
   |  mk_proof_script1 (Defer   : node) = "defer \n"
   |  mk_proof_script1 (Apply n : node) = mk_apply_script1 n;
in
  fun mk_apply_script (log:log) =
   (tracing ("Number of lines of commands: " ^ (length log |> Int.toString));
    map mk_proof_script1 log
    |> String.concat
    |> Active.sendback_markup_properties [Markup.padding_command]) : string;
end;

end;