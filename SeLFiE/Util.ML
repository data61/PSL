(*  Title:      PSL/SeLFiE/src/Preprocessor/Util.ML
    Author:     Yutaka Nagashima, Data61, CSIRO
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Helper functions for PSL and SeLFiE.
*)

type strings = string list;
type ints    = int    list;
type terms   = term list;
type thms    = thm list;
infix 1 >>= <$> <|>;
fun (m >>= f) = Option.mapPartial f m;
fun (m <$> f) = Option.map f m;
fun (NONE   <|> NONE  ) = NONE
  | (NONE   <|> SOME x) = SOME x
  | (SOME x <|> NONE  ) = SOME x
  | (SOME x <|> SOME _) = SOME x;

(*** UTILS : Utility functions not specific to Isabelle/HOL. ***)
signature UTILS =
sig
  val flip                                    : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c;
  val flip_arg_pair                           : ('a * 'b -> 'c) -> 'b * 'a -> 'c;
  val delay                                   : ('a -> 'b) * 'a -> 'b;
  val map_arg                                 : 'a -> ('a -> 'b) list -> 'b list;
  (*map_pair and pair_to_list are useful only if the pair consists of the same type.*)
  val map_pair                                : ('a -> 'b) -> 'a * 'a -> 'b * 'b;
  val pair_to_list                            : 'a * 'a -> 'a list;
  val list_to_pair                            : 'a list -> 'a * 'a;
  val bool_to_real                            : bool -> real;
  val bool_to_int                             : bool -> int;
  val is_some_true                            : bool option -> bool;
  val is_some_false                           : bool option -> bool;
  val is_some_null                            : 'a list option -> 'a list;
  val opt_app                                 : ('a -> 'b) option -> 'a option -> 'b option;
  val eq                                      : ''a -> ''a -> bool;
  val init                                    : 'a list -> 'a list;
  val last                                    : 'a list -> 'a;
  val intersperse                             : 'a -> 'a list -> 'a list;
  val is_in_paren                             : string -> bool;
  val ??                                      : ('a -> bool) * ('a -> 'a) -> 'a -> 'a;
  val If                                      : 'a * 'a -> bool -> 'a;
  val rm_parentheses_with_contents_in_the_end : string -> string;
  val rm_parentheses                          : string -> string;
  val remove__s                               : string -> string;
  val push_to_front                           : string -> strings -> strings;
  val the'                                    : string -> 'a option -> 'a;
  val prefix_if_nonempty                      : string -> strings -> strings;
  val debug                                   : bool; (*flag for debugging.*)
  val debug_mssg                              : bool -> string -> 'a -> 'a;
  val try'                                    : string -> ('a -> 'b) -> 'a -> 'b;
  val try_with                                : 'b -> ('a -> 'b) -> 'a -> 'b;
  val are_same                                : (string * string) -> bool; (*FIXME: Isn't this redundant? We already have equal.*)
  val index                                   : 'a list -> (int * 'a) list;
  val power                                   : int -> int -> int;
  val nat_to_frac                             : int -> real;
  val count_str                               : string -> strings -> int;
  val is_one_of_strings                       : strings -> string -> bool;
  val somes                                   : 'a option list -> 'a list;
  val conjunction                             : bool -> bool -> bool;
  val disjunction                             : bool -> bool -> bool;
  val a_member                                : (('a * 'b) -> bool) -> 'a list -> 'b list -> bool;
  val members                                 : (('a * 'b) -> bool) -> 'a list -> 'b list -> bool;
  val cart_prod                               : 'a list -> 'b list -> ('a * 'b) list;
  val add_index                               : 'a list -> (int * 'a) list; (*index starts at 0*);
  val order_sensitive_multi_subset            : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool;
  val map_flat_distinct                       : (term -> 'a list) -> ('a * 'a -> bool) -> terms -> 'a list;
  val exist_n                                 : ('a -> bool) -> int -> 'a list -> bool;
  val exist_mult                              : ('a -> bool) -> 'a list -> bool;
  val mk_option_pair                          : ('a option * 'b option) -> ('a * 'b) option;
  val mk_options_pair                         : ('a * 'b) option -> ('a option * 'b option);
  val mapPartial2                             : ('a -> 'b option) -> ('a * 'a) option -> ('b * 'b) option;
  val alist_add                               : (''a * 'a) list -> (''a * 'a) -> (''a * 'a) list;
  val alist_lookup_eq                         : (''a * 'a) list -> ''a -> 'a option;
  val opt_equal                               : (''a option * ''a option) -> bool;
  val ints_to_max_option                      : ints -> int option;
  val mk_ints                                 : int -> ints;
end;

(*** Utils : Utility functions not specific to Isabelle/HOL. ***)
structure Utils:UTILS =
struct

fun flip f x y = f y x;

fun flip_arg_pair (f:('a * 'b)-> 'c) = (fn p:('b * 'a) => f (swap p)): ('b * 'a) -> 'c;

infix delay;
fun (f delay x) =  f x;

(*map_arg maps a parameter to a list of functions.*)
fun map_arg _      []           = []
 |  map_arg param (func::funcs) = func param :: map_arg param funcs;

fun map_pair func (a, b) = (func a, func b);

fun pair_to_list (x, y) = [x, y];

fun list_to_pair [a,b] = (a,b)
 |  list_to_pair _ = error "list_to_pair failed. The length of lsit is not two.";

fun bool_to_real b = if b then 1.0 else 0.0;

fun bool_to_int b = if b then 1 else 0;

fun is_some_true maybe = Option.getOpt (maybe, false);

fun is_some_false  NONE    = false
  | is_some_false (SOME b) = not b;

fun is_some_null maybe = Option.getOpt (maybe, []);

fun opt_app (SOME f: ('a -> 'b) option) (SOME x: 'a option) = SOME (f x)
  | opt_app  _                           _                  = NONE;

val eq = (fn x => is_some_true o (try (equal x))): ''a -> ''a -> bool;

fun init [] = error "init failed. empty list"
 |  init xs = take (length xs - 1) xs;

fun last [] = raise List.Empty
  | last [x] = x
  | last (_::xs) = last xs;

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

fun If (thn, els) (b:bool) = if b then thn else els;

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
 |  prefix_if_nonempty prefixed xs = prefixed :: xs : strings;

val debug = false;

fun debug_mssg switch (str:string) f = if switch then (tracing str; f) else f;

fun try' (mssg:string) (f:'a -> 'b) (x:'a) = (case try f x of
  NONE   => error mssg
| SOME y => y);

fun try_with  (fallback:'b) (f:'a -> 'b) (x:'a) = (case try f x of
  NONE => fallback
| SOME y => y);

fun to_bool EQUAL = true
 |  to_bool _     = false;

fun are_same (x, y) = (to_bool o String.compare) (x, y);

fun index (zs:'a list) =
  let
    fun index' _ ys  []             = ys
      | index' i ys (x::xs:'a list) = index' (i+1) ((i, x)::ys) xs
  in
    List.rev (index' (1:int) [] zs): (int * 'a) list
  end;

fun power' (_, 0, z) = z
  | power' (x, y, z) = power' (x, y-1, x * z);

fun power x n = power' (x, n, 1);

fun nat_to_frac (n:int) =
  let
    val digit     = Int.toString n |> String.size : int;
    val divide_by = power 10 digit |> Real.fromInt : real;
    val frac      = Real.fromInt n / divide_by : real;
  in
    frac : real
  end;

fun count_str (str:string) (strs:strings) =
  fold (fn name => fn n => if name = str then n + 1 else n) strs 0;

fun is_one_of_strings (strs:strings) (str:string) = exists (equal str) strs;

fun somes (maybes: 'a option list) = filter is_some maybes |> map the;

fun conjunction x y = x andalso y;

fun disjunction x y = x orelse y;

fun a_member (eq:('a * 'b) -> bool) (one_of_them: 'a list) (in_those: 'b list) =
  fold (fn x:'a => fn b => b orelse member eq in_those x) (one_of_them:'a list) false;

fun members (eq:('a * 'b) -> bool) (all_of_them: 'a list) (in_those: 'b list) =
  fold (fn x:'a => fn b => b andalso member eq in_those x) (all_of_them:'a list) true;

fun cart_prod (xs:'a list) (ys:'b list) =
  let
    fun cart_prod' ([]   :'a list) (_ :'b list) (acc:('a * 'b) list) = acc
      | cart_prod' (x::xs:'a list) (ys:'b list) (acc:('a * 'b) list) =
        cart_prod' xs ys (map (pair x) ys @ acc);
  in cart_prod' xs ys [] end;

fun add_index'     []  result _   = result
  | add_index' (x::xs) result idx = add_index' xs (result @ [(idx, x)]) (idx + 1) ;
fun add_index xs = add_index' xs [] 0;

fun order_sensitive_multi_subset _      []      _   = true
  | order_sensitive_multi_subset _  (_:: _)     []  = false
  | order_sensitive_multi_subset eq (x::xs) (y::ys) =
  if eq x y
  then order_sensitive_multi_subset eq     xs  ys
  else order_sensitive_multi_subset eq (x::xs) ys;

fun map_flat_distinct mapped eq arg  = map mapped arg |> flat |> distinct eq;

fun error_if_less_than_0 (n:int) x = if n < 0 then error "exist_n failed. n is less than 0" else x;

fun exist_n (_:'a -> bool)  (0:int) (_    :'a list) = true
  | exist_n (_:'a -> bool)  (n:int) ([]   :'a list) = error_if_less_than_0 n false
  | exist_n (f:'a -> bool)  (n:int) (x::xs:'a list) =
    error_if_less_than_0 n (if f x then exist_n f (n - 1) xs else exist_n f n xs);

val _ = @{assert} (exist_n (equal "a") 2 ["a","b","c","d","b"]          |> not);
val _ = @{assert} (exist_n (equal "b") 2 ["a","b","c","d","b"]);
val _ = @{assert} (exist_n (equal "b") 1 ["a","b","c","d","b"]);
val _ = @{assert} (exist_n (equal "b") 3 ["a","b","c","d","b"]          |> not);
val _ = @{assert} (exist_n (equal "c") 3 ["a","b","c","d","b", "c"]     |> not);
val _ = @{assert} (exist_n (equal "c") 3 ["a","b","c","d","b", "c", "c"]);
val _ = @{assert} (exist_n (equal "c") 2 ["a","b","c","d","b", "c", "c"]);

fun exist_mult  (f:'a -> bool) (xs:'a list) = exist_n f 2 xs;

val _ = @{assert} (exist_mult (equal "b") ["a","b","c","d","b"]);
val _ = @{assert} (exist_mult (equal "c") ["a","b","c","d"] |> not);

fun mk_option_pair (SOME x, SOME y) = SOME (x, y)
  | mk_option_pair  _               = NONE;

fun mk_options_pair  NONE         = (NONE,   NONE  )
  | mk_options_pair (SOME (x, y)) = (SOME x, SOME y)

fun mapPartial2  (f:'a -> 'b option) (SOME (x1, x2)) =
  let
    val (res1, res2) = apply2 f (x1,x2);
    val result = case res1 of
        SOME r1 => (case res2 of SOME r2 => SOME (r1, r2) | _ => NONE)
      | _ => NONE;
    in result end
  | mapPartial2 _ _ = NONE;

fun alist_add       (alist: (''a * 'a) list) (key:''a, value:'a) = AList.update (op =) (key, value) alist: (''a * 'a) list;

fun alist_lookup_eq (alist: (''a * 'b) list) (key:''a)           = AList.lookup (op =) alist key;

fun opt_equal (SOME x, SOME y) = x = y
  | opt_equal (     _,      _) = false: bool;

fun ints_to_max' ([]:ints)    acc = acc
  | ints_to_max' (i::is:ints) acc = ints_to_max' is (Int.max (i, acc));

fun ints_to_max_option  []          = NONE
  | ints_to_max_option (i::is:ints) = SOME (ints_to_max' is i)

fun mk_ints (n:int) = List.tabulate (n, I);

end;

(*** SEQ2 : Auxiliary functions on Seq.seq ***)
(*
  SEQ2 contains useful functions defined on Seq.seq that do not appear the Isabelle source code.
  AEQ2 does not have significant duplication with the Isabelle source code. 
*)
signature SEQ2 =
sig
  val mk_pairs      : ('a -> 'b Seq.seq) * 'c -> 'a -> 'd -> ('c * ('b * 'd)) Seq.seq;
  val map_arg       : 'a -> ('a -> 'b) Seq.seq -> 'b Seq.seq;
  val pairs         : 'a Seq.seq -> 'b Seq.seq -> ('a * 'b) Seq.seq;
  val foldr         : ('a * 'b -> 'b) -> 'b -> 'a Seq.seq -> 'b;
  val foldr1        : ('a * 'a -> 'a) ->       'a Seq.seq -> 'a;
  val seq_number    : 'a Seq.seq -> (int * 'a) Seq.seq;
  val same_seq      : ('a * 'a -> bool) -> 'a Seq.seq * 'a Seq.seq -> bool;
  val powerset      : 'a Seq.seq -> 'a Seq.seq Seq.seq;
  val seq_to_option : 'a Seq.seq -> 'a option;
  val try_seq       : ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq;
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
        fun tail _ = map_arg para funcs_tl;
        val result = Seq.make (fn () => SOME (func para, tail ()));
      in
       result
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

  (*seq_to_op ignores tails*)
  fun seq_to_option (seq:'a Seq.seq) : 'a option = case Seq.pull seq of
     NONE => NONE
   | SOME (head, _) => SOME head;

  fun try_seq (f:'a -> 'b Seq.seq) (x:'a) = (case try f x of
    NONE => Seq.empty
  | SOME y => y);

end;

(*** ISABELLE_UTILS : Utility functions specific to Isabelle/HOL. ***)
signature ISABELLE_UTILS =
sig
  datatype location = Fst_Subg | Concl | All_Subg;
  val is_Abs                            : term -> bool;
  val is_App                            : term -> bool;
  val if_solved                         : thm -> 'a -> 'a -> 'a;
  val fst_qualifier                     : string -> string;
  val get_1st_subg                      : thm -> term option;
  val flatten_trm                       : term -> terms;
  val get_trms_in_thm                   : thm -> terms;
  val get_trm_in                        : location -> thm -> term option;(*Should it return a list of terms?*)
  val get_cnames_in_trm                 : term -> strings;
  val get_outmost_cname                 : term -> string option;
  val get_typ_names_in_trm              : term -> strings;
  val get_consts_in_thm                 : thm -> terms;
  val get_cnames_in_thm                 : thm -> strings;
  val get_cnames_in_1st_subg            : thm -> strings;
  val get_abs_names_in_trm              : term -> strings;
  val get_abs_names_in_thm              : thm -> strings;
  val get_abs_name_in_1st_subg          : thm -> strings;
  val get_typ_names_in_thm              : thm -> strings;
  val get_typ_names_in_1st_subg         : thm -> strings;
  val get_free_var_names_in_trm         : term -> strings;
  val get_free_var_names_in_trms        : terms -> strings;
  val get_free_var_names_in_thm         : thm -> strings;
  val get_free_var_names_in_1st_subg    : thm -> strings;
  val get_all_var_names_in_1st_subg     : thm -> strings;
  val proof_state_to_thm                : Proof.state -> thm;
  val pst_to_fst_subg                   : Proof.state -> term option;
  val pst_to_subgs                      : Proof.state -> term list;
  val mk_proof_obligation               : Proof.context -> string -> thm;
  val timeout_apply                     : Time.time -> ('a -> 'b) -> 'a -> 'b;
  val TIMEOUT_in                        : real -> ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq;
  val TIMEOUT                           : ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq;
  val same_except_for_fst_prem          : thm -> thm -> bool;
  val defer                             : thm -> thm Seq.seq;
  val is_in_Main                        : Proof.context -> thm -> bool;
  val add_const_names_mult              : term -> strings -> strings;
  val get_meth_name                     : Method.text -> string;
  val are_all_de_Bruijn_indices_used    : term -> bool;
  val pstate_to_usings                  : Proof.state -> thms;
  val pstate_to_chained_facts_as_terms  : Proof.state -> terms;
  val trm_to_fst_args_of_const          : string -> term -> terms;
  val trm_to_snd_args_of_const          : string -> term -> terms;
  val pstate_to_1st_subg_n_chained_facts: Proof.state -> terms;
  val pstate_to_1st_subg_n_chained_facts_record   : Proof.state -> {fst_subg:term option, chained_facts:terms};
  val pstate_to_cnames_in_1st_subg_n_chained_facts: Proof.state -> string list;
  val trms_have_cname                             : string -> terms -> bool;
  val trm_has_prop                                : term -> bool;
  val trm_to_prop_trms                            : term -> terms;
  val is_typ_of_name                              : string -> typ -> bool;
  val is_nat_typ                                  : typ -> bool;
  val trm_has_nat_typ                             : term -> bool;
  val trm_to_nats                                 : term -> {consts: term list, frees: term list, vars: term list};
  val is_fun_typ                                  : typ -> bool;
  val trm_has_fun_typ                             : term -> bool;
  val trm_to_funs                                 : term -> {consts: term list, frees: term list, vars: term list};
  val is_set_typ                                  : typ -> bool;
  val trm_has_set_typ                             : term -> bool;
  val is_int_typ                                  : typ -> bool;
  val trm_has_int_typ                             : term -> bool;
  val is_record_trm                               : term -> bool;
  val trm_to_sets                                 : term -> {consts: term list, frees: term list, vars: term list};
  val is_list_typ                                 : typ -> bool;(*TODO: this name is misleading.*)
  val trm_has_list_typ                            : term -> bool;
  val trm_to_lists                                : term -> {consts: term list, frees: term list, vars: term list};
  val trm_to_sets_and_lists                       : term -> {consts: term list, frees: term list, vars: term list};
  val trm_to_string                               : Proof.context -> term -> string;
  val count_numb_of_args_of_fun_typ               : typ -> int;
  val is_recursive_eq_about_cosnt_name            : term -> string -> bool;
  val has_recursive_simp_about_const_names        : Proof.context -> strings -> bool;
  val has_recursive_simp_about_const_name         : Proof.context -> string -> bool;
  val has_recursive_psimp_about_const_name        : Proof.context -> string -> bool;
  val normalize_trm_as_string                     : Proof.context -> string -> string;
  val contract_abbrevs                            : Proof.context -> term -> term;
  val strip_atyp                                  : term -> term;
  val takes_n_arguments                           : term -> int -> bool;
end;

(*** Isabelle_Utils : Utility functions specific to Isabelle/HOL. ***)
structure Isabelle_Utils : ISABELLE_UTILS  =
struct

fun is_Abs (Abs _) = true
  | is_Abs  _      = false;

fun is_App (_ $ _) = true
  | is_App  _      = false;

fun if_solved (goal:thm) then_clause else_clause =
  if Thm.nprems_of goal = 0 then then_clause else else_clause;

(*fst_qualifier "abc.def.ghi" = "abc"*)
fun fst_qualifier (lname:string) = Option.getOpt (lname |> Long_Name.explode |> try hd, "");

fun get_1st_subg (goal:thm) = (SOME o hd) (Thm.prems_of goal) handle Empty => NONE : term option;

(*TODO: Double check if we should ignore the sub-term in Abs.*)
fun flatten_trm (trm1 $ trm2) = flat [flatten_trm trm1, flatten_trm trm2]
  | flatten_trm trm = [trm];

fun get_trms_in_thm (thm:thm) = Thm.cprop_of thm |> Thm.term_of |> flatten_trm;

datatype location = Fst_Subg | Concl | All_Subg;

fun get_trm_in Fst_Subg g = get_1st_subg g
  | get_trm_in All_Subg g = try (Logic.mk_conjunction_list o Thm.prems_of) g
  | get_trm_in Concl    g = try Thm.concl_of g: term option;

fun get_cnames_in_trm (trm:term) = Term.add_const_names trm []: strings;

fun get_consts_in_thm thm = thm
  |> Thm.cprop_of
  |> Thm.term_of
  |> (fn trm:term => Term.add_consts trm [])
  |> map Const;

fun get_cnames_in_thm thm = thm
  |> Thm.cprop_of
  |> Thm.term_of
  |> (fn subg:term => Term.add_const_names subg []);

fun get_outmost_cname (trm:term) =
  let
    val cnames              = get_cnames_in_trm trm: strings;
    val numb                = length cnames: int;
    val last_cname          = try (nth cnames) (numb - 1): string option;
    val snd_last_cname      = try (nth cnames) (numb - 2): string option;
    val outmost_is_Trueprop = Option.map (equal "HOL.Trueprop") last_cname: bool option;
  in
    Option.map (Utils.If (snd_last_cname, last_cname)) outmost_is_Trueprop |> Option.join: string option
  end;

fun get_cnames_in_1st_subg (goal:thm) = goal
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
  |> distinct (op =)
  |> map Utils.remove__s;

fun get_typ_names_in_thm thm = thm
  |> get_trms_in_thm
  |> map get_typ_names_in_trm
  |> flat
  |> distinct (op =)
  |> map Utils.remove__s;

fun get_typ_names_in_1st_subg (goal:thm) = goal
  |> get_1st_subg
  |> Option.map get_typ_names_in_trm
  |> these
  |> map Utils.remove__s;

fun get_free_var_names_in' trm = if Term.is_Free trm
  then [Term.dest_Free trm |> fst |> Utils.remove__s] else [];

fun get_free_var_names_in_trm trm = Term.fold_aterms (fn trm => fn acc =>
  get_free_var_names_in' trm @ acc |> distinct (op =)) trm [];

fun get_free_var_names_in_trms trms = trms
  |> map get_free_var_names_in_trm
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
  |> map Utils.remove__s : strings;

val proof_state_to_thm = #goal o Proof.goal;

fun pst_to_fst_subg (pst:Proof.state) = try proof_state_to_thm pst
  >>= get_1st_subg;

fun pst_to_subgs (pst:Proof.state) = try proof_state_to_thm pst
  <$> Thm.prems_of
   |> these;

fun mk_proof_obligation ctxt (prop_str:string) =
  Syntax.read_prop ctxt prop_str
  |> Thm.cterm_of ctxt
  |> Thm.trivial;

(*Very similar to Timeout.apply but with my own release function, my_release.*)
fun timeout_apply timeout f x =
  Thread_Attributes.with_attributes Thread_Attributes.no_interrupts (fn orig_atts =>
    let
      val self = Thread.self ();
      val start = Time.now ();
      val request =
        Event_Timer.request {physical = false} (start + timeout)
          (fn () => Isabelle_Thread.interrupt_unsynchronized self);
      val result =
        Exn.capture (fn () => Thread_Attributes.with_attributes orig_atts (fn _ => f x)) ();
      val stop = Time.now ();
      val was_timeout = not (Event_Timer.cancel request);
      val test = Exn.capture Thread_Attributes.expose_interrupt ();
      fun my_release (Exn.Res rel) = rel
       |  my_release _ = error "my_release failed"
    in
      if was_timeout andalso (Exn.is_interrupt_exn result orelse Exn.is_interrupt_exn test)
      then (raise Timeout.TIMEOUT (stop - start))
      else (Exn.release test; my_release result)
    end);

local
(* SINGLE is copied from Tactical.ML, but the types are more general.*)
fun SINGLE tacf = Option.map fst o Seq.pull o tacf;

(* DETERM_TIMEOUT was originally written by Jasmin Blanchette in nitpick_util.ML.
 * This version has exception handling on top of his version with my own timeout_apply.*)
fun DETERM_TIMEOUT delay tac st =
let
  val content = Utils.try_with NONE ((timeout_apply delay) (fn () => SINGLE tac st)) ()
in
  Seq.of_list (the_list (content))
end
in

fun TIMEOUT_in real tac = DETERM_TIMEOUT (seconds real) tac;

fun TIMEOUT tac         = DETERM_TIMEOUT (seconds 1.5) tac;

fun get_meth_name (Method.Source src) = (fst (Token.name_of_src src))
  | get_meth_name _ = "\n"

end;

(*same_except_for_fst_prem checks if two thms are the same except for the first premise of the second.*)
fun same_except_for_fst_prem (goal1:thm) (goal2:thm) =
let
  (*goal1 should have one less premise.*)
  val concl1                            = Thm.concl_of goal1 : term ;
  val concl2                            = Thm.concl_of goal2 : term ;
  val eq_concl                          = Term.aconv (concl1, concl2);
  val prems1                            = Thm.prems_of goal1 : terms;
  val prems2                            = Thm.prems_of goal2 : terms ;
  val goal1_has_a_prem                  = List.null prems1 : bool ;
  fun prems1_prems2tl prems1 prems2     = prems1 ~~ List.tl prems2;
  fun prems1_equiv_prems2 prems1 prems2 = List.all (Term.aconv) (prems1_prems2tl prems1 prems2);
  fun test prems1 prems2                = eq_concl andalso prems1_equiv_prems2 prems1 prems2;
in
  if goal1_has_a_prem then test prems1 prems2 else true
end;

val defer = defer_tac 1;

fun is_in_Main (ctxt:Proof.context) (thm:thm) =
  let
    val this_thy          = Proof_Context.theory_of ctxt:theory;
    val thy_names_in_main = Context.get_theory {long=false} this_thy "Main"
      |> Theory.ancestors_of
      |> map Context.theory_name:strings;
    fun get_theory_name (thm:thm) = thm |> Thm.get_name_hint |> fst_qualifier;
    val thy_name = get_theory_name thm;
    val result = exists (equal thy_name) thy_names_in_main;
  in
    result
  end;

fun is_this_abstract_used (_  :int) (Const _      :term) = false
  | is_this_abstract_used (_  :int) (Free _       :term) = false
  | is_this_abstract_used (_  :int) (Var _        :term) = false
  | is_this_abstract_used (dBi:int) (Bound i      :term) = dBi = i
  | is_this_abstract_used (dBi:int) (Abs (_,_,trm):term) = is_this_abstract_used (dBi + 1) trm
  | is_this_abstract_used (dBi:int) (trm1 $ trm2  :term) =
      is_this_abstract_used dBi trm1 orelse
      is_this_abstract_used dBi trm2;

fun are_all_de_Bruijn_indices_used' (Abs (_,_,trm):term) =
      is_this_abstract_used 0 trm andalso
      are_all_de_Bruijn_indices_used' trm
  | are_all_de_Bruijn_indices_used' (trm1 $ trm2  :term) =
      are_all_de_Bruijn_indices_used' trm1 orelse
      are_all_de_Bruijn_indices_used' trm2
  | are_all_de_Bruijn_indices_used' (trm:term) = is_this_abstract_used 0 trm;

fun are_all_de_Bruijn_indices_used (Const _ $ Abs (name,typ,trm)) =
      are_all_de_Bruijn_indices_used' (Abs (name,typ,trm))
  | are_all_de_Bruijn_indices_used (trm as (Abs (_,_,_):term):term) =
      are_all_de_Bruijn_indices_used' trm
  | are_all_de_Bruijn_indices_used (trm1 $ trm2) =
      are_all_de_Bruijn_indices_used trm1 andalso are_all_de_Bruijn_indices_used trm2
  | are_all_de_Bruijn_indices_used _ = true;

(*add_const_names_mult is similar to Term.add_const_names, but it accepts redundancy.*)
fun add_const_names_mult (trm:term) (names:strings) =
  fold_aterms (fn Const (c, _) => insert (K false) c | _ => I) trm names;

fun pstate_to_usings (pstate:Proof.state) = Proof.raw_goal pstate |> #facts: thms;

fun pstate_to_chained_facts_as_terms (pst:Proof.state) =
  let
    val chained_thms = pstate_to_usings pst: thms;
    val chained_trms = map Thm.prop_of chained_thms: terms;
  in
    chained_trms
  end;

fun trm_to_fst_args_of_const (cname:string) (Const (fn_cname, _) $ arg) = if cname = fn_cname
    then trm_to_fst_args_of_const cname arg @ [arg]
    else trm_to_fst_args_of_const cname arg
  | trm_to_fst_args_of_const (cname:string)(trm1 $ trm2) =
    trm_to_fst_args_of_const cname trm1 @ trm_to_fst_args_of_const cname trm2
  | trm_to_fst_args_of_const (cname:string) (Abs (_, _, trm)) = trm_to_fst_args_of_const cname trm
  | trm_to_fst_args_of_const _ _ = [];

fun trm_to_snd_args_of_const (cname:string) (Const (fn_cname, _) $ arg1 $ arg2) = if cname = fn_cname
    then trm_to_snd_args_of_const cname arg1 @ [arg2]
    else trm_to_snd_args_of_const cname arg1 @ trm_to_snd_args_of_const cname arg2
  | trm_to_snd_args_of_const (cname:string)(trm1 $ trm2) =
    trm_to_snd_args_of_const cname trm1 @ trm_to_snd_args_of_const cname trm2
  | trm_to_snd_args_of_const (cname:string) (Abs (_, _, trm)) = trm_to_snd_args_of_const cname trm
  | trm_to_snd_args_of_const _ _ = [];

fun pstate_to_1st_subg_n_chained_facts (pst:Proof.state) =
  let
    val chained_thms = pstate_to_usings pst: thms;
    val chained_trms = map Thm.prop_of chained_thms: terms;
    val fst_subg_trm = pst_to_fst_subg pst |> the_list: terms;
  in
    fst_subg_trm @ chained_trms
  end;

fun pstate_to_1st_subg_n_chained_facts_record (pst:Proof.state) =
  let
    val chained_thms = pstate_to_usings pst: thms;
    val chained_trms = map Thm.prop_of chained_thms: terms;
    val fst_subg_trm = pst_to_fst_subg pst: term option;
  in
    {fst_subg = fst_subg_trm, chained_facts = chained_trms}
  end;

fun pstate_to_cnames_in_1st_subg_n_chained_facts (pstate:Proof.state) =
   pstate_to_1st_subg_n_chained_facts pstate
|> Utils.map_flat_distinct (fn trm:term => Term.add_const_names trm []) (op =);

fun trms_have_cname (cname:string) (trms:terms) =
  let
    val cnames = map (fn trm => Term.add_consts trm []) trms |> flat |> map fst: strings;
  in
    exists (equal cname) cnames
  end;

fun trm_has_prop (trm:term) =
  let
    val cnames = Term.add_const_names trm []: strings;
    val these_consts_make_prop = ["Pure.imp", "Pure.all", "Pure.conjunction", "Pure.eq"]: strings;
  in
    Utils.a_member (op =) these_consts_make_prop cnames: bool
  end;

fun trm_to_prop_trms_help (trm1 $ trm2)   = trm_to_prop_trms trm1 @ trm_to_prop_trms trm2
  | trm_to_prop_trms_help (Abs (_,_,trm)) = trm_to_prop_trms trm
  | trm_to_prop_trms_help _               = []
and trm_to_prop_trms (trm:term) =
  let
   (*
    fun dest_all' (Const ("Pure.all", _) $ Abs abs) = SOME (Abs abs)
      | dest_all'  _                                = NONE;
    *)
    (*Warning: Logic.dest_all calls Term.dest_abs internally.
      But this helps us identify the names of variables represented by de-Bruijn indices.*)
    val all         = try Logic.dest_all_global trm  >>= try snd |> the_list            : terms;
    val equals      = try Logic.dest_equals trm      >>= try Utils.pair_to_list |> these: terms;
    val implies     = try Logic.dest_implies trm     >>= try Utils.pair_to_list |> these: terms;
    val conjcts     = try Logic.dest_conjunction trm >>= try Utils.pair_to_list |> these: terms;
    val props       = all @ equals @ implies @ conjcts                                  : terms;
    val deeper_lvl  = trm_to_prop_trms_help trm                                         : terms;
    val this_lvl    = map trm_to_prop_trms props |> flat                                : terms;
    (*filter_out trm_has_prop removes some valuable terms in @{term "(\<And>x. y (z \<Longrightarrow> w) )"}*)
    val all_results = (*filter_out trm_has_prop*) props @ this_lvl @ deeper_lvl         : terms;
  in
    distinct Term.aconv all_results
  end;

fun trm_to_certain_var_free_const (assert_trm:term -> bool) (trm:term) =
  let
    val vars       = Term.add_vars trm []  : (indexname * typ) list;
    val frees      = Term.add_frees trm [] : (string * typ) list;
    val consts     = Term.add_consts trm []: (string * typ) list;
    val result =
      {vars   = map Term.Var vars     |> filter assert_trm,
       frees  = map Term.Free frees   |> filter assert_trm,
       consts = map Term.Const consts |> filter assert_trm};
  in
    result:{consts: term list, frees: term list, vars: term list}
  end;

fun is_typ_of_name (typ_name:string) (typ:typ) = try dest_Type typ <$> fst <$> equal typ_name |> Utils.is_some_true;

fun is_nat_typ (typ:typ) = is_typ_of_name "Nat.nat" typ;

fun trm_has_nat_typ (trm:term) = Term.exists_type is_nat_typ trm: bool;

fun trm_to_nats (trm:term) = trm_to_certain_var_free_const trm_has_nat_typ trm;

fun is_fun_typ (typ:typ) = is_typ_of_name "fun" typ;

fun trm_has_fun_typ (trm:term) = Term.exists_type is_fun_typ trm: bool;

fun trm_to_funs (trm:term) = trm_to_certain_var_free_const trm_has_fun_typ trm;

fun is_record_trm (Const ("Set.insert", _) $ (Const ("HOL.eq", _) $ _ $ _) $ (inner as (Const ("Set.insert", _) $ (Const ("HOL.eq", _) $ _ $ _) $ _ ))) =
    is_record_trm inner
  | is_record_trm (Const ("Set.insert", _) $ (Const ("HOL.eq", _) $ _ $ _) $ Const ("Orderings.bot_class.bot", _))                                      = true
  | is_record_trm  _                                                                                                                                    = false;

fun is_set_typ (typ:typ) = is_typ_of_name "Set.set" typ;

fun trm_has_set_typ (trm:term) = Term.exists_type is_set_typ trm: bool;

fun is_int_typ (typ:typ) = is_typ_of_name "Int.int" typ;

fun trm_has_int_typ (trm:term) = Term.exists_type is_int_typ trm: bool;

fun trm_to_sets (trm:term) = trm_to_certain_var_free_const trm_has_set_typ trm;

fun is_list_typ (typ:typ) = is_typ_of_name "List.list" typ;

fun trm_has_list_typ (trm:term) = Term.exists_type is_list_typ trm: bool;

fun trm_to_lists (trm:term) = trm_to_certain_var_free_const trm_has_list_typ trm;

fun trm_to_sets_and_lists (trm:term) =
  let
    val lists = trm_to_certain_var_free_const trm_has_list_typ trm;
    val sets  = trm_to_certain_var_free_const trm_has_set_typ  trm;
    val consts = #consts lists @ #consts sets |> distinct Term.aconv;
    val frees  = #frees  lists @ #frees  sets |> distinct Term.aconv;
    val vars   = #vars   lists @ #vars   sets |> distinct Term.aconv;
  in
    {consts = consts, frees = frees, vars = vars}
  end;

fun trm_to_string (ctxt:Proof.context) (trm:term) = Syntax.string_of_term ctxt trm
 |> YXML.parse_body
 |> XML.content_of : string;

val count_numb_of_args_of_fun_typ = length o Term.binder_types;

(* TODO: remove code-duplication with PaMpeR/Assertion.ML *)
fun is_recursive_eq_about_cosnt_name (_ $ (Term.Const ("HOL.eq",_) $ A $ B)) (cname:string) =
  let
     val cname_is_in_lhs = Term.exists_Const (fn (s,_) => cname = s) A;
     val cname_is_in_rhs = Term.exists_Const (fn (s,_) => cname = s) B;
  in cname_is_in_lhs andalso cname_is_in_rhs end
 |  is_recursive_eq_about_cosnt_name _ _ = false;

fun check_thm_list (thms:thm list) (cname:string) =
  List.exists ((fn trm => is_recursive_eq_about_cosnt_name trm cname) o Thm.concl_of) thms;

fun has_recursive_simp_about_const_names (_   :Proof.context)  []             = false
 |  has_recursive_simp_about_const_names (ctxt:Proof.context) (cname::cnames) =
     (check_thm_list (Proof_Context.get_thms ctxt (cname^".simps")) cname handle ERROR _ =>
      has_recursive_simp_about_const_names ctxt cnames);

fun has_recursive_simp_about_const_name (ctxt:Proof.context) (cname:string) = has_recursive_simp_about_const_names ctxt [cname]

fun has_recursive_psimp_about_const_name (ctxt:Proof.context) (cname:string) =
  let
    val psimps_name         = cname ^ ".psimps"                                     : string;
    val psimps              = try (Proof_Context.get_thms ctxt) psimps_name |> these: thms;
    val psimps_props        = map Thm.prop_of psimps                                : terms;
    val cncls_as_props      = map Logic.strip_imp_concl psimps_props                : terms;
    val has_recursive_psimp = List.exists ((fn trm => is_recursive_eq_about_cosnt_name trm cname)) cncls_as_props;
  in has_recursive_psimp end;

fun normalize_trm_as_string (ctxt:Proof.context) (trm_as_string:string) =
    Syntax.read_term ctxt trm_as_string |> trm_to_string ctxt: string;

(*This contract_abbrevs is a modified version of contract_abbrevs in Pure/Isar/proof_context.ML.*)
fun contract_abbrevs (ctxt:Proof.context) (t:term) =
  let
    val thy            = Proof_Context.theory_of ctxt;
    val consts         = Proof_Context.consts_of ctxt;
    val retrieve       = Consts.retrieve_abbrevs consts (print_mode_value () @ [""]);
    fun match_abbrev u = Option.map #1 (get_first (Pattern.match_rew thy u) (retrieve u));
  in
    Pattern.rewrite_term_top thy [] [match_abbrev] t
  end;

val strip_atyp = Term.map_types (map_atyps (K dummyT)): term -> term;

fun takes_n_arguments (f:term) (n:int) = length (fst (strip_type (type_of f))) = n;

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
  type get_rules           = context -> thm -> (ref * thm) list;
  type get_rule_names      = context -> thm -> strings;
  type pstate_to_thms      = Proof.state -> thms;
  type pstate_to_thm_names = Proof.state -> strings;
  val get_criterion                      : string -> strings -> (bool * 'a criterion) list;
  val all_names_to_rules                 : string -> strings -> get_rules;
  val some_names_to_rules                : string -> strings -> get_rules;
  val get_rule_names                     : get_rules -> context -> thm -> xstring list;
  val get_simp_rules                     : get_rules;
  val get_thms_of_name_with_these_substrs: context -> string list -> thm list;
  val get_thms_of_name_with_suffix       : context -> string -> string -> thm list;
  val get_thms_of_names_with_suffix      : context -> string list -> string -> thm list;
  val get_induct_rules                   : get_rules;      (*used in PSL. TODO: to be replaced with pstate_to_induct_thms*)
  val pstate_to_induct_thms              : pstate_to_thms; (*used in MeLoId*)
  val get_coinduction_rules              : get_rules;
  (*These get_(elim, intro, dest)_rules may not be powerful enough.*)
  val get_elim_rules                     : get_rules;
  val get_intro_rules                    : get_rules;
  val get_dest_rules                     : get_rules;
  val get_split_rules                    : get_rules;
  val get_simp_rule_names                : get_rule_names;
  val get_induct_rule_names              : get_rule_names;      (*used in PSL. TODO: to be replaced with pstate_to_induct_thm_names*)
  val pstate_to_induct_thm_names         : pstate_to_thm_names; (*used in MeLoId*)
  val get_coinduction_rule_names         : get_rule_names;
  val get_elim_rule_names                : get_rule_names;
  val get_intro_rule_names               : get_rule_names;
  val get_dest_rule_names                : get_rule_names;
  val get_split_rule_names               : get_rule_names;
end;

(*** Find_Theorems2: provides an interface of find_theorem for PSL. ***)
structure Find_Theorems2 : FIND_THEOREMS2 =
struct

infix 1 liftM;
fun (m liftM f) = Option.map f m;

open Find_Theorems;

type context = Proof.context;
type ref = Facts.ref;
type get_rules = context -> thm -> (ref * thm) list;
type get_rule_names = context -> thm -> strings;
type pstate_to_thms      = Proof.state -> thms;
type pstate_to_thm_names = Proof.state -> strings;

fun get_criterion kind_name ([]:strings) = [(true, Name kind_name)]
  | get_criterion kind_name (name::names:strings) = (true, Name name)::get_criterion kind_name names;

fun all_names_to_rules kind_name (names:strings) ctxt (_(*just for type checking*):thm) =
  try (find_theorems ctxt NONE NONE true) (get_criterion kind_name names) liftM snd |> Utils.is_some_null;

fun some_names_to_rules kind_name names ctxt goal = names
  |> map (fn name:string => all_names_to_rules kind_name [name] ctxt goal)
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
    val cnames   = Isabelle_Utils.get_cnames_in_1st_subg goal;
    val related_rules = some_names_to_rules "" cnames ctxt goal;
    val simpset_thms  = ctxt |> simpset_of |> Raw_Simplifier.dest_ss |> #simps |> map snd;
    fun eq_test (thm1, (_, thm2)) = Thm.eq_thm (thm1, thm2);
    val unique_rules  = subtract eq_test simpset_thms related_rules;
  in
    unique_rules : (Facts.ref * thm) list
  end;

fun get_simp_rule_names ctxt goal = get_rule_names get_simp_rules ctxt goal : strings;

fun get_induct_rules (ctxt:context) (goal:thm) =
  let
    val cnames  = Isabelle_Utils.get_cnames_in_1st_subg goal         : strings;
    val induct_rules = some_names_to_rules ".induct" cnames ctxt goal;
  in
    induct_rules : (Facts.ref * thm) list
  end;

fun get_induct_rule_names ctxt goal = get_rule_names get_induct_rules ctxt goal : strings;

(* get_thms_of_const_name_with_suffix returns the thms that are named after a given constant with a given suffix from the current context. *)
fun get_thms_of_name_with_suffix (ctxt:context) (sfx:string) (name:string) =
  try (Proof_Context.get_thms ctxt) (name ^ "." ^ sfx) |> these: thms;

(* get_thms_of_cnames_with_suffix is similar to get_thms_of_const_name_with_suffix, but with multiple constant names. *)
fun get_thms_of_names_with_suffix (ctxt:context) (names:strings) (sfx:string) =
  map (get_thms_of_name_with_suffix ctxt sfx) names |> flat: thms;

fun get_thms_of_name_with_these_substrs (ctxt:context) (substrs:strings) =
  let
    val criterion      = get_criterion "" substrs: (bool * term criterion) list;
    val relevant_rules = try (Find_Theorems.find_theorems ctxt NONE NONE true) criterion
                         liftM snd
                         liftM map snd
                         |> Utils.is_some_null
  in
    relevant_rules: thms
  end;

fun pstate_to_induct_thms (pstate:Proof.state) =
  let
    val ctxt        = Proof.context_of pstate                                           : Proof.context;
    val cnames      = Isabelle_Utils.pstate_to_cnames_in_1st_subg_n_chained_facts pstate: strings;
    val induct_thms = get_thms_of_names_with_suffix ctxt cnames "induct"                : thms;
  in
    induct_thms
  end;

fun pstate_to_induct_thm_names (pstate:Proof.state) =
  let
    val ctxt   = Proof.context_of pstate;
    val cnames = Isabelle_Utils.pstate_to_cnames_in_1st_subg_n_chained_facts pstate: strings;
    fun ctxt_has_thm_of_name (thm_name:string) = (*TODO: This function should be defined outside pstate_to_induct_thm_names? *)
        case try (Proof_Context.get_thms ctxt) thm_name of
         NONE      => false
       | SOME thms => null thms |> not;
    val induct_thm_names      = map (fn cname => cname ^ ".induct") cnames: strings;
    val some_induct_thm_names = filter ctxt_has_thm_of_name induct_thm_names;
  in
    some_induct_thm_names
  end;

fun get_coinduction_rules (ctxt:context) (goal:thm) =
  let
    val cnames                  = Isabelle_Utils.get_cnames_in_1st_subg goal : strings;
    fun get_coinduct_rules post = some_names_to_rules post cnames ctxt goal;
    val coinduct_rules1 = get_coinduct_rules ".coinduct";
    val coinduct_rules2 = get_coinduct_rules ".coinduct_strong";
  in
    coinduct_rules1 @ coinduct_rules2: (Facts.ref * thm) list
  end;

fun get_coinduction_rule_names ctxt goal = get_rule_names get_coinduction_rules ctxt goal : strings;

fun get_elim_rules  ctxt goal = find_theorems ctxt (SOME goal) NONE true [(true, Elim)] |> snd;
fun get_intro_rules ctxt goal = find_theorems ctxt (SOME goal) (SOME 100) true [(true, Intro)] |> snd;
fun get_dest_rules  ctxt goal = find_theorems ctxt (SOME goal) (SOME 100) true [(true, Dest)] |> snd;
        
fun get_elim_rule_names  ctxt goal = get_rule_names get_elim_rules  ctxt goal : strings;
fun get_intro_rule_names ctxt goal = get_rule_names get_intro_rules ctxt goal : strings;
fun get_dest_rule_names  ctxt goal = get_rule_names get_dest_rules  ctxt goal : strings;

fun get_split_rules ctxt goal =
  let
    (*For split, we need to use typ_names instead of cnames.*)
    val used_typ_names = Isabelle_Utils.get_typ_names_in_1st_subg goal;
    val related_rules  = some_names_to_rules "split" used_typ_names ctxt goal
  in
    related_rules : (Facts.ref * thm) list
  end;

fun get_split_rule_names ctxt goal = get_rule_names get_split_rules ctxt goal;

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
                   | Apply of {using:strings, methN:string, back:int};
  type log;
  type 'a logtac   = 'a -> (log * 'a) seq;
  type 'a st_monad = log -> (log * 'a) seq;
  type 'a stttac   = 'a -> 'a st_monad;

  val check_src           : context -> src -> src;
  val checked_src_to_meth : context -> src -> Method.method;
  val str_to_tokens       : context -> string -> Token.T list;
  val get_tokens          : string -> Token.T list -> src;
  val get_meth_nm         : string -> strings -> string;
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
                 | Apply of {using:strings, methN:string, back:int};
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

fun get_meth_nm (meth:string) (attributes:strings) =
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
    val results     = Seq2.try_seq (Isabelle_Utils.TIMEOUT_in 30.0 (Proof.apply text_range)) proof_state(*TODO: timeout too long?*)
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
 |> Seq2.try_seq (Seq.map add_back);

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
    val nontac_with_TO = Isabelle_Utils.TIMEOUT_in 1.0  nontac              : state nontac;
    val trace_node     = Apply {using = [], methN = meth_name, back = 0}    : node;
    val logtac         = nontac_to_logtac trace_node nontac_with_TO         : state logtac;
    val stttac         = logtac_to_stttac logtac                            : state stttac;
  in
    stttac : state stttac
  end;

local
  fun mk_using  ([]   : strings) = ""
   |  mk_using  (using: strings) = "using " ^ String.concatWith " " using ^ " ";
  fun mk_apply methN  = "apply " ^ methN ^ "";
  fun mk_backs (n:int) = replicate n "back" |> String.concatWith " " handle Subscript =>
    (tracing "mk_backs in Isabelle_Utils.thy failed. It should take 0 or a positive integer.";"");
  fun mk_apply_script1 {methN : string, using : strings, back : int} =
    mk_using using ^ mk_apply methN ^ mk_backs back ^ "\n";
  fun mk_proof_script1 (Done    : node) = "done \n"
   |  mk_proof_script1 (Subgoal : node) = "subgoal \n"
   |  mk_proof_script1 (Defer   : node) = "defer \n"
   |  mk_proof_script1 (Apply n : node) = mk_apply_script1 n;
in
  fun mk_apply_script (log:log) =
    map mk_proof_script1 log
    |> String.concat
    |> Active.sendback_markup_properties [Markup.padding_command] : string;
end;

end;

(*** signature SELFIE_UTIL ***)
signature SELFIE_UTIL =
sig

val max_int: int;

val same_strings_when_normalized: Proof.context -> string -> string -> bool;

val ctxt_n_string_to_cname: Proof.context -> string -> string option;

(*arguments passed to the induct method*)
datatype rule_or_set          = Ind_Rule of string | Ind_Set of string | Hand_Rule of string;
type     rule_or_sets         = rule_or_set list;
val rule_or_set_to_string     : rule_or_set -> string;
datatype induct_arguments     = Induct_Arguments of {ons: strings, arbs: strings, rules: rule_or_sets};
val dest_induct_arguments     : induct_arguments -> {ons: strings, arbs: strings, rules: rule_or_sets};
val induct_arguments_to_string: induct_arguments -> string;
val ord_induct_arguments      : induct_arguments * induct_arguments -> order;
val sort_induct_argumentss    : induct_arguments list -> induct_arguments list;

datatype qtyp = QOuter_Path | QInner_Path | QOuter_Print | QInner_Print | QOuter_Number | QInner_Number | QInd | QArb | QRule;

val print_qtyp: qtyp -> string;

datatype atomic_assert =
(*Eval_Node*)
  Node_Is_Cnst
| Node_Is_Free
| Node_Is_Var
| Node_Is_Bound
| Node_Is_Lambda
| Node_Is_App
| Is_Rule_Of_Node
| Is_Set_Of_Node
| Node_Is_Defined_With
| Node_Takes_N_Arguments
| Node_Takes_Less_Than_N_Arguments
| Node_Is_Defined_With_N_Clauses
(*Eval_Unode*)
| Has_Same_Prnt_As
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Nth_Child
| Is_N_Plus_One_th_Child
| Is_Root_In_A_Location
| Is_A_Meta_Premise
| Is_A_Meta_Conclusion
| Is_A_Meta_Premise_Or_Below
| Is_A_Meta_Conclusion_Or_Below
| Unode_Has_As_Subprint
(*Eval_Print*)
| Are_Same_Prints
| Is_Subprint_Of
| Is_Nth_Induct
| Is_Nth_Arbitrary
| Is_Induct
| Is_Arbitrary
| Is_Rule
| Is_Rule_Of_Print
| Is_Set
| Is_Set_Of_Print
(*Eval_Print for node*)
| Print_Is_Cnst
| Print_Is_Free
| Print_Is_Var
| Print_Is_Bound
| Print_Is_Lambda
| Print_Is_App
| Print_Is_Defined_With
| Print_Is_Defined_With_N_Clauses
| Print_Takes_N_Arguments
| Print_Takes_Less_Than_N_Arguments
(*Eval_Path*)
| Unode_Has_Print
| Is_In_Subgoal
| Is_In_Chained_Fact
| Is_In_Nth_Subgoal
| Is_In_Nth_Chained_Fact
| Are_In_Same_Location
| Is_Parent_Of
| Is_Path_Above
| Is_Same_Path_As
| Is_An_Argument_Of
| Is_An_Argument_Or_Below_Argument_Of
| Is_Nth_Child_Or_Below_Nth_Child_Of
| Is_Below_N_Plus_One_th_Child_Of
| Is_Nth_Argument_Of
| Is_Nth_Argument_Or_Below_Nth_Argument_Of
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Less_Than_By_One
(*debug*)
| Debug_Non_Path_Literal
| Debug_Print_Unode
| Dummy;

val print_atomic_assert: atomic_assert -> string;

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

val print_assert: assert -> string;

val rule_to_const_name: Proof.context -> string -> string;

val ctxt_n_cname_to_definitions: Proof.context -> string -> terms;

val pst_n_cname_to_definitions: Proof.state -> string -> terms;

val ctxt_n_cname_to_number_of_defining_clauses: Proof.context -> string -> int;

end;

(*** structure SeLFiE_Util ***)
structure SeLFiE_Util: SELFIE_UTIL =
struct

val max_int = 10: int;

fun same_strings_when_normalized (ctxt:Proof.context) st1 st2 =
  let
    val normalize          = Isabelle_Utils.normalize_trm_as_string ctxt;
    val (norm_p1, norm_p2) = apply2 (try normalize) (st1, st2);
  in
    Utils.opt_equal (norm_p1, norm_p2)
  end;

infix isSubstring;

fun ctxt_n_string_to_cname  (ctxt:Proof.context) (str:string) =
  let
    val trm_option = try (Syntax.read_term ctxt) str           : term   option;
    val trm_cname  = trm_option >>= try Term.dest_Const <$> fst: string option;
  in
    trm_cname
  end;

(*arguments passed to the induct method*)
datatype rule_or_set  = Ind_Rule of string | Ind_Set of string | Hand_Rule of string;
type     rule_or_sets = rule_or_set list;
fun rule_or_set_to_string (Ind_Rule  rule_name) = rule_name
  | rule_or_set_to_string (Ind_Set   set_name ) = set_name
  | rule_or_set_to_string (Hand_Rule rule_name) = rule_name;
datatype induct_arguments = Induct_Arguments of {ons: strings, arbs: strings, rules: rule_or_sets};
fun dest_induct_arguments (Induct_Arguments arguments) = arguments;

fun induct_arguments_to_string (Induct_Arguments {ons, arbs, rules}) =
  let
    val ons'  = map (enclose "\"" "\"") ons;
    val on    = String.concatWith " " ons': string;
    val arb   = if null arbs  then "" else " arbitrary:" ^ String.concatWith " " arbs : string;
    val rule  = case rules of
         [                   ] => ""
       | [Ind_Rule  rule_name] => " rule:" ^ rule_name
       | [Ind_Set   set_name ] => " set:"  ^ set_name
       | [Hand_Rule rule_name] => " rule:" ^ rule_name
       |  _                    => error "induct_arguments_to_string failed.";
    val apply = "(induct " ^ on ^ arb ^ rule ^ ")"
  in
    apply
  end;

fun numb_of_args (Induct_Arguments {ons, arbs, rules}) = length ons + length arbs + length rules: int;

fun ord_induct_arguments (args1, args2) = (Int.compare (numb_of_args args1, numb_of_args args2)): order;

fun sort_induct_argumentss (induct_argumentss:induct_arguments list) = sort ord_induct_arguments induct_argumentss
  : induct_arguments list;

datatype qtyp = QOuter_Path | QInner_Path | QOuter_Print | QInner_Print | QOuter_Number | QInner_Number | QInd | QArb | QRule;

fun print_qtyp QOuter_Path = "QOuter_Path"
  | print_qtyp QInner_Path = "QInner_Path"
  | print_qtyp QOuter_Print = "QOuter_Print"
  | print_qtyp QInner_Print = "QInner_Print"
  | print_qtyp QOuter_Number = "QOuter_Number"
  | print_qtyp QInner_Number = "QInner_Number"
  | print_qtyp QInd = "QInd"
  | print_qtyp QArb = "QArb"
  | print_qtyp QRule = "QRule";


datatype atomic_assert =
(*Eval_Node*)
  Node_Is_Cnst
| Node_Is_Free
| Node_Is_Var
| Node_Is_Bound
| Node_Is_Lambda
| Node_Is_App
| Is_Rule_Of_Node
| Is_Set_Of_Node
| Node_Is_Defined_With
| Node_Takes_N_Arguments
| Node_Takes_Less_Than_N_Arguments
| Node_Is_Defined_With_N_Clauses
(*Eval_Unode*)
| Has_Same_Prnt_As
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Nth_Child
| Is_N_Plus_One_th_Child
| Is_Root_In_A_Location
| Is_A_Meta_Premise
| Is_A_Meta_Conclusion
| Is_A_Meta_Premise_Or_Below
| Is_A_Meta_Conclusion_Or_Below
| Unode_Has_As_Subprint
(*Eval_Print*)
| Are_Same_Prints
| Is_Subprint_Of
| Is_Nth_Induct
| Is_Nth_Arbitrary
| Is_Induct
| Is_Arbitrary
| Is_Rule
| Is_Rule_Of_Print
| Is_Set
| Is_Set_Of_Print
(*Eval_Print for node*)
| Print_Is_Cnst
| Print_Is_Free
| Print_Is_Var
| Print_Is_Bound
| Print_Is_Lambda
| Print_Is_App
| Print_Is_Defined_With
| Print_Is_Defined_With_N_Clauses
| Print_Takes_N_Arguments
| Print_Takes_Less_Than_N_Arguments
(*Eval_Path*)
| Unode_Has_Print
| Is_In_Subgoal
| Is_In_Chained_Fact
| Is_In_Nth_Subgoal
| Is_In_Nth_Chained_Fact
| Are_In_Same_Location
| Is_Parent_Of
| Is_Path_Above
| Is_Same_Path_As
| Is_An_Argument_Of
| Is_An_Argument_Or_Below_Argument_Of
| Is_Nth_Child_Or_Below_Nth_Child_Of
| Is_Below_N_Plus_One_th_Child_Of
| Is_Nth_Argument_Of
| Is_Nth_Argument_Or_Below_Nth_Argument_Of
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Less_Than_By_One
(*debug*)
| Debug_Non_Path_Literal
| Debug_Print_Unode
| Dummy;

fun(*Eval_Node*)
    print_atomic_assert (Node_Is_Cnst                              ) = "Node_Is_Cnst"
  | print_atomic_assert (Node_Is_Free                              ) = "Node_Is_Free"
  | print_atomic_assert (Node_Is_Var                               ) = "Node_Is_Var"
  | print_atomic_assert (Node_Is_Bound                             ) = "Node_Is_Bound"
  | print_atomic_assert (Node_Is_Lambda                            ) = "Node_Is_Lambda"
  | print_atomic_assert (Node_Is_App                               ) = "Node_Is_App"
  | print_atomic_assert (Node_Takes_Less_Than_N_Arguments          ) = "Node_Takes_Less_Than_N_Arguments"
  | print_atomic_assert (Node_Is_Defined_With                      ) = "Node_Is_Defined_With"
  | print_atomic_assert (Node_Is_Defined_With_N_Clauses            ) = "Node_Is_Defined_With_N_Clauses"
  | print_atomic_assert (Is_Rule_Of_Node                           ) = "Is_Rule_Of_Node"
  | print_atomic_assert (Is_Set_Of_Node                            ) = "Is_Set_Of_Node"
  | print_atomic_assert (Node_Takes_N_Arguments                    ) = "Takes_N_Arguments"
  | print_atomic_assert (Has_Same_Prnt_As                          ) = "Has_Same_Prnt_As"
  | print_atomic_assert (Is_Deeper_Than                            ) = "Is_Deeper_Than"
  | print_atomic_assert (Is_Shallower_Than                         ) = "Is_Shallower_Than"
  | print_atomic_assert (Is_Nth_Child                              ) = "Is_Nth_Child"
  | print_atomic_assert (Is_N_Plus_One_th_Child                    ) = "Is_N_Plus_One_th_Child"
  | print_atomic_assert (Is_Root_In_A_Location                     ) = "Is_Root_In_A_Location"
  | print_atomic_assert (Are_Same_Prints                           ) = "Are_Same_Prints"
  | print_atomic_assert (Is_Subprint_Of                            ) = "Is_Subprint_Of"
  | print_atomic_assert (Unode_Has_Print                           ) = "Unode_Has_Print"
  | print_atomic_assert (Is_In_Subgoal                             ) = "Is_In_Subgoal"
  | print_atomic_assert (Is_In_Chained_Fact                        ) = "Is_In_Chained_Fact"
  | print_atomic_assert (Is_In_Nth_Subgoal                         ) = "Is_In_Nth_Subgoal"
  | print_atomic_assert (Is_In_Nth_Chained_Fact                    ) = "Is_In_Nth_Chained_Fact"
  | print_atomic_assert (Are_In_Same_Location                      ) = "Are_In_Same_Location"
  | print_atomic_assert (Is_Parent_Of                              ) = "Is_Parent_Of"
  | print_atomic_assert (Is_Path_Above                             ) = "Is_Path_Above"
  | print_atomic_assert (Is_Same_Path_As                           ) = "Is_Same_Path_As"
  | print_atomic_assert (Is_An_Argument_Of                         ) = "Is_An_Argument_Of"
  | print_atomic_assert (Is_An_Argument_Or_Below_Argument_Of       ) = "Is_An_Argument_Or_Below_Argument_Of"
  | print_atomic_assert (Is_Nth_Child_Or_Below_Nth_Child_Of        ) = "Is_Nth_Child_Or_Below_Nth_Child_Of"
  | print_atomic_assert (Is_Below_N_Plus_One_th_Child_Of           ) = "Is_Below_N_Plus_One_th_Child_Of"
  | print_atomic_assert (Is_Nth_Argument_Of                        ) = "Is_Nth_Argument_Of"
  | print_atomic_assert (Is_Nth_Argument_Or_Below_Nth_Argument_Of  ) = "Is_Nth_Arg_Or_Below_Nth_Arg_Of"
  | print_atomic_assert (Is_A_Meta_Premise                         ) = "Is_A_Meta_Premise"
  | print_atomic_assert (Is_A_Meta_Conclusion                      ) = "Is_A_Meta_Conclusion"
  | print_atomic_assert (Is_A_Meta_Premise_Or_Below                ) = "Is_A_Meta_Premise"
  | print_atomic_assert (Is_A_Meta_Conclusion_Or_Below             ) = "Is_A_Meta_Conclusion"
  | print_atomic_assert (Unode_Has_As_Subprint                     ) = "Unode_Has_As_Subprint"
  | print_atomic_assert (Are_Same_Number                           ) = "Are_Same_Number"
  | print_atomic_assert (Is_Less_Than                              ) = "Is_Less_Than"
  | print_atomic_assert (Is_Less_Than_By_One                       ) = "Is_Less_Than_By_One"
  | print_atomic_assert (Is_Nth_Induct                             ) = "Is_Nth_Induct"
  | print_atomic_assert (Is_Nth_Arbitrary                          ) = "Is_Nth_Arbitrary"
  | print_atomic_assert (Is_Induct                                 ) = "Is_Induct"
  | print_atomic_assert (Is_Arbitrary                              ) = "Is_Arbitrary"
  | print_atomic_assert (Is_Rule                                   ) = "Is_Rule"
  | print_atomic_assert (Is_Rule_Of_Print                          ) = "Is_Rule_Of_Print"
  | print_atomic_assert (Is_Set                                    ) = "Is_Set"
  | print_atomic_assert (Is_Set_Of_Print                           ) = "Is_Set_Of_Print"
  (*Eval_Print for node*)
  | print_atomic_assert (Print_Is_Cnst                             ) = "Print_Is_Cnst"
  | print_atomic_assert (Print_Is_Free                             ) = "Print_Is_Free"
  | print_atomic_assert (Print_Is_Var                              ) = "Print_Is_Var"
  | print_atomic_assert (Print_Is_Bound                            ) = "Print_Is_Bound"
  | print_atomic_assert (Print_Is_Lambda                           ) = "Print_Is_Lambda"
  | print_atomic_assert (Print_Is_App                              ) = "Print_Is_App"
  | print_atomic_assert (Print_Is_Defined_With                     ) = "Print_Is_Defined_With"
  | print_atomic_assert (Print_Is_Defined_With_N_Clauses           ) = "Print_Is_Defined_With_N_Clauses"
  | print_atomic_assert (Print_Takes_N_Arguments                   ) = "Print_Takes_N_Arguments"
  | print_atomic_assert (Print_Takes_Less_Than_N_Arguments         ) = "Print_Takes_Less_Than_N_Arguments"
  | print_atomic_assert (Debug_Non_Path_Literal                    ) = "Debug_Non_Path_Literal"
  | print_atomic_assert (Debug_Print_Unode                         ) = "Debug_Print_Unode"
  | print_atomic_assert (Dummy                                     ) = "Dummy";

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

fun print_assert Not   = "Not"
  | print_assert And   = "And"
  | print_assert Or    = "Or"
  | print_assert Nor   = "Nor"
  | print_assert Imply = "Imply"
  | print_assert Ands  = "Ands"
  | print_assert Ors   = "Ors"
  | print_assert (Atomic ass) = "Atomic " ^   print_atomic_assert ass ^ " "

datatype non_path_literal =
  Bool    of bool
| Print   of string
| Number  of int
| Command of Definition_Pattern.command;

datatype 'path literal = Path of 'path | Non_Path of non_path_literal;

type 'path literals = 'path literal list;

fun split_using_period x = String.tokens (fn splitter => splitter = #".") x;

fun rule_to_const_name (ctxt:Proof.context) (rule_name:string) =
  try split_using_period rule_name
<$> Utils.init
<$> String.concatWith "."
>>= try (Syntax.read_term ctxt)
>>= try Term.dest_Const
<$> fst
 |> (fn opt => Option.getOpt (opt, "fake_name"));

local

fun ctxt_n_cname_to_definition_for_def (ctxt:Proof.context) (cname:string) (suffix:string) =
  try (Proof_Context.get_thms ctxt) (cname ^ suffix) |> these |> map Thm.prop_of;

fun get_definitions_using_suffix (ctxt:Proof.context) (cname:string) (suffix:string) =
   try (Proof_Context.get_thms ctxt) (cname ^ "." ^ suffix)
|> these
|> map Thm.prop_of;

fun ctxt_n_cname_to_definitions_for_inductive (ctxt:Proof.context) (cname:string) =
   get_definitions_using_suffix ctxt cname "intros": terms;

fun ctxt_n_cname_to_definitions_for_primrec (ctxt:Proof.context) (cname:string) =
   get_definitions_using_suffix ctxt cname "simps": terms;

val ctxt_n_cname_to_definitions_for_fun = ctxt_n_cname_to_definitions_for_primrec;

fun ctxt_n_cname_to_definitions_for_function (ctxt:Proof.context) (cname:string) =
   get_definitions_using_suffix ctxt cname "psimps"
|> map Logic.strip_imp_concl: terms;

in

fun ctxt_n_cname_to_definitions (ctxt:Proof.context) (cname:string) :terms =
  let
    val command = Definition_Pattern.get_command ctxt cname;
    fun command_to_definitions Definition_Pattern.Definition = ctxt_n_cname_to_definition_for_def        ctxt cname "_def"
      | command_to_definitions Definition_Pattern.Fun        = ctxt_n_cname_to_definitions_for_fun       ctxt cname
      | command_to_definitions Definition_Pattern.Primrec    = ctxt_n_cname_to_definitions_for_primrec   ctxt cname
      | command_to_definitions Definition_Pattern.Function   = ctxt_n_cname_to_definitions_for_function  ctxt cname
      | command_to_definitions Definition_Pattern.Inductive  = ctxt_n_cname_to_definitions_for_inductive ctxt cname
      (*TODO: Inductive_Set*)
      | command_to_definitions Definition_Pattern.Inductive_Set  = ctxt_n_cname_to_definitions_for_inductive ctxt cname
      | command_to_definitions Definition_Pattern.Unknown    = [];
  in
    command_to_definitions command: terms
  end;

fun pst_n_cname_to_definitions (pst:Proof.state) (cname:string) =
  let
    val ctxt        = Proof.context_of pst                  : Proof.context;
    val definitions = ctxt_n_cname_to_definitions ctxt cname: terms;
  in
    definitions:terms
  end;

fun ctxt_n_cname_to_number_of_defining_clauses (ctxt:Proof.context) (cname:string): int =
  let
    val terms = ctxt_n_cname_to_definitions ctxt cname: terms;
  in
    length terms: int
  end;

end;

end;