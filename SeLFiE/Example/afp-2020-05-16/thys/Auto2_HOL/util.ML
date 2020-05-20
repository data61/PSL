(*
  File: util.ML
  Author: Bohua Zhan

  Utility functions.
*)

signature BASIC_UTIL =
sig
  (* Exceptions *)
  val assert: bool -> string -> unit

  (* Types *)
  val propT: typ

  (* Lists *)
  val the_pair: 'a list -> 'a * 'a
  val the_triple: 'a list -> 'a * 'a * 'a
  val filter_split: ('a -> bool) -> 'a list -> 'a list * 'a list

  (* Managing matching environments. *)
  val fo_init: Type.tyenv * Envir.tenv
  val lookup_instn: Type.tyenv * Envir.tenv -> string * int -> term
  val lookup_inst: Type.tyenv * Envir.tenv -> string -> term

  (* Tracing functions. *)
  val trace_t: Proof.context -> string -> term -> unit
  val trace_tlist: Proof.context -> string -> term list -> unit
  val trace_thm: Proof.context -> string -> thm -> unit
  val trace_fullthm: Proof.context -> string -> thm -> unit
  val trace_thm_global: string -> thm -> unit
  val trace_fullthm_global: string -> thm -> unit

  (* Terms *)
  val dest_arg: term -> term
  val dest_arg1: term -> term

  (* Theorems *)
  val apply_to_thm: conv -> thm -> thm
  val meta_sym: thm -> thm
  val apply_to_lhs: conv -> thm -> thm
  val apply_to_rhs: conv -> thm -> thm
end;

signature UTIL =
sig
  include BASIC_UTIL

  (* Lists *)
  val max: ('a * 'a -> order) -> 'a list -> 'a
  val max_partial: ('a -> 'a -> bool) -> 'a list -> 'a list
  val subsets: 'a list -> 'a list list
  val all_permutes: 'a list -> 'a list list
  val all_pairs: 'a list * 'b list -> ('a * 'b) list
  val remove_dup_lists: ('a * 'a -> order) -> 'a list * 'a list -> 'a list * 'a list
  val is_subseq: ('a * 'a -> bool) -> 'a list * 'a list -> bool

  (* Strings. *)
  val is_prefix_str: string -> string -> bool
  val is_just_internal: string -> bool

  (* Managing matching environments. *)
  val defined_instn: Type.tyenv * Envir.tenv -> string * int -> bool
  val lookup_tyinst: Type.tyenv * Envir.tenv -> string -> typ
  val update_env: indexname * term -> Type.tyenv * Envir.tenv ->
                  Type.tyenv * Envir.tenv
  val eq_env: (Type.tyenv * Envir.tenv) * (Type.tyenv * Envir.tenv) -> bool

  (* Matching. *)
  val first_order_match_list:
      theory -> (term * term) list -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

  (* Printing functions, mostly from Isabelle Cookbook. *)
  val string_of_terms: Proof.context -> term list -> string
  val string_of_terms_global: theory -> term list -> string
  val string_of_tyenv: Proof.context -> Type.tyenv -> string
  val string_of_env: Proof.context -> Envir.tenv -> string
  val string_of_list: ('a -> string) -> 'a list -> string
  val string_of_list': ('a -> string) -> 'a list -> string
  val string_of_bool: bool -> string

  (* Managing context. *)
  val declare_free_term: term -> Proof.context -> Proof.context

  (* Terms. *)
  val is_abs: term -> bool
  val is_implies: term -> bool
  val dest_binop: term -> term * (term * term)
  val dest_binop_head: term -> term
  val dest_binop_args: term -> term * term
  val dest_args: term -> term list
  val dest_argn: int -> term -> term
  val get_head_name: term -> string
  val is_meta_eq: term -> bool
  val occurs_frees: term list -> term -> bool
  val occurs_free: term -> term -> bool
  val has_vars: term -> bool
  val is_subterm: term -> term -> bool
  val has_subterm: term list -> term -> bool
  val is_head: term -> term -> bool
  val lambda_abstract: term -> term -> term
  val is_pattern_list: term list -> bool
  val is_pattern: term -> bool

  val normalize_meta_all_imp: Proof.context -> conv
  val swap_meta_imp_alls: Proof.context -> conv
  val normalize_meta_horn: Proof.context -> conv
  val strip_meta_horn: term -> term list * (term list * term)
  val list_meta_horn: term list * (term list * term) -> term
  val to_internal_vars: Proof.context -> term list * term -> term list * term
  val rename_abs_term: term list -> term -> term
  val print_term_detail: Proof.context -> term -> string

  (* cterms. *)
  val dest_cargs: cterm -> cterm list
  val dest_binop_cargs: cterm -> cterm * cterm

  (* Theorems. *)
  val arg_backn_conv: int -> conv -> conv
  val argn_conv: int -> conv -> conv
  val comb_equiv: cterm * thm list -> thm
  val name_of_thm: thm -> string
  val update_name_of_thm: thm -> string -> thm -> thm
  val lhs_of: thm -> term
  val rhs_of: thm -> term
  val assume_meta_eq: theory -> term * term -> thm
  val assume_thm: Proof.context -> term -> thm
  val subst_thm_thy: theory -> Type.tyenv * Envir.tenv -> thm -> thm
  val subst_thm: Proof.context -> Type.tyenv * Envir.tenv -> thm -> thm
  val send_first_to_hyps: thm -> thm
  val send_all_to_hyps: thm -> thm
  val subst_thm_atomic: (cterm * cterm) list -> thm -> thm
  val subst_term_norm: Type.tyenv * Envir.tenv -> term -> term
  val concl_conv_n: int -> conv -> conv
  val concl_conv: conv -> conv
  val transitive_list: thm list -> thm
  val skip_n_conv: int -> conv -> conv
  val pattern_rewr_conv: term -> (term * thm) list -> conv
  val eq_cong_th: int -> term -> term -> Proof.context -> thm
  val forall_elim_sch: thm -> thm

  (* Conversions *)
  val reverse_eta_conv: Proof.context -> conv
  val repeat_n_conv: int -> conv -> conv

  (* Miscellaneous. *)
  val test_conv: Proof.context -> conv -> string -> string * string -> unit
  val term_pat_setup: theory -> theory
  val cterm_pat_setup: theory -> theory
  val type_pat_setup: theory -> theory
  val timer: string * (unit -> 'a) -> 'a
  val exn_trace: (unit -> 'a) -> 'a
end;

structure Util : UTIL =
struct

fun assert b exn_str = if b then () else raise Fail exn_str

val propT = @{typ prop}

fun max comp lst =
    let
      fun max2 t1 t2 = if comp (t1, t2) = LESS then t2 else t1
    in
      case lst of
          [] => raise Fail "max: empty list"
        | l :: ls => fold max2 ls l
    end

(* Given a function comp, remove y for each pair (x, y) such that comp
   x y = true (if x dominates y).
 *)
fun max_partial comp lst =
    let
      fun helper taken remains =
          case remains of
              [] => taken
            | x :: xs =>
              if exists (fn y => comp y x) taken then
                helper taken xs
              else
                helper (x :: filter_out (fn y => comp x y) taken) xs
    in
      helper [] lst
    end

(* Return all subsets of lst. *)
fun subsets [] = [[]]
  | subsets (l::ls) =
    let val prev = subsets ls in prev @ map (cons l) prev end

(* List of all permutations of xs *)
fun all_permutes xs =
    case xs of
        [] => [[]]
      | [x] => [[x]]
      | [x, y] => [[x, y], [y, x]]
      | _ =>
        maps (fn i => map (cons (nth xs i)) (all_permutes (nth_drop i xs)))
             (0 upto (length xs - 1))

(* Convert list to pair. List must consist of exactly two items. *)
fun the_pair lst =
    case lst of [i1, i2] => (i1, i2)
              | _ => raise Fail "the_pair"

(* Convert list to triple. List must consist of exactly three items. *)
fun the_triple lst =
    case lst of [i1, i2, i3] => (i1, i2, i3)
              | _ => raise Fail "the_triple"

(* Split list into (ins, outs), where ins satisfy f, and outs don't. *)
fun filter_split _ [] = ([], [])
  | filter_split f (x :: xs) =
    let
      val (ins, outs) = filter_split f xs
    in
      if f x then (x :: ins, outs) else (ins, x :: outs)
    end

(* Form the Cartesian product of two lists. *)
fun all_pairs (l1, l2) =
    maps (fn y => (map (fn x => (x, y)) l1)) l2

(* Given two sorted lists, remove all pairs of terms that appear in
   both lists, counting multiplicity.
 *)
fun remove_dup_lists ord (xs, ys) =
    case xs of
        [] => ([], ys)
     | x :: xs' =>
       case ys of
           [] => (xs, [])
         | y :: ys' =>
           case ord (x, y) of
               LESS => apfst (cons x) (remove_dup_lists ord (xs', ys))
             | EQUAL => remove_dup_lists ord (xs', ys')
             | GREATER => apsnd (cons y) (remove_dup_lists ord (xs, ys'))

(* Whether l1 is a subsequence of l2. *)
fun is_subseq eq (l1, l2) =
    case l1 of
        [] => true
      | x :: l1' =>
        case l2 of
            [] => false
          | y :: l2' => if eq (x, y) then is_subseq eq (l1', l2')
                        else is_subseq eq (l1, l2')

(* Whether pre is a prefix of str. *)
fun is_prefix_str pre str =
    is_prefix (op =) (String.explode pre) (String.explode str)

(* Test whether x is followed by exactly one _. *)
fun is_just_internal x =
    Name.is_internal x andalso not (Name.is_skolem x)

val fo_init = (Vartab.empty, Vartab.empty)

(* Lookup a Vartab inst with string and integer specifying indexname. *)
fun defined_instn (_, inst) (str, n) = Vartab.defined inst (str, n)
fun lookup_instn (_, inst) (str, n) =
    case Vartab.lookup inst (str, n) of
        NONE => raise Fail ("lookup_inst: not found " ^ str ^
                            (if n = 0 then "" else string_of_int n))
      | SOME (_, u) => u
fun lookup_inst (tyinst, inst) str = lookup_instn (tyinst, inst) (str, 0)
fun lookup_tyinst (tyinst, _) str =
    case Vartab.lookup tyinst (str, 0) of
        NONE => raise Fail ("lookup_tyinst: not found " ^ str)
      | SOME (_, T) => T

fun update_env (idx, t) (tyenv, tenv) =
    (tyenv, tenv |> Vartab.update_new (idx, (type_of t, t)))

(* A rough comparison, simply compare the corresponding terms. *)
fun eq_env ((_, inst1), (_, inst2)) =
    let
      val data1 = Vartab.dest inst1
      val data2 = Vartab.dest inst2
      fun compare_data (((x, i), (ty, t)), ((x', i'), (ty', t'))) =
          x = x' andalso i = i' andalso ty = ty' andalso t aconv t'
    in
      eq_set compare_data (data1, data2)
    end

fun first_order_match_list thy pairs inst =
    case pairs of
        [] => inst
      | (t, u) :: rest =>
        let
          val inst' = Pattern.first_order_match thy (t, u) inst
        in
          first_order_match_list thy rest inst'
        end

fun string_of_terms ctxt ts =
    ts |> map (Syntax.pretty_term ctxt)
       |> Pretty.commas |> Pretty.block |> Pretty.string_of
fun string_of_terms_global thy ts =
    ts |> map (Syntax.pretty_term_global thy)
       |> Pretty.commas |> Pretty.block |> Pretty.string_of

fun pretty_helper aux env =
    env |> Vartab.dest
        |> map aux
        |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
        |> Pretty.enum "," "[" "]"
        |> Pretty.string_of

fun string_of_tyenv ctxt tyenv =
    let
      fun get_typs (v, (s, T)) = (TVar (v, s), T)
      val print = apply2 (Syntax.pretty_typ ctxt)
    in
      pretty_helper (print o get_typs) tyenv
    end

fun string_of_env ctxt env =
    let
      fun get_ts (v, (T, t)) = (Var (v, T), t)
      val print = apply2 (Syntax.pretty_term ctxt)
    in
      pretty_helper (print o get_ts) env
    end

fun string_of_list func lst =
    Pretty.str_list "[" "]" (map func lst) |> Pretty.string_of
fun string_of_list' func lst =
    if length lst = 1 then func (the_single lst) else string_of_list func lst
fun string_of_bool b = if b then "true" else "false"

fun trace_t ctxt s t =
    tracing (s ^ " " ^ (Syntax.string_of_term ctxt t))
fun trace_tlist ctxt s ts =
    tracing (s ^ " " ^ (string_of_terms ctxt ts))
fun trace_thm ctxt s th =
    tracing (s ^ " " ^ (th |> Thm.prop_of |> Syntax.string_of_term ctxt))
fun trace_fullthm ctxt s th =
    tracing (s ^ " [" ^ (Thm.hyps_of th |> string_of_terms ctxt) ^
             "] ==> " ^ (Thm.prop_of th |> Syntax.string_of_term ctxt))
fun trace_thm_global s th =
    let
      val thy = Thm.theory_of_thm th
    in
      tracing (s ^ " " ^ (th |> Thm.prop_of |> Syntax.string_of_term_global thy))
    end

fun trace_fullthm_global s th =
    let
      val thy = Thm.theory_of_thm th
    in
      tracing (s ^ " [" ^ (Thm.hyps_of th |> string_of_terms_global thy) ^
               "] ==> " ^ (Thm.prop_of th |> Syntax.string_of_term_global thy))
    end

fun declare_free_term t ctxt =
    if not (is_Free t) then raise Fail "declare_free_term: t not free."
    else ctxt |> Variable.add_fixes_direct [t |> Term.dest_Free |> fst]
              |> Variable.declare_term t

fun is_abs t =
    case t of Abs _ => true | _ => false

(* Whether a given term is of the form A ==> B. *)
fun is_implies t =
    let val _ = assert (fastype_of t = propT) "is_implies: wrong type"
    in case t of @{const Pure.imp} $ _ $ _ => true
               | _ => false
    end

(* Extract the last two arguments on t, collecting the rest into f. *)
fun dest_binop t =
    case t of
        f $ a $ b => (f, (a, b))
      | _ => raise Fail "dest_binop"

fun dest_binop_head t = fst (dest_binop t)
fun dest_binop_args t = snd (dest_binop t)

(* Return the argument of t. If t is f applied to multiple arguments,
   return the last argument.
 *)
fun dest_arg t =
    case t of _ $ arg => arg | _ => raise Fail "dest_arg"

(* Return the first of two arguments of t. *)
fun dest_arg1 t =
    case t of _ $ arg1 $ _ => arg1 | _ => raise Fail "dest_arg1"

(* Return the list of all arguments of t. *)
fun dest_args t = t |> Term.strip_comb |> snd

(* Return the nth argument of t, counting from left and starting at zero. *)
fun dest_argn n t = nth (dest_args t) n

(* Return the name of the head function. *)
fun get_head_name t =
    case Term.head_of t of
        Const (nm, _) => nm
      | _ => raise Fail "get_head_name"

(* Whether the term is of the form A == B. *)
fun is_meta_eq t =
    let val _ = assert (fastype_of t = propT) "is_meta_eq_term: wrong type"
    in case t of Const (@{const_name Pure.eq}, _) $ _ $ _ => true
               | _ => false
    end

(* Given free variable freevar (or a list of free variables freevars),
   determine whether any of the inputs appears in t.
 *)
fun occurs_frees freevars t =
    inter (op aconv) (map Free (Term.add_frees t [])) freevars <> []
fun occurs_free freevar t = occurs_frees [freevar] t

(* Whether the given term contains schematic variables. *)
fun has_vars t = length (Term.add_vars t []) > 0

(* Whether subt is a subterm of t. *)
fun is_subterm subt t = exists_subterm (fn t' => t' aconv subt) t

(* Whether any of subts is a subterm of t. *)
fun has_subterm subts t = exists_subterm (fn t' => member (op aconv) subts t') t

(* Whether s is a head term of t. *)
fun is_head s t =
    let
      val (sf, sargs) = Term.strip_comb s
      val (tf, targs) = Term.strip_comb t
    in
      sf aconv tf andalso is_prefix (op aconv) sargs targs
    end

(* If stmt is P(t), return %t. P(t). *)
fun lambda_abstract t stmt = Term.lambda t (Term.abstract_over (t, stmt))

(* A more general criterion for patterns. In combinations, any
   argument that is a pattern (in the more general sense) frees up
   checking for any functional schematic variables in that argument.
 *)
fun is_pattern_list ts =
    let
      fun is_funT T = case T of Type ("fun", _) => true | _ => false
      fun get_fun_vars t = (Term.add_vars t [])
                               |> filter (is_funT o snd) |> map Var

      fun test_list exclude_vars ts =
          case ts of
              [] => true
            | [t] => test_term exclude_vars t
            | t :: ts' =>
              if test_term exclude_vars t then
                test_list (merge (op aconv) (exclude_vars, get_fun_vars t)) ts'
              else if test_list exclude_vars ts' then
                test_term (distinct (op aconv)
                                    (exclude_vars @ maps get_fun_vars ts')) t
              else false

      and test_term exclude_vars t =
          case t of
              Abs (_, _, t') => test_term exclude_vars t'
            | _ => let val (head, args) = strip_comb t in
                     if is_Var head then
                       if member (op aconv) exclude_vars head then
                         test_list exclude_vars args
                       else
                         forall is_Bound args andalso
                         not (has_duplicates (op aconv) args)
                     else
                       test_list exclude_vars args
                   end
    in
      test_list [] ts
    end

fun is_pattern t = is_pattern_list [t]

(* Push !!x to the right as much as possible. *)
fun normalize_meta_all_imp_once ct =
    Conv.try_conv (
      Conv.every_conv [Conv.rewr_conv (Thm.symmetric @{thm Pure.norm_hhf_eq}),
                       Conv.arg_conv normalize_meta_all_imp_once]) ct

fun normalize_meta_all_imp ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if Logic.is_all t then
        Conv.every_conv [Conv.binder_conv (normalize_meta_all_imp o snd) ctxt,
                         normalize_meta_all_imp_once] ct
      else if is_implies t then
        Conv.arg_conv (normalize_meta_all_imp ctxt) ct
      else
        Conv.all_conv ct
    end

(* Rewrite A ==> !!v_i. B to !!v_i. A ==> B. *)
fun swap_meta_imp_alls ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if is_implies t andalso Logic.is_all (dest_arg t) then
        Conv.every_conv [Conv.rewr_conv @{thm Pure.norm_hhf_eq},
                         Conv.binder_conv (swap_meta_imp_alls o snd) ctxt] ct
      else
        Conv.all_conv ct
    end

(* Normalize a horn clause into standard form !!v_i. A_i ==> B. *)
fun normalize_meta_horn ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if Logic.is_all t then
        Conv.binder_conv (normalize_meta_horn o snd) ctxt ct
      else if is_implies t then
        Conv.every_conv [Conv.arg_conv (normalize_meta_horn ctxt),
                         swap_meta_imp_alls ctxt] ct
      else
        Conv.all_conv ct
    end

(* Deconstruct a horn clause !!v_i. A_i ==> B into (v_i, (A_i, B)). *)
fun strip_meta_horn t =
    case t of
        Const (@{const_name Pure.all}, _) $ Abs (abs as (_, T, _)) =>
        let
          val (x, body) = Term.dest_abs abs
          val var = Free (x, T)
          val (vars, (assums, concl)) = strip_meta_horn body
        in
          (var :: vars, (assums, concl))
        end
      | @{const Pure.imp} $ P $ Q =>
        let
          val (vars, (assums, concl)) = strip_meta_horn Q
        in
          (vars, (P :: assums, concl))
        end
      | _ => ([], ([], t))

fun list_meta_horn (vars, (As, B)) =
    (Logic.list_implies (As, B)) |> fold Logic.all (rev vars)

fun to_internal_vars ctxt (vars, body) =
    let
      val vars' = vars |> map Term.dest_Free
                       |> Variable.variant_frees ctxt []
                       |> map (apfst Name.internal)
                       |> map Free
      val subst = vars ~~ vars'
    in
      (vars', subst_atomic subst body)
    end

fun rename_abs_term vars t =
    case vars of
        [] => t
      | var :: rest =>
        let
          val (x, _) = Term.dest_Free var
        in
          case t of A $ Abs (_, T1, body) =>
                    A $ Abs (x, T1, rename_abs_term rest body)
                  | _ => error "rename_abs_term"
        end

fun print_term_detail ctxt t =
    case t of
        Const (s, ty) => "Const (" ^ s ^ ", " ^ (Syntax.string_of_typ ctxt ty)
      | Free (s, ty) => "Free (" ^ s ^ ", " ^ (Syntax.string_of_typ ctxt ty) ^ ")"
      | Var ((x, i), ty) => "Var ((" ^ x ^ ", " ^ (string_of_int i) ^ "), " ^
                             (Syntax.string_of_typ ctxt ty) ^ ")"
      | Bound n => "Bound " ^ (string_of_int n)
      | Abs (s, ty, b) => "Abs (" ^ s ^ ", " ^ (Syntax.string_of_typ ctxt ty) ^
                          ", " ^ (print_term_detail ctxt b) ^ ")"
      | u $ v => "(" ^ print_term_detail ctxt u ^ ") $ (" ^
                 print_term_detail ctxt v ^ ")"

(* Version for ct. *)
fun dest_cargs ct = ct |> Drule.strip_comb |> snd
fun dest_binop_cargs ct = (Thm.dest_arg1 ct, Thm.dest_arg ct)

(* Apply cv to nth argument of t, counting from right and starting at 0. *)
fun arg_backn_conv n cv ct =
    if n = 0 then Conv.arg_conv cv ct
    else Conv.fun_conv (arg_backn_conv (n-1) cv) ct

(* Apply cv to nth argument of t, counting from left and starting at 0. *)
fun argn_conv n cv ct =
    let
      val args_count = ct |> Thm.term_of |> dest_args |> length
      val _ = assert (n >= 0 andalso n < args_count)
    in
      arg_backn_conv (args_count - n - 1) cv ct
    end

(* Given a head cterm f (function to be applied), and a list of
   equivalence theorems of arguments, produce an equivalent theorem
   for the overall term.
 *)
fun comb_equiv (cf, arg_equivs) =
    Library.foldl (uncurry Thm.combination) (Thm.reflexive cf, arg_equivs)

(* Retrive name of theorem. *)
fun name_of_thm th = if Thm.has_name_hint th then Thm.get_name_hint th
                     else raise Fail "name_of_thm: not found"

(* Set the name of th to the name of ori_th, followed by suffix. *)
fun update_name_of_thm ori_th suffix th =
    if Thm.has_name_hint ori_th then
      th |> Thm.put_name_hint (Thm.get_name_hint ori_th ^ suffix)
    else th

val lhs_of = Thm.term_of o Thm.lhs_of
val rhs_of = Thm.term_of o Thm.rhs_of

fun assume_meta_eq thy (t1, t2) =
    Thm.assume (Thm.global_cterm_of thy (Logic.mk_equals (t1, t2)))
fun assume_thm ctxt t =
    if type_of t <> propT then
      raise Fail "assume_thm: t is not of type prop"
    else Thm.assume (Thm.cterm_of ctxt t)

(* Similar to Envir.subst_term. Apply an instantiation to a theorem. *)
fun subst_thm_thy thy (tyinsts, insts) th =
    let
      fun process_tyenv (v, (S, T)) =
          ((v, S), Thm.global_ctyp_of thy T)
      val tys = map process_tyenv (Vartab.dest tyinsts)
      fun process_tenv (v, (T, u)) =
          ((v, Envir.subst_type tyinsts T), Thm.global_cterm_of thy u)
      val ts = map process_tenv (Vartab.dest insts)
    in
      th |> Drule.instantiate_normalize (tys, ts)
    end

fun subst_thm ctxt (tyinsts, insts) th =
    subst_thm_thy (Proof_Context.theory_of ctxt) (tyinsts, insts) th

fun send_first_to_hyps th =
    let
      val cprem = Thm.cprem_of th 1
    in
      Thm.implies_elim th (Thm.assume cprem)
    end

fun send_all_to_hyps th =
    let
      val _ = assert (forall (not o has_vars) (Thm.prems_of th))
                     "send_all_to_hyps: schematic variables in hyps."
    in
      funpow (Thm.nprems_of th) send_first_to_hyps th
    end

(* Replace using subst the internal variables in th. This proceeds in
   several steps: first, pull any hypotheses of the theorem involving
   the replaced variables into statement of the theorem, perform the
   replacement (using forall_intr then forall_elim), finally return
   the hypotheses to their original place.
 *)
fun subst_thm_atomic subst th =
    let
      val old_cts = map fst subst
      val old_ts = map Thm.term_of old_cts
      val new_cts = map snd subst
      val chyps = filter (fn ct => has_subterm old_ts (Thm.term_of ct))
                         (Thm.chyps_of th)
    in
      th |> fold Thm.implies_intr chyps
         |> fold Thm.forall_intr old_cts
         |> fold Thm.forall_elim (rev new_cts)
         |> funpow (length chyps) send_first_to_hyps
    end

(* Substitution into terms used in auto2. Substitute types first and
   instantiate the types in the table of term instantiations. Also
   perform beta_norm at the end.
 *)
fun subst_term_norm (tyinsts, insts) t =
    let
      fun inst_tenv tenv =
          tenv |> Vartab.dest
               |> map (fn (ixn, (T, v)) =>
                          (ixn, (Envir.subst_type tyinsts T, v)))
               |> Vartab.make
    in
      t |> Envir.subst_term_types tyinsts
        |> Envir.subst_term (tyinsts, inst_tenv insts)
        |> Envir.beta_norm
    end

(* Apply the conversion cv to the statement of th, yielding the
   equivalent theorem.
 *)
fun apply_to_thm cv th =
    let val eq = cv (Thm.cprop_of th)
    in if Thm.is_reflexive eq then th else Thm.equal_elim eq th end

(* Given th of form A == B, get th' of form B == A. *)
val meta_sym = Thm.symmetric

(* Apply conv to rewrite the left hand side of th. *)
fun apply_to_lhs cv th =
    let val eq = cv (Thm.lhs_of th)
    in if Thm.is_reflexive eq then th else Thm.transitive (meta_sym eq) th end

(* Apply conv to rewrite the right hand side of th. *)
fun apply_to_rhs cv th =
    let val eq = cv (Thm.rhs_of th)
    in if Thm.is_reflexive eq then th else Thm.transitive th eq end

(* Using cv, rewrite the part of ct after stripping i premises. *)
fun concl_conv_n i cv ct =
    if i = 0 then cv ct
    else (Conv.arg_conv (concl_conv_n (i-1) cv)) ct

(* Rewrite part of ct after stripping all premises. *)
fun concl_conv cv ct =
    case Thm.term_of ct of
        @{const Pure.imp} $ _ $ _ => Conv.arg_conv (concl_conv cv) ct
      | _ => cv ct

(* Given a list of theorems A = B, B = C, etc., apply
   Thm.transitive to get equality between start and end.
 *)
fun transitive_list ths =
    let
      fun rev_transitive btoc atob =
          let
            val (b, c) = btoc |> Thm.cprop_of |> Thm.dest_equals
            val (a, b') = atob |> Thm.cprop_of |> Thm.dest_equals
          in
            if b aconvc b' then
              if a aconvc b then btoc
              else if b aconvc c then atob
              else Thm.transitive atob btoc
            else
              let
                val _ = map (trace_thm_global "ths:") ths
              in
                raise Fail "transitive_list: intermediate does not agree"
              end
          end
    in
      fold rev_transitive (tl ths) (hd ths)
    end

(* Skip to argument n times. For example, if applied to rewrite a
   proposition in implication form (==> or -->), it will skip the
   first n assumptions.
 *)
fun skip_n_conv n cv =
    if n <= 0 then cv else Conv.arg_conv (skip_n_conv (n-1) cv)

(* Given a term t, and pairs (a_i, eq_i), where a_i's are atomic
   subterms of t. Suppose the input is obtained by replacing each a_i
   by the left side of eq_i in t, obtain equality from t to the term
   obtained by replacing each a_i by the right side of eq_i in t.
 *)
fun pattern_rewr_conv t eq_ths ct =
    case t of
        Bound _ => raise Fail "pattern_rewr_conv: bound variable."
      | Abs _ => raise Fail "pattern_rewr_conv: abs not supported."
      | _ $ _ =>
        let
          val (f, arg) = Term.strip_comb t
          val (f', arg') = Drule.strip_comb ct
          val _ = assert (f aconv Thm.term_of f')
                         "pattern_rewr_conv: input does not match pattern."
          val ths = map (fn (t, ct) => pattern_rewr_conv t eq_ths ct)
                        (arg ~~ arg')
        in
          comb_equiv (f', ths)
        end
      | Const _ =>
        let
          val _ = assert (t aconv Thm.term_of ct)
                         "pattern_rewr_conv: input does not match pattern."
        in
          Conv.all_conv ct
        end
      | _ =>  (* Free and Var cases *)
        (case AList.lookup (op aconv) eq_ths t of
             NONE => Conv.all_conv ct
           | SOME eq_th =>
             let
               val _ = assert (lhs_of eq_th aconv (Thm.term_of ct))
                              "pattern_rewr_conv: wrong substitution."
             in
               eq_th
             end)

(* Given integer i, term b_i, and a term A = f(a_1, ..., a_n), produce
   the theorem a_i = b_i ==> A = f(a_1, ..., b_i, ..., a_n).
 *)
fun eq_cong_th i bi A ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val (cf, cargs) = Drule.strip_comb (Thm.cterm_of ctxt A)
      val _ = assert (i < length cargs) "eq_cong_th: i out of bounds."
      val ai = Thm.term_of (nth cargs i)
      val eq_i = assume_meta_eq thy (ai, bi)
      val eqs = map Thm.reflexive (take i cargs) @ [eq_i] @
                map Thm.reflexive (drop (i + 1) cargs)
      val eq_A = comb_equiv (cf, eqs)
    in
      Thm.implies_intr (Thm.cprop_of eq_i) eq_A
    end

(* Convert theorems of form !!x y. P x y into P ?x ?y (arbitrary
   number of quantifiers).
 *)
fun forall_elim_sch th =
    case Thm.prop_of th of
        Const (@{const_name Pure.all}, _) $ Abs (x, T, _) =>
        let
          val var_xs = map fst (Term.add_var_names (Thm.prop_of th) [])
          val x' = if member (op =) var_xs x then
                     singleton (Name.variant_list var_xs) x
                   else x
          val thy = Thm.theory_of_thm th
        in
          th |> Thm.forall_elim (Thm.global_cterm_of thy (Var ((x', 0), T)))
             |> forall_elim_sch
        end
      | _ => th

(* Given P of function type, produce P == %x. P x. *)
fun reverse_eta_conv ctxt ct =
    let
      val t = Thm.term_of ct
      val argT = Term.domain_type (fastype_of t)
                 handle Match => raise CTERM ("reverse_eta_conv", [ct])
      val rhs = Abs ("x", argT, t $ Bound 0)
      val eq_th = Thm.eta_conversion (Thm.cterm_of ctxt rhs)
    in
      meta_sym eq_th
    end

(* Repeat cv exactly n times. *)
fun repeat_n_conv n cv t =
    if n = 0 then Conv.all_conv t
    else (cv then_conv (repeat_n_conv (n-1) cv)) t

(* Generic function for testing a conv. *)
fun test_conv ctxt cv err_str (str1, str2) =
    let
      val (t1, t2) = (Proof_Context.read_term_pattern ctxt str1,
                      Proof_Context.read_term_pattern ctxt str2)
      val th = cv (Thm.cterm_of ctxt t1)
    in
      if t1 aconv (lhs_of th) andalso t2 aconv (rhs_of th) then ()
      else let
        val _ = trace_t ctxt "Input:" t1
        val _ = trace_t ctxt "Expected:" t2
        val _ = trace_t ctxt "Actual:" (Thm.prop_of th)
      in
        raise Fail err_str
      end
    end

(* term_pat and typ_pat, from Isabelle Cookbook. *)
val term_pat_setup =
    let
      val parser = Args.context -- Scan.lift Args.embedded_inner_syntax
      fun term_pat (ctxt, str) =
          str |> Proof_Context.read_term_pattern ctxt
              |> ML_Syntax.print_term
              |> ML_Syntax.atomic
    in
      ML_Antiquotation.inline @{binding "term_pat"} (parser >> term_pat)
    end

val cterm_pat_setup =
    let
      val parser = Args.context -- Scan.lift Args.embedded_inner_syntax
      fun cterm_pat (ctxt, str) =
          str |> Proof_Context.read_term_pattern ctxt
              |> ML_Syntax.print_term
              |> ML_Syntax.atomic
              |> prefix "Thm.cterm_of ML_context"
    in
      ML_Antiquotation.value @{binding "cterm_pat"} (parser >> cterm_pat)
    end

val type_pat_setup =
    let
      val parser = Args.context -- Scan.lift Args.embedded_inner_syntax
      fun typ_pat (ctxt, str) =
          let
            val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
          in
            str |> Syntax.read_typ ctxt'
                |> ML_Syntax.print_typ
                |> ML_Syntax.atomic
          end
    in
      ML_Antiquotation.inline @{binding "typ_pat"} (parser >> typ_pat)
    end

(* Time the given function f : unit -> 'a. *)
fun timer (msg, f) =
    let
      val t_start = Timing.start ()
      val res = f ()
      val t_end = Timing.result t_start
    in
      (writeln (msg ^ (Timing.message t_end)); res)
    end

(* When exception is shown when running function f : unit -> 'a, print
   stack trace.
 *)
fun exn_trace f = Runtime.exn_trace f

end  (* structure Util. *)

structure Basic_Util: BASIC_UTIL = Util
open Basic_Util

val _ = Theory.setup (Util.term_pat_setup)
val _ = Theory.setup (Util.cterm_pat_setup)
val _ = Theory.setup (Util.type_pat_setup)
