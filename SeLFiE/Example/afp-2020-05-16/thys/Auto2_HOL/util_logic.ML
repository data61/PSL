(*
  File: util_logic.ML
  Author: Bohua Zhan

  Utility functions, after fixing object logic.
*)

signature BASIC_UTIL_LOGIC =
sig
  (* Terms *)
  val Trueprop: term
  val is_Trueprop: term -> bool
  val mk_Trueprop: term -> term
  val dest_Trueprop: term -> term
  val Trueprop_conv: conv -> conv
  val pFalse: term
  val Not: term
  val mk_not: term -> term
  val dest_not: term -> term
  val is_neg: term -> bool
  val get_neg: term -> term
  val get_neg': term -> term
  val conj: term
  val is_conj: term -> bool
  val mk_conj: term * term -> term
  val strip_conj: term -> term list
  val list_conj: term list -> term
  val disj: term
  val is_disj: term -> bool
  val mk_disj: term * term -> term
  val strip_disj: term -> term list
  val list_disj: term list -> term
  val imp: term
  val is_imp: term -> bool
  val mk_imp: term * term -> term
  val dest_imp: term -> term * term
  val strip_obj_imp: term -> term list * term
  val list_obj_imp: term list * term -> term
  val is_obj_all: term -> bool
  val is_ball: term -> bool
  val mk_obj_all: term -> term -> term
  val is_ex: term -> bool
  val is_bex: term -> bool
  val mk_exists: term -> term -> term
  val is_mem: term -> bool
  val mk_mem: term * term -> term

  (* Theorems *)
  val is_true_th: thm -> bool
  val prop_of': thm -> term
  val cprop_of': thm -> cterm
  val concl_of': thm -> term
  val make_trueprop_eq: thm -> thm
  val assume_eq: theory -> term * term -> thm
  val apply_to_thm': conv -> thm -> thm
  val to_meta_eq: thm -> thm
  val to_obj_eq: thm -> thm
  val obj_sym: thm -> thm
  val rewr_obj_eq: thm -> conv

  val conj_left_th: thm -> thm
  val conj_right_th: thm -> thm
  val equiv_forward_th: thm -> thm
  val equiv_backward_th: thm -> thm
  val inv_backward_th: thm -> thm
  val to_obj_eq_th: thm -> thm
  val to_obj_eq_iff_th: thm -> thm
  val obj_sym_th: thm -> thm
end;

signature UTIL_LOGIC =
sig
  include BASIC_UTIL_LOGIC

  (* Terms *)
  val term_of_bool: bool -> term
  val bool_of_term: term -> bool

  (* Finding subterms *)
  val list_subterms: term -> term list
  val get_all_subterms: term -> term list
  val get_all_subterms_skip_if: term -> term list

  (* cterms *)
  val get_cneg: cterm -> cterm

  (* Theorems *)
  val make_neg_eq: thm -> thm
  val rewrite_to_contra_form: conv
  val rewrite_from_contra_form: conv
  val to_obj_conv: Proof.context -> conv
  val to_obj_conv_on_horn: Proof.context -> conv
  val to_meta_conv: Proof.context -> conv
  val split_conj_th: thm -> thm list
  val split_conj_gen_th: thm -> thm list
  val split_not_disj_th: thm -> thm list
  val strip_horn': thm -> term list * term
  val mk_conjs_th: thm list -> thm
  val ex_elim: Proof.context -> term -> thm -> thm
  val force_abs_form: term -> term
  val strip_obj_horn: term -> term list * (term list * term)
  val list_obj_horn: term list * (term list * term) -> term
  val is_ex_form_gen: term -> bool
  val normalize_exists: Proof.context -> conv
  val strip_exists: term -> term list * term

  (* Wrapper around common tactics. *)
  val prove_by_tac: (Proof.context -> int -> tactic) -> Proof.context ->
                    thm list -> term -> thm
  val contra_by_tac: (Proof.context -> int -> tactic) -> Proof.context ->
                     thm list -> thm
end;

structure UtilLogic : UTIL_LOGIC =
struct

(* Booleans *)

fun term_of_bool b = (if b then bTrue else bFalse)

fun bool_of_term t =
    if t aconv bTrue then true
    else if t aconv bFalse then false
    else raise Fail "bool_of_term: unexpected t."

(* Trueprop *)

val Trueprop = Const (UtilBase.Trueprop_name, boolT --> propT)

(* Returns whether the given term is Trueprop. *)
fun is_Trueprop t =
    let
      val _ = assert (fastype_of t = propT) "is_Trueprop: wrong type"
    in
      case t of Const (c, _) $ _ => c = UtilBase.Trueprop_name
              | _ => false
    end

fun mk_Trueprop P = Trueprop $ P

fun dest_Trueprop t =
    if is_Trueprop t then dest_arg t else raise Fail "dest_Trueprop"

fun Trueprop_conv cv ct =
    if is_Trueprop (Thm.term_of ct) then Conv.arg_conv cv ct
    else raise CTERM ("Trueprop_conv", [ct])

val pFalse = Trueprop $ bFalse

(* Not *)

val Not = Const (UtilBase.Not_name, boolT --> boolT)

fun mk_not P = Not $ P

(* Returns whether the given term is in neg form. *)
fun is_neg t =
    let
      val _ = assert (fastype_of t = boolT) "is_neg: wrong type"
    in
      case t of
          Const (c, _) $ _ => c = UtilBase.Not_name
        | _ => false
    end

fun dest_not t =
    if is_neg t then dest_arg t else raise Fail "dest_not"

(* Returns the negation of the given term. Avoids double negatives. *)
fun get_neg t =
    if is_neg t then dest_not t else Not $ t

(* Version of get_neg for Trueprop terms. *)
fun get_neg' t =
    let
      val _ = assert (is_Trueprop t) "get_neg': input should be a Trueprop."
    in
      t |> dest_Trueprop |> get_neg |> mk_Trueprop
    end

(* Conjunction and disjunction *)

val conj = Const (UtilBase.Conj_name, boolT --> boolT --> boolT)

fun is_conj t =
    case t of Const (c, _) $ _ $ _ => c = UtilBase.Conj_name | _ => false

fun mk_conj (t, u) = conj $ t $ u

fun strip_conj t =
    if is_conj t then (dest_arg1 t) :: strip_conj (dest_arg t) else [t]

fun list_conj ts =
    case ts of
        [] => error "list_conj"
      | [t] => t
      | t :: rest => mk_conj (t, list_conj rest)

val disj = Const (UtilBase.Disj_name, boolT --> boolT --> boolT)

fun is_disj t =
    case t of Const (c, _) $ _ $ _ => c = UtilBase.Disj_name | _ => false

fun mk_disj (t, u) = disj $ t $ u

fun strip_disj t =
    if is_disj t then (dest_arg1 t) :: strip_disj (dest_arg t) else [t]

fun list_disj ts =
    case ts of
        [] => raise Fail "list_disj"
      | [t] => t
      | t :: ts' => mk_disj (t, list_disj ts')

(* Object implication *)

val imp = Const (UtilBase.Imp_name, boolT --> boolT --> boolT)

fun is_imp t =
    case t of Const (c, _) $ _ $ _ => c = UtilBase.Imp_name | _ => false

fun mk_imp (t, u) = imp $ t $ u

fun dest_imp t =
    if is_imp t then (dest_arg1 t, dest_arg t) else raise Fail "dest_imp"

(* Given t of form A1 --> ... --> An, return ([A1, ..., A(n-1)], An). *)
fun strip_obj_imp t =
    if is_imp t then
      let val (As, B') = strip_obj_imp (dest_arg t) in (dest_arg1 t :: As, B') end
    else ([], t)

fun list_obj_imp (As, C) =
    case As of
        [] => C
      | A :: rest => mk_imp (A, list_obj_imp (rest, C))

fun is_obj_all t =
    case t of
        Const (c, _) $ Abs _ => c = UtilBase.All_name | _ => false

fun is_ball t =
    case t of
        Const (c, _) $ _ $ _ => c = UtilBase.Ball_name | _ => false

fun mk_obj_all t body =
    let
      val (x, T) = Term.dest_Free t
    in
      Const (UtilBase.All_name, (T --> boolT) --> boolT) $ Term.absfree (x, T) body
    end

fun is_ex t =
    case t of Const (c, _) $ Abs _ => c = UtilBase.Ex_name | _ => false

fun is_bex t =
    case t of Const (c, _) $ _ $ _ => c = UtilBase.Bex_name | _ => false

fun mk_exists t body =
    let
      val (x, T) = Term.dest_Free t
    in
      Const (UtilBase.Ex_name, (T --> boolT) --> boolT) $ Term.absfree (x, T) body
    end

fun is_mem t =
    case t of Const (c, _) $ _ $ _ => c = UtilBase.Mem_name | _ => false

fun mk_mem (x, A) =
    let
      val T = fastype_of x
    in
      Const (UtilBase.Mem_name, T --> UtilBase.mk_setT T --> boolT) $ x $ A
    end

(* Finding subterms *)

(* Get all subterms of t. *)
fun list_subterms t =
    let
      fun dest_at_head t =
          case t of
              Abs (_, _, body) => dest_at_head body
            | _ => if Term.is_open t then
                     t |> Term.strip_comb |> snd |> maps dest_at_head
                   else [t]

      and dest t =
          case t of
              Abs _ => dest_at_head t
            | _ $ _ => t |> Term.strip_comb |> snd
            | _ => []
    in
      dest t
    end

(* List all (closed) subterms. Larger ones will be listed first. *)
fun get_all_subterms t =
    t |> list_subterms |> maps get_all_subterms |> distinct (op aconv)
      |> cons t

(* List all (closed) subterms. For terms of form if cond then yes or
   no, list only subterms of cond.
 *)
fun get_all_subterms_skip_if t =
    if UtilBase.is_if t then
      t |> Util.dest_args |> hd |> get_all_subterms_skip_if |> cons t
    else
      t |> list_subterms |> maps get_all_subterms_skip_if
        |> distinct (op aconv) |> cons t

(* cterms *)

fun get_cneg ct =
    let
      val t = Thm.term_of ct
      val _ = assert (fastype_of t = boolT) "get_neg: wrong type"
    in
      if is_neg t then Thm.dest_arg ct else Thm.apply UtilBase.cNot ct
    end

(* Theorems *)

fun is_true_th th = Thm.eq_thm_prop (th, true_th)
fun prop_of' th = dest_Trueprop (Thm.prop_of th)
fun cprop_of' th = Thm.dest_arg (Thm.cprop_of th)
fun concl_of' th = dest_Trueprop (Thm.concl_of th)

(* Given an equality between bools, make it an equality between props,
   by applying the function Trueprop to both sides.
 *)
fun make_trueprop_eq th =
    Thm.combination (Thm.reflexive UtilBase.cTrueprop) th

(* Assumed theorems. *)
fun assume_eq thy (t1, t2) =
    Thm.assume (Thm.global_cterm_of thy (mk_Trueprop (mk_eq (t1, t2))))

(* Apply cv to the statement of th, skipping Trueprop. *)
fun apply_to_thm' cv th = apply_to_thm (Trueprop_conv cv) th

val to_meta_eq = apply_to_thm (Util.concl_conv UtilBase.to_meta_eq_cv)

val to_obj_eq = apply_to_thm (Util.concl_conv UtilBase.to_obj_eq_cv)

val obj_sym = apply_to_thm (Util.concl_conv UtilBase.obj_sym_cv)

(* Obtain rewriting conv from obj equality. *)
fun rewr_obj_eq eq_th = Conv.rewr_conv (to_meta_eq eq_th)

(* Given an equality A == B, make the equality ~A == ~B. Cancel ~~ on
   both sides if exists.
 *)
fun make_neg_eq th =
    th |> Thm.combination (Thm.reflexive UtilBase.cNot)
       |> apply_to_lhs (Conv.try_conv (rewr_obj_eq UtilBase.nn_cancel_th))
       |> apply_to_rhs (Conv.try_conv (rewr_obj_eq UtilBase.nn_cancel_th))

(* If ct is of the form [...] ==> False, leave it unchanged.
   Otherwise, change [...] ==> B to [..., ~ B] ==> False and change
   [...] ==> ~ B to [..., B] ==> False.
 *)
fun rewrite_to_contra_form ct =
    let
      val (_, concl) = Logic.strip_horn (Thm.term_of ct)
      val concl' = dest_Trueprop concl
    in
      if concl' aconv bFalse then
        Conv.all_conv ct
      else if is_neg concl' then
        Util.concl_conv (Conv.rewr_conv UtilBase.to_contra_form_th') ct
      else
        Util.concl_conv (Conv.rewr_conv UtilBase.to_contra_form_th) ct
    end

(* Rewrite ct from [...] ==> A ==> False to [...] ==> ~ A and from
   [...] ==> ~ A ==> False to [...] ==> A.
 *)
fun rewrite_from_contra_form ct =
    let
      val (prems, concl) = Logic.strip_horn (Thm.term_of ct)
      val _ = assert (concl aconv pFalse)
                     "rewrite_from_contra_form: concl should be false."
      val num_prems = length prems
      val last_prem' = dest_Trueprop (nth prems (num_prems-1))
      val to_contra_form = if is_neg last_prem' then UtilBase.to_contra_form_th
                           else UtilBase.to_contra_form_th'
    in
      Util.concl_conv_n (num_prems-1)
                        (Conv.rewr_conv (meta_sym to_contra_form)) ct
    end

(* Converts ==> to --> and !! to !. *)
fun to_obj_conv ctxt ct =
    case Thm.term_of ct of
        @{const Pure.imp} $ _ $ _ =>
        Conv.every_conv [Conv.binop_conv (to_obj_conv ctxt),
                         Conv.rewr_conv UtilBase.atomize_imp_th] ct
      | Const (@{const_name Pure.all}, _) $ Abs _ =>
        Conv.every_conv [Conv.binder_conv (to_obj_conv o snd) ctxt,
                         Conv.rewr_conv UtilBase.atomize_all_th] ct
      | _ => Conv.all_conv ct

(* When ct is of form A1 ==> ... ==> An, apply to_obj_conv to each Ai. *)
fun to_obj_conv_on_horn ctxt ct =
    case Thm.term_of ct of
        @{const Pure.imp} $ _ $ _ =>
        Conv.every_conv [Conv.arg1_conv (to_obj_conv ctxt),
                         Conv.arg_conv (to_obj_conv_on_horn ctxt)] ct
      | Const (@{const_name Pure.all}, _) $ Abs _ =>
        Conv.binder_conv (to_obj_conv_on_horn o snd) ctxt ct
      | _ => Conv.all_conv ct

(* Convert !! and ==> on the outermost level. Pull all !! to the front. *)
fun to_meta_conv ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if is_Trueprop t andalso is_obj_all (dest_Trueprop t) then
        Conv.every_conv [Conv.rewr_conv (meta_sym UtilBase.atomize_all_th),
                         to_meta_conv ctxt] ct
      else if is_Trueprop t andalso is_ball (dest_Trueprop t) then
        Conv.every_conv [Conv.arg_conv (rewr_obj_eq UtilBase.Ball_def_th),
                         to_meta_conv ctxt] ct
      else if is_Trueprop t andalso is_imp (dest_Trueprop t) then
        Conv.every_conv [Conv.rewr_conv (meta_sym UtilBase.atomize_imp_th),
                         to_meta_conv ctxt] ct
      else if Logic.is_all t then
        Conv.binder_conv (to_meta_conv o snd) ctxt ct
      else if Util.is_implies t then
        Conv.every_conv [Conv.arg_conv (to_meta_conv ctxt),
                         Util.swap_meta_imp_alls ctxt] ct
      else
        Conv.all_conv ct
    end

(* Modify th using imp_th, and add postfix to name (if available). *)
fun thm_RS_mod imp_th suffix th =
    (th RS imp_th) |> Drule.zero_var_indexes
                   |> Util.update_name_of_thm th suffix

(* From A & B, obtain A. *)
val conj_left_th = thm_RS_mod UtilBase.conjunct1_th "@left"
(* From A & B, obtain B. *)
val conj_right_th = thm_RS_mod UtilBase.conjunct2_th "@right"
(* From (A::bool) = B, obtain A ==> B. *)
val equiv_forward_th = thm_RS_mod UtilBase.iffD1_th "@eqforward"
(* From (A::bool) = B, obtain B ==> A. *)
val equiv_backward_th = thm_RS_mod UtilBase.iffD2_th "@eqbackward"
(* From (A::bool) = B, obtain ~A ==> ~B. *)
val inv_backward_th = thm_RS_mod UtilBase.inv_back_th "@invbackward"
(* Same as to_obj_eq, except keeping names and indices. *)
fun to_obj_eq_th th = th |> to_obj_eq |> Util.update_name_of_thm th "@obj_eq"
(* Same as to_obj_eq_iff, except keeping names and indices. *)
fun to_obj_eq_iff_th th = th |> UtilBase.to_obj_eq_iff |> Util.update_name_of_thm th "@iff"
(* Same as obj_sym, except keeping names and indices. *)
fun obj_sym_th th = th |> obj_sym |> Util.update_name_of_thm th "@sym"

(* Given th of form (P ==>) A1 & ... & An, return theorems (P ==>) A1,
   ..., (P ==>) An, where there can be zero or more premises in front.
 *)
fun split_conj_th th =
    if is_conj (prop_of' th) then
      (th RS UtilBase.conjunct1_th) :: (split_conj_th (th RS UtilBase.conjunct2_th))
    else [th]

(* More general form. *)
fun split_conj_gen_th th =
    if is_conj (prop_of' th) then
      maps split_conj_gen_th [th RS UtilBase.conjunct1_th,
                              th RS UtilBase.conjunct2_th]
    else [th]

(* Given th of form ~ (A1 | ... | An), return theorems ~ A1, ... ~ An. *)
fun split_not_disj_th th =
    let
      val t = prop_of' th
    in
      if is_neg t andalso is_disj (dest_not t) then
        (th RS UtilBase.or_intro1_th) :: (split_not_disj_th (th RS UtilBase.or_intro2_th))
      else [th]
    end

(* Similar to Logic.strip_horn, except remove Trueprop. *)
fun strip_horn' th = (Logic.strip_horn (Thm.prop_of th))
                         |> apfst (map dest_Trueprop)
                         |> apsnd dest_Trueprop

fun mk_conjs_th ths =
    case ths of
        [] => raise Fail "mk_conjs_th"
      | [th] => th
      | th :: rest => [th, mk_conjs_th rest] MRS UtilBase.conjI_th

(* Given th of form P x ==> False, where x is the given free variable,
   obtain new theorem of form (EX x. P x) ==> False. The function is
   written so it can be applied to multiple variables with fold. For
   example, "fold (ex_elim ctxt) [x, y] (P x y ==> False) will give
   (EX y x. P x y) ==> False.
 *)
fun ex_elim ctxt freevar th =
    let
      val thy = Proof_Context.theory_of ctxt
      val th' = th |> Thm.forall_intr (Thm.cterm_of ctxt freevar)
      val head_prem = hd (Thm.prems_of UtilBase.exE_th')
      val inst = Pattern.match thy (head_prem, Thm.prop_of th') fo_init
      val exE_inst = Util.subst_thm ctxt inst UtilBase.exE_th'
    in
      Thm.elim_implies th' exE_inst
    end

fun force_abs_form t =
    case t of
        Abs _ => t
      | _ => Abs ("x", domain_type (fastype_of t), t $ Bound 0)

(* Normalization of object forall expressions in horn-clause form. *)
fun strip_obj_horn t =
    if is_obj_all t then
      case t of
          _ $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val (vars, (assum, concl)) = strip_obj_horn body
          in
            (var :: vars, (assum, concl))
          end
        | f $ arg => strip_obj_horn (f $ force_abs_form arg)
        | _ => raise Fail "strip_obj_horn"
    else if is_ball t then
      case t of
          _ $ S $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val mem = mk_mem (var, S)
            val (vars, (assum, concl)) = strip_obj_horn body
          in
            (var :: vars, (mem :: assum, concl))
          end
        | f $ S $ arg => strip_obj_horn (f $ S $ force_abs_form arg)
        | _ => raise Fail "strip_obj_horn"
    else if is_imp t then
      let
        val (vars, (assum, concl)) = strip_obj_horn (dest_arg t)
      in
        (vars, (dest_arg1 t :: assum, concl))
      end
    else
      ([], ([], t))

fun list_obj_horn (vars, (As, B)) =
    (list_obj_imp (As, B)) |> fold mk_obj_all (rev vars)

(* Whether t can be immediately rewritten into EX form. *)
fun is_ex_form_gen t =
    is_ex t orelse is_bex t orelse
    (is_neg t andalso is_obj_all (dest_not t)) orelse
    (is_neg t andalso is_ball (dest_not t)) orelse
    (is_conj t andalso is_ex_form_gen (dest_arg t))

(* Rewrite A & EX v_i. B to EX v_i. A & B. *)
fun swap_conj_exists ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if is_conj t andalso is_ex (dest_arg t) then
        Conv.every_conv [rewr_obj_eq UtilBase.swap_ex_conj_th,
                         Conv.binder_conv (swap_conj_exists o snd) ctxt] ct
      else
        Conv.all_conv ct
    end

(* Normalize existence statement into EX v_i. A_1 & ... & A_n. This
   includes moving as many existence quantifiers to the left as
   possible.
 *)
fun normalize_exists ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if is_ex t then
        Conv.binder_conv (normalize_exists o snd) ctxt ct
      else if is_bex t then
        Conv.every_conv [rewr_obj_eq UtilBase.Bex_def_th, normalize_exists ctxt] ct
      else if is_neg t andalso is_obj_all (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.not_all_th, normalize_exists ctxt] ct
      else if is_neg t andalso is_ball (dest_not t) then
        Conv.every_conv [Conv.arg_conv (rewr_obj_eq UtilBase.Ball_def_th),
                         rewr_obj_eq UtilBase.not_all_th,
                         Conv.binder_conv (K (rewr_obj_eq UtilBase.not_imp_th)) ctxt,
                         normalize_exists ctxt] ct
      else if is_conj t then
        Conv.every_conv [Conv.arg_conv (normalize_exists ctxt),
                         swap_conj_exists ctxt] ct
      else
        Conv.all_conv ct
    end

(* Assume t is in normal form. *)
fun strip_exists t =
    if is_ex t then
      case t of
          _ $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val (vars, body') = strip_exists body
          in
            (var :: vars, body')
          end
        | _ => raise Fail "strip_exists"
    else
      ([], t)

(* Generic wrapper function. tac can be arith_tac, simp_tac, etc. *)
fun prove_by_tac tac ctxt ths goal =
    let
      val goal' = Logic.list_implies (map Thm.prop_of ths, mk_Trueprop goal)
    in
      ths MRS (Goal.prove ctxt [] [] goal' (K (tac ctxt 1)))
    end

fun contra_by_tac tac ctxt ths = prove_by_tac tac ctxt ths bFalse

end  (* structure UtilLogic *)

structure Basic_UtilLogic: BASIC_UTIL_LOGIC = UtilLogic
open Basic_UtilLogic
