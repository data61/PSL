(*
  File: list_ac.ML
  Author: Bohua Zhan

  Special normalization procedure for list append.

  In addition to normalizing the AC function append, also normalize a # xs to
  [a] @ xs.
*)

signature LIST_AC =
sig
  datatype heads = LIST_APPEND | LIST_CONS | LIST_NIL | LIST_OTHER
  val append_const: typ -> term
  val case_head: typ -> term -> heads
  val is_list_head: typ -> term -> bool
  val get_list_ty: term -> typ option
  val rewrite_on_eqs: typ -> thm list -> cterm -> thm
  val dest_list_full: Proof.context -> typ -> cterm -> cterm list
  val simp_list_expr:
      Proof.context -> typ -> box_id * cterm -> (box_id * thm) list
  val get_list_head_equiv:
      Proof.context -> typ -> box_id * cterm -> (box_id * thm) list
  val list_expand_once:
      Proof.context -> typ -> box_id * cterm -> (box_id * thm) list
  val list_expand:
      Proof.context -> typ -> box_id * cterm -> (box_id * thm) list
  val normalize_list_assoc: typ -> conv
  val normalize_list: typ -> conv
  val list_expand_equiv: proofstep
  val list_expand_unit: proofstep
  val add_list_proofsteps: theory -> theory
end;

structure List_AC : LIST_AC =
struct

datatype heads = LIST_APPEND | LIST_CONS | LIST_NIL | LIST_OTHER

fun append_const T =
    let val lT = HOLogic.listT T
    in Const (@{const_name append}, lT --> lT --> lT) end

fun case_head T t =
    if Util.is_head (append_const T) t then LIST_APPEND
    else if Util.is_head (HOLogic.cons_const T) t andalso
            not (dest_arg t aconv HOLogic.nil_const T) then LIST_CONS
    else if t aconv HOLogic.nil_const T then LIST_NIL
    else LIST_OTHER

fun is_list_head T t =
    case case_head T t of
        LIST_APPEND => true
      | LIST_CONS => true
      | _ => false

fun get_list_ty t =
    case fastype_of t of
        Type ("List.list", [T]) => SOME T
      | _ => NONE

fun rewrite_on_eqs T eqs ct =
    case case_head T (Thm.term_of ct) of
        LIST_APPEND => Conv.binop_conv (rewrite_on_eqs T eqs) ct
      | LIST_CONS => Conv.binop_conv (rewrite_on_eqs T eqs) ct
      | LIST_NIL => Conv.all_conv ct
      | _ =>
        (case find_first (fn eq => (Thm.term_of ct) aconv (Util.lhs_of eq)) eqs of
             NONE => Conv.all_conv ct
           | SOME eq_th => eq_th)

fun dest_list_full ctxt T ct =
    case case_head T (Thm.term_of ct) of
        LIST_APPEND => dest_list_full ctxt T (Thm.dest_arg1 ct) @
                       dest_list_full ctxt T (Thm.dest_arg ct)
      | LIST_CONS => Thm.cterm_of ctxt (
                      HOLogic.mk_list T [dest_arg1 (Thm.term_of ct)]) ::
                     dest_list_full ctxt T (Thm.dest_arg ct)
      | LIST_NIL => []
      | _ => [ct]

fun dest_subs ctxt T ct =
    case case_head T (Thm.term_of ct) of
        LIST_APPEND => dest_subs ctxt T (Thm.dest_arg1 ct) @
                       dest_subs ctxt T (Thm.dest_arg ct)
      | LIST_CONS => Thm.dest_arg1 ct ::
                     dest_subs ctxt T (Thm.dest_arg ct)
      | LIST_NIL => []
      | _ => [ct]

fun simp_list_expr ctxt T (id, cu) =
    let
      val cus = dest_subs ctxt T cu
    in
      if null cus then [(id, Thm.reflexive cu)] else
      cus |> map (RewriteTable.simplify_info ctxt)
          |> BoxID.get_all_merges_info ctxt
          |> BoxID.merge_box_with_info ctxt id
          |> map (fn (id', eqs) => (id', rewrite_on_eqs T eqs cu))
    end

(* Obtain head equivalences of cu, where each term is simplified. *)
fun get_list_head_equiv ctxt T (id, cu) =
    let
      fun process_head_equiv (id', eq_th) =
          let
            val infos = simp_list_expr ctxt T (id', Thm.rhs_of eq_th)
          in
            map (BoxID.merge_eq_infos ctxt (id', eq_th)) infos
          end
    in
      cu |> RewriteTable.get_head_equiv ctxt
         |> BoxID.merge_box_with_info ctxt id
         |> maps process_head_equiv
         |> filter_out (Thm.is_reflexive o snd)
    end

(* Find ways to modify ct once by rewriting one of the subterms. *)
fun list_expand_once ctxt T (id, ct) =
    let
      val cus = dest_subs ctxt T ct
      fun get_equiv cu = get_list_head_equiv ctxt T (id, cu)

      fun process_info (id', eq) =
          (id', rewrite_on_eqs T [eq] ct)
    in
      map process_info (maps get_equiv cus)
    end

(* Find all ways to write ct, up to a certain limit. *)
fun list_expand ctxt T (id, ct) =
    let
      val max_ac = Config.get ctxt AC_ProofSteps.max_ac

      fun list_equiv_eq_better (id, th) (id', th') =
          let
            val seq1 = dest_list_full ctxt T (Thm.rhs_of th)
            val seq2 = dest_list_full ctxt T (Thm.rhs_of th')
          in
            Util.is_subseq (op aconv o apply2 Thm.term_of) (seq1, seq2) andalso
            BoxID.is_eq_ancestor ctxt id id'
          end

      fun has_list_equiv_eq_better infos info' =
          exists (fn info => list_equiv_eq_better info info') infos

      fun helper (old, new) =
          case new of
              [] => old
            | (id', eq_th) :: rest =>
              if length old + length new > max_ac then
                old @ take (max_ac - length old) new
              else let
                val old' = ((id', eq_th) :: old)
                val rhs_expand =
                    (list_expand_once ctxt T (id', Thm.rhs_of eq_th))
                        |> Util.max_partial list_equiv_eq_better
                        |> map (BoxID.merge_eq_infos ctxt (id', eq_th))
                        |> filter_out (has_list_equiv_eq_better (old' @ rest))
              in
                helper (old', rest @ rhs_expand)
              end

      (* Start term *)
      val start = simp_list_expr ctxt T (id, ct)
    in
      helper ([], start)
    end

fun normalize_list_assoc T ct =
    case case_head T (Thm.term_of ct) of
        LIST_APPEND =>
        (case case_head T (dest_arg1 (Thm.term_of ct)) of
             LIST_APPEND =>
             Conv.every_conv [rewr_obj_eq @{thm List.append_assoc},
                              Conv.arg_conv (normalize_list_assoc T)] ct
           | _ => Conv.all_conv ct)
      | _ => Conv.all_conv ct

fun normalize_list T ct =
    case case_head T (Thm.term_of ct) of
        LIST_APPEND =>
        Conv.every_conv [
          Conv.binop_conv (normalize_list T),
          Conv.try_conv (rewr_obj_eq @{thm List.append.append_Nil}),
          Conv.try_conv (rewr_obj_eq @{thm List.append_Nil2}),
          normalize_list_assoc T] ct
      | LIST_CONS =>
        Conv.every_conv [rewr_obj_eq @{thm cons_to_append},
                         normalize_list T] ct
      | _ => Conv.all_conv ct

fun list_expand_equiv_fn ctxt item1 item2 =
    let
      val {id = id1, tname = tname1, ...} = item1
      val {id = id2, tname = tname2, ...} = item2
      val (ct1, ct2) = (the_single tname1, the_single tname2)
      val (t1, t2) = (Thm.term_of ct1, Thm.term_of ct2)
      val id = BoxID.merge_boxes ctxt (id1, id2)
      val T = the (get_list_ty t1)
    in
      if Term_Ord.term_ord (t2, t1) = LESS then []
      else if RewriteTable.is_equiv id ctxt (ct1, ct2) then []
      else if not (is_list_head T t1) orelse not (is_list_head T t2) then []
      else let
        val expand1 = list_expand ctxt T (id, ct1)
        val expand2 = list_expand ctxt T (id, ct2)

        fun get_equiv ((id1, eq_th1), (id2, eq_th2)) =
            let
              val ct1 = Thm.rhs_of eq_th1
              val ct2 = Thm.rhs_of eq_th2
              val ts1 = dest_list_full ctxt T ct1
              val ts2 = dest_list_full ctxt T ct2
            in
              if eq_list (op aconv o apply2 Thm.term_of) (ts1, ts2) then
                let
                  val eq_th1' = normalize_list T ct1
                  val eq_th2' = normalize_list T ct2
                  val id' = BoxID.merge_boxes ctxt (id1, id2)
                  val eq = Util.transitive_list [
                        eq_th1, eq_th1', meta_sym eq_th2', meta_sym eq_th2]
                in
                  [(id', to_obj_eq eq)]
                end
              else []
            end
      in
        (maps get_equiv (Util.all_pairs (expand1, expand2)))
            |> filter (BoxID.has_incr_id o fst)
            |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
            |> map (fn (id, th) => Update.thm_update_sc 1 (id, th))
      end
    end

val list_expand_equiv =
    {name = "list_expand_equiv",
     args = [TypedMatch (TY_TERM, @{term_pat "?A::?'a list"}),
             TypedMatch (TY_TERM, @{term_pat "?B::?'a list"})],
     func = TwoStep list_expand_equiv_fn}

fun list_expand_unit_fn ctxt item =
    let
      val {id, tname, ...} = item
      val ct = the_single tname
      val t = Thm.term_of ct
      val T = the (get_list_ty t)
    in
      if not (is_list_head T t) then []
      else let
        val expand = list_expand ctxt T (id, ct)

        fun process_expand (id', eq_th) =
            let
              val ct = Thm.rhs_of eq_th
              val ts = dest_list_full ctxt T ct
            in
              if length ts <= 1 then
                let
                  val eq' = normalize_list T ct
                  val eq = Util.transitive_list [eq_th, eq']
                in
                  [(id', to_obj_eq eq)]
                end
              else []
            end
      in
        (maps process_expand expand)
            |> filter (BoxID.has_incr_id o fst)
            |> map (fn (id, th) => Update.thm_update_sc 1 (id, th))
      end
    end

val list_expand_unit =
    {name = "list_expand_unit",
     args = [TypedMatch (TY_TERM, @{term_pat "?A::?'a list"})],
     func = OneStep list_expand_unit_fn}

val add_list_proofsteps =
    fold add_prfstep [
      list_expand_equiv, list_expand_unit
    ]

end  (* structure List_AC. *)

val _ = Theory.setup List_AC.add_list_proofsteps
