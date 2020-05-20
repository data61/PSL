(*
  File: wfdata.ML
  Author: Bohua Zhan

  Table storing wellformed-ness data during the proof.
*)

signature WELLFORM_DATA =
sig
  val clean_resolved: box_id -> Proof.context -> Proof.context
  val clear_incr: Proof.context -> Proof.context
  val initialize_wellform_data: term -> Proof.context -> Proof.context

  (* wellform table. *)
  val get_wellform_for_term:
      Proof.context -> term -> (cterm * (box_id * thm) list) list
  val get_wellform_infos_for_term: Proof.context -> term -> (box_id * thm) list
  val convert_wellform:
      Proof.context -> box_id * thm -> box_id * thm -> box_id * thm
  val get_wellform: Proof.context -> box_id * cterm -> (box_id * thm) list
  val get_wellform_t: Proof.context -> box_id * term -> (box_id * thm) list
  val get_complete_wellform:
      Proof.context -> box_id * cterm -> (box_id * thm list) list
  val cterm_to_wfterm:
      Proof.context -> term list -> box_id * cterm -> (box_id * wfterm) list
  val term_to_wfterm:
      Proof.context -> term list -> box_id * term -> (box_id * wfterm) list

  (* Update to wellform table. *)
  val add_wellform_data_raw:
      term * (box_id * thm) -> Proof.context -> Proof.context
  val find_fact: Proof.context -> box_item list -> box_id * cterm -> (box_id * thm) list
  val complete_wellform_data_for_terms:
      box_item list -> term list -> Proof.context -> Proof.context
  val complete_wellform_data: box_item list -> Proof.context -> Proof.context

  (* Get changes to wellform table. *)
  val get_new_wellform_data: Proof.context -> (term * (box_id * thm)) list

  (* More queries on the wellform table.*)
  val simplify_info:
      Proof.context -> term list -> cterm -> (box_id * (wfterm * thm)) list
  val simplify: Proof.context -> term list -> cterm list -> box_id * wfterm ->
                (box_id * (wfterm * thm)) list
  val get_head_equiv:
      Proof.context -> term list -> box_id * cterm -> (box_id * (wfterm * thm)) list
end;

structure WellformData : WELLFORM_DATA =
struct

structure Data = Proof_Data
(
  type T = ((cterm * (box_id * thm) list) list) Termtab.table
  fun init _ = Termtab.empty
)

fun clean_resolved id ctxt =
    let
      fun clean_wellform_1 (ctarget, infos) =
          (ctarget, filter_out (BoxID.is_eq_ancestor ctxt id o fst) infos)

      fun clean_wellform tb =
          tb |> Termtab.map (fn _ => map clean_wellform_1)
    in
      ctxt |> Data.map clean_wellform
    end

fun clear_incr ctxt =
    let
      fun clear_one (ct, infos) =
          if exists (BoxID.has_incr_id o fst) infos then
            (ct, infos |> map (apfst BoxID.replace_incr_id)
                       |> Util.max_partial (BoxID.info_eq_better ctxt))
          else
            (ct, infos)
    in
      ctxt |> Data.map (Termtab.map (fn _ => map clear_one))
    end

(* Initialize wellform data for term t, with (currently) empty slots
   for each target.
 *)
fun initialize_wellform_data t ctxt =
    let
      val wellform = Data.get ctxt
      val thy = Proof_Context.theory_of ctxt
      val targets = map (Thm.cterm_of ctxt) (WellForm.lookup_wellform_data thy t)
    in
      if Termtab.defined wellform t then ctxt
      else if null targets then ctxt
      else ctxt |> Data.map (Termtab.update (t, map (rpair []) targets))
    end

fun get_wellform_for_term ctxt t =
    let
      val wellform = Data.get ctxt
    in
      the_default [] (Termtab.lookup wellform t)
    end

(* Given a term t, return the wellform data for t in a list of (id,
   th) pairs.
 *)
fun get_wellform_infos_for_term ctxt t =
    maps snd (get_wellform_for_term ctxt t)

(* Given (id, th) a wellform data for the left side of eq_th, convert
   to a wellform data for the right side.
 *)
fun convert_wellform ctxt (id', eq_th) (id, th) =
    let
      val (lhs, rhs) = Logic.dest_equals (Thm.prop_of eq_th)
      val thy = Proof_Context.theory_of ctxt
    in
      if lhs aconv rhs then (id, th) else
      case WellForm.lookup_wellform_pattern thy (Util.lhs_of eq_th, prop_of' th) of
          NONE => raise Fail "convert_wellform: invalid input."
        | SOME (pat, data_pat) =>
          let
            (* Cannot use eq_th directly. Rather, find all the
               equivalences again for all the subterms.
             *)
            val cargs1 = Util.dest_cargs (Thm.lhs_of eq_th)
            val cargs2 = Util.dest_cargs (Thm.rhs_of eq_th)
            val eq_ths =
                map (fn (ct, ct') =>
                        (RewriteTable.equiv_info ctxt id' (ct, ct'))
                            |> filter (fn (id'', _) => id'' = id')
                            |> map snd |> the_single)
                    (cargs1 ~~ cargs2)
            val pat_args = Util.dest_args pat
            val th' = apply_to_thm' (
                  Util.pattern_rewr_conv data_pat (pat_args ~~ eq_ths)) th

            (* Check the result is in the right form. *)
            val subst' = pat_args ~~ map Thm.term_of cargs2
            val prop' = Term.subst_atomic subst' data_pat
            val _ = assert (prop_of' th' aconv prop')
                           "convert_wellform: invalid output."
          in
            (BoxID.merge_boxes ctxt (id, id'), th')
          end
    end

(* Retrieve wellform data for the given term. May need to rewrite t up
   to subterm equivalence.
 *)
fun get_wellform ctxt (id, ct) =
    let
      val t = Thm.term_of ct
    in
      if RewriteTable.in_table_raw_for_id ctxt (id, t) then
        (get_wellform_infos_for_term ctxt t)
            |> BoxID.merge_box_with_info ctxt id
      else
        let
          (* eq_th rewrites t to t', where t' is subterm equivalent to
             t and in the table. Obtain wellform data for t', then
             convert them into wellform data for t.
           *)
          fun process_head_rep (id', eq_th) =
              (get_wellform_infos_for_term ctxt (Util.rhs_of eq_th))
                  |> map (convert_wellform ctxt (id', meta_sym eq_th))
        in
          (RewriteTable.subterm_simplify_info ctxt ct)
              |> maps (RewriteTable.get_head_rep_with_id_th ctxt)
              |> maps process_head_rep
              |> BoxID.merge_box_with_info ctxt id
              |> Util.max_partial (BoxID.info_eq_better ctxt)
        end
    end

fun get_wellform_t ctxt (id, t) =
    get_wellform ctxt (id, Thm.cterm_of ctxt t)

(* Retrieve the complete set of wellform data for term t, indexed by
   box id.
 *)
fun get_complete_wellform ctxt (id, ct) =
    let
      val thy = Proof_Context.theory_of ctxt
      val t = Thm.term_of ct
      val targets = WellForm.lookup_wellform_data thy t
    in
      case targets of
          [] => [(id, [])]
        | _ =>
          let
            val data = (get_wellform ctxt (id, ct))
                           |> map (fn (id', th) => (prop_of' th, (id', th)))
                           |> AList.group (op aconv)
                           |> map snd
            val _ = assert (length data <= length targets)
                           "get_complete_wellform: unexpected length data"
          in
            if length data < length targets then []
            else data |> BoxID.get_all_merges_info ctxt
                      |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
          end
    end

(* Given a regular term, construct a wellformed term by adding
   theorems corresponding to any combination whose head agrees with
   one of fheads.
 *)
fun cterm_to_wfterm ctxt fheads (id, ct) =
    case Thm.term_of ct of
        _ $ _ =>
        let
          val t = Thm.term_of ct
          val (cf, cargs) = Drule.strip_comb ct
        in
          if forall (fn fhead => not (Util.is_head fhead t)) fheads then
            [(id, WfTerm ct)] else
          let
            val wfdata = get_complete_wellform ctxt (id, ct)
            fun process_wfdata (id', ths) =
                (* For each wellform data of t at box id', retrieve
                   the wellform data of each argment, then merge
                   together.
                 *)
                cargs |> map (pair id')
                      |> map (cterm_to_wfterm ctxt fheads)
                      |> BoxID.get_all_merges_info ctxt
                      |> map (fn (id'', arg') => (id'', WfComb (cf, arg', ths)))
          in
            (maps process_wfdata wfdata)
                |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
          end
        end
      | _ => [(id, WfTerm ct)]

fun term_to_wfterm ctxt fheads (id, t) =
    cterm_to_wfterm ctxt fheads (id, Thm.cterm_of ctxt t)

(* Add the given wellform data (id, th) for the term t to the table. *)
fun add_wellform_data_raw (t, (id, th)) ctxt =
    let
      val cprop = cprop_of' th
      val wellform_data = get_wellform_for_term ctxt t
      val infos = the (AList.lookup (op aconvc) wellform_data cprop)
                  handle Option.Option => raise Fail "add_wellform_data_raw"
    in
      if exists (fn info => BoxID.info_eq_better ctxt info (id, th)) infos then ctxt
      else let
        val infos' = infos |> filter_out (BoxID.info_eq_better ctxt (id, th))
                           |> cons (id, th)
      in
        ctxt |> Data.map (
          Termtab.map_entry t (AList.map_entry (op aconvc) cprop (K infos')))
      end
    end

(* Given a list of items, attempt to justify t (of type bool)
   using the theorems, or equalities / properties in the rewrite
   table. Return a list of (id, th) pairs, where the statement of
   th' is t.
 *)
fun find_fact ctxt items (id, ct) =
    let
      val t = Thm.term_of ct

      fun match_item item =
          (ItemIO.match_arg ctxt (PropMatch t) item (id, fo_init))
              |> map (fn ((id', _), th) => (id', th))
    in
      if is_eq_term t then  (* Equality case *)
        map (apsnd to_obj_eq)
            (RewriteTable.equiv_info ctxt id (cdest_eq ct))
      else if Property.is_property t then  (* Property case *)
        PropertyData.get_property ctxt (id, ct)
      else  (* General case *)
        maps match_item items
    end

(* Given a list of (id, th), complete the wellform data. New wellform
   data could be added when:

   - There are new theorems in the list of (id, th).

   - There are new properties added.

   - There are new equalities added.
 *)
fun complete_wellform_data_for_terms items ts ctxt =
    let
      fun get_for_t t =
          let
            val cur_data = get_wellform_for_term ctxt t
            val target_ids = RewriteTable.in_table_raw_ids ctxt t

            fun is_target (id, cprop) =
                let
                  val prop_data = the (AList.lookup (op aconvc) cur_data cprop)
                in
                  not (exists (fn (id', _) => BoxID.is_eq_ancestor ctxt id' id)
                              prop_data)
                end

            val targets = (Util.all_pairs (target_ids, map fst cur_data))
                              |> filter is_target
          in
            targets |> maps (find_fact ctxt items)
                    |> map (pair t)
          end

      val all_data = maps get_for_t ts
    in
      fold add_wellform_data_raw all_data ctxt
    end

fun complete_wellform_data items ctxt =
    let
      val wellform = Data.get ctxt
      val ts = Termtab.keys wellform
    in
      complete_wellform_data_for_terms items ts ctxt
    end

(* Return the list of new wellform data (added under id prim or
   lower). Return as a list of (t, (id, th)).
 *)
fun get_new_wellform_data ctxt =
    let
      val wellform = Data.get ctxt
    in
      wellform |> Termtab.dest
               |> maps (fn (t, vals) => map (pair t) (maps snd vals))
               |> filter (fn (_, (id, _)) => BoxID.has_incr_id id)
    end

(* Find simplifications of ct that are well-formed. *)
fun simplify_info ctxt fheads ct =
    let
      val infos = RewriteTable.simplify_info ctxt ct

      fun process_info (id, eq_th) =
          let
            val rhs = Thm.rhs_of eq_th
            val wfts = cterm_to_wfterm ctxt fheads (id, rhs)
          in
            map (fn (id', wft) => (id', (wft, eq_th))) wfts
          end
    in
      maps process_info infos
    end

(* Assume cts are distinct subterms of wft, find all combinations of
   simplifying the terms ts.
 *)
fun simplify ctxt fheads cts (id, wft) =
    if null cts then [(id, (wft, Thm.reflexive (WfTerm.cterm_of wft)))]
    else
      cts |> map (simplify_info ctxt fheads)
          |> BoxID.get_all_merges_info ctxt
          |> BoxID.merge_box_with_info ctxt id
          |> map (fn (id', wf_eqs) =>
                     (id', WfTerm.rewrite_on_eqs fheads wf_eqs wft))

(* Find all well-formed head equivalences of ct. Return as a list of
   (id, (wft, eq_th)) pairs.
 *)
fun get_head_equiv ctxt fheads (id, ct) =
    let
      val head_equivs =
          ct |> RewriteTable.get_head_equiv ctxt
             |> BoxID.merge_box_with_info ctxt id

      fun process_head_equiv (id', eq_th) =
          let
            val rhs = Thm.rhs_of eq_th
            val wfts = cterm_to_wfterm ctxt fheads (id', rhs)
          in
            map (fn (id'', wft) => (id'', (wft, eq_th))) wfts
          end
    in
      maps process_head_equiv head_equivs
    end

end  (* WellformData *)
