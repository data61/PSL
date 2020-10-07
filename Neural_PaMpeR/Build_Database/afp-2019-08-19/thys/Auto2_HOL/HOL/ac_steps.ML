(*
  File: ac_steps.ML
  Author: Bohua Zhan

  Proof steps related to associative-commutative operations.
*)

signature AC_PROOFSTEPS =
sig
  val max_ac: int Config.T
  val simp_ac_expr: Proof.context -> ac_info -> box_id * cterm -> (box_id * thm) list
  val get_ac_head_equiv:
      Proof.context -> ac_info -> box_id * cterm -> (box_id * thm) list
  val ac_expand_once:
      Proof.context -> ac_info -> box_id * cterm -> (box_id * thm) list
  val ac_expand:
      Proof.context -> ac_info -> box_id * cterm -> (box_id * thm) list
  val ac_expand_equiv: proofstep
  val ac_expand_unit: proofstep

  val add_ac_proofsteps: theory -> theory
end;

structure AC_ProofSteps : AC_PROOFSTEPS =
struct

val max_ac = Attrib.setup_config_int @{binding "max_ac"} (K 20)

fun rewrite_on_eqs ac_info eqs ct =
    let
      val t = Thm.term_of ct
    in
      if ACUtil.head_agrees ac_info t then
        Conv.binop_conv (rewrite_on_eqs ac_info eqs) ct
      else
        case find_first (fn eq => t aconv (Util.lhs_of eq)) eqs of
            NONE => Conv.all_conv ct
          | SOME eq_th => eq_th
    end

fun dest_ac_full ac_info ct =
    if ACUtil.head_agrees ac_info (Thm.term_of ct) then
      let
        val (a1, a2) = Util.dest_binop_cargs ct
        val sort_opt = if ACUtil.has_comm_th ac_info then
                         sort (Term_Ord.term_ord o apply2 Thm.term_of) else I
      in
        sort_opt (dest_ac_full ac_info a1 @ dest_ac_full ac_info a2)
      end
    else if ACUtil.eq_unit ac_info (Thm.term_of ct) then []
    else [ct]

(* Simplify each term of the AC expression. *)
fun simp_ac_expr ctxt ac_info (id, cu) =
    let
      val cus = dest_ac_full ac_info cu
    in
      if null cus then [(id, Thm.reflexive cu)] else
      cus |> map (RewriteTable.simplify_info ctxt)
          |> BoxID.get_all_merges_info ctxt
          |> BoxID.merge_box_with_info ctxt id
          |> map (fn (id', eqs) => (id', rewrite_on_eqs ac_info eqs cu))
    end

(* Obtain head equivalences of cu, where each term is simplified. *)
fun get_ac_head_equiv ctxt ac_info (id, cu) =
    let
      fun process_head_equiv (id', eq_th) =
          let
            val infos = simp_ac_expr ctxt ac_info (id', Thm.rhs_of eq_th)
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
fun ac_expand_once ctxt ac_info (id, ct) =
    let
      val cus = dest_ac_full ac_info ct
      fun get_equiv cu = get_ac_head_equiv ctxt ac_info (id, cu)

      fun process_info (id', eq) =
          (id', rewrite_on_eqs ac_info [eq] ct)
    in
      map process_info (maps get_equiv cus)
    end

(* Find all ways to write ct, up to a certain limit. *)
fun ac_expand ctxt ac_info (id, ct) =
    let
      val max_ac = Config.get ctxt max_ac

      fun ac_equiv_eq_better (id, th) (id', th') =
          let
            val seq1 = dest_ac_full ac_info (Thm.rhs_of th)
            val seq2 = dest_ac_full ac_info (Thm.rhs_of th')
          in
            Util.is_subseq (op aconv o apply2 Thm.term_of) (seq1, seq2) andalso
            BoxID.is_eq_ancestor ctxt id id'
          end

      fun has_ac_equiv_eq_better infos info' =
          exists (fn info => ac_equiv_eq_better info info') infos

      fun helper (old, new) =
          case new of
              [] => old
            | (id', eq_th) :: rest =>
              if length old + length new > max_ac then
                old @ take (max_ac - length old) new
              else let
                val old' = ((id', eq_th) :: old)
                val rhs_expand =
                    (ac_expand_once ctxt ac_info (id', Thm.rhs_of eq_th))
                        |> Util.max_partial ac_equiv_eq_better
                        |> map (BoxID.merge_eq_infos ctxt (id', eq_th))
                        |> filter_out (has_ac_equiv_eq_better (old' @ rest))
              in
                helper (old', rest @ rhs_expand)
              end

      (* Start term *)
      val start = simp_ac_expr ctxt ac_info (id, ct)
    in
      helper ([], start)
    end

fun ac_expand_equiv_fn ctxt item1 item2 =
    let
      val thy = Proof_Context.theory_of ctxt
      val {id = id1, tname = tname1, ...} = item1
      val {id = id2, tname = tname2, ...} = item2
      val (ct1, ct2) = (the_single tname1, the_single tname2)
      val (t1, t2) = (Thm.term_of ct1, Thm.term_of ct2)
      val id = BoxID.merge_boxes ctxt (id1, id2)
    in
      case ACUtil.get_head_ac_info thy t1 of
          NONE => []
        | SOME ac_info =>
          if not (ACUtil.head_agrees ac_info t2) then []
          else if Term_Ord.term_ord (t2, t1) = LESS then []
          else if RewriteTable.is_equiv id ctxt (ct1, ct2) then []
          else let
            val expand1 = ac_expand ctxt ac_info (id, ct1)
            val expand2 = ac_expand ctxt ac_info (id, ct2)

            fun get_equiv ((id1, eq_th1), (id2, eq_th2)) =
                let
                  val ct1 = Thm.rhs_of eq_th1
                  val ct2 = Thm.rhs_of eq_th2
                  val ts1 = dest_ac_full ac_info ct1
                  val ts2 = dest_ac_full ac_info ct2
                in
                  if eq_list (op aconv o apply2 Thm.term_of) (ts1, ts2) then
                    let
                      val eq_th1' = ACUtil.normalize_all_ac ac_info ct1
                      val eq_th2' = ACUtil.normalize_all_ac ac_info ct2
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

val ac_expand_equiv =
    {name = "ac_expand_equiv",
     args = [TypedUniv TY_TERM, TypedUniv TY_TERM],
     func = TwoStep ac_expand_equiv_fn}

fun ac_expand_unit_fn ctxt item =
    let
      val thy = Proof_Context.theory_of ctxt
      val {id, tname, ...} = item
      val ct = the_single tname
      val t = Thm.term_of ct
    in
      case ACUtil.get_head_ac_info thy t of
          NONE => []
        | SOME ac_info =>
          let
            val expand = ac_expand ctxt ac_info (id, ct)

            fun process_expand (id', eq_th) =
                let
                  val ct = Thm.rhs_of eq_th
                  val ts = dest_ac_full ac_info ct
                in
                  if length ts <= 1 then
                    let
                      val eq' = ACUtil.normalize_all_ac ac_info ct
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

val ac_expand_unit =
    {name = "ac_expand_unit",
     args = [TypedUniv TY_TERM],
     func = OneStep ac_expand_unit_fn}

val add_ac_proofsteps =
    fold add_prfstep [
      ac_expand_equiv, ac_expand_unit
   ]

end  (* structure AC_ProofSteps. *)

val _ = Theory.setup AC_ProofSteps.add_ac_proofsteps
