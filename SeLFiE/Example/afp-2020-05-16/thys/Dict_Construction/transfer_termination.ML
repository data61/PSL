signature TRANSFER_TERMINATION = sig
  val termination_tac: Function.info -> Function.info -> Proof.context -> int -> tactic
end

structure Transfer_Termination : TRANSFER_TERMINATION = struct

open Dict_Construction_Util

fun termination_tac ({R = new_R, ...}: Function.info) (old_info: Function.info) ctxt =
  let
    fun fallback_tac warn _ =
      (if warn then warning "Falling back to another termination proof" else ();
        Seq.empty)

    (*copied from BNF_Comp, in turn copied from Envir.expand_term_free*)
    fun expand_term_const defs =
      let
        val eqs = map ((fn ((x, U), u) => (x, (U, u))) o apfst dest_Const) defs;
        val get = fn Const (x, _) => AList.lookup (op =) eqs x | _ => NONE;
      in Envir.expand_term get end

    fun map_comp_bnf typ =
      let
        (* we start from a fresh lthy to avoid local hyps interfering with BNF *)
        val lthy =
          Proof_Context.theory_of ctxt
          |> Named_Target.theory_init
          |> Config.put BNF_Comp.typedef_threshold ~1
        (* we just pretend that they're all live here *)
        val live_As = all_tfrees typ
        fun flatten_tyargs Ass =
          live_As
          |> filter (fn T => exists (fn Ts => member (op =) Ts T) Ass)
        (* Dont_Inline would create new definitions, always *)
        val ((bnf, _), ((_, {map_unfolds, ...}), _)) =
          BNF_Comp.bnf_of_typ false BNF_Def.Do_Inline I flatten_tyargs live_As [] typ
            ((BNF_Comp.empty_comp_cache, BNF_Comp.empty_unfolds), lthy)
        val subst = map (Logic.dest_equals o Thm.prop_of) map_unfolds
        val t = BNF_Def.map_of_bnf bnf
      in
        (live_As, expand_term_const subst t)
      end

      val tac = case old_info of
        {R = old_R, totality = SOME totality, ...} =>
          let
            fun get_eq R =
              Inductive.the_inductive ctxt R
              |> snd |> #eqs
              |> the_single
              |> Local_Defs.abs_def_rule ctxt
            val (old_R_eq, new_R_eq) = apply2 get_eq (old_R, new_R)

            fun get_typ R =
              fastype_of R
              |> strip_type
              |> fst |> hd
              |> Type.legacy_freeze_type
            val (old_R_typ, new_R_typ) = apply2 get_typ (old_R, new_R)

            (* simple strategy: old_R and new_R are identical *)
            val simple_tac =
              let
                val totality' = Local_Defs.unfold ctxt [old_R_eq] totality
              in
                Local_Defs.unfold_tac ctxt [new_R_eq] THEN
                  HEADGOAL (SOLVED' (resolve_tac ctxt [totality']))
              end

            (* smart strategy: new_R can be simulated by old_R *)
            (* FIXME this is trigger-happy *)
            val smart_tac = Exn.interruptible_capture (fn st =>
              let
                val old_R_stripped =
                  Thm.prop_of old_R_eq
                  |> Logic.dest_equals |> snd
                  |> map_types (K dummyT)
                  |> Syntax.check_term ctxt

                val futile =
                  old_R_stripped |> exists_type (exists_subtype
                    (fn TFree (_, sort) => sort <> @{sort type}
                      | TVar (_, sort) => sort <> @{sort type}
                      | _ => false))

                fun costrip_prodT new_t old_t =
                  if Type.could_match (old_t, new_t) then
                    (0, new_t)
                  else
                    case costrip_prodT (snd (HOLogic.dest_prodT new_t)) old_t of
                      (n, stripped_t) => (n + 1, stripped_t)

                fun construct_inner_proj new_t old_t =
                  let
                    val (diff, stripped_t) = costrip_prodT new_t old_t
                    val (tfrees, f_head) = map_comp_bnf stripped_t
                    val f_args = map (K (Abs ("x", dummyT, Const (@{const_name undefined}, dummyT)))) tfrees
                    fun add_snd 0 = list_comb (map_types (K dummyT) f_head, f_args)
                      | add_snd n = Const (@{const_name comp}, dummyT) $ add_snd (n - 1) $ Const (@{const_name snd}, dummyT)
                  in
                    add_snd diff
                  end

                fun construct_outer_proj new_t old_t = case (new_t, old_t) of
                  (Type (@{type_name sum}, new_ts), Type (@{type_name sum}, old_ts)) =>
                    let
                      val ps = map2 construct_outer_proj new_ts old_ts
                    in list_comb (Const (@{const_name map_sum}, dummyT), ps) end
                | _ => construct_inner_proj new_t old_t

                val outer_proj = construct_outer_proj new_R_typ old_R_typ

                val old_R_typ_imported =
                  yield_singleton Variable.importT_terms old_R ctxt
                  |> fst |> get_typ

                val c =
                  outer_proj
                  |> Type.constraint (new_R_typ --> old_R_typ_imported)
                  |> Syntax.check_term ctxt
                  |> Thm.cterm_of ctxt

                val wf_simulate =
                  Drule.infer_instantiate ctxt [(("g", 0), c)] @{thm wf_simulate_simple}

                val old_wf = (@{thm wfP_implies_wf_set_of} OF [@{thm accp_wfPI} OF [totality]])

                val inner_tac =
                  match_tac ctxt @{thms wf_implies_dom} THEN'
                    match_tac ctxt [wf_simulate] CONTINUE_WITH_FW
                      [resolve_tac ctxt [old_wf],
                       match_tac ctxt @{thms set_ofI} THEN'
                         dmatch_tac ctxt @{thms set_ofD} THEN'
                         SELECT_GOAL (Local_Defs.unfold_tac ctxt [old_R_eq, new_R_eq]) THEN'
                         TRY'
                           (REPEAT_ALL_NEW (ematch_tac ctxt @{thms conjE exE}) THEN'
                             hyp_subst_tac_thin true ctxt THEN'
                             REPEAT_ALL_NEW (match_tac ctxt @{thms conjI exI}))]

                val unfold_tac =
                  Local_Defs.unfold_tac ctxt @{thms comp_apply id_apply prod.sel} THEN
                    auto_tac ctxt

                val tac = SOLVED (HEADGOAL inner_tac THEN unfold_tac)
              in
                if futile then
                  (warning "Termination relation has sort constraints; termination proof is unlikely to be automatic or may even be impossible";
                   Seq.empty)
                else
                  (tracing "Trying to re-use termination proof";
                   tac st)
              end)
            #> Exn.get_res
            #> the_default Seq.empty
          in
            simple_tac ORELSE smart_tac ORELSE fallback_tac true
          end
      | _ => fallback_tac false
  in SELECT_GOAL tac end

end