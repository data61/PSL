structure Transform_Tactic = struct
  fun my_print_tac msg st = (tracing msg; all_tac st)
  
  fun totality_resolve_tac totality0 def0 def1 ctxt =
    let
      val totality0_unfolded = totality0 |> Local_Defs.unfold ctxt [def0]
      val totality1 = totality0_unfolded |> Local_Defs.fold ctxt [def1]
    in
      if Thm.full_prop_of totality0_unfolded aconv Thm.full_prop_of totality1
        then
          let
            val msg = Pretty.string_of (Pretty.block [
              Pretty.str "Failed to transform totality from", Pretty.brk 1,
              Pretty.quote (Syntax.pretty_term ctxt (Thm.full_prop_of def0)), Pretty.brk 1,
              Pretty.str "to", Pretty.brk 1,
              Pretty.quote (Syntax.pretty_term ctxt (Thm.full_prop_of def1)), Pretty.brk 1])
          in (*print_tac ctxt msg THEN*) no_tac end
        else HEADGOAL (resolve_tac ctxt [totality1])
    end
  
  fun totality_blast_tac totality0 def0 def1 ctxt =
    HEADGOAL (
      (resolve_tac ctxt [totality0 RS @{thm rev_iffD1}])
      THEN' (resolve_tac ctxt [@{thm arg_cong[where f=HOL.All]}])
      THEN' SELECT_GOAL (unfold_tac ctxt (map (Local_Defs.abs_def_rule ctxt) [def0, def1]))
      THEN' (resolve_tac ctxt [@{thm arg_cong[where f=Wellfounded.accp]}])
      THEN' (Blast.depth_tac ctxt 2)
    )
  
  fun totality_replay_tac old_info new_info ctxt =
    let
      val totality0 = Transform_Misc.totality_of old_info
      val def0 = Transform_Misc.rel_of old_info ctxt
      val def1 = Transform_Misc.rel_of new_info ctxt
      fun my_print_tac msg st = (tracing msg; all_tac st)
    in
      no_tac
      ORELSE (totality_resolve_tac totality0 def0 def1 ctxt
        THEN my_print_tac "termination by replaying")
      ORELSE (totality_blast_tac totality0 def0 def1 ctxt
        THEN my_print_tac "termination by blast")
    end

  fun dp_intro_tac ctxt (cmd_info: Transform_Data.cmd_info) =
    let
      val scope_name = Binding.name_of (#scope cmd_info)
      val consistentDP_rule = Transform_Misc.locale_thms ctxt scope_name "consistentDP_intro"
    in
      resolve_tac ctxt consistentDP_rule
    end

  fun expand_relator_tac ctxt =
    SELECT_GOAL (Local_Defs.fold_tac ctxt (Transfer.get_relator_eq ctxt))

  fun solve_relator_tac ctxt =
    SOLVED' (Transfer.eq_tac ctxt)

  fun split_params_tac ctxt =
    clarify_tac ctxt

  fun dp_induct_tac ctxt (cmd_info: Transform_Data.cmd_info) =
    let
      val dpT' = cmd_info |> #dp_info |> the |> #new_head'
      val dpT'_info = Function.get_info ctxt dpT'
      val induct_rule = dpT'_info |> #inducts |> the
    in
      resolve_tac ctxt induct_rule
    end

  fun dp_unfold_def_tac ctxt (cmd_info: Transform_Data.cmd_info) sel =
    cmd_info |> #dp_info |> the |> sel
    |> map (Local_Defs.meta_rewrite_rule ctxt)
    |> Conv.rewrs_conv 
    |> Conv.try_conv
    |> Conv.binop_conv
    |> HOLogic.Trueprop_conv 
    |> Conv.concl_conv ~1
    |> (fn cv => Conv.params_conv ~1 (K cv) ctxt)
    |> CONVERSION
    (* |> EqSubst.eqsubst_tac ctxt [0] : may rewrite locale parameters in certain situations *)

  fun dp_match_rule_tac ctxt (cmd_info: Transform_Data.cmd_info) =
    let
      val scope_name = Binding.name_of (#scope cmd_info)
      val dp_match_rules = Transform_Misc.locale_thms ctxt scope_name "dp_match_rule"
    in
      resolve_tac ctxt dp_match_rules
    end

  fun checkmem_tac ctxt (cmd_info: Transform_Data.cmd_info) =
    let
      val scope_name = Binding.name_of (#scope cmd_info)
      val dp_match_rules = Transform_Misc.locale_thms ctxt scope_name "crel_vs_checkmem_tupled"
    in
      resolve_tac ctxt dp_match_rules
      THEN' SOLVED' (clarify_tac ctxt)
      THEN' Transfer.eq_tac ctxt
    end

  fun solve_IH_tac ctxt =
    Method.assm_tac ctxt

  fun transfer_raw_tac ctxt =
    resolve_tac ctxt (Transfer.get_transfer_raw ctxt)

  fun step_tac ctxt (cmd_info: Transform_Data.cmd_info) =
    solve_IH_tac ctxt
    ORELSE' solve_relator_tac ctxt
    ORELSE' dp_match_rule_tac ctxt cmd_info
    ORELSE' transfer_raw_tac ctxt

  fun prepare_case_tac ctxt (cmd_info: Transform_Data.cmd_info) =
    dp_unfold_def_tac ctxt cmd_info #new_def'
    THEN' checkmem_tac ctxt cmd_info
    THEN' dp_unfold_def_tac ctxt cmd_info #old_defs

  fun solve_case_tac ctxt (cmd_info: Transform_Data.cmd_info) =
    prepare_case_tac ctxt cmd_info
    THEN' REPEAT_ALL_NEW (step_tac ctxt cmd_info)

  fun prepare_consistentDP_tac ctxt (cmd_info: Transform_Data.cmd_info) =
    dp_intro_tac ctxt cmd_info
    THEN' expand_relator_tac ctxt
    THEN' split_params_tac ctxt
    THEN' dp_induct_tac ctxt cmd_info

  fun solve_consistentDP_tac ctxt (cmd_info: Transform_Data.cmd_info) =
    prepare_consistentDP_tac ctxt cmd_info
    THEN_ALL_NEW SOLVED' (solve_case_tac ctxt cmd_info)

  fun prepare_combinator_tac ctxt (cmd_info: Transform_Data.cmd_info) =
     EqSubst.eqsubst_tac ctxt [0] @{thms Rel_def[symmetric]}
     THEN' dp_unfold_def_tac ctxt cmd_info (single o #new_defT)
     THEN' REPEAT_ALL_NEW (resolve_tac ctxt (@{thm Rel_abs} :: Transform_Misc.locale_thms ctxt "local" "crel_vs_return_ext"))
     THEN' (SELECT_GOAL (unfold_tac ctxt @{thms Rel_def}))

   fun dp_unfold_defs_tac ctxt (cmd_info: Transform_Data.cmd_info) =
     dp_unfold_def_tac ctxt cmd_info #new_def'
     THEN' dp_unfold_def_tac ctxt cmd_info #old_defs

end
