theory Concl_Pres_Clarification
imports Main
begin
  text \<open>Clarification and clarsimp that preserve the structure of 
    the subgoal's conclusion, i.e., neither solve it, nor swap it 
    with premises, as, eg, @{thm [source] notE} does.
    \<close>

  ML \<open>
    local 
      open Classical

      fun is_cp_brl (is_elim,thm) = let
        val prems = Thm.prems_of thm
        val nprems = length prems
        val concl = Thm.concl_of thm
      in
        (if is_elim then nprems=2 else nprems=1) andalso let
          val lprem_concl = hd (rev prems)
            |> Logic.strip_assums_concl
        in
          concl aconv lprem_concl
        end
      end

      val not_elim = @{thm notE}
      val hyp_subst_tacs = [Hypsubst.hyp_subst_tac]

      fun eq_contr_tac ctxt i = ematch_tac ctxt [not_elim] i THEN eq_assume_tac i;
      fun eq_assume_contr_tac ctxt = eq_assume_tac ORELSE' eq_contr_tac ctxt;

      fun cp_bimatch_from_nets_tac ctxt =
        biresolution_from_nets_tac ctxt (order_list o filter (is_cp_brl o snd)) true;


    in
      fun cp_clarify_step_tac ctxt =
        let val {safep_netpair, ...} = (rep_cs o claset_of) ctxt in
          appSWrappers ctxt
           (FIRST'
             [eq_assume_contr_tac ctxt,
              FIRST' (map (fn tac => tac ctxt) hyp_subst_tacs),
              cp_bimatch_from_nets_tac ctxt safep_netpair
              ])
        end;
      
        fun cp_clarify_tac ctxt = SELECT_GOAL (REPEAT_DETERM (cp_clarify_step_tac ctxt 1));

        fun cp_clarsimp_tac ctxt =
          Simplifier.safe_asm_full_simp_tac ctxt THEN_ALL_NEW
          cp_clarify_tac (addSss ctxt);


    end


  \<close>

  method_setup cp_clarify = \<open>
    (Classical.cla_method' (CHANGED_PROP oo cp_clarify_tac))
    \<close>

  method_setup cp_clarsimp = \<open>let
    fun clasimp_method' tac =
      Method.sections clasimp_modifiers >> K (SIMPLE_METHOD' o tac);
  in
    clasimp_method' (CHANGED_PROP oo cp_clarsimp_tac)
  end\<close>



end
