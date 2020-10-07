theory SM_LTL
imports LTL.LTL SM_Semantics
begin

  definition test_aprop :: "exp \<Rightarrow> valuation \<Rightarrow> bool"
    where "test_aprop e s \<equiv> case eval_exp e (\<lparr> local_state.variables = Map.empty \<rparr>,
      \<lparr> global_state.variables = s \<rparr>) of None \<Rightarrow> False | Some v \<Rightarrow> bool_of_val v"

  definition sm_props :: "valuation \<Rightarrow> exp set"
    where "sm_props s \<equiv> {e. test_aprop e s}"

  definition ap_accept :: "program \<Rightarrow> (nat \<Rightarrow> exp set) \<Rightarrow> bool"
    where "ap_accept prog w \<equiv> \<exists> w'. ref_accept prog w' \<and> w = sm_props \<circ> global_state.variables \<circ> w'"
  (* TODO: Can we get rid of the 
    distribution of global_state.variables here, 
    and global_config.state in the SM_Semantics reference point? *)
  (* TODO: also think about separating types for global/local/undecided stuff, or at least
    factor this part out of the various types of expressions, cmds, actions, etc. *)

end

