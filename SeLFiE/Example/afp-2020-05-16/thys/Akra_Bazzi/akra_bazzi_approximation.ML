(*  Title:      akra_bazzi_approximation.ML
    Author:     Manuel Eberl, TU Muenchen
*)

signature AKRA_BAZZI_APPROXIMATION =
sig
  val akra_bazzi_approximate_tac : int -> Proof.context -> int -> tactic
end

structure Akra_Bazzi_Approximation: AKRA_BAZZI_APPROXIMATION =
struct

val code_simp_tac = 
  Code_Simp.static_tac {consts = [@{const_name arith_consts}], ctxt = @{context}, simpset = NONE}

fun akra_bazzi_approximate_tac prec ctxt =
  let 
    val simps = @{thms eval_length eval_akra_bazzi_sum add_0_left add_0_right 
                       mult_1_left mult_1_right}
  in
    SELECT_GOAL (
      resolve_tac ctxt @{thms akra_bazzi_p_rel_intros} 1
      THEN ALLGOALS (fn i => 
        if i > 1 then 
          SELECT_GOAL (
            Local_Defs.unfold_tac ctxt 
              @{thms bex_set_simps ball_set_simps greaterThanLessThan_iff eval_length}
            THEN TRY (SOLVE (code_simp_tac ctxt 1))
          ) i
        else 
          SELECT_GOAL (Local_Defs.unfold_tac ctxt simps) i
          THEN Approximation.approximation_tac prec [] NONE ctxt i
      ) 
    )
  end
   
end;
