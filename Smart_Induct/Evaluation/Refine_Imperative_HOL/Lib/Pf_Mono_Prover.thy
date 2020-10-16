section \<open>Interfacing Partial-Function's Monotonicity Prover\<close>
theory Pf_Mono_Prover
imports Separation_Logic_Imperative_HOL.Sep_Main
begin
  (* TODO: Adjust mono-prover accordingly  *)
  (* Wraps mono-prover of partial-function to erase premises. 
    This is a workaround for mono_tac, which does not accept premises if the case-split rule is applied. *)

ML \<open>
  structure Pf_Mono_Prover = struct
    fun mono_tac ctxt = (REPEAT o eresolve_tac ctxt @{thms thin_rl})
      THEN' Partial_Function.mono_tac ctxt
  end
\<close>

method_setup pf_mono = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Pf_Mono_Prover.mono_tac ctxt))\<close> \<open>Monotonicity prover of the partial function package\<close>

end
