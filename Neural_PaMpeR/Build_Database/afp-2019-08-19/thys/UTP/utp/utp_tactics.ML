(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_tactics.ML                                                       *)
(* Authors: Simon Foster & Frank Zeyda (University of York, UK)               *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)
(* LAST REVIEWED: 3 Mar 2017 *)

(* Structure List_Util *)

structure List_Extra =
struct
  fun contains y = List.exists (fn x => x = y);
end;

(* Signature BASIC_TACTICS *)

signature BASIC_TACTICS =
sig
  val fast_transfer : Proof.context -> thm list -> context_tactic
  val interp_tac : Proof.context -> thm list -> context_tactic
  val slow_transfer : Proof.context -> thm list -> context_tactic
  val utp_auto_tac : Proof.context -> thm list -> context_tactic
  val utp_blast_tac : Proof.context -> thm list -> context_tactic
  val utp_simp_tac : Proof.context -> thm list -> context_tactic
end;

(* Structure Basic_Tactics *)

structure Basic_Tactics : BASIC_TACTICS =
struct
  local
    fun apply_method_noargs name ctxt =
      Method_Closure.apply_method ctxt name [] [] [] ctxt;
  in
    val slow_transfer = (apply_method_noargs @{method slow_uexpr_transfer});
    val fast_transfer = (apply_method_noargs @{method fast_uexpr_transfer});
    val interp_tac = (apply_method_noargs @{method uexpr_interp_tac});
    val utp_simp_tac = (apply_method_noargs @{method utp_simp_tac});
    val utp_auto_tac = (apply_method_noargs @{method utp_auto_tac});
    val utp_blast_tac = (apply_method_noargs @{method utp_blast_tac});
  end;
end;

(* Signature UTP_TACTICS *)

signature UTP_TACTICS =
sig
  type utp_tac_args;
  val robustN : string; val no_interpN : string;
  val scan_args : utp_tac_args parser
  val inst_gen_pred_tac : utp_tac_args ->
    (Proof.context -> thm list -> context_tactic) ->
    (Proof.context -> thm list -> context_tactic)
  val inst_gen_rel_tac : utp_tac_args ->
    (Proof.context -> thm list -> context_tactic) ->
    (Proof.context -> thm list -> context_tactic)
end;

(* Structure UTP_Methods *)

structure UTP_Tactics : UTP_TACTICS =
struct
  type utp_tac_args = {robust : bool, no_interp : bool};

  val robustN = "robust"; val no_interpN = "no_interp";

  local
  fun parse_args (args : string list) =
    {robust = (List_Extra.contains robustN args),
     no_interp = (List_Extra.contains no_interpN args)};
  in
  val scan_args =
    (Scan.repeat ((Args.$$$ robustN) || (Args.$$$ no_interpN))) >> parse_args;
  end;

  fun inst_gen_pred_tac (args : utp_tac_args) prove_tac ctxt =
    let
    val transfer_tac =
      (if #robust args
        then (Basic_Tactics.slow_transfer)
        else (Basic_Tactics.fast_transfer));
    val interp_tac =
      (if #no_interp args
        then (K Method.succeed)
        else (Basic_Tactics.interp_tac));
    in
      Method_Closure.apply_method ctxt @{method gen_pred_tac}
        [] [] [transfer_tac, interp_tac, prove_tac] ctxt
    end;

  fun inst_gen_rel_tac (args : utp_tac_args) prove_tac ctxt =
    let
    val transfer_tac =
      (if #robust args
        then (Basic_Tactics.slow_transfer)
        else (Basic_Tactics.fast_transfer));
    val interp_tac =
      (if #no_interp args
        then (K Method.succeed)
        else (Basic_Tactics.interp_tac));
    in
      Method_Closure.apply_method ctxt @{method gen_rel_tac}
        [] [] [transfer_tac, interp_tac, prove_tac] ctxt
    end;
end;