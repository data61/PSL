(* This file provides an interface of nitpick for PSL as an assertion tactic.             *)
(* This file does not include significant code duplication with the Isabelle source code. *)
theory Nitpick_as_Tactic
imports "../Runtime/Dynamic_Tactic_Generation"
begin

ML{* signature NITPICK2 =
sig
  val nitpick_tac: Proof.state Dynamic_Utils.logtac;
end;
*}

ML{* structure Nitpick2 =
struct
fun nitpick_tac (state:Proof.state) =
  let
    val single             = Seq.single ([], state);
    val thy:theory         = (Proof.theory_of state);
    val params             = Nitpick_Commands.default_params thy [];
    val nitpick_result     = Nitpick.pick_nits_in_subgoal state params Nitpick.Normal 1 1;
    (* "genuine" means "genuine counter-example", I guess. *)
    val nitpick_succeed    = fst nitpick_result = "genuine";
    val nitpick_tac_result = if nitpick_succeed then Seq.empty else single
  in
    nitpick_tac_result : ('a list * Proof.state) Seq.seq
  end;
end;
*}

ML{* structure Nitpick_Tactic : DIAGNOSTIC_TACTIC =
struct
fun nontac (state:Proof.state) =
  let
    val single             = Seq.single state;
    val thy:theory         = (Proof.theory_of state);
    val params             = Nitpick_Commands.default_params thy [];
    val nitpick_result     = Nitpick.pick_nits_in_subgoal state params Nitpick.Normal 1 1;
    (* "genuine" means "genuine counter-example", I guess. *)
    val nitpick_succeed    = fst nitpick_result = "genuine";
    val nitpick_tac_result = if nitpick_succeed then Seq.empty else single
  in
    nitpick_tac_result : Proof.state Seq.seq
  end;
end;
*}

end