(* This file provides a mechanism to derive functions that are necessary to generate tactics 
 * at run-time in the PSL framework.
 * Essentially, the functor, "mk_Dynamic_Tactic_Generator", abstracts functions that are commonly 
 * observed when dynamically generating tactics, thus avoiding code-duplication. *)
theory Dynamic_Tactic_Generation
imports Dynamic_Utils
begin

ML{* signature DYNAMIC_TACTIC_GENERATOR_SEED =
sig
  type modifier;
  type modifiers = modifier list;
  val  get_all_modifiers : Proof.state -> modifiers;
  (* mods_to_string should reorder parameters and remove duplicated modifier declarations.*)
  val  mods_to_string    : modifiers -> string;
end;
*}

ML{* signature DYNAMIC_TACTIC_GENERATOR =
sig
  include DYNAMIC_TACTIC_GENERATOR_SEED;
  val meth_name_n_modifiers_to_nontac_on_state: string -> modifiers -> Proof.state -> Proof.state Seq.seq;
  val meth_name_n_modifiers_to_logtac_on_state: string -> modifiers -> Proof.state ->
    (Dynamic_Utils.log * Proof.state) Seq.seq;
  val meth_name_n_modifiers_to_stttac_on_state: string -> modifiers -> Proof.state ->
    Dynamic_Utils.log -> (Dynamic_Utils.log * Proof.state) Seq.seq;
end;
*}

ML{* functor mk_Dynamic_Tactic_Generator (Seed:DYNAMIC_TACTIC_GENERATOR_SEED) : DYNAMIC_TACTIC_GENERATOR =
struct
  open Seed;
  structure DG = Dynamic_Utils;

  fun general_case (meth_name:string) (mods:modifiers) =
    let
      val attributes_name   = mods_to_string mods: string;
      val method_str_w_attr = meth_name ^ attributes_name;

      val nontac_on_state  = DG.string_to_nontac_on_pstate method_str_w_attr
        |> Tactic.TIMEOUT_in 0.3: Proof.state DG.nontac
        handle THM _ => K Seq.empty;
      val trace_node       = {using = [], methN = method_str_w_attr, back = 0};
      val logtac_on_state  = DG.nontac_to_logtac trace_node nontac_on_state : Proof.state DG.logtac;
      val stttac_on_state  = DG.logtac_to_stttac logtac_on_state;
    in
      (nontac_on_state, logtac_on_state, stttac_on_state)
    end;

  val meth_name_n_modifiers_to_nontac_on_state = #1 oo general_case;
  val meth_name_n_modifiers_to_logtac_on_state = #2 oo general_case;
  val meth_name_n_modifiers_to_stttac_on_state = #3 oo general_case;
end;
*}

ML{* signature DYNAMIC_TACTIC =
sig
  val get_state_stttacs  : Proof.state -> Proof.state Dynamic_Utils.stttac Seq.seq;
end;
*}

ML{* signature DIAGNOSTIC_TACTIC =
sig
  val nontac : Proof.state -> Proof.state Seq.seq;
end;
*}

end