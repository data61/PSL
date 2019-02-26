(*  Title:      PSL/MiLkMaId_LiFtEr/Apply_MeLoId_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

local

type asf = Proof.state Seq.result Seq.seq;

val mk_single_results = Seq.make_results o Seq.single;

open Dynamic_Induct;
val sample_induct_args = [Ind "x", Arb "y"]: modifiers;

open LiFtEr;
infix And;

val sample_assert =
  All_Ind (Sub_Trm 1,
    Some_Sub_Trm_Occ (Sub_Trm_Occ 2,
        Trm_Occ_Is_Of_Trm (Sub_Trm_Occ 2, Sub_Trm 1)
      And
        Is_Atom (Sub_Trm_Occ 2))): assrt;

(*
val eval      : name_domains * abs_pstate_w_aux * assrt * ind_mods * Proof.context -> bool;
*)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>apply_MeLoId\<close> "initial goal refinement step (unstructured)"
    (Method.parse >> (fn m => (Method.report m; Toplevel.proofs mk_single_results)));

in end;