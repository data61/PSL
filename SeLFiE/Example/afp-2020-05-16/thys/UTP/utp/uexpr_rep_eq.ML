(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: uexpr_rep_eq.ML                                                      *)
(* Authors: Simon Foster & Frank Zeyda (University of York, UK)               *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)
(* LAST REVIEWED: 2 Mar 2017 *)

(* UEXPR_REP_EQ Signature *)

signature UEXPR_REP_EQ =
sig
  val get_uexpr_rep_eq_thms : theory -> thm list
  val read_uexpr_rep_eq_thms : theory -> theory
end;

(* uexpr_rep_eq Structure *)

structure uexpr_rep_eq : UEXPR_REP_EQ =
struct
  (* Theory Data to store the relevant transfer laws. *)

  structure UTP_Tactics_Data = Theory_Data (
    type T = thm list;
    val empty = [];
    val extend = I;
    val merge = Thm.merge_thms;
  );

  val get_uexpr_rep_eq_thms = UTP_Tactics_Data.get;
  val put_uexpr_rep_eq_thms = UTP_Tactics_Data.put;

  val uexpr_rep_eq_query =
  let val query_string = "name:\"rep_eq\" \"Rep_uexpr ?e = ?t\"" in
    Find_Theorems.read_query Position.none query_string
  end;

  fun read_uexpr_rep_eq_thms thy =
    let val ctxt = Proof_Context.init_global thy;
      val facts = Find_Theorems.find_theorems_cmd
        ctxt NONE NONE true uexpr_rep_eq_query;
    in
      (put_uexpr_rep_eq_thms (map snd (snd facts)) thy)
    end;
end;