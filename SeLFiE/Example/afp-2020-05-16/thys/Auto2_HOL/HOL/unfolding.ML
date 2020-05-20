(*
  File: unfolding.ML
  Author: Bohua Zhan

  Unfolding of functional definitions.
*)

signature UNFOLDING =
sig
  val get_unfold_thms_by_name: theory -> string -> thm list
  val get_unfold_thms: theory -> term -> thm list
  val unfold: theory -> conv
  val unfold_cmd: string -> Proof.state -> Proof.state
end;

structure Unfolding : UNFOLDING =
struct

fun get_unfold_thms_by_name thy nm =
    let
      val simp_nm = nm ^ ".simps"
      val def_nm = nm ^ "_def"
    in
      Global_Theory.get_thms thy simp_nm
      handle ERROR _ => Global_Theory.get_thms thy def_nm
                        handle ERROR _ => raise Fail "get_unfold_thms"
    end

fun get_unfold_thms thy t =
    get_unfold_thms_by_name thy (Util.get_head_name t)

(* Unfold the given term. *)
fun unfold thy ct =
    let
      val ths = get_unfold_thms thy (Thm.term_of ct)
    in
      Conv.first_conv (map rewr_obj_eq ths) ct
    end

fun unfold_cmd s state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt

      val (_, (As, _)) = ctxt |> Auto2_State.get_subgoal
                              |> Util.strip_meta_horn
      val cAs = map (Thm.cterm_of ctxt) As

      val t = Syntax.read_term ctxt s
      val eq_th = t |> Thm.cterm_of ctxt |> unfold thy
                    |> to_obj_eq
                    |> fold Thm.implies_intr (rev cAs)
      val _ = writeln ("Obtained " ^ (eq_th |> Thm.concl_of
                                            |> Syntax.string_of_term ctxt))

      val after_qed = Auto2_Outer.have_after_qed ctxt eq_th
    in
      state |> Proof.map_contexts (Auto2_State.map_head_th after_qed)
    end

val _ =
  Outer_Syntax.command @{command_keyword "@unfold"} "unfold a term"
    (Parse.term >>
        (fn s =>
            Toplevel.proof (fn state => unfold_cmd s state)))

end  (* structure Unfolding *)
