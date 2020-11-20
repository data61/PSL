section \<open>Subgoal Structure for Apply Scripts\<close>
theory Structured_Apply
imports Main
keywords 
  "focus" "solved" "applyS" "apply1" "applyF" "applyT" :: prf_script
begin

text \<open>This theory provides some variants of the apply command 
  that make the proof structure explicit. See below for examples.

  Compared to the @{command subgoal}-command, these set of commands is more lightweight,
  and fully supports schematic variables.
\<close>

(*
  focus, focus <method text>, applyF <method text>
    Focus on current subgoal, and then (optionally) apply method. applyF m is a synonym for focus m.

  solved
    Assert that subgoal is solved and release focus.

  applyT <method text>
    Apply method to current subgoal only. Same as apply m [].

  applyS <method text>
    Apply method to current subgoal, and assert that subgoal is solved.
    "applyS m" is roughly equal to "focus m solved"

  apply1 <method text>
    Apply method to current subgoal, and assert that there is exactly one resulting subgoal.

*)

ML \<open>
signature STRUCTURED_APPLY = sig
  val focus: Proof.state -> Proof.state
  val solved: Proof.state -> Proof.state
  val unfocus: Proof.state -> Proof.state

  val apply1: Method.text_range -> Proof.state -> Proof.state Seq.result Seq.seq
  val applyT: Method.text * Position.range -> Proof.state -> Proof.state Seq.result Seq.seq
  val apply_focus: Method.text_range -> Proof.state -> Proof.state Seq.result Seq.seq
  val apply_solve: Method.text_range -> Proof.state -> Proof.state Seq.result Seq.seq
end

structure Structured_Apply: STRUCTURED_APPLY = struct
  val focus = Proof.refine_primitive (K (Goal.restrict 1 1))
  val unfocus = Proof.refine_primitive (K (Goal.unrestrict 1))
  val solved = Proof.refine_primitive (fn _ => fn thm => let
      val _ = if Thm.nprems_of thm > 0 then error "Subgoal not solved" else ()
    in
      Goal.unrestrict 1 thm
    end
  )

  fun apply_focus m = focus #> Proof.apply m

  fun assert_num_solved d msg m s = let
    val n_subgoals = Proof.raw_goal #> #goal #> Thm.nprems_of
    val n1 = n_subgoals s

    fun do_assert s = if n1 - n_subgoals s <> d then error msg else s
  in
    s 
    |> Proof.apply m
    |> Seq.map_result do_assert
  end

  fun apply_solve m = 
      focus 
    #> assert_num_solved 1 "Subgoal not solved" m
    #> Seq.map_result unfocus

  fun apply1 m = 
      focus 
    #> assert_num_solved 0 "Method must not produce or solve subgoals" m 
    #> Seq.map_result unfocus

  fun applyT (m,pos) = let
    open Method
    val m = Combinator (no_combinator_info, Select_Goals 1, [m])
  in
    Proof.apply (m,pos)
  end  


end

val _ =
  Outer_Syntax.command @{command_keyword solved} "Primitive unfocus after subgoal is solved"
    (Scan.succeed ( Toplevel.proof (Structured_Apply.solved) ));

val _ =
  Outer_Syntax.command @{command_keyword focus} "Primitive focus then optionally apply method"
    (Scan.option Method.parse >> (fn 
        NONE => Toplevel.proof (Structured_Apply.focus)
      | SOME m => (Method.report m; Toplevel.proofs (Structured_Apply.apply_focus m))
    ));

val _ =
  Outer_Syntax.command @{command_keyword applyF} "Primitive focus then apply method"
    (Method.parse >> (fn m => (Method.report m; 
      Toplevel.proofs (Structured_Apply.apply_focus m)
    )));

val _ =
  Outer_Syntax.command @{command_keyword applyS} "Apply method that solves exactly one subgoal"
    (Method.parse >> (fn m => (Method.report m; 
      Toplevel.proofs (Structured_Apply.apply_solve m) 
    )));

val _ =
  Outer_Syntax.command @{command_keyword apply1} "Apply method that does not change number of subgoals"
    (Method.parse >> (fn m => (Method.report m; 
      Toplevel.proofs (Structured_Apply.apply1 m) 
    )));

val _ =
  Outer_Syntax.command @{command_keyword applyT} "Apply method on first subgoal"
    (Method.parse >> (fn m => (Method.report m; 
      Toplevel.proofs (Structured_Apply.applyT m) 
    )));

\<close>


end
