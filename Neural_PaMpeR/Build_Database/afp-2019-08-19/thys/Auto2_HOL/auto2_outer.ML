(*
  File: auto2_outer.ML
  Author: Bohua Zhan

  Proof language for auto2.
*)

signature AUTO2_OUTER =
sig
  val auto2_solve: Proof.context -> cterm -> thm
  val init_state: Proof.state -> Proof.state
  val refine_subgoal_th: thm -> thm -> thm

  val have_resolve: Proof.context -> term list -> thm -> term -> thm
  val have_after_qed: Proof.context -> thm -> thm -> thm
  val have_cmd: bool * string * bool -> Proof.state -> Proof.state

  val subgoal_cmd: string -> Proof.state -> Proof.state
  val endgoal_cmd: Proof.state -> Proof.state

  val end_cmd: Proof.state -> Proof.state
  val qed_cmd: Proof.state -> Proof.context

  val obtain_resolve: Proof.context -> term list -> thm -> term -> thm
  val obtain_after_qed: Proof.context -> thm list -> thm -> thm
  val obtain_cmd: string list * string list * bool -> Proof.state -> Proof.state

  val case_resolve: Proof.context -> term list -> thm -> thm
  val case_after_qed: Proof.context -> thm list -> thm -> thm
  val case_cmd: string * bool -> Proof.state -> Proof.state

  val contra_resolve: Proof.context -> term list -> term list -> term -> thm
  val contra_after_qed: Proof.context -> thm -> thm
  val contra_cmd: Proof.state -> Proof.state

  val let_resolve: Proof.context -> term list -> term -> term list -> term -> thm
  val let_after_qed: Proof.context -> term list -> thm -> thm
  val let_cmd: string list -> Proof.state -> Proof.state
end;

structure Auto2_Outer : AUTO2_OUTER =
struct

(* Use auto2 to solve the given statement *)
fun auto2_solve ctxt stmt =
    let
      val goal = stmt |> Thm.trivial |> Goal.protect 1
    in
      (Auto2.auto2_tac ctxt goal)
          |> Seq.hd |> Goal.conclude
    end

(* Initiate auto2 state, using goal from the Isar state. *)
fun init_state state =
    let
      val {goal, context = ctxt, ...} = Proof.goal state
      val _ = assert (Auto2_State.get_num_frame ctxt = 0)
                     "init_state: state not empty."
      val subgoals = goal |> Thm.cprop_of |> Drule.strip_imp_prems
      val init_frame = Auto2_State.simple_frame (hd subgoals, NONE)
    in
      state |> Proof.map_contexts (Auto2_State.push_head init_frame)
    end

val _ =
    Outer_Syntax.command @{command_keyword "@proof"} "begin auto2 proof"
    (Scan.succeed (Toplevel.proof init_state))

(* Given th of the form A ==> B, and prop of the form B ==> C, return
   the theorem A ==> C. In effect, we modified (refined) the subgoal
   in prop from B to A using th.
 *)
fun refine_subgoal_th th prop =
    let
      val assum = hd (Drule.cprems_of th)  (* A *)
    in
      th |> Util.send_first_to_hyps  (* [A] ==> B *)
         |> Thm.implies_elim prop    (* [A] ==> C *)
         |> Thm.implies_intr assum   (* A ==> C *)
    end

(* Given theorem As ==> B, a term C, and a list of variables x, obtain
   the theorem (!!x. As ==> B ==> C) ==> (!!x. As ==> C).
 *)
fun have_resolve ctxt vars th concl =
    let
      val prop = Thm.prop_of th
      val (As, B) = Logic.strip_horn prop
      val cAs = map (Thm.cterm_of ctxt) As
      val c_vars = map (Thm.cterm_of ctxt) vars
      val stmt = (Util.list_meta_horn (vars, (As @ [B], concl)))
                     |> Thm.cterm_of ctxt

      val thAs = map Thm.assume cAs
      val th_bc =
          stmt |> Thm.assume  (* !!x. As ==> B ==> C *)
               |> fold Thm.forall_elim c_vars
               |> fold Thm.elim_implies thAs  (* B ==> C *)

      val th_b = th |> fold Thm.elim_implies thAs  (* B *)

      val th_c = Thm.implies_elim th_bc th_b  (* C *)
    in
      th_c |> fold Thm.implies_intr (rev cAs)
           |> fold Thm.forall_intr (rev c_vars)
           |> Thm.implies_intr stmt
    end

(* Given prop in the form (!!x. As ==> C) ==> D, and th in the form As
   ==> B, return the theorem (!!x. As ==> B ==> C) ==> D.

   In effect, this adds B as an extra assumption in the current
   subgoal.
 *)
fun have_after_qed ctxt th prop =
    let
      val (vars, (_, concl)) = prop |> Thm.prems_of |> the_single
                                    |> Util.strip_meta_horn
      val have_res = have_resolve ctxt vars th concl
    in
      refine_subgoal_th have_res prop
    end

(* Implementation of @have command. *)
fun have_cmd (is_rule, t, is_with) state =
    let
      val {context = ctxt, ...} = Proof.goal state

      (* Goal to be proved: !!x. As' ==> C *)
      val (vars, (assums, concl)) = t |> Syntax.read_term ctxt
                                      |> UtilLogic.strip_obj_horn

      (* Current subgoal *)
      val (_, (As, _)) = ctxt |> Auto2_State.get_subgoal
                              |> Util.strip_meta_horn

      (* Actual goal: strip vars, and add As as additional assumptions. *)
      val stmt = Logic.list_implies (As @ map mk_Trueprop assums,
                                     mk_Trueprop concl)

      (* Post-processing. We begin with th: As ==> As' ==> C, and want
         to create the theorem As ==> (!!x. As' ==> C), then use it to
         insert !!x. As' ==> C as an additional assumption.
       *)
      fun post_process th =
          th |> funpow (length As) Util.send_first_to_hyps
             (* [As] ==> As' ==> C *)
             |> fold Thm.forall_intr (rev (map (Thm.cterm_of ctxt) vars))
             (* [As] ==> !!x. As' ==> C *)
             |> apply_to_thm (UtilLogic.to_obj_conv ctxt)
             (* [As] ==> !x. As' --> C *)
             |> fold Thm.implies_intr (rev (map (Thm.cterm_of ctxt) As))

      fun after_qed ths prop =
          have_after_qed ctxt (post_process (the_single ths)) prop

      val add_prem_only =
          if is_rule then I
          else Auto2_State.add_prem_only
                   (UtilLogic.list_obj_horn (vars, (assums, concl)))

      val new_vars =
          filter_out (Variable.is_fixed ctxt o fst o Term.dest_Free) vars
    in
      if not is_with then
        let
          (* Run auto2 to obtain As ==> As' ==> C. *)
          val ctxt' = fold Util.declare_free_term new_vars ctxt
          val th = auto2_solve ctxt' (Thm.cterm_of ctxt' stmt)
        in
          state |> Proof.map_contexts (Auto2_State.map_head_th (after_qed [th]))
                |> Proof.map_contexts add_prem_only
        end
      else
        let
          val new_frame = Auto2_State.simple_frame (
                Thm.cterm_of ctxt stmt, SOME ([], after_qed))
        in
          (* The order here does not matter much. All three actions
             will be completed before proof begins.
           *)
          state |> Proof.map_contexts add_prem_only
                |> Proof.map_contexts (fold Util.declare_free_term new_vars)
                |> Proof.map_contexts (Auto2_State.push_head new_frame)
        end
    end

val read_rule =
    Scan.option (Parse.$$$ "(" --| @{keyword "@rule"} |-- Parse.$$$ ")")

val read_with =
    Scan.option @{keyword "@with"}

val _ =
    Outer_Syntax.command @{command_keyword "@have"} "intermediate goal"
    (read_rule -- Parse.term -- read_with >>
        (fn ((rule_opt, t), with_opt) =>
            Toplevel.proof
                (fn state =>
                    have_cmd (is_some rule_opt, t, is_some with_opt) state)))

(* Whether the goal is already resolved. *)
fun is_goal_resolved th =
    not (Util.is_head (Logic.protectC) (Thm.concl_of th))

(* Match pattern pat with t. Here pat is the pattern for selecting the
   i'th subgoal.
 *)
fun match_subgoal_pat thy t (i, pat) =
    let
      val inst = Pattern.first_order_match thy (pat, t) fo_init
      val vars = rev (map Var (Term.add_vars pat []))
      val ts = map (Util.subst_term_norm inst) vars
    in
      SOME (i, ts)
    end
    handle Pattern.MATCH => NONE

(* Implementation of the @subgoal command. *)
fun subgoal_cmd s state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val {goals, selected, ...} = Auto2_State.get_top_frame ctxt
      val _ = assert (selected = NONE) "@subgoal: already selected a subgoal."

      (* Figure out which subgoal to select by matching *)
      val thy = Proof_Context.theory_of ctxt
      val t = Syntax.read_term ctxt s
      val res = get_first (match_subgoal_pat thy t) (tag_list 0 (map fst goals))
    in
      case res of
          NONE => error "@subgoal: pattern not found"
        | SOME (i, ts) =>
          let
            val prop = snd (nth goals i)
            val _ = assert (not (is_goal_resolved prop))
                           "@subgoal: goal already resolved."

            (* Use the matched variables ts to name the forall variables. *)
            val t' = case Thm.prop_of prop of
                         imp $ A $ B => imp $ Util.rename_abs_term ts A $ B
                       | _ => raise Fail "subgoal_cmd"
            val prop = Thm.renamed_prop t' prop

            val new_ts =
                filter_out (Variable.is_fixed ctxt o fst o Term.dest_Free) ts
          in
            state |> Proof.map_contexts (Auto2_State.set_selected (SOME i))
                  |> Proof.map_contexts (Auto2_State.map_head_th (K prop))
                  |> Proof.map_contexts (fold Util.declare_free_term new_ts)
          end
    end

val _ =
    Outer_Syntax.command @{command_keyword "@subgoal"} "select subgoal"
    (Parse.term >>
       (fn s => Toplevel.proof (fn state => subgoal_cmd s state)))

(* Use auto2 to resolve one of the goals. *)
fun auto2_solve_goal ctxt prop =
    if is_goal_resolved prop then prop else
    let
      val (vars, (As, C)) =
          prop |> Thm.prems_of |> the_single |> Util.strip_meta_horn
      val body = Util.list_meta_horn ([], (As, C))
      val th = auto2_solve ctxt (Thm.cterm_of ctxt body)
    in
      th |> fold Thm.forall_intr (rev (map (Thm.cterm_of ctxt) vars))
         |> Thm.implies_elim prop
         |> Goal.conclude
    end

(* Implementation of the @endgoal command.

   There should be more than one goal in the current frame, and one of
   the goals is selected. Use auto2 to finish the selected goal.
 *)
fun endgoal_cmd state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val {goals, selected, ...} = Auto2_State.get_top_frame ctxt
      val _ = assert (length goals > 1 andalso is_some selected)
                     "@endgoal: called without a selection"
      val prop = snd (nth goals (the selected))
      val solved_prop = auto2_solve_goal ctxt prop
    in
      state |> Proof.map_contexts (Auto2_State.map_head_th (K solved_prop))
            |> Proof.map_contexts (Auto2_State.set_selected NONE)
    end

val _ =
    Outer_Syntax.command @{command_keyword "@endgoal"} "endgoal of with block"
    (Scan.succeed (
        Toplevel.proof (fn state => endgoal_cmd state)))

(* Implementation of the @end command.

   If there is exactly one goal in the current frame, that goal should
   be selected and unresolved. Use auto2 to resolve that goal. If
   there are multiple goals in the current frame, use auto2 to finish
   all unresolved goals.
 *)
fun end_cmd state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val {goals, selected, after_qed, ...} = Auto2_State.get_top_frame ctxt
      val _ = assert ((length goals = 1 andalso selected = SOME 0) orelse
                      (length goals > 1 andalso selected = NONE))
                     "@end: cannot call within an selection."
      val solved_props = map (auto2_solve_goal ctxt o snd) goals
      val _ = assert (forall is_goal_resolved solved_props)
                     "@end: failed to resolve all goals"

      (* List of new variables, and callback function. *)
      val (new_vars, f) = the after_qed
    in
      state |> Proof.map_contexts Auto2_State.pop_head
            |> Proof.map_contexts (Auto2_State.map_head_th (f solved_props))
            |> Proof.map_contexts (fold Util.declare_free_term new_vars)
    end

val _ =
    Outer_Syntax.command @{command_keyword "@end"} "end of with block"
    (Scan.succeed (
        Toplevel.proof (fn state => end_cmd state)))

(* Implementation of the @qed command. *)
fun qed_cmd state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val _ = assert (Auto2_State.get_num_frame ctxt = 1)
                     "Qed should be applied outside any 'with' blocks"

      val prop = Auto2_State.get_selected ctxt
      val (vars, (As, C)) = prop |> Thm.prems_of |> the_single
                                 |> Util.strip_meta_horn
      val body = Util.list_meta_horn ([], (As, C))

      val th = (auto2_solve ctxt (Thm.cterm_of ctxt body))
                   |> fold Thm.forall_intr (rev (map (Thm.cterm_of ctxt) vars))
      val new_prop = Thm.implies_elim prop th

      val method = K (Method.CONTEXT_TACTIC (PRIMITIVE (K new_prop)))
    in
      state |> Proof.map_contexts (Auto2_State.map_head_th (K new_prop))
            |> Proof.refine_singleton (Method.Basic (K method))
            |> Proof.global_done_proof
    end

val _ =
    Outer_Syntax.command @{command_keyword "@qed"} "end of proof"
    (Scan.succeed (
        Toplevel.end_proof (K qed_cmd)))

(* Given theorem As ==> EX y. P(y), a term C, and a list of variables
   x, obtain the theorem (!!x y. As ==> P(y) ==> C) ==> (!!x. As ==>
   C).
 *)
fun obtain_resolve ctxt vars th concl =
    let
      val prop = Thm.prop_of th

      (* B is EX y. P(y) *)
      val (As, B) = Logic.strip_horn prop
      val cAs = map (Thm.cterm_of ctxt) As
      val c_vars = map (Thm.cterm_of ctxt) vars

      val (new_vars, body) = UtilLogic.strip_exists (dest_Trueprop B)

      val As' = As @ [mk_Trueprop body]
      val stmt = (Util.list_meta_horn (vars @ new_vars, (As', concl)))
                     |> Thm.cterm_of ctxt

      val thAs = map Thm.assume cAs
      val th_b = th |> fold Thm.elim_implies thAs

      (* P(y) ==> C *)
      val th_bc = stmt |> Thm.assume
                       |> fold Thm.forall_elim c_vars
                       |> fold Thm.forall_elim (map (Thm.cterm_of ctxt) new_vars)
                       |> fold Thm.elim_implies thAs
      val th_c = (fold (UtilLogic.ex_elim ctxt) (rev new_vars) th_bc)
                     |> Thm.elim_implies th_b
    in
      th_c |> fold Thm.implies_intr (rev cAs)
           |> fold Thm.forall_intr (rev c_vars)
           |> Thm.implies_intr stmt
    end

(* Give prop in the form (!!x. As ==> C) ==> D, and th in the form As
   ==> EX y. P(y), return the theorem (!!x y. As ==> P(y) ==> C) ==>
   D.

   In effect, this creates new variables y with property P(y) in the
   current subgoal.
 *)
fun obtain_after_qed ctxt ths prop =
    let
      val th = the_single ths
      val (vars, (As, C)) = prop |> Thm.prems_of |> the_single
                                 |> Util.strip_meta_horn
      val body = Util.list_meta_horn ([], (As, C))

      val concl = Logic.strip_imp_concl body
      val obtain_res = obtain_resolve ctxt vars th concl
    in
      refine_subgoal_th obtain_res prop
    end

(* Implementation of @obtain command. *)
fun obtain_cmd (vars, conds, is_with) state =
    let
      val {context = ctxt, ...} = Proof.goal state

      (* First read list of variables and conditions *)
      val (vars, conds) = (Syntax.read_terms ctxt (vars @ conds))
                              |> chop (length vars)

      (* Elements of vars can be in the form x : A, process it into a
         variable x and a condition x : A.
       *)
      val (vars, conds) =
          (map (fn t => if is_mem t then dest_arg1 t else t) vars,
           filter is_mem vars @ conds)

      (* Goal: EX vars. conds *)
      val C = conds |> list_conj |> fold mk_exists (rev vars) |> mk_Trueprop

      (* Current subgoal *)
      val (_, (As, _)) = ctxt |> Auto2_State.get_subgoal
                              |> Util.strip_meta_horn

      (* Actual goal: As ==> EX vars. conds *)
      val stmt = Logic.list_implies (As, C)

      val new_vars =
          filter_out (Variable.is_fixed ctxt o fst o Term.dest_Free) vars

      val after_qed = obtain_after_qed ctxt
    in
      if not is_with then
        let
          (* Run auto2 to obtain As ==> EX vars. conds. *)
          val th = auto2_solve ctxt (Thm.cterm_of ctxt stmt)
        in
          state |> Proof.map_contexts (fold Util.declare_free_term new_vars)
                |> Proof.map_contexts (Auto2_State.map_head_th (after_qed [th]))
        end
      else
        let
          val new_frame = Auto2_State.simple_frame (
                Thm.cterm_of ctxt stmt, SOME (new_vars, after_qed))
        in
          state |> Proof.map_contexts (Auto2_State.push_head new_frame)
        end
    end

val obtain_param =
    Scan.repeat Parse.term --
    Scan.option (@{keyword "where"} |-- Scan.repeat Parse.term) --
    read_with

val _ =
  Outer_Syntax.command @{command_keyword "@obtain"} "obtain variables"
    (obtain_param >>
       (fn ((vars, conds), with_opt) =>
           Toplevel.proof (
             fn state =>
                obtain_cmd (vars, these conds, is_some with_opt) state)))

(* Given theorem As ==> B ==> C, and a list of variables x, obtain the
   theorem (!!x. As ==> ~B ==> C) ==> (!!x. As ==> C).
 *)
fun case_resolve ctxt vars th =
    let
      val prop = Thm.prop_of th

      val ((As, B), C) = prop |> Logic.strip_horn |> apfst split_last
      val cAs = map (Thm.cterm_of ctxt) As
      val c_vars = map (Thm.cterm_of ctxt) vars
      val nB = mk_Trueprop (Not $ (dest_Trueprop B))
      val stmt = (Util.list_meta_horn (vars, (As @ [nB], C)))
                     |> Thm.cterm_of ctxt

      val thAs = map Thm.assume cAs
      val th_nbc =
          stmt |> Thm.assume  (* !!x. As ==> ~B ==> C *)
               |> fold Thm.forall_elim c_vars
               |> fold Thm.elim_implies thAs  (* ~B ==> C *)

      val th_bc = th |> fold Thm.elim_implies thAs

      val inst = fo_init |> Util.update_env (("P",0), dest_Trueprop B)
                         |> Util.update_env (("Q",0), dest_Trueprop C)
      val th_c = (Util.subst_thm ctxt inst UtilBase.case_split_th)
                     |> fold Thm.elim_implies [th_bc, th_nbc]
    in
      th_c |> fold Thm.implies_intr (rev cAs)
           |> fold Thm.forall_intr (rev c_vars)
           |> Thm.implies_intr stmt
    end

(* Given prop in the form (!!x. As ==> C) ==> D, and th in the form As
   ==> B ==> C, return the theorem (!!x. As ==> ~B ==> C) ==> D.

   In effect, this adds ~B as extra assumption in the current subgoal.
 *)
fun case_after_qed ctxt ths prop =
    let
      val th = the_single ths
      val (vars, _) = prop |> Thm.prems_of |> the_single
                           |> Util.strip_meta_horn
      val case_res = case_resolve ctxt vars th
    in
      refine_subgoal_th case_res prop
    end

(* Implementation of @case command. *)
fun case_cmd (t, is_with) state =
    let
      val {context = ctxt, ...} = Proof.goal state

      val B = t |> Syntax.read_term ctxt |> mk_Trueprop

      val (_, (As, C)) = ctxt |> Auto2_State.get_subgoal
                              |> Util.strip_meta_horn

      val stmt = Logic.list_implies (As @ [B], C) |> Thm.cterm_of ctxt
      val after_qed = case_after_qed ctxt
    in
      if not is_with then
        let
          (* Run auto2 to obtain A_1 ==> ... ==> A_n ==> B ==> C *)
          val th = auto2_solve ctxt stmt
        in
          state |> Proof.map_contexts (Auto2_State.map_head_th (after_qed [th]))
        end
      else
        let
          val new_frame = Auto2_State.simple_frame (stmt, SOME ([], after_qed))
        in
          state |> Proof.map_contexts (Auto2_State.push_head new_frame)
        end
    end

val _ =
    Outer_Syntax.command @{command_keyword "@case"} "intermediate case"
    (Parse.term -- read_with >>
        (fn (t, with_opt) =>
            Toplevel.proof (fn state => case_cmd (t, is_some with_opt) state)))

(* Given a list of variables x, assumptions As, and term C, return the
   theorem (!!x. As ==> ~C ==> False) ==> (!!x. As ==> C).
 *)
fun contra_resolve ctxt vars As C =
    let
      val stmt = (Util.list_meta_horn (vars, (As @ [get_neg' C], pFalse)))
                     |> Thm.cterm_of ctxt
      val cAs = map (Thm.cterm_of ctxt) As
      val c_vars = map (Thm.cterm_of ctxt) vars

      val thAs = map Thm.assume cAs
      val th_c =
          stmt |> Thm.assume  (* !!x. A_1 ==> ... ==> A_n ==> ~C ==> False *)
               |> fold Thm.forall_elim c_vars
               |> fold Thm.elim_implies thAs  (* ~C ==> False *)
               |> apply_to_thm UtilLogic.rewrite_from_contra_form  (* C *)
    in
      th_c |> fold Thm.implies_intr (rev cAs)
           |> fold Thm.forall_intr (rev c_vars)
           |> Thm.implies_intr stmt
    end

(* Given prop in the form (!!x. As ==> C) ==> D, return the theorem
   (!!x. As ==> ~C ==> False) ==> D.
 *)
fun contra_after_qed ctxt prop =
    let
      val (vars, (As, C)) = prop |> Thm.prems_of |> the_single
                                 |> Util.strip_meta_horn
      val contra_res = contra_resolve ctxt vars As C
    in
      refine_subgoal_th contra_res prop
    end

(* Implementation of @contradiction command. *)
fun contra_cmd state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val after_qed = contra_after_qed ctxt
    in
      state |> Proof.map_contexts (Auto2_State.map_head_th after_qed)
    end

val _ =
    Outer_Syntax.command @{command_keyword "@contradiction"}
    "apply proof by contradiction"
    (Scan.succeed (
        Toplevel.proof (fn state => contra_cmd state)))

(* Given a list of variables x, an equation y = t, assumptions As, and
   a term C, return the theorem (!!x y. As ==> y = t ==> C) ==>
   (!!x. As ==> C).
 *)
fun let_resolve ctxt vars eq As C =
    let
      val thy = Proof_Context.theory_of ctxt

      (* Call obtain_resolve with th as A_i ==> EX y. y = t. *)
      val (lhs, rhs) = dest_eq eq
      val pat_a = case UtilBase.ex_vardef_th |> prop_of' |> dest_arg of
                      Abs (_, _, b) => dest_arg b
                    | _ => raise Fail "ex_vardef_th"
      val (x, _) = Term.dest_Free lhs
      val inst = Pattern.first_order_match thy (pat_a, rhs) fo_init
      val ex_th = Util.subst_thm ctxt inst UtilBase.ex_vardef_th
      val t' = case Thm.prop_of ex_th of
                   A $ (B $ Abs (_, T, body)) => A $ (B $ Abs (x, T, body))
                 | _ => error "let_resolve"
      val ex_th =
          ex_th |> Thm.renamed_prop t'
                |> fold Thm.implies_intr (rev (map (Thm.cterm_of ctxt) As))
    in
      obtain_resolve ctxt vars ex_th C
    end

(* Given prop in the form (!!x. As ==> C) ==> D, and an equation y =
   t, return the theorem (!!x y. As ==> y = t ==> C) ==> D.

   In effect, this creates a new variable y with property y = t in the
   current subgoal.
 *)
fun let_after_qed ctxt eqs prop =
    let
      fun fold_one eq prop =
          let
            val (vars, (As, C)) = prop |> Thm.prems_of |> the_single
                                       |> Util.strip_meta_horn
            val let_res = let_resolve ctxt vars eq As C
          in
            refine_subgoal_th let_res prop
          end
    in
      fold fold_one eqs prop
    end

(* Implementation of the @let command. *)
fun let_cmd eqs state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val eqs = Syntax.read_terms ctxt eqs
      val vars = map (fst o dest_eq) eqs
      val new_vars =
          filter_out (Variable.is_fixed ctxt o fst o Term.dest_Free) vars

      val after_qed = let_after_qed ctxt
    in
      state |> Proof.map_context (fold Util.declare_free_term new_vars)
            |> Proof.map_contexts (Auto2_State.map_head_th (after_qed eqs))
    end

val _ =
    Outer_Syntax.command @{command_keyword "@let"} "define a variable"
    (Scan.repeat Parse.term >>
        (fn eqs => Toplevel.proof (fn state => let_cmd eqs state)))

end  (* structure Auto2_Outer *)
