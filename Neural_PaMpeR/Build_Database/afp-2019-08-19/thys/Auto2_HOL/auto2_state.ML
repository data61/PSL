(*
  File: auto2_state.ML
  Author: Bohua Zhan

  Data structure containing auto2's state for the proof language.
*)

(* The state consists of a stack of frames. *)
type auto2_frame = {
  (* List of subgoals in the current frame. Each element is of the
     form (pat, th), where pat is the pattern used to select the
     subgoal, and th is the subgoal itself.
   *)
  goals: (term * thm) list,

  (* Index of the currently selected subgoal. *)
  selected: int option,

  (* Possible induction statement. *)
  induct_stmt: term option,

  (* List of forall statements that should only be matched to premises
     of theorems (not in disj_match_update).
   *)
  prem_only: term list,

  (* Callback after all subgoals are resolved. This is a pair (vars,
     f), where vars is a list of new variables, and f is the function
     that, given the list of solved subgoals as theorems, performs a
     modification on the current subgoal.
   *)
  after_qed: (term list * (thm list -> thm -> thm)) option
}

type auto2_state = auto2_frame list

signature AUTO2_STATE =
sig
  val print_state: Proof.context -> unit
  val get_num_frame: Proof.context -> int
  val pop_head: Proof.context -> Proof.context
  val push_head: auto2_frame -> Proof.context -> Proof.context
  val simple_frame:
      cterm * (term list * (thm list -> thm -> thm)) option -> auto2_frame
  val multiple_frame:
      (term * cterm) list * (term list * (thm list -> thm -> thm)) option ->
      auto2_frame
  val map_head_th: (thm -> thm) -> Proof.context -> Proof.context
  val set_selected: int option -> Proof.context -> Proof.context
  val set_induct_stmt: term -> Proof.context -> Proof.context
  val get_last_induct_stmt: Proof.context -> term option
  val add_prem_only: term -> Proof.context -> Proof.context
  val lookup_prem_only: Proof.context -> term -> bool
  val get_top_frame: Proof.context -> auto2_frame
  val get_selected: Proof.context -> thm
  val get_subgoal: Proof.context -> term
end;

structure Auto2_State : AUTO2_STATE =
struct

structure Data = Proof_Data
(
  type T = auto2_state
  fun init _ = []
)

(* Print the auto2 state. *)
fun string_of_frame ctxt frame =
    let
      val {goals, selected, ...} = frame
      val n = length goals
      fun print_i (i, (pat, th)) =
          (if selected = SOME i then "*" else " ") ^
          (pat |> Syntax.string_of_term ctxt) ^ ": " ^
          (th |> Thm.prop_of |> Syntax.string_of_term ctxt)
    in
      if n = 1 then
        goals |> the_single |> snd |> Thm.prop_of |> Syntax.string_of_term ctxt
      else cat_lines (map print_i (0 upto (n - 1) ~~ goals))
    end

fun string_of_state ctxt =
    let
      val frames = Data.get ctxt
      val _ = tracing ("Auto2 state. Number of frames is " ^
                       (string_of_int (length frames)))
    in
      cat_lines (map (string_of_frame ctxt) frames)
    end

fun print_state ctxt = tracing (string_of_state ctxt)

(* Number of frames in the current state. *)
fun get_num_frame ctxt = length (Data.get ctxt)

(* Remove the top-most frame of the state. *)
val pop_head =
    Data.map (fn frames => case frames of
                               [] => error "pop_head"
                             | _ :: rest => rest)

(* Push a head layer of auto2 state. *)
fun push_head frame =
    Data.map (cons frame)

(* Create a frame with a single goal, with statement ct. Note the
   resulting pair is (ct, ct ==> (ct)).
 *)
fun simple_frame (ct, after_qed) =
    {goals = [(Thm.term_of ct, Goal.protect 1 (Thm.trivial ct))],
     selected = SOME 0, induct_stmt = NONE, prem_only = [],
     after_qed = after_qed}

(* Create a frame with multiple goals. Here the input is a list of
   (pat, ct) pairs. The goals are (pat, ct ==> (ct)) pairs.
 *)
fun multiple_frame (goals, after_qed) =
    {goals = map (apsnd (Goal.protect 1 o Thm.trivial)) goals,
     selected = NONE, induct_stmt = NONE, prem_only = [], after_qed = after_qed}

(* Modify the top frame of the auto2 state. *)
fun map_head f =
    Data.map (fn frames => case frames of
                               [] => error "map_head"
                             | frame :: rest => f frame :: rest)

(* Modify the selected subgoal. *)
fun map_head_th f =
    map_head (
      fn {goals, selected, induct_stmt, prem_only, after_qed} =>
         case selected of
             NONE => raise Fail "map_frame_th: no proposition selected"
           | SOME i =>
             if i < 0 orelse i >= length goals then
               raise Fail "map_frame_th: unexpected selected"
             else
               {goals = nth_map i (apsnd f) goals,
                selected = selected, induct_stmt = induct_stmt,
                prem_only = prem_only, after_qed = after_qed})

(* Set selected subgoal. *)
fun set_selected sel =
    map_head (
      fn {goals, induct_stmt, prem_only, after_qed, ...} =>
         {goals = goals, selected = sel, induct_stmt = induct_stmt,
          prem_only = prem_only, after_qed = after_qed})

(* Set induction statement. *)
fun set_induct_stmt stmt =
    map_head (
      fn {goals, selected, prem_only, after_qed, ...} =>
         {goals = goals, selected = selected, induct_stmt = SOME stmt,
          prem_only = prem_only, after_qed = after_qed})

(* Return the last induction statement. *)
fun get_last_induct_stmt ctxt =
    let
      val frames = Data.get ctxt
    in
      get_first #induct_stmt (rev frames)
    end

(* Add a statement as matching with premise only. *)
fun add_prem_only stmt =
    map_head (
      fn {goals, selected, induct_stmt, prem_only, after_qed} =>
         {goals = goals, selected = selected, induct_stmt = induct_stmt,
          prem_only = stmt :: prem_only, after_qed = after_qed})

(* Check whether a statement is matching with premise only. *)
fun lookup_prem_only ctxt t =
    let
      val prem_only = maps #prem_only (Data.get ctxt)
    in
      member (op aconv) prem_only t
    end

(* Return the top frame of the state. *)
fun get_top_frame ctxt =
    case Data.get ctxt of
      [] => raise Fail "Auto2 proof should start with @begin keyword"
    | st :: _ => st

(* Return the goal theorem (of the form A ==> (C)). *)
fun get_selected ctxt =
    let
      val {goals, selected, ...} = get_top_frame ctxt
    in
      case selected of
          NONE => raise Fail "get_selected: no goal is selected."
        | SOME i => snd (nth goals i)
    end

(* Return the current subgoal. *)
fun get_subgoal ctxt =
    ctxt |> get_selected |> Thm.prems_of |> the_single
    handle List.Empty => error "get_subgoal: should have exactly one premise."

end  (* structure Auto2_State *)
