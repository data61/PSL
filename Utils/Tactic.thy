(* This file provides utility functions that are useful to write tactics in Isabelle/HOL. *)
theory Tactic
imports Utils
begin

ML{* signature TACTIC =
sig
  val TIMEOUT_in               : real -> ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq;
  val TIMEOUT                  : ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq;
  val is_solved                : Proof.state -> Proof.state Seq.seq;
  val same_except_for_fst_prem : thm -> thm -> bool;
  val defer                    : thm -> thm Seq.seq;
end;
*}

ML{* structure Tactic : TACTIC =
struct

local
(* copy from Tactical.ML, but the types are more general.*)
fun SINGLE tacf = Option.map fst o Seq.pull o tacf;

(* DETERM_TIMEOUT was written by Jasmin Blanchette in nitpick_util.ML.
 * This version has exception handling on top of his version.*)
fun DETERM_TIMEOUT delay tac st =
  Seq.of_list (the_list (TimeLimit.timeLimit delay (fn () => SINGLE tac st) () 
   handle TimeLimit.TimeOut => NONE));
in

fun TIMEOUT_in real tac = DETERM_TIMEOUT (seconds real) tac;

fun TIMEOUT tac         = DETERM_TIMEOUT (seconds 0.3) tac;

end;

fun is_solved (state:Proof.state) =
  let
    val goal       = state |> Proof.goal |> #goal : thm;
    val is_solved' = Thm.nprems_of goal = 0 : bool;
    val result     = if is_solved' then Seq.single state else Seq.empty
  in
    result : Proof.state Seq.seq
  end;

(* same_except_for_fst_prem *)
(* Check if two thms are the same except for the first premise of the second.*)
fun same_except_for_fst_prem (goal1:thm) (goal2:thm) =
let
  (* This is ugly. Rewrite this. *)
  (* goal1 should have one less premise.*)
  val concl1                            = Thm.concl_of goal1 : term ;
  val concl2                            = Thm.concl_of goal2 : term ;
  val eq_concl                          = Term.aconv (concl1, concl2);
  val prems1                            = Thm.prems_of goal1 : term list;
  val prems2                            = Thm.prems_of goal2 : term list ;
  val goal1_has_a_prem                  = List.null prems1 : bool ;
  fun prems1_prems2tl prems1 prems2     = prems1 ~~ List.tl prems2;
  fun prems1_equiv_prems2 prems1 prems2 = List.all (Term.aconv) (prems1_prems2tl prems1 prems2);
  fun test prems1 prems2                = eq_concl andalso prems1_equiv_prems2 prems1 prems2;
in
  if goal1_has_a_prem then test prems1 prems2 else true
end;

val defer = defer_tac 1;

end;
*}

end