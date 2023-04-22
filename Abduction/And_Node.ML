(*
 * And_Node.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)

(*** AND_NODE ***)
signature AND_NODE =
sig

(** andnode and functions on andnode **)
(* andnodes do not have corresponding constructs in resulting proof scripts. *)
type andnode;
type andnodes;

(* update of andnode *)
val update_proved_completely: andnode -> andnode;
val update_refuted          : andnode -> andnode;

end

(*** And_Node ***)
structure And_Node: AND_NODE =
struct

(** andnode and functions on andnode **)
(* andnode *)
type andnode =
{
 subgoals               : terms, (*Used to detect the order of sub-goals.*)
 proved_completely      : bool,
 refuted                : bool
};

(* andnodes *)
type andnodes = andnode list;

(** update of andnode **)
(* update_proved_completely_of_andnode *)
fun update_proved_completely (
{
  subgoals: terms,
  refuted: bool, ...
}: andnode) =
{
  subgoals          = subgoals,
  proved_completely = true,
  refuted           = refuted
}: andnode;

(* update_refuted_of_andnode *)
fun update_refuted (
{
  subgoals                  : terms,
  proved_completely: bool,...
}: andnode) =
{
  subgoals          = subgoals,
  proved_completely = proved_completely,
  refuted           = true
}: andnode;

end;