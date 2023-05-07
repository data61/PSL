(*
 * Or_Node.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)

(*** OR_NODE ***)
signature OR_NODE =
sig

(** ornode and functions on ornode **)
type ornode;
type ornodes;

(* query on ornode *)
val is_refuted          : ornode -> bool;
val is_worth_proving    : Proof.context -> ornode -> bool;

(* creation of ornode *)
type is_final_goal = bool;
val mk_ornode: is_final_goal -> term -> ornode;

(* update of ornode *)
val update_gg_parent_not_finished: ornode -> bool -> ornode;
val update_proved_completely     : ornode -> ornode;
val update_proof_n_proof_id      : string -> ornode -> ornode;
val update_refuted               : ornode -> ornode;
val update_branch                : ornode -> ornode;

end;

(*** Or_Node ***)
structure Or_Node: OR_NODE =
struct

(** ornode and functions on ornode **)
(* ornode and ornodes *)
type ornode = {
  final_goal                      : bool,
  branch                          : bool,
  lemma_name                      : string,
  lemma_term                      : term,(*For now we ignore "assumes" and "using".*)
  proof                           : string option,(*Proof script to finish proving this node.*)
  proof_id                        : int option,(*To track dependency. based on the timing proved with or w/o assuming conjectures.*)
  refuted                         : bool,
  proved_completely               : bool, (*= proved w/o assuming conjectures.*)
  (* If an or-node has a great grandparent that is not proved or refuted and this node is not
   * proved_completely, this node still needs a proof.*)
  gg_parent_not_finished          : bool
};

type ornodes = ornode list;
              
(** query on ornode **)

(* is_refuted *)
fun is_refuted ({refuted,...}:ornode) = refuted: bool;

(* is_worth_proving *)
fun is_worth_proving (ctxt:Proof.context) (ornode:ornode) =
((*
 tracing "@@ In is_worth_proving";
 tracing ("  " ^ Isabelle_Utils.trm_to_string ctxt (#lemma_term ornode));
 if is_none (#proof ornode) then tracing "  TRUE: has no proof" else tracing "  has a proof";
 if #gg_parent_not_finished ornode then tracing "  TRUE: gg_parent_not_finished" else tracing "  gg_parent_finished";
 if not (#refuted ornode) then tracing "  TRUE: not refuted" else tracing "  refuted";
 *)

    (*TODO: I don't think type checking should happen here. But much earlier.*)
    is_some (try (Syntax.check_term ctxt) (#lemma_term ornode))
  andalso
    #gg_parent_not_finished ornode
  andalso
    not (#refuted ornode): bool
  andalso
    is_none (#proof ornode));

(* creation of ornode *)
type is_final_goal = bool;
fun mk_ornode (is_final_goal:is_final_goal) (goal:term) =
  let
    (*TODO: check if the name is already taken.*)
    val name = (if is_final_goal then "original_goal_" else "top_down_lemma_") ^ serial_string ();
  in
   {final_goal             = is_final_goal,
    branch                 = false,
    lemma_name             = name,
    lemma_term             = goal,
    proof                  = NONE,
    proof_id               = NONE,
    refuted                = false,
    proved_completely      = false,(*We do not search for a counterexample before checking for duplication.*)
    gg_parent_not_finished = true
   }: ornode
  end;

(** update of ornode **)
(* update_gg_parent_not_finished *)
(* 
 * unlike proved_completely, gg_parent_not_finished can change both ways.
 * For example, when a new conjecture from one or-node is identical to an existing conjecture,
 * we have to add a new grand parent to this existing conjecture. 
 * Such operation may change the gg_parent_not_finished of this existing one from
 * false to true.
 *)
fun update_gg_parent_not_finished ({
  final_goal       : bool,
  branch           : bool,
  lemma_name       : string,
  lemma_term       : term,
  proof            : string option,
  proof_id         : int option,
  refuted          : bool,
  proved_completely: bool,...
}: ornode) (gg_parent_not_finished: bool) =
{
  final_goal             = final_goal,
  branch                 = branch,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = proof,
  proof_id               = proof_id,
  refuted                = refuted,
  proved_completely      = proved_completely,
  gg_parent_not_finished = gg_parent_not_finished
}: ornode;

(* update_proved_completely *)
fun update_proved_completely ({
  final_goal            : bool,
  branch                : bool,
  lemma_name            : string,
  lemma_term            : term,
  proof                 : string option,
  proof_id              : int option,
  refuted               : bool,
  gg_parent_not_finished: bool,...
}: ornode) =
{
  final_goal            = final_goal,
  branch                = branch,
  lemma_name            = lemma_name,
  lemma_term            = lemma_term,
  proof                 = proof,     
  proof_id              = proof_id,
  refuted               = refuted,
  proved_completely     = true,
  gg_parent_not_finished = gg_parent_not_finished
}: ornode;

(* update_proof_n_proof_id *)
fun update_proof_n_proof_id (proof:string) ({
  final_goal            : bool,
  branch                : bool,
  lemma_name            : string,
  lemma_term            : term,
  refuted               : bool,
  proved_completely     : bool,
  gg_parent_not_finished: bool,...
}: ornode)  =
{
  final_goal             = final_goal,
  branch                 = branch,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = SOME proof,
  proof_id               = (Unsynchronized.inc PBC_Utils.proof_id_counter; SOME (Unsynchronized.! PBC_Utils.proof_id_counter)),
  refuted                = refuted,
  proved_completely      = proved_completely: bool,
  gg_parent_not_finished = gg_parent_not_finished
}: ornode;

(* update_refuted *)
fun update_refuted ({
  final_goal            : bool,
  branch                : bool,
  lemma_name            : string,
  lemma_term            : term,
  proof                 : string option,
  proof_id              : int option,
  proved_completely     : bool,
  gg_parent_not_finished: bool,...
}: ornode) =
{
  final_goal             = final_goal,
  branch                 = branch,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = proof,
  proof_id               = proof_id,
  refuted                = true,
  proved_completely      = proved_completely: bool,
  gg_parent_not_finished = gg_parent_not_finished
}: ornode;

(* update_branch *)
fun update_branch ({
  final_goal            : bool,
  lemma_name            : string,
  lemma_term            : term,
  proof                 : string option,
  proof_id              : int option,
  refuted               : bool,
  proved_completely     : bool,
  gg_parent_not_finished: bool,...
}: ornode) =
{
  final_goal             = final_goal,
  branch                 = true,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = proof,
  proof_id               = proof_id,
  refuted                = refuted,
  proved_completely      = proved_completely: bool,
  gg_parent_not_finished = gg_parent_not_finished
}: ornode;

end;