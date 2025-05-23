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
val is_worth_proving    : Proof.context -> ornode -> bool;

(* creation of ornode *)
type is_final_goal = bool;
val mk_ornode: Proof.context -> is_final_goal -> string -> term -> ornode;

val is_template_based: ornode -> bool;

(* update of ornode *)
val update_gg_parent_not_finished: ornode -> bool -> ornode;
val update_proved_completely     : ornode -> ornode;
val update_proof_n_proof_id      : strings -> ornode -> ornode;
val update_is_branch             : ornode -> ornode;
val update_importance            : real -> ornode -> ornode;
val multiply_importance          : real -> ornode -> ornode;
val update_imp_if_this_is_larger : real -> ornode -> ornode;
val update_attacked              : ornode -> ornode;

end;

(*** Or_Node ***)
structure Or_Node: OR_NODE =
struct

(** ornode and functions on ornode **)
(* ornode and ornodes *)
type ornode = {
  final_goal                      : bool,
  is_branch                       : bool,
  lemma_name                      : string,
  lemma_term                      : term,(*For now we ignore "assumes" and "using".*)
  proof                           : strings option,(*Proof script to finish proving this node.*)
  proof_id                        : int option,(*To track dependency. based on the timing proved with or w/o assuming conjectures.*)
  proved_completely               : bool, (*= proved w/o assuming conjectures.*)
  (* If an or-node has a great grandparent that is not proved or refuted and this node is not
   * proved_completely, this node still needs a proof.*)
  gg_parent_not_finished          : bool,
  importance                      : real option(*NONE means "not computed yet"*),
  attacked                        : bool (*if already attacked by the Attack_On_Or_Node strategy.*)
};

type ornodes = ornode list;
              
(** query on ornode **)

(* is_worth_proving *)
fun is_worth_proving (ctxt:Proof.context) (ornode:ornode) =
    is_some (try (Syntax.check_term ctxt) (#lemma_term ornode))
  andalso
    #gg_parent_not_finished ornode
  andalso
    is_none (#proof ornode)
  andalso
    not (#is_branch ornode);

(* creation of ornode *)
type is_final_goal = bool;

fun mk_ornode (ctxt:Proof.context) (is_final_goal:is_final_goal) (lemma_name:string) (goal:term) =
  let
    val name = if   is_final_goal
               then Top_Down_Util.mk_new_lemma_name ctxt is_final_goal ""
               else lemma_name;
  in
   {final_goal             = is_final_goal,
    is_branch              = false,
    lemma_name             = name,
    lemma_term             = goal,
    proof                  = NONE,
    proof_id               = NONE,
    proved_completely      = false,(*We do not search for a counterexample before checking for duplication.*)
    gg_parent_not_finished = true,
    importance             = NONE,
    attacked               = false
   }: ornode
  end;

fun is_template_based ({lemma_name, ...}: ornode) =
  Top_Down_Util.is_template_based lemma_name;

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
  is_branch        : bool,
  lemma_name       : string,
  lemma_term       : term,
  proof            : strings option,
  proof_id         : int option,
  proved_completely: bool,
  importance       : real option,
  attacked         : bool,...
}: ornode) (gg_parent_not_finished: bool) =
{
  final_goal             = final_goal,
  is_branch              = is_branch,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = proof,
  proof_id               = proof_id,
  proved_completely      = proved_completely,
  gg_parent_not_finished = gg_parent_not_finished,
  importance             = importance,
  attacked               = attacked
}: ornode;

(* update_proved_completely *)
fun update_proved_completely ({
  final_goal            : bool,
  is_branch             : bool,
  lemma_name            : string,
  lemma_term            : term,
  proof                 : strings option,
  proof_id              : int option,
  gg_parent_not_finished: bool,
  importance            : real option,
  attacked              : bool,...
}: ornode) =
{
  final_goal             = final_goal,
  is_branch              = is_branch,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = proof,
  proof_id               = proof_id,
  proved_completely      = true,
  gg_parent_not_finished = gg_parent_not_finished,
  importance             = importance,
  attacked               = attacked
}: ornode;

local

  val  synched_int = Synchronized.var "current_proof_id" 0: int Synchronized.var;
  fun increment (i:int) = (i + 1, i + 1);
  fun get_proof_id  _ = SOME (Synchronized.change_result synched_int increment): int option;
in

(* update_proof_n_proof_id *)
fun update_proof_n_proof_id (proof:strings) ({
  final_goal            : bool,
  is_branch             : bool,
  lemma_name            : string,
  lemma_term            : term,
  proved_completely     : bool,
  gg_parent_not_finished: bool,
  importance            : real option,
  attacked              : bool,...
}: ornode)  =
{
  final_goal             = final_goal,
  is_branch              = is_branch,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = SOME proof,
  proof_id               = get_proof_id (),
  proved_completely      = proved_completely: bool,
  gg_parent_not_finished = gg_parent_not_finished,
  importance             = importance,
  attacked               = attacked
}: ornode;

end;

(* update_branch *)
fun update_is_branch ({
  final_goal            : bool,
  lemma_name            : string,
  lemma_term            : term,
  proof                 : strings option,
  proof_id              : int option,
  proved_completely     : bool,
  gg_parent_not_finished: bool,
  importance            : real option,
  attacked              : bool,...
}: ornode) =
{
  final_goal             = final_goal,
  is_branch              = true,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = proof,
  proof_id               = proof_id,
  proved_completely      = proved_completely: bool,
  gg_parent_not_finished = gg_parent_not_finished,
  importance             = importance,
  attacked               = attacked
}: ornode;

(* update_importance *)
fun update_importance (importance:real) ({
  final_goal            : bool,
  is_branch             : bool,
  lemma_name            : string,
  lemma_term            : term,
  proof                 : strings option,
  proof_id              : int option,
  proved_completely     : bool,
  gg_parent_not_finished: bool,
  attacked              : bool,...
}: ornode) =
{
  final_goal             = final_goal,
  is_branch              = is_branch,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = proof,
  proof_id               = proof_id,
  proved_completely      = proved_completely: bool,
  gg_parent_not_finished = gg_parent_not_finished,
  importance             = SOME importance,
  attacked               = attacked
}: ornode;

fun multiply_importance (importance:real) (ornode:ornode) = case #importance ornode of
  NONE => update_importance importance ornode
| SOME old_imp => update_importance (importance * old_imp) ornode;

(* update_imp_if_this_is_larger *)
fun update_imp_if_this_is_larger (new_imp:real) (ornode as {importance: real option, ...}: ornode) =
  case importance of
    NONE => update_importance new_imp ornode
  | SOME (old_imp:real) =>
      if   old_imp < new_imp
      then update_importance new_imp ornode
      else ornode;

(* update_attacked *)
fun update_attacked({
  final_goal            : bool,
  is_branch             : bool,
  lemma_name            : string,
  lemma_term            : term,
  proof                 : strings option,
  proof_id              : int option,
  proved_completely     : bool,
  gg_parent_not_finished: bool,
  importance            : real option,...
}: ornode) =
{
  final_goal             = final_goal,
  is_branch              = is_branch,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = proof,
  proof_id               = proof_id,
  proved_completely      = proved_completely: bool,
  gg_parent_not_finished = gg_parent_not_finished,
  importance             = importance,
  attacked               = true
}: ornode;

end;