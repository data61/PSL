(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Path.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** structure Path_Assert ***)
structure Path_Assert =
struct

type gen_path = Gen_Path_To_Unode.gen_path;

datatype assert =
(*Eval_Node*)
  Node_Is_Cnst                     of gen_path
| Node_Is_Free                     of gen_path
| Node_Is_Var                      of gen_path
| Node_Is_Bound                    of gen_path
| Node_Is_Lambda                   of gen_path
| Node_Is_App                      of gen_path
| Node_Is_Defined_With             of gen_path * Pattern.command
| Node_Is_Defined_With_N_Clauses   of gen_path * int
| Is_Rule_Of_Node                  of string * gen_path
| Node_Takes_N_Arguments           of gen_path * int
| Node_Takes_Less_Than_N_Arguments of gen_path * int
(*Eval_Unode*)
| Has_Same_Prnt_As            of gen_path * gen_path
| Is_Deeper_Than              of gen_path * gen_path
| Is_Shallower_Than           of gen_path * gen_path
| Is_Path_Above               of gen_path * gen_path
| Is_Same_Path_As             of gen_path * gen_path
| Is_Nth_Child                of gen_path * int
| Is_N_Plus_One_th_Child      of gen_path * int
| Is_Root_In_A_Location       of gen_path
(*only in path*)
| Unode_Has_Print               of gen_path * string
| Is_In_Subgoal                 of gen_path
| Is_In_Chained_Fact            of gen_path
| Is_In_Nth_Subgoal             of gen_path * int
| Is_In_Nth_Chained_Fact        of gen_path * int
| Is_Parent_Of                  of gen_path * gen_path
| Is_A_Meta_Premise             of gen_path(*These assertions about the meta implication cannot be in Eval_Unode because we need a table to get its parent node.*)
| Is_A_Meta_Conclusion          of gen_path
| Is_A_Meta_Premise_Or_Below    of gen_path
| Is_A_Meta_Conclusion_Or_Below of gen_path
(*debug*)
| Debug_Print_Unode           of gen_path;

end;

(*** signature EVAL_PATH ***)
signature EVAL_PATH =
sig

val eval: Proof.state -> Gen_Path_To_Unode.gen_path_to_unode_table -> Path_Assert.assert -> Eval_Bool.assert;

end;

(*** structure Each_Path: EVAL_PATH ***)
structure Eval_Path: EVAL_PATH =
struct

structure EB  = Eval_Bool;
structure END = Eval_Node;
structure EU  = Eval_Unode;
structure EIP = Eval_Print;
structure ENB = Eval_Number;
structure PA  = Path_Assert;
structure GP2U = Gen_Path_To_Unode;

type connective = Eval_Bool.assert;
type gen_path   = GP2U.gen_path;

fun eval (pst:Proof.state) (path_to_unode_table:GP2U.gen_path_to_unode_table) assert =
  let
    val path_to_unode                              = GP2U.gen_table_n_gen_path_to_unode path_to_unode_table: gen_path -> UN.unode;
    fun path_to_node    (p:gen_path)               = path_to_unode p |> #node: UN.node;
    fun path2_to_unode2 (p1:gen_path, p2:gen_path) = apply2 path_to_unode (p1, p2): (UN.unode * UN.unode);
    fun
      (*Eval_Node*)
        eval' (PA.Node_Is_Cnst                      p       ) ctxt = END.eval (END.Node_Is_Cnst                     (path_to_node p                )) ctxt
      | eval' (PA.Node_Is_Free                      p       ) ctxt = END.eval (END.Node_Is_Free                     (path_to_node p                )) ctxt
      | eval' (PA.Node_Is_Var                       p       ) ctxt = END.eval (END.Node_Is_Var                      (path_to_node p                )) ctxt
      | eval' (PA.Node_Is_Bound                     p       ) ctxt = END.eval (END.Node_Is_Bound                    (path_to_node p                )) ctxt
      | eval' (PA.Node_Is_Lambda                    p       ) ctxt = END.eval (END.Node_Is_Lambda                   (path_to_node p                )) ctxt
      | eval' (PA.Node_Is_App                       p       ) ctxt = END.eval (END.Node_Is_App                      (path_to_node p                )) ctxt
      | eval' (PA.Node_Is_Defined_With             (p,  cmd)) ctxt = END.eval (END.Node_Is_Defined_With             (path_to_node p, cmd           )) ctxt
      | eval' (PA.Node_Is_Defined_With_N_Clauses   (p,    n)) ctxt = END.eval (END.Node_Is_Defined_With_N_Clauses   (path_to_node p, n             )) ctxt
      | eval' (PA.Is_Rule_Of_Node                  (rule, p)) ctxt = END.eval (END.Is_Rule_Of_Node                  (rule,           path_to_node p)) ctxt
      | eval' (PA.Node_Takes_N_Arguments           (p,    n)) ctxt = END.eval (END.Node_Takes_N_Arguments           (path_to_node p, n             )) ctxt
      | eval' (PA.Node_Takes_Less_Than_N_Arguments (p,    n)) ctxt = END.eval (END.Node_Takes_Less_Than_N_Arguments (path_to_node p, n             )) ctxt
      (*Eval_Unode*)
      | eval' (PA.Has_Same_Prnt_As        pair)     _ = path2_to_unode2 pair    |> EU.Has_Same_Prnt_As      |> EU.eval
      | eval' (PA.Is_Deeper_Than          pair)     _ = path2_to_unode2 pair    |> EU.Is_Deeper_Than        |> EU.eval
      | eval' (PA.Is_Shallower_Than       pair)     _ = path2_to_unode2 pair    |> EU.Is_Shallower_Than     |> EU.eval
      | eval' (PA.Is_Path_Above           pair)     _ = path2_to_unode2 pair    |> EU.Is_Path_Above         |> EU.eval
      | eval' (PA.Is_Same_Path_As         pair)     _ = path2_to_unode2 pair    |> EU.Is_Same_Path_As       |> EU.eval
      | eval' (PA.Is_Nth_Child           (path, i)) _ = (path_to_unode path, i) |> EU.Is_Nth_Child          |> EU.eval
      | eval' (PA.Is_N_Plus_One_th_Child (path, i)) _ = (path_to_unode path, i) |> EU.Is_N_Plus_One_th_Child|> EU.eval
      | eval' (PA.Is_Root_In_A_Location   path)     _ = path_to_unode path      |> EU.Is_Root_In_A_Location |> EU.eval
      (*only in path*)
      | eval' (PA.Unode_Has_Print (path, print)) _ =
          let
            val unode = path_to_unode path: UN.unode;
          in
            print = #print unode |> Eval_Bool.bool_to_assert
          end
      | eval' (PA.Is_In_Subgoal          path) _ = GP2U.path_is_in_subgoal path                  |> EB.bool_to_assert
      | eval' (PA.Is_In_Chained_Fact     path) _ = GP2U.path_is_in_chained_fact path             |> EB.bool_to_assert
      | eval' (PA.Is_In_Nth_Subgoal      pair) _ = uncurry GP2U.path_is_in_nth_subgoal pair      |> EB.bool_to_assert
      | eval' (PA.Is_In_Nth_Chained_Fact pair) _ = uncurry GP2U.path_is_in_nth_chained_fact pair |> EB.bool_to_assert
      | eval' (PA.Is_Parent_Of           pair) _ = GP2U.is_parent_path_of pair |> EB.bool_to_assert
      (*TODO for all atomic assertions about the meta-implication. Check if the first child of the parent node is the meta implication.*)
      | eval' (PA.Is_A_Meta_Premise      prem) ctxt = EB.bool_to_assert (
        let
          val parent_path_opt = GP2U.path_to_its_parent_path prem                  : gen_path option;
          fun is_app  p       = eval' (PA.Node_Is_App p) ctxt |> EB.assert_to_bool : bool;
          fun is_cncl p       = GP2U.is_last_child_of path_to_unode_table (prem, p): bool;
          (*TODO: check if the premise is not the first child of the parent node
                  because the first child of the parent node should be the meta-implication.*)
        in
          Utils.is_some_true (Option.map is_app parent_path_opt) andalso
          not (Utils.is_some_true (Option.map is_cncl parent_path_opt))
        end)
      | eval' (PA.Is_A_Meta_Conclusion      cncl) ctxt = EB.bool_to_assert ((*TODO: refactor with Is_A_Meta_Premise?*)
        let
          val parent_path_opt = GP2U.path_to_its_parent_path cncl                  : gen_path option;
          fun is_app  p       = eval' (PA.Node_Is_App p) ctxt |> EB.assert_to_bool : bool;
          fun is_cncl p       = GP2U.is_last_child_of path_to_unode_table (cncl, p): bool;
        in
          Utils.is_some_true (Option.map is_app parent_path_opt) andalso
          Utils.is_some_true (Option.map is_cncl parent_path_opt)
        end)
      | eval' (PA.Is_A_Meta_Premise_Or_Below prem) ctxt = EB.bool_to_assert ((*TODO*)
(*
 * 1. Implement Is_An_Arg_Of first
 * 3. Implement get_all_ancestors_of (w/o user-interface)
 * 2. Implement Is_An_Arg_Or_Below_Arg_Of using Is_An_Arg_Of and get_all_ancestors_of
 * 4. For an ancestor,
          that ancestor is function application
        and
          the first child of the ancestor is the meta-implication
        and
          the part-of-a-premise is not the first child of the ancestor
        and
          not (the part-of-a-premise is_an_argument_or_below_argument_of the last child of the ancestor.
 *)
        true)
      | eval' (PA.Is_A_Meta_Conclusion_Or_Below prem) ctxt = EB.bool_to_assert ((*TODO*)
        true)
      (*debug*)
      | eval' (PA.Debug_Print_Unode      path) _ = path_to_unode path |> EU.Debug_Print_Unode |> EU.eval;
  in eval' assert (Proof.context_of pst) end;

end;