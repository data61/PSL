(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Path.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** structure Path_Assert ***)
structure Path_Assert =
struct

type gen_path = Gen_Path.gen_path;

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
| Is_Nth_Child                of gen_path * int
| Is_N_Plus_One_th_Child      of gen_path * int
| Is_Root_In_A_Location       of gen_path
(*only in path*)
| Unode_Has_Print                          of gen_path * string
| Is_In_Subgoal                            of gen_path
| Is_In_Chained_Fact                       of gen_path
| Is_In_Nth_Subgoal                        of gen_path * int
| Is_In_Nth_Chained_Fact                   of gen_path * int
| Are_In_Same_Location                     of gen_path * gen_path
| Is_Parent_Of                             of gen_path * gen_path
| Is_Path_Above                            of gen_path * gen_path
| Is_Same_Path_As                          of gen_path * gen_path
| Is_An_Argument_Of                        of gen_path * gen_path
| Is_An_Argument_Or_Below_Argument_Of      of gen_path * gen_path
| Is_Nth_Child_Or_Below_Nth_Child_Of       of gen_path * int * gen_path
| Is_Nth_Argument_Of                       of gen_path * int * gen_path
| Is_Nth_Argument_Or_Below_Nth_Argument_Of of gen_path * int * gen_path
| Is_A_Meta_Premise                        of gen_path(*These assertions about the meta implication cannot be in Eval_Unode because we need a table to get its parent node.*)
| Is_A_Meta_Conclusion                     of gen_path
| Is_A_Meta_Premise_Or_Below               of gen_path
| Is_A_Meta_Conclusion_Or_Below            of gen_path
(*debug*)
| Debug_Print_Unode           of gen_path;

end;

(*** signature EVAL_PATH ***)
signature EVAL_PATH =
sig

val eval: Proof.state -> Gen_Path.gen_path_to_unode_table -> Path_Assert.assert -> Eval_Bool.assert;

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
structure GP  = Gen_Path;

type connective = Eval_Bool.assert;
type gen_path   = GP.gen_path;

fun eval (pst:Proof.state) (path_to_unode_table:GP.gen_path_to_unode_table) assert =
  let
    val path_to_unode                              = GP.gen_table_n_gen_path_to_unode path_to_unode_table: gen_path -> UN.unode;
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
      | eval' (PA.Is_In_Subgoal          path          ) _    = GP.path_is_in_subgoal path                  |> EB.bool_to_assert
      | eval' (PA.Is_In_Chained_Fact     path          ) _    = GP.path_is_in_chained_fact path             |> EB.bool_to_assert
      | eval' (PA.Is_In_Nth_Subgoal      pair          ) _    = uncurry GP.path_is_in_nth_subgoal pair      |> EB.bool_to_assert
      | eval' (PA.Is_In_Nth_Chained_Fact pair          ) _    = uncurry GP.path_is_in_nth_chained_fact pair |> EB.bool_to_assert
      | eval' (PA.Are_In_Same_Location   pair          ) _    = uncurry GP.are_in_same_location  pair       |> EB.bool_to_assert
      | eval' (PA.Is_Parent_Of          (parent, child)) _    = GP.is_parent_of parent child                |> EB.bool_to_assert
      | eval' (PA.Is_Path_Above         (above,  below)) _    = GP.is_above above below                     |> EB.bool_to_assert
      | eval' (PA.Is_Same_Path_As       (path1,  path2)) _    = GP.is_same_path_as path1 path2              |> EB.bool_to_assert
      | eval' (PA.Is_An_Argument_Of     (arg,    func )) ctxt = EB.bool_to_assert (
        let
          val parent_path_opt = GP.path_to_its_parent_path arg: gen_path option;
          val parent_is_app   = Option.map (fn p => eval' (PA.Node_Is_App p) ctxt |> EB.assert_to_bool) parent_path_opt
                             |> Utils.is_some_true: bool;
          fun is_its_child  c = Option.map (Utils.flip GP.is_parent_of c) parent_path_opt
                             |> Utils.is_some_true: bool;
          fun is_fst_child c  = Option.map (GP.is_fst_child_of c) parent_path_opt
                             |> Utils.is_some_true: bool;
          fun is_not_fst_child c = Option.map (GP.is_fst_child_of c) parent_path_opt
                             |> Utils.is_some_false: bool;
        in
                  parent_is_app
          andalso is_fst_child func
          andalso is_its_child arg
          andalso is_not_fst_child arg
        end
        )
      | eval' (PA.Is_An_Argument_Or_Below_Argument_Of (part_of_arg, func)) ctxt = EB.bool_to_assert (
        let
          val ancestors = GP.path_to_its_ancestors_paths part_of_arg: GP.gen_path list;
          fun for_an_ancestor (ancestor:GP.gen_path) =
          let
            val ancestor_is_app       = eval' (PA.Node_Is_App ancestor) ctxt |> EB.assert_to_bool: bool;
            val func_is_fst_child     = GP.is_fst_child_of func ancestor                         : bool;
            val arg_is_not_fst_child  = not (GP.is_fst_child_of part_of_arg ancestor)            : bool;
            val ancestor_is_above_arg = GP.is_above ancestor part_of_arg                         : bool;
           in
             ancestor_is_app andalso func_is_fst_child andalso arg_is_not_fst_child andalso ancestor_is_above_arg
           end;
        in
          exists for_an_ancestor ancestors
        end
        )
      | eval' (PA.Is_Nth_Child_Or_Below_Nth_Child_Of (part_of_nth_child, i, parent)) ctxt = EB.bool_to_assert (
        let
          val nth_child_opt      = GP.path_to_its_nth_child_path path_to_unode_table parent i: GP.gen_path option;
          val is_nth_child       = nth_child_opt <$> (fn nth_child => eval' (PA.Is_Same_Path_As (part_of_nth_child, nth_child)) ctxt |> EB.assert_to_bool)
                                |> Utils.is_some_true: bool;
          val is_below_nth_child = nth_child_opt <$> (fn nth_child => eval' (PA.Is_Path_Above (nth_child, part_of_nth_child)) ctxt |> EB.assert_to_bool)
                                |> Utils.is_some_true: bool;
        in
            is_nth_child orelse is_below_nth_child
         end)
      | eval' (PA.Is_Nth_Argument_Of (nth_arg, numb, func)) ctxt = EB.bool_to_assert ((*TODO: refactor with Is_An_Argument_Of*)
        let
          val parent_path_opt = GP.path_to_its_parent_path nth_arg: gen_path option;
          val parent_is_app   = Option.map (fn p => eval' (PA.Node_Is_App p) ctxt |> EB.assert_to_bool) parent_path_opt
                             |> Utils.is_some_true: bool;
          fun is_fst_child c  = Option.map (GP.is_fst_child_of c) parent_path_opt
                             |> Utils.is_some_true: bool;
          fun is_its_n_plus1_th_child c = eval' (PA.Is_Nth_Child  (c, numb + 1(*!*))) ctxt  |> EB.assert_to_bool;
        in
                  parent_is_app
          andalso is_fst_child func
          andalso is_its_n_plus1_th_child nth_arg
        end
        )
      | eval' (PA.Is_Nth_Argument_Or_Below_Nth_Argument_Of (part_of_nth_arg, numb, func)) ctxt = EB.bool_to_assert ((*TODO: refactor with Is_An_Argument_Or_Below_Argument_Of and Is_Nth_Argument_Of*)
        let
          val ancestors = GP.path_to_its_ancestors_paths part_of_nth_arg: GP.gen_path list;
          fun for_an_ancestor (ancestor:GP.gen_path) =
            let
              val parent_of_ancestor_opt       = GP.path_to_its_parent_path ancestor: gen_path option;
              val parent_of_ancestor_is_app    = Option.map (fn p => eval' (PA.Node_Is_App p) ctxt |> EB.assert_to_bool) parent_of_ancestor_opt |> Utils.is_some_true: bool;
              val part_of_nth_arg_is_fst_child_of_parent_of_ancestor
                                               = Option.map (GP.is_fst_child_of func) parent_of_ancestor_opt |> Utils.is_some_true: bool;
              val ancestor_is_n_plus1_th_child = eval' (PA.Is_Nth_Child (ancestor, numb + 1(*!*))) ctxt  |> EB.assert_to_bool;
             in
                       parent_of_ancestor_is_app
               andalso part_of_nth_arg_is_fst_child_of_parent_of_ancestor
               andalso ancestor_is_n_plus1_th_child
             end;
        in
          exists for_an_ancestor (part_of_nth_arg::ancestors)
        end
        )

      | eval' (PA.Is_A_Meta_Premise      prem) ctxt = EB.bool_to_assert ((*TODO: refactoring with Is_A_Meta_Conclusion*)
        let
          val parent_path_opt   = GP.path_to_its_parent_path prem                                      : gen_path option;
          val func_opt          = parent_path_opt >>= GP.path_to_its_fst_child_path path_to_unode_table: GP.gen_path option;
          val func_unode        = func_opt >>= try path_to_unode                                       : UN.unode option;
          val func_print_opt    = func_unode <$> #print                                                : string option;
          val func_is_meta_imp  = func_print_opt <$> equal "Pure.imp" |> Utils.is_some_true            : bool;
          fun is_app  p         = eval' (PA.Node_Is_App p) ctxt |> EB.assert_to_bool                   : bool;
          fun prem_is_cncl_of p = GP.is_last_child_of path_to_unode_table (prem, p)                    : bool;
        in
          func_is_meta_imp andalso
          Utils.is_some_true (Option.map is_app parent_path_opt) andalso
          not (Utils.is_some_true (Option.map prem_is_cncl_of parent_path_opt))
        end)
      | eval' (PA.Is_A_Meta_Conclusion      cncl) ctxt = EB.bool_to_assert ((*TODO: refactor with Is_A_Meta_Premise?*)
        let
          val parent_path_opt   = GP.path_to_its_parent_path cncl                  : gen_path option;
          val func_opt          = parent_path_opt >>= GP.path_to_its_fst_child_path path_to_unode_table: GP.gen_path option;
          val func_unode        = func_opt >>= try path_to_unode                                       : UN.unode option;
          val func_print_opt    = func_unode <$> #print                                                : string option;
          val func_is_meta_imp  = func_print_opt <$> equal "Pure.imp" |> Utils.is_some_true            : bool;
          fun is_app  p         = eval' (PA.Node_Is_App p) ctxt |> EB.assert_to_bool : bool;
          fun prem_is_cncl_of p = GP.is_last_child_of path_to_unode_table (cncl, p): bool;
        in
          func_is_meta_imp andalso
          Utils.is_some_true (Option.map is_app parent_path_opt) andalso
          Utils.is_some_true (Option.map prem_is_cncl_of parent_path_opt)
        end)
      | eval' (PA.Is_A_Meta_Premise_Or_Below part_of_prem) ctxt = EB.bool_to_assert ((*TODO*)
        let
          val ancestors = GP.path_to_its_ancestors_paths part_of_prem: GP.gen_path list;
          fun for_an_ancestor (ancestor:GP.gen_path) =
          let
            val ancestor_is_app       = eval' (PA.Node_Is_App ancestor) ctxt |> EB.assert_to_bool : bool;
            val func_opt              = GP.path_to_its_fst_child_path path_to_unode_table ancestor: GP.gen_path option;
            val func_unode            = func_opt >>= try path_to_unode                            : UN.unode option;
            val func_print_opt        = func_unode <$> #print                                     : string option;
            val func_is_meta_imp      = func_print_opt <$> equal "Pure.imp" |> Utils.is_some_true : bool;
            val func_is_fst_child     = func_opt <$> (Utils.flip GP.is_fst_child_of ancestor)
                                     |> Utils.is_some_true                                        : bool;
            val ancestor_is_above_prem = GP.is_above ancestor part_of_prem                        : bool;
            fun ancestors_are_never_part_of_last_child_of_ancestor func_app =
                not (exists (fn prem => GP.is_last_child_of path_to_unode_table (prem, func_app)) ancestors): bool;
          in
                     ancestor_is_app
             andalso func_is_meta_imp
             andalso func_is_fst_child
             andalso ancestor_is_above_prem
             andalso ancestors_are_never_part_of_last_child_of_ancestor ancestor
           end;
        in
          exists for_an_ancestor ancestors
        end
        )
      | eval' (PA.Is_A_Meta_Conclusion_Or_Below part_of_cncl) ctxt = EB.bool_to_assert ((*TODO: refactoring with Is_A_Meta_Premise_Or_Below*)
        let
          val ancestors = GP.path_to_its_ancestors_paths part_of_cncl: GP.gen_path list;
          fun for_an_ancestor (ancestor:GP.gen_path) =
          let
            val ancestor_is_app       = eval' (PA.Node_Is_App ancestor) ctxt |> EB.assert_to_bool : bool;
            val func_opt              = GP.path_to_its_fst_child_path path_to_unode_table ancestor: GP.gen_path option;
            val func_unode            = func_opt >>= try path_to_unode                            : UN.unode option;
            val func_print_opt        = func_unode <$> #print                                     : string option;
            val func_is_meta_imp      = func_print_opt <$> equal "Pure.imp" |> Utils.is_some_true : bool;
            val func_is_fst_child     = func_opt <$> (Utils.flip GP.is_fst_child_of ancestor)
                                     |> Utils.is_some_true                                        : bool;
            val ancestor_is_above_prem = GP.is_above ancestor part_of_cncl                        : bool;
            fun ancestors_are_part_of_last_child_of_ancestor func_app =
                exists (fn prem => GP.is_last_child_of path_to_unode_table (prem, func_app)) ancestors: bool;
          in
                     ancestor_is_app 
             andalso func_is_meta_imp
             andalso func_is_fst_child
             andalso ancestor_is_above_prem
             andalso ancestors_are_part_of_last_child_of_ancestor ancestor
           end;
        in
          exists for_an_ancestor ancestors
        end
        )
      (*debug*)
      | eval' (PA.Debug_Print_Unode      path) _ = path_to_unode path |> EU.Debug_Print_Unode |> EU.eval;
  in eval' assert (Proof.context_of pst) end;

end;