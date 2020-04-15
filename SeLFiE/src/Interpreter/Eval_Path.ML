(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Path.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** structure Path_Assert ***)
structure Path_Assert =
struct

datatype 'path assert =
(*Eval_Node*)
  Is_Cnst                of 'path
| Is_Free                of 'path
| Is_Var                 of 'path
| Is_Bound               of 'path
| Is_Lambda              of 'path
| Is_App                 of 'path
| Is_Defined_With        of 'path * Pattern.command
| Is_Rule_Of_Node        of string * 'path
(*Eval_Unode*)
| Has_Same_Prnt_As       of 'path * 'path
| Is_In_Trm_Prnt         of 'path * 'path
| Is_Deeper_Than         of 'path * 'path
| Is_Shallower_Than      of 'path * 'path
| Is_Path_Above          of 'path * 'path
| Is_Same_Path_As        of 'path * 'path
| Is_Nth_Child           of 'path * int
| Is_N_Plus_One_th_Child of 'path * int
(*only in path*)
| Unode_Has_Print        of 'path * string
| Is_In_Subgoal          of 'path
| Is_In_Chained_Fact     of 'path
| Is_In_Nth_Subgoal      of 'path * int
| Is_In_Nth_Chained_Fact of 'path * int
(*debug*)
| Debug_Print_Unode      of 'path;

end;

(*** signature EVAL_EACH_PATH ***)
signature EVAL_EACH_PATH =
sig

type path;

val eval: term -> Proof.state -> path Path_Assert.assert -> Eval_Bool.assert;

end;

(*** signature EVAL_PATH ***)
signature EVAL_PATH =
sig

datatype gen_assert =
  Outer_Assert of outer_path    Path_Assert.assert
| Inner_Assert of UN.inner_path Path_Assert.assert;

val eval: term -> Proof.state -> gen_assert -> Eval_Bool.assert;

end;

(*** functor make_Each_Eval_Path: PATH_TO_UNODE -> EVAL_PATH ***)
functor make_Each_Eval_Path (Path_To_Unode:PATH_TO_UNODE): EVAL_EACH_PATH =
struct

type connective = Eval_Bool.assert;
type path       = Path_To_Unode.path;

structure END = Eval_Node;
structure EU  = Eval_Unode;
structure EIP = Eval_Print;
structure ENB = Eval_Number;
structure PA  = Path_Assert;

fun eval (term:term) (pst:Proof.state) assert =
  let
    val table  = Path_To_Unode.pst_n_trm_to_path_to_unode_table pst term: Path_To_Unode.path_to_unode_table;
    type unode = UN.unode;
    fun path_to_unode (p:path) = Path_To_Unode.lookup table p |> Utils.the' "lookup in path_to_unode failed";
    fun path_to_node  (p:path) = path_to_unode p |> #node: UN.node;
    fun path2_to_unode2 (p1:path, p2:path) = apply2 path_to_unode (p1, p2): (UN.unode * UN.unode);
    fun
      (*Eval_Node*)
        eval' (PA.Is_Cnst   p)               ctxt = END.eval (END.Is_Cnst         (path_to_node p                )) ctxt
      | eval' (PA.Is_Free   p)               ctxt = END.eval (END.Is_Free         (path_to_node p                )) ctxt
      | eval' (PA.Is_Var    p)               ctxt = END.eval (END.Is_Var          (path_to_node p                )) ctxt
      | eval' (PA.Is_Bound  p)               ctxt = END.eval (END.Is_Bound        (path_to_node p                )) ctxt
      | eval' (PA.Is_Lambda p)               ctxt = END.eval (END.Is_Lambda       (path_to_node p                )) ctxt
      | eval' (PA.Is_App    p)               ctxt = END.eval (END.Is_App          (path_to_node p                )) ctxt
      | eval' (PA.Is_Defined_With (p, cmd))  ctxt = END.eval (END.Is_Defined_With (path_to_node p, cmd           )) ctxt
      | eval' (PA.Is_Rule_Of_Node (rule, p)) ctxt = END.eval (END.Is_Rule_Of_Node (rule,           path_to_node p)) ctxt
      (*Eval_Unode*)
      | eval' (PA.Has_Same_Prnt_As        pair)     _ = path2_to_unode2 pair    |> EU.Has_Same_Prnt_As      |> EU.eval
      | eval' (PA.Is_In_Trm_Prnt          pair)     _ = path2_to_unode2 pair    |> EU.Is_In_Trm_Prnt        |> EU.eval
      | eval' (PA.Is_Deeper_Than          pair)     _ = path2_to_unode2 pair    |> EU.Is_Deeper_Than        |> EU.eval
      | eval' (PA.Is_Shallower_Than       pair)     _ = path2_to_unode2 pair    |> EU.Is_Shallower_Than     |> EU.eval
      | eval' (PA.Is_Path_Above           pair)     _ = path2_to_unode2 pair    |> EU.Is_Path_Above         |> EU.eval
      | eval' (PA.Is_Same_Path_As         pair)     _ = path2_to_unode2 pair    |> EU.Is_Same_Path_As       |> EU.eval
      | eval' (PA.Is_Nth_Child           (path, i)) _ = (path_to_unode path, i) |> EU.Is_Nth_Child          |> EU.eval
      | eval' (PA.Is_N_Plus_One_th_Child (path, i)) _ = (path_to_unode path, i) |> EU.Is_N_Plus_One_th_Child|> EU.eval
      (*only in path*)
      | eval' (PA.Unode_Has_Print (path, print)) _ =
          let
            val unode = path_to_unode path: UN.unode;
          in
            print = #print unode |> Eval_Bool.bool_to_assert
          end
      | eval' (PA.Is_In_Subgoal          path) _ = Path_To_Unode.path_is_in_subgoal path                  |> Eval_Bool.bool_to_assert
      | eval' (PA.Is_In_Chained_Fact     path) _ = Path_To_Unode.path_is_in_chained_fact path             |> Eval_Bool.bool_to_assert
      | eval' (PA.Is_In_Nth_Subgoal      pair) _ = uncurry Path_To_Unode.path_is_in_nth_subgoal pair      |> Eval_Bool.bool_to_assert
      | eval' (PA.Is_In_Nth_Chained_Fact pair) _ = uncurry Path_To_Unode.path_is_in_nth_chained_fact pair |> Eval_Bool.bool_to_assert
      (*debug*)
      | eval' (PA.Debug_Print_Unode      path) _ = path_to_unode path |> EU.Debug_Print_Unode |> EU.eval;
  in eval' assert (Proof.context_of pst) end;

end;

(*** structure: Eval_Inner_Path and Eval_Outer_Path ***)
structure Eval_Inner_Path = make_Each_Eval_Path (Inner_Path_To_Unode): EVAL_EACH_PATH;
structure Eval_Outer_Path = make_Each_Eval_Path (Outer_Path_To_Unode): EVAL_EACH_PATH;

(*** structure: EVAL_PATH ***)
structure Eval_Path: EVAL_PATH =
struct

datatype gen_assert =
  Outer_Assert of outer_path    Path_Assert.assert
| Inner_Assert of UN.inner_path Path_Assert.assert;

fun eval trm pst (Inner_Assert assert) = Eval_Inner_Path.eval trm pst assert
  | eval trm pst (Outer_Assert assert) = Eval_Outer_Path.eval trm pst assert

end;