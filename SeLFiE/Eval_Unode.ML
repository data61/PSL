(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Unode.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_UNODE ***)
signature EVAL_UNODE =
sig

datatype assert =
  Has_Same_Prnt_As              of UN.unode * UN.unode
| Is_Deeper_Than                of UN.unode * UN.unode
| Is_Shallower_Than             of UN.unode * UN.unode
| Is_Nth_Child                  of UN.unode * int
| Is_N_Plus_One_th_Child        of UN.unode * int
| Is_Root_In_A_Location         of UN.unode
| Debug_Print_Unode             of UN.unode
| Node_Is_Defined_With          of (UN.unode * Pattern.command)
| Is_A_Meta_Premise             of UN.unode
| Is_A_Meta_Conclusion          of UN.unode
| Is_A_Meta_Premise_Or_Below    of UN.unode
| Is_A_Meta_Conclusion_Or_Below of UN.unode;

val eval: assert -> Eval_Bool.assert;

end;

(*** Eval_Unode ***)
structure Eval_Unode: EVAL_UNODE =
struct

type unode = Unique_Node.unode;

datatype assert =
  Has_Same_Prnt_As              of unode * unode
| Is_Deeper_Than                of unode * unode
| Is_Shallower_Than             of unode * unode
| Is_Nth_Child                  of unode * int
| Is_N_Plus_One_th_Child        of unode * int
| Is_Root_In_A_Location         of unode
| Debug_Print_Unode             of unode
| Node_Is_Defined_With          of (unode * Pattern.command)
| Is_A_Meta_Premise             of unode
| Is_A_Meta_Conclusion          of unode
| Is_A_Meta_Premise_Or_Below    of unode
| Is_A_Meta_Conclusion_Or_Below of unode;

infix
  Has_Same_Prnt_As
  Is_Deeper_Than
  Is_Shallower_Than
  Is_Path_Above
  Is_Same_Path_As
  Is_Nth_Child
  Is_N_Plus_One_th_Child;

val unode2_to_depth2                        = apply2 Unique_Node.unode_to_depth: unode * unode -> int * int;
fun unode2_to_print2 (unode2:unode * unode) = apply2 #print unode2;

fun eval' (unode1 Has_Same_Prnt_As unode2): bool =
    let
      val (print1, print2) = unode2_to_print2 (unode1, unode2);
      val result_bool      = print1 = print2;
    in
      result_bool
    end
  | eval' (unode1 Is_Deeper_Than unode2) =
    let
      val (depth1, depth2) = unode2_to_depth2 (unode1, unode2): (int * int);
      val result_bool      = depth1 > depth2;
    in
      result_bool
    end
  | eval' (unode1 Is_Shallower_Than unode2) =
    let
      val (depth1, depth2) = unode2_to_depth2 (unode1, unode2): (int * int);
      val result_bool      = depth1 < depth2;
    in
      result_bool
    end
  | eval' (unode Is_Nth_Child number) =
    let
      val last_digit_option = UN.is_nth_child unode: int option;
      val result_option     = last_digit_option <$> equal number: bool option;
    in
      Utils.is_some_true result_option
    end
  | eval' (unode Is_N_Plus_One_th_Child number) =
    let
      val last_digit_option   = UN.is_nth_child unode                        : int option;
      val result_option       = last_digit_option <$> equal (number + 1)     : bool option;
    in
      Utils.is_some_true result_option
    end
  | eval' (Is_Root_In_A_Location {inner_path,...}) = inner_path = []
  | eval' (Debug_Print_Unode {print,...}) = (tracing ("Debug_Print_Unode: " ^ print); true)
  | eval' (Node_Is_Defined_With       (unode, cmd)) = UN.is_defined_by unode cmd
  | eval' (Is_A_Meta_Premise             {tag,...}) = #is_premise    tag
  | eval' (Is_A_Meta_Conclusion          {tag,...}) = #is_conclusion tag
  | eval' (Is_A_Meta_Premise_Or_Below    {tag,...}) = #part_of_prem  tag
  | eval' (Is_A_Meta_Conclusion_Or_Below {tag,...}) = #part_of_cncl  tag;

fun eval assert = eval' assert |> Eval_Bool.bool_to_assert;

end;