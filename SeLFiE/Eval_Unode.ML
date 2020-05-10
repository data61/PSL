(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Unode.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_UNODE ***)
signature EVAL_UNODE =
sig

datatype assert =
  Has_Same_Prnt_As       of UN.unode * UN.unode
| Is_In_Trm_Prnt         of UN.unode * UN.unode (*sub-tree-1 is within sub-tree-2 string-wise*)
| Is_Deeper_Than         of UN.unode * UN.unode
| Is_Shallower_Than      of UN.unode * UN.unode
| Is_Path_Above          of UN.unode * UN.unode
| Is_Same_Path_As        of UN.unode * UN.unode
| Is_Nth_Child           of UN.unode * int
| Is_N_Plus_One_th_Child of UN.unode * int
| Debug_Print_Unode      of UN.unode;

val eval: assert -> Eval_Bool.assert;

end;

(*** Eval_Unode ***)
structure Eval_Unode: EVAL_UNODE =
struct

type unode = Unique_Node.unode;

datatype assert =
  Has_Same_Prnt_As       of unode * unode
| Is_In_Trm_Prnt         of unode * unode (*sub-tree-1 is within sub-tree-2 string-wise*)
| Is_Deeper_Than         of unode * unode
| Is_Shallower_Than      of unode * unode
| Is_Path_Above          of unode * unode
| Is_Same_Path_As        of unode * unode
| Is_Nth_Child           of unode * int
| Is_N_Plus_One_th_Child of unode * int
| Debug_Print_Unode      of UN.unode;

infix
  Has_Same_Prnt_As
  Is_In_Trm_Prnt
  Is_Deeper_Than
  Is_Shallower_Than
  Is_Path_Above
  Is_Same_Path_As
  Is_Nth_Child
  Is_N_Plus_One_th_Child;

val unode2_to_depth2                              = apply2 Unique_Node.unode_to_depth: unode * unode -> int * int;
fun unode2_to_print2 (unode2:unode * unode)       = apply2 #print unode2;
fun unode2_to_inner_path2  (unode2:unode * unode) = apply2 #inner_path  unode2;

fun eval' (unode1 Has_Same_Prnt_As unode2): bool =
    let
      val (print1, print2) = unode2_to_print2 (unode1, unode2);
      val result_bool      = print1 = print2;
    in
      result_bool
    end
  | eval' (unode1 Is_In_Trm_Prnt unode2) =
    let
      val (print1, print2) = unode2_to_print2 (unode1, unode2);
      val result_bool      = String.isSubstring print1 print2;
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
  | eval' (unode1 Is_Path_Above unode2) =
    let
      val (inner_path1, inner_path2) = unode2_to_inner_path2 (unode1, unode2)                    : (UN.inner_path * UN.inner_path);
      val result_bool    = uncurry UN.inner_path1_is_above_inner_path2 (inner_path1, inner_path2): bool;
    in
      result_bool
    end
  | eval' (unode1 Is_Same_Path_As unode2) =
    let
      val (inner_path1, inner_path2) = unode2_to_inner_path2 (unode1, unode2)       : (UN.inner_path * UN.inner_path);
      val result_bool    = uncurry UN.are_same_inner_path (inner_path1, inner_path2): bool;
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
  | eval' (Debug_Print_Unode {print,...}) = (tracing ("Debug_Print_Unode: " ^ print); true);

fun eval assert = eval' assert |> Eval_Bool.bool_to_assert;

end;