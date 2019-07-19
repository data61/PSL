(*  Title:      PSL/SeLFeE/src/Eval_FPUnode_Core_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Fpunode_Core: EVAL_FPUNODE_CORE =
struct

type fpunode = Full_Path_To_Fpunode.fpunode;

datatype assert =
  Is_In_Same_Location_As of fpunode * fpunode
| Is_In_Chained          of fpunode
| Is_In_Fst_Subg         of fpunode (*Syntactic sugar with Numb and Is_In_Nth_Subg? But we do not need Is__In_Nth_Subg.*);

infix
  Is_In_Same_Location_As;

fun eval' (fpun1 Is_In_Same_Location_As fpun2) =
    let
      val loc1 = #location fpun1: location;
      val loc2 = #location fpun2: location;
    in
      are_same_location loc1 loc2
    end
  | eval' (Is_In_Chained fpunode ) = (case #location fpunode of Chained_Fact _ => true | _ => false)
  | eval' (Is_In_Fst_Subg fpunode) = (case #location fpunode of Subgoal 0      => true | _ => false)

fun eval assert_fpunode_core = eval' assert_fpunode_core |> Eval_Connective.bool_to_assert_connective;

end;