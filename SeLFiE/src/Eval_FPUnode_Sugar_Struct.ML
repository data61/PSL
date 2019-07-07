(*  Title:      PSL/SeLFeE/src/Eval_Fpunode_Sugar_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Fpunode_Sugar: EVAL_FPUNODE_SUGAR =
struct

open Eval_Fpunode_Core;
open Eval_Connective;
open Full_Path_To_Fpunode;
open Eval_Unode_Core;
open Eval_Unode_Sugar;

datatype assert_fpunode_sugar =
  Assert_Fpunode_Core of assert_fpunode_core
| Connective          of assert_connective
| Is_Above            of fpunode * fpunode
| Is_Below            of fpunode * fpunode
| Is_Same_Occ_As      of fpunode * fpunode;

infix
  Is_Above
  Is_Below
  Is_In
  Is_Same_Occ_As
  And
  Is_In_Same_Location_As

fun fpunode2_to_unode2 (fpun1, fpun2) = apply2 fpunode_to_unode (fpun1, fpun2): (UN.unode * UN.unode);

fun eval_fpunode_sugar (Assert_Fpunode_Core assert_fpunode_core) = eval_fpunode_core assert_fpunode_core
  | eval_fpunode_sugar (Connective assert_connective) = eval_connective assert_connective
  | eval_fpunode_sugar (fpun1 Is_Above fpun2) =
    eval_connective (
       (eval_fpunode_core (fpun1 Is_In_Same_Location_As fpun2))
      And
       (eval_unode_core (Is_Path_Above (fpunode2_to_unode2 (fpun1, fpun2)))))
  | eval_fpunode_sugar (fpun1 Is_Below fpun2) =
    eval_connective (
       (eval_fpunode_core (fpun1 Is_In_Same_Location_As fpun2))
      And
       (eval_unode_sugar (Is_Path_Below (fpunode2_to_unode2 (fpun1, fpun2)))))
  | eval_fpunode_sugar (fpun1 Is_Same_Occ_As fpun2) =
    eval_connective (
       (eval_fpunode_core (fpun1 Is_In_Same_Location_As fpun2))
      And
       (eval_unode_core (Is_Same_Path_As (fpunode2_to_unode2 (fpun1, fpun2)))))

end;