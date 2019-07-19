(*  Title:      PSL/SeLFeE/src/Eval_Fpunode_Sugar_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Fpunode_Sugar: EVAL_FPUNODE_SUGAR =
struct

structure EC   = Eval_Connective;
structure EUC  = Eval_Unode_Core;
structure EUS  = Eval_Unode_Sugar;
structure EFC  = Eval_Fpunode_Core;
structure FPTF = Full_Path_To_Fpunode;

type fpunode = Full_Path_To_Fpunode.fpunode;

datatype assert =
  Connective     of Eval_Connective.assert
| Is_Above       of fpunode * fpunode
| Is_Below       of fpunode * fpunode
| Is_Same_Occ_As of fpunode * fpunode;

val Is_In_Same_Location_As = EFC.Is_In_Same_Location_As;
val And = EC.And;

infix
  Is_Above
  Is_Below
  Is_In
  Is_Same_Occ_As
  And
  Is_In_Same_Location_As

fun eval (Connective assert_connective) = EC.eval assert_connective
  | eval (fpun1 Is_Above fpun2) =
    EC.eval (
       (EFC.eval (fpun1 Is_In_Same_Location_As fpun2))
      And
       (EUC.eval (EUC.Is_Path_Above (FPTF.fpunode2_to_unode2 (fpun1, fpun2)))))
  | eval (fpun1 Is_Below fpun2) =
    EC.eval (
       (EFC.eval (fpun1 Is_In_Same_Location_As fpun2))
      And
       (EUS.eval (EUS.Is_Path_Below (FPTF.fpunode2_to_unode2 (fpun1, fpun2)))))
  | eval (fpun1 Is_Same_Occ_As fpun2) =
    EC.eval (
       (EFC.eval (fpun1 Is_In_Same_Location_As fpun2))
      And
       (EUC.eval (EUC.Is_Same_Path_As (FPTF.fpunode2_to_unode2 (fpun1, fpun2)))))

end;