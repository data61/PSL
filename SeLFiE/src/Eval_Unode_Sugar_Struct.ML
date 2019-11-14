(*  Title:      PSL/SeLFeE/src/Eval_Unode_Sugar_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Unode_Sugar : EVAL_UNODE_SUGAR =
struct

structure EC  = Eval_Connective;
structure EUC = Eval_Unode_Core;

datatype assert =
  Connective    of EC.assert
| Is_As_Deep_As of UN.unode * UN.unode
| Is_Path_Below of UN.unode * UN.unode;

val Is_Deeper_Than    = EUC.Is_Deeper_Than;
val Is_Shallower_Than = EUC.Is_Shallower_Than;
val Is_Path_Above     = EUC.Is_Path_Above;
val Is_Same_Path_As   = EUC.Is_Same_Path_As;
val Nor               = EC.Nor;

infix
  Is_As_Deep_As
  Is_Shallower_Than
  Is_Deeper_Than
  Nor
  Is_Path_Below
  Is_Path_Above
  Is_Same_Path_As;

fun eval (Connective assert) = EC.eval assert
  | eval (unode1 Is_As_Deep_As unode2) =
    EC.eval (EUC.eval (unode1 Is_Deeper_Than unode2)
         Nor EUC.eval (unode1 Is_Shallower_Than unode2))
  | eval (unode1 Is_Path_Below unode2) =
    EC.eval (EUC.eval (unode1 Is_Path_Above unode2)
         Nor EUC.eval (unode1 Is_Same_Path_As unode2));

end;