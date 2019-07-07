(*  Title:      PSL/SeLFeE/src/Eval_Unode_Sugar_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Unode_Sugar : EVAL_UNODE_SUGAR =
struct

open Eval_Connective;
open Eval_Unode_Core;

datatype assert_unode_sugar =
  Assert_Unode_Core of assert_unode_core
| Connective        of assert_connective
| Is_As_Deep_As     of unode * unode
| Is_Path_Below     of unode * unode;

infix
  Is_As_Deep_As
  Is_Shallower_Than
  Is_Deeper_Than
  Nor
  Is_Path_Below
  Is_Path_Above
  Is_Same_Path_As;

fun eval_unode_sugar (Assert_Unode_Core assert_unode_core) = eval_unode_core assert_unode_core
  | eval_unode_sugar (Connective assert_connective)        =
    eval_connective assert_connective
  | eval_unode_sugar (unode1 Is_As_Deep_As unode2)         =
    eval_connective (eval_unode_core (unode1 Is_Deeper_Than    unode2)
                 Nor eval_unode_core (unode1 Is_Shallower_Than unode2))
  | eval_unode_sugar (unode1 Is_Path_Below unode2)         =
    eval_connective (eval_unode_core (unode1 Is_Path_Above   unode2)
                 Nor eval_unode_core (unode1 Is_Same_Path_As unode2));

end;