(*  Title:      PSL/SeLFeE/src/Eval_Node_Sugar_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Node_Sugar: EVAL_NODE_SUGAR =
struct

structure ENC = Eval_Node_Core;
structure EC  = Eval_Connective;

datatype assert =
  Connective of EC.assert
| Is_Atom    of UN.node
| Is_Compund of UN.node;

val Or = EC.Or;
infix Or;

fun eval (Connective assert_connective)      = EC.eval assert_connective
  | eval (Is_Atom assert_node_sugar)         =
    EC.eval (ENC.eval (ENC.Is_Cnst  assert_node_sugar)
          Or ENC.eval (ENC.Is_Free  assert_node_sugar)
          Or ENC.eval (ENC.Is_Var   assert_node_sugar)
          Or ENC.eval (ENC.Is_Bound assert_node_sugar))
  | eval (Is_Compund node)                   =
    EC.eval (ENC.eval (ENC.Is_Lambda node)
          Or ENC.eval (ENC.Is_App node));

end;