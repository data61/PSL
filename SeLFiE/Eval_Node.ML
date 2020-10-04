(*  Title:      PSL/SeLFeE/src/Eval_Node_Core_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_NODE ***)
signature EVAL_NODE =
sig

datatype assert =
  Node_Is_Cnst                     of UN.node
| Node_Is_Free                     of UN.node
| Node_Is_Var                      of UN.node
| Node_Is_Bound                    of UN.node (*corresponds to Bound in term*)
| Node_Is_Lambda                   of UN.node (*lambda abstraction corresponding to Abs in Term*)
| Node_Is_App                      of UN.node (*function application corresponding to $ in Term*)
| Node_Is_Defined_With_N_Clauses   of UN.node * int
| Is_Rule_Of_Node                  of string  * UN.node
| Node_Takes_N_Arguments           of UN.node * int
| Node_Takes_Less_Than_N_Arguments of UN.node * int;

val eval': assert -> Proof.context -> bool;
val eval : assert -> Proof.context -> Eval_Bool.assert;

end;

(*** Eval_Node ***)
structure Eval_Node: EVAL_NODE =
struct

datatype assert =
  Node_Is_Cnst                     of UN.node
| Node_Is_Free                     of UN.node
| Node_Is_Var                      of UN.node
| Node_Is_Bound                    of UN.node (*corresponds to Bound in term*)
| Node_Is_Lambda                   of UN.node (*lambda abstraction corresponding to Abs in Term*)
| Node_Is_App                      of UN.node (*function application corresponding to $ in Term*)
| Node_Is_Defined_With_N_Clauses   of UN.node * int
| Is_Rule_Of_Node                  of string  * UN.node
| Node_Takes_N_Arguments           of UN.node * int
| Node_Takes_Less_Than_N_Arguments of UN.node * int;

fun eval' (Node_Is_Cnst                      node                      ) _    = UN.is_NC node
  | eval' (Node_Is_Free                      node                      ) _    = UN.is_NF node
  | eval' (Node_Is_Var                       node                      ) _    = UN.is_NV node
  | eval' (Node_Is_Bound                     node                      ) _    = UN.is_NB node
  | eval' (Node_Is_Lambda                    node                      ) _    = UN.is_NL node
  | eval' (Node_Is_App                       node                      ) _    = UN.is_NA node
  | eval' (Node_Is_Defined_With_N_Clauses   (UN.NC (cname, _), int))     ctxt = SeLFiE_Util.ctxt_n_cname_to_number_of_defining_clauses ctxt cname = int
  | eval' (Node_Is_Defined_With_N_Clauses    _                         ) _    = false
(*TODO: Is_Set_Of_Node*)
  | eval' (Is_Rule_Of_Node                  (rule, UN.NC (cname, _)))    ctxt = SeLFiE_Util.rule_to_const_name ctxt rule = cname orelse rule = cname
  | eval' (Is_Rule_Of_Node                   _                         ) _    = false
  | eval' (Node_Takes_N_Arguments           (node, n))                   _    = UN.node_to_numb_of_arguments node = n
  | eval' (Node_Takes_Less_Than_N_Arguments (node, n))                   _    = n < UN.node_to_numb_of_arguments node;(*Note the direction.*)

fun eval assert ctxt = eval' assert ctxt |> Eval_Bool.bool_to_assert;

end;