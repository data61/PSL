(*  Title:      PSL/SeLFeE/src/Eval_Bound_Fpunode.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Bound_Fpunode: BOUND =
struct

structure EC  = Eval_Connective;
structure EFS = Eval_Fpunode_Sugar;
structure EFC = Eval_Fpunode_Core;

type connective = EC.assert_connective;
type atom       = EFC.fpunode;
datatype primitive_op = Is_In_Chained | Is_In_Fst_Subg | Is_Same_Occ_As;

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr   * expr
| Connective of connective
| Primitive  of primitive_op * atom list;

fun eval_prim Is_In_Chained  [fpun]         = EFC.eval_fpunode_core  (EFC.Is_In_Chained   fpun         ): connective
  | eval_prim Is_In_Fst_Subg [fpun]         = EFC.eval_fpunode_core  (EFC.Is_In_Fst_Subg  fpun         ): connective
  | eval_prim Is_Same_Occ_As [fpun1, fpun2] = EFS.eval_fpunode_sugar (EFS.Is_Same_Occ_As (fpun1, fpun2)): connective
  | eval_prim _               _             = error "eval_prim in Fpunode_Lambda failed!"               : connective;

end;

structure Eval_Bound_Fpunode = add_Eval_to_Bound(Bound_Fpunode): EVAL_BOUND;