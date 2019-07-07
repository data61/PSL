(*  Title:      PSL/SeLFeE/src/Eval_Fpunode_Quantifier_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Fpunode_Quantifier: EVAL_FPUNODE_QUANTIFIER =
struct

open Full_Path_To_Fpunode;
open Eval_Fpunode_Sugar;

datatype domain_fpunode = Domain_Fpunode of full_path list;

val full_path_to_fpunode_table_to_domain_fpunode = undefined: full_path_to_fpunode_table -> domain_fpunode;

datatype assert_fpunode_quantifier_core =
  Assert_Fpunode_Sugar of assert_fpunode_sugar
| All_Fpunode          of fpunode * assert_fpunode_quantifier_core;

fun eval_fpunode_quantifier_core (Assert_Fpunode_Sugar assert_fpunode_sugar) = eval_fpunode_sugar assert_fpunode_sugar

end;