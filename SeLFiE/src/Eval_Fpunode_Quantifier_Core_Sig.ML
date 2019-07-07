(*  Title:      PSL/SeLFeE/src/Eval_Fpunode_Quantifier_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_FPUNODE_QUANTIFIER =
sig

type assert_fpunode_sugar;
type fpunode;
type full_path_to_fpunode_table;
type assert_connective;

datatype domain_fpunode = Domain_Fpunode of full_path list;

val full_path_to_fpunode_table_to_domain_fpunode: full_path_to_fpunode_table -> domain_fpunode;

datatype assert_fpunode_quantifier_core =
  Assert_Fpunode_Sugar of assert_fpunode_sugar
| All_Fpunode          of fpunode * assert_fpunode_quantifier_core;

val eval_fpunode_quantifier_core: assert_fpunode_quantifier_core -> assert_connective;

end;