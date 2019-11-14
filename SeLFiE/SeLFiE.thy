(*  Title:      PSL/SeLFiE/SeLFiE.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

MeLoId: Machine Learning Induction for Isabelle/HOL, and
LiFtEr: Logical Feature Extractor.
SeLFiE: Semantic Logical Feature Extractor.
*)
theory SeLFiE
  imports "../PSL"
(*
  keywords "assert_SeLFiE_true" :: diag
   and     "assert_SeLFiE_false":: diag
*)
begin
(*pre-processing*)
ML_file "../src/Utils.ML"
ML_file "../MeLoId/src/MeLoId_Util.ML"
ML_file "../LiFtEr/src/Matrix_Sig.ML"
ML_file "../LiFtEr/src/Matrix_Struct.ML"
ML_file "../LiFtEr/src/Matrix_Test.ML"
ML_file "../LiFtEr/src/LiFtEr_Util_Sig.ML"
ML_file "../LiFtEr/src/LiFtEr_Util_Struct.ML"
ML_file "../LiFtEr/src/Pattern_Sig.ML" (*TODO: We only need get_command from this module.*)
ML_file "../LiFtEr/src/Pattern_Struct.ML"
ML_file "../LiFtEr/src/Pattern_Test.ML"
ML_file "../LiFtEr/src/Unique_Node_Sig.ML"
ML_file "../LiFtEr/src/Unique_Node_Struct.ML"
ML_file "../LiFtEr/src/Unique_Node_Test.ML"
ML_file "../LiFtEr/src/Term_Table_Sig.ML"
ML_file "../LiFtEr/src/Term_Table_Struct.ML"
ML_file "../LiFtEr/src/Term_Table_Test.ML"
ML_file "../LiFtEr/src/DInduct_Sig.ML"
ML_file "../LiFtEr/src/DInduct_Struct.ML"
(*bootstrapping interpreter*)
ML_file "src/Eval_Connective_Sig.ML"
ML_file "src/Eval_Connective_Struct.ML"
ML_file "src/Eval_Node_Core_Sig.ML"
ML_file "src/Eval_Node_Core_Struct.ML"
ML_file "src/Eval_Node_Sugar_Sig.ML"
ML_file "src/Eval_Node_Sugar_Struct.ML"
ML_file "src/Eval_Unode_Core_Sig.ML"
ML_file "src/Eval_Unode_Core_Struct.ML"
ML_file "src/Eval_Unode_Sugar_Sig.ML"
ML_file "src/Eval_Unode_Sugar_Struct.ML"
ML_file "src/Path_To_Unode_Sig.ML"
ML_file "src/Path_To_Unode_Struct.ML"
ML_file "src/Print_To_Paths_Sig.ML"
ML_file "src/Print_To_Paths_Struct.ML"
ML_file "src/Eval_Print_Core_Sig.ML"   (*Rename this to Eval_Print_Path_Core*)
ML_file "src/Eval_Print_Core_Struct.ML"
ML_file "src/Eval_Print_Sugar_Sig.ML"
ML_file "src/Eval_Print_Sugar_Struct.ML"
ML_file "src/Eval_Number_Sig.ML"
ML_file "src/Eval_Number_Struct.ML"
ML_file "src/Eval_Path_Sig.ML"
ML_file "src/Eval_Path_Struct.ML"
ML_file "src/Eval_Parameter_Sig.ML"
ML_file "src/Eval_Expression_Sig.ML"
ML_file "src/Eval_Bound_Sig.ML"
ML_file "src/Eval_Var_Sig.ML"
ML_file "src/Eval_Quantifier_Sig.ML"    (*TODO:Number*)
ML_file "src/Eval_Path_Parameter_Struct.ML"
ML_file "src/From_Parameter_To_Expression.ML"
ML_file "src/From_Expression_To_Bound.ML"
ML_file "src/From_Bound_To_Var.ML"
ML_file "src/From_Var_To_Quantifier.ML" (*This should be an ML functor.*)

ML\<open> (* from Path_Expression to Path_Var *)
structure Eval_Path_Expression = from_Parameter_to_Expression (Eval_Path_Parameter ): EVAL_EXPRESSION;
structure Eval_Path_Bound      = from_Expression_to_Bound     (Eval_Path_Expression): EVAL_BOUND;
structure Eval_Path_Var        = from_Bound_to_Var            (Eval_Path_Bound     ): EVAL_VAR;
\<close>
ML\<open> (* Path_Quantifier_Domain *)
structure Path_Quantifier_Domain:QUANTIFIER_DOMAIN =
struct

datatype qtyp  = QPath | QPrint | QNumber;
type parameter = Eval_Path_Expression.parameter;

val qtyp_to_qdomain = undefined: qtyp -> parameter list;

type path  = UN.path;
type path_to_node_table   = path Path_Table.table;
type print_to_paths_table = path list Print_Table.table;

fun mk_all_paths  pst term = Path_To_Unode.pst_n_trm_to_path_to_unode_table pst term |> Path_Table.keys: path list;
fun mk_all_prints pst term =
let
  val path_to_node_table   = Path_To_Unode.pst_n_trm_to_path_to_unode_table pst term                      : Path_To_Unode.path_to_unode_table;
  val print_to_paths_table = Print_To_Paths.path_to_unode_table_to_print_to_paths_table path_to_node_table: print_to_paths_table;
in
  Print_Table.keys print_to_paths_table
end;
end;
\<close>
ML\<open> (* from Path_Var to Path_Quantifier *)
structure Eval_Path_Quantifier = 
  from_Var_to_Quantifier(structure Eval_Var = Eval_Path_Var and Quantifier_Domain = Path_Quantifier_Domain)
\<close>
(*Global/Local? Outer/Inner?*)
ML_file "src/Eval_Inner_Sig.ML"
ML_file "src/Eval_Global_Unode_Core_Sig.ML"
ML_file "src/Eval_Global_Unode_Sugar_Sig.ML"
ML_file "src/Global_Path_To_Global_Unode_Sig.ML"
ML_file "src/Print_To_Global_Paths_Sig.ML"
ML_file "src/Eval_Global_Print_Sig.ML"
ML_file "src/Eval_Global_Modifier_Sig.ML" (*Modifier is always Global.*)
ML_file "src/Eval_Global_Path_Sig.ML"
ML_file "src/Eval_Global_Parameter_Struct.ML" (*TODO: add Inner*)
(*convert Eval_Global_Parameter_Struct to Eval_Global_Quantifier_Struct*)
ML_file "src/Eval_Outer_Sig.ML"

ML\<open>
@{term "let x = 1 in x"};
(*
  Const ("HOL.Let", "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a")
$ Const ("Groups.one_class.one", "'a")
$ Abs   ("x", "'a", Bound 0): term
*)

@{term "let x = 1 + y in x"};
(*
  Const ("HOL.Let", "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a")
$(  Const ("Groups.plus_class.plus", "'a \<Rightarrow> 'a \<Rightarrow> 'a")
  $ Const ("Groups.one_class.one", "'a")
  $ Free ("y", "'a")
 )
$ Abs   ("x", "'a", Bound 0)
*)

@{term "\<lambda>x. x + 1"};
@{term "case x of [] => y | _ \<Rightarrow> z"};
(*
  Const ("List.list.case_list", "'a \<Rightarrow> ('b \<Rightarrow> 'b list \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a")
$ Free  ("y", "'a")
$ Abs   ("a", "'b", Abs ("list", "'b list", Free ("z", "'a")))
$ Free  ("x", "'b list")
*)
@{term "case x of [] => y | w#ws \<Rightarrow> z"};
(*
  Const ("List.list.case_list", "'a \<Rightarrow> ('b \<Rightarrow> 'b list \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a")
$ Free  ("y", "'a")
$ Abs   ("w", "'b", Abs ("ws", "'b list", Free ("z", "'a")))
$ Free  ("x", "'b list"):
*)

@{term "case x of [] => y | w#ws \<Rightarrow> w"};
(*
  Const ("List.list.case_list", "'a \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a")
$ Free  ("y", "'a")
$ Abs   ("w", "'a", Abs ("ws", "'a list", Bound 1))
$ Free  ("x", "'a list")
*)

@{term "case x of True => y | _ \<Rightarrow> z"}
(*
  Const ("Product_Type.bool.case_bool", "'a \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a")
$ Free  ("y", "'a")
$ Free  ("z", "'a")
$ Free  ("x", "bool")
*)

(*
Is_Case = name has a string "case" as its sub-string
  and it it takes n arguments, (n-1)th argument's type name is part of the constant name..;
Is_Maybe_Bound_Of_Case;
*)
\<close>
find_consts name:"case_list"
find_consts name:"Product_Type.bool.case_bool"
find_theorems name:"case" name:"bool"
find_theorems name:"List.list"
thm List.list.case

datatype alpha = A | B | C | D
ML\<open>
@{term "case x of A \<Rightarrow> a | B \<Rightarrow> b"};
(*
  Const ("LiFtEr.alpha.case_alpha", "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> alpha \<Rightarrow> 'a")
$ Free  ("a", "'a")
$ Free  ("b", "'a")
$ Const ("HOL.undefined", "'a")
$ Const ("HOL.undefined", "'a")
$ Free  ("x", "alpha")
*)
\<close>

end