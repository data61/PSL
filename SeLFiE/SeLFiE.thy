(*  Title:      PSL/SeLFeE/SeLFeE.thy
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

ML_file "../src/Utils.ML"
ML_file "../MeLoId/src/MeLoId_Util.ML"
ML_file "../LiFtEr/src/Matrix_Sig.ML"
ML_file "../LiFtEr/src/Matrix_Struct.ML"
ML_file "../LiFtEr/src/Matrix_Test.ML"
ML_file "../LiFtEr/src/LiFtEr_Util_Sig.ML"
ML_file "../LiFtEr/src/LiFtEr_Util_Struct.ML"
ML_file "../LiFtEr/src/Pattern_Sig.ML"
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
ML_file "src/Full_Path_To_FPUnode_Sig.ML"
ML_file "src/Full_Path_To_FPUnode_Struct.ML"
ML_file "src/Eval_FPUnode_Core_Sig.ML"
ML_file "src/Eval_FPUnode_Core_Struct.ML"
ML_file "src/Eval_FPUnode_Sugar_Sig.ML"
ML_file "src/Eval_FPUnode_Sugar_Struct.ML"
ML_file "src/Print_To_Full_Paths_Sig.ML"
ML_file "src/Print_To_Full_Paths_Struct.ML"
ML_file "src/Eval_Print_Core_Sig.ML"
ML_file "src/Eval_Print_Core_Struct.ML"
ML_file "src/Eval_Print_Sugar_Sig.ML"
ML_file "src/Eval_Print_Sugar_Struct.ML"
ML_file "src/Eval_Number_Sig.ML"
ML_file "src/Eval_Number_Struct.ML"
ML_file "src/Eval_Full_Path_Sig.ML"(*TODO:Is_Nth_Arg*)
ML_file "src/Eval_Full_Path_Struct.ML"
ML_file "src/Eval_Primitive_Sig.ML" (*TODO: a separate module for Is_Nth_Arg_Of?*)
ML_file "src/Eval_Primitive_Struct.ML"
ML_file "src/Eval_Parameters_Sig.ML"
ML_file "src/Eval_Parameters_Struct.ML"
ML_file "src/Eval_Bound_Sig.ML"
ML_file "src/Eval_Bound_Struct.ML"
ML_file "src/Eval_Bound_Test.ML"
ML_file "src/Eval_Var_Sig.ML"
ML_file "src/Eval_Var_Struct.ML"
ML_file "src/Eval_Quantifier_Core_Sig.ML"
ML_file "src/Eval_Quantifier_Core_Struct.ML"
ML_file "src/Eval_Modifier_Sig.ML"(*TODO:add atomic-assertion "Is_Rule_Of"*)
ML_file "src/Eval_Modifier_Struct.ML"
(*TODO: bootstrapping*)
(* Bootstrapping has to happen after introducing Eval_Modifier
 * because we need modifiers to fetch related lemmas.
 *)
ML_file "src/Eval_Surface_Sig.ML"
ML_file "src/Eval_Surface_Struct.ML"
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