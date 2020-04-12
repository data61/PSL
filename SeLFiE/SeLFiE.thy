(*  Title:      PSL/SeLFiE/SeLFiE.thy
 *  Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
 *
 * Examples about rev and itrev were originally developed by Tobias Nipkow and Gerwin Klein
 * as Isabelle theory files accompanying their book "Concrete Semantics".
 *
 * The PDF file of the book and the original Isabelle theory files are available
 * at the following website:
 *   http://concrete-semantics.org/index.html
 *
 * MeLoId: Machine Learning Induction for Isabelle/HOL, and
 * LiFtEr: Logical Feature Extractor.
 * SeLFiE: Semantic Logical Feature Extractor.
 *)
theory SeLFiE
  imports "../PSL"
  keywords "assert_SeLFiE"      :: diag
(*
   and     "test_all_LiFtErs"   :: diag
*)
begin

find_theorems name:"wf_induct"

(* pre-processing *)
ML_file "../src/Utils.ML"
ML_file "../MeLoId/src/MeLoId_Util.ML"
ML_file "src/Preprocessor/Pattern.ML"
ML_file "src/Preprocessor/Util.ML"

ML_file "src/Preprocessor/Unique_Node.ML"
ML_file "src/Preprocessor/Unique_Node_Test.ML"
ML_file "src/Preprocessor/Path_Table_And_Print_Table.ML"
ML_file "src/Preprocessor/Term_Table.ML"
ML_file "src/Preprocessor/Term_Table_Test.ML"
ML_file "src/Preprocessor/Dynamic_Induct.ML"

ML_file "src/Interpreter/Eval_Bool.ML"
ML_file "src/Interpreter/Eval_Node.ML"
ML_file "src/Interpreter/Eval_Number.ML"
ML_file "src/Interpreter/Eval_Unode.ML"
ML_file "src/Interpreter/Eval_Print.ML"

ML_file "src/Interpreter/Path_To_Unode.ML"  (*The bifurcation of "inner" and "outer" starts here.*)
ML_file "src/Interpreter/Print_To_Paths.ML"

ML\<open> structure Print_To_Inner_Paths = from_Path_Table_and_Path_To_Unode_to_Print_To_Paths(Inner_Path_Table): PRINT_TO_PATHS; \<close>
ML\<open> structure Print_To_Outer_Paths = from_Path_Table_and_Path_To_Unode_to_Print_To_Paths(Outer_Path_Table): PRINT_TO_PATHS; \<close>
ML_file "src/Interpreter/Eval_Path.ML"

ML_file "src/Interpreter/Eval_Induct_Argument.ML"
ML_file "src/Interpreter/Eval_Parameter.ML"
ML_file "src/Interpreter/Eval_Parameter_With_Bool.ML"
ML_file "src/Interpreter/Quantifier_Domain.ML"
ML_file "src/Interpreter/Eval_Unary.ML"
ML_file "src/Interpreter/Eval_Multi_Arity.ML"
ML_file "src/Interpreter/Eval_Variable.ML"
ML_file "src/Interpreter/Eval_Surface.ML"

ML_file "src/Interpreter/Eval_Syntactic_Sugar.ML"
ML_file "src/Interface/Apply_SeLFiE.ML"

definition "func x \<equiv> x"
thm func_def
ML\<open>
val meta_imp = @{term "1"}
val func_thm = @{thm func_def};
val func_term = Thm.cprop_of func_thm |> Thm.term_of;

val eq = @{term "1 \<equiv> 1"};
val eq2 = Isabelle_Utils.flatten_trm eq |> (fn trms => nth trms 0);
Isabelle_Utils.trm_to_string @{context} eq2
\<close>

ML_file "src/Interface/SeLFiE_Assertion.ML"
ML\<open> Apply_SeLFiE.activate (); \<close>

setup\<open> Apply_SeLFiE.update_assert "heuristic_1" SeLFiE_Assertion.heuristic_1 \<close>
setup\<open> Apply_SeLFiE.update_assert "heuristic_2" SeLFiE_Assertion.heuristic_2 \<close>
setup\<open> Apply_SeLFiE.update_assert "heuristic_3" SeLFiE_Assertion.heuristic_3 \<close>
setup\<open> Apply_SeLFiE.update_assert "heuristic_4" SeLFiE_Assertion.heuristic_4 \<close>
setup\<open> Apply_SeLFiE.update_assert "heuristic_5" SeLFiE_Assertion.heuristic_5 \<close>
setup\<open> Apply_SeLFiE.update_assert "heuristic_6" SeLFiE_Assertion.heuristic_6 \<close>
setup\<open> Apply_SeLFiE.update_assert "heuristic_7" SeLFiE_Assertion.heuristic_7 \<close>
setup\<open> Apply_SeLFiE.update_assert "heuristic_8" SeLFiE_Assertion.heuristic_8 \<close>
setup\<open> Apply_SeLFiE.update_assert "heuristic_9" SeLFiE_Assertion.heuristic_9 \<close>
setup\<open> Apply_SeLFiE.update_assert "heuristic_10" SeLFiE_Assertion.heuristic_10 \<close>
setup\<open> Apply_SeLFiE.update_assert "heuristic_11" SeLFiE_Assertion.heuristic_11 \<close>
setup\<open> Apply_SeLFiE.update_assert "heuristic_12" SeLFiE_Assertion.heuristic_12 \<close>
setup\<open> Apply_SeLFiE.update_assert "heuristic_13" SeLFiE_Assertion.heuristic_13 \<close>
setup\<open> Apply_SeLFiE.update_assert "heuristic_14" SeLFiE_Assertion.heuristic_14 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_1"  SeLFiE_Assertion.lifter_1 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_1b" SeLFiE_Assertion.lifter_1b \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_2"  SeLFiE_Assertion.lifter_2 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_3"  SeLFiE_Assertion.lifter_3 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_4"  SeLFiE_Assertion.lifter_4 \<close>
setup\<open> Apply_SeLFiE.update_assert "test_dive_in"  SeLFiE_Assertion.test_dive_in \<close>
setup\<open> Apply_SeLFiE.update_assert "print_all_outer_prints"  SeLFiE_Assertion.print_all_outer_prints \<close>
setup\<open> Apply_SeLFiE.update_assert "print_all_inner_prints"  SeLFiE_Assertion.print_all_inner_prints \<close>
setup\<open> Apply_SeLFiE.update_assert "print_all_unodes"        SeLFiE_Assertion.print_all_unodes \<close>
setup\<open> Apply_SeLFiE.update_assert "print_outer_path_root"   SeLFiE_Assertion.print_outer_path_root \<close>
setup\<open> Apply_SeLFiE.update_assert "print_inner_roots"       SeLFiE_Assertion.print_inner_roots \<close>
setup\<open> Apply_SeLFiE.update_assert "print_all_inner_lhss"    SeLFiE_Assertion.print_all_inner_lhss \<close>

primrec rev :: "'a list \<Rightarrow> 'a list" where
  "rev []       = []" |
  "rev (x # xs) = rev xs @ [x]"
 print_theorems

 fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev []     ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"
 print_theorems

lemma "itrev xs ys = rev xs @ ys"
  assert_SeLFiE heuristic_1  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE heuristic_2  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE heuristic_3  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE heuristic_4  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE heuristic_5  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE heuristic_6  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE heuristic_7  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE heuristic_8  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE heuristic_9  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE heuristic_10 [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE heuristic_11 [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE heuristic_12 [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE heuristic_13 [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE heuristic_14 [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE test_dive_in  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE print_all_outer_prints [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE print_all_inner_prints [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE print_all_unodes       [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE print_outer_path_root  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE print_inner_roots      [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE print_all_inner_lhss   [on["xs"], arb["ys"],rule["itrev.induct"]]

  assert_SeLFiE lifter_1  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE lifter_1b [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE lifter_2  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE lifter_3  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE lifter_4  [on["xs"], arb["ys"],rule["itrev.induct"]]


  apply(induct xs arbitrary: ys) apply auto done

ML\<open>
@{term "itrev"};
@{term "(@)"};
\<close>

(* auxiliary stuff *)
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