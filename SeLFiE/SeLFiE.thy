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
  imports "PSL.PSL"
  keywords "assert_SeLFiE_true"      :: diag
  and      "assert_SeLFiE_false"     :: diag
(*
   and     "test_all_LiFtErs"   :: diag
*)
begin

find_theorems name:"wf_induct"

(* pre-processing *)
ML_file "../PSL/Utils.ML"
ML_file "../MeLoId/src/MeLoId_Util.ML"
ML_file "Pattern.ML"
ML_file "Util.ML"

ML_file "Unique_Node.ML"
ML_file "Unique_Node_Test.ML"
ML_file "Path_Table_And_Print_Table.ML"
ML_file "Term_Table.ML"
(* This Term_Table_Test works only in the interactive mode.
ML_file "Term_Table_Test.ML"
*)
ML_file "Dynamic_Induct.ML"

ML_file "Eval_Bool.ML"
ML_file "Eval_Node.ML"
ML_file "Eval_Number.ML"
ML_file "Eval_Unode.ML"
ML_file "Eval_Print.ML"

ML_file "Path_To_Unode.ML"  (*The bifurcation of "inner" and "outer" starts here.*)
ML_file "Print_To_Paths.ML"

ML\<open> structure Print_To_Inner_Paths = from_Path_Table_and_Path_To_Unode_to_Print_To_Paths(Inner_Path_Table): PRINT_TO_PATHS; \<close>
ML\<open> structure Print_To_Outer_Paths = from_Path_Table_and_Path_To_Unode_to_Print_To_Paths(Outer_Path_Table): PRINT_TO_PATHS; \<close>

ML_file "Eval_Path.ML"

ML_file "Eval_Parameter.ML"
ML_file "Eval_Parameter_With_Bool.ML"
ML_file "Quantifier_Domain.ML"
ML_file "Eval_Unary.ML"
ML_file "Eval_Multi_Arity.ML"
ML_file "Eval_Variable.ML"
ML_file "Eval_Surface.ML"

ML_file "Eval_Syntactic_Sugar.ML"
ML_file "Apply_SeLFiE.ML"

definition "func x \<equiv> x"
thm func_def
ML\<open>
val meta_eq  = @{term "True \<Longrightarrow> (x \<equiv> y)"}
val hol_eq   = @{term  "True \<Longrightarrow> (x = y)"}
val hol_imp  = @{term  "f (x \<longrightarrow> y)"}
val meta_imp = @{term  "f (x \<Longrightarrow> y)"}
\<close>
ML\<open>
val meta_eq_hol_eq = @{term "(x = y) \<Longrightarrow> (z \<equiv> w)"}
val meta_imp = @{term "1"};
val meta_imply = @{term "True \<Longrightarrow> True"};
val meta_imply = @{term "True \<Longrightarrow> (False \<equiv> x)"};
val meta_imply = @{term "(x \<Longrightarrow> y) \<Longrightarrow> (z \<longrightarrow> w)"};
val func_thm = @{thm func_def};
val func_term = Thm.cprop_of func_thm |> Thm.term_of;

val eq = @{term "1 \<equiv> 1"};
val eq2 = Isabelle_Utils.flatten_trm eq |> (fn trms => nth trms 0);
Isabelle_Utils.trm_to_string @{context} eq2
\<close>

ML_file "SeLFiE_Assertion.ML"
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
setup\<open> Apply_SeLFiE.update_assert "lifter_1"      SeLFiE_Assertion.lifter_1 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_1b"     SeLFiE_Assertion.lifter_1b \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_2"      SeLFiE_Assertion.lifter_2 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_3"      SeLFiE_Assertion.lifter_3 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_4"      SeLFiE_Assertion.lifter_4 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_5"      SeLFiE_Assertion.lifter_5 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_6"      SeLFiE_Assertion.lifter_6 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_7"      SeLFiE_Assertion.lifter_7 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_8"      SeLFiE_Assertion.lifter_8 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_9"      SeLFiE_Assertion.lifter_9 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_10"     SeLFiE_Assertion.lifter_10 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_11"     SeLFiE_Assertion.lifter_11 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_12"     SeLFiE_Assertion.lifter_12 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_13"     SeLFiE_Assertion.lifter_13 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_14"     SeLFiE_Assertion.lifter_14 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_15"     SeLFiE_Assertion.lifter_15 \<close>
setup\<open> Apply_SeLFiE.update_assert "lifter_20"     SeLFiE_Assertion.lifter_20 \<close>
setup\<open> Apply_SeLFiE.update_assert "test_dive_in"  SeLFiE_Assertion.test_dive_in \<close>
setup\<open> Apply_SeLFiE.update_assert "print_all_outer_prints"        SeLFiE_Assertion.print_all_outer_prints \<close>
setup\<open> Apply_SeLFiE.update_assert "print_all_inner_prints"        SeLFiE_Assertion.print_all_inner_prints \<close>
setup\<open> Apply_SeLFiE.update_assert "print_all_unodes"              SeLFiE_Assertion.print_all_unodes \<close>
setup\<open> Apply_SeLFiE.update_assert "print_outer_path_root"         SeLFiE_Assertion.print_outer_path_root \<close>
setup\<open> Apply_SeLFiE.update_assert "print_inner_roots"             SeLFiE_Assertion.print_inner_roots \<close>
setup\<open> Apply_SeLFiE.update_assert "print_all_inner_lhss"          SeLFiE_Assertion.print_all_inner_lhss \<close>
setup\<open> Apply_SeLFiE.update_assert "print_fst_params_of_fun_const" SeLFiE_Assertion.print_fst_params_of_fun_const \<close>

setup\<open> Apply_SeLFiE.update_assert "test_is_a_meta_premise"    SeLFiE_Assertion.test_is_a_meta_premise \<close>
setup\<open> Apply_SeLFiE.update_assert "test_is_a_meta_conclusion" SeLFiE_Assertion.test_is_a_meta_conclusion \<close>
setup\<open> Apply_SeLFiE.update_assert "test_is_a_meta_premise_or_below"    SeLFiE_Assertion.test_is_a_meta_premise_or_below \<close>
setup\<open> Apply_SeLFiE.update_assert "test_is_a_meta_conclusion_or_below" SeLFiE_Assertion.test_is_a_meta_conclusion_or_below \<close>
setup\<open> Apply_SeLFiE.update_assert "test_is_more_than" SeLFiE_Assertion.test_is_more_than \<close>

setup\<open> Apply_SeLFiE.update_assert "is_defined_recursively_on_nth"            SeLFiE_Assertion.is_defined_recursively_on_nth_outer \<close>
setup\<open> Apply_SeLFiE.update_assert "generalize_arguments_used_in_recursion"   SeLFiE_Assertion.generalize_arguments_used_in_recursion \<close>
setup\<open> Apply_SeLFiE.update_assert "test_Is_If_Then_Else"                     SeLFiE_Assertion.test_Is_If_Then_Else \<close>
setup\<open> Apply_SeLFiE.update_assert "test_Is_Subprint_Of_true"                 SeLFiE_Assertion.test_Is_Subprint_Of_true \<close>
setup\<open> Apply_SeLFiE.update_assert "test_Is_Subprint_Of_false"                SeLFiE_Assertion.test_Is_Subprint_Of_false \<close>
setup\<open> Apply_SeLFiE.update_assert "test_Is_Case_Distinct_Of_Trm_With_A_Case" SeLFiE_Assertion.test_Is_Case_Distinct_Of_Trm_With_A_Case \<close>


lemma "f x \<Longrightarrow> g y \<Longrightarrow> h z"
  assert_SeLFiE_true test_is_a_meta_premise    [on["f x"], arb[],rule[]]
  assert_SeLFiE_true test_is_a_meta_conclusion [on["h z"], arb[],rule[]]
  assert_SeLFiE_true test_is_a_meta_premise_or_below    [on["x"], arb[],rule[]]
  assert_SeLFiE_true test_is_a_meta_conclusion_or_below [on["z"], arb[],rule[]]
  assert_SeLFiE_true test_is_more_than [on["zs"], arb[],rule[]]
  assert_SeLFiE_false test_Is_If_Then_Else [on["zs"], arb[],rule[]]
  assert_SeLFiE_false test_Is_If_Then_Else [on["x"], arb[],rule[]]
  assert_SeLFiE_false test_Is_Case_Distinct_Of_Trm_With_A_Case [on["zs"], arb[],rule[]]
  oops

lemma "if x then True else False"
  assert_SeLFiE_true  test_Is_If_Then_Else [on["x"], arb[],rule[]]
  oops

lemma "case x of [] \<Rightarrow> True | _ \<Rightarrow> False"
  assert_SeLFiE_true test_Is_Case_Distinct_Of_Trm_With_A_Case [on["zs"], arb[],rule[]]
  oops

primrec rev :: "'a list \<Rightarrow> 'a list" where
  "rev []       = []" |
  "rev (x # xs) = rev xs @ [x]"
 print_theorems

 fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev []     ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"
 print_theorems

lemma "itrev xs ys = rev xs @ ys"
  assert_SeLFiE_true  generalize_arguments_used_in_recursion [on["xs"], arb["ys"],rule[]](*It used to take 1.196s elapsed time*)
  assert_SeLFiE_false generalize_arguments_used_in_recursion [on["xs"], arb["xs"],rule[]](*It used to take 2.467s elapsed time*)
  assert_SeLFiE_false generalize_arguments_used_in_recursion [on["xs"], arb[    ],rule[]](*It used to take 0.864s elapsed time*)
  assert_SeLFiE_true  is_defined_recursively_on_nth  [on["xs"], arb["ys"],rule[]](*It used to take 0.703s elapsed time*)
  assert_SeLFiE_false is_defined_recursively_on_nth  [on["ys"], arb[],rule[]](*It used to take 1.647s elapsed time*)
  assert_SeLFiE_true heuristic_1  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_2  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_3  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_4  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true heuristic_5  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_6  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_7  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_8  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_9  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_10 [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_11 [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_12 [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true heuristic_13 [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true heuristic_14 [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true test_dive_in  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true print_all_outer_prints [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true print_all_inner_prints [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true print_all_unodes       [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true print_outer_path_root  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true lifter_4  [on["xs"], arb["ys"], rule[]]
  assert_SeLFiE_true lifter_5  [on["xs","ys"], arb[], rule["itrev.induct"]]
  assert_SeLFiE_true lifter_6  [on["xs"], arb["ys"], rule[]]
  assert_SeLFiE_true lifter_7  [on["xs"], arb["ys"], rule[]]
  assert_SeLFiE_true lifter_8  [on["xs"], arb["ys"], rule[]]
  assert_SeLFiE_true lifter_9  [on["xs"], arb["ys"], rule[]]
  assert_SeLFiE_true lifter_10  [on["xs"], arb["ys"], rule[]]
  assert_SeLFiE_true lifter_11  [on["xs","ys"], arb[], rule["itrev.induct"]]
  assert_SeLFiE_true lifter_12  [on["xs"], arb["ys"], rule["itrev.induct"]]
  assert_SeLFiE_true lifter_15  [on["xs"], arb["ys"], rule["rev.induct"]]
  assert_SeLFiE_true lifter_13  [on["xs"], arb["ys"], rule["itrev.induct"]]
  assert_SeLFiE_true lifter_14  [on["xs"], arb["ys"], rule["itrev.induct"]]
  assert_SeLFiE_true print_fst_params_of_fun_const [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true print_inner_roots      [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true print_all_inner_lhss   [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true lifter_1  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true lifter_1b [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true lifter_2  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true lifter_3  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true  test_Is_Subprint_Of_true  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_false test_Is_Subprint_Of_false  [on["xs"], arb["ys"],rule["itrev.induct"]]
  apply(induct xs arbitrary: ys) apply auto done

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
@{term "case x of A \<Rightarrow> True | B \<Rightarrow> False"};
(*
   Const ("SeLFiE.alpha.case_alpha", "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> alpha \<Rightarrow> bool")
 $ Const ("HOL.True", "bool")
 $ Const ("HOL.False", "bool")
 $ Const ("HOL.undefined", "bool")
 $ Const ("HOL.undefined", "bool")
 $ Free ("x", "alpha"):
 term


  Const ("LiFtEr.alpha.case_alpha", "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> alpha \<Rightarrow> 'a")
$ Free  ("a", "'a")
$ Free  ("b", "'a")
$ Const ("HOL.undefined", "'a")
$ Const ("HOL.undefined", "'a")
$ Free  ("x", "alpha")
*)
\<close>

ML\<open>
@{term "case x of B \<Rightarrow> False | A \<Rightarrow> True "};
(*
  Const ("SeLFiE.alpha.case_alpha", "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> alpha \<Rightarrow> bool")
$ Const ("HOL.True", "bool")
$ Const ("HOL.False", "bool")
$ Const ("HOL.undefined", "bool")
$ Const ("HOL.undefined", "bool")
$ Free ("x", "alpha")
: term
*)
\<close>
declare[[ML_print_depth=100]]
ML\<open>
@{term "case x of [x] \<Rightarrow> False | [] \<Rightarrow> True | x#xs \<Rightarrow> True"};
(*
  Const ("List.list.case_list", "bool \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool")
$ Const ("HOL.True", "bool")
$ Abs ("x", "'a",
    Abs ("xs",
         "'a list",
           Const ("List.list.case_list", "bool \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool")
         $ Const ("HOL.False", "bool")
         $ Abs ("a", "'a",
             Abs ("list", "'a list",
               Const ("HOL.True", "bool")
             )
           )
         $ Bound 0
    )
  )
$ Free ("x", "'a list")
: term
*)
\<close>

ML\<open>
@{term "case x of [] \<Rightarrow> True | x#xs \<Rightarrow> False"};
(*
  Const ("List.list.case_list", "bool \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool")
$ Const ("HOL.True", "bool")
$ Abs ("x", "'a", Abs ("xs", "'a list", Const ("HOL.False", "bool")))
$ Free ("x", "'a list")
: term
*)
\<close>

ML\<open>
@{term "List.list.case_list"};
Isabelle_Utils.count_numb_of_args_of_fun_typ;

fun count_numb_of_args_of_fun_typ' (fun_typ:typ) (acc:int) = case try dest_funT fun_typ of
  NONE => acc
| SOME (_(*domain_typ*), range_typ) => count_numb_of_args_of_fun_typ' range_typ (acc + 1);

fun count_numb_of_args_of_fun_typ (typ:typ) = count_numb_of_args_of_fun_typ' typ 0;

@{term "List.null"};
dest_Const @{term "List.null"} |> snd |> dest_funT;

@{term "List.nth"};
dest_Const @{term "List.nth"} |> snd |> dest_funT |> snd |> dest_funT;

local

fun get_fist_type (fun_typ:typ) =
    let
      val (first_typ, _) = dest_funT fun_typ;
    in
      first_typ
    end;

fun remove_first_n_minus_one_typs (fun_typ:typ) (0:int) = fun_typ
  | remove_first_n_minus_one_typs (fun_typ:typ) (n:int) =
    let
      val (_, tail_fun_typ) = dest_funT fun_typ;
    in
      remove_first_n_minus_one_typs tail_fun_typ (n - 1)
    end;

in

fun fun_typ_to_typ_of_nth_arg (fun_typ:typ) (n:int) = (get_fist_type oo remove_first_n_minus_one_typs) fun_typ n;

end;

fun_typ_to_typ_of_nth_arg ((snd o dest_Const) @{term "List.list.case_list"}) 1
\<close>

ML\<open>
@{term "case x of x#xs \<Rightarrow> False | [] \<Rightarrow> True"};
(*
  Const ("List.list.case_list", "bool \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool")
$ Const ("HOL.True", "bool")
$ Abs ("x", "'a", Abs ("xs", "'a list", Const ("HOL.False", "bool")))
$ Free ("x", "'a list")
: term
*)
\<close>

ML\<open>
@{term "case [] of x#xs \<Rightarrow> False | [] \<Rightarrow> True"};
(*
  Const ("List.list.case_list", "bool \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool")
$ Const ("HOL.True", "bool")
$ Abs ("x", "'a", Abs ("xs", "'a list", Const ("HOL.False", "bool")))
$ Const ("List.list.Nil", "'a list"): term
*)
\<close>

ML\<open>
@{term "case f x of x#xs \<Rightarrow> False | [] \<Rightarrow> True"};
(*
  Const ("List.list.case_list", "bool \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool")
$ Const ("HOL.True", "bool")
$ Abs ("x", "'a", Abs ("xs", "'a list", Const ("HOL.False", "bool")))
$ (Free ("f", "'b \<Rightarrow> 'a list") $ Free ("x", "'b")): term
*);
\<close>

ML\<open>
@{term "if x then True else False"}
\<close>

end