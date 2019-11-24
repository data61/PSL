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

(* pre-processing *)
ML_file "../src/Utils.ML"
ML_file "../MeLoId/src/MeLoId_Util.ML"
ML_file "../LiFtEr/src/Matrix_Sig.ML"
ML_file "../LiFtEr/src/Matrix_Struct.ML"
ML_file "../LiFtEr/src/Matrix_Test.ML"
ML_file "src/Preprocessor/Util.ML"
ML_file "src/Preprocessor/Pattern.ML" (*TODO: We only need get_command from this module.*)
ML_file "src/Preprocessor/Unique_Node.ML"
ML_file "src/Preprocessor/Unique_Node_Test.ML"
ML_file "src/Preprocessor/Path_Table_And_Print_Table.ML"
ML_file "src/Preprocessor/Term_Table.ML"
ML_file "src/Preprocessor/Term_Table_Test.ML"
ML_file "src/Preprocessor/Dynamic_Induct.ML"

(* bootstrapping interpreter *)
ML_file "src/Interpreter/Eval_Bool.ML"
ML_file "src/Interpreter/Eval_Node.ML"
ML_file "src/Interpreter/Eval_Unode.ML"
ML_file "src/Interpreter/Eval_Path.ML"
ML_file "src/Interpreter/Eval_Print.ML"
ML_file "src/Interpreter/Eval_Number.ML"
ML_file "src/Interpreter/Eval_Parameter.ML"
ML_file "src/Interpreter/Eval_Parameter_With_Bool.ML"
ML_file "src/Interpreter/Eval_Bound.ML"
ML_file "src/Interpreter/Eval_Variable.ML"
ML_file "src/Interpreter/Eval_Quantifier.ML"(*TODO:Number*)
ML_file "src/Interpreter/Eval_Deep.ML"

ML_file "src/Interpreter/Path_To_Unode.ML"  (*The bifurcation of "inner" and "outer" starts here.*)
ML_file "src/Interpreter/Print_To_Paths.ML"
ML\<open> structure Print_To_Inner_Paths = from_Path_Table_and_Path_To_Unode_to_Print_To_Paths(Inner_Path_Table); \<close>
ML\<open> structure Print_To_Outer_Paths = from_Path_Table_and_Path_To_Unode_to_Print_To_Paths(Outer_Path_Table); \<close>

ML_file "src/Interpreter/Make_Eval_Path.ML"
ML_file "src/Interpreter/From_Path_To_Parameter.ML"
ML_file "src/Interpreter/From_Parameter_To_Parameter_With_Bool.ML"
ML_file "src/Interpreter/From_Parameter_With_Bool_To_Bound.ML"
ML_file "src/Interpreter/From_Bound_To_Variable.ML"
ML_file "src/Interpreter/Quantifier_Domain.ML"
ML_file "src/Interpreter/From_Variable_To_Quantifier.ML"

ML\<open> structure Eval_Inner_Path = make_Eval_Path (Inner_Path_To_Unode): EVAL_PATH; \<close>
ML\<open> structure Eval_Outer_Path = make_Eval_Path (Outer_Path_To_Unode): EVAL_PATH; \<close>

ML\<open> structure Eval_Inner_Parameter = from_Path_to_Parameter(Eval_Inner_Path): EVAL_PARAMETER; \<close>
ML\<open> structure Eval_Outer_Parameter = from_Path_to_Parameter(Eval_Outer_Path): EVAL_PARAMETER; \<close>

ML\<open> structure Eval_Inner_Parameter_With_Bool = from_Parameter_to_Parameter_With_Bool (Eval_Inner_Parameter): EVAL_PARAMETER_WITH_BOOL; \<close>
ML\<open> structure Eval_Outer_Parameter_With_Bool = from_Parameter_to_Parameter_With_Bool (Eval_Outer_Parameter): EVAL_PARAMETER_WITH_BOOL; \<close>

ML\<open> structure Eval_Inner_Bound = from_Parameter_With_Bool_to_Bound (Eval_Inner_Parameter_With_Bool): EVAL_BOUND; \<close>
ML\<open> structure Eval_Outer_Bound = from_Parameter_With_Bool_to_Bound (Eval_Outer_Parameter_With_Bool): EVAL_BOUND; \<close>

ML\<open> structure Eval_Inner_Variable = from_Bound_to_Variable (Eval_Inner_Bound): EVAL_VARIABLE; \<close>
ML\<open> structure Eval_Outer_Variable = from_Bound_to_Variable (Eval_Outer_Bound): EVAL_VARIABLE; \<close>

ML\<open> structure Inner_Quantifier_Domain = make_Quantifier_Domain
     (structure Print_To_Paths           = Print_To_Inner_Paths
            and Path_To_Unode            = Inner_Path_To_Unode
            and Eval_Parameter_With_Bool = Eval_Inner_Parameter_With_Bool): QUANTIFIER_DOMAIN \<close>
ML\<open> structure Outer_Quantifier_Domain = make_Quantifier_Domain
     (structure Print_To_Paths           = Print_To_Outer_Paths
            and Path_To_Unode            = Outer_Path_To_Unode
            and Eval_Parameter_With_Bool = Eval_Outer_Parameter_With_Bool): QUANTIFIER_DOMAIN \<close>

ML\<open> structure Eval_Inner_Quantifier = from_Variable_to_Quantifier(structure Eval_Variable = Eval_Inner_Variable and Quantifier_Domain = Inner_Quantifier_Domain): EVAL_QUANTIFIER; \<close>
ML\<open> structure Eval_Outer_Quantifier = from_Variable_to_Quantifier(structure Eval_Variable = Eval_Outer_Variable and Quantifier_Domain = Outer_Quantifier_Domain): EVAL_QUANTIFIER; \<close>

(*TODO: we should add the "dive-in" construct to Assert. No. to parameter.*)
ML\<open>

structure EIQ = Eval_Inner_Quantifier;
structure EOQ = Eval_Outer_Quantifier;

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

datatype outermost_expr = Outer of EOQ.expr | Dive_In     of inner_expr
     and inner_expr     = Inner of EIQ.expr | Dive_Deeper of inner_expr;

datatype expr = Out of outermost_expr | In of inner_expr;

fun convert' (Eval_Outer_Parameter_With_Bool.Bool true)  = Eval_Inner_Parameter_With_Bool.Bool true
  | convert' (Eval_Outer_Parameter_With_Bool.Bool false) = Eval_Inner_Parameter_With_Bool.Bool false
  | convert'  _                                          = error "convert failed!"

fun convert (Eval_Outer_Quantifier.Literal l) = Eval_Inner_Quantifier.Literal (convert' l)
  | convert  _ = error "convert failed!"


fun eval (pst:Proof.state) (expr:expr) (trm:term) =
  let
    fun eval_outer (Outer       outer_eq_expr ) (trm:term) = EOQ.eval trm pst outer_eq_expr |> convert
      | eval_outer (Dive_In     inner_expr    ) (trm:term) = eval_in_all_def pst inner_expr trm
    and eval_inner (Inner       inner_expr    ) (trm:term) = EIQ.eval trm pst inner_expr
      | eval_inner (Dive_Deeper inner_expr    ) (trm:term) = eval_in_all_def pst inner_expr trm
    and eval_in_all_def (pst:Proof.state) (inner_expr:inner_expr) (trm:term) =
        let
          val simp_rules = []: terms;(*TODO*)
          val subexprs   = map (eval_inner inner_expr) simp_rules: EIQ.expr list;
          val result     = EIQ.eval Term.dummy pst (EIQ.Assert (EIQ.Ands, subexprs)): EIQ.expr
        in
          result: EIQ.expr
        end
  in
    case expr of Out outermost_expr => eval_outer outermost_expr trm
               | In inner_expr => eval_inner inner_expr trm
  end;
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