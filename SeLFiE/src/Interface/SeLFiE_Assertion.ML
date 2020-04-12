(*  Title:      PSL/SeLFiE/src/Interface/SeLFiE_Assertion.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** signature: SELFIE_ASSERTION ***)

(*** structure: SeLFiE_Assertion ***)
structure SeLFiE_Assertion =
struct

open SeLFiE_Util;
open Eval_Syntactic_Sugar;
open Pattern;

val is_meta_equation =
  Lambdas (["meta_eq"], Are_Same_Prints (Variable "meta_eq", Print "(\<equiv>)"));

(*is_function returns true  for "f" when applied to "f x y"
  is_function returns false for "x" when applied to "f x y"
  is_function returns false for "c" when applied to "c"*)
val is_function =
  Lambdas (["func"],
    Some ("func_app", QOuter_Path,
      Ands
        [Is_App (Variable "func_app"),
         Is_Nth_Child_Of (Variable "func", Number 0, Variable "func_app")
         ]));

val is_constant =
  Lambdas (["constant"], Is_Cnst (Variable "constnat"));

val is_on_the_rhs_of_meta_eq =
  Lambdas (["constant"],
    Some ("meta_eq", QOuter_Path,
      Ands
        [Is_Cnst (Variable "meta_eq"),
         Are_Same_Prints (Variable "meta_eq", Print "(\<equiv>)"),
         Ors
           [(*TODO*)
            ]
        ]
    )
  );

val heuristic_1 =
  Ands
   [Applies (Lambdas (["x","y","z","w"], Variable "y"), [False, True, False, False]),
    True]

val heuristic_2 =
 Not (Some ("x", QRule, True))

val heuristic_3 =
 All ("x", QInd,
  Some ("x", QOuter_Print, True))

val heuristic_4 =
 (Some ("x", QRule, True))

val heuristic_5 =
 (Some ("x", QInd, True))

val heuristic_6 =
 (Some ("x", QArb, True))

val heuristic_7 =
 (All ("x", QOuter_Print,
   Are_Same_Prints (Print "SeLFiE.itrev", Print "SeLFiE.itrev")))

val heuristic_8 =
 Applies (
  Lambdas (["x"], 
           Are_Same_Prints (Variable "x", Print "SeLFiE.itrev")),
  [Print "SeLFiE.itrev"]);

val heuristic_9 =
 (Some ("x", QOuter_Path,
   Unode_Has_Print (Variable "x", Print "ys")));;

val heuristic_10 =
 Not
  (Some ("x", QOuter_Path,
   Unode_Has_Print (Variable "x", Print "yss")));

val heuristic_11 =
 (Some ("x", QOuter_Path,
   Unode_Has_Print (Variable "x", Print "SeLFiE.itrev")));

val heuristic_12 =
  Some ("induct", QInd,
    Are_Same_Prints (Variable "induct", Print "xs"));

val heuristic_13 =
  Not (
    Some ("induct", QArb,
      Are_Same_Prints (Variable "induct", Print "xs")));

infix And Or Imply;

val heuristic_14 =
  Some ("var_occ2", QOuter_Path,
  Some ("var_occ1", QOuter_Path,
  Some ("var_occ", QOuter_Path,
    Has_Same_Prnt_As (Variable "var_occ2", Variable "var_occ")
  )));

val lifter_1 =
All ("induct", QInd,
  Some ("var_occ", QOuter_Path,
      Not (Is_Cnst (Variable "var_occ"))
    And
      Unode_Has_Print (Variable "var_occ", Variable "induct")
));

val lifter_1b =
All ("induct", QInd,
  Some_Of ("var_occ", Variable "induct",
      Not (Is_Cnst (Variable "var_occ"))));

val lifter_2 =
All ("xs", QInd,
  Some_Of ("xs_occ", Variable "xs",
      Is_Atomic (Variable "xs_occ")
    Imply
      Is_At_Deepest_In_A_Location (Variable "xs_occ")
  ));

val lifter_3 =
Some ("func_occ", QOuter_Path,
  All ("ind", QInd,
    Some_Of ("ind_occ", Variable "ind",
        Is_An_Arg_Of (Variable "ind_occ", Variable "func_occ")
      And
        Ors
         [
          Is_Defined_With (Variable "func_occ", Command Primrec),
          Is_Defined_With (Variable "func_occ", Command Fun),
          Is_Defined_With (Variable "func_occ", Command Function),
          Is_Defined_With (Variable "func_occ", Command Inductive)
          ])));

val lifter_4 =
All("printed", QOuter_Print, Are_Same_Prints (Variable "printed", Variable "printed") And True);

val nth_arg_on_lfs_is_const_or_app =
 Lambdas (["nth"], Debug_Non_Path_Literal (Variable "func"));

val help_test_dive_in =
 Lambdas (["func"],
  All ("printed", QInner_Print,
   Debug_Non_Path_Literal (Variable "printed")));

(*
 Debug_Non_Path_Literal (Variable "func"))
*)
(*
  All("printed", QInner_Print,
    Are_Same_Prints (Variable "printed", Variable "printed")))
*);

val test_dive_in =
All ("func_occ", QOuter_Path,
    Is_Defined_With (Variable "func_occ", Command Fun)
  Imply
    All ("func", QOuter_Print,
        Unode_Has_Print (Variable "func_occ", Variable "func")
      Imply
        In_All_Definitions (Variable "func_occ", help_test_dive_in, [Variable "func"]))
  )

val print_all_inner_prints_helper =
Lambdas (["outer_print"],
 All ("printed", QInner_Print,
  Debug_Non_Path_Literal (Variable "printed")));

val print_all_inner_prints =
  All ("outer_path", QOuter_Path,
    In_All_Definitions (Variable "outer_path", print_all_inner_prints_helper, [Print "outer_print"]));

val print_all_outer_prints =
All ("printed", QOuter_Print,
  Debug_Non_Path_Literal (Variable "printed"));

val print_all_unodes =
All ("unode", QOuter_Path,
  Debug_Print_Unode (Variable "unode"));

val print_outer_path_root =
All ("outpath", QOuter_Path,
    Is_Root_In_A_Location (Variable "outpath")
  Imply
    Debug_Print_Unode (Variable "outpath"));

val print_inner_path_root_help =
Lambdas (["outer_print"],
  Some ("inner_path", QInner_Path,
      Is_Root_In_A_Location (Variable "inner_path")
    And
      Debug_Print_Unode (Variable "inner_path")));

val print_inner_roots =
All ("outer_path", QOuter_Path,
  Some ("outer_print", QOuter_Print,
      Unode_Has_Print (Variable "outer_path", Variable "outer_print")
    And
      In_All_Definitions (Variable "outer_path", print_inner_path_root_help, [Variable "outer_print"])));

val help_print_inner_lhs =
Lambdas (["outer_print"],
  Some ("root_path", QInner_Path,
      Is_Root_In_A_Location (Variable "root_path")
    And
      Some ("lfs_path", QInner_Path,
          Is_Nth_Child_Of (Variable "lfs_path", Number 1, Variable "root_path")
        And
          Debug_Print_Unode (Variable "lfs_path"))));

val print_all_inner_lhss =
All ("outer_path", QOuter_Path,
  Some ("outer_print", QOuter_Print,
      Unode_Has_Print (Variable "outer_path", Variable "outer_print")
    And
      In_All_Definitions (Variable "outer_path", help_print_inner_lhs, [Variable "outer_print"])));

val help_print_n_plus_one_th_param =
Lambdas (["number"],
  Some ("root_path", QInner_Path,
      Is_Root_In_A_Location (Variable "root_path")
    And
      Some ("lfs_path", QInner_Path,
          Is_Nth_Child_Of (Variable "lfs_path", Number 1, Variable "root_path")
        And
          Some ("fst_param", QInner_Path,
              Is_N_Plus_One_th_Child_Of (Variable "fst_param", Variable "number", Variable "lfs_path")
            And
              Debug_Print_Unode (Variable "fst_param")
          )
      )
  )
);

val print_fst_params_of_fun_const =
Some ("outer_path", QOuter_Path,
  Some ("outer_print", QOuter_Print,
    Ands [
      Unode_Has_Print (Variable "outer_path", Variable "outer_print"),
      Is_Defined_With (Variable "outer_path", Command Fun),
      In_All_Definitions (Variable "outer_path", help_print_n_plus_one_th_param, [Number 0])
      ]));



(*
val all_ind_vars_are_arguments_of_a_rec_func_where_pattern_match_is_complete =
 Not (Some_Rule (Rule 1, True))
Imply
 Some_Trm (Trm 1,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    ((Trm_Occ 1 Is_Defined_With Fun)
    Or
     (Trm_Occ 1 Is_Defined_With  Function)
    Or
     (Trm_Occ 1 Is_Defined_With Inductive)
    Or
     (Trm_Occ 1 Is_Defined_With  Primrec))
   And
    All_Ind (Trm 2,
      Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
       Some_Numb (Numb 1,
         Pattern (Numb 1, Trm_Occ 1, All_Constr)
        And
         Is_Nth_Arg_Of (Trm_Occ 2, Numb 1, Trm_Occ 1))))));
*)

end;