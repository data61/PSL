(*  Title:      PSL/SeLFiE/src/Interface/SeLFiE_Assertion.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** signature: SELFIE_ASSERTION ***)

(*** structure: SeLFiE_Assertion ***)
structure SeLFiE_Assertion =
struct

open SeLFiE_Util;
open Eval_Syntactic_Sugar;

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
   Unode_Has_Print (Variable "x", Print "ys")));

val heuristic_10 =
 Not
  (Some ("x", QOuter_Path,
   Unode_Has_Print (Variable "x", Print "yss")));

val heuristic_11 =
 (Some ("x", QOuter_Path,
   Unode_Has_Print (Variable "x", Print "itrev")));

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
(*
All ("xs", QInd,
  Some_Of ("xs_occ", Variable "xs",
*)
Some ("xs_occ", QOuter_Path,
(*
      Is_Atomic (Variable "xs_occ")
    Imply
*)
(*
      Is_At_Deepest_In_A_Location (Variable "xs_occ")
*)
  Are_In_Same_Location (Variable "xs_occ", Variable "xs_occ")
  );
(*
    Not (Is_Cnst (Variable "var_occ"))));
*)
(*
Outermost (
 (Some ("hol_eq", QFull_Path,
  Unode_Has_Print (Variable "hol_eq", Print "SeLFiE.itrev"))));
*)
(*
  Alls ([("ind_trm", QPrint)],
    True)
*)
(*
  Alls ([("ind_trm", QPrint)],
    Somes ([("ind_trm_occ", QFull_Path)],
      Ands
        [(*Unode_Has_Print (Variable "ind_trm_occ", Variable "ind_trm"),
         Not (Is_Cnst (Variable "ind_trm_occ"))*)
         True
         ]
)));
*)



end;