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
    Some ("func_app", QFull_Path,
      Ands
        [Is_App (Variable "func_app"),
         Is_Nth_Child_Of (Variable "func", Number 0, Variable "func_app")
         ]));

val is_constant =
  Lambdas (["constant"], Is_Cnst (Variable "constnat"));

val is_on_the_rhs_of_meta_eq =
  Lambdas (["constant"],
    Some ("meta_eq", QFull_Path,
      Ands
        [Is_Cnst (Variable "meta_eq"),
         Are_Same_Prints (Variable "meta_eq", Print "(\<equiv>)"),
         Ors
           [(*TODO*)
            ]
        ]
    )
  );

val is_recursive_equation = ()

(*
Lambdas ([("rec_const")],
 In_Some_Definitions
  (Variable "rec_const",
   ))
*)

val heuristic_1a =
Outermost (
  Ands
   [Applies (Lambdas (["x","y","z","w"], Variable "y"), [False, True, False, False]),
    True]
)
(*
Outermost (
  Applies (Lambdas (["true"], Variable "true"), [True])
)
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