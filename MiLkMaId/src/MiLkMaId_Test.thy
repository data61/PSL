theory MiLkMaId_Test
imports MiLkMaId
begin

ML{* (** test MiLkMaId_Assertion_Test **)
structure MiLkMaId_Assertion_Test =
struct
open MiLkMaId_Assertion

val test_data =
 [[true, false, true, false],
  [true, false, true, false],
  [true, false, true, true ]]: bool list list;

val _ = @{assert} (get_elem_in_matrix test_data (1,3) = SOME false);
val _ = @{assert} (get_elem_in_matrix test_data (2,3) = SOME true);
val _ = @{assert} (get_elem_in_matrix test_data (3,2) = NONE);
val _ = @{assert} (get_elem_in_matrix test_data (2,3) = SOME true);

val test_data2 =
 [[true, false, true, false],
  [true, true, false],
  [true, false, true, true ]]: bool list list;

val _ = @{assert} (is_regular_matrix test_data2 = false);

val _ = @{assert} (get_lefts @{context} "MyTrue2_def" = []); (*TODO: This is probably wrong. Double-check. *)

val _ = @{assert} (transpose test_data = SOME
  [[true,  true,  true],
   [false, false, false],
   [true,  true,  true],
   [false, false, true]]);

val test_data3 = [[], [], [], []];

val _ = @{assert} (transpose test_data3 = NONE);
val _ = @{assert} (classify test_data  = SOME [Full, Var, Full, Partial]);
val _ = @{assert} (classify test_data2 = NONE);
val _ = @{assert} (classify test_data3 = NONE);

val _ =
((@{term "(\<lambda>E. F E)"} |> uncurry |> uncurried_trm_to_data) =
 [{point = {cname = "F", level = 2, utyp = UF},  ancestors = [({cname = "E", level = 1, utyp = UAb}, Full)]},
  {point = {cname = "0", level = 3, utyp = UB},  ancestors = [({cname = "F", level = 2, utyp = UF},  Full),
                                                              ({cname = "E", level = 1, utyp = UAb}, Full)]},
  {point = {cname = "E", level = 1, utyp = UAb}, ancestors = []}]);

(* test mk_parameter_matrix_for_fun *)
val _ = @{assert} ((mk_parameter_matrix_for_fun @{context} "MiLkMaId_Example.filter" |> classify) =
  SOME [Full, Var, Full]);
val _ = @{assert} ((mk_parameter_matrix_for_fun @{context} "MiLkMaId_Example.identity" |> classify) =
  SOME [Full, Var]);

(* test are_Consts *)
val _ = @{assert} ((get_lefts @{context} "filter.simps" |> map are_Consts) =
  [[true, false, true],
   [true, false, true]]);

(* test mk_parameter_matrix_for_intros *)
val _ = @{assert} ((mk_parameter_matrix_for_intros @{context} "evn" |> classify) = 
  (SOME [Full, Full, Var]: pattern list option));

(* test mk_parameter_matrix_for_function *)
val _ = @{assert} 
  (mk_parameter_matrix_for_function @{context} "even" = [[true, true], [true, true]]);

val _ = @{assert}
 ((mk_parameter_matrix_for_function @{context} "even" |> classify) = SOME [Full, Full]);

val _ = @{assert}
 (mk_parameter_matrix_for_function @{context} "nubBy" = [[true, false, true], [true, false, true]]);

val _ = @{assert}
 ((mk_parameter_matrix_for_function @{context} "nubBy" |> classify) = SOME [Full, Var, Full]);

(* test uncurry and uncurried_trm_to_data *)
val _ = @{assert} ((@{term "(A B (identity G)) (D (\<lambda>E. F E))"} |> uncurry |> uncurried_trm_to_data) =
 ([{point = {cname = "A", level = 1, utyp = UF},
      ancestors = []},
   {point = {cname = "B", level = 2, utyp = UF},
      ancestors = [({cname = "A", level = 1, utyp = UF}, Full)]},
   {point = {cname = "MiLkMaId_Example.identity", level = 2, utyp = UC},
     ancestors = [({cname = "A", level = 1, utyp = UF}, Full)]},
   {point = {cname = "G", level = 3, utyp = UF},
     ancestors = [({cname = "MiLkMaId_Example.identity", level = 2, utyp = UC}, Full),
                  ({cname = "A", level = 1, utyp = UF}, Full)]},
   {point = {cname = "D", level = 2, utyp = UF},
     ancestors = [({cname = "A", level = 1, utyp = UF}, Full)]},
   {point = {cname = "F", level = 4, utyp = UF},
      ancestors = [({cname = "E", level = 3, utyp = UAb}, Full),
                   ({cname = "D", level = 2, utyp = UF},  Full),
                   ({cname = "A", level = 1, utyp = UF},  Full)]},
   {point = {cname = "0", level = 5, utyp = UB},
      ancestors = [({cname = "F", level = 4, utyp = UF},  Full),
                   ({cname = "E", level = 3, utyp = UAb}, Full),
                   ({cname = "D", level = 2, utyp = UF},  Full),
                   ({cname = "A", level = 1, utyp = UF},  Full)]},
   {point = {cname = "E", level = 3, utyp = UAb},
      ancestors = [({cname = "D", level = 2, utyp = UF}, Full),
                   ({cname = "A", level = 1, utyp = UF}, Full)]}]: data));

val _ = @{assert} ((@{term "(\<lambda>E. F E)"} |> uncurry |> uncurried_trm_to_data) =
 [{point = {cname = "F", level = 2, utyp = UF},  ancestors = [({cname = "E", level = 1, utyp = UAb}, Full)]},
  {point = {cname = "0", level = 3, utyp = UB},  ancestors = [({cname = "F", level = 2, utyp = UF},  Full),
                                                              ({cname = "E", level = 1, utyp = UAb}, Full)]},
  {point = {cname = "E", level = 1, utyp = UAb}, ancestors = []}]);

val _ = @{assert} ((@{term "even n = odd (Suc n)"} |> uncurry |> uncurried_trm_to_data) =
 [{point = {cname = "HOL.eq", level = 1, utyp = UC},
   ancestors = []},
  {point = {cname = "MiLkMaId_Example.even",       level = 2, utyp = UC},
   ancestors = [({cname = "HOL.eq",                level = 1, utyp = UC}, Full)]},
  {point = {cname = "n", level = 3, utyp = UF},
   ancestors = [({cname = "MiLkMaId_Example.even", level = 2, utyp = UC}, Full),
                ({cname = "HOL.eq",                level = 1, utyp = UC}, Full)]},
  {point = {cname = "MiLkMaId_Example.odd", level = 2, utyp = UC},
   ancestors = [({cname = "HOL.eq",                level = 1, utyp = UC}, Full)]},
  {point = {cname = "Nat.Suc", level = 3, utyp = UC},
   ancestors = [({cname = "MiLkMaId_Example.odd",  level = 2, utyp = UC}, Full),
                ({cname = "HOL.eq",                level = 1, utyp = UC}, Full)]},
  {point = {cname = "n", level = 4, utyp = UF},
   ancestors = [({cname = "Nat.Suc",               level = 3, utyp = UC}, Full),
                ({cname = "MiLkMaId_Example.odd",  level = 2, utyp = UC}, Full),
                ({cname = "HOL.eq",                level = 1, utyp = UC}, Full)]}]);

val _ = @{assert} ((@{term "filter (\<lambda> _. True) xs = xs"} |> uncurry |> uncurried_trm_to_data) =
[{point = {cname = "HOL.eq", level = 1, utyp = UC},
  ancestors = []},
 {point = {cname = "MiLkMaId_Example.filter", level = 2, utyp = UC},
  ancestors = [({cname = "HOL.eq",                  level = 1, utyp = UC}, Full)]},
 {point = {cname = "HOL.True", level = 4, utyp = UC},
  ancestors = [({cname = "uu_",                     level = 3, utyp = UAb}, Full),
               ({cname = "MiLkMaId_Example.filter", level = 2, utyp = UC},  Full(*TODO: This should not be Full.*)),
               ({cname = "HOL.eq",                  level = 1, utyp = UC},  Full)]},
 {point = {cname = "uu_", level = 3, utyp = UAb},
  ancestors = [({cname = "MiLkMaId_Example.filter", level = 2, utyp = UC}, Full),
               ({cname = "HOL.eq",                  level = 1, utyp = UC}, Full)]},
 {point = {cname = "xs", level = 3, utyp = UF},
  ancestors = [({cname = "MiLkMaId_Example.filter", level = 2, utyp = UC}, Full),
               ({cname = "HOL.eq",                  level = 1, utyp = UC}, Full)]},
 {point = {cname = "xs", level = 2, utyp = UF},
  ancestors = [({cname = "HOL.eq",                  level = 1, utyp = UC}, Full)]}]);

end;
*}

(** tests **)
ML{* open MiLkMaId_Assertion; *}

ML{* get_many @{context} "evn.intros" get_cncl; *}

ML{* @{term "(A B (identity G)) (D (\<lambda>E. F E))"} |> uncurry; *}

ML{*
uncurry @{term "even 1"};
uncurry @{term "\<lambda> B. C B (\<lambda>E. F E B)"};
uncurry @{term "\<forall>x. P x y x"};
uncurry @{term "\<And>x. P x y x"};
*}

end