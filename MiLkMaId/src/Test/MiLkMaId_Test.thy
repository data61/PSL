theory MiLkMaId_Test
imports "../MiLkMaId"
begin

ML{* (* test on utility functions *)
val _ = @{assert} (exist_related_rsimp ["TIP_prop_01.drop"]);
val _ = @{assert} (exist_related_rsimp ["identity"] = false);
val _ = @{assert} (count_recursive_consts @{term "x (take n xs) (drop n xs) = x xs (take n xs)"} = 5);
*}

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
 [{point = {cname = "F", level = 2, utyp = UF},  ancestors = [({cname = "E", level = 1, utyp = UAb}, 1)]},
  {point = {cname = "0", level = 3, utyp = UB},  ancestors = [({cname = "F", level = 2, utyp = UF},  1),
                                                              ({cname = "E", level = 1, utyp = UAb}, 1)]},
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
val _ = @{assert} ((mk_parameter_matrix_for_inductive @{context} "evn" |> classify) = 
  (SOME [Full, Full, Var]: pattern list option));

(* test mk_parameter_matrix_for_function *)
val _ = @{assert} 
  (mk_parameter_matrix_for_function @{context} "even" = [[true, true], [true, true]]);

val _ = @{assert}
 ((mk_parameter_matrix_for_function @{context} "even" |> classify) = SOME [Full, Full]);

val _ = @{assert} (mk_parameter_matrix_for_function @{context} "nubBy" = [[true, false, true], [true, false, true]]);

val _ = @{assert}
 ((mk_parameter_matrix_for_function @{context} "nubBy" |> classify) = SOME [Full, Var, Full]);

(* test uncurry and uncurried_trm_to_data *)

val _ = @{assert} ((@{term "(A B (identity G)) (D (\<lambda>E. F E))"} |> uncurry |> uncurried_trm_to_data) =
 ([{point = {cname = "A", level = 1, utyp = UF},
      ancestors = []},
   {point = {cname = "B", level = 2, utyp = UF},
      ancestors = [({cname = "A", level = 1, utyp = UF}, 1)]},
   {point = {cname = "MiLkMaId_Example.identity", level = 2, utyp = UC},
     ancestors = [({cname = "A", level = 1, utyp = UF}, 2)]},
   {point = {cname = "G", level = 3, utyp = UF},
     ancestors = [({cname = "MiLkMaId_Example.identity", level = 2, utyp = UC}, 1),
                  ({cname = "A", level = 1, utyp = UF}, 2)]},
   {point = {cname = "D", level = 2, utyp = UF},
     ancestors = [({cname = "A", level = 1, utyp = UF}, 3)]},
   {point = {cname = "F", level = 4, utyp = UF},
      ancestors = [({cname = "E", level = 3, utyp = UAb}, 1),
                   ({cname = "D", level = 2, utyp = UF},  1),
                   ({cname = "A", level = 1, utyp = UF},  3)]},
   {point = {cname = "0", level = 5, utyp = UB},
      ancestors = [({cname = "F", level = 4, utyp = UF},  1),
                   ({cname = "E", level = 3, utyp = UAb}, 1),
                   ({cname = "D", level = 2, utyp = UF},  1),
                   ({cname = "A", level = 1, utyp = UF},  3)]},(*"0" (="E") is an argument of "A"!*)
   {point = {cname = "E", level = 3, utyp = UAb},
      ancestors = [({cname = "D", level = 2, utyp = UF}, 1),
                   ({cname = "A", level = 1, utyp = UF}, 3)]}]: data));

val _ = @{assert} ((@{term "(\<lambda>E. F E)"} |> uncurry |> uncurried_trm_to_data) =
 [{point = {cname = "F", level = 2, utyp = UF},  ancestors = [({cname = "E", level = 1, utyp = UAb}, 1)]},
  {point = {cname = "0", level = 3, utyp = UB},  ancestors = [({cname = "F", level = 2, utyp = UF},  1),
                                                              ({cname = "E", level = 1, utyp = UAb}, 1)]},
  {point = {cname = "E", level = 1, utyp = UAb}, ancestors = []}]);

val _ = @{assert} ((@{term "even n = odd (Suc n)"} |> uncurry |> uncurried_trm_to_data) =
 [{point = {cname = "HOL.eq", level = 1, utyp = UC},
   ancestors = []},
  {point = {cname = "MiLkMaId_Example.even",       level = 2, utyp = UC},
   ancestors = [({cname = "HOL.eq",                level = 1, utyp = UC}, 1)]},
  {point = {cname = "n", level = 3, utyp = UF},
   ancestors = [({cname = "MiLkMaId_Example.even", level = 2, utyp = UC}, 1),
                ({cname = "HOL.eq",                level = 1, utyp = UC}, 1)]},
  {point = {cname = "MiLkMaId_Example.odd", level = 2, utyp = UC},
   ancestors = [({cname = "HOL.eq",                level = 1, utyp = UC}, 2)]},
  {point = {cname = "Nat.Suc", level = 3, utyp = UC},
   ancestors = [({cname = "MiLkMaId_Example.odd",  level = 2, utyp = UC}, 1),
                ({cname = "HOL.eq",                level = 1, utyp = UC}, 2)]},
  {point = {cname = "n", level = 4, utyp = UF},
   ancestors = [({cname = "Nat.Suc",               level = 3, utyp = UC}, 1),
                ({cname = "MiLkMaId_Example.odd",  level = 2, utyp = UC}, 1),
                ({cname = "HOL.eq",                level = 1, utyp = UC}, 2)]}]);

val _ = @{assert} ((@{term "filter (\<lambda> _. True) xs = xs"} |> uncurry |> uncurried_trm_to_data) =
[{point = {cname = "HOL.eq", level = 1, utyp = UC},
  ancestors = []},
 {point = {cname = "MiLkMaId_Example.filter", level = 2, utyp = UC},
  ancestors = [({cname = "HOL.eq",                  level = 1, utyp = UC}, 1)]},
 {point = {cname = "HOL.True", level = 4, utyp = UC},
  ancestors = [({cname = "uu_",                     level = 3, utyp = UAb}, 1),
               ({cname = "MiLkMaId_Example.filter", level = 2, utyp = UC},  1(*TODO: This should not be Full.*)),
               ({cname = "HOL.eq",                  level = 1, utyp = UC},  1)]},
 {point = {cname = "uu_", level = 3, utyp = UAb},
  ancestors = [({cname = "MiLkMaId_Example.filter", level = 2, utyp = UC}, 1),
               ({cname = "HOL.eq",                  level = 1, utyp = UC}, 1)]},
 {point = {cname = "xs", level = 3, utyp = UF},
  ancestors = [({cname = "MiLkMaId_Example.filter", level = 2, utyp = UC}, 2),
               ({cname = "HOL.eq",                  level = 1, utyp = UC}, 1)]},
 {point = {cname = "xs", level = 2, utyp = UF},
  ancestors = [({cname = "HOL.eq",                  level = 1, utyp = UC}, 2)]}]);

(* test check_suffix *)
(* "evn" defined with the "inductive" keyword *)
val _ = @{assert} (check_suffix @{context} "evn" suffix_for_inductive);
val _ = @{assert} (check_suffix @{context} "evn" suffix_for_fun = false);
val _ = @{assert} (check_suffix @{context} "evn" suffix_for_function = false);
val _ = @{assert} (check_suffix @{context} "evn" suffix_for_primrec = false);
 
(* "fib" defined with the "fun" keyword *)
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.fib" suffix_for_inductive = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.fib" suffix_for_fun);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.fib" suffix_for_function = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.fib" suffix_for_primrec = false);

(* "even" defined with the "function" keyword *)
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.even" suffix_for_inductive = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.even" suffix_for_fun = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.even" suffix_for_function);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.even" suffix_for_primrec = false);

(* "odd" defined with the "function" keyword *)
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.odd" suffix_for_inductive = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.odd" suffix_for_fun = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.odd" suffix_for_function);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.odd" suffix_for_primrec = false);

(* "filter" defined with the "fun" keyword *)
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.filter" suffix_for_inductive = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.filter" suffix_for_fun);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.filter" suffix_for_function = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.filter" suffix_for_primrec = false);

(* "nubBy" defined with the "fun" keyword *)
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.nubBy" suffix_for_inductive = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.nubBy" suffix_for_fun = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.nubBy" suffix_for_function);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.nubBy" suffix_for_primrec = false);

(* test get_command *)
val _ = @{assert} (get_command "MiLkMaId_Example.MyTrue1"  @{context} = Unknown);
val _ = @{assert} (get_command "MiLkMaId.append2"          @{context} = Unknown (*Because it is not really defined in that file.*));
val _ = @{assert} (get_command "MiLkMaId_Example.append2"  @{context} = Primrec);
val _ = @{assert} (get_command "MiLkMaId_Example.evn"      @{context} = Inductive);
val _ = @{assert} (get_command "MiLkMaId_Example.fib"      @{context} = Fun);
val _ = @{assert} (get_command "MiLkMaId_Example.even"     @{context} = Function);
val _ = @{assert} (get_command "MiLkMaId_Example.odd"      @{context} = Function);
val _ = @{assert} (get_command "MiLkMaId_Example.filter"   @{context} = Fun);
val _ = @{assert} (get_command "MiLkMaId_Example.nubBy"    @{context} = Function);
val _ = @{assert} (get_command "MiLkMaId_Example.even_set" @{context} = Inductive);(*FIXME: It should be Inductive_Set.*)

end;
*}

(** tests **)
ML{* open MiLkMaId_Assertion; *}

ML{*

mk_parameter_matrix @{context} "append2";
mk_parameter_matrix @{context} "evn";
mk_parameter_matrix @{context} "fib";
mk_parameter_matrix @{context} "even";
mk_parameter_matrix @{context} "odd";
mk_parameter_matrix @{context} "filter";
mk_parameter_matrix @{context} "nubBy";
mk_parameter_matrix @{context} "even_set";
 *}


ML{*
uncurry @{term "\<lambda> B. C B (\<lambda>E. F E B)"};
uncurry @{term "\<forall>x. P x y x"};
uncurry @{term "\<And>x. P x y x"};
*}


ML{*
uncurry @{term "\<lambda> B. C B (\<lambda>E. F E B)"};
uncurry @{term "\<forall>x. P x y x"};
uncurry @{term "\<And>x. P x y x"};
*}

lemma "True"
  apply auto
  done

lemma "True"
proof -
  show ?thesis
    by auto
qed

end