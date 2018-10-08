theory MiLkMaId_Test
imports (*"../MiLkMaId"*)Main
begin

lemma "True"
  apply induct
  apply induct_tac
  apply induction
  apply induct
  apply induct
  apply auto
  done
(*
ML{* (* test on utility functions *)
val _ = @{assert} (exist_related_rsimp ["TIP_prop_01.drop"]);
val _ = @{assert} (exist_related_rsimp ["identity"] = false);
val _ = @{assert} (count_recursive_consts @{term "x (take n xs) (drop n xs) = x xs (take n xs)"} = 5);
*}

ML{* (** test MiLkMaId_Assertion_Test **)
structure MiLkMaId_Assertion_Test =
struct
open MiLkMaId_Table

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
((@{term "(\<lambda>E. F E)"} |> trm_to_utrm |> utrm_to_data) =
 [{point = {name = "F", level = 2, utyp = UF},
   ancestors = [{point = {name = "E", level = 1, utyp = UAb}, nth_arg = 1}]},
  {point = {name = "0", level = 3, utyp = UB},
   ancestors = [{point = {name = "F", level = 2, utyp = UF},  nth_arg = 1},
                {point = {name = "E", level = 1, utyp = UAb}, nth_arg = 1}]},
  {point = {name = "E", level = 1, utyp = UAb},
   ancestors = []}]);

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

val _ = @{assert} ((@{term "(A B (identity G)) (D (\<lambda>E. F E))"} |> trm_to_utrm |> utrm_to_data) =
 ([{point = {name = "A", level = 1, utyp = UF},
      ancestors = []},
   {point = {name = "B", level = 2, utyp = UF},
      ancestors = [{point = {name = "A", level = 1, utyp = UF},
                    nth_arg = 1}]},
   {point = {name = "MiLkMaId_Example.identity", level = 2, utyp = UC},
     ancestors = [{point = {name = "A", level = 1, utyp = UF},
                   nth_arg = 2}]},
   {point = {name = "G", level = 3, utyp = UF},
     ancestors = [{point   = {name = "MiLkMaId_Example.identity", level = 2, utyp = UC},
                   nth_arg = 1},
                  {point   = {name = "A", level = 1, utyp = UF},
                   nth_arg = 2}]},
   {point = {name = "D", level = 2, utyp = UF},
     ancestors = [{point   = {name = "A", level = 1, utyp = UF},
                   nth_arg =  3}]},
   {point = {name = "F", level = 4, utyp = UF},
      ancestors = [{point   = {name = "E", level = 3, utyp = UAb},
                    nth_arg = 1},
                   {point   = {name = "D", level = 2, utyp = UF},
                    nth_arg = 1},
                   {point   = {name = "A", level = 1, utyp = UF},
                    nth_arg = 3}]},
   {point = {name = "0", level = 5, utyp = UB},
      ancestors = [{point   = {name = "F", level = 4, utyp = UF},
                    nth_arg = 1},
                   {point = {name = "E", level = 3, utyp = UAb},
                    nth_arg = 1},
                   {point = {name = "D", level = 2, utyp = UF},
                    nth_arg = 1},
                   {point = {name = "A", level = 1, utyp = UF},
                    nth_arg = 3}]},(*"0" (="E") is an argument of "A"!*)
   {point = {name = "E", level = 3, utyp = UAb},
      ancestors = [{point   = {name = "D", level = 2, utyp = UF},
                    nth_arg = 1},
                   {point   = {name = "A", level = 1, utyp = UF},
                    nth_arg = 3}]}]: data));

val _ = @{assert} ((@{term "(\<lambda>E. F E)"} |> trm_to_utrm |> utrm_to_data) =
 [{point     = {name = "F", level = 2, utyp = UF},
   ancestors = [{point = {name = "E", level = 1, utyp = UAb}, nth_arg = 1}]},
  {point     = {name = "0", level = 3, utyp = UB},
   ancestors = [{point = {name = "F", level = 2, utyp = UF},  nth_arg = 1},
                {point = {name = "E", level = 1, utyp = UAb}, nth_arg = 1}]},
  {point     = {name = "E", level = 1, utyp = UAb},
   ancestors = []}]);

val _ = @{assert} ((@{term "even n = odd (Suc n)"} |> trm_to_utrm |> utrm_to_data) =
 [{point = {name = "HOL.eq", level = 1, utyp = UC},
   ancestors = []},
  {point = {name = "MiLkMaId_Example.even",       level = 2, utyp = UC},
   ancestors = [{point = {name = "HOL.eq",       level = 1, utyp = UC}, nth_arg = 1}]},
  {point = {name = "n", level = 3, utyp = UF},
   ancestors = [{point = {name = "MiLkMaId_Example.even", level = 2, utyp = UC}, nth_arg = 1},
                {point = {name = "HOL.eq",                level = 1, utyp = UC}, nth_arg = 1}]},
  {point = {name = "MiLkMaId_Example.odd", level = 2, utyp = UC},
   ancestors = [{point = {name = "HOL.eq",                level = 1, utyp = UC}, nth_arg = 2}]},
  {point = {name = "Nat.Suc", level = 3, utyp = UC},
   ancestors = [{point = {name = "MiLkMaId_Example.odd",  level = 2, utyp = UC}, nth_arg = 1},
                {point = {name = "HOL.eq",                level = 1, utyp = UC}, nth_arg = 2}]},
  {point = {name = "n", level = 4, utyp = UF},
   ancestors = [{point = {name = "Nat.Suc",               level = 3, utyp = UC}, nth_arg = 1},
                {point = {name = "MiLkMaId_Example.odd",  level = 2, utyp = UC}, nth_arg = 1},
                {point = {name = "HOL.eq",                level = 1, utyp = UC}, nth_arg = 2}]}]);

val _ = @{assert} ((@{term "filter (\<lambda> _. True) xs = xs"} |> trm_to_utrm |> utrm_to_data) =
[{point = {name = "HOL.eq", level = 1, utyp = UC},
  ancestors = []},
 {point = {name = "MiLkMaId_Example.filter", level = 2, utyp = UC},
  ancestors = [{point = {name = "HOL.eq",                  level = 1, utyp = UC}, nth_arg = 1}]},
 {point = {name = "HOL.True", level = 4, utyp = UC},
  ancestors = [{point = {name = "uu_",                     level = 3, utyp = UAb}, nth_arg = 1},
               {point = {name = "MiLkMaId_Example.filter", level = 2, utyp = UC},  nth_arg = 1(*TODO: This should not be Full.*)},
               {point = {name = "HOL.eq",                  level = 1, utyp = UC},  nth_arg = 1}]},
 {point = {name = "uu_", level = 3, utyp = UAb},
  ancestors = [{point = {name = "MiLkMaId_Example.filter", level = 2, utyp = UC}, nth_arg = 1},
               {point = {name = "HOL.eq",                  level = 1, utyp = UC}, nth_arg = 1}]},
 {point = {name = "xs", level = 3, utyp = UF},
  ancestors = [{point = {name = "MiLkMaId_Example.filter", level = 2, utyp = UC}, nth_arg = 2},
               {point = {name = "HOL.eq",                  level = 1, utyp = UC}, nth_arg = 1}]},
 {point = {name = "xs", level = 2, utyp = UF},
  ancestors = [{point = {name = "HOL.eq",                  level = 1, utyp = UC}, nth_arg = 2}]}]);

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
ML{* open MiLkMaId_Table; *}

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
trm_to_utrm @{term "\<lambda> B. C B (\<lambda>E. F E B)"};
trm_to_utrm @{term "\<forall>x. P x y x"};
trm_to_utrm @{term "\<And>x. P x y x"};
*}


ML{*
trm_to_utrm @{term "\<lambda> B. C B (\<lambda>E. F E B)"};
trm_to_utrm @{term "\<forall>x. P x y x"};
trm_to_utrm @{term "\<And>x. P x y x"};
*}

ML{*
val test1 = @{term "\<lambda> B. A (C (\<lambda>D. B)) (\<lambda>E. F E B)"};
val test2 = @{term "\<And>x. P x y x"};
val _ = @{assert} ((utrm_to_trm o trm_to_utrm) test1 = test1);
val _ = @{assert} ((utrm_to_trm o trm_to_utrm) test2 = test2);
*}

lemma "True"
  apply auto
  done

lemma "True"
proof -
  show ?thesis
    by auto
qed

datatype Nat = Z | S "Nat"

fun double :: "Nat => Nat" where
  "double (Z) = Z"
| "double (S y) = S (S (double y))"

ML{*
(*The first column is for the constant name.*)
val _ = @{assert} ((mk_parameter_matrix @{context} "MiLkMaId_Test.double" |> classify <$> length)
                  = SOME 2);
*}

ML{*
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "(\<forall>x. y)"}                 = false);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "(\<forall>x. y) \<and> (\<forall>z. z)"}       = false);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "(\<lambda>x. y (\<forall>x. z)) (\<lambda>x. x)"} = false);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "True"}                   = true);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>x. x"}                 = true);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>x y. x y"}             = true);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>x y. z x y"}           = true);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>x y. x y"}             = true);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>x. z"}                 = false);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>x z. z (\<forall>x. x)"}       = false);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>x z. y z (\<forall>x. x)"}     = false);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>x z. y x (\<forall>x. w x z)"} = true);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>x z. (y x) (\<forall>x. w x z)"} = true);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>x z. (y x) (\<forall>z. w x z)"} = false);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>x z. x (\<And>z. z)"}        = false);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>P z. P (\<And>z. z)"}        = false);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>  z. P (\<And>z. z)"}        = false);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>z. (\<And>z. z)"}            = false);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>z. z \<and> True"}           = true);
@{assert} (Isabelle_Utils.are_all_de_Bruijn_indices_used @{term "\<And>z. True \<and> (\<forall>y. y z)"}   = true);
*}
*)
end