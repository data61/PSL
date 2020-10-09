theory Test_SeLFiE
imports Main SeLFiE
begin

lemma "zip xs ys = zip xs ys"
  semantic_induct
  oops

lemma "length xs = length ys \<Longrightarrow> True"
  semantic_induct
  oops

lemma "List.list.list_all2 f xs ys \<Longrightarrow> xs = ys"
  semantic_induct
  apply(induct xs ys rule:list_all2_induct)
  oops

lemma "f x \<Longrightarrow> g y \<Longrightarrow> h z"
  semantic_induct
  assert_SeLFiE_true  test_is_a_meta_premise    [on["f x"], arb[],rule[]]
  assert_SeLFiE_false test_is_a_meta_premise    [on["h z"], arb[],rule[]]
  assert_SeLFiE_true  test_is_a_meta_conclusion [on["h z"], arb[],rule[]]
  assert_SeLFiE_true  test_is_a_meta_premise_or_below    [on["x"], arb[],rule[]]
  assert_SeLFiE_false test_is_a_meta_premise_or_below    [on["z"], arb[],rule[]]
  assert_SeLFiE_true  test_is_a_meta_conclusion_or_below [on["z"], arb[],rule[]]
  assert_SeLFiE_false test_is_a_meta_conclusion_or_below [on["x"], arb[],rule[]]
  assert_SeLFiE_true test_is_more_than [on["zs"], arb[],rule[]]
  assert_SeLFiE_false test_Is_If_Then_Else [on["zs"], arb[],rule[]]
  assert_SeLFiE_false test_Is_If_Then_Else [on["x"], arb[],rule[]]
  assert_SeLFiE_false test_Is_Case_Distinct_Of_Trm_With_A_Case [on["zs"], arb[],rule[]]
  oops

lemma "if x then True else False"
  semantic_induct
  assert_SeLFiE_true  test_Is_If_Then_Else [on["x"], arb[],rule[]]
  oops

lemma "case x of [y] \<Rightarrow> y | _ \<Rightarrow> False"
  assert_SeLFiE_true  test_Is_Case_Distinct_Of_Trm_With_A_Case [on["zs"], arb[],rule[]]
  assert_SeLFiE_false test_Is_Let_X_Be_Y_In_X [on["zs"], arb[],rule[]]
  oops

lemma "let (x1, x2) = y in z < x1"
  assert_SeLFiE_true test_Is_Let_X_Be_Y_In_X [on["zs"], arb[],rule[]]
  oops

 primrec rev :: "'a list \<Rightarrow> 'a list"
  where
  "rev []       = []" |
  "rev (x # xs) = rev xs @ [x]"

 fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
  "itrev []     ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"

lemma "itrev xs ys = rev xs @ ys"
  semantic_induct
  all_induction_heuristic      [on["xs"], arb["ys"],rule[]]
  all_generalization_heuristic [on["xs"], arb["ys"],rule[]]
  all_induction_heuristic [on["xs","ys"], arb[],rule["itrev.induct"]]
  assert_SeLFiE_true  generalize_arguments_used_in_recursion_deep [on["xs"], arb["ys"], rule[]]
  assert_SeLFiE_true  generalize_arguments_used_in_recursion_deep [on["xs"], arb[    ], rule[]](*Not great, but does not harm much.*)
  assert_SeLFiE_true  generalize_arguments_used_in_recursion [on["xs"], arb["ys"],rule[]](*It used to take 1.196s elapsed time*)
  assert_SeLFiE_false generalize_arguments_used_in_recursion [on["xs"], arb["xs"],rule[]](*It used to take 2.467s elapsed time*)
  assert_SeLFiE_false generalize_arguments_used_in_recursion [on["xs"], arb[    ],rule[]](*It used to take 0.864s elapsed time*)
  assert_SeLFiE_true  for_all_arbs_there_should_be_a_change  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_false for_all_arbs_there_should_be_a_change  [on["xs"], arb["xs"],rule[]]
  assert_SeLFiE_true  for_all_arbs_there_should_be_a_change_simplified_for_presentation [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_false for_all_arbs_there_should_be_a_change_simplified_for_presentation [on["xs"], arb["xs"],rule[]]
  assert_SeLFiE_true  for_all_arbs_there_should_be_a_change  [on["xs"], arb[],rule[]](*unfortunate result due to the universal quantifier.*)
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
  assert_SeLFiE_false rule_inversion_using_the_deepest_const [on["xs", "ys"], arb[],rule["itrev.induct"]]
  apply(induct xs arbitrary: ys) apply auto done

definition "list_reversal_eq xs ys \<equiv> itrev xs ys = rev xs @ ys"
print_theorems

lemma "list_reversal_eq xs ys"
  semantic_induct
  assert_SeLFiE_true  generalize_arguments_used_in_recursion_deep [on["xs"], arb["ys"], rule[]](*good*)
  assert_SeLFiE_false generalize_arguments_used_in_recursion_deep [on["xs"], arb[    ], rule[]](*Great*)

  semantic_induct
  apply(induct xs arbitrary: ys)
   apply(auto simp: list_reversal_eq_def)
  done

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
(*
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
*)
ML\<open>
(*
@{term "case x of B \<Rightarrow> False | A \<Rightarrow> True "};
*)
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
@{term "let ((x1,  x2),  x3) = (y1, y2) in (y1, x3)"};
(*
val it =
   Const ("HOL.Let", "'a \<times> 'b \<times> 'c \<Rightarrow> ('a \<times> 'b \<times> 'c \<Rightarrow> 'a \<times> 'c) \<Rightarrow> 'a \<times> 'c")
$ (Const ("Product_Type.Pair", "'a \<Rightarrow> 'b \<times> 'c \<Rightarrow> 'a \<times> 'b \<times> 'c")
  $ Free ("y1", "'a")
  $ Free ("y2", "'b \<times> 'c"))
$ (Const ("Product_Type.prod.case_prod", "('a \<Rightarrow> 'b \<times> 'c \<Rightarrow> 'a \<times> 'c) \<Rightarrow> 'a \<times> 'b \<times> 'c \<Rightarrow> 'a \<times> 'c")
  $ Abs ("x1", "'a",
      Const ("Product_Type.prod.case_prod", "('b \<Rightarrow> 'c \<Rightarrow> 'a \<times> 'c) \<Rightarrow> 'b \<times> 'c \<Rightarrow> 'a \<times> 'c")
     $ Abs ("x2", "'b",
         Abs ("x3", "'c",
           Const ("Product_Type.Pair", "'a \<Rightarrow> 'c \<Rightarrow> 'a \<times> 'c")
          $ Free ("y1", "'a")
          $ Bound 0
         )
       )
    )
  )

: term
Is_Let_X_Be_Y_In_Z.
Again, we have to count the number of Abs.
X_Is_Let_Z_Be_Y_In_Z.
*)
@{term "Product_Type.Pair"};
dest_funT;
\<close>

ML\<open>
@{term "let x = y in z"};
@{term "(x = y)"};
Name.skolem;
Variable.names_of;
Variable.add_fixes;
type asdf = term;
\<close>

schematic_goal "?x = ?x"
  apply(tactic \<open>fn x => (
let
  val fst_subg = try (hd o Thm.prems_of) x: term option;
  val _        = if length (Thm.prems_of x) = 0 then tracing "empty" else tracing "no empty";
  
  val _ = Option.map (tracing o Isabelle_Utils.trm_to_string @{context}) (fst_subg);

  val _ = if Utils.is_some_true (Option.map (exists_subterm (is_Var)) fst_subg)
          then tracing "Yes Var!"
          else tracing "No Var!"
  val _ = if Utils.is_some_true (Option.map (exists_subterm (is_Bound)) fst_subg)
          then tracing "Yes Bound!"
          else tracing "No Bound!"

in
  Seq.single x
end) \<close>)
  oops

lemma helper: "itrev xs ys = rev xs @ ys"
  apply (induct xs arbitrary: ys)
  by auto

lemma equivalence: "itrev xs [] = rev xs"
  by (simp add: helper)


ML\<open>
(*
 Try.tool_setup (nitpickN, (50, \<^system_option>\<open>auto_nitpick\<close>, try_nitpick))
*)
 Try.tool_setup;

Term.add_free_names @{term "f (x z) y"} [] |> rev  |> distinct (op =)
\<close>

lemma "itrev xs ys = rev xs @ ys"
  apply(induct xs)
   apply auto
  apply(subgoal_tac "\<And>xs. \<forall>ys. itrev xs ys = rev xs @ ys")
  apply fastforce
  apply(induct_tac xsa)
   apply auto
  done

end