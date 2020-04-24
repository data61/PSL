(*  Title:      Smart_Induct/src/LiFtEr_Heuristics.thy
    Author:     Yutaka Nagashima, CIIRC, CTU, University of Innsbruck
*)
structure LiFtEr_Heuristics =
struct
(* Example assertions in LiFtEr. *)

local

open LiFtEr_Util LiFtEr;
infix And Imply Is_An_Arg_Of Is_Rule_Of Is_Nth_Ind Is_In_Trm_Loc Is_In_Trm_Str;
infix Or Trm_Occ_Is_Of_Trm Is_Const_Of_Name Is_Printed_As Is_At_Depth Is_Defined_With;

in

(* heuristic_1 *)
val all_ind_term_are_non_const_wo_syntactic_sugar =
 All_Ind (Trm 1,
   Some_Trm_Occ (Trm_Occ 1,
       (Trm_Occ 1 Trm_Occ_Is_Of_Trm Trm 1)
     And
       Not (Is_Cnst (Trm_Occ 1)))): assrt;

(* heuristic_2 *)
val all_ind_terms_have_an_occ_as_variable_at_bottom =
 All_Ind (Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
       Is_Atom (Trm_Occ 1)
     Imply
       Is_At_Deepest (Trm_Occ 1)));

(* heuristic_3 *)
val all_ind_vars_are_arguments_of_a_recursive_function =
Some_Trm (Trm 1,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    All_Ind (Trm 2,
      Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
         (((Trm_Occ 1 Is_Defined_With Fun)
          Or
           (Trm_Occ 1 Is_Defined_With Function)
          Or
           (Trm_Occ 1 Is_Defined_With Inductive)
          Or
           (Trm_Occ 1 Is_Defined_With  Primrec))
         And
           (Trm_Occ 2 Is_An_Arg_Of Trm_Occ 1))))));

(* heuristic_4 *)
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

(* heuristic_5 *)
val all_ind_terms_are_arguments_of_a_const_with_a_related_rule_in_order =
 Some_Rule (Rule 1, True)
Imply
 Some_Rule (Rule 1,
  Some_Trm (Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    (Rule 1 Is_Rule_Of Trm_Occ 1)
    And
    (All_Ind (Trm 2,
     (Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
       Some_Numb (Numb 1,
         Is_Nth_Arg_Of (Trm_Occ 2, Numb 1, Trm_Occ 1)
        And
        (Trm 2 Is_Nth_Ind Numb 1)))))))));

(* heuristic_6 and heuristic_18 *)
val ind_is_not_arb =
All_Arb (Trm 1,
 Not (Some_Ind (Trm 2,
  Are_Same_Trm (Trm 1, Trm 2))));

(* heuristic_7 *)
val at_least_one_recursive_term =
  Some_Trm_Occ (Trm_Occ 1,
    (Trm_Occ 1 Is_Defined_With Fun)
   Or
    (Trm_Occ 1 Is_Defined_With Function)
   Or
    (Trm_Occ 1 Is_Defined_With Inductive)
   Or
    (Trm_Occ 1 Is_Defined_With Primrec))
Imply
  Some_Trm (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
      Some_Trm (Trm 2,
        Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
          Some_Ind (Trm 3,
            Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
                ((Trm_Occ 1 Is_Defined_With Fun)
                Or
                 (Trm_Occ 1 Is_Defined_With Function)
                Or
                 (Trm_Occ 1 Is_Defined_With Inductive)
                Or
                 (Trm_Occ 1 Is_Defined_With Primrec))
               And
                 (Trm_Occ 2 Is_An_Arg_Of Trm_Occ 1)
               And
                  Are_Same_Trm (Trm 2, Trm 3)))))));

(* heuristic_8 *)
val at_least_one_on = Some_Ind (Trm 1, True);

(* heuristic_9 *)
val one_on_is_deepest =
  Some_Ind (Trm 1, True)
Imply
  Some_Ind (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1, Is_At_Deepest (Trm_Occ 1)));

(* heuristic_10 *)
val ons_and_arbs_share_func =
All_Ind (Trm 1,
 All_Arb (Trm 2,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
    Some_Trm_Occ (Trm_Occ 3,
      ((Trm_Occ 1) Is_An_Arg_Of (Trm_Occ 3)
     And
      ((Trm_Occ 2) Is_An_Arg_Of (Trm_Occ 3))))))));

(* heuristic_11 *)
val all_args_of_rule_as_ons =
 Some_Rule (Rule 1, True)
Imply
 Some_Rule (Rule 1,
   Some_Trm_Occ (Trm_Occ 1,
     (Rule 1 Is_Rule_Of Trm_Occ 1)
    And
      All_Trm_Occ (Trm_Occ 2,
        (Trm_Occ 2 Is_An_Arg_Of Trm_Occ 1)
       Imply
        Some_Ind (Trm 2,
          Trm_Occ 2 Trm_Occ_Is_Of_Trm Trm 2
))
));

(* heuristic_12 *)
val arb_share_parent_with_ind =
 Some_Arb (Trm 1, True)
Imply
 Some_Arb (Trm 1,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
   Some_Ind (Trm 2,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
     Some_Trm_Occ (Trm_Occ 3,
       (Trm_Occ 1 Is_An_Arg_Of Trm_Occ 3)
      And
       (Trm_Occ 2 Is_An_Arg_Of Trm_Occ 3)
)))));

(* heuristic_13 and heuristic_19 *)
val no_arb_should_be_at_the_same_loc_as_ind =
 Some_Arb (Trm 1, True)
Imply
  (All_Arb (Trm 1,
   Not
    (Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
     (Some_Trm (Trm 3,
      (Some_Trm_Occ_Of (Trm_Occ 31, Trm 3,
       (Some_Numb (Numb 4,
         (Is_Nth_Arg_Of (Trm_Occ 1, Numb 4, Trm_Occ 31))
        And
         (Some_Ind (Trm 2,
          (Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
           (Some_Trm_Occ_Of (Trm_Occ 32, Trm 3,
            (Is_Nth_Arg_Of (Trm_Occ 2, Numb 4, Trm_Occ 32))
))))))))))))))));

(* heuristic_14 *)
val only_one_rule =
 Some_Rule (Rule 1, True)
Imply
  (All_Rule (Rule 1,
    All_Rule (Rule 2,
     (Are_Same_Rule (Rule 1, Rule 2)))));

(* heuristic_15 *)
val inner_rec_const_rule =
 Some_Rule (Rule 1,
   Some_Trm_Occ (Trm_Occ 1,
      ((Trm_Occ 1 Is_Defined_With Fun)
      Or
       (Trm_Occ 1 Is_Defined_With Function)
      Or
       (Trm_Occ 1 Is_Defined_With Inductive)
      Or
       (Trm_Occ 1 Is_Defined_With Primrec))
    And
     Some_Trm_Occ (Trm_Occ 2,
        ((Trm_Occ 2 Is_Defined_With Fun)
        Or
         (Trm_Occ 2 Is_Defined_With Function)
        Or
         (Trm_Occ 2 Is_Defined_With Inductive)
        Or
         (Trm_Occ 2 Is_Defined_With Primrec))
      And
       Are_Diff_Str (Trm_Occ 1, Trm_Occ 2)
      And
       Some_Trm_Occ (Trm_Occ 3,
        (Trm_Occ 3 Is_An_Arg_Of Trm_Occ 1)
        And
        (Trm_Occ 2 Is_In_Trm_Loc Trm_Occ 3)
        And
         All_Ind (Trm 4,
          All_Trm_Occ_Of (Trm_Occ 4, Trm 4,
           Is_Atom (Trm_Occ 4)))))))
Imply
 Some_Rule (Rule 1,
   Some_Trm_Occ (Trm_Occ 1,
      ((Trm_Occ 1 Is_Defined_With Fun)
      Or
       (Trm_Occ 1 Is_Defined_With Function)
      Or
       (Trm_Occ 1 Is_Defined_With Inductive)
      Or
       (Trm_Occ 1 Is_Defined_With Primrec))
    And
     Some_Trm_Occ (Trm_Occ 2,
        ((Trm_Occ 2 Is_Defined_With Fun)
        Or
         (Trm_Occ 2 Is_Defined_With Function)
        Or
         (Trm_Occ 2 Is_Defined_With Inductive)
        Or
         (Trm_Occ 2 Is_Defined_With Primrec))
      And
       Some_Trm_Occ (Trm_Occ 3,
        (Trm_Occ 3 Is_An_Arg_Of Trm_Occ 1)
        And
        (Trm_Occ 2 Is_In_Trm_Loc Trm_Occ 3)
        And
        (Rule 1 Is_Rule_Of Trm_Occ 2)))));

(* heuristic_16 *)
val no_ind_at_nth_arg_if_two_occ_of_recs =
 (Not (Some_Rule (Rule 1, True))
 And
  Some_Ind (Trm 1, True))
Imply
 Not
 (Some_Trm (Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
     ((Trm_Occ 1 Is_Defined_With Fun)
     Or
      (Trm_Occ 1 Is_Defined_With Function)
     Or
      (Trm_Occ 1 Is_Defined_With Inductive)
     Or
      (Trm_Occ 1 Is_Defined_With Primrec))
    And
      Some_Trm (Trm 2,
        Are_Same_Trm (Trm 1, Trm 2)
       And
       (Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
          Not (Are_At_Same_Loc (Trm_Occ 1, Trm_Occ 2))
         And
          Some_Numb (Numb 3,
           Some_Trm_Occ (Trm_Occ 3,
            (Is_Nth_Arg_Of (Trm_Occ 1, Numb 3, Trm_Occ 4)(*FIXME? What is Trm_Occ 4? It should be Trm_Occ 3? Trm_occ 1 and Trm_occ 4 should be swapped?*)
           And
             Is_Nth_Arg_Of (Trm_Occ 2, Numb 3, Trm_Occ 4)
           And
            Some_Ind (Trm 5,
              ((Trm_Occ 1 Trm_Occ_Is_Of_Trm Trm 5)
              And
               (Trm_Occ 1 Trm_Occ_Is_Of_Trm Trm 5))(*FIXME? The first argument should be Trm_Occ2?*)
))))))))));

(* heuristic_17 *)
val no_diff_var_at_same_pos_for_diff_occ_of_rec =
 Not (Some_Rule (Rule 1, True))
Imply
 ((Some_Ind (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
     Some_Trm (Trm 2,
      Some_Trm_Occ_Of (Trm_Occ 21, Trm 2,
        ((Trm_Occ 21 Is_Defined_With Fun)
        Or
         (Trm_Occ 21 Is_Defined_With Function)
        Or
         (Trm_Occ 21 Is_Defined_With Inductive)
        Or
         (Trm_Occ 21 Is_Defined_With Primrec))
       And
        Some_Numb (Numb 5,
          Is_Nth_Arg_Of(Trm_Occ 1, Numb 5, Trm_Occ 21)
         And
          Some_Trm_Occ_Of (Trm_Occ 22, Trm 2,
            Some_Numb (Numb 6,
              (Trm_Occ 21 Is_At_Depth Numb 6)
             And
              (Trm_Occ 21 Is_At_Depth Numb 6))
           And
            Some_Trm (Trm 3,
              Not (Are_Same_Trm (Trm 1, Trm 3))
             And
              Some_Trm_Occ_Of (Trm_Occ 3, Trm 3,
               Is_Nth_Arg_Of (Trm_Occ 3, Numb 5, Trm_Occ 22))))))))))
 Imply
  Some_Ind (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
     Some_Trm (Trm 2,
      Some_Trm_Occ_Of (Trm_Occ 21, Trm 2,
        ((Trm_Occ 21 Is_Defined_With Fun)
        Or
         (Trm_Occ 21 Is_Defined_With Function)
        Or
         (Trm_Occ 21 Is_Defined_With Inductive)
        Or
         (Trm_Occ 21 Is_Defined_With Primrec))
       And
        Some_Numb (Numb 5,
          Is_Nth_Arg_Of(Trm_Occ 1, Numb 5, Trm_Occ 21)
         And
          Pattern (Numb 5, Trm_Occ 21, All_Constr)(*!*)
         And
          Some_Trm_Occ_Of (Trm_Occ 22, Trm 2,
            Some_Numb (Numb 6,
              (Trm_Occ 21 Is_At_Depth Numb 6)
             And
              (Trm_Occ 21 Is_At_Depth Numb 6))
           And
            Some_Trm (Trm 3,
              Not (Are_Same_Trm (Trm 1, Trm 3))
             And
              Some_Trm_Occ_Of (Trm_Occ 3, Trm 3,
               Is_Nth_Arg_Of (Trm_Occ 3, Numb 5, Trm_Occ 22)
               And
                Pattern (Numb 5, Trm_Occ 22, All_Constr))))))))))(*!*)


(* heuristic_20 *)
val rule_inversion_on_premise =
 (  Some_Rule (Rule 1, True)
  And
    Some_Trm_Occ (Trm_Occ 1,
       (Trm_Occ 1 Is_Defined_With Inductive)
      And
       (Is_In_Prems (Trm_Occ 1))
    )
  )
Imply
  Some_Rule (Rule 2,
    Some_Trm_Occ (Trm_Occ 2,
       (Trm_Occ 2 Is_Defined_With Inductive)
      And
       (Is_In_Prems (Trm_Occ 2))
      And
       (Rule 2 Is_Rule_Of Trm_Occ 2)
    )
  );

(* heuristic_21 *)
val rule_inversion_on_a_member_if_inductive_set_in_a_premise =
 (  Some_Rule (Rule 1, True)
  And
    Some_Trm_Occ (Trm_Occ 1,
       (Trm_Occ 1 Is_Defined_With Inductive_Set)
      And
       (Is_In_Prems (Trm_Occ 1))
      And
        Some_Trm_Occ (Trm_Occ 2,
            (Trm_Occ 2 Is_Const_Of_Name "Set.member")
          And
            Some_Trm_Occ (Trm_Occ 3, (*RHS of \<in>*)
              For_Numb_N (Numb 1, 1,
                  Is_Nth_Arg_Of (Trm_Occ 3, Numb 1, Trm_Occ 2)
                And
                  (Trm_Occ 1 Is_In_Trm_Loc  Trm_Occ 3)
                And
                  Some_Trm_Occ (Trm_Occ 4, (*LHS of \<in>*)
                    For_Numb_N (Numb 2, 0,
                        Is_Nth_Arg_Of (Trm_Occ 4, Numb 2, Trm_Occ 2)
                      And
                        (
                          (Is_Free (Trm_Occ 4) Or Is_Bound (Trm_Occ 4) Or Is_Var (Trm_Occ 4))
(*
                        Or
                          Some_Trm_Occ (Trm_Occ 5, (*a variable in LHS of \<in>*)
                              (Trm_Occ 5 Is_In_Trm_Loc  Trm_Occ 4)
                            And
                              (Is_Free (Trm_Occ 5) Or Is_Bound (Trm_Occ 5) Or Is_Var (Trm_Occ 5))
                          )
*)
                        )
                    )
                  )
              )
            )
        )
    )
  )
Imply
 (  (*Some_Rule (Rule 1, True)
  And*)
    Some_Trm_Occ (Trm_Occ 1,
       (Trm_Occ 1 Is_Defined_With Inductive_Set)
      And
       Some_Rule (Rule 1, (Rule 1 Is_Rule_Of Trm_Occ 1))
      And
       (Is_In_Prems (Trm_Occ 1))
      And
        Some_Trm_Occ (Trm_Occ 2,
            (Trm_Occ 2 Is_Const_Of_Name "Set.member")
          And
            Some_Trm_Occ (Trm_Occ 3, (*RHS of \<in>*)
              For_Numb_N (Numb 1, 1,
                  Is_Nth_Arg_Of (Trm_Occ 3, Numb 1, Trm_Occ 2)
                And
                  (Trm_Occ 1 Is_In_Trm_Loc  Trm_Occ 3)
                And
                  Some_Trm_Occ (Trm_Occ 4, (*LHS of \<in>*)
                    For_Numb_N (Numb 2, 0,
                        Is_Nth_Arg_Of (Trm_Occ 4, Numb 2, Trm_Occ 2)
                      And
                        (
                          (  Is_Free (Trm_Occ 4) Or Is_Bound (Trm_Occ 4) Or Is_Var (Trm_Occ 4)
                           (*Imply*)And
                             Some_Ind (Trm 4, Trm_Occ 4 Trm_Occ_Is_Of_Trm Trm 4)
                           )
                        And (*!*)(*because of Imply*)
(*
                          Some_Trm_Occ (Trm_Occ 5, (*a variable in LHS of \<in>*)
                              (
                                (Trm_Occ 5 Is_In_Trm_Loc  Trm_Occ 4)
                              And
                                (Is_Free (Trm_Occ 5) Or Is_Bound (Trm_Occ 5) Or Is_Var (Trm_Occ 5))
                              )
                            Imply
                              Some_Ind (Trm 5, Trm_Occ 5 Trm_Occ_Is_Of_Trm Trm 5)
                          )
*)True
                        )
                    )
                  )
              )
            )
        )
    )
  );

end;

end;