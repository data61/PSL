(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website:
     https://github.com/tip-org/tools
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
theory TIP_prop_01
  imports "../../Test_Base" "../../../LiFtEr"
begin

ML{* (*samples*)
local

open LiFtEr_Util LiFtEr;
infix And;

in

val sample_assert =
 All_Ind (Trm 1,
   Some_Trm_Occ (Trm_Occ 2,
       Trm_Occ_Is_Of_Trm (Trm_Occ 2, Trm 1)
     And
       Is_Atom (Trm_Occ 2))): assrt;

val sample_induct_args1 = Ind_Mods
 {ons   = [Ind_On (Print "x")],
  arbs  = [Ind_Arb (Print "y")],
  rules = []
  }: ind_mods;

val sample_induct_args2 = Ind_Mods
 {ons   = [Ind_On (Print "x")],
  arbs  = [],
  rules = []
  }: ind_mods;

end;
*}

setup{* Apply_LiFtEr.update_assert "1" sample_assert;        *}
ML   {* Apply_LiFtEr.get_assrt @{context} "1";               *}
setup{* Apply_LiFtEr.update_ind_mod "1" sample_induct_args1; *}
setup{* Apply_LiFtEr.update_ind_mod "2" sample_induct_args2; *}
ML   {* Apply_LiFtEr.get_ind_mod @{context} "1";             *}
ML   {* Apply_LiFtEr.get_ind_mod @{context} "2";             *}

ML{* (*modifiers*)
local

open LiFtEr LiFtEr_Util;
infix And Or Imply Is_In_Trm_Loc Is_In_Trm_Str Is_Nth_Ind
  Is_In_Trm_Loc
  Is_In_Trm_Str
  Is_Typ
  Is_More_Than
  Is_Const_Of_Name
  Is_Printed_As
  Is_At_Depth
  Is_Rule_Of
  Is_An_Arg_Of;

in

val mods_for_Isaplanner_01_01 = Ind_Mods
 {ons   = [Ind_On (Print "xs")],
  arbs  = [],
  rules = [Ind_Rule "TIP_prop_01.drop.induct"]
  }: ind_mods;

val mods_for_Isaplanner_01_02 = Ind_Mods
 {ons   = [],
  arbs  = [],
  rules = [Ind_Rule "TIP_prop_01.drop.induct"]
  }: ind_mods;

val mods_for_Isaplanner_01_03 = Ind_Mods
 {ons   = [],
  arbs  = [Ind_Arb (Print "n")],
  rules = []
  }: ind_mods;

val mods_for_Isaplanner_01_04 = Ind_Mods
 {ons   = [Ind_On (Print "xs")],
  arbs  = [Ind_Arb (Print "n")],
  rules = []
  }: ind_mods;

val mods_for_Isaplanner_01_05 = Ind_Mods
 {ons   = [Ind_On (Print "xs"), Ind_On (Print "n")],
  arbs  = [],
  rules = []
  }: ind_mods;

val mods_for_Isaplanner_01_06 = Ind_Mods
 {ons   = [Ind_On (Print "TIP_prop_01.drop n xs"), Ind_On (Print "n")],
  arbs  = [],
  rules = []
  }: ind_mods;

val mods_for_Isaplanner_01_07 = Ind_Mods
 {ons   = [Ind_On (Print "TIP_prop_01.drop n xs")],
  arbs  = [Ind_Arb (Print "n")],
  rules = []
  }: ind_mods;

val mods_for_Isaplanner_01_08 = Ind_Mods
 {ons   = [Ind_On (Print "n") , Ind_On (Print "xs")],
  arbs  = [],
  rules = [Ind_Rule "TIP_prop_01.drop.induct"]
  }: ind_mods;

val mods_for_Isaplanner_01_09 = Ind_Mods
 {ons   = [Ind_On (Print "n")],
  arbs  = [],
  rules = []
  }: ind_mods;

val test_Some_Rule_n_Some_Trm_Occ_n_Is_Rule_Of =
    Some_Rule (Rule 1,
      Some_Trm_Occ (Trm_Occ 2,
        Rule 1 Is_Rule_Of  Trm_Occ 2));

val assert_should_succeed =
  Some_Rule (Rule 1,
    Some_Trm (Trm 2,
      Some_Trm_Occ (Trm_Occ 3,
          Is_Cnst (Trm_Occ 3)
        And
          (Rule 1 Is_Rule_Of Trm_Occ 3)
        And
          Trm_Occ_Is_Of_Trm (Trm_Occ 3, Trm 2))));

val test_True      = True;
val test_Not       = Not True;
val test_Or_True   = True Or (Not True);
val test_Or_False  = (Not True) Or (Not True);
val test_Some_Ind_and_Some_Trm_Occ = Some_Ind (Trm 1, True)
(* test_Print_Is *)
val test_Print_Is =
    (Some_Trm (Trm 1,
       Trm 1 Is_Printed_As "TIP_prop_01.drop"))
  And
    (Some_Trm (Trm 1,
       Trm 1 Is_Printed_As "TIP_prop_01.take"))
  And
    (Some_Trm (Trm 1,
       Trm 1 Is_Printed_As "TIP_prop_01.drop n xs"))
  And
    (Not (*Print does not contain redundant parentheses.*)
      (Some_Trm (Trm 1,
         Trm 1 Is_Printed_As "(TIP_prop_01.drop n xs)")))
  And
    (*For some reasons, Print uses a short name for "x".         *)
    (*==> Because there is no constant previously defined as "x".*)
    (Some_Trm (Trm 1,
       Trm 1 Is_Printed_As "x"))
  And
    (Some_Trm (Trm 1,
       Trm 1 Is_Printed_As "x (TIP_prop_01.take n xs) (TIP_prop_01.drop n xs)"))
  And
    (Some_Trm (Trm 1,
       Trm 1 Is_Printed_As "x (TIP_prop_01.take n xs) (TIP_prop_01.drop n xs) = xs"));

(* test_Some_Trm_Occ *)
val test_Some_Trm_Occ =
    (Some_Trm (Trm 1,
       (Some_Trm_Occ (Trm_Occ 2,
         Trm 1 Is_Printed_As "TIP_prop_01.drop"
       And
         Trm_Occ_Is_Of_Trm (Trm_Occ 2, Trm 1)))));

(* test_Print_Is_n_Is_Rule_Of *)
val test_Print_Is_n_Is_Rule_Of =
  (Some_Rule (Rule 1,
    (Some_Trm (Trm 2,
       (Some_Trm_Occ (Trm_Occ 3,
         Trm 2 Is_Printed_As "TIP_prop_01.drop"
       And
         Is_Rule_Of (Rule 1, Trm_Occ 3)))))));

val test_Some_Rule = Some_Rule (Rule 1, True);

val test_Some_Ind  = Some_Ind  (Trm 1, True);

val test_Some_Arb  = Some_Arb  (Trm 1, True);

val test_All_Ind_n_Is_Atom =
  All_Ind (Trm 1,
    Some_Trm_Occ (Trm_Occ 2,
        Trm_Occ_Is_Of_Trm (Trm_Occ 2, Trm 1)
     And
        Is_Atom (Trm_Occ 2)));

val test_All_Ind_n_Is_Atom_n_Some_Trm_Occ_Of =
  All_Ind (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 1,
      Is_Atom (Trm_Occ 2)));

val test_All_Ind_n_Is_Atom_n_All_Trm_Occ_Of =
  All_Ind (Trm 1,
    All_Trm_Occ_Of (Trm_Occ 2, Trm 1,
      Is_Atom (Trm_Occ 2)));

val test_All_Ind_n_All_Trm_Occ_n_Imply_Is_Atom =
  All_Ind (Trm 1,
    All_Trm_Occ (Trm_Occ 2,
        Trm_Occ_Is_Of_Trm (Trm_Occ 2, Trm 1)
      Imply
        Is_Atom (Trm_Occ 2)));

val test_All_Ind_n_Some_Trm_Occ_Of1 =
  All_Ind (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 1,
      Is_Atom (Trm_Occ 2)));

val test_All_Ind_n_Some_Trm_Occ_Of2 =
  All_Ind (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 1,
      Not (Is_Atom (Trm_Occ 2))));

val test_All_Ind_n_Some_Trm_Occ_Of3 =
    Some_Arb (Trm 1, True)
  Imply
    Some_Arb (Trm 1,
      All_Ind (Trm 2,
        All_Trm_Occ_Of (Trm_Occ 1, Trm 1,
          Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
            Trm_Occ 1 Is_In_Trm_Str Trm_Occ 2))));

val test_Is_At_Deepest_n_Some_Trm_Occ_Of =
  All_Ind (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 1,
      Is_At_Deepest (Trm_Occ 2)));

val test_Is_At_Deepest_n_All_Trm_Occ_Of =
  All_Ind (Trm 1,
    All_Trm_Occ_Of (Trm_Occ 2, Trm 1,
      Is_At_Deepest (Trm_Occ 2)));

val test_Is_Nth_Ind0 =
  Some_Ind (Trm 1,
    For_Numb_N (Numb 2, 0,
      Trm 1 Is_Nth_Ind Numb 2));

val test_Is_Nth_Ind1 =
  Some_Ind (Trm 1,
    For_Numb_N (Numb 2, 1,
      Trm 1 Is_Nth_Ind Numb 2));

val test_Is_Nth_Ind2 =
  Some_Ind (Trm 1,
    For_Numb_N (Numb 2, 2,
      Trm 1 Is_Nth_Ind Numb 2));

val test_Depth_Of_Trm_Occ_Is1 =
  Some_Trm (Trm 1,
      Some_Trm_Occ (Trm_Occ 2,
        For_Numb_N (Numb 3, 3,
            (Trm_Occ 2 Is_Const_Of_Name "TIP_prop_01.drop")
          And
            (Trm_Occ 2  Is_At_Depth Numb 3)
        )
    )
  );

val test_Depth_Of_Trm_Occ_Is2 =
  Some_Trm (Trm 1,
      Some_Trm_Occ (Trm_Occ 2,
        For_Numb_N (Numb 3, 4,
            (Trm_Occ 2 Is_Const_Of_Name "TIP_prop_01.drop")
          And
            (Trm_Occ 2 Is_At_Depth Numb 3)
        )
    )
  );

val test_Depth_Of_Trm_Occ_Is3 =
  Some_Trm (Trm 1,
      Some_Trm_Occ (Trm_Occ 2,
        For_Numb_N (Numb 3, 3,
            (Trm_Occ 2 Is_Const_Of_Name "TIP_prop_01.x")
          And
            (Trm_Occ 2 Is_At_Depth Numb 3)
        )
    )
  );

val test_Depth_Of_Trm_Occ_Is4 =
  Some_Trm (Trm 1,
      Some_Trm_Occ (Trm_Occ 2,
        For_Numb_N (Numb 3, 2,
            (Trm_Occ 2 Is_Const_Of_Name "TIP_prop_01.x")
          And
            (Trm_Occ 2 Is_At_Depth Numb 3)
        )
    )
  );

val test_Depth_Of_Trm_Occ_Is5 =
  Some_Trm (Trm 1,
      Some_Trm_Occ (Trm_Occ 2,
        For_Numb_N (Numb 3, 2,
            (Trm_Occ 2 Is_Const_Of_Name "HOL.eq")
          And
            (Trm_Occ 2 Is_At_Depth Numb 3)
        )
    )
  );

val test_Depth_Of_Trm_Occ_Is6 =(*Probably the depth is for function application.*)
  Some_Trm (Trm 1,
      Some_Trm_Occ (Trm_Occ 2,
        For_Numb_N (Numb 3, 1,
            (Trm_Occ 2 Is_Const_Of_Name "HOL.Trueprop")
          And
            (Trm_Occ 2 Is_At_Depth Numb 3)
        )
    )
  );

val test_Is_At_Deepest_n_Depth_Of_Trm_Occ_Is =
  Some_Trm (Trm 2,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 2,
        Is_At_Deepest (Trm_Occ 1)
      And
        For_Numb_N (Numb 3, 4,
           Trm_Occ 1 Is_At_Depth Numb 3
         )
    )
  );

val test_Is_At_Deepest =
  Some_Trm (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 1,
        Is_At_Deepest (Trm_Occ 2)
      And
        (Trm 1 Is_Printed_As "xs")));

val test_Is_At_Deepest2 =
  All_Trm (Trm 1,
      Some_Trm_Occ_Of (Trm_Occ 2, Trm 1,
          Is_At_Deepest (Trm_Occ 2)
        Imply
         ((Trm 1 Is_Printed_As "xs")
          Or
          (Trm 1 Is_Printed_As "n")
          Or
          (Trm 1 Is_Printed_As "TIP_prop_01.drop")
          Or
          (Trm 1 Is_Printed_As "TIP_prop_01.take"))));

val test_Is_At_Deepest3 =
  Some_Trm (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 1,
       (Trm 1 Is_Printed_As "TIP_prop_01.x")
      And
        Is_At_Deepest (Trm_Occ 2)));

(*TODO: fix Is_In_Prems*)
val test_Is_In_Prems1 =
  Some_Trm (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 1,
        (Trm 1 Is_Printed_As "x")
      And
        (Is_In_Prems (Trm_Occ 2))));

val test_Is_Nth_Arg_Of1 =
  Some_Trm (Trm 1,
  Some_Trm (Trm 2,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
        (Trm 1 Is_Printed_As "n")
      And
        (Trm 2 Is_Printed_As "TIP_prop_01.take")
      And
        For_Numb_N (Numb 1, 0,
          Is_Nth_Arg_Of (Trm_Occ 1, Numb 1, Trm_Occ 2))))));

val test_Is_Nth_Arg_Of2 =
  Some_Trm (Trm 1,
  Some_Trm (Trm 2,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
        (Trm 1 Is_Printed_As "n")
      And
        (Trm 2 Is_Printed_As "TIP_prop_01.take")
      And
        For_Numb_N (Numb 1, 1,
          Is_Nth_Arg_Of (Trm_Occ 1, Numb 1, Trm_Occ 2))))));

val test_Is_Recursive_Cnst_true =
  Some_Trm (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
        (Trm 1 Is_Printed_As "TIP_prop_01.take")
      And
         Is_Recursive_Cnst (Trm_Occ 1)));

val test_Is_Recursive_Cnst_false =
  Some_Trm (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
        (Trm 1 Is_Printed_As "HOL.eq")
      And
         Is_Recursive_Cnst (Trm_Occ 1)));

val test_Is_Nth_Arg_Of =
  Some_Trm (Trm 1,
  Some_Trm (Trm 2,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
      For_Numb_N (Numb 1, 0,
          (Trm 1 Is_Printed_As "n")
        And
          (Trm 2 Is_Printed_As "TIP_prop_01.take")
        And
          (Is_Nth_Arg_Of ((Trm_Occ 1), (Numb 1), (Trm_Occ 2))))))));

val test_Is_An_Arg_Of =
  Some_Trm (Trm 1,
  Some_Trm (Trm 2,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
        (Trm 1 Is_Printed_As "xs")
      And
        (Trm 2 Is_Printed_As "TIP_prop_01.take")
      And
        (Trm_Occ 1 Is_An_Arg_Of Trm_Occ 2)))));

val test_Is_An_Arg_Of2 =
  Some_Trm (Trm 1,
  Some_Trm (Trm 2,
  Some_Trm (Trm 3,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
    Some_Trm_Occ_Of (Trm_Occ 3, Trm 3,
        (Trm 1 Is_Printed_As "x")
      And
        (Trm 2 Is_Printed_As "n")
      And
        (Trm_Occ 2 Is_In_Trm_Str Trm_Occ 3)
      And
        (Trm_Occ 3 Is_An_Arg_Of Trm_Occ 1)
      ))))));

val test_Is_In_Trm_Loc =
  Some_Trm (Trm 1,
  Some_Trm (Trm 2,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
        (Trm 1 Is_Printed_As "xs")
      And
        (Trm 2 Is_Printed_As "TIP_prop_01.take n xs")
      And
        (Trm_Occ 1 Is_In_Trm_Loc Trm_Occ 2)
      ))));

val test_Pattern1 =
  Some_Trm (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
        (Trm 1 Is_Printed_As "TIP_prop_01.take")
      And
        For_Numb_N (Numb 0, 0, Pattern (Numb 0, Trm_Occ 1, All_Constr))
    ));

val test_Pattern2 =
  Some_Trm (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
        (Trm 1 Is_Printed_As "x")
      And
        For_Numb_N (Numb 0, 1, Pattern (Numb 0, Trm_Occ 1, All_Only_Var))
    ));

val test_Pattern3 =
  Some_Trm (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
        (Trm 1 Is_Printed_As "TIP_prop_01.take")
      And
        For_Numb_N (Numb 0, 1, Pattern (Numb 0, Trm_Occ 1, Mixed))));

val test_Pattern4 =
  Some_Trm (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
        (Trm 1 Is_Printed_As "TIP_prop_01.take")
      And
        For_Numb_N (Numb 0, 0, Pattern (Numb 0, Trm_Occ 1, Mixed))));

val test_Rule_n_Inds =
  Some_Rule (Rule 1, True)
Imply
  Some_Rule (Rule 1,(*TIP_prop_01.drop.induct*)
    Some_Trm (Trm 1,
       Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
         (Rule 1 Is_Rule_Of Trm_Occ 1)(*Trm_Occ 1 is "drop"*)
        And
         (All_Ind (Trm 2, (*n xs*)
            (Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
               Some_Numb (Numb 1,
                 (Is_Nth_Arg_Of (Trm_Occ 2(*n xs*), Numb 1, Trm_Occ 1(*drop*))
                And
                 (Trm 2 Is_Nth_Ind Numb 1))))))))));

val test_if_all_ind_vars_have_an_occ_at_bottom =
  All_Ind (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 1,
      Is_At_Deepest (Trm_Occ 2)));

val test_if_all_ind_vars_are_arguments_of_a_recursive_function =
  All_Ind (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 1,
       Some_Trm (Trm 3,
         Some_Trm_Occ_Of (Trm_Occ 4, Trm 3,
           Is_Recursive_Cnst (Trm_Occ 4)
         And
           (Trm_Occ 2 Is_An_Arg_Of Trm_Occ 4)))));

val test_If_all_ind_vars_are_arguments_of_a_rec_func_where_pattern_match_is_complete =
All_Ind (Trm 1,
  All_Trm_Occ_Of (Trm_Occ 2, Trm 1,
    Some_Trm (Trm 3,
      Some_Trm_Occ_Of (Trm_Occ 4, Trm 3,
        Is_Recursive_Cnst (Trm_Occ 4)
      And
        (Trm_Occ 2 Is_An_Arg_Of Trm_Occ 4)
      And
        (Some_Numb (Numb 5,
             Pattern (Numb 5, Trm_Occ 4, All_Constr)
           And
             Is_Nth_Arg_Of (Trm_Occ 2, Numb 5, Trm_Occ 4)))))));

val test_Are_Same_Numb1 = ();

val test_Are_Same_Str1 = ();

val test_Is_In_Fst_Subg = ();

val test_Pattern = ();

end;
*}

setup{* Apply_LiFtEr.update_assert  "5"  test_Some_Rule_n_Some_Trm_Occ_n_Is_Rule_Of;                                      *}
setup{* Apply_LiFtEr.update_assert  "6"  test_True;                                                                       *}
setup{* Apply_LiFtEr.update_assert  "7"  test_Not;                                                                        *}
setup{* Apply_LiFtEr.update_assert  "8"  test_Or_True;                                                                    *}
setup{* Apply_LiFtEr.update_assert  "9"  test_Or_False;                                                                   *}
setup{* Apply_LiFtEr.update_assert  "10" test_Some_Ind_and_Some_Trm_Occ;                                                  *}
setup{* Apply_LiFtEr.update_assert  "11" test_Print_Is                                                                    *}
setup{* Apply_LiFtEr.update_assert  "12" test_Some_Trm_Occ;                                                               *}
setup{* Apply_LiFtEr.update_assert  "13" test_Print_Is_n_Is_Rule_Of;                                                      *}
setup{* Apply_LiFtEr.update_assert  "14" test_Some_Rule;                                                                  *}
setup{* Apply_LiFtEr.update_assert  "15" test_Some_Arb;                                                                   *}
setup{* Apply_LiFtEr.update_assert  "16" test_Some_Ind;                                                                   *}
setup{* Apply_LiFtEr.update_assert  "17" test_All_Ind_n_Is_Atom;                                                          *}
setup{* Apply_LiFtEr.update_assert  "18" test_All_Ind_n_Is_Atom_n_Some_Trm_Occ_Of;                                        *}
setup{* Apply_LiFtEr.update_assert  "19" test_All_Ind_n_Is_Atom_n_All_Trm_Occ_Of;                                         *}
setup{* Apply_LiFtEr.update_assert  "20" test_All_Ind_n_All_Trm_Occ_n_Imply_Is_Atom;                                      *}
setup{* Apply_LiFtEr.update_assert  "21" test_All_Ind_n_Some_Trm_Occ_Of1;                                                 *}
setup{* Apply_LiFtEr.update_assert  "22" test_All_Ind_n_Some_Trm_Occ_Of2;                                                 *}
setup{* Apply_LiFtEr.update_assert  "23" test_All_Ind_n_Some_Trm_Occ_Of3;                                                 *}
setup{* Apply_LiFtEr.update_assert  "24" test_Is_At_Deepest_n_Some_Trm_Occ_Of;                                            *}
setup{* Apply_LiFtEr.update_assert  "25" test_Is_At_Deepest_n_All_Trm_Occ_Of;                                             *}
setup{* Apply_LiFtEr.update_assert  "26" test_Is_Nth_Ind0;                                                                *}
setup{* Apply_LiFtEr.update_assert  "27" test_Is_Nth_Ind1;                                                                *}
setup{* Apply_LiFtEr.update_assert  "28" test_Is_Nth_Ind2;                                                                *}
setup{* Apply_LiFtEr.update_assert  "29" test_Depth_Of_Trm_Occ_Is1;                                                       *}
setup{* Apply_LiFtEr.update_assert  "30" test_Depth_Of_Trm_Occ_Is2;                                                       *}
setup{* Apply_LiFtEr.update_assert  "31" test_Depth_Of_Trm_Occ_Is3;                                                       *}
setup{* Apply_LiFtEr.update_assert  "32" test_Depth_Of_Trm_Occ_Is4;                                                       *}
setup{* Apply_LiFtEr.update_assert  "33" test_Depth_Of_Trm_Occ_Is5;                                                       *}
setup{* Apply_LiFtEr.update_assert  "34" test_Depth_Of_Trm_Occ_Is6;                                                       *}
setup{* Apply_LiFtEr.update_assert  "35" test_Is_At_Deepest_n_Depth_Of_Trm_Occ_Is;                                        *}
setup{* Apply_LiFtEr.update_assert  "36" test_Is_At_Deepest;                                                              *}
setup{* Apply_LiFtEr.update_assert  "37" test_Is_At_Deepest2;                                                             *}
setup{* Apply_LiFtEr.update_assert  "38" test_Is_At_Deepest3;                                                             *}
setup{* Apply_LiFtEr.update_assert  "39" test_Is_In_Prems1;                                                               *}
setup{* Apply_LiFtEr.update_assert  "40" test_Is_Nth_Arg_Of1;                                                             *}
setup{* Apply_LiFtEr.update_assert  "41" test_Is_Nth_Arg_Of2;                                                             *}
setup{* Apply_LiFtEr.update_assert  "42" test_Is_Recursive_Cnst_true;                                                     *}
setup{* Apply_LiFtEr.update_assert  "43" test_Is_Recursive_Cnst_false;                                                    *}
setup{* Apply_LiFtEr.update_assert  "44" test_Is_Nth_Arg_Of;                                                              *}
setup{* Apply_LiFtEr.update_assert  "45" test_Is_An_Arg_Of;                                                               *}
setup{* Apply_LiFtEr.update_assert  "46" test_Is_An_Arg_Of2;                                                              *}
setup{* Apply_LiFtEr.update_assert  "47" test_Is_In_Trm_Loc;                                                              *}
setup{* Apply_LiFtEr.update_assert  "48" test_Pattern1;                                                                   *}
setup{* Apply_LiFtEr.update_assert  "49" test_Pattern2;                                                                   *}
setup{* Apply_LiFtEr.update_assert  "50" test_Pattern3;                                                                   *}
setup{* Apply_LiFtEr.update_assert  "51" test_Pattern4;                                                                   *}
setup{* Apply_LiFtEr.update_assert  "52" test_Rule_n_Inds;                                                                *}
setup{* Apply_LiFtEr.update_assert  "53" test_if_all_ind_vars_have_an_occ_at_bottom;                                      *}
setup{* Apply_LiFtEr.update_assert  "54" test_if_all_ind_vars_are_arguments_of_a_recursive_function;                      *}
setup{* Apply_LiFtEr.update_assert  "55" test_If_all_ind_vars_are_arguments_of_a_rec_func_where_pattern_match_is_complete;*}

setup{* Apply_LiFtEr.update_ind_mod  "3"  mods_for_Isaplanner_01_01; *}
setup{* Apply_LiFtEr.update_ind_mod  "4"  mods_for_Isaplanner_01_02; *}
setup{* Apply_LiFtEr.update_ind_mod  "5"  mods_for_Isaplanner_01_03; *}
setup{* Apply_LiFtEr.update_ind_mod  "6"  mods_for_Isaplanner_01_04; *}
setup{* Apply_LiFtEr.update_ind_mod  "7"  mods_for_Isaplanner_01_05; *}
setup{* Apply_LiFtEr.update_ind_mod  "8"  mods_for_Isaplanner_01_06; *}
setup{* Apply_LiFtEr.update_ind_mod  "9"  mods_for_Isaplanner_01_07; *}
setup{* Apply_LiFtEr.update_ind_mod  "10" mods_for_Isaplanner_01_08; *}
setup{* Apply_LiFtEr.update_ind_mod  "11" mods_for_Isaplanner_01_09; *}

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun take :: "Nat => 'a list => 'a list" where
  "take (Z)     z            = nil2"
| "take (S z2) (nil2)        = nil2"
| "take (S z2) (cons2 x2 x3) = cons2 x2 (take z2 x3)"

fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z)     z            = z"
| "drop (S z2) (nil2)        = nil2"
| "drop (S z2) (cons2 x2 x3) = drop z2 x3"

theorem property0 :
  "((x (take n xs) (drop n xs)) = xs)"
(*
  test_LiFtEr_true  1 3
  test_LiFtEr_true  4 3
*)
  assert_LiFtEr_true  5 3
  assert_LiFtEr_true  6 3
  assert_LiFtEr_false 7 3
  assert_LiFtEr_true  8 3
  assert_LiFtEr_false 9 3
  assert_LiFtEr_true  10 3
  assert_LiFtEr_true  11 3
  assert_LiFtEr_true  12 3
  assert_LiFtEr_true  13 3
  assert_LiFtEr_false 14 5
  assert_LiFtEr_true  14 4
  assert_LiFtEr_true  15 5
  assert_LiFtEr_true  15 6
  assert_LiFtEr_true  16 6
  assert_LiFtEr_true  17 7
  assert_LiFtEr_false 17 8
  assert_LiFtEr_true  18 7
  assert_LiFtEr_false 18 8
  assert_LiFtEr_true  19 7
  assert_LiFtEr_false 19 8
  assert_LiFtEr_true  20 7
  assert_LiFtEr_false 20 8
  assert_LiFtEr_true  21 7
  assert_LiFtEr_false 21 8
  assert_LiFtEr_false 22 7
  assert_LiFtEr_false 22 8
  assert_LiFtEr_true  23 9
  assert_LiFtEr_true  24 6
  assert_LiFtEr_true  24 7
  assert_LiFtEr_false 25 7
  assert_LiFtEr_true  26 8
  assert_LiFtEr_true  27 8
  assert_LiFtEr_false 28 8
  assert_LiFtEr_true  26 9
  assert_LiFtEr_false 27 9
  assert_LiFtEr_false 28 9
  assert_LiFtEr_false 29 9
  assert_LiFtEr_true  30 9
  assert_LiFtEr_true  31 9
  assert_LiFtEr_false 32 9
  assert_LiFtEr_true  33 9
  assert_LiFtEr_true  34 9
  assert_LiFtEr_true  35 9
  assert_LiFtEr_true  36 9
  assert_LiFtEr_true  37 9
  assert_LiFtEr_false 38 9
  assert_LiFtEr_true  40 1
  assert_LiFtEr_false 41 1
  assert_LiFtEr_true  42 1
  assert_LiFtEr_false 43 1
  assert_LiFtEr_true  44 1
  assert_LiFtEr_true  45 1
  assert_LiFtEr_true  46 1
  assert_LiFtEr_true  47 1
  assert_LiFtEr_true  48 1
  assert_LiFtEr_true  49 1
  assert_LiFtEr_true  50 1
  assert_LiFtEr_false 51 1
  assert_LiFtEr_true  52 10
  assert_LiFtEr_false 52 3 (*Probably it is worthwhile to check the number of arguments a function takes. Is_Func_W_Numb_Args*)
  assert_LiFtEr_true  53 3
  assert_LiFtEr_true  53 7
  assert_LiFtEr_true  54 7
  assert_LiFtEr_true  55 11
  assert_LiFtEr_false 55 3
  apply (induct n xs rule: TIP_prop_01.drop.induct)
  apply auto
  done

lemma "P x \<Longrightarrow> Q y"

  oops

lemma "(\<lambda>x . True \<or> x) = (\<lambda>x . True \<or> x)"
  oops

lemma "nth [1] = nth [1]"
(*test_Not_Fully_App*)
  oops

ML{* open Pattern;*}

ML{*
mk_pattern_matrix                       @{context} "take";
ctxt_n_name_to_patterns_of_each_param   @{context} "take";
val _ = @{assert} (is_nth_all_Only_Var                     @{context} "take" 0 |> not);
val _ = @{assert} (is_nth_all_Only_Var                     @{context} "take" 1 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_W_Var       @{context} "take" 0 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_W_Var       @{context} "take" 1 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_WO_Var      @{context} "take" 0 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_WO_Var      @{context} "take" 1 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_W_or_WO_Var @{context} "take" 0       );
val _ = @{assert} (is_nth_all_Data_Constructor_W_or_WO_Var @{context} "take" 1 |> not);
mk_pattern_matrix                       @{context} "x"  ;
ctxt_n_name_to_patterns_of_each_param   @{context} "x"  ;
val _ = @{assert} (is_nth_all_Only_Var                     @{context} "x" 0 |> not);
val _ = @{assert} (is_nth_all_Only_Var                     @{context} "x" 1       );
val _ = @{assert} (is_nth_all_Data_Constructor_W_Var       @{context} "x" 0 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_W_Var       @{context} "x" 1 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_WO_Var      @{context} "x" 0 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_WO_Var      @{context} "x" 1 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_W_or_WO_Var @{context} "x" 0       );
val _ = @{assert} (is_nth_all_Data_Constructor_W_or_WO_Var @{context} "x" 1 |> not);
*}

end
