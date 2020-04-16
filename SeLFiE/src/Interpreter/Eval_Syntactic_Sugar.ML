(*  Title:      PSL/SeLFiE/src/Interpreter/Syntactic_Sugar.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** signature: EVAL_SYNTACTIC_SUGAR ***)
signature EVAL_SYNTACTIC_SUGAR =
sig

datatype out_or_in = Out | Inn;

datatype assert =
(*bool*)
  True
| False
| Not      of assert
| And      of assert * assert
| Or       of assert * assert
| Nor      of assert * assert
| Imply    of assert * assert
| Ands     of assert list
| Ors      of assert list
(*Eval_Node*)
| Is_Cnst         of assert
| Is_Free         of assert
| Is_Var          of assert
| Is_Bound        of assert
| Is_Lambda       of assert
| Is_App          of assert
| Is_Defined_With of assert * assert
| Is_Rule_Of_Node of assert * assert
(*Eval_Unode*)
| Has_Same_Prnt_As       of assert * assert
| Is_In_Trm_Prnt         of assert * assert
| Is_Deeper_Than         of assert * assert
| Is_Shallower_Than      of assert * assert
| Is_Path_Above          of assert * assert
| Is_Same_Path_As        of assert * assert
| Is_Nth_Child           of assert * assert
| Is_N_Plus_One_th_Child of assert * assert
(*Eval_Print*)
| Are_Same_Prints   of assert * assert
| Is_Nth_Induct     of assert * assert
| Is_Nth_Arbitrary  of assert * assert
| Is_Induct         of assert
| Is_Arbitrary      of assert
| Is_Rule           of assert
| Is_Rule_Of_Print  of assert * assert
(*Eval_Path*)
| Unode_Has_Print        of assert * assert
| Is_In_Subgoal          of assert
| Is_In_Chained_Fact     of assert
| Is_In_Nth_Subgoal      of assert * assert
| Is_In_Nth_Chained_Fact of assert * assert
(*Eval_Number*)
| Are_Same_Number of assert * assert
| Is_Less_Than    of assert * assert
(*Parameter*)
| Print   of string
| Number  of int
| Command of Pattern.command
(*expr*)
| Variable            of string
| Lambdas             of strings * assert
| Applies             of assert  * assert list
| All                 of string * SeLFiE_Util.qtyp * assert
| Some                of string * SeLFiE_Util.qtyp * assert
| In_All_Definitions  of assert * assert * assert list
| In_Some_Definitions of assert * assert * assert list
(*Syntactic Sugar*)
| Is_Atomic                          of assert
| Have_Different_Prnts               of assert * assert
| Is_Path_Below                      of assert * assert
| Is_Parent_Of                       of assert * assert
| Is_Child_Of                        of assert * assert
| Is_Nth_Child_Of                    of assert * assert * assert
| Is_N_Plus_One_th_Child_Of          of assert * assert * assert
| Is_Nth_Child_Or_Below_Nth_Child_Of of assert * assert * assert
| Is_An_Arg_Of                       of assert * assert
| Is_An_Arg_Or_Below_Arg_Of          of assert * assert
| Is_Nth_Arg_Of                      of assert * assert * assert
| Is_Nth_Arg_Or_Below_Nth_Arg_Of     of assert * assert * assert
| Are_In_Same_Location               of assert * assert
| Is_Deeper_Than_In_Same_Location    of assert * assert
| Is_Shallower_Than_In_Same_Location of assert * assert
| Is_Root_In_A_Location              of assert
| Is_At_Deepest_In_A_Location        of assert
| Is_Less_Than_Or_Equal              of assert * assert
| Is_More_Than_Or_Equal              of assert * assert
| Is_More_Than                       of assert * assert
| Is_A_Meta_Premise                  of assert
| Is_A_Meta_Premise_Or_Below         of assert
| Is_A_Meta_Conclusion               of assert
| Is_A_Meta_Conclusion_Or_Below      of assert
| Some_Of                            of string * assert * assert
| All_Of                             of string * assert * assert
(*debug*)
| Debug_Non_Path_Literal             of assert
| Debug_Print_Unode                  of assert
| Debug_Space;

val eval: Proof.state -> SeLFiE_Util.induct_arguments -> assert -> assert;

end;

(*** Eval_Syntactic_Sugar ***)
structure Eval_Syntactic_Sugar: EVAL_SYNTACTIC_SUGAR =
struct

datatype out_or_in = Out | Inn;

datatype assert =
(*bool*)
  True
| False
| Not      of assert
| And      of assert * assert
| Or       of assert * assert
| Nor      of assert * assert
| Imply    of assert * assert
| Ands     of assert list
| Ors      of assert list
(*Eval_Node*)
| Is_Cnst         of assert
| Is_Free         of assert
| Is_Var          of assert
| Is_Bound        of assert
| Is_Lambda       of assert
| Is_App          of assert
| Is_Defined_With of assert * assert
| Is_Rule_Of_Node of assert * assert
(*Eval_Unode*)
| Has_Same_Prnt_As       of assert * assert
| Is_In_Trm_Prnt         of assert * assert
| Is_Deeper_Than         of assert * assert
| Is_Shallower_Than      of assert * assert
| Is_Path_Above          of assert * assert
| Is_Same_Path_As        of assert * assert
| Is_Nth_Child           of assert * assert
| Is_N_Plus_One_th_Child of assert * assert
(*Eval_Print*)
| Are_Same_Prints   of assert * assert
| Is_Nth_Induct     of assert * assert
| Is_Nth_Arbitrary  of assert * assert
| Is_Induct         of assert
| Is_Arbitrary      of assert
| Is_Rule           of assert
| Is_Rule_Of_Print  of assert * assert
(*Eval_Path*)
| Unode_Has_Print        of assert * assert
| Is_In_Subgoal          of assert
| Is_In_Chained_Fact     of assert
| Is_In_Nth_Subgoal      of assert * assert
| Is_In_Nth_Chained_Fact of assert * assert
(*Eval_Number*)
| Are_Same_Number of assert * assert
| Is_Less_Than    of assert * assert
(*Parameter*)
| Print   of string
| Number  of int
| Command of Pattern.command
(*expr*)
| Variable            of string
| Lambdas             of strings * assert
| Applies             of assert  * assert list
| All                 of string * SeLFiE_Util.qtyp * assert
| Some                of string * SeLFiE_Util.qtyp * assert
| In_All_Definitions  of assert * assert * assert list
| In_Some_Definitions of assert * assert * assert list
(*Syntactic Sugar*)
| Is_Atomic                          of assert
| Have_Different_Prnts               of assert * assert
| Is_Path_Below                      of assert * assert
| Is_Parent_Of                       of assert * assert
| Is_Child_Of                        of assert * assert
| Is_Nth_Child_Of                    of assert * assert * assert
| Is_N_Plus_One_th_Child_Of          of assert * assert * assert
| Is_Nth_Child_Or_Below_Nth_Child_Of of assert * assert * assert
| Is_An_Arg_Of                       of assert * assert
| Is_An_Arg_Or_Below_Arg_Of          of assert * assert
| Is_Nth_Arg_Of                      of assert * assert * assert
| Is_Nth_Arg_Or_Below_Nth_Arg_Of     of assert * assert * assert
| Are_In_Same_Location               of assert * assert
| Is_Deeper_Than_In_Same_Location    of assert * assert
| Is_Shallower_Than_In_Same_Location of assert * assert
| Is_Root_In_A_Location              of assert
| Is_At_Deepest_In_A_Location        of assert
| Is_Less_Than_Or_Equal              of assert * assert
| Is_More_Than_Or_Equal              of assert * assert
| Is_More_Than                       of assert * assert
| Is_A_Meta_Premise                  of assert
| Is_A_Meta_Premise_Or_Below         of assert
| Is_A_Meta_Conclusion               of assert
| Is_A_Meta_Conclusion_Or_Below      of assert
| Some_Of                            of string * assert * assert
| All_Of                             of string * assert * assert
(*debug*)
| Debug_Non_Path_Literal             of assert
| Debug_Print_Unode                  of assert
| Debug_Space;

structure ES = Eval_Surface;
structure SU = SeLFiE_Util;

fun get_new_name' acc []                    = acc
  | get_new_name' acc (Variable name::vars) = get_new_name' (acc ^ name) vars
  | get_new_name' acc (_            ::xs  ) = get_new_name' (acc ^ "nonvar") xs;

 (*For atomic assertions, we have to avoid a name collisions with the arguments to the assertion only.*)
val get_new_name = get_new_name' "A";

infix And Or Imply Is_In_Nth_Subgoal Is_In_Nth_Chained_Fact;

fun convert_pair loc pair = Utils.map_pair (convert loc) pair
and convert_list loc list = map (convert loc) list
and
  (*bool*)
    convert _    True              = ES.True
  | convert _    False             = ES.False
  | convert loc (Not    ass)       = ES.Not   (convert loc ass)
  | convert loc (ass1 And ass2)    = ES.And   (convert_pair loc (ass1, ass2))
  | convert loc (ass1 Or ass2)     = ES.Or    (convert_pair loc (ass1, ass2))
  | convert loc (Nor   pair)       = ES.Nor   (convert_pair loc pair)
  | convert loc (prem Imply concl) = ES.Imply (convert_pair loc (prem, concl))
  | convert loc (Ands  list)       = ES.Ands  (convert_list loc list)
  | convert loc (Ors   list)       = ES.Ors   (convert_list loc list)
  (*Eval_Node*)
  | convert loc (Is_Cnst         ass)   = ES.Is_Cnst         (convert loc ass)
  | convert loc (Is_Free         ass)   = ES.Is_Free         (convert loc ass)
  | convert loc (Is_Var          ass)   = ES.Is_Var          (convert loc ass)
  | convert loc (Is_Bound        ass)   = ES.Is_Bound        (convert loc ass)
  | convert loc (Is_Lambda       ass)   = ES.Is_Lambda       (convert loc ass)
  | convert loc (Is_App          ass)   = ES.Is_App          (convert loc ass)
  | convert loc (Is_Defined_With asses) = ES.Is_Defined_With (convert_pair loc asses)
  | convert loc (Is_Rule_Of_Node pair)  = ES.Is_Rule_Of_Node (convert_pair loc pair)
  (*Eval_Unode*)
  | convert loc (Has_Same_Prnt_As       pair) = ES.Has_Same_Prnt_As       (convert_pair loc pair)
  | convert loc (Is_In_Trm_Prnt         pair) = ES.Is_In_Trm_Prnt         (convert_pair loc pair)
  | convert loc (Is_Deeper_Than         pair) = ES.Is_Deeper_Than         (convert_pair loc pair)
  | convert loc (Is_Shallower_Than      pair) = ES.Is_Shallower_Than      (convert_pair loc pair)
  | convert loc (Is_Path_Above          pair) = ES.Is_Path_Above          (convert_pair loc pair)
  | convert loc (Is_Same_Path_As        pair) = ES.Is_Same_Path_As        (convert_pair loc pair)
  | convert loc (Is_Nth_Child           pair) = ES.Is_Nth_Child           (convert_pair loc pair)
  | convert loc (Is_N_Plus_One_th_Child pair) = ES.Is_N_Plus_One_th_Child (convert_pair loc pair)
  (*Eval_Prnt*)
  | convert loc (Are_Same_Prints    pair) = ES.Are_Same_Prints  (convert_pair loc pair)
  | convert loc (Is_Nth_Induct      pair) = ES.Is_Nth_Induct    (convert_pair loc pair)
  | convert loc (Is_Nth_Arbitrary   pair) = ES.Is_Nth_Arbitrary (convert_pair loc pair)
  | convert loc (Is_Induct          ass ) = ES.Is_Induct        (convert loc ass)
  | convert loc (Is_Arbitrary       ass ) = ES.Is_Arbitrary     (convert loc ass)
  | convert loc (Is_Rule            ass ) = ES.Is_Rule          (convert loc ass)
  | convert loc (Is_Rule_Of_Print   pair) = ES.Is_Rule_Of_Print (convert_pair loc pair)
  (*Eval_Path*)
  | convert loc (Unode_Has_Print            pair) = ES.Unode_Has_Print        (convert_pair loc pair)
  | convert loc (Is_In_Subgoal              ass)  = ES.Is_In_Subgoal          (convert loc ass)
  | convert loc (Is_In_Chained_Fact         ass)  = ES.Is_In_Chained_Fact     (convert loc ass)
  | convert loc (ass Is_In_Nth_Subgoal      numb) = ES.Is_In_Nth_Subgoal      (convert_pair loc (ass, numb))
  | convert loc (ass Is_In_Nth_Chained_Fact numb) = ES.Is_In_Nth_Chained_Fact (convert_pair loc (ass, numb))
  (*Eval_Number*)
  | convert loc (Are_Same_Number pair) = ES.Are_Same_Number (convert_pair loc pair)
  | convert loc (Is_Less_Than    pair) = ES.Is_Less_Than    (convert_pair loc pair)
  (*Parameter*)
  | convert _ (Print  string) = ES.Print string
  | convert _ (Number    int) = ES.Number int
  | convert _ (Command   cmd) = ES.Command cmd
  (*expr*)
  | convert _   (Variable        string) = ES.Variable string
  | convert loc (Lambdas (strings, ass)) = ES.Lambdas (strings, convert loc ass)
  | convert loc (Applies   (func, args)) = ES.Applies (convert loc func, convert_list loc args)
  | convert loc (All    (vname, typ, assert)) = ES.All  (vname, typ, convert loc assert)
  | convert loc (Some   (vname, typ, assert)) = ES.Some (vname, typ, convert loc assert)
  | convert Out (In_All_Definitions (target, inner_fun, outer_args)) = ES.Dive_In   (convert Out target, convert Inn inner_fun, convert_list Out outer_args)
  | convert Inn (In_All_Definitions (target, inner_fun, outer_args)) = ES.Deep_Dive (convert Inn target, convert Inn inner_fun, convert_list Inn outer_args)
  (*syntax sugar*)
  | convert Out (In_Some_Definitions (target, Lambdas (strings, ass), outer_args)) = convert Out (Not (In_All_Definitions (target, Lambdas (strings, Not ass), outer_args)))
  | convert In  (In_Some_Definitions (target, Lambdas (strings, ass), outer_args)) = convert In  (Not (In_All_Definitions (target, Lambdas (strings, Not ass), outer_args)))
  | convert _   (In_Some_Definitions _) = error "convert in Eval_Syntactic_Sugar.ML failed at In_Some_Definitions"
  | convert loc (Is_Atomic assert) =
    convert loc
     (Ors
       [Is_Cnst  assert,
        Is_Free  assert,
        Is_Var   assert,
        Is_Bound assert])
  | convert loc (Have_Different_Prnts pair) = convert loc (Not (Has_Same_Prnt_As pair))
  | convert loc (Is_Path_Below (descendent, anscestor)) = convert loc (Is_Path_Above (anscestor, descendent))
  | convert loc (Is_Parent_Of (parent, child)) =
    let
      val non_exist = get_new_name [parent, child];
      val path_typ  = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
    in
      convert loc (
          Is_Path_Above (parent, child)
        And
          Not
           (Some (non_exist, path_typ,
                Is_Path_Above (Variable non_exist, child)
              And
                Is_Path_Below (Variable non_exist, parent))))
    end
  | convert loc (Is_Child_Of (child, parent))             = convert loc (Is_Parent_Of (parent, child))
  | convert loc (Is_Nth_Child_Of (child, number, parent)) =
    convert loc
      (Ands
         [Is_Parent_Of (parent, child),
          Is_Nth_Child (child, number)])
  | convert loc (Is_N_Plus_One_th_Child_Of (child, number, parent)) =
    convert loc
      (Ands
         [Is_Parent_Of (parent, child),
          Is_N_Plus_One_th_Child (child, number)])
  | convert loc (Is_Nth_Child_Or_Below_Nth_Child_Of (child_or_in_child, number, parent)) =
    let
      val nth_child_str = get_new_name [child_or_in_child, number, parent]: string;
      val nth_child     = Variable nth_child_str                          : assert;
      val path_typ      = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
    in
      convert loc
        (Ors
          [Is_Nth_Child_Of (child_or_in_child, number, parent),
           Some (nth_child_str, path_typ,
             Is_Path_Below (child_or_in_child, nth_child))
           ])
    end
  | convert loc (Is_An_Arg_Of (arg, func)) =
    let
      val func_app_str = get_new_name [func,arg]: string;
      val func_app     = Variable func_app_str  : assert;
      val path_typ     = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
    in
    (*Note that we have already transformed the syntax tree structure in Unique_Node.*)
      convert loc
       (Some (func_app_str, path_typ,
          Ands
           [Is_Parent_Of (func_app, func),
            Is_Nth_Child (func, Number 0),
            Is_Parent_Of (func_app, arg),
            Not (Is_Nth_Child (arg, Number 0)),
            Is_App func_app]))
    end
  | convert loc (Is_An_Arg_Or_Below_Arg_Of (arg_or_in_arg, func)) =
    let
      val arg_str  = get_new_name [func, arg_or_in_arg]: string;
      val arg      = Variable arg_str                  : assert;
      val path_typ = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
    in
      convert loc
       (Ors
         [Is_An_Arg_Of (arg_or_in_arg, func),
          Some (arg_str, path_typ,
            Ands
              [Is_An_Arg_Of (arg, func),
               Is_Path_Above (arg, arg_or_in_arg)])])
    end
  | convert loc (Is_Nth_Arg_Of (arg, number, func)) =
    let
      val func_app_str = get_new_name [func, number, arg]: string;
      val func_app     = Variable func_app_str           : assert;
      val path_typ      = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
    in
     (*Note helper to define futrm_w_prnt_to_futrm_w_prnt_n_inner_path in Unique_Node.ML*)
      convert loc
       (Some (func_app_str, path_typ,
          Ands
           [Is_Parent_Of (func_app, func),
            Is_Nth_Child (func, Number 0),
            Is_Parent_Of (func_app, arg),
            Is_N_Plus_One_th_Child (arg, number),
            Is_App func_app]))
    end
  | convert loc (Is_Nth_Arg_Or_Below_Nth_Arg_Of (arg_or_in_arg, number, func)) =
    let
      val nth_arg_str = get_new_name [func, number, arg_or_in_arg]: string;
      val nth_arg     = Variable nth_arg_str                      : assert;
      val path_typ    = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
    in
      convert loc
       (Ors
         [Is_Nth_Arg_Of (arg_or_in_arg, number, func),
          Some (nth_arg_str, path_typ,
            Ands
              [Is_Nth_Arg_Of (nth_arg, number, func),
               Is_Path_Above (nth_arg, arg_or_in_arg)])])
    end
  | convert loc (Are_In_Same_Location (ass1, ass2)) =
    let
      val non_exist_str = get_new_name [ass1, ass2] : string;
      val non_exist     = Variable non_exist_str: assert;
      val numb_typ      = case loc of Out => SU.QOuter_Number | Inn => SU.QInner_Number;
    in
      convert loc
        (Some (non_exist_str, numb_typ,
             ((ass1 Is_In_Nth_Subgoal non_exist)
             And
              (ass2 Is_In_Nth_Subgoal non_exist))
           Or
             ((ass1 Is_In_Nth_Chained_Fact non_exist)
             And
              (ass2 Is_In_Nth_Chained_Fact non_exist))))
    end
  | convert loc (Is_Deeper_Than_In_Same_Location (deep, shallow)) =
    convert loc
       (Are_In_Same_Location (deep, shallow)
      And
        Is_Deeper_Than (deep, shallow))
  | convert loc (Is_Shallower_Than_In_Same_Location (shallow, deep)) =
    convert loc
       (Are_In_Same_Location (deep, shallow)
      And
        Is_Shallower_Than (shallow, deep))
  | convert loc (Is_Root_In_A_Location assert) =
    let
      val non_exist_str = get_new_name [assert] : string;
      val non_exist     = Variable non_exist_str: assert;
      val path_typ      = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
    in
      convert loc
        (Not
          (Some (non_exist_str, path_typ,
            Is_Shallower_Than_In_Same_Location (non_exist, assert))))
    end
  | convert loc (Is_At_Deepest_In_A_Location assert) =
    let
      val non_exist_str = get_new_name [assert] : string;
      val non_exist     = Variable non_exist_str: assert;
      val path_typ      = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
    in
      convert loc
        (Not
          (Some (non_exist_str, path_typ,
            Is_Deeper_Than_In_Same_Location (non_exist, assert))))
    end
  | convert loc (Is_Less_Than_Or_Equal (less, more)) = convert loc (Is_Less_Than (less, more) Or Are_Same_Number (less, more))
  | convert loc (Is_More_Than_Or_Equal (more, less)) = convert loc (Not (Is_Less_Than (more, less)))
  | convert loc (Is_More_Than (more, less)) = convert loc (Is_Less_Than (less, more))
  | convert loc (Is_A_Meta_Premise premise) =
    let
      val imp_name            = get_new_name [premise];
      val imp                 = Variable imp_name;
      val conclusion_name     = get_new_name [premise, imp];
      val conclusion          = Variable conclusion_name;
      val nth_premise_name    = get_new_name [premise, imp, conclusion];
      val nth_premise         = Variable nth_premise_name;
      val nth_conclusion_name = get_new_name [premise, imp, conclusion, nth_premise];
      val nth_conclusion      = Variable nth_conclusion_name;
      val path_typ            = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
      val numb_typ            = case loc of Out => SU.QOuter_Number | Inn => SU.QInner_Number;
    in
      convert loc (
        Some (imp_name, path_typ,
          Ands [
            Unode_Has_Print (imp, Print "Pure.imp"),
            Is_An_Arg_Of (premise, imp),
            Some (nth_premise_name, numb_typ,
              Ands [
                Is_Nth_Arg_Of (premise, nth_premise, imp),
                Some (conclusion_name, path_typ,
                  Ands [
                    Is_An_Arg_Of (conclusion, imp),
                    Not (Is_Same_Path_As (premise, conclusion)),
                    Some (nth_conclusion_name, numb_typ,
                      Ands [
                        Is_Less_Than (nth_premise, nth_conclusion),
                        Is_Nth_Arg_Of (conclusion, nth_conclusion, imp)
                      ]
                    )
                  ]
                )
              ]
            )
          ]
        )
      )
    end
  | convert loc (Is_A_Meta_Premise_Or_Below premise) =
    let
      val imp_name            = get_new_name [premise];
      val imp                 = Variable imp_name;
      val conclusion_name     = get_new_name [premise, imp];
      val conclusion          = Variable conclusion_name;
      val nth_premise_name    = get_new_name [premise, imp, conclusion];
      val nth_premise         = Variable nth_premise_name;
      val nth_conclusion_name = get_new_name [premise, imp, conclusion, nth_premise];
      val nth_conclusion      = Variable nth_conclusion_name;
      val path_typ            = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
      val numb_typ            = case loc of Out => SU.QOuter_Number | Inn => SU.QInner_Number;
    in
      convert loc (
        Some (imp_name, path_typ,
          Ands [
            Unode_Has_Print (imp, Print "Pure.imp"),
            Is_An_Arg_Or_Below_Arg_Of (premise, imp),(*!*)
            Some (nth_premise_name, numb_typ,
              Ands [
                Is_Nth_Arg_Or_Below_Nth_Arg_Of (premise, nth_premise, imp),(*!*)
                Some (conclusion_name, path_typ,
                  Ands [
                    Is_An_Arg_Of (conclusion, imp),
                    Not (Is_Same_Path_As (premise, conclusion)),
                    Some (nth_conclusion_name, numb_typ,
                      Ands [
                        Is_Less_Than (nth_premise, nth_conclusion),
                        Is_Nth_Arg_Of (conclusion, nth_conclusion, imp)
                      ]
                    )
                  ]
                )
              ]
            )
          ]
        )
      )
    end
  | convert loc (Is_A_Meta_Conclusion conclusion) =(*FIXME: a conclusion can be a premise, too!*)
    let
      val imp_name            = get_new_name [conclusion];
      val imp                 = Variable imp_name;
      val premise_name        = get_new_name [conclusion, imp];
      val premise             = Variable premise_name;
      val nth_premise_name    = get_new_name [conclusion, imp, premise];
      val nth_premise         = Variable nth_premise_name;
      val nth_conclusion_name = get_new_name [conclusion, imp, premise, nth_premise];
      val nth_conclusion      = Variable nth_conclusion_name;
      val path_typ            = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
      val numb_typ            = case loc of Out => SU.QOuter_Number | Inn => SU.QInner_Number;
    in
      convert loc (
        Some (imp_name, path_typ,
          Ands [
            Unode_Has_Print (imp, Print "Pure.imp"),
            Is_An_Arg_Of (conclusion, imp),
            Some (nth_conclusion_name, numb_typ,
              Ands [
                Is_Nth_Arg_Of (conclusion, nth_conclusion, imp),
                Not (
                  Some (premise_name, path_typ,
                    Ands [
                      Is_An_Arg_Of (premise, imp),
                      Not (Is_Same_Path_As (premise, conclusion)),
                      Some (nth_premise_name, numb_typ,
                        Ands [
                          Is_Less_Than (nth_conclusion, nth_premise),
                          Is_Nth_Arg_Of (premise, nth_premise, imp)
                        ]
                      )
                    ]
                  )
                )
              ]
            )
          ]
        )
      )
    end
  | convert loc (Is_A_Meta_Conclusion_Or_Below conclusion) =
    let
      val imp_name            = get_new_name [conclusion];
      val imp                 = Variable imp_name;
      val premise_name        = get_new_name [conclusion, imp];
      val premise             = Variable premise_name;
      val nth_premise_name    = get_new_name [conclusion, imp, premise];
      val nth_premise         = Variable nth_premise_name;
      val nth_conclusion_name = get_new_name [conclusion, imp, premise, nth_premise];
      val nth_conclusion      = Variable nth_conclusion_name;
      val path_typ            = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
      val numb_typ            = case loc of Out => SU.QOuter_Number | Inn => SU.QInner_Number;
    in
      convert loc (
        Some (imp_name, path_typ,
          Ands [
            Unode_Has_Print (imp, Print "Pure.imp"),
            Is_An_Arg_Or_Below_Arg_Of (conclusion, imp),(*!*)
            Some (nth_conclusion_name, numb_typ,
              Ands [
                  Is_Nth_Arg_Or_Below_Nth_Arg_Of (conclusion, nth_conclusion, imp),(*!*)
                  All (premise_name, path_typ,
                      Ands [
                        Is_An_Arg_Of (premise, imp),
                        Not (Is_Path_Above (premise, conclusion)),(*!*)
                        Not (Is_Same_Path_As (premise, conclusion))
                      ]
                    Imply
                      Some (nth_premise_name, numb_typ,
                        Ands [
                          Is_Less_Than (nth_premise, nth_conclusion),
                          Is_Nth_Arg_Of (premise, nth_premise, imp)
                        ]
                      )
                  )
              ]
            )
          ]
        )
      )
    end
  | convert loc (Some_Of (occ:string, prnt:assert, inner_assert)) =
    let
      val path_typ = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
    in
      convert loc
       (Some (occ, path_typ,
            Unode_Has_Print (Variable occ, prnt)
          And
            inner_assert))
    end
  | convert loc (All_Of (occ, prnt, inner_assert)) = convert loc (Not (Some_Of (occ, prnt, Not inner_assert)))
  | convert loc (Debug_Non_Path_Literal assert) = ES.Debug_Non_Path_Literal (convert loc assert)
  | convert loc (Debug_Print_Unode      assert) = ES.Debug_Print_Unode (convert loc assert)
  | convert loc (Debug_Space                  ) = convert loc (tracing "\n"; True);

fun surf_to_sugar ES.True  = True
  | surf_to_sugar ES.False = False
  | surf_to_sugar _ = error "surf_to_sugar failed."

fun eval (pst:Proof.state) (ind_args:SU.induct_arguments) (assert:assert) =
    ES.eval pst ind_args (convert Out assert) |> surf_to_sugar;

end;