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
| Node_Is_Cnst                     of assert
| Node_Is_Free                     of assert
| Node_Is_Var                      of assert
| Node_Is_Bound                    of assert
| Node_Is_Lambda                   of assert
| Node_Is_App                      of assert
| Node_Is_Defined_With             of assert * assert
| Node_Is_Defined_With_N_Clauses   of assert * assert
| Is_Rule_Of_Node                  of assert * assert
| Node_Takes_N_Arguments           of assert * assert
| Node_Takes_Less_Than_N_Arguments of assert * assert
(*Eval_Unode*)
| Has_Same_Prnt_As       of assert * assert
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
(*Eval_Print for node*)
| Print_Is_Cnst                     of assert
| Print_Is_Free                     of assert
| Print_Is_Var                      of assert
| Print_Is_Bound                    of assert (*corresponds to Bound in term*)
| Print_Is_Lambda                   of assert (*lambda abstraction corresponding to Abs in Term*)
| Print_Is_App                      of assert (*function application corresponding to $ in Term*)
| Print_Is_Defined_With             of assert * assert
| Print_Is_Defined_With_N_Clauses   of assert * assert
| Print_Takes_N_Arguments           of assert * assert
| Print_Takes_Less_Than_N_Arguments of assert * assert
(*Eval_Path*)
| Unode_Has_Print        of assert * assert
| Is_Subprint_Of         of assert * assert
| Is_In_Subgoal          of assert
| Is_In_Chained_Fact     of assert
| Is_In_Nth_Subgoal      of assert * assert
| Is_In_Nth_Chained_Fact of assert * assert
| Is_Parent_Of           of assert * assert
| Is_A_Meta_Premise      of assert
| Is_A_Meta_Conclusion   of assert
(*Eval_Number*)
| Are_Same_Number     of assert * assert
| Is_Less_Than        of assert * assert
| Is_Less_Than_By_One of assert * assert
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
| Unode_Has_As_Subprint              of assert * assert
| Is_Path_Below                      of assert * assert
| Is_Child_Of                        of assert * assert
| Is_Nth_Child_Of                    of assert * assert * assert
| Is_N_Plus_One_th_Child_Of          of assert * assert * assert
| Is_Nth_Child_Or_Below_Nth_Child_Of of assert * assert * assert
| Is_Below_N_Plus_One_th_Child_Of    of assert * assert * assert
| Is_N_Plus_One_th_Child_Or_Below_N_Plus_One_th_Child_Of of assert * assert * assert
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
| Is_A_Meta_Premise_Or_Below         of assert
| Is_A_Meta_Conclusion_Or_Below      of assert
| Is_If_Then_Else                    of assert * assert * assert * assert
| Is_Case_Distinct_Of_Trm_With_A_Case of assert * assert * assert
| Is_Let_X_Be_Y_In_X                  of assert * assert * assert
| Some_Of                             of string * assert * assert
| All_Of                              of string * assert * assert
(*debug*)
| Debug_Non_Path_Literal             of assert
| Debug_Print_Unode                  of assert
| Dummy

val eval: Proof.state -> Outer_Path_To_Unode.path_to_unode_table -> SeLFiE_Util.induct_arguments -> assert -> assert;

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
| Node_Is_Cnst                     of assert
| Node_Is_Free                     of assert
| Node_Is_Var                      of assert
| Node_Is_Bound                    of assert
| Node_Is_Lambda                   of assert
| Node_Is_App                      of assert
| Node_Is_Defined_With             of assert * assert
| Node_Is_Defined_With_N_Clauses   of assert * assert
| Is_Rule_Of_Node                  of assert * assert
| Node_Takes_N_Arguments           of assert * assert
| Node_Takes_Less_Than_N_Arguments of assert * assert
(*Eval_Unode*)
| Has_Same_Prnt_As       of assert * assert
| Is_Deeper_Than         of assert * assert
| Is_Shallower_Than      of assert * assert
| Is_Path_Above          of assert * assert
| Is_Same_Path_As        of assert * assert
| Is_Nth_Child           of assert * assert
| Is_N_Plus_One_th_Child of assert * assert
(*Eval_Print*)
| Are_Same_Prints   of assert * assert
| Is_Subprint_Of    of assert * assert
| Is_Nth_Induct     of assert * assert
| Is_Nth_Arbitrary  of assert * assert
| Is_Induct         of assert
| Is_Arbitrary      of assert
| Is_Rule           of assert
| Is_Rule_Of_Print  of assert * assert
(*Eval_Print for node*)
| Print_Is_Cnst                     of assert
| Print_Is_Free                     of assert
| Print_Is_Var                      of assert
| Print_Is_Bound                    of assert (*corresponds to Bound in term*)
| Print_Is_Lambda                   of assert (*lambda abstraction corresponding to Abs in Term*)
| Print_Is_App                      of assert (*function application corresponding to $ in Term*)
| Print_Is_Defined_With             of assert * assert
| Print_Is_Defined_With_N_Clauses   of assert * assert
| Print_Takes_N_Arguments           of assert * assert
| Print_Takes_Less_Than_N_Arguments of assert * assert
(*Eval_Path*)
| Unode_Has_Print        of assert * assert
| Is_In_Subgoal          of assert
| Is_In_Chained_Fact     of assert
| Is_In_Nth_Subgoal      of assert * assert
| Is_In_Nth_Chained_Fact of assert * assert
| Is_Parent_Of           of assert * assert
| Is_A_Meta_Premise      of assert
| Is_A_Meta_Conclusion   of assert
(*Eval_Number*)
| Are_Same_Number     of assert * assert
| Is_Less_Than        of assert * assert
| Is_Less_Than_By_One of assert * assert
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
| Unode_Has_As_Subprint              of assert * assert
| Is_Path_Below                      of assert * assert
| Is_Child_Of                        of assert * assert
| Is_Nth_Child_Of                    of assert * assert * assert
| Is_N_Plus_One_th_Child_Of          of assert * assert * assert
| Is_Nth_Child_Or_Below_Nth_Child_Of of assert * assert * assert
| Is_Below_N_Plus_One_th_Child_Of    of assert * assert * assert
| Is_N_Plus_One_th_Child_Or_Below_N_Plus_One_th_Child_Of of assert * assert * assert
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
| Is_A_Meta_Premise_Or_Below         of assert
| Is_A_Meta_Conclusion_Or_Below      of assert
| Is_If_Then_Else                    of assert * assert * assert * assert
| Is_Case_Distinct_Of_Trm_With_A_Case of assert * assert * assert
| Is_Let_X_Be_Y_In_X                  of assert * assert * assert
| Some_Of                             of string * assert * assert
| All_Of                              of string * assert * assert
(*debug*)
| Debug_Non_Path_Literal             of assert
| Debug_Print_Unode                  of assert
| Dummy

structure ES = Eval_Surface;
structure SU = SeLFiE_Util;

fun get_new_name' acc []                    = acc
  | get_new_name' acc (Variable name::vars) = get_new_name' (acc ^ name) vars
  | get_new_name' acc (_            ::xs  ) = get_new_name' (acc ^ "nonvar") xs;

 (*For atomic assertions, we have to avoid a name collisions with the arguments to the assertion only.*)
val get_new_name = get_new_name' "A";

infix And Or Imply Is_In_Nth_Subgoal Is_In_Nth_Chained_Fact;

(*TODO: Should I use lazy sequences for pairs as well?*)
fun convert_pair loc pair = Utils.map_pair (convert loc) pair
and convert_list loc list = map (convert loc) list
(*
and convert_list_to_seq loc list = Seq.map (convert loc) (Seq.of_list list)
*)
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
  | convert loc (Node_Is_Cnst                     ass)   = ES.Node_Is_Cnst                     (convert      loc ass)
  | convert loc (Node_Is_Free                     ass)   = ES.Node_Is_Free                     (convert      loc ass)
  | convert loc (Node_Is_Var                      ass)   = ES.Node_Is_Var                      (convert      loc ass)
  | convert loc (Node_Is_Bound                    ass)   = ES.Node_Is_Bound                    (convert      loc ass)
  | convert loc (Node_Is_Lambda                   ass)   = ES.Node_Is_Lambda                   (convert      loc ass)
  | convert loc (Node_Is_App                      ass)   = ES.Node_Is_App                      (convert      loc ass)
  | convert loc (Node_Is_Defined_With             pair)  = ES.Node_Is_Defined_With             (convert_pair loc pair)
  | convert loc (Node_Is_Defined_With_N_Clauses   pair)  = ES.Node_Is_Defined_With_N_Clauses   (convert_pair loc pair)
(*| Node_Is_Defined_With_N_Clauses   of assert * assert*)
  | convert loc (Is_Rule_Of_Node                  pair)  = ES.Is_Rule_Of_Node                  (convert_pair loc pair)
  | convert loc (Node_Takes_N_Arguments           pair)  = ES.Node_Takes_N_Arguments           (convert_pair loc pair)
  | convert loc (Node_Takes_Less_Than_N_Arguments pair)  = ES.Node_Takes_Less_Than_N_Arguments (convert_pair loc pair)
  (*Eval_Unode*)
  | convert loc (Has_Same_Prnt_As       pair) = ES.Has_Same_Prnt_As       (convert_pair loc pair)
  | convert loc (Is_Deeper_Than         pair) = ES.And (convert loc (Are_In_Same_Location pair), ES.Is_Deeper_Than         (convert_pair loc pair))(*TODO:Should I add this same-location check somewhere else?*)
  | convert loc (Is_Shallower_Than      pair) = ES.And (convert loc (Are_In_Same_Location pair), ES.Is_Shallower_Than      (convert_pair loc pair))(*TODO:Should I add this same-location check somewhere else?*)
  | convert loc (Is_Path_Above          pair) = ES.And (convert loc (Are_In_Same_Location pair), ES.Is_Path_Above          (convert_pair loc pair))(*TODO:Should I add this same-location check somewhere else?*)
  | convert loc (Is_Same_Path_As        pair) = ES.And (convert loc (Are_In_Same_Location pair), ES.Is_Same_Path_As        (convert_pair loc pair))(*TODO:Should I add this same-location check somewhere else?*)
  | convert loc (Is_Nth_Child           pair) = ES.Is_Nth_Child           (convert_pair loc pair)
  | convert loc (Is_N_Plus_One_th_Child pair) = ES.Is_N_Plus_One_th_Child (convert_pair loc pair)
  | convert loc (Is_Root_In_A_Location  arg ) = ES.Is_Root_In_A_Location  (convert      loc arg )
  (*Eval_Prnt*)
  | convert loc (Are_Same_Prints    pair) = ES.Are_Same_Prints  (convert_pair loc pair)
  | convert loc (Is_Subprint_Of     pair) = ES.Is_Subprint_Of   (convert_pair loc pair)
  | convert loc (Is_Nth_Induct      pair) = ES.Is_Nth_Induct    (convert_pair loc pair)
  | convert loc (Is_Nth_Arbitrary   pair) = ES.Is_Nth_Arbitrary (convert_pair loc pair)
  | convert loc (Is_Induct          ass ) = ES.Is_Induct        (convert loc ass)
  | convert loc (Is_Arbitrary       ass ) = ES.Is_Arbitrary     (convert loc ass)
  | convert loc (Is_Rule            ass ) = ES.Is_Rule          (convert loc ass)
  | convert loc (Is_Rule_Of_Print   pair) = ES.Is_Rule_Of_Print (convert_pair loc pair)
  (*Eval_Print for node*)
  | convert loc (Print_Is_Cnst                     ass ) = ES.Print_Is_Cnst                     (convert      loc ass)
  | convert loc (Print_Is_Free                     ass ) = ES.Print_Is_Free                     (convert      loc ass)
  | convert loc (Print_Is_Var                      ass ) = ES.Print_Is_Var                      (convert      loc ass)
  | convert loc (Print_Is_Bound                    ass ) = ES.Print_Is_Bound                    (convert      loc ass)
  | convert loc (Print_Is_Lambda                   ass ) = ES.Print_Is_Lambda                   (convert      loc ass)
  | convert loc (Print_Is_App                      ass ) = ES.Print_Is_App                      (convert      loc ass)
  | convert loc (Print_Is_Defined_With             pair) = ES.Print_Is_Defined_With             (convert_pair loc pair)
  | convert loc (Print_Is_Defined_With_N_Clauses   pair) = ES.Print_Is_Defined_With_N_Clauses   (convert_pair loc pair)
  | convert loc (Print_Takes_N_Arguments           pair) = ES.Print_Takes_N_Arguments           (convert_pair loc pair)
  | convert loc (Print_Takes_Less_Than_N_Arguments pair) = ES.Print_Takes_Less_Than_N_Arguments (convert_pair loc pair)
  (*Eval_Path*)
  | convert loc (Unode_Has_Print            pair) = ES.Unode_Has_Print        (convert_pair loc pair)
  | convert loc (Is_In_Subgoal              ass)  = ES.Is_In_Subgoal          (convert loc ass)
  | convert loc (Is_In_Chained_Fact         ass)  = ES.Is_In_Chained_Fact     (convert loc ass)
  | convert loc (ass Is_In_Nth_Subgoal      numb) = ES.Is_In_Nth_Subgoal      (convert_pair loc (ass, numb))
  | convert loc (ass Is_In_Nth_Chained_Fact numb) = ES.Is_In_Nth_Chained_Fact (convert_pair loc (ass, numb))
  | convert loc (Is_Parent_Of               pair) = ES.Is_Parent_Of           (convert_pair loc pair)
  | convert loc (Is_A_Meta_Premise          ass)  = ES.Is_A_Meta_Premise      (convert loc ass)
  | convert loc (Is_A_Meta_Conclusion       ass)  = ES.Is_A_Meta_Conclusion   (convert loc ass)
  (*Eval_Number*)
  | convert loc (Are_Same_Number     pair) = ES.Are_Same_Number     (convert_pair loc pair)
  | convert loc (Is_Less_Than        pair) = ES.Is_Less_Than        (convert_pair loc pair)
  | convert loc (Is_Less_Than_By_One pair) = ES.Is_Less_Than_By_One (convert_pair loc pair)
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
       [Node_Is_Cnst  assert,
        Node_Is_Free  assert,
        Node_Is_Var   assert,
        Node_Is_Bound assert])
  | convert loc (Have_Different_Prnts pair) = convert loc (Not (Has_Same_Prnt_As pair))
  | convert loc (Unode_Has_As_Subprint (trm_occ, subprint)) = convert loc (
    let
      val print_str = get_new_name [trm_occ, subprint];
      val print     = Variable print_str;
      val path_typ  = case loc of Out => SU.QOuter_Print | Inn => SU.QInner_Print;
    in
      Some (print_str, path_typ,
        Ands [
          Unode_Has_Print (trm_occ, print),
          Is_Subprint_Of  (subprint, print)
        ]
      )
    end
    )
  | convert loc (Is_Path_Below (descendent, anscestor)) = convert loc (Is_Path_Above (anscestor, descendent))
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
             Ands [
               Is_Nth_Child_Of (nth_child, number, parent),
               Is_Path_Below (child_or_in_child, nth_child)
             ]
           )
          ]
        )
    end
  | convert loc (Is_Below_N_Plus_One_th_Child_Of (in_child, number, parent)) =
    let
      val n_plus_one_th_child_str = get_new_name [in_child, number, parent]: string;
      val n_plus_one_th_child     = Variable n_plus_one_th_child_str                : assert;
      val path_typ                = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
    in
      convert loc
        (Some (n_plus_one_th_child_str, path_typ,
           Ands [
             Is_N_Plus_One_th_Child_Of (n_plus_one_th_child, number, parent),
             Is_Path_Below (in_child, n_plus_one_th_child)
           ]
         )
        )
    end
  | convert loc (Is_N_Plus_One_th_Child_Or_Below_N_Plus_One_th_Child_Of (child_or_in_child, number, parent)) =
      convert loc
        (Ors
          [Is_N_Plus_One_th_Child_Of (child_or_in_child, number, parent),
           Is_Below_N_Plus_One_th_Child_Of (child_or_in_child, number, parent)
          ]
        )
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
            Node_Is_App func_app]))
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
            Node_Is_App func_app]))
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
  | convert loc (Is_If_Then_Else (if_then_else, if_condition, then_clase, else_clase)) =
    let
      val hol_if_str = get_new_name [if_then_else, if_condition, then_clase, else_clase]: string;
      val hol_if     = Variable hol_if_str                                              : assert;
      val path_typ   = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
    in
    convert loc (
      Ands [
        Node_Is_App if_then_else,
        Some (hol_if_str, path_typ,
          Ands [
            Is_Nth_Child_Of (hol_if, Number 0, if_then_else),
            Unode_Has_Print (hol_if, Print "HOL.If"),
            Is_Nth_Arg_Of (if_condition, Number 0, hol_if),
            Is_Nth_Arg_Of (then_clase,   Number 1, hol_if),
            Is_Nth_Arg_Of (else_clase,   Number 2, hol_if)
          ]
        )
      ]
    )
    end
  | convert loc (Is_Case_Distinct_Of_Trm_With_A_Case (whole_term, case_on, a_case)) =
    let
      val case_const_str             = get_new_name [whole_term, case_on, a_case]                                    : string;
      val case_const                 = Variable case_const_str                                                       : assert;
      val case_path_typ              = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path                     : SU.qtyp;
      val numb_of_args_str           = get_new_name [whole_term, case_on, a_case, case_const]                        : string;
      val numb_of_args               = Variable numb_of_args_str                                                     : assert;
      val nth_case_str               = get_new_name [whole_term, case_on, a_case, case_const, numb_of_args]          : string;
      val nth_case                   = Variable nth_case_str                                                         : assert;
      val numb_path_typ              = case loc of Out => SU.QOuter_Number | Inn => SU.QInner_Number                 : SU.qtyp;
      val numb_of_args_minus_one_str = get_new_name [whole_term, case_on, a_case, case_const, numb_of_args, nth_case]: string;
      val numb_of_args_minus_one     = Variable numb_of_args_minus_one_str                                           : assert;
    in
    convert loc (
      Ands [
        Node_Is_App whole_term,
        Some (case_const_str, case_path_typ,
          Ands [
            Unode_Has_As_Subprint (case_const, Print ".case_"),
            Is_Nth_Child_Of       (case_const, Number 0, whole_term),
            Some (numb_of_args_str, numb_path_typ,
              Ands [
                Node_Takes_N_Arguments (case_const, numb_of_args),
                Some (numb_of_args_minus_one_str, numb_path_typ,
                  Ands [
                    Is_Less_Than_By_One (numb_of_args_minus_one, numb_of_args),
                    Is_Nth_Arg_Of (case_on, numb_of_args_minus_one, case_const),
                    Some (nth_case_str, numb_path_typ,
                      Ands [
                        Is_Less_Than (nth_case, numb_of_args_minus_one),
                        Is_Nth_Arg_Of (a_case, nth_case, case_const)
                      ]
                    )
                  ]
                )
              ]
            )
          ]
        )
      ]
    )
    end
  | convert loc (Is_Let_X_Be_Y_In_X (whole_term_occ, let_sth_be_this_occ, bound_and_body_occ)) =
    let
      val let_const_str = get_new_name [whole_term_occ, let_sth_be_this_occ, bound_and_body_occ]: string;
      val let_const     = Variable let_const_str                                                : assert;
      val path_typ      = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
    in
    convert loc (
      Ands [
        Node_Is_App whole_term_occ,
        Some (let_const_str, path_typ,
          Ands [
            Unode_Has_Print (let_const, Print "HOL.Let"),
            Is_Nth_Child_Of (let_const, Number 0, whole_term_occ),
            Is_Nth_Arg_Of   (let_sth_be_this_occ, Number 0, let_const),
            Is_Nth_Arg_Of   (bound_and_body_occ,  Number 1, let_const)
          ]
        )
      ]
    )
    end
  | convert loc (Some_Of (occ:string, prnt:assert, inner_assert)) =
    let
      val path_typ = case loc of Out => SU.QOuter_Path | Inn => SU.QInner_Path;
    in
      convert loc
       (Some (occ, path_typ,
          Ands [
            Unode_Has_Print (Variable occ, prnt),
            inner_assert
          ]
        )
       )
    end
  | convert loc (All_Of (occ, prnt, inner_assert)) = convert loc (Not (Some_Of (occ, prnt, Not inner_assert)))
  | convert loc (Debug_Non_Path_Literal assert)    = ES.Debug_Non_Path_Literal (convert loc assert)
  | convert loc (Debug_Print_Unode      assert)    = ES.Debug_Print_Unode (convert loc assert)
  | convert _    Dummy                             = ES.Dummy

fun surf_to_sugar ES.True  = True
  | surf_to_sugar ES.False = False
  | surf_to_sugar _ = error "surf_to_sugar failed."

fun eval (pst:Proof.state) (path_to_unode_table: Outer_Path_To_Unode.path_to_unode_table) (ind_args:SU.induct_arguments) (assert:assert) =
    ES.eval pst path_to_unode_table ind_args (convert Out assert) |> surf_to_sugar;

end;