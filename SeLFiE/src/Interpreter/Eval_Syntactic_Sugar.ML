(*  Title:      PSL/SeLFiE/src/Interpreter/Syntactic_Sugar.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** signature: EVAL_SYNTACTIC_SUGAR ***)
signature EVAL_SYNTACTIC_SUGAR =
sig

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
| Is_Cnst    of assert
| Is_Free    of assert
| Is_Var     of assert
| Is_Bound   of assert
| Is_Lambda  of assert
| Is_App     of assert
(*Eval_Unode*)
| Has_Same_Prnt_As  of assert * assert
| Is_In_Trm_Prnt    of assert * assert
| Is_Deeper_Than    of assert * assert
| Is_Shallower_Than of assert * assert
| Is_Path_Above     of assert * assert
| Is_Same_Path_As   of assert * assert
| Is_Nth_Child      of assert * assert
(*Eval_Print*)
| Are_Same_Prints   of assert * assert
(*Eval_Path*)
| Unode_Has_Print   of assert * assert
(*Eval_Number*)
| Are_Same_Number of assert * assert
| Is_Less_Than    of assert * assert
(*Parameter*)
| Print  of string
| Number of int
(*expr*)
| Variable            of string
| Lambdas             of strings * assert
| Applies             of assert  * assert list
| Alls                of (string * SeLFiE_Util.qtyp) list * assert
| Somes               of (string * SeLFiE_Util.qtyp) list * assert
| In_All_Definitions  of (assert * assert * assert list)
| In_Some_Definitions of (assert * assert * assert list)
| Outermost           of assert
(*Syntactic Sugar*)
| Is_Atomic           of assert
| Is_Path_Below       of assert * assert
| Is_Parent_Of        of assert * assert
| Is_Child_Of         of assert * assert
| Is_An_Arg_Of        of assert * assert
| Is_Nth_Arg_Of       of assert * assert * assert
| Is_At_Deepest       of assert
| Somes_Of            of (string * assert) list * assert
| Alls_Of             of (string * assert) list * assert;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> assert -> Eval_Surface.assert;

end;

(*** Eval_Syntactic_Sugar ***)
structure Eval_Syntactic_Sugar: EVAL_SYNTACTIC_SUGAR =
struct

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
| Is_Cnst    of assert
| Is_Free    of assert
| Is_Var     of assert
| Is_Bound   of assert
| Is_Lambda  of assert
| Is_App     of assert
(*Eval_Unode*)
| Has_Same_Prnt_As  of assert * assert
| Is_In_Trm_Prnt    of assert * assert
| Is_Deeper_Than    of assert * assert
| Is_Shallower_Than of assert * assert
| Is_Path_Above     of assert * assert
| Is_Same_Path_As   of assert * assert
| Is_Nth_Child      of assert * assert
(*Eval_Print*)
| Are_Same_Prints   of assert * assert
(*Eval_Path*)
| Unode_Has_Print   of assert * assert
(*Eval_Number*)
| Are_Same_Number of assert * assert
| Is_Less_Than    of assert * assert
(*Parameter*)
| Print  of string
| Number of int
(*expr*)
| Variable            of string
| Lambdas             of strings * assert
| Applies             of assert  * assert list
| Alls                of (string * SeLFiE_Util.qtyp) list * assert
| Somes               of (string * SeLFiE_Util.qtyp) list * assert
| In_All_Definitions  of (assert * assert * assert list)
| In_Some_Definitions of (assert * assert * assert list)
| Outermost           of assert
(*Syntactic Sugar*)
| Is_Atomic           of assert
| Is_Path_Below       of assert * assert
| Is_Parent_Of        of assert * assert
| Is_Child_Of         of assert * assert
| Is_An_Arg_Of        of assert * assert
| Is_Nth_Arg_Of       of assert * assert * assert
| Is_At_Deepest       of assert
| Somes_Of            of (string * assert) list * assert
| Alls_Of             of (string * assert) list * assert;

structure ES = Eval_Surface;
structure SU = SeLFiE_Util;

infix And;

fun get_new_name' acc []                    = acc
  | get_new_name' acc (Variable name::vars) = get_new_name' (acc ^ name) vars
  | get_new_name' _   (_            ::_   ) = error "get_new_name' in Eval_Syntactic_Sugar.ML failed.";

 (*For atomic assertions, we have to avoid a name collisions with the arguments to the assertion only.*)
val get_new_name = get_new_name' "";

fun convert_pair pair = Utils.map_pair convert pair
and convert_list list = map convert list
and convert  True                    = ES.True
  | convert  False                   = ES.False
  | convert (Not    ass)             = ES.Not   (convert       ass)
  | convert (And   pair)             = ES.And   (convert_pair pair)
  | convert (Or    pair)             = ES.Or    (convert_pair pair)
  | convert (Nor   pair)             = ES.Nor   (convert_pair pair)
  | convert (Imply pair)             = ES.Imply (convert_pair pair)
  | convert (Ands  list)             = ES.Ands  (convert_list list)
  | convert (Ors   list)             = ES.Ors   (convert_list list)
  | convert (Is_Cnst   ass)          = ES.Is_Cnst   (convert ass)
  | convert (Is_Free   ass)          = ES.Is_Free   (convert ass)
  | convert (Is_Var    ass)          = ES.Is_Var    (convert ass)
  | convert (Is_Bound  ass)          = ES.Is_Bound  (convert ass)
  | convert (Is_Lambda ass)          = ES.Is_Lambda (convert ass)
  | convert (Is_App    ass)          = ES.Is_App (convert ass)
  | convert (Has_Same_Prnt_As  pair) = ES.Has_Same_Prnt_As  (convert_pair pair)
  | convert (Is_In_Trm_Prnt    pair) = ES.Is_In_Trm_Prnt    (convert_pair pair)
  | convert (Is_Deeper_Than    pair) = ES.Is_Deeper_Than    (convert_pair pair)
  | convert (Is_Shallower_Than pair) = ES.Is_Shallower_Than (convert_pair pair)
  | convert (Is_Path_Above     pair) = ES.Is_Path_Above     (convert_pair pair)
  | convert (Is_Same_Path_As   pair) = ES.Is_Same_Path_As   (convert_pair pair)
  | convert (Is_Nth_Child      pair) = ES.Is_Nth_Child      (convert_pair pair)
  | convert (Are_Same_Prints   pair) = ES.Are_Same_Prints   (convert_pair pair)
  | convert (Unode_Has_Print   pair) = ES.Unode_Has_Print   (convert_pair pair)
  | convert (Are_Same_Number   pair) = ES.Are_Same_Number   (convert_pair pair)
  | convert (Is_Less_Than      pair) = ES.Is_Less_Than      (convert_pair pair)
  | convert (Print           string) = ES.Print string
  | convert (Number             int) = ES.Number int
  | convert (Variable        string) = ES.Variable string
  | convert (Lambdas (strings, ass)) = ES.Lambdas (strings, convert ass)
  | convert (Applies   (func, args)) = ES.Applies (convert func, convert_list args)
  | convert (Alls   (pairs, assert)) = ES.Alls    (pairs, convert assert)
  | convert (Somes  (pairs, assert)) = ES.Somes   (pairs, convert assert)
  | convert (In_All_Definitions  (target, inner_fun, outer_args)) = ES.In_All_Definitions  (convert target, convert inner_fun, convert_list outer_args)
  | convert (In_Some_Definitions (target, inner_fun, outer_args)) = ES.In_Some_Definitions (convert target, convert inner_fun, convert_list outer_args)
  | convert (Outermost assert)       = ES.Outermost (convert assert)
  (*syntax sugar*)
  | convert (Is_Atomic assert)       =
    convert
     (Ors
       [Is_Cnst assert,
        Is_Free assert,
        Is_Var  assert,
        Is_Bound assert])
  | convert (Is_Path_Below (anscestor, descendent)) = convert (Is_Path_Above (descendent, anscestor))
  | convert (Is_Parent_Of (parent, child)) =
    let
      val non_exist = get_new_name [parent, child];
    in
      convert(
          Is_Path_Above (parent, child)
        And
          Not
           (Somes ([(non_exist, SeLFiE_Util.QFull_Path)],
                Is_Path_Above (Variable non_exist, child)
              And
                Is_Path_Below (Variable non_exist, parent))))
    end
  | convert (Is_Child_Of (child, parent)) = convert (Is_Parent_Of (parent, child))
  | convert (Is_An_Arg_Of (func, arg)) =
    let
      val func_app_str = get_new_name [func, arg]: string;
      val func_app     = Variable func_app_str   : assert;
    in
      convert
       (Somes ([(func_app_str, SU.QFull_Path)],
          Ands
           [Is_Parent_Of (func_app, func),
            Is_Nth_Child (Number 0, func_app),
            Is_Parent_Of (func_app, arg),
            Not (Is_Nth_Child (func_app, Number 0)),
            Is_App func_app]))
    end
  | convert (Is_Nth_Arg_Of (func, number, arg)) =
    let
      val func_app_str = get_new_name [func, arg]: string;
      val func_app     = Variable func_app_str   : assert;
    in
      convert
       (Somes ([(func_app_str, SU.QFull_Path)],
          Ands
           [Is_Parent_Of (func_app, func),
            Is_Nth_Child (Number 0, func_app),
            Is_Parent_Of (func_app, arg),
            Is_Nth_Child (number, func_app),
            Is_App (func_app)]))
    end
  | convert (Is_At_Deepest assert) =
    let
      val non_exist_str = get_new_name [assert] : string;
      val non_exist     = Variable non_exist_str: assert;
    in
    convert
      (Not
       (Somes ([(non_exist_str, SU.QFull_Path)],
         Is_Path_Above (assert, non_exist))))
    end
  | convert (Somes_Of ([], _)) = error "convert in Eval_Syntactic_Sugar.ML failed at Some_Occurrences_Of with an empty list."
  | convert (Somes_Of ((occ:string, prnt:assert)::[], inner_assert)) =
    convert
     (Somes ([(occ, SU.QFull_Path)],
          Unode_Has_Print (Variable occ, prnt)
        And
          inner_assert))
  | convert (Somes_Of ((occ:string, prnt:assert)::pairs, inner_assert)) =
    convert
     (Somes ([(occ, SU.QFull_Path)],
          Unode_Has_Print (Variable occ, prnt)
        And
          (Somes_Of (pairs, inner_assert))))
  | convert (Alls_Of (pairs, inner_assert)) = convert (Not (Somes_Of (pairs, Not inner_assert)))

fun eval (term:term) (pst:Proof.state) (ind_args:SU.induct_arguments) (assert:assert) =
    ES.eval term pst ind_args (convert assert);

end;