(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Surface.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** signature: EVAL_SURFACE ***)
signature EVAL_SURFACE =
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
| Is_Root_In_A_Location  of assert
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
| Dive_In             of assert * assert * assert list
| Deep_Dive           of assert * assert * assert list
(*debug*)
| Debug_Non_Path_Literal of assert
| Debug_Print_Unode      of assert
| Dummy;

val eval: Proof.state -> Outer_Path_To_Unode.path_to_unode_table -> SeLFiE_Util.induct_arguments -> assert -> assert;

end;

(*** structure: Eval_Surface ***)
structure Eval_Surface: EVAL_SURFACE =
struct

structure SU = SeLFiE_Util;
structure EV = Eval_Variable;
structure EP = Eval_Parameter;

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
| Is_Root_In_A_Location  of assert 
(*Eval_Print*)
| Print_Is_Cnst     of assert
| Print_Is_Free     of assert
| Print_Is_Var      of assert
| Print_Is_Bound    of assert (*corresponds to Bound in term*)
| Print_Is_Lambda   of assert (*lambda abstraction corresponding to Abs in Term*)
| Print_Is_App      of assert (*function application corresponding to $ in Term*)
| Are_Same_Prints   of assert * assert
| Is_Subprint_Of    of assert * assert
| Is_Nth_Induct     of assert * assert
| Is_Nth_Arbitrary  of assert * assert
| Is_Induct         of assert
| Is_Arbitrary      of assert
| Is_Rule           of assert
| Is_Rule_Of_Print  of assert * assert
(*Eval_Print for node*)
| Print_Is_Defined_With             of assert * assert
| Print_Takes_N_Arguments           of assert * assert
| Print_Is_Defined_With_N_Clauses   of assert * assert
| Print_Takes_Less_Than_N_Arguments of assert * assert
(*Eval_Path*)
| Unode_Has_Print        of assert * assert
| Is_In_Subgoal          of assert
| Is_In_Chained_Fact     of assert
| Is_In_Nth_Subgoal      of assert * assert
| Is_In_Nth_Chained_Fact of assert * assert
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
| All                 of string * SU.qtyp * assert
| Some                of string * SU.qtyp * assert
| Dive_In             of assert * assert * assert list
| Deep_Dive           of assert * assert * assert list
(*debug*)
| Debug_Non_Path_Literal of assert
| Debug_Print_Unode      of assert
| Dummy;

fun surf_to_var_pair_to_list p = Utils.map_pair surf_to_var p |> Utils.pair_to_list
and surf_to_var_list ps = map surf_to_var ps
and surf_to_var_singleton p = surf_to_var_list [p]
and (*bool*)
    surf_to_var  True         = EV.Literal (EP.Non_Path (EP.Bool true))
  | surf_to_var  False        = EV.Literal (EP.Non_Path (EP.Bool false))
  | surf_to_var (Not   arg)   = EV.Assert  (SU.Not,   surf_to_var_singleton arg)
  | surf_to_var (And   args)  = EV.Assert  (SU.And,   surf_to_var_pair_to_list args)
  | surf_to_var (Or    args)  = EV.Assert  (SU.Or,    surf_to_var_pair_to_list args)
  | surf_to_var (Nor   args)  = EV.Assert  (SU.Nor,   surf_to_var_pair_to_list args)
  | surf_to_var (Imply args)  = EV.Assert  (SU.Imply, surf_to_var_pair_to_list args)
  | surf_to_var (Ands  args)  = EV.Assert  (SU.Ands,  surf_to_var_list args)
  | surf_to_var (Ors   args)  = EV.Assert  (SU.Ors,   surf_to_var_list args)
  (*Eval_Node*)
  | surf_to_var (Node_Is_Cnst                     arg ) = EV.Assert (SU.Atomic SU.Node_Is_Cnst,                     surf_to_var_singleton    arg)
  | surf_to_var (Node_Is_Free                     arg ) = EV.Assert (SU.Atomic SU.Node_Is_Free,                     surf_to_var_singleton    arg)
  | surf_to_var (Node_Is_Var                      arg ) = EV.Assert (SU.Atomic SU.Node_Is_Var,                      surf_to_var_singleton    arg)
  | surf_to_var (Node_Is_Bound                    arg ) = EV.Assert (SU.Atomic SU.Node_Is_Bound,                    surf_to_var_singleton    arg)
  | surf_to_var (Node_Is_Lambda                   arg ) = EV.Assert (SU.Atomic SU.Node_Is_Lambda,                   surf_to_var_singleton    arg)
  | surf_to_var (Node_Is_App                      arg ) = EV.Assert (SU.Atomic SU.Node_Is_App,                      surf_to_var_singleton    arg)
  | surf_to_var (Node_Is_Defined_With             args) = EV.Assert (SU.Atomic SU.Node_Is_Defined_With,             surf_to_var_pair_to_list args)
  | surf_to_var (Node_Is_Defined_With_N_Clauses   args) = EV.Assert (SU.Atomic SU.Node_Is_Defined_With_N_Clauses,   surf_to_var_pair_to_list args)
  | surf_to_var (Is_Rule_Of_Node                  pair) = EV.Assert (SU.Atomic SU.Is_Rule_Of_Node,                  surf_to_var_pair_to_list pair)
  | surf_to_var (Node_Takes_N_Arguments           pair) = EV.Assert (SU.Atomic SU.Node_Takes_N_Arguments,           surf_to_var_pair_to_list pair)
  | surf_to_var (Node_Takes_Less_Than_N_Arguments pair) = EV.Assert (SU.Atomic SU.Node_Takes_Less_Than_N_Arguments, surf_to_var_pair_to_list pair)
  (*Eval_Unode*)
  | surf_to_var (Has_Same_Prnt_As       args) = EV.Assert (SU.Atomic SU.Has_Same_Prnt_As,       surf_to_var_pair_to_list args)
  | surf_to_var (Is_Deeper_Than         args) = EV.Assert (SU.Atomic SU.Is_Deeper_Than,         surf_to_var_pair_to_list args)
  | surf_to_var (Is_Shallower_Than      args) = EV.Assert (SU.Atomic SU.Is_Shallower_Than,      surf_to_var_pair_to_list args)
  | surf_to_var (Is_Path_Above          args) = EV.Assert (SU.Atomic SU.Is_Path_Above,          surf_to_var_pair_to_list args)
  | surf_to_var (Is_Same_Path_As        args) = EV.Assert (SU.Atomic SU.Is_Same_Path_As,        surf_to_var_pair_to_list args)
  | surf_to_var (Is_Nth_Child           args) = EV.Assert (SU.Atomic SU.Is_Nth_Child,           surf_to_var_pair_to_list args)
  | surf_to_var (Is_N_Plus_One_th_Child args) = EV.Assert (SU.Atomic SU.Is_N_Plus_One_th_Child, surf_to_var_pair_to_list args)
  | surf_to_var (Is_Root_In_A_Location  arg ) = EV.Assert (SU.Atomic SU.Is_Root_In_A_Location , surf_to_var_singleton    arg )
  (*Eval_Print*)
  | surf_to_var (Are_Same_Prints  args) = EV.Assert (SU.Atomic SU.Are_Same_Prints,  surf_to_var_pair_to_list args)
  | surf_to_var (Is_Subprint_Of   args) = EV.Assert (SU.Atomic SU.Is_Subprint_Of ,  surf_to_var_pair_to_list args)
  | surf_to_var (Is_Nth_Induct    args) = EV.Assert (SU.Atomic SU.Is_Nth_Induct,    surf_to_var_pair_to_list args)
  | surf_to_var (Is_Nth_Arbitrary args) = EV.Assert (SU.Atomic SU.Is_Nth_Arbitrary, surf_to_var_pair_to_list args)
  | surf_to_var (Is_Induct        arg ) = EV.Assert (SU.Atomic SU.Is_Induct,        surf_to_var_singleton    arg )
  | surf_to_var (Is_Arbitrary     arg ) = EV.Assert (SU.Atomic SU.Is_Arbitrary,     surf_to_var_singleton    arg )
  | surf_to_var (Is_Rule          arg ) = EV.Assert (SU.Atomic SU.Is_Rule,          surf_to_var_singleton    arg )
  | surf_to_var (Is_Rule_Of_Print args) = EV.Assert (SU.Atomic SU.Is_Rule_Of_Print, surf_to_var_pair_to_list args)
  (*Eval_Print for node*)
  | surf_to_var (Print_Is_Cnst                     arg ) = EV.Assert (SU.Atomic SU.Print_Is_Cnst,                     surf_to_var_singleton    arg)
  | surf_to_var (Print_Is_Free                     arg ) = EV.Assert (SU.Atomic SU.Print_Is_Free,                     surf_to_var_singleton    arg)
  | surf_to_var (Print_Is_Var                      arg ) = EV.Assert (SU.Atomic SU.Print_Is_Var,                      surf_to_var_singleton    arg)
  | surf_to_var (Print_Is_Bound                    arg ) = EV.Assert (SU.Atomic SU.Print_Is_Bound,                    surf_to_var_singleton    arg)
  | surf_to_var (Print_Is_Lambda                   arg ) = EV.Assert (SU.Atomic SU.Print_Is_Lambda,                   surf_to_var_singleton    arg)
  | surf_to_var (Print_Is_App                      arg ) = EV.Assert (SU.Atomic SU.Print_Is_App,                      surf_to_var_singleton    arg)
  | surf_to_var (Print_Is_Defined_With             args) = EV.Assert (SU.Atomic SU.Print_Is_Defined_With,             surf_to_var_pair_to_list args)
  | surf_to_var (Print_Is_Defined_With_N_Clauses   args) = EV.Assert (SU.Atomic SU.Print_Is_Defined_With_N_Clauses,   surf_to_var_pair_to_list args)
  | surf_to_var (Print_Takes_N_Arguments           args) = EV.Assert (SU.Atomic SU.Print_Takes_N_Arguments,           surf_to_var_pair_to_list args)
  | surf_to_var (Print_Takes_Less_Than_N_Arguments args) = EV.Assert (SU.Atomic SU.Print_Takes_Less_Than_N_Arguments, surf_to_var_pair_to_list args)
  (*Eval_Path*)
  | surf_to_var (Unode_Has_Print        args) = EV.Assert (SU.Atomic SU.Unode_Has_Print,        surf_to_var_pair_to_list args)
  | surf_to_var (Is_In_Subgoal          arg ) = EV.Assert (SU.Atomic SU.Is_In_Subgoal,          surf_to_var_singleton    arg )
  | surf_to_var (Is_In_Chained_Fact     arg ) = EV.Assert (SU.Atomic SU.Is_In_Chained_Fact,     surf_to_var_singleton    arg )
  | surf_to_var (Is_In_Nth_Subgoal      args) = EV.Assert (SU.Atomic SU.Is_In_Nth_Subgoal,      surf_to_var_pair_to_list args)
  | surf_to_var (Is_In_Nth_Chained_Fact args) = EV.Assert (SU.Atomic SU.Is_In_Nth_Chained_Fact, surf_to_var_pair_to_list args)
  (*Eval_Number*)
  | surf_to_var (Are_Same_Number     args) = EV.Assert (SU.Atomic SU.Are_Same_Number,     surf_to_var_pair_to_list args)
  | surf_to_var (Is_Less_Than        args) = EV.Assert (SU.Atomic SU.Is_Less_Than,        surf_to_var_pair_to_list args)
  | surf_to_var (Is_Less_Than_By_One args) = EV.Assert (SU.Atomic SU.Is_Less_Than_By_One, surf_to_var_pair_to_list args)
  (*parameter*)
  | surf_to_var (Print   p) = EV.Literal (EP.Non_Path (EP.Print   p))
  | surf_to_var (Number  n) = EV.Literal (EP.Non_Path (EP.Number  n))
  | surf_to_var (Command c) = EV.Literal (EP.Non_Path (EP.Command c))
  (*expr*)
  | surf_to_var (Variable vname)             = EV.Variable vname
  | surf_to_var (Lambdas (vnames, fbody))    = EV.Lambdas (vnames, surf_to_var fbody)
  | surf_to_var (Applies (func,   args))     = EV.Applies (surf_to_var func, surf_to_var_list args)
  | surf_to_var (All     (vname, typ, body)) = EV.All  (vname, typ, surf_to_var body)
  | surf_to_var (Some    (vname, typ, body)) = EV.Some (vname, typ, surf_to_var body)
  | surf_to_var (Dive_In   (target, inner_lambda, outer_args)) = EV.Dive_In   (surf_to_var target, surf_to_var inner_lambda, surf_to_var_list outer_args)
  | surf_to_var (Deep_Dive (target, inner_lambda, outer_args)) = EV.Deep_Dive (surf_to_var target, surf_to_var inner_lambda, surf_to_var_list outer_args)
  (*debug*)
  | surf_to_var (Debug_Non_Path_Literal assert) = EV.Assert (SU.Atomic SU.Debug_Non_Path_Literal, surf_to_var_singleton assert)
  | surf_to_var (Debug_Print_Unode      assert) = EV.Assert (SU.Atomic SU.Debug_Print_Unode,      surf_to_var_singleton assert)
  | surf_to_var  Dummy                          = EV.Assert (SU.Atomic SU.Dummy,                  []                          )

fun deep_to_surface (EV.Literal (EP.Non_Path (EP.Bool b))) = if b then True else False
  | deep_to_surface (EV.Variable vname) = Variable vname
  | deep_to_surface _ = error "deep_to_surface failed.";

fun eval (pst:Proof.state) (path_to_unode_table:Outer_Path_To_Unode.path_to_unode_table) (induct_args:SeLFiE_Util.induct_arguments) (assert:assert) =
  let
    val var_expr  = surf_to_var assert                                  : EV.expr;
    val result_ev = EV.eval pst path_to_unode_table induct_args var_expr: EV.expr;
    val result    = deep_to_surface result_ev                           : assert;
  in
    result
  end;

end;