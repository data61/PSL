(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Surface.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

In Eval_Surface_Two, I try to implement the conversion between Surface and Deep
by considering Surface as a syntactic sugar of Deep.
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
| Is_Cnst    of assert
| Is_Free    of assert
| Is_Var     of assert
| Is_Bound   of assert
| Is_Lambda  of assert
| Is_App     of assert
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
(*Eval_Path*)
| Unode_Has_Print        of assert * assert
| Is_In_Subgoal          of assert
| Is_In_Chained_Fact     of assert
| Is_In_Nth_Subgoal      of assert * assert
| Is_In_Nth_Chained_Fact of assert * assert
(*Eval_Number*)
| Are_Same_Number   of assert * assert
| Is_Less_Than      of assert * assert
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
(*
| In_Some_Definitions of (assert * assert * assert list)
*)
| Outermost           of assert;

val eval: Proof.state -> SeLFiE_Util.induct_arguments -> assert -> assert;

end;

(*** Eval_Surface ***)
structure Eval_Surface: EVAL_SURFACE =
struct

structure ED = Eval_Deep;
structure SU = SeLFiE_Util;

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
| Print  of string
| Number of int
(*expr*)
| Variable            of string
| Lambdas             of strings * assert
| Applies             of assert  * assert list
| Alls                of (string * SU.qtyp) list * assert
| Somes               of (string * SU.qtyp) list * assert
| In_All_Definitions  of (assert * assert * assert list)
| Outermost           of assert;

datatype tag = Syntax | Semantics;

fun outer_surf_to_outer_deep_pair_to_list p = Utils.map_pair outer_surf_to_outer_deep p |> Utils.pair_to_list
and outer_surf_to_outer_deep_list ps = map outer_surf_to_outer_deep ps
and outer_surf_to_outer_deep_singleton p = outer_surf_to_outer_deep_list [p]
and (*bool*)
    outer_surf_to_outer_deep  True         = ED.Outer_Literal (ED.Outer_Non_Path (SU.Bool true))
  | outer_surf_to_outer_deep  False        = ED.Outer_Literal (ED.Outer_Non_Path (SU.Bool false))
  | outer_surf_to_outer_deep (Not   arg)   = ED.Outer_Assert  (SU.Not,  [outer_surf_to_outer_deep arg])
  | outer_surf_to_outer_deep (And   args)  = ED.Outer_Assert  (SU.And,   outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Or    args)  = ED.Outer_Assert  (SU.Or,    outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Nor   args)  = ED.Outer_Assert  (SU.Nor,   outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Imply args)  = ED.Outer_Assert  (SU.Imply, outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Ands  args)  = ED.Outer_Assert  (SU.Ands,  outer_surf_to_outer_deep_list args)
  | outer_surf_to_outer_deep (Ors   args)  = ED.Outer_Assert  (SU.Ors,   outer_surf_to_outer_deep_list args)
  (*Eval_Node*)
  | outer_surf_to_outer_deep (Is_Cnst   arg) = ED.Outer_Assert  (SU.Atomic SU.Is_Cnst,   outer_surf_to_outer_deep_singleton arg)
  | outer_surf_to_outer_deep (Is_Free   arg) = ED.Outer_Assert  (SU.Atomic SU.Is_Free,   outer_surf_to_outer_deep_singleton arg)
  | outer_surf_to_outer_deep (Is_Var    arg) = ED.Outer_Assert  (SU.Atomic SU.Is_Var,    outer_surf_to_outer_deep_singleton arg)
  | outer_surf_to_outer_deep (Is_Bound  arg) = ED.Outer_Assert  (SU.Atomic SU.Is_Bound,  outer_surf_to_outer_deep_singleton arg)
  | outer_surf_to_outer_deep (Is_Lambda arg) = ED.Outer_Assert  (SU.Atomic SU.Is_Lambda, outer_surf_to_outer_deep_singleton arg)
  | outer_surf_to_outer_deep (Is_App    arg) = ED.Outer_Assert  (SU.Atomic SU.Is_App,    outer_surf_to_outer_deep_singleton arg)
  (*Eval_Unode*)
  | outer_surf_to_outer_deep (Has_Same_Prnt_As       args) = ED.Outer_Assert (SU.Atomic SU.Has_Same_Prnt_As,       outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Is_In_Trm_Prnt         args) = ED.Outer_Assert (SU.Atomic SU.Is_In_Trm_Prnt,         outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Is_Deeper_Than         args) = ED.Outer_Assert (SU.Atomic SU.Is_Deeper_Than,         outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Is_Shallower_Than      args) = ED.Outer_Assert (SU.Atomic SU.Is_Shallower_Than,      outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Is_Path_Above          args) = ED.Outer_Assert (SU.Atomic SU.Is_Path_Above,          outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Is_Same_Path_As        args) = ED.Outer_Assert (SU.Atomic SU.Is_Same_Path_As,        outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Is_Nth_Child           args) = ED.Outer_Assert (SU.Atomic SU.Is_Nth_Child,           outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Is_N_Plus_One_th_Child args) = ED.Outer_Assert (SU.Atomic SU.Is_N_Plus_One_th_Child, outer_surf_to_outer_deep_pair_to_list args)
  (*Eval_Print*)
  | outer_surf_to_outer_deep (Are_Same_Prints args) = ED.Outer_Assert (SU.Atomic SU.Are_Same_Prints, outer_surf_to_outer_deep_pair_to_list args)
  (*Eval_Path*)
  | outer_surf_to_outer_deep (Unode_Has_Print        args) = ED.Outer_Assert (SU.Atomic SU.Unode_Has_Print,        outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Is_In_Subgoal          arg ) = ED.Outer_Assert (SU.Atomic SU.Is_In_Subgoal,          outer_surf_to_outer_deep_singleton    arg )
  | outer_surf_to_outer_deep (Is_In_Chained_Fact     arg ) = ED.Outer_Assert (SU.Atomic SU.Unode_Has_Print,        outer_surf_to_outer_deep_singleton    arg )
  | outer_surf_to_outer_deep (Is_In_Nth_Subgoal      args) = ED.Outer_Assert (SU.Atomic SU.Unode_Has_Print,        outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Is_In_Nth_Chained_Fact args) = ED.Outer_Assert (SU.Atomic SU.Is_In_Nth_Chained_Fact, outer_surf_to_outer_deep_pair_to_list args)
  (*Eval_Number*)
  | outer_surf_to_outer_deep (Are_Same_Number args) = ED.Outer_Assert (SU.Atomic SU.Are_Same_Number, outer_surf_to_outer_deep_pair_to_list args)
  | outer_surf_to_outer_deep (Is_Less_Than    args) = ED.Outer_Assert (SU.Atomic SU.Is_Less_Than,    outer_surf_to_outer_deep_pair_to_list args)
  (*parameter*)
  | outer_surf_to_outer_deep (Print  p) = ED.Outer_Literal (ED.Outer_Non_Path (SU.Print  p))
  | outer_surf_to_outer_deep (Number n) = ED.Outer_Literal (ED.Outer_Non_Path (SU.Number n))
  (*expr*)
  | outer_surf_to_outer_deep (Variable vname)          = ED.Outer_Variable vname
  | outer_surf_to_outer_deep (Lambdas (vnames, fbody)) =
   (tracing "outer_surf_to_outer_deep for Lambdas";
    ED.Outer_Lambdas ((tracing "outer_surf_to_outer_deep for Lambdas vname"; vnames),
     (tracing "outer_surf_to_outer_deep for Lambdas fbody"; outer_surf_to_outer_deep fbody))
    )
  | outer_surf_to_outer_deep (Applies (func,   args))  = ED.Outer_Applies (outer_surf_to_outer_deep func, outer_surf_to_outer_deep_list args)
  | outer_surf_to_outer_deep (Alls    (vars,   body))  = ED.Outer_Alls    (vars, outer_surf_to_outer_deep body)
  | outer_surf_to_outer_deep (Somes   (vars,   body))  = ED.Outer_Somes   (vars, outer_surf_to_outer_deep body)
  | outer_surf_to_outer_deep (In_All_Definitions (target, inner_lambda, outer_args)) =
    ED.Dive_In (outer_surf_to_outer_deep target,
                inner_surf_to_inner_deep inner_lambda,
                outer_surf_to_outer_deep_list outer_args)
  | outer_surf_to_outer_deep (Outermost expr) = outer_surf_to_outer_deep expr
and inner_surf_to_inner_deep_pair_to_list p = Utils.map_pair inner_surf_to_inner_deep p |> Utils.pair_to_list
and inner_surf_to_inner_deep_list ps = map inner_surf_to_inner_deep ps
and inner_surf_to_inner_deep_singleton p = inner_surf_to_inner_deep_list [p]
and (*bool*)
    inner_surf_to_inner_deep  True         = ED.Inner_Literal (ED.Inner_Non_Path (SU.Bool true))
  | inner_surf_to_inner_deep  False        = ED.Inner_Literal (ED.Inner_Non_Path (SU.Bool false))
  | inner_surf_to_inner_deep (Not   arg)   = ED.Inner_Assert  (SU.Not,  [inner_surf_to_inner_deep arg])
  | inner_surf_to_inner_deep (And   args)  = ED.Inner_Assert  (SU.And,   inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Or    args)  = ED.Inner_Assert  (SU.Or,    inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Nor   args)  = ED.Inner_Assert  (SU.Nor,   inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Imply args)  = ED.Inner_Assert  (SU.Imply, inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Ands  args)  = ED.Inner_Assert  (SU.Ands,  inner_surf_to_inner_deep_list args)
  | inner_surf_to_inner_deep (Ors   args)  = ED.Inner_Assert  (SU.Ors,   inner_surf_to_inner_deep_list args)
  (*Eval_Node*)
  | inner_surf_to_inner_deep (Is_Cnst   arg) = ED.Inner_Assert  (SU.Atomic SU.Is_Cnst,   inner_surf_to_inner_deep_singleton arg)
  | inner_surf_to_inner_deep (Is_Free   arg) = ED.Inner_Assert  (SU.Atomic SU.Is_Free,   inner_surf_to_inner_deep_singleton arg)
  | inner_surf_to_inner_deep (Is_Var    arg) = ED.Inner_Assert  (SU.Atomic SU.Is_Var,    inner_surf_to_inner_deep_singleton arg)
  | inner_surf_to_inner_deep (Is_Bound  arg) = ED.Inner_Assert  (SU.Atomic SU.Is_Bound,  inner_surf_to_inner_deep_singleton arg)
  | inner_surf_to_inner_deep (Is_Lambda arg) = ED.Inner_Assert  (SU.Atomic SU.Is_Lambda, inner_surf_to_inner_deep_singleton arg)
  | inner_surf_to_inner_deep (Is_App    arg) = ED.Inner_Assert  (SU.Atomic SU.Is_App,    inner_surf_to_inner_deep_singleton arg)
  (*Eval_Unode*)
  | inner_surf_to_inner_deep (Has_Same_Prnt_As       args) = ED.Inner_Assert (SU.Atomic SU.Has_Same_Prnt_As,       inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Is_In_Trm_Prnt         args) = ED.Inner_Assert (SU.Atomic SU.Is_In_Trm_Prnt,         inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Is_Deeper_Than         args) = ED.Inner_Assert (SU.Atomic SU.Is_Deeper_Than,         inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Is_Shallower_Than      args) = ED.Inner_Assert (SU.Atomic SU.Is_Shallower_Than,      inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Is_Path_Above          args) = ED.Inner_Assert (SU.Atomic SU.Is_Path_Above,          inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Is_Same_Path_As        args) = ED.Inner_Assert (SU.Atomic SU.Is_Same_Path_As,        inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Is_Nth_Child           args) = ED.Inner_Assert (SU.Atomic SU.Is_Nth_Child,           inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Is_N_Plus_One_th_Child args) = ED.Inner_Assert (SU.Atomic SU.Is_N_Plus_One_th_Child, inner_surf_to_inner_deep_pair_to_list args)
  (*Eval_Print*)
  | inner_surf_to_inner_deep (Are_Same_Prints args) = ED.Inner_Assert (SU.Atomic SU.Are_Same_Prints, inner_surf_to_inner_deep_pair_to_list args)
  (*Eval_Path*)
  | inner_surf_to_inner_deep (Unode_Has_Print        args) = ED.Inner_Assert (SU.Atomic SU.Unode_Has_Print,        inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Is_In_Subgoal          arg ) = ED.Inner_Assert (SU.Atomic SU.Is_In_Subgoal,          inner_surf_to_inner_deep_singleton    arg )
  | inner_surf_to_inner_deep (Is_In_Chained_Fact     arg ) = ED.Inner_Assert (SU.Atomic SU.Unode_Has_Print,        inner_surf_to_inner_deep_singleton    arg )
  | inner_surf_to_inner_deep (Is_In_Nth_Subgoal      args) = ED.Inner_Assert (SU.Atomic SU.Unode_Has_Print,        inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Is_In_Nth_Chained_Fact args) = ED.Inner_Assert (SU.Atomic SU.Is_In_Nth_Chained_Fact, inner_surf_to_inner_deep_pair_to_list args)
  (*Eval_Number*)
  | inner_surf_to_inner_deep (Are_Same_Number args) = ED.Inner_Assert (SU.Atomic SU.Are_Same_Number, inner_surf_to_inner_deep_pair_to_list args)
  | inner_surf_to_inner_deep (Is_Less_Than    args) = ED.Inner_Assert (SU.Atomic SU.Is_Less_Than,    inner_surf_to_inner_deep_pair_to_list args)
  (*parameter*)
  | inner_surf_to_inner_deep (Print  p) = ED.Inner_Literal (ED.Inner_Non_Path (SU.Print  p))
  | inner_surf_to_inner_deep (Number n) = ED.Inner_Literal (ED.Inner_Non_Path (SU.Number n))
  (*expr*)
  | inner_surf_to_inner_deep (Variable vname)          = ED.Inner_Variable vname
  | inner_surf_to_inner_deep (Lambdas (vnames, fbody)) = ED.Inner_Lambdas (vnames, inner_surf_to_inner_deep fbody)
  | inner_surf_to_inner_deep (Applies (func,   args))  = ED.Inner_Applies (inner_surf_to_inner_deep func, inner_surf_to_inner_deep_list args)
  | inner_surf_to_inner_deep (Alls    (vars,   body))  = ED.Inner_Alls    (vars, inner_surf_to_inner_deep body)
  | inner_surf_to_inner_deep (Somes   (vars,   body))  = ED.Inner_Somes   (vars, inner_surf_to_inner_deep body)
  | inner_surf_to_inner_deep (In_All_Definitions (target, inner_lambda, inner_args)) =
    ED.Dive_Deeper (inner_surf_to_inner_deep target,
                   inner_surf_to_inner_deep inner_lambda,
                    inner_surf_to_inner_deep_list inner_args)
  | inner_surf_to_inner_deep (Outermost _) = error "inner_surf_to_inner_deep in Eval_Surface_Two.ML failed at Outermost."

fun inner_surf_to_inner_deep _ = error "TODO";

fun surf_to_deep' Syntax    expr = outer_surf_to_outer_deep expr
  | surf_to_deep' Semantics expr = inner_surf_to_inner_deep expr;

fun surf_to_deep (Outermost expr) = surf_to_deep' Syntax expr
  | surf_to_deep _ = error "surf_to_deep in Eval_Surface_Two failed. The outermost construct has to be Outermost.";

fun come_back_expression (ED.Outer (ED.Outer_Literal (ED.Outer_Non_Path (SU.Bool bool)))) = if bool then True else False
  | come_back_expression  _                                                               = error "come_back_expression in Eval_Surface.ML failed."

fun eval (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) (assert:assert) =
  let
    val expr_deep = outer_surf_to_outer_deep assert             : ED.outer_expression;
    val result_ed = ED.eval pst induct_args (ED.Outer expr_deep): ED.expr;
  in
    come_back_expression result_ed
  end;

end;