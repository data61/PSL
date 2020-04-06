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
| All                 of string * SeLFiE_Util.qtyp * assert
| Some                of string * SeLFiE_Util.qtyp * assert
| Dive_In             of assert * assert * assert list
| Deep_Dive           of assert * assert * assert list;

val eval: Proof.state -> SeLFiE_Util.induct_arguments -> assert -> assert;

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
| All                 of string * SU.qtyp * assert
| Some                of string * SU.qtyp * assert
| Dive_In             of assert * assert * assert list
| Deep_Dive           of assert * assert * assert list;

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
  | surf_to_var (Is_Cnst   arg) = EV.Assert  (SU.Atomic SU.Is_Cnst,   surf_to_var_singleton arg)
  | surf_to_var (Is_Free   arg) = EV.Assert  (SU.Atomic SU.Is_Free,   surf_to_var_singleton arg)
  | surf_to_var (Is_Var    arg) = EV.Assert  (SU.Atomic SU.Is_Var,    surf_to_var_singleton arg)
  | surf_to_var (Is_Bound  arg) = EV.Assert  (SU.Atomic SU.Is_Bound,  surf_to_var_singleton arg)
  | surf_to_var (Is_Lambda arg) = EV.Assert  (SU.Atomic SU.Is_Lambda, surf_to_var_singleton arg)
  | surf_to_var (Is_App    arg) = EV.Assert  (SU.Atomic SU.Is_App,    surf_to_var_singleton arg)
  (*Eval_Unode*)
  | surf_to_var (Has_Same_Prnt_As       args) = EV.Assert (SU.Atomic SU.Has_Same_Prnt_As,       surf_to_var_pair_to_list args)
  | surf_to_var (Is_In_Trm_Prnt         args) = EV.Assert (SU.Atomic SU.Is_In_Trm_Prnt,         surf_to_var_pair_to_list args)
  | surf_to_var (Is_Deeper_Than         args) = EV.Assert (SU.Atomic SU.Is_Deeper_Than,         surf_to_var_pair_to_list args)
  | surf_to_var (Is_Shallower_Than      args) = EV.Assert (SU.Atomic SU.Is_Shallower_Than,      surf_to_var_pair_to_list args)
  | surf_to_var (Is_Path_Above          args) = EV.Assert (SU.Atomic SU.Is_Path_Above,          surf_to_var_pair_to_list args)
  | surf_to_var (Is_Same_Path_As        args) = EV.Assert (SU.Atomic SU.Is_Same_Path_As,        surf_to_var_pair_to_list args)
  | surf_to_var (Is_Nth_Child           args) = EV.Assert (SU.Atomic SU.Is_Nth_Child,           surf_to_var_pair_to_list args)
  | surf_to_var (Is_N_Plus_One_th_Child args) = EV.Assert (SU.Atomic SU.Is_N_Plus_One_th_Child, surf_to_var_pair_to_list args)
  (*Eval_Print*)
  | surf_to_var (Are_Same_Prints args) = EV.Assert (SU.Atomic SU.Are_Same_Prints, surf_to_var_pair_to_list args)
  (*Eval_Path*)
  | surf_to_var (Unode_Has_Print        args) = EV.Assert (SU.Atomic SU.Unode_Has_Print,        surf_to_var_pair_to_list args)
  | surf_to_var (Is_In_Subgoal          arg ) = EV.Assert (SU.Atomic SU.Is_In_Subgoal,          surf_to_var_singleton    arg )
  | surf_to_var (Is_In_Chained_Fact     arg ) = EV.Assert (SU.Atomic SU.Unode_Has_Print,        surf_to_var_singleton    arg )
  | surf_to_var (Is_In_Nth_Subgoal      args) = EV.Assert (SU.Atomic SU.Unode_Has_Print,        surf_to_var_pair_to_list args)
  | surf_to_var (Is_In_Nth_Chained_Fact args) = EV.Assert (SU.Atomic SU.Is_In_Nth_Chained_Fact, surf_to_var_pair_to_list args)
  (*Eval_Number*)
  | surf_to_var (Are_Same_Number args) = EV.Assert (SU.Atomic SU.Are_Same_Number, surf_to_var_pair_to_list args)
  | surf_to_var (Is_Less_Than    args) = EV.Assert (SU.Atomic SU.Is_Less_Than,    surf_to_var_pair_to_list args)
  (*parameter*)
  | surf_to_var (Print  p) = EV.Literal (EP.Non_Path (EP.Print  p))
  | surf_to_var (Number n) = EV.Literal (EP.Non_Path (EP.Number n))
  (*expr*)
  | surf_to_var (Variable vname)             = EV.Variable vname
  | surf_to_var (Lambdas (vnames, fbody))    = EV.Lambdas (vnames, surf_to_var fbody)
  | surf_to_var (Applies (func,   args))     = EV.Applies (surf_to_var func, surf_to_var_list args)
  | surf_to_var (All     (vname, typ, body)) = EV.All  (vname, typ, surf_to_var body)
  | surf_to_var (Some    (vname, typ, body)) = EV.Some (vname, typ, surf_to_var body)
  | surf_to_var (Dive_In (target, inner_lambda, outer_args)) =
    EV.Dive_In (surf_to_var target, surf_to_var inner_lambda, surf_to_var_list outer_args)
  | surf_to_var (Deep_Dive (target, inner_lambda, outer_args)) =
    EV.Dive_In (surf_to_var target, surf_to_var inner_lambda, surf_to_var_list outer_args);

fun deep_to_surface (EV.Literal (EP.Non_Path (EP.Bool b))) = if b then True else False
  | deep_to_surface (EV.Variable vname) = Variable vname
  | deep_to_surface _ = error "deep_to_surface failed.";

fun eval (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) (assert:assert) =
  let
    val var_expr  = surf_to_var assert              : EV.expr;
    val result_ev = EV.eval pst induct_args var_expr: EV.expr;
    val result      = deep_to_surface result_ev     : assert;
  in
    result
  end;

end;