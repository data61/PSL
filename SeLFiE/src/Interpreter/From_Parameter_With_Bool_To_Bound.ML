(*  Title:      PSL/SeLFeE/src/Interpreter/From_Parameter_With_Bool_To_Bound.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    This file contains signatures, structures, and functors to support lambda abstraction in SeLFiE.
    The three functions (shift, subst, and eval) in this file are inspired by the functions of the 
    same names found in "ML for the Working Programmer" written by Larry C. Paulson.
*)
functor from_Parameter_With_Bool_to_Bound (Eval_Parameter_With_Bool:EVAL_PARAMETER_WITH_BOOL): EVAL_BOUND =
struct

structure EPWB = Eval_Parameter_With_Bool;

type path    = EPWB.path;
type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of print
| String  of string
| Number  of number
| Int     of int
| Command of command;

fun here_to_there (Bool b)    = EPWB.Bool b
  | here_to_there (Path p)    = EPWB.Path p
  | here_to_there (Print p)   = EPWB.Print p
  | here_to_there (String s)  = EPWB.String s
  | here_to_there (Number n)  = EPWB.Number n
  | here_to_there (Int i)     = EPWB.Int i
  | here_to_there (Command i) = EPWB.Command i;

fun there_to_here (EPWB.Bool b)    = Bool b
  | there_to_here (EPWB.Path p)    = Path p
  | there_to_here (EPWB.Print p)   = Print p
  | there_to_here (EPWB.String s)  = String s
  | there_to_here (EPWB.Number n)  = Number n
  | there_to_here (EPWB.Int i)     = Int i
  | there_to_here (EPWB.Command i) = Command i;

datatype atomic_assert =
(*Eval_Node*)
  Is_Cnst
| Is_Free
| Is_Var
| Is_Bound
| Is_Lambda
| Is_App
(*Eval_Unode*)
| Has_Same_Prnt_As
| Is_In_Trm_Prnt
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Path_Above
| Is_Same_Path_As
(*Eval_Print*)
| Are_Same_Prints
| Is_Printed_As
(*Eval_Path*)
| Unode_Has_Print
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Int;

fun convert_parameter_assert Is_Cnst           = EPWB.Is_Cnst
  | convert_parameter_assert Is_Free           = EPWB.Is_Free
  | convert_parameter_assert Is_Var            = EPWB.Is_Var
  | convert_parameter_assert Is_Bound          = EPWB.Is_Bound
  | convert_parameter_assert Is_Lambda         = EPWB.Is_Lambda
  | convert_parameter_assert Is_App            = EPWB.Is_App
  | convert_parameter_assert Has_Same_Prnt_As  = EPWB.Has_Same_Prnt_As
  | convert_parameter_assert Is_In_Trm_Prnt    = EPWB.Is_In_Trm_Prnt
  | convert_parameter_assert Is_Deeper_Than    = EPWB.Is_Deeper_Than
  | convert_parameter_assert Is_Shallower_Than = EPWB.Is_Shallower_Than
  | convert_parameter_assert Is_Path_Above     = EPWB.Is_Path_Above
  | convert_parameter_assert Is_Same_Path_As   = EPWB.Is_Same_Path_As
  | convert_parameter_assert Are_Same_Prints   = EPWB.Are_Same_Prints
  | convert_parameter_assert Is_Printed_As     = EPWB.Is_Printed_As
  | convert_parameter_assert Unode_Has_Print   = EPWB.Unode_Has_Print
  | convert_parameter_assert Are_Same_Number   = EPWB.Are_Same_Number
  | convert_parameter_assert Is_Less_Than      = EPWB.Is_Less_Than
  | convert_parameter_assert Is_Int            = EPWB.Is_Int;

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

fun convert_assert Not   = EPWB.Not
  | convert_assert And   = EPWB.And
  | convert_assert Or    = EPWB.Or
  | convert_assert Nor   = EPWB.Nor
  | convert_assert Imply = EPWB.Imply
  | convert_assert Ands  = EPWB.Ands
  | convert_assert Ors   = EPWB.Ors
  | convert_assert (Atomic assert) = EPWB.Atomic (convert_parameter_assert assert);

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Literal    of parameter
| Assert     of assert * expr list;

fun shift 0 _ u                     = u
  | shift i d (Bound j)             = if j >= d then Bound (j+i) else Bound j
  | shift i d (Lambda t)            = Lambda (shift i (d+1) t)
  | shift i d (Apply (t, u))        = Apply (shift i d t, shift i d u)
  | shift _ _ (Literal param)       = Literal param
  | shift i d (Assert (ass, exprs)) = Assert (ass, map (shift i d) exprs);

fun subst i u (Bound j) =
      if      j < i then Bound j (*locally bound*)
      else if j = i then shift i 0 u
      else               Bound (j-1)
  | subst i u (Lambda t)            = Lambda (subst (i+1) u t)
  | subst i u (Apply (t1, t2))      = Apply (subst i u t1, subst i u t2)
  | subst _ _ (Literal param)       = Literal param
  | subst i u (Assert (ass, exprs)) = Assert (ass, map (subst i u) exprs);

fun eval_prim (Literal param) = here_to_there param
  | eval_prim  _              = error "eval_prim in Eval_Bound_Struct failed!"

fun eval (trm:term) (pst:Proof.state) (expr:expr) =
  let
    fun eval' (Apply (trm1, trm2)) = (case eval' trm1 of
          Lambda u => eval' (subst 0 (eval' trm2) u)
        | u1       => Apply (u1, eval' trm2))
      | eval' (Assert (assert, param_exprs)) =
          let
            (* Note that param_exprs are always Literal at this point
             * because the evaluation function in From_Variable_To_Quantifier evaluated
             * param_exprs eagerly.*)
            val params = map eval_prim param_exprs: EPWB.parameters;
          in
            EPWB.eval trm pst (convert_assert assert) params |> there_to_here |> Literal
          end
      | eval' t = t
  in
    eval' expr
  end;

end;