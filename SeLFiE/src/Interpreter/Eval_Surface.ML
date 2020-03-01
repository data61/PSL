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

fun come_back_expression (ED.Outer_Literal (ED.Outer_Non_Path (SU.Bool bool))) = if bool then True else False
  | come_back_expression  _                                                    = error "come_back_expression in Eval_Surface.ML failed."

fun eval (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) (assert:assert) =
  let
    val thm     = Isabelle_Utils.proof_state_to_thm pst: thm;
    val thm_trm = Thm.prop_of thm                      : term;
    fun ed_eval_outer                    (outer_expr:ED.outer_expression)                    = ED.eval_outer pst induct_args outer_expr thm_trm                : ED.outer_expression;
    fun ed_eval_outer_param              (param     :ED.outer_parameter)                     = ed_eval_outer (ED.Outer_Literal param)                          : ED.outer_expression;
    fun ed_eval_outer_assert_one         (ass:SU.assert,          arg:assert)                = ed_eval_outer (ED.Outer_Assert (ass, [eval_out arg]))           : ED.outer_expression
    and ed_eval_outer_assert_atomic_one  (atom:SU.atomic_assert,  arg:assert)                = ed_eval_outer_assert_one (SU.Atomic atom, arg)                  : ED.outer_expression
    and ed_eval_outer_assert_pair        (ass:SU.assert,         (arg1:assert, arg2:assert)) = ed_eval_outer (ED.Outer_Assert (ass, map eval_out [arg1, arg2])): ED.outer_expression
    and ed_eval_outer_assert_atomic_pair (atom:SU.atomic_assert, (arg1:assert, arg2:assert)) = ed_eval_outer_assert_pair (SU.Atomic atom, (arg1, arg2))        : ED.outer_expression
    and ed_eval_outer_assert_list        (assert:SU.assert,  args: assert list)              = ed_eval_outer (ED.Outer_Assert (assert, map eval_out args))     : ED.outer_expression
    and eval_enter (Outermost ass) = eval_out ass
      | eval_enter _ = error "eval in From_Deep_To_Surface.ML failed. eval is defined only for Outermost."
    and eval_out True                            = ed_eval_outer_param              (ED.Outer_Non_Path (SU.Bool true ))
      | eval_out False                           = ed_eval_outer_param              (ED.Outer_Non_Path (SU.Bool false))
      | eval_out (Not               ass)         = ed_eval_outer_assert_one         (SU.Not,                    ass)
      | eval_out (And               pair)        = ed_eval_outer_assert_pair        (SU.And,                    pair)
      | eval_out (Or                pair)        = ed_eval_outer_assert_pair        (SU.Or,                     pair)
      | eval_out (Nor               pair)        = ed_eval_outer_assert_pair        (SU.Nor,                    pair)
      | eval_out (Imply             pair)        = ed_eval_outer_assert_pair        (SU.Imply,                  pair)
      | eval_out (Ands              asses)       = ed_eval_outer_assert_list        (SU.Ands,                   asses)
      | eval_out (Ors               asses)       = ed_eval_outer_assert_list        (SU.Ors,                    asses)
      | eval_out (Is_Cnst           ass)         = ed_eval_outer_assert_atomic_one  (SU.Is_Cnst,                ass)
      | eval_out (Is_Free           ass)         = ed_eval_outer_assert_atomic_one  (SU.Is_Free,                ass)
      | eval_out (Is_Var            ass)         = ed_eval_outer_assert_atomic_one  (SU.Is_Var,                 ass)
      | eval_out (Is_Bound          ass)         = ed_eval_outer_assert_atomic_one  (SU.Is_Bound,               ass)
      | eval_out (Is_Lambda         ass)         = ed_eval_outer_assert_atomic_one  (SU.Is_Lambda,              ass)
      | eval_out (Is_App            ass)         = ed_eval_outer_assert_atomic_one  (SU.Is_App,                 ass)
      | eval_out (Has_Same_Prnt_As  pair)        = ed_eval_outer_assert_atomic_pair (SU.Has_Same_Prnt_As,       pair)
      | eval_out (Is_In_Trm_Prnt    pair)        = ed_eval_outer_assert_atomic_pair (SU.Is_In_Trm_Prnt,         pair)
      | eval_out (Is_Deeper_Than    pair)        = ed_eval_outer_assert_atomic_pair (SU.Is_Deeper_Than,         pair)
      | eval_out (Is_Shallower_Than pair)        = ed_eval_outer_assert_atomic_pair (SU.Is_Shallower_Than,      pair)
      | eval_out (Is_Path_Above     pair)        = ed_eval_outer_assert_atomic_pair (SU.Is_Path_Above,          pair)
      | eval_out (Is_Same_Path_As   pair)        = ed_eval_outer_assert_atomic_pair (SU.Is_Same_Path_As,        pair)
      | eval_out (Is_Nth_Child      pair)        = ed_eval_outer_assert_atomic_pair (SU.Is_Nth_Child,           pair)
      | eval_out (Is_N_Plus_One_th_Child pair)   = ed_eval_outer_assert_atomic_pair (SU.Is_N_Plus_One_th_Child, pair)
      | eval_out (Are_Same_Prints   pair)        = ed_eval_outer_assert_atomic_pair (SU.Are_Same_Prints,        pair)
      | eval_out (Unode_Has_Print   pair)        = ed_eval_outer_assert_atomic_pair (SU.Unode_Has_Print,        pair)
      | eval_out (Is_In_Subgoal          assert) = ed_eval_outer_assert_atomic_one  (SU.Is_In_Subgoal,          assert)
      | eval_out (Is_In_Chained_Fact     assert) = ed_eval_outer_assert_atomic_one  (SU.Is_In_Chained_Fact,     assert)
      | eval_out (Is_In_Nth_Subgoal      pair)   = ed_eval_outer_assert_atomic_pair (SU.Is_In_Nth_Subgoal,      pair)
      | eval_out (Is_In_Nth_Chained_Fact pair)   = ed_eval_outer_assert_atomic_pair (SU.Is_In_Nth_Chained_Fact, pair)
      | eval_out (Are_Same_Number   pair)        = ed_eval_outer_assert_atomic_pair (SU.Are_Same_Number,        pair)
      | eval_out (Is_Less_Than      pair)        = ed_eval_outer_assert_atomic_pair (SU.Is_Less_Than,           pair)
      | eval_out (Print            print)        = ed_eval_outer_param              (ED.Outer_Non_Path (SU.Print  print ))
      | eval_out (Number          number)        = ed_eval_outer_param              (ED.Outer_Non_Path (SU.Number number))
      | eval_out (Variable        string)        = ed_eval_outer (ED.Outer_Variable string)
      | eval_out (Lambdas (strings, sub_ass))    = 
(tracing "Lambdas in ed_eval in Eval_Surface";
(*TODO: FIXME: We should not call eval_out inside the sub-term.
  because we do not have an environment for the variables there yet.
  But if eval_out has In_All_Definitions, we cannot simply take it as a syntactic sugar, can't we? *)
        ed_eval_outer (ED.Outer_Lambdas (strings,       eval_out sub_ass ))
)
      | eval_out (Applies (func,    args))       = ed_eval_outer (ED.Outer_Applies (eval_out func, map eval_out args))
      | eval_out (Alls    (pairs,   sub_ass))    = (tracing "eval_out Alls in Eval_Surface";ed_eval_outer (ED.Outer_Alls    (pairs, eval_out sub_ass)))
      | eval_out (Somes   (pairs,   sub_ass))    = ed_eval_outer (ED.Outer_Somes   (pairs, eval_out sub_ass))
      | eval_out (In_All_Definitions  (target, inner_ass as Lambdas _, outer_args)) = ED.eval_outer pst induct_args (ED.Dive_In (eval_out target, eval_in thm_trm inner_ass, map eval_out outer_args)) thm_trm
      | eval_out (In_All_Definitions  _)         = error "eval_out in From_Deep_To_Surface.ML failed. The inner part of In_All_Definitions has to be a lambda abstraction."
      | eval_out (Outermost _)                   = error "eval_out in From_Deep_To_Surface.ML failed. eval_out is not defined for Outermost."
    and ed_eval_inner                    (inner_expr:ED.inner_expression)                    (in_trm:term) = ED.eval_inner pst induct_args inner_expr (in_trm:term)                                            : ED.inner_expression
    and ed_eval_inner_param              (param     :ED.inner_parameter)                     (in_trm:term) = ed_eval_inner             (ED.Inner_Literal param)                                   (in_trm:term): ED.inner_expression
    and ed_eval_inner_assert_one         (ass:SU.assert,          arg:assert)                (in_trm:term) = ed_eval_inner             (ED.Inner_Assert (ass, [eval_in in_trm arg]))              (in_trm:term): ED.inner_expression
    and ed_eval_inner_assert_atomic_one  (atom:SU.atomic_assert,  arg:assert)                (in_trm:term) = ed_eval_inner_assert_one  (SU.Atomic atom, arg)                                      (in_trm:term): ED.inner_expression
    and ed_eval_inner_assert_pair        (ass:SU.assert,         (arg1:assert, arg2:assert)) (in_trm:term) = ed_eval_inner             (ED.Inner_Assert (ass, map (eval_in in_trm) [arg1, arg2])) (in_trm:term): ED.inner_expression
    and ed_eval_inner_assert_atomic_pair (atom:SU.atomic_assert, (arg1:assert, arg2:assert)) (in_trm:term) = ed_eval_inner_assert_pair (SU.Atomic atom, (arg1, arg2))                             (in_trm:term): ED.inner_expression
    and ed_eval_inner_assert_list        (assert:SU.assert,  args: assert list)              (in_trm:term) = ed_eval_inner             (ED.Inner_Assert (assert, map (eval_in in_trm) args))      (in_trm:term): ED.inner_expression
    and eval_in (in_trm:term) True                           = ed_eval_inner_param              (ED.Inner_Non_Path (SU.Bool true ))                                  in_trm
      | eval_in (in_trm:term) False                          = ed_eval_inner_param              (ED.Inner_Non_Path (SU.Bool false))                                  in_trm
      | eval_in (in_trm:term) (Not ass)                      = ed_eval_inner_assert_one         (SU.Not, ass)                                                        in_trm
      | eval_in (in_trm:term) (And                    pair)  = ed_eval_inner_assert_pair        (SU.And,                    pair)                                    in_trm
      | eval_in (in_trm:term) (Or                     pair)  = ed_eval_inner_assert_pair        (SU.Or,                     pair)                                    in_trm
      | eval_in (in_trm:term) (Nor                    pair)  = ed_eval_inner_assert_pair        (SU.Nor,                    pair)                                    in_trm
      | eval_in (in_trm:term) (Imply                  pair)  = ed_eval_inner_assert_pair        (SU.Imply,                  pair)                                    in_trm
      | eval_in (in_trm:term) (Ands                   asses) = ed_eval_inner_assert_list        (SU.Ands,                   asses)                                   in_trm
      | eval_in (in_trm:term) (Ors                    asses) = ed_eval_inner_assert_list        (SU.Ors,                    asses)                                   in_trm
      | eval_in (in_trm:term) (Is_Cnst                ass)   = ed_eval_inner_assert_atomic_one  (SU.Is_Cnst,                ass)                                     in_trm
      | eval_in (in_trm:term) (Is_Free                ass)   = ed_eval_inner_assert_atomic_one  (SU.Is_Free,                ass)                                     in_trm
      | eval_in (in_trm:term) (Is_Var                 ass)   = ed_eval_inner_assert_atomic_one  (SU.Is_Var,                 ass)                                     in_trm
      | eval_in (in_trm:term) (Is_Bound               ass)   = ed_eval_inner_assert_atomic_one  (SU.Is_Bound,               ass)                                     in_trm
      | eval_in (in_trm:term) (Is_Lambda              ass)   = ed_eval_inner_assert_atomic_one  (SU.Is_Lambda,              ass)                                     in_trm
      | eval_in (in_trm:term) (Is_App                 ass)   = ed_eval_inner_assert_atomic_one  (SU.Is_App,                 ass)                                     in_trm
      | eval_in (in_trm:term) (Has_Same_Prnt_As       pair)  = ed_eval_inner_assert_atomic_pair (SU.Has_Same_Prnt_As,       pair)                                    in_trm
      | eval_in (in_trm:term) (Is_In_Trm_Prnt         pair)  = ed_eval_inner_assert_atomic_pair (SU.Is_In_Trm_Prnt,         pair)                                    in_trm
      | eval_in (in_trm:term) (Is_Deeper_Than         pair)  = ed_eval_inner_assert_atomic_pair (SU.Is_Deeper_Than,         pair)                                    in_trm
      | eval_in (in_trm:term) (Is_Shallower_Than      pair)  = ed_eval_inner_assert_atomic_pair (SU.Is_Shallower_Than,      pair)                                    in_trm
      | eval_in (in_trm:term) (Is_Path_Above          pair)  = ed_eval_inner_assert_atomic_pair (SU.Is_Path_Above,          pair)                                    in_trm
      | eval_in (in_trm:term) (Is_Same_Path_As        pair)  = ed_eval_inner_assert_atomic_pair (SU.Is_Same_Path_As,        pair)                                    in_trm
      | eval_in (in_trm:term) (Is_Nth_Child           pair)  = ed_eval_inner_assert_atomic_pair (SU.Is_Nth_Child,           pair)                                    in_trm
      | eval_in (in_trm:term) (Is_N_Plus_One_th_Child pair)  = ed_eval_inner_assert_atomic_pair (SU.Is_N_Plus_One_th_Child, pair)                                    in_trm
      | eval_in (in_trm:term) (Are_Same_Prints        pair)  = ed_eval_inner_assert_atomic_pair (SU.Are_Same_Prints,        pair)                                    in_trm
      | eval_in (in_trm:term) (Unode_Has_Print        pair)  = ed_eval_inner_assert_atomic_pair (SU.Unode_Has_Print,        pair)                                    in_trm
      | eval_in (in_trm:term) (Is_In_Subgoal          ass)   = ed_eval_inner_assert_atomic_one  (SU.Is_In_Subgoal,          ass)                                     in_trm
      | eval_in (in_trm:term) (Is_In_Chained_Fact     ass)   = ed_eval_inner_assert_atomic_one  (SU.Is_In_Chained_Fact,     ass)                                     in_trm
      | eval_in (in_trm:term) (Is_In_Nth_Subgoal      pair)  = ed_eval_inner_assert_atomic_pair (SU.Is_In_Nth_Subgoal,      pair)                                    in_trm
      | eval_in (in_trm:term) (Is_In_Nth_Chained_Fact pair)  = ed_eval_inner_assert_atomic_pair (SU.Is_In_Nth_Chained_Fact, pair)                                    in_trm
      | eval_in (in_trm:term) (Are_Same_Number   pair)       = ed_eval_inner_assert_atomic_pair (SU.Are_Same_Number,        pair)                                    in_trm
      | eval_in (in_trm:term) (Is_Less_Than      pair)       = ed_eval_inner_assert_atomic_pair (SU.Is_Less_Than,           pair)                                    in_trm
      | eval_in (in_trm:term) (Print            print)       = ed_eval_inner_param              (ED.Inner_Non_Path (SU.Print  print ))                               in_trm
      | eval_in (in_trm:term) (Number          number)       = ed_eval_inner_param              (ED.Inner_Non_Path (SU.Number number))                               in_trm
      | eval_in (in_trm:term) (Variable        string)       = ed_eval_inner                    (ED.Inner_Variable  string)                                          in_trm
      | eval_in (in_trm:term) (Lambdas (strings, sub_ass))   = ed_eval_inner                    (ED.Inner_Lambdas  (strings, eval_in in_trm sub_ass ))               in_trm
(*TODO: FIXME: We should not call eval_in inside the sub-term of the lambda abstraction
               because we do not have an environment for the variables there yet.*)
      | eval_in (in_trm:term) (Applies (func,    args))      = ed_eval_inner                    (ED.Inner_Applies  (eval_in in_trm func, map (eval_in in_trm) args)) in_trm
      | eval_in (in_trm:term) (Alls    (pairs,   sub_ass))   = ed_eval_inner                    (ED.Inner_Alls     (pairs, eval_in in_trm sub_ass))                  in_trm
      | eval_in (in_trm:term) (Somes   (pairs,   sub_ass))   = ed_eval_inner                    (ED.Inner_Somes    (pairs, eval_in in_trm sub_ass))                  in_trm
      | eval_in (in_trm:term) (In_All_Definitions  (target, inner_ass as Lambdas _, outer_args)) =
        ED.eval_inner pst induct_args (ED.Dive_Deeper (eval_in in_trm target, eval_in in_trm inner_ass, map (eval_in in_trm) outer_args)) in_trm
        (*TODO: Double-check if I can really use this term.*)
      | eval_in (_:term) (In_All_Definitions  _) = error "eval_in in From_Deep_To_Surface.ML failed. The inner part of In_All_Definitions has to be a lambda abstraction."
      | eval_in (_:term) (Outermost _)           = error "eval_in in From_Deep_To_Surface.ML failed. eval_in is not defined for Outermost."
  in
      eval_enter assert |> come_back_expression
  end

end;