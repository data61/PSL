(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Quantifier.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** EVAL_QUANTIFIER ***)
signature EVAL_QUANTIFIER =
sig

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Literal    of Eval_Parameter.literal
| Assert     of SeLFiE_Util.assert * expr list
| Dive_In    of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| Deep_Dive  of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| All        of SeLFiE_Util.qtyp * expr
| Some       of SeLFiE_Util.qtyp * expr;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;

(*** Eval_Quantifier ***)
structure Eval_Quantifier: EVAL_QUANTIFIER =
struct

structure EB  = Eval_Deep_Bound;
structure QD  = Quantifier_Domain;
structure SU  = SeLFiE_Util;

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Literal    of Eval_Parameter.literal
| Assert     of SeLFiE_Util.assert * expr list
| Dive_In    of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| Deep_Dive  of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| All        of SeLFiE_Util.qtyp * expr
| Some       of SeLFiE_Util.qtyp * expr;

fun print_expr (Bound i) = "EQ.Bound " ^ Int.toString i ^ " "
  | print_expr (Lambda expr) = "EQ.Lambda ( " ^ print_expr expr ^ " )"
  | print_expr (Apply (exp1, exp2)) = "EQ.Apply " ^ print_expr exp1 ^ " " ^ print_expr exp2 ^ " )"
  | print_expr (Literal _) = "EQ.Literal "
  | print_expr (Assert (_, expres)) = "EQ.Assert " ^ (fold (curry (op ^)) (map print_expr expres) "")
  | print_expr (Dive_In _) = "EX.Dive_In ..."
  | print_expr (Deep_Dive _) = "EX.Deep_Dive ..."
  | print_expr (All  _) = "EQ.All "
  | print_expr (Some _) = "EQ.Some "

fun convert_result (EB.Literal l   ) = Literal l
  | convert_result (EB.Bound   i   ) = Bound i
  | convert_result (EB.Lambda  expr) = Lambda (convert_result expr)
  | convert_result  _ = error "eval in From_Bound_To_Quantifier failed. Evaluation is not complete.";

fun eval (trm:term) (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) expr =
  let
    fun subexpr_n_qtyp_to_apps (subexpr:expr) (qtyp:SU.qtyp) (ands_or_ors:SU.assert) =
      let
        val params = QD.qtyp_to_qdomain qtyp pst trm induct_args: Eval_Parameter.literal list;
        val apps   = map (fn param => Apply (Lambda subexpr, Literal param)) params: expr list;
      in
        Assert (ands_or_ors, apps): expr
      end;
    fun quantifier_to_bound (Bound      i              )     = EB.Bound i
      | quantifier_to_bound (Lambda     subexpr        )     = EB.Lambda  (quantifier_to_bound subexpr)
      | quantifier_to_bound (Apply      pair           )     = EB.Apply   (apply2 quantifier_to_bound pair)
      | quantifier_to_bound (Literal    ps             )     = EB.Literal ps
      | quantifier_to_bound (Assert    (assrt, ps     ))     = EB.Assert  (assrt, map quantifier_to_bound ps)
      | quantifier_to_bound (Dive_In   (target, lamb, args)) = EB.Dive_In   (quantifier_to_bound target, quantifier_to_bound lamb, quantifiers_to_bounds args)
      | quantifier_to_bound (Deep_Dive (target, lamb, args)) = EB.Deep_Dive (quantifier_to_bound target, quantifier_to_bound lamb, quantifiers_to_bounds args)
      | quantifier_to_bound (All       (qtyp,  subexpr))     = quantifier_to_bound (subexpr_n_qtyp_to_apps subexpr qtyp SU.Ands)
      | quantifier_to_bound (Some      (qtyp,  subexpr))     = quantifier_to_bound (subexpr_n_qtyp_to_apps subexpr qtyp SU.Ors)
    and quantifiers_to_bounds exprs = map quantifier_to_bound exprs;

    val _ = tracing ("Print expr of Quantifier"; print_expr expr);
    val eb_result  = EB.eval trm pst induct_args (quantifier_to_bound expr): EB.expr;
    val result     = convert_result eb_result: expr;
  in
    result
  end;

end;