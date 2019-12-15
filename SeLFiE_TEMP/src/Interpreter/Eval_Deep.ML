(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Deep.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** signature EVAL_DEEP ***)
signature EVAL_DEEP =
sig

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

type outer_assert = Eval_Outer_Sugar.assert;
type inner_assert = Eval_Inner_Sugar.assert;

(*The triples are:
 - the literal for which we dive in,
 - the expression we use at the inner level,
 - arguments sent from the outer level to the inner level.*)
datatype expr       = Outer of outer_assert | Dive_In     of (outer_assert * inner_expr * (outer_assert list))
     and inner_expr = Inner of inner_assert | Dive_Deeper of (inner_assert * inner_expr * (inner_assert list));
(*
datatype expr       = Expr expr | Outer of outer_assert | Dive_In     of (outer_assert * inner_expr * (outer_assert list))
     and inner_expr = Inner of inner_assert | Dive_Deeper of (inner_assert * inner_expr * (inner_assert list));
*)
val eval: Proof.state -> expr -> term -> Eval_Inner_Sugar.assert;

end;

(*** structure Eval_Deep ***)
structure Eval_Deep: EVAL_DEEP =
struct

structure EOS = Eval_Outer_Sugar;
structure EIS = Eval_Inner_Sugar;

type outer_assert = Eval_Outer_Sugar.assert;
type inner_assert = Eval_Inner_Sugar.assert;

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

(*The triples are:
 - the literal for which we dive in,
 - the expression we use at the inner level,
 - arguments sent from the outer level to the inner level.*)
datatype expr       = Outer of outer_assert | Dive_In     of (outer_assert * inner_expr * (outer_assert list))
     and inner_expr = Inner of inner_assert | Dive_Deeper of (inner_assert * inner_expr * (inner_assert list));

fun convert  Eval_Outer_Sugar.True         = Eval_Inner_Sugar.True
  | convert  Eval_Outer_Sugar.False        = Eval_Inner_Sugar.False
  | convert (Eval_Outer_Sugar.Print print) = Eval_Inner_Sugar.Print print
  | convert (Eval_Outer_Sugar.Number numb) = Eval_Inner_Sugar.Number numb
  | convert  _                             = error "convert in Eval_Deep failed!"

fun outer_expr_to_trms (_:Proof.state) (_) = [](*TODO*);
fun inner_expr_to_trms (_:Proof.state) (_) = [](*TODO*);

fun convert_outer_args  _ = []:EIS.assert list; (*TODO*)
fun convert_inner_args  _ = []:EIS.assert list; (*TODO*)

fun eval (pst:Proof.state) (expr:expr) (trm:term) =
  let
    fun eval_outer (Outer outer_eq_expr) (trm:term)        = EOS.eval pst trm outer_eq_expr |> convert
      | eval_outer (Dive_In     (const, expr, literals)) _ = eval_in_all_def pst expr (convert_outer_args literals) (outer_expr_to_trms pst const):Eval_Inner_Sugar.assert
    and eval_inner (Inner inner_expr) (trm:term)           = EIS.eval pst trm inner_expr: EIS.assert
      | eval_inner (Dive_Deeper (const, expr, literals)) _ = eval_in_all_def pst expr (convert_inner_args literals) (inner_expr_to_trms pst const):Eval_Inner_Sugar.assert
    and eval_in_all_def (pst:Proof.state) (Inner lambda:inner_expr) (args:EIS.assert list) (simp_rules:terms) =
        let
          val inner_expr = Inner (EIS.Applies (lambda, args))         : inner_expr;
          val subexprs   = map (eval_inner inner_expr) simp_rules     : EIS.assert list;
          val result     = EIS.eval pst Term.dummy (EIS.Ands subexprs): EIS.assert;
        in
          result:Eval_Inner_Sugar.assert
        end
      | eval_in_all_def _ (Dive_Deeper _:inner_expr) _ _ = error "Diving two levels in a row is not supported.";
  in
    eval_outer expr trm
  end;

end;