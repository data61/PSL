(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Deep.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** EVAL_DEEP ***)
signature EVAL_DEEP =
sig

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

type outer_assert = Eval_Outer_Multi_Arity.parameter_assert;
type inner_assert = Eval_Inner_Multi_Arity.parameter_assert;

(*The triples are:
 - the literal for which we dive in,
 - the expression we use at the inner level,
 - arguments sent from the outer level to the inner level.*)
datatype expr       = Outer of Eval_Outer_Multi_Arity.expr | Dive_In     of (Eval_Outer_Multi_Arity.expr * inner_expr * (Eval_Outer_Multi_Arity.expr list))
     and inner_expr = Inner of Eval_Inner_Multi_Arity.expr | Dive_Deeper of (Eval_Inner_Multi_Arity.expr * inner_expr * (Eval_Inner_Multi_Arity.expr list));

val eval: Proof.state -> expr -> term -> Eval_Inner_Multi_Arity.expr;

end;

(*** Eval_Deep ***)
structure Eval_Deep: EVAL_DEEP =
struct

structure EOMA = Eval_Outer_Multi_Arity;
structure EIMA = Eval_Inner_Multi_Arity;

type outer_assert = EOMA.parameter_assert;
type inner_assert = EIMA.parameter_assert;

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

(*The triples are:
 - the literal for which we dive in,
 - the expression we use at the inner level,
 - arguments sent from the outer level to the inner level.*)
datatype expr       = Outer of EOMA.expr | Dive_In     of (EOMA.expr * inner_expr * (EOMA.expr list))
     and inner_expr = Inner of EIMA.expr | Dive_Deeper of (EIMA.expr * inner_expr * (EIMA.expr list));

fun convert' (Eval_Outer_Parameter_With_Bool.Bool   true ) = Eval_Inner_Parameter_With_Bool.Bool   true
  | convert' (Eval_Outer_Parameter_With_Bool.Bool   false) = Eval_Inner_Parameter_With_Bool.Bool   false
  | convert' (Eval_Outer_Parameter_With_Bool.Print  print) = Eval_Inner_Parameter_With_Bool.Print  print
  | convert' (Eval_Outer_Parameter_With_Bool.Number numb ) = Eval_Inner_Parameter_With_Bool.Number numb
  | convert' (Eval_Outer_Parameter_With_Bool.Int    int  ) = Eval_Inner_Parameter_With_Bool.Int    int
  | convert'  _                                            = error "convert failed!"

fun convert (EOMA.Literal l) = EIMA.Literal (convert' l)
  | convert  _ = error "convert to produce Eval_Deep failed!"

fun outer_expr_to_trms (_:Proof.state) (_: EOMA.expr) = [](*TPDP*);
fun inner_expr_to_trms (_:Proof.state) (_: EIMA.expr) = [](*TPDP*);
fun convert_outer_args _ = []:EIMA.expr list; (*TODO*)
fun convert_inner_args _ = []:EIMA.expr list; (*TODO*)

fun eval (pst:Proof.state) (expr:expr) (trm:term) =
  let
    fun eval_outer (Outer outer_eq_expr) (trm:term)        = EOMA.eval trm pst outer_eq_expr |> convert
      | eval_outer (Dive_In     (const, expr, literals)) _ = eval_in_all_def pst expr (convert_outer_args literals) (outer_expr_to_trms pst const):EIMA.expr
    and eval_inner (Inner inner_expr) (trm:term)           = EIMA.eval trm pst inner_expr: EIMA.expr
      | eval_inner (Dive_Deeper (const, expr, literals)) _ = eval_in_all_def pst expr (convert_inner_args literals) (inner_expr_to_trms pst const):EIMA.expr
    and eval_in_all_def (pst:Proof.state) (Inner lambda:inner_expr) (args:EIMA.expr list) (simp_rules:terms) =
        let
          val inner_expr = Inner (EIMA.Applies (lambda, args))                         : inner_expr;
          val subexprs   = map (eval_inner inner_expr) simp_rules                      : EIMA.expr list;
          val result     = EIMA.eval Term.dummy pst (EIMA.Assert (EIMA.Ands, subexprs)): EIMA.expr;
        in
          result: EIMA.expr
        end
      | eval_in_all_def _ (Dive_Deeper _:inner_expr) _ _ = error "Diving two levels in a row is not supported.";
  in
    eval_outer expr trm
  end;

end;