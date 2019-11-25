(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Deep.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** EVAL_DEEP ***)
signature EVAL_DEEP =
sig

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

datatype expr       = Outer of Eval_Outer_Quantifier.expr | Dive_In     of inner_expr
     and inner_expr = Inner of Eval_Inner_Quantifier.expr | Dive_Deeper of inner_expr;

val eval: Proof.state -> expr -> term -> Eval_Inner_Quantifier.expr;

end;

(*** Eval_Deep ***)
structure Eval_Deep: EVAL_DEEP =
struct

structure EOQ = Eval_Outer_Quantifier;
structure EIQ = Eval_Inner_Quantifier;

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

datatype expr       = Outer of EOQ.expr | Dive_In     of inner_expr
     and inner_expr = Inner of EIQ.expr | Dive_Deeper of inner_expr;

fun convert' (Eval_Outer_Parameter_With_Bool.Bool   true ) = Eval_Inner_Parameter_With_Bool.Bool   true
  | convert' (Eval_Outer_Parameter_With_Bool.Bool   false) = Eval_Inner_Parameter_With_Bool.Bool   false
  | convert' (Eval_Outer_Parameter_With_Bool.Print  print) = Eval_Inner_Parameter_With_Bool.Print  print
  | convert' (Eval_Outer_Parameter_With_Bool.Number numb ) = Eval_Inner_Parameter_With_Bool.Number numb
  | convert' (Eval_Outer_Parameter_With_Bool.Int    int  ) = Eval_Inner_Parameter_With_Bool.Int    int
  | convert'  _                                            = error "convert failed!"

fun convert (EOQ.Literal l) = EIQ.Literal (convert' l)
  | convert  _ = error "convert to produce Eval_Deep failed!"

fun eval (pst:Proof.state) (expr:expr) (trm:term) =
  let
    fun eval_outer (Outer       outer_eq_expr ) (trm:term) = EOQ.eval trm pst outer_eq_expr |> convert
      | eval_outer (Dive_In     inner_expr    ) (trm:term) = eval_in_all_def pst inner_expr trm
    and eval_inner (Inner       inner_expr    ) (trm:term) = EIQ.eval trm pst inner_expr
      | eval_inner (Dive_Deeper inner_expr    ) (trm:term) = eval_in_all_def pst inner_expr trm
    and eval_in_all_def (pst:Proof.state) (inner_expr:inner_expr) (trm:term) =
      let
        val simp_rules = [trm(*TODO*)]: terms;
        val subexprs   = map (eval_inner inner_expr) simp_rules: EIQ.expr list;
        val result     = EIQ.eval Term.dummy pst (EIQ.Assert (EIQ.Ands, subexprs)): EIQ.expr
      in
        result: EIQ.expr
      end;
  in
    eval_outer expr trm
  end;

end;