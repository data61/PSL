(*  Title:      PSL/SeLFiE/src/From_Quantifier_To_Deep.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

functor from_Quantifier_to_Deep
 (structure Eval_Quantifier:EVAL_QUANTIFIER
  and       Quantifier_Domain:QUANTIFIER_DOMAIN
  sharing type Eval_Quantifier.parameter = Quantifier_Domain.parameter): EVAL_DEEP =
struct

structure EQ  = Eval_Quantifier;
structure QD  = Quantifier_Domain;

type parameter = EQ.parameter;

type parameter_assert = EQ.parameter_assert;

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Eval_Parameter of parameter_assert;

fun convert_assert Not   = EQ.Not
  | convert_assert And   = EQ.And
  | convert_assert Or    = EQ.Or
  | convert_assert Nor   = EQ.Nor
  | convert_assert Imply = EQ.Imply
  | convert_assert Ands  = EQ.Ands
  | convert_assert Ors   = EQ.Ors
  | convert_assert (Eval_Parameter assert) = EQ.Eval_Parameter assert;

type qtyp      = QD.qtyp;

val convert_qtyp = undefined;(*TODO*)

datatype expr =
  Variable              of string
| Lambda                of string * expr
| Apply                 of expr   * expr
| Literal               of parameter
| Assert                of assert * expr list
| All                   of string * qtyp * expr
| Some                  of string * qtyp * expr
| In_All_Definition_Of  of string * expr
| In_Some_Definition_Of of string * expr;

type path_to_node_table   = QD.path_to_node_table;
type print_to_paths_table = QD.print_to_paths_table;

fun convert_result (EQ.Literal ee_bool) = Literal ee_bool
  | convert_result  _ = error "eval in Eval_Quantifier_Struct failed. Evaluation is not complete.";

(*TODO: should I use Eval_Parameter instead of Eval_Expression?
Probably, it does not matter much. Both of them are too concrete (w/wo full-nodes).
The good news is that the return type of eval in Quantifier can be Connective.bool rather than Expression*)
fun eval(trm:term) (pst:Proof.state) expr =
  let
    (*TODO: get terms for definitions!*)
    fun get_terms (_:string) = [(*TODO*)]: terms;
    fun eval' (Variable vname)              = EQ.eval trm pst (EQ.Variable vname)
      | eval' (Lambda (vname, subexpr))     = EQ.eval trm pst (EQ.Lambda (vname, eval' subexpr))
      | eval' (Apply   pair           )     = EQ.eval trm pst (EQ.Apply (apply2 eval' pair))
      | eval' (Literal ps             )     = EQ.eval trm pst (EQ.Literal ps)
      | eval' (Assert (assrt, ps))          = EQ.eval trm pst (EQ.Assert (convert_assert assrt, map eval' ps))
      | eval' (All  (vname, qtyp, subexpr)) = EQ.eval trm pst (EQ.All  (vname, convert_qtyp qtyp, eval' subexpr))
      | eval' (Some (vname, qtyp, subexpr)) = EQ.eval trm pst (EQ.Some (vname, convert_qtyp qtyp, eval' subexpr))
      | eval' (In_All_Definition_Of (vname, subexpr)) =
        let
          (*TODO: This inner call of eval should be
           * - eval in Eval_Inner            if this functor is creating Eval_Outer.
           * - just a recursive call of eval if this functor is creating Eval_Inner.*)
          val subexprs = map (fn term => eval term pst subexpr) (get_terms vname): expr list;
        in
          eval' (Assert (Ands, subexprs))
        end
      | eval' (In_Some_Definition_Of (vname, subexpr)) =
        let
          (*TODO: This inner call of eval should be
           * - eval in Eval_Inner            if this functor is creating Eval_Outer.
           * - just a recursive call of eval if this functor is creating Eval_Inner.*)
          val subexprs = map (fn term => eval term pst subexpr) (get_terms vname): expr list;
        in
          eval' (Assert (Ors, subexprs))
        end;

    val ev_result  = eval' expr              : EQ.expr;
    val result     = convert_result ev_result: expr;
  in
    result
  end;

end;