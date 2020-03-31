(*  Title:      PSL/SeLFiE/src/From_Bound_To_Quantifier.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
functor from_Bound_to_Quantifier
 (structure Eval_Bound:EVAL_BOUND
  and       Quantifier_Domain:QUANTIFIER_DOMAIN
  sharing type Eval_Bound.parameter = Quantifier_Domain.parameter): EVAL_QUANTIFIER =
struct

structure EB  = Eval_Bound;
structure QD  = Quantifier_Domain;
structure SU  = SeLFiE_Util;

type path    = EB.path;
type command = Pattern.command;

datatype parameter = Path of path | Non_Path of SeLFiE_Util.non_path_parameter;

fun here_to_there (Path     p ) = EB.Path p
  | here_to_there (Non_Path np) = EB.Non_Path np;

fun param_to_quantifier (EB.Path     p ) = Path p
  | param_to_quantifier (EB.Non_Path np) = Non_Path np;

datatype expr =
  Bound   of int
| Lambda  of expr
| Apply   of expr   * expr
| Literal of parameter
| Assert  of SeLFiE_Util.assert * expr list
| All     of SeLFiE_Util.qtyp * expr
| Some    of SeLFiE_Util.qtyp * expr;

type path_to_node_table   = QD.path_to_node_table;
type print_to_paths_table = QD.print_to_paths_table;

fun print_expr (Bound i) = "EQ.Bound " ^ Int.toString i ^ " "
  | print_expr (Lambda expr) = "EQ.Lambda ( " ^ print_expr expr ^ " )"
  | print_expr (Apply (exp1, exp2)) = "EQ.Apply " ^ print_expr exp1 ^ " " ^ print_expr exp2 ^ " )"
  | print_expr (Literal _) = "EQ.Literal "
  | print_expr (Assert (_, expres)) = "EQ.Assert " ^ (fold (curry (op ^)) (map print_expr expres) "")
  | print_expr (All _) = "EQ.All "
  | print_expr (Some _) = "EQ.Some "

fun print_expr_eb (EB.Bound i) = "Bound " ^ Int.toString i ^ " "
  | print_expr_eb (EB.Lambda expr) = "Lambda ( " ^ print_expr_eb expr ^ " )"
  | print_expr_eb (EB.Apply (exp1, exp2)) = "EQ.Apply " ^ print_expr_eb exp1 ^ " " ^ print_expr_eb exp2 ^ " )"
  | print_expr_eb (EB.Literal p) = "Literal " ^ (case p of
       EB.Path _ => "path"
     | EB.Non_Path non_path  => case non_path of
         SU.Bool b => if b then "True" else "False"
       | SU.Print   p => "print "
       | SU.Number  n => "number "
       | SU.Command c => "command ")
  | print_expr_eb (EB.Assert (_, expres)) = "Assert " ^ (fold (curry (op ^)) (map print_expr_eb expres) "")

fun convert_result (EB.Literal ee_bool) = Literal (param_to_quantifier ee_bool)
  | convert_result (EB.Bound   i      ) = Bound i
  | convert_result (EB.Lambda  expr   ) = Lambda (convert_result expr)
  | convert_result  eb_expr = (case eb_expr of 
      EB.Bound   i   => Bound i
    | EB.Literal lit => Literal (param_to_quantifier lit)
    | eb_expr2 =>
   (tracing ("Is about to fail at convert_result in From_Bound_To_Quantifier.ML with "  ^ print_expr_eb eb_expr2);
    error "eval in From_Bound_To_Quantifier failed. Evaluation is not complete."));

fun eval (trm:term) (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) expr =
  let
    fun subexpr_n_qtyp_to_apps (subexpr:expr) (qtyp:SU.qtyp) (ands_or_ors:SU.assert) =
      let
        val params = QD.qtyp_to_qdomain qtyp pst trm induct_args: QD.parameter list;
        val apps = map (fn param => Apply (Lambda (subexpr), Literal (param_to_quantifier param))) params: expr list;
      in
        Assert (ands_or_ors, apps): expr
      end;
    fun quantifier_to_bound (Bound   i              ) = EB.Bound i
      | quantifier_to_bound (Lambda  subexpr        ) = EB.Lambda (quantifier_to_bound subexpr)
      | quantifier_to_bound (Apply   pair           ) = EB.Apply   (apply2 quantifier_to_bound pair)
      | quantifier_to_bound (Literal ps             ) = EB.Literal (here_to_there ps)
      | quantifier_to_bound (Assert (assrt, ps     )) = EB.Assert  (assrt, map quantifier_to_bound ps)
      | quantifier_to_bound (All    (qtyp,  subexpr)) = quantifier_to_bound (subexpr_n_qtyp_to_apps subexpr qtyp SU.Ands)
      | quantifier_to_bound (Some   (qtyp,  subexpr)) = quantifier_to_bound (subexpr_n_qtyp_to_apps subexpr qtyp SU.Ors)

val _ = tracing ("Print expr of Quantifier"; print_expr expr);
val _ = tracing ("Print expr of Bound in Q"; print_expr_eb (quantifier_to_bound expr));

    val eb_result  = EB.eval trm pst induct_args (quantifier_to_bound expr): EB.expr;
    val result     = convert_result eb_result: expr;
  in
    result
  end;

end;