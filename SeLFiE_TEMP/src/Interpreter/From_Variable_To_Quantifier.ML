(*  Title:      PSL/SeLFiE/src/From_Variable_To_Quantifier.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
functor from_Variable_to_Quantifier
 (structure Eval_Variable:EVAL_VARIABLE
  and       Quantifier_Domain:QUANTIFIER_DOMAIN
  sharing type Eval_Variable.parameter = Quantifier_Domain.parameter): EVAL_QUANTIFIER =
struct

structure EV  = Eval_Variable;
structure QD  = Quantifier_Domain;

type parameter = EV.parameter;

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

fun convert_parameter_assert Is_Cnst          = EV.Is_Cnst
  | convert_parameter_assert Is_Free          = EV.Is_Free
  | convert_parameter_assert Is_Var           = EV.Is_Var
  | convert_parameter_assert Is_Bound         = EV.Is_Bound
  | convert_parameter_assert Is_Lambda        = EV.Is_Lambda
  | convert_parameter_assert Is_App           = EV.Is_App
  | convert_parameter_assert Has_Same_Prnt_As = EV.Has_Same_Prnt_As
  | convert_parameter_assert Is_In_Trm_Prnt   = EV.Is_In_Trm_Prnt
  | convert_parameter_assert Is_Deeper_Than   = EV.Is_Deeper_Than
  | convert_parameter_assert Is_Shallower_Than= EV.Is_Shallower_Than
  | convert_parameter_assert Is_Path_Above    = EV.Is_Path_Above
  | convert_parameter_assert Is_Same_Path_As  = EV.Is_Same_Path_As
  | convert_parameter_assert Are_Same_Prints  = EV.Are_Same_Prints
  | convert_parameter_assert Is_Printed_As    = EV.Is_Printed_As
  | convert_parameter_assert Unode_Has_Print  = EV.Unode_Has_Print
  | convert_parameter_assert Are_Same_Number  = EV.Are_Same_Number
  | convert_parameter_assert Is_Less_Than     = EV.Is_Less_Than
  | convert_parameter_assert Is_Int           = EV.Is_Int;

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

fun convert_assert Not   = EV.Not
  | convert_assert And   = EV.And
  | convert_assert Or    = EV.Or
  | convert_assert Nor   = EV.Nor
  | convert_assert Imply = EV.Imply
  | convert_assert Ands  = EV.Ands
  | convert_assert Ors   = EV.Ors
  | convert_assert (Atomic assert) = EV.Atomic (convert_parameter_assert assert);

type qtyp = QD.qtyp;

datatype expr =
  Variable of string
| Lambda   of string * expr
| Apply    of expr   * expr
| Literal  of parameter
| Assert   of assert * expr list
| All      of string * qtyp * expr
| Some     of string * qtyp * expr;

type path_to_node_table   = QD.path_to_node_table;
type print_to_paths_table = QD.print_to_paths_table;

fun convert_result (EV.Literal ee_bool) = Literal ee_bool
  | convert_result  _ = error "eval in Eval_Quantifier_Struct failed. Evaluation is not complete.";

(*TODO: should I use Atomic instead of Eval_Expression?
Probably, it does not matter much. Both of them are too concrete (w/wo full-nodes).
The good news is that the return type of eval in Quantifier can be Connective.bool rather than Expression*)
fun eval(trm:term) (pst:Proof.state) expr =
  let
    fun vname_n_subexpr_n_qtyp_to_apps (vname:string) (subexpr:expr) (qtyp:qtyp) =
      let
        val params = QD.qtyp_to_qdomain qtyp: QD.parameter list;
        val apps = map (fn param => Apply (Lambda (vname, subexpr), Literal param)) params: expr list;
      in
        Assert (Ands, apps): expr
      end;
    fun eval' (Variable vname)              = EV.eval trm pst (EV.Variable vname)
      | eval' (Lambda (vname, subexpr))     = EV.eval trm pst (EV.Lambda (vname, eval' subexpr))
      | eval' (Apply   pair           )     = EV.eval trm pst (EV.Apply (apply2 eval' pair))
      | eval' (Literal ps             )     = EV.eval trm pst (EV.Literal ps)
      | eval' (Assert (assrt, ps))          = EV.eval trm pst (EV.Assert (convert_assert assrt, map eval' ps))
      | eval' (All  (vname, qtyp, subexpr)) = eval' (vname_n_subexpr_n_qtyp_to_apps vname subexpr qtyp)
      | eval' (Some (vname, qtyp, subexpr)) = eval' (Assert (Not, [All (vname, qtyp, Assert (Not, [subexpr]))]))
    val ev_result  = eval' expr              : EV.expr;
    val result     = convert_result ev_result: expr;
  in
    result
  end;

end;