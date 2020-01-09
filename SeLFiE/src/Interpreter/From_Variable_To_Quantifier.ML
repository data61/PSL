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

type path    = EV.path;
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

fun here_to_there (Bool b)    = EV.Bool b
  | here_to_there (Path p)    = EV.Path p
  | here_to_there (Print p)   = EV.Print p
  | here_to_there (String s)  = EV.String s
  | here_to_there (Number n)  = EV.Number n
  | here_to_there (Int i)     = EV.Int i
  | here_to_there (Command i) = EV.Command i;

fun there_to_here (EV.Bool b)    = Bool b
  | there_to_here (EV.Path p)    = Path p
  | there_to_here (EV.Print p)   = Print p
  | there_to_here (EV.String s)  = String s
  | there_to_here (EV.Number n)  = Number n
  | there_to_here (EV.Int i)     = Int i
  | there_to_here (EV.Command i) = Command i;

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

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

fun qtyp_go_away QFull_Path = QD.QFull_Path
  | qtyp_go_away QPrint     = QD.QPrint
  | qtyp_go_away QInd       = QD.QInd
  | qtyp_go_away QArb       = QD.QArb
  | qtyp_go_away QRule      = QD.QRule
  | qtyp_go_away QNumber    = QD.QNumber

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

fun convert_result (EV.Literal ee_bool) = Literal (there_to_here ee_bool)
  | convert_result  _ = error "eval in Eval_Quantifier_Struct failed. Evaluation is not complete.";

fun eval(trm:term) (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) expr =
  let
    fun vname_n_subexpr_n_qtyp_to_apps (vname:string) (subexpr:expr) (qtyp:qtyp) (ands_or_ors:assert) =
      let
        val params = QD.qtyp_to_qdomain (qtyp_go_away qtyp) pst trm induct_args: QD.parameter list;
        val apps = map (fn param => Apply (Lambda (vname, subexpr), Literal (there_to_here param))) params: expr list;
      in
        Assert (ands_or_ors, apps): expr
      end;
    fun eval' (Variable vname)              = EV.eval trm pst (EV.Variable vname)
      | eval' (Lambda (vname, subexpr))     = EV.eval trm pst (EV.Lambda (vname, eval' subexpr))
      | eval' (Apply   pair           )     = EV.eval trm pst (EV.Apply (apply2 eval' pair))
      | eval' (Literal ps             )     = EV.eval trm pst (EV.Literal (here_to_there ps))
      | eval' (Assert (assrt, ps))          = EV.eval trm pst (EV.Assert (convert_assert assrt, map eval' ps))
      | eval' (All  (vname, qtyp, subexpr)) = eval' (vname_n_subexpr_n_qtyp_to_apps vname subexpr qtyp Ands)
      (*Note that we cannot treat Some as a syntax sugar for All because Not has to take Literals due to the restriction imposed in From_Parameter_To_Parameter_With_Bool.ML.*)
      | eval' (Some (vname, qtyp, subexpr)) = eval' (vname_n_subexpr_n_qtyp_to_apps vname subexpr qtyp Ors)
    val ev_result  = eval' expr              : EV.expr;
    val result     = convert_result ev_result: expr;
  in
    result
  end;

end;