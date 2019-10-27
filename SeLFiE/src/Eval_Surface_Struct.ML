(*  Title:      PSL/SeLFiE/src/Eval_Surface_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Surface:EVAL_SURFACE =
struct

type print     = LiFtEr_Util.print;
type name      = string;


structure EC   = Eval_Connective;
structure EP   = Eval_Parameters;
structure EE   = Eval_Expression;
structure EQC  = Eval_Quantifier_Core;
structure EM   = Eval_Modifier;
structure FPTF = Full_Path_To_Fpunode;
structure PTFP = Print_To_Full_Paths;

type qtyp = EQC.qtyp;

datatype assert =
(*Eval_Connective*)
  True
| False
| Not                    of assert
| And                    of assert * assert
| Or                     of assert * assert
| Nor                    of assert * assert
| Imply                  of assert * assert
| Ands                   of assert list
| Ors                    of assert list
(*Eval_Node_Core*)
| Is_Cnst                of name
| Is_Free                of name
| Is_Var                 of name
| Is_Bound               of name
| Is_Lambda              of name
| Is_App                 of name
(*Eval_Node_Sugar*)
| Is_Atom                of name
| Is_Compund             of name
(*Eval_Unode_Core*)
| Has_Same_Prnt_As       of name * name
| Is_In_Trm_Prnt         of name * name
| Is_Deeper_Than         of name * name
| Is_Shallower_Than      of name * name
| Is_Path_Above          of name * name
| Is_Same_Path_As        of name * name
(*Eval_Unode_Sugar*)
| Is_As_Deep_As          of name * name
| Is_Path_Below          of name * name
(*Eval_Fpunode_Core*)
| Is_In_Same_Location_As of name * name
| Is_In_Chained          of name
| Is_In_Fst_Subg         of name
(*Eval_Fpunode_Sugar*)
| Is_Above               of name * name
| Is_Below               of name * name
| Is_Same_Occ_As         of name * name
(*Eval_Print_Core*)
| Are_Same_Prints        of name * name
| Is_Printed_As          of name * string
(*Eval_Print_Sugar*)
| Are_Different_Prints   of name * name
| Fpnode_Has_Print       of name * name
(*Eval_Number*)
| Are_Same_Number        of name  * name
| Is_Less_Than           of name  * name
| Is_Int                 of name  * int
(*Other*)
| Is_Nth_Arg_Of          of name * name * name
(*Quantifier*)
| All                    of name * qtyp * assert
| Some                   of name * qtyp * assert
(*Modifier*)
| Is_Rule_Of             of name * name
(*Semantic*)
| Is_Defined_With        of name   * Pattern.command
| Holds_In_Any_Clause_Of of assert * name
| Holds_In_One_Clause_Of of assert * name;

val name_dup_check = undefined: assert -> bool;

val type_check = undefined: assert -> bool;

val pair_to_list = Utils.pair_to_list;

fun surf_pair_to_mod_list pair = map surf_to_mod (pair_to_list pair)
and surf_list_to_mod_list list = map surf_to_mod  list
and name_pair_to_var_list pair = map EQC.Var     (pair_to_list pair)
and 
(*Eval_Connective*)
  surf_to_mod True         = EQC.Literal (EE.Bool true)
| surf_to_mod False        = EQC.Literal (EE.Bool false)
| surf_to_mod (Not   ass)  = EQC.Assert (EE.Not,  [surf_to_mod ass] )
| surf_to_mod (And   pair) = EQC.Assert (EE.And,   surf_pair_to_mod_list pair)
| surf_to_mod (Or    pair) = EQC.Assert (EE.Or,    surf_pair_to_mod_list pair)
| surf_to_mod (Nor   pair) = EQC.Assert (EE.Nor,   surf_pair_to_mod_list pair)
| surf_to_mod (Imply pair) = EQC.Assert (EE.Imply, surf_pair_to_mod_list pair)
| surf_to_mod (Ands  list) = EQC.Assert (EE.Ands,  surf_list_to_mod_list list)
| surf_to_mod (Ors   list) = EQC.Assert (EE.Ors,   surf_list_to_mod_list list)
(*Eval_Node_Core*)
| surf_to_mod (Is_Cnst   name) = EQC.Assert (EE.Is_Cnst,   [EQC.Var name])
| surf_to_mod (Is_Free   name) = EQC.Assert (EE.Is_Free,   [EQC.Var name])
| surf_to_mod (Is_Var    name) = EQC.Assert (EE.Is_Var,    [EQC.Var name])
| surf_to_mod (Is_Bound  name) = EQC.Assert (EE.Is_Bound,  [EQC.Var name])
| surf_to_mod (Is_Lambda name) = EQC.Assert (EE.Is_Lambda, [EQC.Var name])
| surf_to_mod (Is_App    name) = EQC.Assert (EE.Is_App,    [EQC.Var name])
(*Eval_Node_Sugar*)
| surf_to_mod (Is_Atom    name) = EQC.Assert (EE.Is_Atom,    [EQC.Var name])
| surf_to_mod (Is_Compund name) = EQC.Assert (EE.Is_Compund, [EQC.Var name])
(*Eval_Unode_Core*)
| surf_to_mod (Has_Same_Prnt_As  pair) = EQC.Assert (EE.Has_Same_Prnt_As,  name_pair_to_var_list pair)
| surf_to_mod (Is_In_Trm_Prnt    pair) = EQC.Assert (EE.Is_In_Trm_Prnt,    name_pair_to_var_list pair)
| surf_to_mod (Is_Deeper_Than    pair) = EQC.Assert (EE.Is_Deeper_Than,    name_pair_to_var_list pair)
| surf_to_mod (Is_Shallower_Than pair) = EQC.Assert (EE.Is_Shallower_Than, name_pair_to_var_list pair)
| surf_to_mod (Is_Path_Above     pair) = EQC.Assert (EE.Is_Path_Above,     name_pair_to_var_list pair)
| surf_to_mod (Is_Same_Path_As   pair) = EQC.Assert (EE.Is_Same_Path_As,   name_pair_to_var_list pair)
(*Eval_Unode_Sugar*)
| surf_to_mod (Is_As_Deep_As     pair) = EQC.Assert (EE.Is_As_Deep_As,     name_pair_to_var_list pair)
| surf_to_mod (Is_Path_Below     pair) = EQC.Assert (EE.Is_Path_Below,     name_pair_to_var_list pair)
(*Eval_Fpunode_Core*)
| surf_to_mod (Is_In_Same_Location_As pair) = EQC.Assert (EE.Is_In_Same_Location_As, name_pair_to_var_list pair)
| surf_to_mod (Is_In_Chained          name) = EQC.Assert (EE.Is_In_Chained,          [EQC.Var name])
| surf_to_mod (Is_In_Fst_Subg         name) = EQC.Assert (EE.Is_In_Fst_Subg,         [EQC.Var name])
(*Eval_Fpunode_Sugar*)
| surf_to_mod (Is_Above       pair) = EQC.Assert (EE.Is_Above,       name_pair_to_var_list pair)
| surf_to_mod (Is_Below       pair) = EQC.Assert (EE.Is_Below,       name_pair_to_var_list pair)
| surf_to_mod (Is_Same_Occ_As pair) = EQC.Assert (EE.Is_Same_Occ_As, name_pair_to_var_list pair)
(*Eval_Print_Core*)
| surf_to_mod (Are_Same_Prints  pair         ) = EQC.Assert (EE.Are_Same_Prints, name_pair_to_var_list pair)
| surf_to_mod (Is_Printed_As   (name, string)) = EQC.Assert (EE.Is_Printed_As,   [EQC.Var name, EQC.Literal (EE.String string)])
(*Eval_Print_Sugar*)
| surf_to_mod (Are_Different_Prints pair) = EQC.Assert (EE.Are_Different_Prints, name_pair_to_var_list pair)
| surf_to_mod (Fpnode_Has_Print     pair) = EQC.Assert (EE.Fpnode_Has_Print,     name_pair_to_var_list pair)
(*Eval_Number*)
| surf_to_mod (Are_Same_Number pair) = EQC.Assert (EE.Are_Same_Number, name_pair_to_var_list pair)
| surf_to_mod (Is_Less_Than    pair) = EQC.Assert (EE.Is_Less_Than,    name_pair_to_var_list pair)
| surf_to_mod (Is_Int   (name, int)) = EQC.Assert (EE.Is_Int,          [EQC.Var name, EQC.Literal (EE.Int int)])
(*Other*)
| surf_to_mod (Is_Nth_Arg_Of (fp_name1, numb_name, fp_name2)) = EQC.Assert (EE.Is_Nth_Arg_Of, [EQC.Var fp_name1, EQC.Var numb_name, EQC.Var fp_name2])
(*Quantifier*)
| surf_to_mod (All  (name, qyp, assert)) = EQC.All  (name, qyp, surf_to_mod assert)
| surf_to_mod (Some (name, qyp, assert)) = EQC.Some (name, qyp, surf_to_mod assert)
(*Modifier*)
| surf_to_mod (Is_Rule_Of pair) = surf_to_mod (Are_Same_Prints pair)(*TODO: maybe we need a sanity checker to confirm that the first argument is rule.*)
(*Semantic*)
| surf_to_mod (Is_Defined_With        (name,   cmnd)) = EQC.Assert (EE.Is_Defined_With, [EQC.Var name, EQC.Literal (EE.Command cmnd)])
| surf_to_mod (Holds_In_Any_Clause_Of (assert, name)) = undefined ((*TODO*))
| surf_to_mod (Holds_In_One_Clause_Of (assert, name)) = undefined ((*TODO*));

fun convert_result (EQC.Literal (EE.Bool true )) = True
  | convert_result (EQC.Literal (EE.Bool false)) = False
  | convert_result  _ = error "eval in Eval_Syntax_Struct failed. Evaluation is not complete.";

val sanity_check = undefined: assert -> bool;

val pst_to_modifiers = undefined; (*TODO: probably in Eval_Modifier*)

fun eval (pst:Proof.state) (assert:assert) =
  let
    val eqc_expr             = surf_to_mod assert       : EQC.expr;
    val eqc_result           = EQC.eval pst eqc_expr    : EQC.expr;
    val result               = convert_result eqc_result: assert;
  in
    result
  end;

end;