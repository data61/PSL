(*  Title:      PSL/SeLFiE/src/Eval_Surface_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Surface:EVAL_SURFACE =
struct

type full_path = full_path;
type print     = LiFtEr_Util.print;
type name      = string;

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule;

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
| Is_Rule_Of             of name * name;

val name_dup_check = undefined: assert -> bool;

val type_check = undefined: assert -> bool;

structure EM = Eval_Modifier;
structure EC = Eval_Connective;
structure EP = Eval_Parameters;

val pair_to_list = Utils.pair_to_list;

fun convert_qtyp QFull_Path = EM.QFull_Path
  | convert_qtyp QPrint     = EM.QPrint
  | convert_qtyp QInd       = EM.QInd
  | convert_qtyp QArb       = EM.QArb
  | convert_qtyp QRule      = EM.QRule;

fun surf_pair_to_mod_list pair = map surf_to_mod (pair_to_list pair)
and surf_list_to_mod_list list = map surf_to_mod  list
and name_pair_to_var_list pair = map EM.Var      (pair_to_list pair)
and 
(*Eval_Connective*)
  surf_to_mod True         = EM.Literal (EP.Connective (EC.True))
| surf_to_mod False        = EM.Literal (EP.Connective (EC.False))
| surf_to_mod (Not   ass)  = EM.Assert (EP.Not,  [surf_to_mod ass] )
| surf_to_mod (And   pair) = EM.Assert (EP.And,   surf_pair_to_mod_list pair)
| surf_to_mod (Or    pair) = EM.Assert (EP.Or,    surf_pair_to_mod_list pair)
| surf_to_mod (Nor   pair) = EM.Assert (EP.Or,    surf_pair_to_mod_list pair)
| surf_to_mod (Imply pair) = EM.Assert (EP.Imply, surf_pair_to_mod_list pair)
| surf_to_mod (Ands  list) = EM.Assert (EP.Ands,  surf_list_to_mod_list list)
| surf_to_mod (Ors   list) = EM.Assert (EP.Ors,   surf_list_to_mod_list list)
(*Eval_Node_Core*)
| surf_to_mod (Is_Cnst   name) = EM.Assert (EP.Is_Cnst,   [EM.Var name])
| surf_to_mod (Is_Free   name) = EM.Assert (EP.Is_Free,   [EM.Var name])
| surf_to_mod (Is_Var    name) = EM.Assert (EP.Is_Var,    [EM.Var name])
| surf_to_mod (Is_Bound  name) = EM.Assert (EP.Is_Bound,  [EM.Var name])
| surf_to_mod (Is_Lambda name) = EM.Assert (EP.Is_Lambda, [EM.Var name])
| surf_to_mod (Is_App    name) = EM.Assert (EP.Is_App,    [EM.Var name])
(*Eval_Node_Sugar*)
| surf_to_mod (Is_Atom    name) = EM.Assert (EP.Is_Atom,    [EM.Var name])
| surf_to_mod (Is_Compund name) = EM.Assert (EP.Is_Compund, [EM.Var name])
(*Eval_Unode_Core*)
| surf_to_mod (Has_Same_Prnt_As  pair) = EM.Assert (EP.Has_Same_Prnt_As,  name_pair_to_var_list pair)
| surf_to_mod (Is_In_Trm_Prnt    pair) = EM.Assert (EP.Is_In_Trm_Prnt,    name_pair_to_var_list pair)
| surf_to_mod (Is_Deeper_Than    pair) = EM.Assert (EP.Is_Deeper_Than,    name_pair_to_var_list pair)
| surf_to_mod (Is_Shallower_Than pair) = EM.Assert (EP.Is_Shallower_Than, name_pair_to_var_list pair)
| surf_to_mod (Is_Path_Above     pair) = EM.Assert (EP.Is_Path_Above,     name_pair_to_var_list pair)
| surf_to_mod (Is_Same_Path_As   pair) = EM.Assert (EP.Is_Same_Path_As,   name_pair_to_var_list pair)
(*Eval_Unode_Sugar*)
| surf_to_mod (Is_As_Deep_As     pair) = EM.Assert (EP.Is_As_Deep_As,     name_pair_to_var_list pair)
| surf_to_mod (Is_Path_Below     pair) = EM.Assert (EP.Is_Path_Below,     name_pair_to_var_list pair)
(*Eval_Fpunode_Core*)
| surf_to_mod (Is_In_Same_Location_As pair) = EM.Assert (EP.Is_In_Same_Location_As, name_pair_to_var_list pair)
| surf_to_mod (Is_In_Chained          name) = EM.Assert (EP.Is_In_Chained,          [EM.Var name])
| surf_to_mod (Is_In_Fst_Subg         name) = EM.Assert (EP.Is_In_Fst_Subg,         [EM.Var name])
(*Eval_Fpunode_Sugar*)
| surf_to_mod (Is_Above       pair) = EM.Assert (EP.Is_Above,       name_pair_to_var_list pair)
| surf_to_mod (Is_Below       pair) = EM.Assert (EP.Is_Below,       name_pair_to_var_list pair)
| surf_to_mod (Is_Same_Occ_As pair) = EM.Assert (EP.Is_Same_Occ_As, name_pair_to_var_list pair)
(*Eval_Print_Core*)
| surf_to_mod (Are_Same_Prints  pair         ) = EM.Assert (EP.Are_Same_Prints, name_pair_to_var_list pair)
| surf_to_mod (Is_Printed_As   (name, string)) = EM.Assert (EP.Is_Printed_As,   [EM.Var name, EM.Literal (EP.String string)])
(*Eval_Print_Sugar*)
| surf_to_mod (Are_Different_Prints pair) = EM.Assert (EP.Are_Different_Prints, name_pair_to_var_list pair)
| surf_to_mod (Fpnode_Has_Print     pair) = EM.Assert (EP.Fpnode_Has_Print,     name_pair_to_var_list pair)
(*Eval_Number*)
| surf_to_mod (Are_Same_Number pair) = EM.Assert (EP.Are_Same_Number, name_pair_to_var_list pair)
| surf_to_mod (Is_Less_Than    pair) = EM.Assert (EP.Is_Less_Than,    name_pair_to_var_list pair)
| surf_to_mod (Is_Int   (name, int)) = EM.Assert (EP.Is_Int,          [EM.Var name, EM.Literal (EP.Int int)])
(*Other*)
| surf_to_mod (Is_Nth_Arg_Of (fp_name1, numb_name, fp_name2)) = EM.Assert (EP.Is_Nth_Arg_Of, [EM.Var fp_name1, EM.Var numb_name, EM.Var fp_name2])
(*Quantifier*)
| surf_to_mod (All  (name, qyp, assert)) = EM.All  (name, convert_qtyp qyp, surf_to_mod assert)
| surf_to_mod (Some (name, qyp, assert)) = EM.Some (name, convert_qtyp qyp, surf_to_mod assert)
(*Modifier*)
| surf_to_mod (Is_Rule_Of pair) = surf_to_mod (Are_Same_Prints pair);

fun convert_result (EM.Literal (EP.Connective EC.True))  = True
  | convert_result (EM.Literal (EP.Connective EC.False)) = False
  | convert_result  _ = error "eval in Eval_Syntax_Struct failed. Evaluation is not complete.";

fun eval (pst:Proof.state) (assert:assert) =
  let
    val em_expr   = surf_to_mod assert      : EM.expr;
    val em_result = EM.eval pst em_expr     : EM.expr;
    val result    = convert_result em_result: assert;
  in
    result
  end;

end;