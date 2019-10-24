(*  Title:      PSL/SeLFeE/src/Eval_Primitive_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Primitive: EVAL_PRIMITIVE =
struct

structure EC  = Eval_Connective;
structure EPC = Eval_Print_Core;
structure EPS = Eval_Print_Sugar;
structure EN  = Eval_Number;
structure EFP = Eval_Full_Path;

type connective = Eval_Connective.assert;
type node       = UN.node;
type unode      = UN.unode;
type fpunode    = Full_Path_To_Fpunode.fpunode;
type print      = LiFtEr_Util.print;
type number     = Eval_Number.number;

datatype assert =
(*Eval_Node_Core*)
  Is_Cnst                of full_path
| Is_Free                of full_path
| Is_Var                 of full_path
| Is_Bound               of full_path
| Is_Lambda              of full_path
| Is_App                 of full_path
(*Eval_Node_Sugar*)
| Is_Atom                of full_path
| Is_Compund             of full_path
(*Eval_Unode_Core*)
| Has_Same_Prnt_As       of full_path * full_path
| Is_In_Trm_Prnt         of full_path * full_path
| Is_Deeper_Than         of full_path * full_path
| Is_Shallower_Than      of full_path * full_path
| Is_Path_Above          of full_path * full_path
| Is_Same_Path_As        of full_path * full_path
(*Eval_Unode_Sugar*)
| Is_As_Deep_As          of full_path * full_path
| Is_Path_Below          of full_path * full_path
(*Eval_Fpunode_Core*)
| Is_In_Same_Location_As of full_path * full_path
| Is_In_Chained          of full_path
| Is_In_Fst_Subg         of full_path
(*Eval_Fpunode_Sugar*)
| Is_Above               of full_path * full_path
| Is_Below               of full_path * full_path
| Is_Same_Occ_As         of full_path * full_path
(*Eval_Print_Core*)
| Are_Same_Prints        of print * print
| Is_Printed_As          of print * string
(*Eval_Print_Sugar*)
| Are_Different_Prints   of print     * print
| Fpnode_Has_Print       of full_path * print
(*Eval_Number*)
| Are_Same_Number        of number * number
| Is_Less_Than           of number * number
| Is_Int                 of number * int
(*Others*)
| Is_Nth_Arg_Of          of full_path * number * full_path;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;

fun eval fpun_table assert =
  let
    fun (*Eval_Node_Core*)
        eval' (Is_Cnst   full_path)  = EFP.eval fpun_table (EFP.Is_Cnst   full_path)
      | eval' (Is_Free   full_path)  = EFP.eval fpun_table (EFP.Is_Free   full_path)
      | eval' (Is_Var    full_path)  = EFP.eval fpun_table (EFP.Is_Var    full_path)
      | eval' (Is_Bound  full_path)  = EFP.eval fpun_table (EFP.Is_Bound  full_path)
      | eval' (Is_Lambda full_path)  = EFP.eval fpun_table (EFP.Is_Lambda full_path)
      | eval' (Is_App    full_path)  = EFP.eval fpun_table (EFP.Is_App    full_path)
      (*Eval_Node_Sugar*)
      | eval' (Is_Atom    full_path) = EFP.eval fpun_table (EFP.Is_Atom full_path)
      | eval' (Is_Compund full_path) = EFP.eval fpun_table (EFP.Is_Compund full_path)
      (*Eval_Unode_Core*)
      | eval' (Has_Same_Prnt_As  pair) = EFP.eval fpun_table (EFP.Has_Same_Prnt_As  pair)
      | eval' (Is_In_Trm_Prnt    pair) = EFP.eval fpun_table (EFP.Is_In_Trm_Prnt    pair)
      | eval' (Is_Deeper_Than    pair) = EFP.eval fpun_table (EFP.Is_Deeper_Than    pair)
      | eval' (Is_Shallower_Than pair) = EFP.eval fpun_table (EFP.Is_Shallower_Than pair)
      | eval' (Is_Path_Above     pair) = EFP.eval fpun_table (EFP.Is_Path_Above     pair)
      | eval' (Is_Same_Path_As   pair) = EFP.eval fpun_table (EFP.Is_Same_Path_As   pair)
      (*Eval_Unode_Sugar*)
      | eval' (Is_As_Deep_As pair) = EFP.eval fpun_table (EFP.Is_As_Deep_As pair)
      | eval' (Is_Path_Below pair) = EFP.eval fpun_table (EFP.Is_Path_Below pair)
      (*Eval_Fpunode_Core*)
      | eval' (Is_In_Same_Location_As pair) = EFP.eval fpun_table (EFP.Is_In_Same_Location_As pair)
      | eval' (Is_In_Chained          fpun) = EFP.eval fpun_table (EFP.Is_In_Chained          fpun)
      | eval' (Is_In_Fst_Subg         fpun) = EFP.eval fpun_table (EFP.Is_In_Fst_Subg         fpun)
      (*Eval_Fpunode_Sugar*)
      | eval' (Is_Above       pair) = EFP.eval fpun_table (EFP.Is_Above pair)
      | eval' (Is_Below       pair) = EFP.eval fpun_table (EFP.Is_Below pair)
      | eval' (Is_Same_Occ_As pair) = EFP.eval fpun_table (EFP.Is_Same_Occ_As pair)
      (*Eval_Print_Core*)
      | eval' (Are_Same_Prints pair) = EPC.eval (EPC.Are_Same_Prints pair)
      | eval' (Is_Printed_As pair)   = EPC.eval (EPC.Is_Printed_As   pair)
      (*Eval_Print_Sugar*)
      | eval' (Are_Different_Prints pair) = EPS.eval (EPS.Are_Different_Prints pair)
      | eval' (Fpnode_Has_Print     pair) = EFP.eval fpun_table (EFP.Fpnode_Has_Print pair)
      (*Eval_Number*)
      | eval' (Are_Same_Number pair) = EN.eval (EN.Are_Same_Number pair)
      | eval' (Is_Less_Than    pair) = EN.eval (EN.Is_Less_Than    pair)
      | eval' (Is_Int          pair) = EN.eval (EN.Is_Int          pair)
      (*Others*)
      | eval' (Is_Nth_Arg_Of ((loc1, path1), EN.Number n,  (loc2, path2))) =
        (loc1 = loc2 andalso UN.is_nth_arg_of path1 n path2) |> EC.bool_to_assert_connective;
  in
    eval' assert
  end;

end;