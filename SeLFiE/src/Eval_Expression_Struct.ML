(*  Title:      PSL/SeLFeE/src/Eval_Expression_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    Eval_Expression has constructs from Eval_Connective.
*)
structure Eval_Expression: EVAL_EXPRESSION =
struct           

structure EC  = Eval_Connective;
structure EPC = Eval_Print_Core;
structure EPS = Eval_Print_Sugar;
structure EFP = Eval_Full_Path;
structure EN  = Eval_Number;
structure EP  = Eval_Parameters;
structure EM  = Eval_Modifier;

type connective = Eval_Connective.assert;
type print      = LiFtEr_Util.print;
type number     = Eval_Number.number;
type command    = Pattern.command;

datatype parameter =
  Bool       of bool
| Full_Path  of full_path
| Print      of print
| String     of string(*redundant?*)
| Number     of Eval_Number.number
| Int        of int
| Command    of command;

type  parameters = parameter list;

fun convert_param (Bool       _) = error "convert_param in Eval_Expression_Struct failed."
  | convert_param (Full_Path fp) = EP.Full_Path fp
  | convert_param (Print      p) = EP.Print p
  | convert_param (String     s) = EP.String s
  | convert_param (Number     n) = EP.Number n
  | convert_param (Int        i) = EP.Int i
  | convert_param (Command    c) = EP.Command c;

fun de_Bool (Bool c) = c
  | de_Bool  _       = error "de_Bool in Eval_Expression_Struct failed."

datatype assert =
(*Eval_Connective*)
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
(*Eval_Node_Core*)
| Is_Cnst
| Is_Free
| Is_Var
| Is_Bound
| Is_Lambda
| Is_App
(*Eval_Node_Sugar*)
| Is_Atom
| Is_Compund
(*Eval_Unode_Core*)
| Has_Same_Prnt_As
| Is_In_Trm_Prnt
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Path_Above
| Is_Same_Path_As
(*Eval_Unode_Sugar*)
| Is_As_Deep_As
| Is_Path_Below     
(*Eval_Fpunode_Core*)
| Is_In_Same_Location_As
| Is_In_Chained
| Is_In_Fst_Subg
(*Eval_Fpunode_Sugar*)
| Is_Above
| Is_Below
| Is_Same_Occ_As
(*Eval_Print_Core*)
| Are_Same_Prints
| Is_Printed_As
(*Eval_Print_Sugar*)
| Are_Different_Prints
| Fpnode_Has_Print
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Int
(*Eval_Modifier*)
| Is_Nth_Ind
| Is_Nth_Arb
(*Others*)
| Is_Nth_Arg_Of
| Is_Defined_With;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;
type modifiers                  = Eval_Modifier.modifiers;

val bool_to_connect    = EC.bool_to_assert_connective;
val bools_to_connects  = Utils.map_pair bool_to_connect;
val de_bool_to_connect = bool_to_connect o de_Bool;

fun expr_to_param Is_Cnst                = EP.Is_Cnst
(*Eval_Node_Core*)
  | expr_to_param Is_Free                = EP.Is_Free
  | expr_to_param Is_Var                 = EP.Is_Var
  | expr_to_param Is_Bound               = EP.Is_Bound
  | expr_to_param Is_Lambda              = EP.Is_Lambda
  | expr_to_param Is_App                 = EP.Is_App
  (*Eval_Node_Sugar*)
  | expr_to_param Is_Atom                = EP.Is_Atom
  | expr_to_param Is_Compund             = EP.Is_Compund
  (*Eval_Unode_Core*)
  | expr_to_param Has_Same_Prnt_As       = EP.Has_Same_Prnt_As
  | expr_to_param Is_In_Trm_Prnt         = EP.Is_In_Trm_Prnt
  | expr_to_param Is_Deeper_Than         = EP.Is_Deeper_Than
  | expr_to_param Is_Shallower_Than      = EP.Is_Shallower_Than
  | expr_to_param Is_Path_Above          = EP.Is_Path_Above
  | expr_to_param Is_Same_Path_As        = EP.Is_Same_Path_As
  (*Eval_Unode_Sugar*)
  | expr_to_param Is_As_Deep_As          = EP.Is_As_Deep_As
  | expr_to_param Is_Path_Below          = EP.Is_Path_Below
  (*Eval_Fpunode_Core*)
  | expr_to_param Is_In_Same_Location_As = EP.Is_In_Same_Location_As
  | expr_to_param Is_In_Chained          = EP.Is_In_Chained
  | expr_to_param Is_In_Fst_Subg         = EP.Is_In_Fst_Subg
  (*Eval_Fpunode_Sugar*)
  | expr_to_param Is_Above               = EP.Is_Above
  | expr_to_param Is_Below               = EP.Is_Below
  | expr_to_param Is_Same_Occ_As         = EP.Is_Same_Occ_As
  (*Eval_Print_Core*)
  | expr_to_param Are_Same_Prints        = EP.Are_Same_Prints
  | expr_to_param Is_Printed_As          = EP.Is_Printed_As
  (*Eval_Print_Sugar*)
  | expr_to_param Are_Different_Prints   = EP.Are_Different_Prints
  | expr_to_param Fpnode_Has_Print       = EP.Fpnode_Has_Print
  (*Eval_Number*)
  | expr_to_param Are_Same_Number        = EP.Are_Same_Number
  | expr_to_param Is_Less_Than           = EP.Is_Less_Than
  | expr_to_param Is_Int                 = EP.Is_Int
  (*Eval_Modifier*)
  | expr_to_param Is_Nth_Ind             = EP.Is_Nth_Ind
  | expr_to_param Is_Nth_Arb             = EP.Is_Nth_Arb
  (*Others*)
  | expr_to_param Is_Nth_Arg_Of          = EP.Is_Nth_Arg_Of
  | expr_to_param Is_Defined_With        = EP.Is_Defined_With
  | expr_to_param _                      = error "expr_to_param in Eval_Expression_Struct failed.";

fun eval pst assert parameters =
  let
    fun
      (*Eval_Connective*)
        eval' Not   [Bool b]           = EC.eval (EC.Not   (bool_to_connect    b      ))
      | eval' And   [Bool b1, Bool b2] = EC.eval (EC.And   (bools_to_connects (b1, b2)))
      | eval' Or    [Bool b1, Bool b2] = EC.eval (EC.Or    (bools_to_connects (b1, b2)))
      | eval' Nor   [Bool b1, Bool b2] = EC.eval (EC.Nor   (bools_to_connects (b1, b2)))
      | eval' Imply [Bool b1, Bool b2] = EC.eval (EC.Imply (bools_to_connects (b1, b2)))
      | eval' Ands  ands               = EC.eval (EC.Ands  (map de_bool_to_connect ands))
      | eval' Ors   ors                = EC.eval (EC.Ors   (map de_bool_to_connect ors ))
      (*Eval_Node_Core*)
      | eval' ass params = EP.eval pst (expr_to_param ass) (map convert_param params)
    val ec_result = eval' assert parameters: Eval_Connective.assert;
    val result    = ec_result |> EC.assert_connective_to_bool |> Bool;
  in
    result
  end;

end;