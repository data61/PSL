(*  Title:      PSL/SeLFeE/src/Eval_Path_Expression_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    Eval_Expression has constructs from Eval_Connective.
*)
structure Eval_Path_Expression: EVAL_PATH_EXPRESSION =
struct           

structure EC  = Eval_Connective;
structure EPC = Eval_Print_Core;
structure EPS = Eval_Print_Sugar;
structure EPT = Eval_Path;
structure EN  = Eval_Number;
structure EPR = Eval_Path_Parameter;

type connective = Eval_Connective.assert;
type path       = LiFtEr_Util.path;
type print      = LiFtEr_Util.print;
type number     = Eval_Number.number;
type command    = Pattern.command;

datatype parameter =
  Bool       of bool
| Path       of path
| Print      of print
| String     of string(*redundant?*)
| Number     of Eval_Number.number
| Int        of int
| Command    of command;

type  parameters = parameter list;

fun convert_param (Bool       _) = error "convert_param in Eval_Expression_Struct failed."
  | convert_param (Path       p) = EPR.Path p
  | convert_param (Print      p) = EPR.Print p
  | convert_param (String     s) = EPR.String s
  | convert_param (Number     n) = EPR.Number n
  | convert_param (Int        i) = EPR.Int i
  | convert_param (Command    c) = EPR.Command c;

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
(*Eval_Print_Core*)
| Are_Same_Prints
| Is_Printed_As
(*Eval_Print_Sugar*)
| Are_Different_Prints
| Unode_Has_Print
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Int;

type full_path_to_fpunode_table = Path_To_Unode.path_to_unode_table;

val bool_to_connect    = EC.bool_to_assert_connective;
val bools_to_connects  = Utils.map_pair bool_to_connect;
val de_bool_to_connect = bool_to_connect o de_Bool;

fun expr_to_param Is_Cnst              = EPR.Is_Cnst
(*Eval_Node_Core*)
  | expr_to_param Is_Free              = EPR.Is_Free
  | expr_to_param Is_Var               = EPR.Is_Var
  | expr_to_param Is_Bound             = EPR.Is_Bound
  | expr_to_param Is_Lambda            = EPR.Is_Lambda
  | expr_to_param Is_App               = EPR.Is_App
  (*Eval_Node_Sugar*)
  | expr_to_param Is_Atom              = EPR.Is_Atom
  | expr_to_param Is_Compund           = EPR.Is_Compund
  (*Eval_Unode_Core*)
  | expr_to_param Has_Same_Prnt_As     = EPR.Has_Same_Prnt_As
  | expr_to_param Is_In_Trm_Prnt       = EPR.Is_In_Trm_Prnt
  | expr_to_param Is_Deeper_Than       = EPR.Is_Deeper_Than
  | expr_to_param Is_Shallower_Than    = EPR.Is_Shallower_Than
  | expr_to_param Is_Path_Above        = EPR.Is_Path_Above
  | expr_to_param Is_Same_Path_As      = EPR.Is_Same_Path_As
  (*Eval_Unode_Sugar*)
  | expr_to_param Is_As_Deep_As        = EPR.Is_As_Deep_As
  | expr_to_param Is_Path_Below        = EPR.Is_Path_Below
  (*Eval_Print_Core*)
  | expr_to_param Are_Same_Prints      = EPR.Are_Same_Prints
  | expr_to_param Is_Printed_As        = EPR.Is_Printed_As
  (*Eval_Print_Sugar*)
  | expr_to_param Are_Different_Prints = EPR.Are_Different_Prints
  | expr_to_param Unode_Has_Print      = EPR.Unode_Has_Print
  (*Eval_Number*)
  | expr_to_param Are_Same_Number      = EPR.Are_Same_Number
  | expr_to_param Is_Less_Than         = EPR.Is_Less_Than
  | expr_to_param Is_Int               = EPR.Is_Int
  | expr_to_param _                    = error "expr_to_param in Eval_Expression_Struct failed.";

fun eval trm pst assert parameters =
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
      | eval' ass params = EPR.eval trm pst (expr_to_param ass) (map convert_param params)
    val ec_result = eval' assert parameters: Eval_Connective.assert;
    val result    = ec_result |> EC.assert_connective_to_bool |> Bool;
  in
    result
  end;

end;