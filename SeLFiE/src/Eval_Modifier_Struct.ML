(*  Title:      PSL/SeLFiE/src/Eval_Modifier_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Modifier: EVAL_MODIFIER =
struct

structure EC  = Eval_Connective;
structure LU  = LiFtEr_Util;
structure EPC = Eval_Print_Core;
structure EN  = Eval_Number;

type print         = LiFtEr_Util.print;
type prints        = LiFtEr_Util.prints;
type fpunode       = Full_Path_To_Fpunode.fpunode;
type number        = Eval_Number.number;
datatype modifiers = Modifiers of {ons:   prints,
                                   arbs:  prints,
                                   rules: prints};

datatype assert =
  Is_Nth_Ind of print * number (*Counting starts with 0.*)
| Is_Nth_Arb of print * number (*Counting starts with 0.*);

val try' = Utils.try';

fun eval' pair = EPC.eval (EPC.Are_Same_Prints pair): EC.assert;

fun eval (Modifiers {ons,...})  (Is_Nth_Ind (prnt, EN.Number i)) = eval' (try' "eval in Eval_Modifier failed at Is_Nth_Ind" nth ons  i, prnt)
  | eval (Modifiers {arbs,...}) (Is_Nth_Arb (prnt, EN.Number i)) = eval' (try' "eval in Eval_Modifier failed at Is_Nth_Arb" nth arbs i, prnt);

end;