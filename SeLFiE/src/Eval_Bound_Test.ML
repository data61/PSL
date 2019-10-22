(*  Title:      PSL/SeLFeE/src/Eval_Bound_Test.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

local

open Eval_Bound;
structure EC = Eval_Connective;
val empty_table = Full_Path_Table.empty;

in

(*(\<lambda>x. x) True*)
val expr1 =
Apply
 (Lambda
  (Bound 0),
 (Connective EC.True));

val _ = @{assert} (Connective EC.True = eval empty_table expr1);
(*
val expr2 =
Apply
 (Lambda
  (Apply
   (Assert (Eval_Parameters.Not)
    Bound 0)
   ),
 (Connective EC.True));
*)
end;