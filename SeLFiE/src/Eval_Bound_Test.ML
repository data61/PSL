(*  Title:      PSL/SeLFeE/src/Eval_Bound_Test.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

local

open Eval_Bound;
structure EC = Eval_Connective;
structure EP = Eval_Parameters;
val empty_table = Full_Path_Table.empty;

in

(*(\<lambda>x. x) True = True*)
val expr1 =
Apply
 (Lambda
  (Bound 0),
 (Connective EC.True));
                                                                       
val _ = @{assert} (Connective EC.True = eval empty_table expr1);

(*(\<lambda>x. \<lambda>y. y) True False = False*)
val expr2 =
Apply
 (Apply
   (Lambda
     (Lambda
      (Bound 0)),
     (Connective EC.True)),
  Connective EC.False
  );

val _ = @{assert} (Connective EC.False = eval empty_table expr2);

(*True \<or> False = True*)
val expr3 = Connective (EC.Or (EC.True, EC.False));
(*
val _ = @{assert} (Connective EC.True = eval empty_table expr3);

(*True \<and> False = False*)
val expr4 = Connective (EC.And (EC.True, EC.False));

val _ = @{assert} (Connective EC.False = eval empty_table expr4);
*)
(*(\<lambda>x. Not x) False = True*)
val expr5 =
Apply
 (Lambda
  (Assert (EP.Not, [Bound 0])),
 (Literal (EP.Connective EC.False)));
(*What? We have two Trues? One as assert the other one as parameter?*)

val _ = @{assert} (Connective EC.True = eval empty_table expr5);

end;