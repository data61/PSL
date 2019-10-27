(*  Title:      PSL/SeLFeE/src/Eval_Bound_Test.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

local

open Eval_Bound;
structure EC = Eval_Connective;
structure EP = Eval_Parameters;
structure EE = Eval_Expression;
structure EM = Eval_Modifier;
val empty_table = Full_Path_Table.empty;
val empty_mods  = EM.Modifiers {ons = [], arbs = [], rules = []};

in

(*TODO: I had to comment out these tests becasue of the change of the type signature of eval.*)
(*
(*(\<lambda>x. x) True = True*)
val expr1 =
Apply
 (Lambda
  (Bound 0),
 (Literal (EE.Bool true)));
                                                                       
val _ = @{assert} (Literal (EE.Bool true) = eval empty_table empty_mods expr1);

(*(\<lambda>x. \<lambda>y. y) True False = False*)
val expr2 =
Apply
 (Apply
  (Lambda
   (Lambda
    (Bound 0)),
   (Literal (EE.Bool true))),
  (Literal (EE.Bool false))
  );

val _ = @{assert} (Literal (EE.Bool false) = eval empty_table empty_mods expr2);

(*True \<or> False = True*)
(*
val expr3 = Connective (EC.Or (EC.True, EC.False));
*)
val expr3 =
Assert
 (EE.Or,
  [(Literal (EE.Bool true)),
   (Literal (EE.Bool false))
   ])

val _ = @{assert} (Literal (EE.Bool true) = eval empty_table empty_mods expr3);
(*
(*True \<and> False = False*)
val expr4 = Connective (EC.And (EC.True, EC.False));

val _ = @{assert} (Connective EC.False = eval empty_table expr4);
*)
(*(\<lambda>x. Not x) False = True*)
val expr5 =
Apply
 (Lambda
  (Assert (EE.Not, [Bound 0])),
 (Literal (EE.Bool false)));
(*What? We have two Trues? One as assert the other one as parameter?*)

val _ = @{assert} (Literal (EE.Bool true) = eval empty_table empty_mods expr5);
*)
end;