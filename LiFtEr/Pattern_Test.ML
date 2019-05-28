(*  Title:      PSL/LiFtEr/Pattern_Test.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** Pattern_Test ***)
structure Pattern_Test =
struct

open Pattern;
val _ = ctxt_n_name_to_patterns_of_each_param @{context} "List.nth"
val _ = @{assert} true;

end;