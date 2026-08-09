(*  Title:      Abduction/Remove_Outermost_Assumption.ML
    Author:     Yutaka Nagashima, Huawei Technologies Research & Development (UK) Limited.
    Author:     Daniel Goc Sebastian, Huawei Technologies Research & Development (UK) Limited.

A top-down conjecturing heuristic that removes the outermost assumption of a goal.
*)
(*** structure Remove_Outermost_Assumption ***)
structure Remove_Outermost_Assumption: TOP_DOWN_CONJECTURING =
struct

fun top_down_conjectures _ _ (trm:term) =
   try Logic.dest_implies trm <$> snd <$> pair "remove_assumption"
|> the_list: (string * term) list;

end;