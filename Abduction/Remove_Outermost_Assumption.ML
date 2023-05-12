(*
 * Remove_Outermost_Assumption.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
(*** structure Remove_Outermost_Assumption ***)
structure Remove_Outermost_Assumption: TOP_DOWN_CONJECTURING =
struct

fun top_down_conjectures _ (trm:term) = try Logic.dest_implies trm <$> snd <$> pair "remove_assumption" |> the_list: (string * term) list;

end;