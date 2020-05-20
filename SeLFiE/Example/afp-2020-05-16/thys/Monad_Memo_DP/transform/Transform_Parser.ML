structure Transform_Parser = struct

val dp_fun_parser =
  Parse.binding (* name of instantiation and monadified term *)

(*
fun dp_fun binding =
  Transform_Data.update_last_binding binding
*)

val memoizes_parser =
  Parse.name_position (* name of locale, e.g. dp_consistency_rbt *)

val monadifies_parser =
  Parse.term (* term to be monadified *)
  -- Scan.option (
    @{keyword "("}
    |--  Parse.thms1 --| (* optional definitions, ".simps" as default *)
    @{keyword ")"})

val dp_monadify_cmd_parser =
  Scan.optional (Parse.binding --| Parse.$$$ ":") Binding.empty (* optional scope *)
  -- Parse.term (* term to be monadified *)
  -- Scan.option (@{keyword "("} |-- (* optional definitions, ".simps" as default *)
      Parse.thms1
    --| @{keyword ")"})
  -- Scan.option (@{keyword with_memory} |-- Parse.name_position) (* e.g. dp_consistency_rbt *)

val instance =
  (Parse.where_ |-- Parse.and_list1 (Parse.name -- (Parse.$$$ "=" |-- Parse.term))
  || Scan.succeed [])

val dp_fun_part1_parser =
  (Parse.binding --| Parse.$$$ ":") (* scope, e.g., bf\<^sub>T *)
  -- Parse.term (* term to be monadified, e.g., bf *)
  -- Scan.option (@{keyword with_memory}
    |-- Parse.opt_keyword "default_proof" -- Parse.name_position -- instance
    ) (* e.g. dp_consistency_rbt *)

val dp_fun_part2_parser =
  (* monadifies *)
  (@{keyword "("} |-- Parse.name --| @{keyword ")"}) -- Parse.thms1

end
