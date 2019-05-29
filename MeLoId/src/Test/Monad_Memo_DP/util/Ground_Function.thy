theory Ground_Function
  imports Main
  keywords
    "ground_function" :: thy_decl
begin

ML_file \<open>../util/Ground_Function.ML\<close>

ML \<open>
fun ground_function_cmd ((termination, binding), thm_refs) lthy =
  let
    val def_thms = Attrib.eval_thms lthy thm_refs
  in
    Ground_Function.mk_fun (termination <> NONE) def_thms binding lthy
  end

val ground_function_parser =
  Scan.option (Parse.$$$ "(" |-- Parse.reserved "prove_termination" --| Parse.$$$ ")")
  -- (Parse.binding --| Parse.$$$ ":") (* scope, e.g., bf\<^sub>T *)
  -- Parse.thms1

val _ =
  Outer_Syntax.local_theory @{command_keyword ground_function}
  "Define a new ground constant from an existing function definition"
    (ground_function_parser >> ground_function_cmd)
\<close>

end