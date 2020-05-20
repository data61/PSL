chapter "CakeML Compiler"

theory CakeML_Compiler
imports
  "generated/CakeML/Ast"
  "Show.Show_Instances"
keywords "cakeml" :: diag
begin

hide_const (open) Lem_string.concat

ML_file \<open>Tools/cakeml_sexp.ML\<close>
ML_file \<open>Tools/cakeml_compiler.ML\<close>

end