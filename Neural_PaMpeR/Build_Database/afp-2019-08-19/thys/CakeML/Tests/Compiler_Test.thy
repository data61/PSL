theory Compiler_Test
imports "../CakeML_Compiler"
begin

definition default_loc :: locs where
"default_loc =
  (\<lparr> locn.row = 0, locn.col = 0, locn.offset = 0 \<rparr>,
   \<lparr> locn.row = 0, locn.col = 0, locn.offset = 0 \<rparr>)"

definition simple_print :: Ast.prog where
"simple_print =
  [Ast.Tdec (Ast.Dlet default_loc Ast.Pany (Ast.App Ast.Opapp [Ast.Var (Short ''print''), Ast.Lit (Ast.StrLit ''hi'')]))]"

cakeml (literal) \<open>print "hi1";\<close>
cakeml (literal) \<open>print "hi2";\<close>

ML\<open>
  val out = CakeML_Compiler.eval_source CakeML_Compiler.Literal \<open>val x = 3 + 4; print (Int.toString x);\<close>;
  @{assert} (out = "7")
\<close>

cakeml (prog) \<open>simple_print\<close>

end