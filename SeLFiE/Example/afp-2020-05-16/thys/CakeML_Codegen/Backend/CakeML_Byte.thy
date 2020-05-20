section \<open>Converting bytes to integers\<close>

theory CakeML_Byte
imports
  CakeML.Evaluate_Single
  Show.Show_Instances
begin

definition pat :: Ast.pat where
"pat = Ast.Pcon (Some (Short ''String_char_Char'')) (map (\<lambda>n. Ast.Pvar (''b'' @ show n)) [0..<8])"

definition cake_plus :: "exp \<Rightarrow> exp \<Rightarrow> exp" where
"cake_plus t u = Ast.App (Ast.Opn Ast.Plus) [t, u]"

lemma cake_plus_correct:
  assumes "evaluate env s u = (s', Rval (Litv (IntLit y)))"
  assumes "evaluate env s' t = (s'', Rval (Litv (IntLit x)))"
  shows "evaluate env s (cake_plus t u) = (s'', Rval (Litv (IntLit (x + y))))"
unfolding cake_plus_def using assms by simp

definition cake_times :: "exp \<Rightarrow> exp \<Rightarrow> exp" where
"cake_times t u = Ast.App (Ast.Opn Ast.Times) [t, u]"

lemma cake_times_correct:
  assumes "evaluate env s u = (s', Rval (Litv (IntLit y)))"
  assumes "evaluate env s' t = (s'', Rval (Litv (IntLit x)))"
  shows "evaluate env s (cake_times t u) = (s'', Rval (Litv (IntLit (x * y))))"
unfolding cake_times_def using assms by simp

definition cake_int_of_bool :: "exp \<Rightarrow> exp" where
"cake_int_of_bool e = Ast.Mat e
  [(Ast.Pcon (Some (Short ''HOL_False'')) [], Lit (IntLit 0)),
   (Ast.Pcon (Some (Short ''HOL_True'')) [], Lit (IntLit 1))]"

definition summands :: "exp list" where
"summands = map (\<lambda>n. cake_times (Lit (IntLit (2 ^ n))) (cake_int_of_bool (Ast.Var (Short (''b'' @ show n))))) [0..<8]"

definition cake_int_of_byte :: "exp" where
"cake_int_of_byte =
  Ast.Fun ''x'' (Ast.Mat (Ast.Var (Short ''x'')) [(pat, foldl cake_plus (Lit (IntLit 0)) summands)])"

end