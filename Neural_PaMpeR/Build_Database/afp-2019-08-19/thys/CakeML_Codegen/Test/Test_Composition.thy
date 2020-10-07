theory Test_Composition
imports
  "../Preproc/Eval_Instances"
  "../Compiler/Compiler"
  "../Preproc/Embed"
  Lazy_Case.Lazy_Case
begin

fun the_val where
"the_val (_, Rval val) = val"

lemma [code]: "id x = x" by simp

declassify List.append List.rev HOL.Not
embed (eval) test_code is id List_append List_rev HOL_Not .

thm test_code_def

definition "test_sem_env \<equiv> compile_to_env test_code.C_info test_code"
declare test_code.C_info_def[code]

definition "ml_app f x = Ast.App Opapp [f, x]"

definition "ml_true = term_to_exp test_code.C_info test_code \<langle>True\<rangle>"
definition "ml_false = term_to_exp test_code.C_info test_code \<langle>False\<rangle>"
definition "ml_nil = term_to_exp test_code.C_info test_code \<langle>[]\<rangle>"
definition "ml_cons x xs = ml_app (ml_app (Var (Short ''List_List_list_constructor__fun_Cons'')) x) xs"

definition exp :: exp where
"exp =
  ml_app (Var (Short ''Fun_id''))
    (ml_app (Var (Short ''Test__Composition_List__rev'')) (ml_cons ml_true (ml_cons ml_false ml_nil)))"

definition exp_expected :: exp where
"exp_expected = ml_cons ml_false (ml_cons ml_true ml_nil)"

lemma "is_cupcake_exp exp" by eval

\<comment> \<open>could also use @{const prim_sem_state} with updated clock\<close>

definition test_state :: "unit SemanticPrimitives.state" where
"test_state = empty_state \<lparr> clock := 100 \<rparr>"

definition "value = the_val (Evaluate_Single.evaluate test_sem_env test_state exp)"
definition "value_expected = the_val (Evaluate_Single.evaluate test_sem_env test_state exp_expected)"

(* takes 15 seconds *)
code_reflect Test
  functions test_sem_env "value" value_expected

ML_val\<open>Test.test_sem_env\<close>
ML_val\<open>Test.value\<close>
ML_val\<open>@{assert} (Test.value = Test.value_expected)\<close>

end
