chapter "Code generation"

theory CakeML_Code
imports
  Evaluate_Single
  Matching
  "generated/CakeML/PrimTypes"
begin

hide_const (open) Lib.the

declare evaluate_list_eq[code_unfold]
declare fix_clock_evaluate[code_unfold]
declare fun_evaluate_equiv[code]
declare pmatch_single_equiv[code]

declare [[code abort: failwith fp64_negate fp64_sqrt fp64_sub fp64_mul fp64_div fp64_add fp64_abs]]

definition empty_ffi_state :: "unit ffi_state" where
"empty_ffi_state = initial_ffi_state (\<lambda>_ _ _ _. Oracle_fail) ()"

context begin

private definition prim_sem_res where
"prim_sem_res = Option.the (prim_sem_env empty_ffi_state)"

local_setup \<open>fn lthy =>
  let
    val thm = Code_Simp.dynamic_conv lthy @{cterm prim_sem_res}
    val (_, lthy') = Local_Theory.note ((@{binding prim_sem_res_code}, @{attributes [code]}), [thm]) lthy
  in lthy' end
\<close>

value [simp] prim_sem_res

definition prim_sem_env where "prim_sem_env = snd prim_sem_res"
definition prim_sem_state where "prim_sem_state = fst prim_sem_res"

end

export_code evaluate fun_evaluate fun_evaluate_prog prim_sem_env
  checking SML

\<comment>\<open>Test\<close>
lemma "snd (evaluate prim_sem_env prim_sem_state (Lit (IntLit 1))) = Rval (Litv (IntLit 1))"
  by simp

end