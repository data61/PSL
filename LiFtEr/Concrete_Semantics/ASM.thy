(*
 * This file "ASM.thy" was originally developed by Tobias Nipkow and Gerwin Klein
 * as Isabelle theory files accompanying their book "Concrete Semantics".
 * 
 * The PDF file of the book and the original Isabelle theory files are available 
 * at the following website:
 *   http://concrete-semantics.org/index.html
 *
 *)
section "Stack Machine and Compilation"

theory ASM
  imports AExp Induction_Demo
begin

subsection "Stack Machine"

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec1 (LOADI n) _ stk  =  n # stk" |
  "exec1 (LOAD x) s stk  =  s(x) # stk" |
  "exec1  ADD _ (j#i#stk)  =  (i + j) # stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec [] _ stk = stk" |
  "exec (i#is) s stk = exec is s (exec1 i s stk)"

value "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]"

lemma exec_append_model_prf[simp]:
  "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  apply(induct is1 arbitrary: stk)
   apply (auto)
  done

lemma exec_append_alt_proof:
  "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  apply(induct is1 s stk rule:exec.induct)
   apply (auto)
  done

ML{* (*Arguments for the induct method to attack "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)". *)
local

open LiFtEr;

in

(* Official solution by Tobias Nipkow and Gerwin Klein. *)
val model_prf_for_exec_append =
Ind_Mods
 {ons   = [Ind_On  (Print "is1")],
  arbs  = [Ind_Arb (Print "stk")],
  rules = []
  }: ind_mods;

(* Alternative solution found by Yutaka Nagashima. *)
val alt_prf_for_exec_append =
Ind_Mods
 {ons   = [Ind_On  (Print "is1"), Ind_On  (Print "s"), Ind_On  (Print "stk")],
  arbs  = [],
  rules = [Ind_Rule "ASM.exec.induct"]
  }: ind_mods;

end
*}
setup{* Apply_LiFtEr.update_ind_mod "model_prf_for_exec_append" model_prf_for_exec_append; *}
setup{* Apply_LiFtEr.update_ind_mod "alt_prf_for_exec_append"   alt_prf_for_exec_append       ; *}

(* test LiFtEr assertions *)
lemma exec_append:
  "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  assert_LiFtEr_true  example_1a model_prf_for_exec_append
  assert_LiFtEr_true  example_1a alt_prf_for_exec_append
  assert_LiFtEr_true  example_1b model_prf_for_exec_append
  assert_LiFtEr_true  example_1b alt_prf_for_exec_append
  assert_LiFtEr_true  example_2  model_prf_for_exec_append
  assert_LiFtEr_true  example_2  alt_prf_for_exec_append
  assert_LiFtEr_true  example_3  model_prf_for_exec_append
  assert_LiFtEr_true  example_3  alt_prf_for_exec_append
  assert_LiFtEr_true  example_4  model_prf_for_exec_append
  assert_LiFtEr_true  example_4  alt_prf_for_exec_append
  assert_LiFtEr_true  example_5  model_prf_for_exec_append
  assert_LiFtEr_true  example_5  alt_prf_for_exec_append
  assert_LiFtEr_true  example_6a model_prf_for_exec_append
  assert_LiFtEr_true  example_6a alt_prf_for_exec_append
  assert_LiFtEr_true  example_6b model_prf_for_exec_append
  assert_LiFtEr_true  example_6b alt_prf_for_exec_append
  oops

subsection "Compilation"

fun comp :: "aexp \<Rightarrow> instr list" where
  "comp (N n) = [LOADI n]" |
  "comp (V x) = [LOAD x]" |
  "comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

theorem exec_comp: "exec (comp a) s stk = aval a s # stk"
  apply(induction a arbitrary: stk)
    apply (auto)
  done

end
