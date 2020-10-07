(*  Title:      JinjaThreads/Execute/PCompilerRefine.thy
    Author:     Andreas Lochbihler

    Tabulation for the compiler
*)

theory PCompilerRefine
imports
  TypeRelRefine
  "../Compiler/PCompiler"
begin

subsection \<open>@{term "compP"}\<close>

text \<open>
  Applying the compiler to a tabulated program either compiles every
  method twice (once for the program itself and once for method lookup)
  or recomputes the class and method lookup tabulation from scratch.
  We follow the second approach.
\<close>

fun compP_code' :: "(cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a prog_impl' \<Rightarrow> 'b prog_impl'"
where
  "compP_code' f (P, Cs, s, F, m) = 
  (let P' = map (compC f) P
   in (P', tabulate_class P', s, F, tabulate_Method P'))"

definition compP_code :: "(cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a prog_impl \<Rightarrow> 'b prog_impl"
where "compP_code f P = ProgRefine (compP_code' f (impl_of P))"

declare compP.simps [simp del] compP.simps[symmetric, simp]

lemma compP_code_code [code abstract]:
  "impl_of (compP_code f P) = compP_code' f (impl_of P)"
apply(cases P)
apply(simp add: compP_code_def)
apply(subst ProgRefine_inverse)
apply(auto simp add: tabulate_subcls_def tabulate_sees_field_def Mapping_inject intro!: ext)
done

declare compP.simps [simp] compP.simps[symmetric, simp del]

lemma compP_program [code]:
  "compP f (program P) = program (compP_code f P)"
by(cases P)(clarsimp simp add: program_def compP_code_code)

text \<open>Merge module names to avoid cycles in module dependency\<close>

code_identifier
  code_module PCompiler \<rightharpoonup>
    (SML) PCompiler and (OCaml) PCompiler and (Haskell) PCompiler 
| code_module PCompilerRefine \<rightharpoonup>
    (SML) PCompiler and (OCaml) PCompiler and (Haskell) PCompiler 

ML_val \<open>@{code compP}\<close>

end
