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
imports AExp
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

lemma exec_append[simp]:
  "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
apply(induction is1 arbitrary: stk)
apply (auto)
done

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
