theory Tracing
  imports
    "../heap_monad/Heap_Main"
    "HOL-Library.Code_Char"
    "HOL-Library.Code_Target_Numeral"
begin

text \<open>NB:
  There is also the more complete entry \<^url>\<open>https://www.isa-afp.org/entries/Show.html\<close>,
  but we avoid the dependency of the AFP here.
\<close>

definition writeln :: "string \<Rightarrow> unit" where
  "writeln = (\<lambda> s. ())"

code_printing
  constant writeln \<rightharpoonup> (SML) "writeln (String.implode _)"

value "writeln ''ab''"

definition trace where
  "trace s x = (let a = writeln s in x)"

lemma trace_alt_def[simp]:
  "trace s x = (\<lambda> _. x) (writeln s)"
  unfolding trace_def by simp

definition (in heap_mem_defs) checkmem_trace :: "('k \<Rightarrow> string) \<Rightarrow> 'k \<Rightarrow> (unit \<Rightarrow> 'v Heap) \<Rightarrow> 'v Heap"
  where
  "checkmem_trace trace_key param calc \<equiv>
    Heap_Monad.bind (lookup param) (\<lambda> x.
    case x of
      Some x \<Rightarrow> trace (''Hit '' @ trace_key param) (return x)
    | None \<Rightarrow> trace (''Miss ''  @ trace_key param)
       Heap_Monad.bind (calc ()) (\<lambda> x.
        Heap_Monad.bind (update param x) (\<lambda> _.
        return x
      )
    )
  )
  "

lemma (in heap_mem_defs) checkmem_checkmem_trace:
  "checkmem param calc = checkmem_trace trace_key param (\<lambda>_. calc)"
  unfolding checkmem_trace_def checkmem_def trace_alt_def ..

fun nat_to_string :: "nat \<Rightarrow> string" where
  "nat_to_string 0 = ''''" |
  "nat_to_string (Suc i) = ''I'' @ nat_to_string i"

definition nat_pair_to_string :: "nat \<times> nat \<Rightarrow> string" where
  "nat_pair_to_string = (\<lambda> (m, n). ''('' @ nat_to_string m @ '', '' @ nat_to_string n @ '')'')"

code_printing
  constant nat_to_string \<rightharpoonup> (SML) "String.explode (Int.toString (case _ of Nat x => x))"

value "nat_to_string 3"

paragraph \<open>Code Setup\<close>

lemmas [code] =
  heap_mem_defs.checkmem_trace_def

lemmas [code_unfold] =
  heap_mem_defs.checkmem_checkmem_trace[where trace_key = nat_to_string]
  heap_mem_defs.checkmem_checkmem_trace[where trace_key = nat_pair_to_string]

end