theory Tracing
  imports
    "../heap_monad/Heap_Main"
    "HOL-Library.Code_Target_Numeral"
    Show.Show_Instances
begin

text \<open>NB:
  A more complete solution could be built by using the following entry:
  \<^url>\<open>https://www.isa-afp.org/entries/Show.html\<close>.
\<close>

definition writeln :: "String.literal \<Rightarrow> unit" where
  "writeln = (\<lambda> s. ())"

code_printing
  constant writeln \<rightharpoonup> (SML) "writeln _"

definition trace where
  "trace s x = (let a = writeln s in x)"

lemma trace_alt_def[simp]:
  "trace s x = (\<lambda> _. x) (writeln s)"
  unfolding trace_def by simp

definition (in heap_mem_defs) checkmem_trace ::
  "('k \<Rightarrow> String.literal) \<Rightarrow> 'k \<Rightarrow> (unit \<Rightarrow> 'v Heap) \<Rightarrow> 'v Heap"
  where
  "checkmem_trace trace_key param calc \<equiv>
    Heap_Monad.bind (lookup param) (\<lambda> x.
    case x of
      Some x \<Rightarrow> trace (STR ''Hit '' + trace_key param) (return x)
    | None \<Rightarrow> trace (STR ''Miss ''  + trace_key param)
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

definition nat_to_string :: "nat \<Rightarrow> String.literal" where
  "nat_to_string x = String.implode (show x)"

definition nat_pair_to_string :: "nat \<times> nat \<Rightarrow> String.literal" where
  "nat_pair_to_string x = String.implode (show x)"

value "show (3 :: nat)"

paragraph \<open>Code Setup\<close>

lemmas [code] =
  heap_mem_defs.checkmem_trace_def

lemmas [code_unfold] =
  heap_mem_defs.checkmem_checkmem_trace[where trace_key = nat_to_string]
  heap_mem_defs.checkmem_checkmem_trace[where trace_key = nat_pair_to_string]

end
