section \<open>Introduction\<close>

theory Lazy_Case
  imports Main
  keywords "lazify" :: thy_decl
begin

text \<open>
  Importing this theory adds a preprocessing step to the code generator: All case constants
  (and @{const HOL.If}) are replaced by ``lazy'' versions; i.e., new constants that evaluate the
  cases lazily. For example, the type of @{const case_list} is
  @{typ "'a \<Rightarrow> ('b \<Rightarrow> 'b list \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a"}. A new constant is created with the type
  @{typ "(unit \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b list \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a"}. All fully-applied occurrences of
  the standard case constants are rewritten (using the [@{attribute code_unfold}] attribute).
\<close>

text \<open>
  The motivation for doing this is twofold:

  \<^enum> Reconstructing match expressions is complicated. For existing target languages, this theory
    reduces the amount of code that has to be trusted in the code generator, because the
    transformation goes through the kernel.
  \<^enum> It lays the groundwork to support targets that do not have syntactic constructs for case
    expressions or that cannot be used for some reason, or targets where lazy evaluation of
    branching constructs is not given.
\<close>

text \<open>
  The obvious downside is that this construction will usually degrade performance of generated code.
  To some extent, an optimising compiler that performs inlining can alleviate that.
\<close>

section \<open>Setup\<close>

text \<open>@{const HOL.If} is just an alias for @{const case_bool}.\<close>
lemma [code_unfold]: "HOL.If P t f = case_bool t f P" by simp

ML_file \<open>lazy_case.ML\<close>
setup \<open>Lazy_Case.setup\<close>

end