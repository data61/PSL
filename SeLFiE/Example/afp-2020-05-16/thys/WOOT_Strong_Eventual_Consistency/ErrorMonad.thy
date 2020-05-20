section \<open>Preliminary Notes\<close>

subsection \<open>Algorithms in Isabelle\<close>
theory ErrorMonad
  imports
    "Certification_Monads.Error_Monad"
begin

text \<open>\noindent Isabelle's functions are mathematical functions and not necessarily algorithms. For
  example, it is possible to define a non-constructible function:\<close>

fun non_constructible_function where
  "non_constructible_function f = (if (\<exists>n. f n = 0) then 1 else 0)"

text \<open>\noindent and even prove properties of them, like for example:

  \begin{center}
  @{lemma "non_constructible_function (\<lambda>x. (Suc 0)) = (0 :: nat)" by auto}
  \end{center}

  In addition to that, some native functions in Isabelle are under-defined, e.g.,
  @{term "[] ! 1"}. But it is still possible to show lemmas about these undefined values, e.g.:
  @{lemma "[] ! 1 = [a,b] ! 3" by simp}.
  While it is possible to define a notion of algorithm in Isabelle~\cite{klein2018java}, we think
  that this is not necessary for the purpose of this formalization, since the reader needs to verify
  that the formalized functions correctly model the algorithms described by
  Oster et al.~\cite{oster2006data} anyway.
  However, we show that Isabelle can generate code for the functions, indicating that
  non-constructible terms are not being used within the algorithms.\<close>

type_synonym error = String.literal

fun assert :: "bool \<Rightarrow> error + unit"
  where
    "assert False = error (STR ''Assertion failed.'')" |
    "assert True = return ()"

fun fromSingleton :: "'a list \<Rightarrow> error + 'a"
  where
    "fromSingleton [] = error (STR ''Expected list of length 1'')" |
    "fromSingleton (x # []) = return x" |
    "fromSingleton (x # y # ys) = error (STR ''Expected list of length 1'')"

text \<open>Moreover, we use the error monad---modelled using the @{type sum} type---and
  build wrappers around partially defined Isabelle functions such that the
  evaluation of undefined terms and violation of invariants expected by the
  algorithms result in error values.

  We are able to show that all operations succeed without reaching unexpected states during the
  execution of the framework.\<close>

end
