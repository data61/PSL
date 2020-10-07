(*<*)
(*
 * The worker/wrapper transformation, following Gill and Hutton.
 * (C)opyright 2009-2011, Peter Gammie, peteg42 at gmail.com, commenced December 2007.
 * License: BSD
 *)

theory WorkerWrapper
imports
  HOLCF
  FixedPointTheorems
begin

(*>*)
section\<open>The transformation according to Gill and Hutton\<close>

text\<open>

\begin{figure}[tb]
 \begin{center}
  \fbox{\parbox{0.96\textwidth}{For a recursive definition @{haskell "comp =
      \\mathsf{fix}\\ body"} for some @{haskell "body :: A \\to A"} and a pair of
      functions @{haskell "wrap :: B \\to A"} and @{haskell "unwrap :: A \\to B"} where
      @{haskell "wrap \\circ unwrap = id_A"}, we have:

      \parbox{0.35\textwidth}{\begin{haskell}
        comp = wrap\ work\\
        \quad work :: B\\
        \quad work = \mathsf{fix}\ (unwrap \circ body \circ wrap)
      \end{haskell}}\hfill \textsf{(the worker/wrapper transformation)}

      Also:

      \parbox{0.35\textwidth}{\begin{haskell}
        (unwrap \circ wrap)\ work = work
      \end{haskell}}\hfill \textsf{(worker/wrapper fusion)}}}%
 \end{center}%
 \caption{The worker/wrapper transformation and fusion rule of \citet{GillHutton:2009}.}\label{fig:ww}
\end{figure}

The worker/wrapper transformation and associated fusion rule as
formalised by \citet*{GillHutton:2009} are reproduced in
Figure~\ref{fig:ww}, and the reader is referred to the original paper
for further motivation and background.

Armed with the rolling rule we can show that Gill and Hutton's
justification of the worker/wrapper transformation is sound. There is
a battery of these transformations with varying strengths of
hypothesis.

The first requires @{term "wrap oo unwrap"} to be the identity for all
values.

\<close>

lemma worker_wrapper_id:
  fixes wrap :: "'b::pcpo \<rightarrow> 'a::pcpo"
  fixes unwrap :: "'a \<rightarrow> 'b"
  assumes wrap_unwrap: "wrap oo unwrap = ID"
  assumes comp_body: "computation = fix\<cdot>body"
  shows "computation = wrap\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
proof -
  from comp_body have "computation = fix\<cdot>(ID oo body)"
    by simp
  also from wrap_unwrap have "\<dots> = fix\<cdot>(wrap oo unwrap oo body)"
    by (simp add: assoc_oo)
  also have "... = wrap\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
    using rolling_rule[where f="unwrap oo body" and g="wrap"]
    by (simp add: assoc_oo)
  finally show ?thesis .
qed

text\<open>

The second weakens this assumption by requiring that @{term "wrap oo
wrap"} only act as the identity on values in the image of @{term
"body"}.

\<close>

lemma worker_wrapper_body:
  fixes wrap :: "'b::pcpo \<rightarrow> 'a::pcpo"
  fixes unwrap :: "'a \<rightarrow> 'b"
  assumes wrap_unwrap: "wrap oo unwrap oo body = body"
  assumes comp_body: "computation = fix\<cdot>body"
  shows "computation = wrap\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
proof -
  from comp_body have "computation = fix\<cdot>(wrap oo unwrap oo body)"
    using wrap_unwrap by (simp add: assoc_oo wrap_unwrap)
  also have "... = wrap\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
    using rolling_rule[where f="unwrap oo body" and g="wrap"]
    by (simp add: assoc_oo)
  finally show ?thesis .
qed

text\<open>

This is particularly useful when the computation being transformed is
strict in its argument.

Finally we can allow the identity to take the full recursive context
into account. This rule was described by Gill and Hutton but not used.

\<close>

lemma worker_wrapper_fix:
  fixes wrap :: "'b::pcpo \<rightarrow> 'a::pcpo"
  fixes unwrap :: "'a \<rightarrow> 'b"
  assumes wrap_unwrap: "fix\<cdot>(wrap oo unwrap oo body) = fix\<cdot>body"
  assumes comp_body: "computation = fix\<cdot>body"
  shows "computation = wrap\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
proof -
  from comp_body have "computation = fix\<cdot>(wrap oo unwrap oo body)"
    using wrap_unwrap by (simp add: assoc_oo wrap_unwrap)
  also have "... = wrap\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
    using rolling_rule[where f="unwrap oo body" and g="wrap"]
    by (simp add: assoc_oo)
  finally show ?thesis .
qed

text\<open>

Gill and Hutton's \<open>worker_wrapper_fusion\<close> rule is intended to
allow the transformation of @{term "(unwrap oo wrap)\<cdot>R"} to @{term
"R"} in recursive contexts, where @{term "R"} is meant to be a
self-call. Note that it assumes that the first worker/wrapper
hypothesis can be established.

\<close>

lemma worker_wrapper_fusion:
  fixes wrap :: "'b::pcpo \<rightarrow> 'a::pcpo"
  fixes unwrap :: "'a \<rightarrow> 'b"
  assumes wrap_unwrap: "wrap oo unwrap = ID"
  assumes work: "work = fix\<cdot>(unwrap oo body oo wrap)"
  shows "(unwrap oo wrap)\<cdot>work = work"
proof -
  have "(unwrap oo wrap)\<cdot>work = (unwrap oo wrap)\<cdot>(fix\<cdot>(unwrap oo body oo wrap))"
    using work by simp
  also have "\<dots> = (unwrap oo wrap)\<cdot>(fix\<cdot>(unwrap oo body oo wrap oo unwrap oo wrap))"
    using wrap_unwrap by (simp add: assoc_oo)
  also have "\<dots> = fix\<cdot>(unwrap oo wrap oo unwrap oo body oo wrap)"
    using rolling_rule[where f="unwrap oo body oo wrap" and g="unwrap oo wrap"]
    by (simp add: assoc_oo)
  also have "\<dots> = fix\<cdot>(unwrap oo body oo wrap)"
    using wrap_unwrap by (simp add: assoc_oo)
  finally show ?thesis using work by simp
qed

text\<open>

The following sections show that this rule only preserves partial
correctness. This is because Gill and Hutton apply it in the context
of the fold/unfold program transformation framework of
\citet*{BurstallDarlington:1977}, which need not preserve termination.
We show that the fusion rule does in fact require extra conditions to
be totally correct and propose one such sufficient condition.


\<close>
(*<*)

end
(*>*)
