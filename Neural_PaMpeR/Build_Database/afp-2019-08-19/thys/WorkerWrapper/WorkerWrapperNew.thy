(*<*)
(*
 * The worker/wrapper transformation, following Gill and Hutton.
 * (C)opyright 2009-2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory WorkerWrapperNew
imports
  HOLCF
  FixedPointTheorems
  WorkerWrapper
begin

(*>*)
section\<open>A totally-correct fusion rule\<close>

text\<open>
\label{sec:ww-fixed}

We now show that a termination-preserving worker/wrapper fusion rule
can be obtained by requiring @{term "unwrap"} to be strict. (As we
observed earlier, @{term "wrap"} must always be strict due to the
assumption that \<open>wrap oo unwrap = ID\<close>.)

Our first result shows that a combined worker/wrapper transformation
and fusion rule is sound, using the assumptions of \<open>worker_wrapper_id\<close> and the ubiquitous \<open>lfp_fusion\<close> rule.

\<close>

lemma worker_wrapper_fusion_new:
  fixes wrap :: "'b::pcpo \<rightarrow> 'a::pcpo"
  fixes unwrap :: "'a \<rightarrow> 'b"
  fixes body' :: "'b \<rightarrow> 'b"
  assumes wrap_unwrap: "wrap oo unwrap = (ID :: 'a \<rightarrow> 'a)"
  assumes unwrap_strict: "unwrap\<cdot>\<bottom> = \<bottom>"
  assumes body_body': "unwrap oo body oo wrap = body' oo (unwrap oo wrap)"
  shows "fix\<cdot>body = wrap\<cdot>(fix\<cdot>body')"
proof -
  from body_body'
  have "unwrap oo body oo (wrap oo unwrap) = (body' oo unwrap oo (wrap oo unwrap))"
    by (simp add: assoc_oo)
  with wrap_unwrap have "unwrap oo body = body' oo unwrap"
    by simp
  with unwrap_strict have "unwrap\<cdot>(fix\<cdot>body) = fix\<cdot>body'"
    by (rule lfp_fusion)
  hence "(wrap oo unwrap)\<cdot>(fix\<cdot>body) = wrap\<cdot>(fix\<cdot>body')"
    by simp
  with wrap_unwrap show ?thesis by simp
qed

text\<open>

We can also show a more general result which allows fusion to be
optionally performed on a per-recursive-call basis using
\texttt{parallel\_fix\_ind}:

\<close>

lemma worker_wrapper_fusion_new_general:
  fixes wrap :: "'b::pcpo \<rightarrow> 'a::pcpo"
  fixes unwrap :: "'a \<rightarrow> 'b"
  assumes wrap_unwrap: "wrap oo unwrap = (ID :: 'a \<rightarrow> 'a)"
  assumes unwrap_strict: "unwrap\<cdot>\<bottom> = \<bottom>"
  assumes body_body': "\<And>r. (unwrap oo wrap)\<cdot>r = r
                        \<Longrightarrow> (unwrap oo body oo wrap)\<cdot>r = body'\<cdot>r"
  shows "fix\<cdot>body = wrap\<cdot>(fix\<cdot>body')"
proof -
  let ?P = "\<lambda>(x, y). x = y \<and> unwrap\<cdot>(wrap\<cdot>x) = x"
  have "?P (fix\<cdot>(unwrap oo body oo wrap), (fix\<cdot>body'))"
  proof(induct rule: parallel_fix_ind)
    case 2 with retraction_strict unwrap_strict wrap_unwrap show "?P (\<bottom>, \<bottom>)"
      by (bestsimp simp add: cfun_eq_iff)
    case (3 x y)
    hence xy: "x = y" and unwrap_wrap: "unwrap\<cdot>(wrap\<cdot>x) = x" by auto
    from body_body' xy unwrap_wrap
    have "(unwrap oo body oo wrap)\<cdot>x = body'\<cdot>y"
      by simp
    moreover
    from wrap_unwrap
    have "unwrap\<cdot>(wrap\<cdot>((unwrap oo body oo wrap)\<cdot>x)) = (unwrap oo body oo wrap)\<cdot>x"
      by (simp add: cfun_eq_iff)
    ultimately show ?case by simp
  qed simp
  thus ?thesis
    using worker_wrapper_id[OF wrap_unwrap refl] by simp
qed

text\<open>

This justifies the syntactically-oriented rules shown in
Figure~\ref{fig:wwc2}; note the scoping of the fusion rule.

Those familiar with the ``bananas'' work of \citet*{barbed-wire:1991}
will not be surprised that adding a strictness assumption justifies an
equational fusion rule.

\begin{figure}[tb]
 \begin{center}
  \fbox{\parbox{0.96\textwidth}{For a recursive definition @{haskell "comp =
      body"} of type @{haskell "A"} and a pair of functions @{haskell "wrap :: B \\to A"}
      and @{haskell "unwrap :: A \\to B"} where @{haskell "wrap \\circ unwrap = id_A"} and
      @{haskell "unwrap\\ \\bot = \\bot"}, define:

      \parbox{0.35\textwidth}{\begin{haskell}
        comp & = wrap\ work\\
        work & = unwrap\ (body[wrap\ work / comp])
      \end{haskell}}\hfill \textsf{(the worker/wrapper transformation)}

    In the scope of @{haskell "work"}, the following rewrite is admissable:

    \parbox{0.35\textwidth}{\begin{haskell}
        unwrap\ (wrap\ work) \Longrightarrow work
      \end{haskell}}\hfill \textsf{(worker/wrapper fusion)}}}%
 \end{center}%
\caption{The syntactic worker/wrapper transformation and fusion rule.}\label{fig:wwc2}
\end{figure}

\<close>

(*<*)
end
(*>*)
