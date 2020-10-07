(*<*)
theory CounterExample
imports
  HOLCF
  WorkerWrapper
begin
(*>*)

subsection\<open>Worker/wrapper fusion is partially correct\<close>

text\<open>

We now examine how Gill and Hutton apply their worker/wrapper fusion
rule in the context of the fold/unfold framework.

The key step of those left implicit in the original paper is the use
of the \textsf{fold} rule to justify replacing the worker with the
fused version. Schematically, the fold/unfold framework maintains a
history of all definitions that have appeared during transformation,
and the \textsf{fold} rule treats this as a set of rewrite rules
oriented right-to-left. (The \textsf{unfold} rule treats the current
working set of definitions as rewrite rules oriented left-to-right.)
Hence as each definition @{haskell "f = body"} yields a rule of the form
@{haskell "body\\ \\Longrightarrow\\ f"}, one can always derive @{haskell "f =\\
f"}. Clearly this has dire implications for the preservation of
termination behaviour.

\citet{Tullsen:PhDThesis} in his \S3.1.2 observes that the semantic
essence of the \textsf{fold} rule is Park induction:
\begin{center}
  @{thm[mode=Rule] "fix_least"[where F=f]} {\texttt{fix\_least}}
\end{center}
viz that @{haskell "f\\ x = x"} implies only the partially correct @{haskell "fix\\ f
\\sqsubseteq x"}, and not the totally correct @{haskell "fix\\ f = x"}. We use
this characterisation to show that if @{haskell "unwrap"} is non-strict
(i.e. @{haskell "unwrap \\bot \\neq \\bot"}) then there are programs where
worker/wrapper fusion as used by Gill and Hutton need only be
partially correct.

Consider the scenario described in Figure~\ref{fig:ww}. After applying
the worker/wrapper transformation, we attempt to apply fusion by
finding a residual expression @{term "body'"} such that the body of
the worker, i.e. the expression @{term "unwrap oo body oo wrap"}, can
be rewritten as @{term "body' oo unwrap oo wrap"}. Intuitively this is
the semantic form of workers where all self-calls are fusible. Our
goal is to justify redefining @{term "work"} to @{term "fix\<cdot>body'"},
i.e. to establish:
\begin{center}
  @{term "fix\<cdot>(unwrap oo body oo wrap) = fix\<cdot>body'"}
\end{center}
We show that worker/wrapper fusion as proposed by Gill and Hutton is
partially correct using Park induction:

\<close>

lemma fusion_partially_correct:
  assumes wrap_unwrap: "wrap oo unwrap = ID"
  assumes work: "work = fix\<cdot>(unwrap oo body oo wrap)"
  assumes body': "unwrap oo body oo wrap = body' oo unwrap oo wrap"
  shows "fix\<cdot>body' \<sqsubseteq> work"
proof(rule fix_least)
  have "work = (unwrap oo body oo wrap)\<cdot>work"
    using work by (simp add: fix_eq[symmetric])
  also have "... = (body' oo unwrap oo wrap)\<cdot>work"
    using body' by simp
  also have "... = (body' oo unwrap oo wrap)\<cdot>((unwrap oo body oo wrap)\<cdot>work)"
    using work by (simp add: fix_eq[symmetric])
  also have "... = (body' oo unwrap oo wrap oo unwrap oo body oo wrap)\<cdot>work"
    by simp
  also have "... = (body' oo unwrap oo body oo wrap)\<cdot>work"
    using wrap_unwrap by (simp add: assoc_oo)
  also have "... = body'\<cdot>work"
    using work by (simp add: fix_eq[symmetric])
  finally show "body'\<cdot>work = work" by simp
qed

text\<open>

The next section shows the converse does not obtain.

\<close>

subsection\<open>A non-strict @{term "unwrap"} may go awry\<close>

text\<open>

\label{sec:ww-counterexample}

If @{term "unwrap"} is non-strict, then it is possible that the fusion
rule proposed by Gill and Hutton does not preserve termination. To
show this we take a small artificial example. The type @{term "A"} is
not important, but we need access to a non-bottom inhabitant. The
target type @{term "B"} is the non-strict lift of @{term "A"}.

\<close>

domain A = A
domain B = B (lazy "A")

text\<open>

The functions @{term "wrap"} and @{term "unwrap"} that map between
these types are routine. Note that @{term "wrap"} is (necessarily)
strict due to the property @{thm "retraction_strict"}.

\<close>

fixrec wrap :: "B \<rightarrow> A"
where "wrap\<cdot>(B\<cdot>a) = a"

(*<*)
lemma wrap_strict[simp]: "wrap\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp
(*>*)

fixrec unwrap :: "A \<rightarrow> B"
where "unwrap = B"

text\<open>

Discharging the worker/wrapper hypothesis is similarly routine.

\<close>

lemma wrap_unwrap: "wrap oo unwrap = ID"
  by (simp add: cfun_eq_iff)

text\<open>

The candidate computation we transform can be any that uses the
recursion parameter @{term "r"} non-strictly. The following is
especially trivial.

\<close>

fixrec body :: "A \<rightarrow> A"
where "body\<cdot>r = A"

text\<open>

The wrinkle is that the transformed worker can be strict in the
recursion parameter @{term "r"}, as @{term "unwrap"} always lifts it.

\<close>

fixrec body' :: "B \<rightarrow> B"
where "body'\<cdot>(B\<cdot>a) = B\<cdot>A"
(*<*)

lemma body'_strict[simp]: "body'\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

(*>*)
text\<open>

As explained above, we set up the fusion opportunity:

\<close>

lemma body_body': "unwrap oo body oo wrap = body' oo unwrap oo wrap"
  by (simp add: cfun_eq_iff)

text\<open>

This result depends crucially on @{term "unwrap"} being non-strict.

Our earlier result shows that the proposed transformation is partially
correct:

\<close>

lemma "fix\<cdot>body' \<sqsubseteq> fix\<cdot>(unwrap oo body oo wrap)"
  by (rule fusion_partially_correct[OF wrap_unwrap refl body_body'])

text\<open>

However it is easy to see that it is not totally correct:

\<close>

lemma "\<not> fix\<cdot>(unwrap oo body oo wrap) \<sqsubseteq> fix\<cdot>body'"
proof -
  have l: "fix\<cdot>(unwrap oo body oo wrap) = B\<cdot>A"
    by (subst fix_eq) simp
  have r: "fix\<cdot>body' = \<bottom>"
    by (simp add: fix_strict)
  from l r show ?thesis by simp
qed

text\<open>

This trick works whenever @{term "unwrap"} is not strict. In the
following section we show that requiring @{term "unwrap"} to be strict
leads to a straightforward proof of total correctness.

Note that if we have already established that @{term "wrap oo unwrap =
ID"}, then making @{term "unwrap"} strict preserves this equation:

\<close>

lemma
  assumes "wrap oo unwrap = ID"
  shows "wrap oo strictify\<cdot>unwrap = ID"
proof(rule cfun_eqI)
  fix x
  from assms
  show "(wrap oo strictify\<cdot>unwrap)\<cdot>x = ID\<cdot>x"
    by (cases "x = \<bottom>") (simp_all add: cfun_eq_iff retraction_strict)
qed

text\<open>

From this we conclude that the worker/wrapper transformation itself
cannot exploit any laziness in @{term "unwrap"} under the
context-insensitive assumptions of @{thm [source]
"worker_wrapper_id"}. This is not to say that other program
transformations may not be able to.

\<close>

(*<*)
lemma
  "\<not> strictify\<cdot>unwrap oo body oo wrap = body' oo strictify\<cdot>unwrap oo wrap"
  by (simp add: cfun_eq_iff exI[where x="\<bottom>"])
(*>*)

(*<*)
end
(*>*)
