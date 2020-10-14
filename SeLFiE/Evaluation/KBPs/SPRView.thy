(*<*)
theory SPRView
imports
  KBPsAuto
begin
(*>*)

subsection\<open>The Synchronous Perfect-Recall View\<close>

text\<open>

\label{sec:kbps-theory-pr-view}

The synchronous perfect-recall (SPR) view records all observations the
agent has made on a given trace. This is the canonical
full-information synchronous view; all others are functions of this
one.

Intuitively it maintains a list of all observations made on the trace,
with the length of the list recording the time:

\<close>

definition (in Environment) spr_jview :: "('a, 's, 'obs Trace) JointView" where
  "spr_jview a = tMap (envObs a)"
(*<*)

context Environment
begin

lemma spr_jview_length_eq:
  "tLength (spr_jview a t) = tLength t"
  by (simp add: spr_jview_def)

lemma spr_jview_tInit_inv[simp]:
  "spr_jview a t = tInit obs \<longleftrightarrow> (\<exists>s. t = tInit s \<and> envObs a s = obs)"
  by (cases t) (simp_all add: spr_jview_def)

lemma spr_jview_tStep_eq_inv:
  "spr_jview a t' = spr_jview a (t \<leadsto> s) \<Longrightarrow> \<exists>t'' s'. t' = t'' \<leadsto> s'"
  by (cases t') (simp_all add: spr_jview_def)

lemma spr_jview_prefix_closed[dest]:
  "spr_jview a (t \<leadsto> s) = spr_jview a (t' \<leadsto> s') \<Longrightarrow> spr_jview a t = spr_jview a t'"
  by (simp add: spr_jview_def)

end

(*>*)
text\<open>

The corresponding incremental view appends a new observation to the
existing ones:

\<close>

definition (in Environment) spr_jviewInit :: "'a \<Rightarrow> 'obs \<Rightarrow> 'obs Trace" where
  "spr_jviewInit \<equiv> \<lambda>a obs. tInit obs"

definition (in Environment)
  spr_jviewIncr :: "'a \<Rightarrow> 'obs \<Rightarrow> 'obs Trace \<Rightarrow> 'obs Trace"
where
  "spr_jviewIncr \<equiv> \<lambda>a obs' tobs. tobs \<leadsto> obs'"

sublocale Environment
        < SPR: IncrEnvironment jkbp envInit envAction envTrans envVal
                spr_jview envObs spr_jviewInit spr_jviewIncr
(*<*)
proof
  { fix a t t' assume "spr_jview a t = spr_jview a t'"
    hence "tLength t = tLength t'"
      using spr_jview_length_eq[where a=a, symmetric] by simp }
  thus "\<forall>a t t'. spr_jview a t = spr_jview a t' \<longrightarrow> tLength t = tLength t'"
    by blast
next
  show "\<forall>a s. spr_jviewInit a (envObs a s) = spr_jview a (tInit s)"
    unfolding spr_jviewInit_def by (simp add: spr_jview_def)
next
  show "\<forall>a t s. spr_jview a (t \<leadsto> s) = spr_jviewIncr a (envObs a s) (spr_jview a t)"
    unfolding spr_jviewIncr_def by (simp add: spr_jview_def)
qed

(* These need to follow the locale instantiation as we appeal to
sync. *)

lemma (in Environment) spr_tFirst[dest]:
  assumes v: "spr_jview a t = spr_jview a t'"
  shows "envObs a (tFirst t) = envObs a (tFirst t')"
  using SPR.sync[rule_format, OF v] v
  apply (induct rule: trace_induct2)
  apply (simp_all add: spr_jview_def)
  done

lemma (in Environment) spr_tLast[dest]:
  assumes v: "spr_jview a t = spr_jview a t'"
  shows "envObs a (tLast t) = envObs a (tLast t')"
  using SPR.sync[rule_format, OF v] v
  apply (induct rule: trace_induct2)
  apply (simp_all add: spr_jview_def)
  done

(*>*)

text\<open>

\citet[Theorem~5]{Ron:1996} showed that it is not the case that
finite-state implementations always exist with respect to the SPR
view, and so we consider three special cases:
\begin{itemize}

\item[\S\ref{sec:kbps-spr-single-agent}] where there is a single
agent;

\item[\S\ref{sec:kbps-theory-spr-deterministic-protocols}] when the
protocols of the agents are deterministic and communication is by
broadcast; and

\item[\S\ref{sec:kbps-theory-spr-non-deterministic-protocols}] when
the agents use non-deterministic protocols and again use broadcast to
communicate.

\end{itemize}
Note that these cases do overlap but none is wholly
contained in another.

\<close>

(*<*)
end
(*>*)
