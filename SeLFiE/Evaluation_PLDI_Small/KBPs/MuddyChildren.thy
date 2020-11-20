(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory MuddyChildren
imports ClockView SPRViewDet
begin
(*>*)

subsection\<open>The Muddy Children\<close>

text\<open>

\label{sec:kbps-theory-mc}

Our first example of a multi-agent broadcast scenario is the classic
muddy children puzzle, one of a class of such puzzles that exemplify
non-obvious reasoning about mutual states of knowledge. It goes as
follows \citep[\S1.1, Example~7.2.5]{FHMV:1995}:
\begin{quotation}

  $N$ children are playing together, $k$ of whom get mud on their
  foreheads. Each can see the mud on the others' foreheads but not
  their own.

  A parental figure appears and says ``At least one of you has mud on your
  forehead.'', expressing something already known to each of them if $k >
  1$.

  The parental figure then asks ``Does any of you know whether you have mud
  on your own forehead?'' over and over.

  Assuming the children are perceptive, intelligent, truthful and they
  answer simultaneously, what will happen?
\end{quotation}
This puzzle relies essentially on \emph{synchronous public broadcasts}
making particular facts \emph{common knowledge}, and that agents are
capable of the requisite logical inference.

As the mother has complete knowledge of the situation, we integrate
her behaviour into the environment. Each agent $\mbox{child}_i$
reasons with the following KBP:
\begin{center}
  \begin{tabular}{lll}
    $\mathbf{do}$\\
     & $\gcalt\ \hat{\mathbf{K}}_{\mbox{child}_i} \mbox{muddy}_i$ & $\<open>\<rightarrow>\<close>$ Say ``I know if my forehead is muddy''\\
     & $\gcalt\ \<open>\<not>\<close>\hat{\mathbf{K}}_{\mbox{child}_i} \mbox{muddy}_i$ & $\<open>\<rightarrow>\<close>$ Say nothing\\
    $\mathbf{od}$\\
  \end{tabular}
\end{center}
where $\hat{\mathbf{K}}_a \<open>\<phi>\<close>$ abbreviates $\mathbf{K}_a
\<open>\<phi>\<close>\ \<open>\<or>\<close>\ \mathbf{K}_a \<open>\<not>\<phi>\<close>$.

As this protocol is deterministic, we use the SPR algorithm of
\S\ref{sec:kbps-theory-spr-deterministic-protocols}.

\begin{wrapfigure}{r}{0.5\textwidth}
  \vspace{-20pt}
  \includegraphics[width=0.48\textwidth]{MC}
  \vspace{-10pt}
  \caption{The protocol of $\mbox{child}_0$.}
  \label{fig:mc}
\end{wrapfigure}

The model records a child's initial observation of the mother's
pronouncement and the muddiness of the other children in her initial
private state, and these states are not changed by @{term
"envTrans"}. The recurring common observation is all of the children's
public responses to the mother's questions. Being able to distinguish
these observations is crucial to making this a broadcast scenario.

Running the algorithm for three children and minimising using
Hopcroft's algorithm yields the automaton in Figure~\ref{fig:mc} for
$\mbox{child}_0$. The initial transitions are labelled with the
initial observation, i.e., the cleanliness ``C'' or muddiness ``M'' of
the other two children. The dashed initial transition covers the case
where everyone is clean; in the others the mother has announced that
someone is dirty. Later transitions simply record the actions
performed by each of the agents, where ``K'' is the first action in
the above KBP, and ``N'' the second. Double-circled states are those
in which $\mbox{child}_0$ knows whether she is muddy, and
single-circled where she does not.

In essence the child counts the number of muddy foreheads she sees and
waits that many rounds before announcing that she knows.

Note that a solution to this puzzle is beyond the reach of the clock
semantics as it requires (in general) remembering the sequence of
previous broadcasts of length proportional to the number of
children. We discuss this further in \S\ref{sec:kbps-muddychildren}.

\<close>
(*<*)

datatype Agent = Child0 | Child1 | Child2
datatype Proposition = Dirty Agent

datatype ChildAct = SayIKnow | SayNothing

lemma Agent_univ: "(UNIV :: Agent set) = {Child0, Child1, Child2}"
  unfolding UNIV_def
  apply auto
  apply (case_tac x)
  apply auto
  done

instance Agent :: finite
  apply intro_classes
  apply (auto iff: Agent_univ)
  done

instantiation Agent :: linorder
begin

fun
  less_Agent
where
  "less_Agent Child0 Child0 = False"
| "less_Agent Child0 _      = True"
| "less_Agent Child1 Child2 = True"
| "less_Agent Child1 _      = False"
| "less_Agent Child2 _      = False"

definition
  less_eq_Agent :: "Agent \<Rightarrow> Agent \<Rightarrow> bool"
where
  "less_eq_Agent x y \<equiv> x = y \<or> x < y"

instance
  apply intro_classes
  unfolding less_eq_Agent_def
  apply (case_tac x, case_tac y, simp_all)
  apply (case_tac y, simp_all)
  apply (case_tac y, simp_all)
  apply (case_tac x, case_tac y, case_tac z, simp_all)
  apply (case_tac x, case_tac z, simp_all)
  apply (case_tac x, case_tac y, simp_all)
  apply (case_tac y, simp_all)
  apply (case_tac x, case_tac y, simp_all)
  apply (case_tac y, simp_all)
  apply (case_tac y, simp_all)
  done
end

instantiation Agent :: enum
begin

definition
  "enum_class.enum = [Child0, Child1, Child2]"

definition
  "enum_class.enum_all P = (P Child0 \<and> P Child1 \<and> P Child2)"

definition
  "enum_class.enum_ex P = (P Child0 \<or> P Child1 \<or> P Child2)"

instance
  apply standard
  unfolding enum_Agent_def enum_all_Agent_def enum_ex_Agent_def
  by auto (case_tac x, auto)+

end

lemma Act_univ: "(UNIV :: ChildAct set) = {SayIKnow, SayNothing}"
  unfolding UNIV_def
  apply auto
  apply (case_tac x)
  apply auto
  done

instance ChildAct :: finite
  by standard (auto iff: Act_univ)

instantiation ChildAct :: enum
begin

definition
  "enum_class.enum = [SayIKnow, SayNothing]"

definition
  "enum_class.enum_all P = (P SayIKnow \<and> P SayNothing)"

definition
  "enum_class.enum_ex P = (P SayIKnow \<or> P SayNothing)"

instance
  apply standard
  unfolding enum_ChildAct_def enum_all_ChildAct_def enum_ex_ChildAct_def
  by auto (case_tac x, auto)+

end

instantiation ChildAct :: linorder
begin

fun
  less_ChildAct
where
  "less_ChildAct SayIKnow SayNothing = True"
| "less_ChildAct _ _ = False"

definition
  less_eq_ChildAct :: "ChildAct \<Rightarrow> ChildAct \<Rightarrow> bool"
where
  "less_eq_ChildAct x y \<equiv> x = y \<or> x < y"

instance
  apply intro_classes
  unfolding less_eq_ChildAct_def
  apply (case_tac x, case_tac y, simp_all)
  apply (case_tac y, simp_all)
  apply (case_tac y, simp_all)
  apply (case_tac x, case_tac y, simp_all)
  apply (case_tac y, simp_all)
  done
end

type_synonym EnvAct = "unit"
type_synonym EnvState = "(bool \<times> bool \<times> bool) \<times> (ChildAct \<times> ChildAct \<times> ChildAct)"
type_synonym AgentState = "bool \<times> bool \<times> bool"
type_synonym GlobalState = "(Agent, EnvState, AgentState) BEState"

definition "agents \<equiv> fromList [Child0, Child1, Child2]"

fun
  aChildIsDirty :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
where
  "aChildIsDirty False False False = False"
| "aChildIsDirty _ _ _ = True"

definition
  initPS :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (Agent \<times> (bool \<times> bool \<times> bool)) odlist"
where
  "initPS c0 c1 c2 \<equiv>
     let acid = aChildIsDirty c0 c1 c2
      in fromList [ (Child0, (acid, c1, c2)), (Child1, (acid, c0, c2)), (Child2, (acid, c0, c1))]"

definition
  envInit :: "GlobalState list"
where
  "envInit \<equiv>
    let bu = [False, True]
     in [ \<lparr> es = ((c0, c1, c2), (SayNothing, SayNothing, SayNothing)), ps = initPS c0 c1 c2 \<rparr> .
             c0 \<leftarrow> bu, c1 \<leftarrow> bu, c2 \<leftarrow> bu ]"

(* The environment is passive, but it still needs to do something in
   each round for the system as a whole to evolve. *)

definition
  envAction :: "GlobalState \<Rightarrow> EnvAct list"
where
  "envAction \<equiv> \<lambda>_. [()]"

(* Transitions involve broadcasting the children's private actions,
leaving their private states unchanged. *)

definition
  envTransES :: "EnvAct \<Rightarrow> (Agent \<Rightarrow> ChildAct) \<Rightarrow> EnvState \<Rightarrow> EnvState"
where
  "envTransES \<equiv> \<lambda>eAct aAct s. (fst s, aAct Child0, aAct Child1, aAct Child2)"

definition
  envTrans :: "EnvAct \<Rightarrow> (Agent \<Rightarrow> ChildAct) \<Rightarrow> GlobalState \<Rightarrow> GlobalState"
where
  "envTrans eact aact s \<equiv> s \<lparr> es := envTransES eact aact (es s) \<rparr>"

(* Common observation: the actions of the agents. *)

definition "envObsC \<equiv> snd"

definition
  envVal :: "GlobalState \<Rightarrow> Proposition \<Rightarrow> bool"
where
  "envVal \<equiv> \<lambda>s p.
     case p of Dirty a \<Rightarrow>
       (case es s of ((c0, c1, c2), _) \<Rightarrow>
         (case a of
            Child0 \<Rightarrow> c0
          | Child1 \<Rightarrow> c1
          | Child2 \<Rightarrow> c2))"

(* FIXME This is a bit grot, this definition is already made for us in the locale. *)

definition "envObs \<equiv> \<lambda>a s. (envObsC (es s), ODList.lookup (ps s) a)"

(* The KBP. Clearly subjective and deterministic. *)

abbreviation
  "Kor \<phi> \<psi> \<equiv> Knot (Kand (Knot \<phi>) (Knot \<psi>))"

definition
  jkbp :: "Agent \<Rightarrow> (Agent, Proposition, ChildAct) KBP"
where
  "jkbp a = [ \<lparr> guard = Kor (\<^bold>K\<^sub>a (Kprop (Dirty a)))
                            (\<^bold>K\<^sub>a (Knot (Kprop (Dirty a)))), action = SayIKnow \<rparr>,
              \<lparr> guard = Kand (Knot (\<^bold>K\<^sub>a (Kprop (Dirty a))))
                             (Knot (\<^bold>K\<^sub>a (Knot (Kprop (Dirty a))))), action = SayNothing \<rparr> ]"

subsubsection\<open>Locale instantiations\<close>

interpretation MC: Environment jkbp envInit envAction envTrans envVal envObs
  apply unfold_locales
  apply (auto simp: jkbp_def)
  done

subsubsection\<open>The Clock view implementation\<close>

interpretation MC_Clock:
  FiniteLinorderEnvironment jkbp envInit envAction envTrans envVal envObs agents
  apply unfold_locales
  apply (simp add: Agent_univ agents_def)
  done

definition
  mc_ClockDFS
where
  "mc_ClockDFS \<equiv> ClockAutoDFS agents jkbp envInit envAction envTrans envVal envObs"

definition
  mc_ClockAlg
where
  "mc_ClockAlg \<equiv> mkClockAuto agents jkbp envInit envAction envTrans envVal envObs"

lemma (in FiniteLinorderEnvironment)
  "MC.Clock.implements mc_ClockAlg"
  unfolding mc_ClockAlg_def by (rule MC_Clock.mkClockAuto_implements)

subsubsection\<open>The SPR view implementation\<close>

interpretation MC_SPR:
  FiniteDetBroadcastEnvironment jkbp envInit envAction envTrans envVal envObs agents envObsC
  apply unfold_locales
  prefer 3
  apply (fold envObs_def envAction_def envTrans_def)
  apply clarify
  apply (erule MC.SPR.jkbpDetI)
   apply (simp add: jkbp_def)
   apply (auto simp: jkbp_def)[1]

  unfolding envAction_def envTrans_def envObs_def agents_def
  apply (simp_all add: Agent_univ jkbp_def)

  done

definition
  mc_SPRDFS
where
  "mc_SPRDFS \<equiv> SPRDetAutoDFS agents jkbp envInit envAction envTrans envVal envObsC envObs"

definition
  mc_SPRAlg
where
  "mc_SPRAlg \<equiv> mkSPRDetAuto agents jkbp envInit envAction envTrans envVal envObsC envObs"

lemma (in FiniteDetBroadcastEnvironment)
  "MC.SPR.implements mc_SPRAlg"
  unfolding mc_SPRAlg_def by (rule MC_SPR.mkSPRDetAuto_implements)

end
(*>*)
