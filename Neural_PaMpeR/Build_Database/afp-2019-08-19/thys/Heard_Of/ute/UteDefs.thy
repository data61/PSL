theory UteDefs
imports "../HOModel"
begin

section \<open>Verification of the \ute{} Consensus Algorithm\<close>

text \<open>
  Algorithm \ute{} is presented in~\cite{biely:tolerating}. It is an
  uncoordinated algorithm that tolerates value (a.k.a.\ Byzantine) faults,
  and can be understood as a variant of \emph{UniformVoting}. The parameters
  $T$, $E$, and $\alpha$ appear as thresholds of the algorithm and in the
  communication predicates. Their values can be chosen within certain bounds
  in order to adapt the algorithm to the characteristics of different systems.

  We formalize in Isabelle the correctness proof of the algorithm that
  appears in~\cite{biely:tolerating}, using the framework of theory
  \<open>HOModel\<close>.
\<close>


subsection \<open>Model of the Algorithm\<close>

text \<open>
  We begin by introducing an anonymous type of processes of finite
  cardinality that will instantiate the type variable \<open>'proc\<close>
  of the generic HO model.
\<close>

typedecl Proc \<comment> \<open>the set of processes\<close>
axiomatization where Proc_finite: "OFCLASS(Proc, finite_class)"
instance Proc :: finite by (rule Proc_finite)

abbreviation
  "N \<equiv> card (UNIV::Proc set)"   \<comment> \<open>number of processes\<close>

text \<open>
  The algorithm proceeds in \emph{phases} of $2$ rounds each (we call
  \emph{steps} the individual rounds that constitute a phase).
  The following utility functions compute the phase and step of a round,
  given the round number.
\<close>

abbreviation
 "nSteps \<equiv> 2"
definition phase where "phase (r::nat) \<equiv> r div nSteps"
definition step where "step (r::nat) \<equiv> r mod nSteps"

lemma phase_zero [simp]: "phase 0 = 0"
by (simp add: phase_def)

lemma step_zero [simp]: "step 0 = 0"
by (simp add: step_def)

lemma phase_step: "(phase r * nSteps) + step r = r"
  by (auto simp add: phase_def step_def)

text \<open>The following record models the local state of a process.\<close>

record 'val pstate =
  x :: 'val                \<comment> \<open>current value held by process\<close>
  vote :: "'val option"    \<comment> \<open>value the process voted for, if any\<close>
  decide :: "'val option"  \<comment> \<open>value the process has decided on, if any\<close>

text \<open>Possible messages sent during the execution of the algorithm.\<close>

datatype 'val msg =
   Val "'val"
 | Vote "'val option"

text \<open>
  The \<open>x\<close> field of the initial state is unconstrained, all other
  fields are initialized appropriately.
\<close>

definition Ute_initState where
  "Ute_initState p st \<equiv>
   (vote st = None) \<and> (decide st = None)"

text \<open>
  The following locale introduces the parameters used for the \ute{}
  algorithm and their constraints~\cite{biely:tolerating}.
\<close>

locale ute_parameters =
  fixes \<alpha>::nat and T::nat and E::nat
  assumes majE: "2*E \<ge> N + 2*\<alpha>"
      and majT: "2*T \<ge> N + 2*\<alpha>"
      and EltN: "E < N"
      and TltN: "T < N"
begin

text \<open>Simple consequences of the above parameter constraints.\<close>

lemma alpha_lt_N: "\<alpha> < N"
using EltN majE by auto

lemma alpha_lt_T: "\<alpha> < T"
using majT alpha_lt_N by auto

lemma alpha_lt_E: "\<alpha> < E"
using majE alpha_lt_N by auto

text \<open>
  We separately define the transition predicates and the send functions
  for each step and later combine them to define the overall next-state relation.
\<close>

text \<open>
  In step 0, each process sends its current \<open>x\<close>.
  If it receives the value $v$ more than $T$ times, it votes for $v$,
  otherwise it doesn't vote.
\<close>

definition
  send0 :: "nat \<Rightarrow> Proc \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> 'val msg"
where
  "send0 r p q st \<equiv> Val (x st)"

definition
  next0 :: "nat \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> (Proc \<Rightarrow> 'val msg option) 
                \<Rightarrow> 'val pstate \<Rightarrow> bool" 
where
  "next0 r p st msgs st' \<equiv>
     (\<exists>v. card {q. msgs q = Some (Val v)} > T \<and> st' = st \<lparr> vote := Some v \<rparr>)
   \<or> \<not>(\<exists>v. card {q. msgs q = Some (Val v)} > T) \<and> st' = st \<lparr> vote := None \<rparr>"

text \<open>
  In step 1, each process sends its current \<open>vote\<close>.

  If it receives more than \<open>\<alpha>\<close> votes for a given value \<open>v\<close>,
  it sets its \<open>x\<close> field to \<open>v\<close>, else it sets \<open>x\<close> to a
  default value.

  If the process receives more than \<open>E\<close> votes for \<open>v\<close>, it decides
  \<open>v\<close>, otherwise it leaves its decision unchanged.
\<close>

definition
  send1 :: "nat \<Rightarrow> Proc \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> 'val msg" 
where
  "send1 r p q st \<equiv> Vote (vote st)"

definition
  next1 :: "nat \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> (Proc \<Rightarrow> 'val msg option) 
                \<Rightarrow> 'val pstate \<Rightarrow> bool" 
where
  "next1 r p st msgs st' \<equiv>
    ( (\<exists>v. card {q. msgs q = Some (Vote (Some v))} > \<alpha> \<and> x st' = v)
     \<or> \<not>(\<exists>v. card {q. msgs q = Some (Vote (Some v))} > \<alpha>) 
         \<and> x st' = undefined  )
  \<and> ( (\<exists>v. card {q. msgs q = Some (Vote (Some v))} > E \<and> decide st' = Some v)
     \<or> \<not>(\<exists>v. card {q. msgs q = Some (Vote (Some v))} > E) 
         \<and> decide st' = decide st )
  \<and> vote st' = None"

text \<open>
  The overall send function and next-state relation are simply obtained as
  the composition of the individual relations defined above.
\<close>

definition 
  Ute_sendMsg :: "nat \<Rightarrow> Proc \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> 'val msg" 
where
  "Ute_sendMsg (r::nat) \<equiv> if step r = 0 then send0 r else send1 r"

definition 
  Ute_nextState :: "nat \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> (Proc \<Rightarrow> 'val msg option)
                        \<Rightarrow> 'val pstate \<Rightarrow> bool" 
where
  "Ute_nextState r \<equiv> if step r = 0 then next0 r else next1 r"


subsection \<open>Communication Predicate for \ute{}\<close>

text \<open>
  Following~\cite{biely:tolerating}, we now define the communication predicate
  for the \ute{} algorithm to be correct.

  The round-by-round predicate stipulates the following conditions:
  \begin{itemize}
  \item no process may receive more than \<open>\<alpha>\<close> corrupted messages, and
  \item every process should receive more than \<open>max(T, N + 2*\<alpha> - E - 1)\<close> 
    correct messages.
  \end{itemize}
  \cite{biely:tolerating} also requires that every process should receive more
  than \<open>\<alpha>\<close> correct messages, but this is implied, since \<open>T > \<alpha>\<close>
  (cf. lemma \<open>alpha_lt_T\<close>).
\<close>

definition Ute_commPerRd where
  "Ute_commPerRd HOrs SHOrs \<equiv>
   \<forall>p. card (HOrs p - SHOrs p) \<le> \<alpha>
     \<and> card (SHOrs p \<inter> HOrs p) > N + 2*\<alpha> - E - 1
     \<and> card (SHOrs p \<inter> HOrs p) > T"

text \<open>
  The global communication predicate requires there exists some phase
  \<open>\<Phi>\<close> such that:
  \begin{itemize}
  \item all HO and SHO sets of all processes are equal in the second step
    of phase \<open>\<Phi>\<close>, i.e.\ all processes receive messages from the 
    same set of processes, and none of these messages is corrupted,
  \item every process receives more than \<open>T\<close> correct messages in
    the first step of phase \<open>\<Phi>+1\<close>, and
  \item every process receives more than \<open>E\<close> correct messages in the
    second step of phase \<open>\<Phi>+1\<close>.
  \end{itemize}
  The predicate in the article~\cite{biely:tolerating} requires infinitely
  many such phases, but one is clearly enough.
\<close>

definition Ute_commGlobal where
  "Ute_commGlobal HOs SHOs \<equiv>
    \<exists>\<Phi>. (let r = Suc (nSteps*\<Phi>)
         in  (\<exists>\<pi>. \<forall>p. \<pi> = HOs r p \<and> \<pi> = SHOs r p)
           \<and> (\<forall>p. card (SHOs (Suc r) p \<inter> HOs (Suc r) p) > T)
           \<and> (\<forall>p. card (SHOs (Suc (Suc r)) p \<inter> HOs (Suc (Suc r)) p) > E))"


subsection \<open>The \ute{} Heard-Of Machine\<close>

text \<open>
  We now define the coordinated HO machine for the \ute{} algorithm
  by assembling the algorithm definition and its communication-predicate.
\<close>

definition Ute_SHOMachine where
  "Ute_SHOMachine = \<lparr>
     CinitState =  (\<lambda> p st crd. Ute_initState p st),
     sendMsg =  Ute_sendMsg,
     CnextState = (\<lambda> r p st msgs crd st'. Ute_nextState r p st msgs st'),
     SHOcommPerRd = Ute_commPerRd,
     SHOcommGlobal = Ute_commGlobal 
   \<rparr>"

abbreviation
  "Ute_M \<equiv> (Ute_SHOMachine::(Proc, 'val pstate, 'val msg) SHOMachine)"

end   \<comment> \<open>locale @{text "ute_parameters"}\<close>

end   (* theory UteDefs *)
