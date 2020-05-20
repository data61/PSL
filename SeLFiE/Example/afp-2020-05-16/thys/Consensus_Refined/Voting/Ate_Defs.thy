section \<open>The $A_{T,E}$ Algorithm\<close>

theory Ate_Defs
imports Heard_Of.HOModel "../Consensus_Types"
begin

text \<open>The contents of this file have been taken almost verbatim from the
  Heard Of Model AFP entry. The only difference is that the types have been
  changed.\<close>

subsection \<open>Model of the algorithm\<close>

text \<open>The following record models the local state of a process.\<close>

record 'val pstate =
  x :: "'val"              \<comment> \<open>current value held by process\<close>
  decide :: "'val option"  \<comment> \<open>value the process has decided on, if any\<close>

text \<open>
  The \<open>x\<close> field of the initial state is unconstrained, but no
  decision has yet been taken.
\<close>

definition Ate_initState where
  "Ate_initState p st \<equiv> (decide st = None)"

locale ate_parameters =
  fixes \<alpha>::nat and T::nat and E::nat
  assumes TNaE:"T \<ge> 2*(N + 2*\<alpha> - E)"
      and TltN:"T < N"
      and EltN:"E < N"

begin

text \<open>The following are consequences of the assumptions on the parameters.\<close>

lemma majE: "2 * (E - \<alpha>) \<ge> N"
using TNaE TltN by auto

lemma Egta: "E > \<alpha>"
using majE EltN by auto

lemma Tge2a: "T \<ge> 2 * \<alpha>"
using TNaE EltN by auto

text \<open>
  At every round, each process sends its current \<open>x\<close>.
  If it received more than \<open>T\<close> messages, it selects the smallest value
  and store it in \<open>x\<close>. As in algorithm \emph{OneThirdRule}, we
  therefore require values to be linearly ordered.

  If more than \<open>E\<close> messages holding the same value are received,
  the process decides that value.
\<close>

definition mostOftenRcvd where
  "mostOftenRcvd (msgs::process \<Rightarrow> 'val option) \<equiv>
   {v. \<forall>w. card {qq. msgs qq = Some w} \<le> card {qq. msgs qq = Some v}}"

definition 
  Ate_sendMsg :: "nat \<Rightarrow> process \<Rightarrow> process \<Rightarrow> 'val pstate \<Rightarrow> 'val"
where
  "Ate_sendMsg r p q st \<equiv> x st"

definition
  Ate_nextState :: "nat \<Rightarrow> process \<Rightarrow> ('val::linorder) pstate \<Rightarrow> (process \<Rightarrow> 'val option)
                        \<Rightarrow> 'val pstate \<Rightarrow> bool"
where
  "Ate_nextState r p st msgs st' \<equiv>
     (if card {q. msgs q \<noteq> None} > T
      then x st' = Min (mostOftenRcvd msgs)
      else x st' = x st)
   \<and> (   (\<exists>v. card {q. msgs q = Some v} > E  \<and> decide st' = Some v)
       \<or> \<not> (\<exists>v. card {q. msgs q = Some v} > E) 
         \<and> decide st' = decide st)"


subsection \<open>Communication predicate for $A_{T,E}$\<close>

definition Ate_commPerRd where
  "Ate_commPerRd HOrs SHOrs \<equiv>
   \<forall>p. card (HOrs p - SHOrs p) \<le> \<alpha>"

text \<open>
  The global communication predicate stipulates the three following
  conditions:
  \begin{itemize}
  \item for every process \<open>p\<close> there are infinitely many rounds 
    where \<open>p\<close> receives more than \<open>T\<close> messages,
  \item for every process \<open>p\<close> there are infinitely many rounds 
    where \<open>p\<close> receives more than \<open>E\<close> uncorrupted messages,
  \item and there are infinitely many rounds in which more than
    \<open>E - \<alpha>\<close> processes receive uncorrupted messages from the
    same set of processes, which contains more than \<open>T\<close> processes.
  \end{itemize}
\<close>
definition
  Ate_commGlobal where
  "Ate_commGlobal HOs SHOs \<equiv>
     (\<forall>r p. \<exists>r' > r. card (HOs r' p) > T)
   \<and> (\<forall>r p.  \<exists>r' > r. card (SHOs r' p \<inter> HOs r' p) > E)
   \<and> (\<forall>r. \<exists>r' > r. \<exists>\<pi>1 \<pi>2.
        card \<pi>1 > E - \<alpha>
      \<and> card \<pi>2 > T
      \<and> (\<forall>p \<in> \<pi>1. HOs r' p = \<pi>2 \<and> SHOs r' p \<inter> HOs r' p = \<pi>2))"

subsection \<open>The $A_{T,E}$ Heard-Of machine\<close>

text \<open>
  We now define the non-coordinated SHO machine for the Ate algorithm
  by assembling the algorithm definition and its communication-predicate.
\<close>

definition Ate_SHOMachine where
  "Ate_SHOMachine = \<lparr> 
    CinitState =  (\<lambda> p st crd. Ate_initState p (st::('val::linorder) pstate)),
    sendMsg =  Ate_sendMsg,
    CnextState = (\<lambda> r p st msgs crd st'. Ate_nextState r p st msgs st'),
    SHOcommPerRd = (Ate_commPerRd:: process HO \<Rightarrow> process HO \<Rightarrow> bool),
    SHOcommGlobal = Ate_commGlobal
   \<rparr>"

abbreviation
  "Ate_M \<equiv> (Ate_SHOMachine::(process, 'val::linorder pstate, 'val) SHOMachine)"

end   \<comment> \<open>locale @{text "ate_parameters"}\<close>

end   (* theory AteDefs *)
