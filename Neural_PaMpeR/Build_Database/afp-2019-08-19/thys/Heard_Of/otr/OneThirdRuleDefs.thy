theory OneThirdRuleDefs
imports "../HOModel"
begin

section \<open>Verification of the \emph{One-Third Rule} Consensus Algorithm\<close>

text \<open>
  We now apply the framework introduced so far to the verification of
  concrete algorithms, starting with algorithm \emph{One-Third Rule},
  which is one of the simplest algorithms presented in~\cite{charron:heardof}.
  Nevertheless, the algorithm has some interesting characteristics:
  it ensures safety (i.e., the Integrity and Agreement) properties in the
  presence of arbitrary benign faults, and if everything works perfectly,
  it terminates in just two rounds. \emph{One-Third Rule} is an uncoordinated
  algorithm tolerating benign faults, hence SHO or coordinator sets do not
  play a role in its definition.
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
  "N \<equiv> card (UNIV::Proc set)"

text \<open>
  The state of each process consists of two fields: \<open>x\<close> holds
  the current value proposed by the process and \<open>decide\<close> the
  value (if any, hence the option type) it has decided.
\<close>

record 'val pstate =
  x :: "'val"
  decide :: "'val option"

text \<open>
  The initial value of field \<open>x\<close> is unconstrained, but no decision
  has been taken initially.
\<close>

definition OTR_initState where
  "OTR_initState p st \<equiv> decide st = None"

text \<open>
  Given a vector \<open>msgs\<close> of values (possibly null) received from 
  each process, @{term "HOV msgs v"} denotes the set of processes from
  which value \<open>v\<close> was received.
\<close>

definition HOV :: "(Proc \<Rightarrow> 'val option) \<Rightarrow> 'val \<Rightarrow> Proc set" where
  "HOV msgs v \<equiv> { q . msgs q = Some v }"

text \<open>
  @{term "MFR msgs v"} (``most frequently received'') holds for
  vector \<open>msgs\<close> if no value has been received more frequently
  than \<open>v\<close>.

  Some such value always exists, since there is only a finite set of
  processes and thus a finite set of possible cardinalities of the
  sets @{term "HOV msgs v"}.
\<close>

definition MFR :: "(Proc \<Rightarrow> 'val option) \<Rightarrow> 'val \<Rightarrow> bool" where
  "MFR msgs v \<equiv> \<forall>w. card (HOV msgs w) \<le> card (HOV msgs v)"

lemma MFR_exists: "\<exists>v. MFR msgs v"
proof -
  let ?cards = "{ card (HOV msgs v) | v . True }"
  let ?mfr = "Max ?cards"
  have "\<forall>v. card (HOV msgs v) \<le> N" by (auto intro: card_mono)
  hence "?cards \<subseteq> { 0 .. N }" by auto
  hence fin: "finite ?cards" by (metis atLeast0AtMost finite_atMost finite_subset)
  hence "?mfr \<in> ?cards" by (rule Max_in) auto
  then obtain v where v: "?mfr = card (HOV msgs v)" by auto
  have "MFR msgs v"
  proof (auto simp: MFR_def)
    fix w
    from fin have "card (HOV msgs w) \<le> ?mfr" by (rule Max_ge) auto
    thus "card (HOV msgs w) \<le> card (HOV msgs v)" by (unfold v)
  qed
  thus ?thesis ..
qed

text \<open>
  Also, if a process has heard from at least one other process,
  the most frequently received values are among the received messages.
\<close>

lemma MFR_in_msgs:
  assumes HO:"HOs m p \<noteq> {}"
      and v: "MFR (HOrcvdMsgs OTR_M m p (HOs m p) (rho m)) v"
             (is "MFR ?msgs v")
  shows "\<exists>q \<in> HOs m p. v = the (?msgs q)"
proof -
  from HO obtain q where q: "q \<in> HOs m p"
    by auto
  with v have "HOV ?msgs (the (?msgs q)) \<noteq> {}"
    by (auto simp: HOV_def HOrcvdMsgs_def)
  hence HOp: "0 < card (HOV ?msgs (the (?msgs q)))"
    by auto
  also from v have "\<dots> \<le> card (HOV ?msgs v)"
    by (simp add: MFR_def)
  finally have "HOV ?msgs v \<noteq> {}"
    by auto
  thus ?thesis
    by (auto simp: HOV_def HOrcvdMsgs_def)
qed

text \<open>
  @{term "TwoThirds msgs v"} holds if value \<open>v\<close> has been
  received from more than $2/3$ of all processes.
\<close>

definition TwoThirds where
  "TwoThirds msgs v \<equiv> (2*N) div 3 < card (HOV msgs v)"

text \<open>
  The next-state relation of algorithm \emph{One-Third Rule} for every process
  is defined as follows:
  if the process has received values from more than $2/3$ of all processes,
  the \<open>x\<close> field is set to the smallest among the most frequently received
  values, and the process decides value $v$ if it received $v$ from more than
  $2/3$ of all processes. If \<open>p\<close> hasn't heard from more than $2/3$ of
  all processes, the state remains unchanged.
  (Note that \<open>Some\<close> is the constructor of the option datatype, whereas
  \<open>\<some>\<close> is Hilbert's choice operator.)
  We require the type of values to be linearly ordered so that the minimum
  is guaranteed to be well-defined.
\<close>

definition OTR_nextState where
  "OTR_nextState r p (st::('val::linorder) pstate) msgs st' \<equiv> 
   if (2*N) div 3 < card {q. msgs q \<noteq> None}
   then st' = \<lparr> x = Min {v . MFR msgs v},
          decide = (if (\<exists>v. TwoThirds msgs v)
                    then Some (\<some>v. TwoThirds msgs v)
                    else decide st) \<rparr>
   else st' = st"

text \<open>
  The message sending function is very simple: at every round, every process
  sends its current proposal (field \<open>x\<close> of its local state) to all 
  processes.
\<close>

definition OTR_sendMsg where
  "OTR_sendMsg r p q st \<equiv> x st"

subsection \<open>Communication Predicate for \emph{One-Third Rule}\<close>

text \<open>
  We now define the communication predicate for the \emph{One-Third Rule}
  algorithm to be correct.
  It requires that, infinitely often, there is a round where all processes
  receive messages from the same set \<open>\<Pi>\<close> of processes where \<open>\<Pi>\<close>
  contains more than two thirds of all processes.
  The ``per-round'' part of the communication predicate is trivial.
\<close>

definition OTR_commPerRd where
  "OTR_commPerRd HOrs \<equiv> True"

definition OTR_commGlobal where
  "OTR_commGlobal HOs \<equiv>
    \<forall>r. \<exists>r0 \<Pi>. r0 \<ge> r \<and> (\<forall>p. HOs r0 p = \<Pi>) \<and> card \<Pi> > (2*N) div 3"

subsection \<open>The \emph{One-Third Rule} Heard-Of Machine\<close>

text \<open>
  We now define the HO machine for the \emph{One-Third Rule} algorithm
  by assembling the algorithm definition and its communication-predicate.
  Because this is an uncoordinated algorithm, the \<open>crd\<close> arguments
  of the initial- and next-state predicates are unused.
\<close>

definition OTR_HOMachine where
  "OTR_HOMachine =
    \<lparr> CinitState =  (\<lambda> p st crd. OTR_initState p st),
     sendMsg =  OTR_sendMsg,
     CnextState = (\<lambda> r p st msgs crd st'. OTR_nextState r p st msgs st'),
     HOcommPerRd = OTR_commPerRd,
     HOcommGlobal = OTR_commGlobal \<rparr>"

abbreviation "OTR_M \<equiv> OTR_HOMachine::(Proc, 'val::linorder pstate, 'val) HOMachine"

end
