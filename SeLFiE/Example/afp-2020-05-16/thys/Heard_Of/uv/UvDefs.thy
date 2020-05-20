theory UvDefs
imports "../HOModel"
begin

section \<open>Verification of the \emph{UniformVoting} Consensus Algorithm\<close>

text \<open>
  Algorithm \emph{UniformVoting} is presented in~\cite{charron:heardof}.
  It can be considered as a deterministic version of Ben-Or's well-known 
  probabilistic Consensus algorithm~\cite{ben-or:advantage}. We formalize
  in Isabelle the correctness proof given in~\cite{charron:heardof},
  using the framework of theory \<open>HOModel\<close>.
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

abbreviation "nSteps \<equiv> 2"

definition phase where "phase (r::nat) \<equiv> r div nSteps"

definition step where "step (r::nat) \<equiv> r mod nSteps"

text \<open>
  The following record models the local state of a process.
\<close>

record 'val pstate =
  x :: 'val                \<comment> \<open>current value held by process\<close>
  vote :: "'val option"    \<comment> \<open>value the process voted for, if any\<close>
  decide :: "'val option"  \<comment> \<open>value the process has decided on, if any\<close>

text \<open>
  Possible messages sent during the execution of the algorithm, and characteristic
  predicates to distinguish types of messages.
\<close>

datatype 'val msg =
  Val 'val
| ValVote 'val "'val option"
| Null  \<comment> \<open>dummy message in case nothing needs to be sent\<close>

definition isValVote where "isValVote m \<equiv> \<exists>z v. m = ValVote z v"

definition isVal where "isVal m \<equiv> \<exists>v. m = Val v"

text \<open>
  Selector functions to retrieve components of messages. These functions
  have a meaningful result only when the message is of appropriate kind.
\<close>

fun getvote where
  "getvote (ValVote z v) = v"

fun getval where
  "getval (ValVote z v) = z"
| "getval (Val z) = z"


text \<open>
  The \<open>x\<close> field of the initial state is unconstrained, all other
  fields are initialized appropriately.
\<close>

definition UV_initState where
  "UV_initState p st \<equiv> (vote st = None) \<and> (decide st = None)"

text \<open>
  We separately define the transition predicates and the send functions
  for each step and later combine them to define the overall next-state relation.
\<close>

definition msgRcvd where  \<comment> \<open>processes from which some message was received\<close>
  "msgRcvd (msgs:: Proc \<rightharpoonup> 'val msg) = {q . msgs q \<noteq> None}"

definition smallestValRcvd where
  "smallestValRcvd (msgs::Proc \<rightharpoonup> ('val::linorder) msg) \<equiv>
   Min {v. \<exists>q. msgs q = Some (Val v)}"

text \<open>
  In step 0, each process sends its current \<open>x\<close> value.

  It updates its \<open>x\<close> field to the smallest value it has received.
  If the process has received the same value \<open>v\<close> from all processes
  from which it has heard, it updates its \<open>vote\<close> field to \<open>v\<close>.
\<close>

definition send0 where
  "send0 r p q st \<equiv> Val (x st)"

definition next0 where
  "next0 r p st (msgs::Proc \<rightharpoonup> ('val::linorder) msg) st' \<equiv>
       (\<exists>v. (\<forall>q \<in> msgRcvd msgs. msgs q = Some (Val v))
           \<and> st' = st \<lparr> vote := Some v, x := smallestValRcvd msgs \<rparr>)
    \<or> \<not>(\<exists>v. \<forall>q \<in> msgRcvd msgs. msgs q = Some (Val v))
       \<and> st' = st \<lparr> x := smallestValRcvd msgs \<rparr>"

text \<open>
  In step 1, each process sends its current \<open>x\<close> and \<open>vote\<close> values.
\<close>

definition send1 where
  "send1 r p q st \<equiv> ValVote (x st) (vote st)"

definition valVoteRcvd where
  \<comment> \<open>processes from which values and votes were received\<close>
  "valVoteRcvd (msgs :: Proc \<rightharpoonup> 'val msg) \<equiv> 
   {q . \<exists>z v. msgs q = Some (ValVote z v)}"

definition smallestValNoVoteRcvd where
  "smallestValNoVoteRcvd (msgs::Proc \<rightharpoonup> ('val::linorder) msg) \<equiv>
   Min {v. \<exists>q. msgs q = Some (ValVote v None)}"

definition someVoteRcvd where
  \<comment> \<open>set of processes from which some vote was received\<close>
  "someVoteRcvd (msgs :: Proc \<rightharpoonup> 'val msg) \<equiv>
   { q . q \<in> msgRcvd msgs \<and> isValVote (the (msgs q)) \<and> getvote (the (msgs q)) \<noteq> None }"

definition identicalVoteRcvd where
  "identicalVoteRcvd (msgs :: Proc \<rightharpoonup> 'val msg) v \<equiv>
   \<forall>q \<in> msgRcvd msgs. isValVote (the (msgs q)) \<and> getvote (the (msgs q)) = Some v"

definition x_update where
 "x_update st msgs st' \<equiv>
   (\<exists>q \<in> someVoteRcvd msgs . x st' = the (getvote (the (msgs q))))
 \<or> someVoteRcvd msgs = {} \<and> x st' = smallestValNoVoteRcvd msgs"

definition dec_update where
  "dec_update st msgs st' \<equiv>
    (\<exists>v. identicalVoteRcvd msgs v \<and> decide st' = Some v)
  \<or> \<not>(\<exists>v. identicalVoteRcvd msgs v) \<and> decide st' = decide st"

definition next1 where
  "next1 r p st msgs st' \<equiv>
     x_update st msgs st'
   \<and> dec_update st msgs st'
   \<and> vote st' = None"

text \<open>
  The overall send function and next-state relation are simply obtained as 
  the composition of the individual relations defined above.
\<close>

definition UV_sendMsg where
  "UV_sendMsg (r::nat) \<equiv> if step r = 0 then send0 r else send1 r"

definition UV_nextState where
  "UV_nextState r \<equiv> if step r = 0 then next0 r else next1 r"


subsection \<open>Communication Predicate for \emph{UniformVoting}\<close>

text \<open>
  We now define the communication predicate for the \emph{UniformVoting}
  algorithm to be correct.

  The round-by-round predicate requires that for any two processes
  there is always one process heard by both of them. In other words,
  no ``split rounds'' occur during the execution of the algorithm~\cite{charron:heardof}.
  Note that in particular, heard-of sets are never empty.
\<close>

definition UV_commPerRd where
  "UV_commPerRd HOrs \<equiv> \<forall>p q. \<exists>pq. pq \<in> HOrs p \<inter> HOrs q"

text \<open>
  The global predicate requires the existence of a (space-)uniform round
  during which the heard-of sets of all processes are equal.
  (Observe that \cite{charron:heardof} requires infinitely many uniform
  rounds, but the correctness proof uses just one such round.)
\<close>

definition UV_commGlobal where
  "UV_commGlobal HOs \<equiv> \<exists>r. \<forall>p q. HOs r p = HOs r q"


subsection \<open>The \emph{UniformVoting} Heard-Of Machine\<close>

text \<open>
  We now define the HO machine for \emph{Uniform Voting} by assembling the
  algorithm definition and its communication predicate. Notice that the
  coordinator arguments for the initialization and transition functions are
  unused since \emph{UniformVoting} is not a coordinated algorithm.
\<close>

definition UV_HOMachine where
  "UV_HOMachine = \<lparr> 
    CinitState =  (\<lambda>p st crd. UV_initState p st),
    sendMsg =  UV_sendMsg,
    CnextState = (\<lambda>r p st msgs crd st'. UV_nextState r p st msgs st'),
    HOcommPerRd = UV_commPerRd,
    HOcommGlobal = UV_commGlobal
  \<rparr>"

abbreviation
  "UV_M \<equiv> (UV_HOMachine::(Proc, 'val::linorder pstate, 'val msg) HOMachine)"

end
