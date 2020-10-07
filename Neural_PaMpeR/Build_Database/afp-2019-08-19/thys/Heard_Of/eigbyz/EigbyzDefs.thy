theory EigbyzDefs
imports "../HOModel"
begin


section \<open>Verification of the \eigbyz{} Consensus Algorithm\<close>

text \<open>
  Lynch~\cite{lynch:distributed} presents \eigbyz{}, a version of
  the \emph{exponential information gathering} algorithm tolerating
  Byzantine faults, that works in $f$ rounds, and that was originally
  introduced in~\cite{bar-noy:shifting-gears}.

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
  The algorithm is parameterized by $f$, which represents the number of
  rounds and the height of the tree data structure (see below).
\<close>

axiomatization f::nat
where f: "f < N"
(* NB: couldn't turn this into a locale, since f is used in the typedef below *)

subsection \<open>Tree Data Structure\<close>

text \<open>
  The algorithm relies on propagating information about the initially proposed
  values among all the processes. This information is stored in trees whose
  branches are labeled by lists of (distinct) processes. For example, the
  interpretation of an entry \<open>[p,q] \<mapsto> Some v\<close> is that the current
  process heard from process \<open>q\<close> that it had heard from process \<open>p\<close>
  that its proposed value is \<open>v\<close>. The value initially proposed by the process
  itself is stored at the root of the tree.

  We introduce the type of \emph{labels}, which encapsulate lists of distinct
  process identifiers and whose length is at most \<open>f+1\<close>.
\<close>

definition "Label = {xs::Proc list. length xs \<le> Suc f \<and> distinct xs}"
typedef Label = Label
  by (auto simp: Label_def intro: exI[where x= "[]"])  \<comment> \<open>the empty list is a label\<close>

text \<open>There is a finite number of different labels.\<close>

lemma finite_Label: "finite Label"
proof -
  have "Label \<subseteq> {xs. set xs \<subseteq> (UNIV::Proc set) \<and> length xs \<le> Suc f}" 
    by (auto simp: Label_def)
  moreover
  have "finite {xs. set xs \<subseteq> (UNIV::Proc set) \<and> length xs \<le> Suc f}"
    by (rule finite_lists_length_le) auto
  ultimately
  show ?thesis by (auto elim: finite_subset)
qed

lemma finite_UNIV_Label: "finite (UNIV::Label set)"
proof -
  from finite_Label have "finite (Abs_Label ` Label)" by simp
  moreover
  {
    fix l::Label
    have "l \<in> Abs_Label ` Label"
      by (rule Abs_Label_cases) auto
  }
  hence "(UNIV::Label set) = (Abs_Label ` Label)" by auto
  ultimately show ?thesis by simp
qed

lemma finite_Label_set [iff]: "finite (S :: Label set)"
  using finite_UNIV_Label by (auto intro: finite_subset)

text \<open>Utility functions on labels.\<close>

definition root_node where
  "root_node \<equiv> Abs_Label []"

definition length_lbl where
  "length_lbl l \<equiv> length (Rep_Label l)"
(* Don't declare the following [simp] because it would then be simplified away from
   hypotheses, whereas it can be useful for arithmetic reasoning. *)
lemma length_lbl [intro]: "length_lbl l \<le> Suc f"
  unfolding length_lbl_def using Label_def Rep_Label by auto

definition is_leaf where
 "is_leaf l \<equiv> length_lbl l = Suc f"

definition last_lbl where
  "last_lbl l \<equiv> last (Rep_Label l)"

definition butlast_lbl where
  "butlast_lbl l \<equiv> Abs_Label (butlast (Rep_Label l))"

definition set_lbl where
  "set_lbl l = set (Rep_Label l)"

text \<open>
  The children of a non-leaf label are all possible extensions of that label.
\<close>
(**
definition children where
  "children t \<equiv> { s . s \<noteq> root_node \<and> t = butlast_lbl s }"
**)

definition children where
  "children l \<equiv> 
   if is_leaf l
   then {} 
   else { Abs_Label (Rep_Label l @ [p]) | p . p \<notin> set_lbl l }"


subsection \<open>Model of the Algorithm\<close>

text \<open>
  The following record models the local state of a process.
\<close>

record 'val pstate =
  vals :: "Label \<Rightarrow> 'val option"
  newvals :: "Label \<Rightarrow> 'val"
  decide :: "'val option"

text \<open>
  Initially, no values are assigned to non-root labels, and an arbitrary value
  is assigned to the root: that value is interpreted as the initial proposal of
  the process. No decision has yet been taken, and the \<open>newvals\<close> field
  is unconstrained.
\<close>

definition EIG_initState (*::"Proc \<Rightarrow> 'val pstate \<Rightarrow> bool"*) where
  "EIG_initState p st \<equiv>
     (\<forall>l. (vals st l = None) = (l \<noteq> root_node))
   \<and> decide st = None"

type_synonym 'val Msg = "Label \<Rightarrow> 'val option"

text \<open>
  At every round, every process sends its current \<open>vals\<close> tree to all processes.
  In fact, only the level of the tree corresponding to the round number
  is used (cf. definition of \<open>extend_vals\<close> below).
\<close>

definition EIG_sendMsg (*:: "nat \<Rightarrow> Proc \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> 'val Msg"*) where
  "EIG_sendMsg r p q st \<equiv> vals st"

text \<open>
  During the first \<open>f-1\<close> rounds, every process extends its
  tree \<open>vals\<close> according to the values received in the round.
  No decision is taken.
\<close>

definition extend_vals where
  "extend_vals r p st msgs st' \<equiv>
   vals st' = (\<lambda> l.
      if length_lbl l = Suc r \<and> msgs (last_lbl l) \<noteq> None
      then (the (msgs (last_lbl l))) (butlast_lbl l)
      else if length_lbl l = Suc r \<and> msgs (last_lbl l) = None then None
      else vals st l)"

definition next_main where
  "next_main r p st msgs st' \<equiv> extend_vals r p st msgs st' \<and> decide st' = None"

text \<open>
  In the final round, in addition to extending the tree as described previously,
  processes construct the tree \<open>newvals\<close>, starting
  at the leaves. The values at the leaves are copied from \<open>vals\<close>,
  except that missing values \<open>None\<close> are replaced by the default value
  \<open>undefined\<close>. Moving up, if there exists a majority value among the 
  children, it is assigned to the parent node, otherwise the parent node
  receives the default value \<open>undefined\<close>. The decision is set to the
  value computed for the root of the tree.
\<close>

fun fixupval :: "'val option \<Rightarrow> 'val" where
  "fixupval None = undefined"
| "fixupval (Some v) = v"

definition has_majority :: "'val \<Rightarrow> ('a \<Rightarrow> 'val) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "has_majority v g S \<equiv> card {e \<in> S. g e = v} > (card S) div 2"

definition check_newvals :: "'val pstate \<Rightarrow> bool" where
  "check_newvals st \<equiv>
   \<forall>l. is_leaf l \<and> newvals st l = fixupval (vals st l)
     \<or> \<not>(is_leaf l) \<and>
       ( (\<exists>w. has_majority w (newvals st) (children l) \<and> newvals st l = w)
       \<or> (\<not>(\<exists>w. has_majority w (newvals st) (children l))
             \<and> newvals st l = undefined))"

definition next_end where
  "next_end r p st msgs st' \<equiv> 
     extend_vals r p st msgs st'
   \<and> check_newvals st'
   \<and> decide st' = Some (newvals st' root_node)"

text \<open>
  The overall next-state relation is defined such that every process applies
  \<open>nextMain\<close> during rounds \<open>0\<close>, \ldots, \<open>f-1\<close>, and applies
  \<open>nextEnd\<close> during round \<open>f\<close>. After that, the algorithm terminates
  and nothing changes anymore.
\<close>
definition EIG_nextState where
  "EIG_nextState r \<equiv> 
   if r < f then next_main r
   else if r = f then next_end r
   else (\<lambda>p st msgs st'. st' = st)"


subsection \<open>Communication Predicate for \eigbyz\<close>

text \<open>
  The secure kernel \<open>SKr\<close> w.r.t. given HO and SHO collections consists
  of the process from which every process receives the correct message.
\<close>

definition SKr :: "Proc HO \<Rightarrow> Proc HO \<Rightarrow> Proc set" where
  "SKr HO SHO \<equiv> { q . \<forall>p. q \<in> HO p \<inter> SHO p}"

text \<open>
  The secure kernel \<open>SK\<close> of an entire execution (i.e., for sequences of
  HO and SHO collections) is the intersection of the secure kernels for
  all rounds. Obviously, only the first \<open>f\<close> rounds really matter,
  since the algorithm terminates after that.
\<close>

definition SK :: "(nat \<Rightarrow> Proc HO) \<Rightarrow> (nat \<Rightarrow> Proc HO) \<Rightarrow> Proc set" where
  "SK HOs SHOs \<equiv> {q. \<forall>r. q \<in> SKr (HOs r) (SHOs r)}"

text \<open>
  The round-by-round predicate requires that the secure kernel at every round
  contains more than \<open>(N+f) div 2\<close> processes.
\<close>

definition EIG_commPerRd where
  "EIG_commPerRd HO SHO \<equiv> card (SKr HO SHO) > (N + f) div 2"

text \<open>
  The global predicate requires that the secure kernel for the entire
  execution contains at least \<open>N-f\<close> processes. Messages from these
  processes are always correctly received by all processes.
\<close>

definition EIG_commGlobal where
  "EIG_commGlobal HOs SHOs \<equiv> card (SK HOs SHOs) \<ge> N - f"

text \<open>
  The above communication predicates differ from Lynch's presentation of
  \eigbyz{}. In fact, the algorithm was originally designed for synchronous
  systems with reliable links and at most \<open>f\<close> faulty processes.
  In such a system, every process receives the correct message from at least
  the non-faulty processes at every round, and therefore the global predicate
  \<open>EIG_commGlobal\<close> is satisfied. The standard correctness
  proof assumes that $N>3f$, and therefore $N - f > (N + f) \div 2$.
  Since moreover, for any $r$, we obviously have
  \[
   \bigg(\bigcap_{p \in \Pi, r' \in \nat}\!\!\!\! SHO(p,r')\bigg)
   \ \subseteq\ \bigg(\bigcap_{p \in \Pi} SHO(p,r)\bigg),
  \]
  it follows that any execution of \eigbyz{} where $N>3f$ also satisfies
  \<open>EIG_commPerRd\<close> at any round. The standard correctness hypotheses thus imply
  our communication predicates.

  However, our proof shows that \eigbyz{} can indeed tolerate more
  transient faults than the standard bound can express. For example, consider the
  case where $N=5$ and $f=2$. Our predicates are satisfied in
  executions where two processes exhibit transient faults, but never fail
  simultaneously. Indeed, in such an execution, every process receives four
  correct messages at every round, hence \<open>EIG_commPerRd\<close> always holds.
  Also, \<open>EIG_commGlobal\<close> is satisfied because there are
  three processes from which every process receives the correct messages at all
  rounds. By our correctness proof, it follows that $EIGByz_f$ then
  achieves Consensus, unlike what one could expect from the standard correctness
  predicate. This observation underlines the interest of expressing assumptions
  about transient faults, as in the HO model.
\<close>


subsection \<open>The \eigbyz{} Heard-Of Machine\<close>

text \<open>
  We now define the non-coordinated SHO machine for \eigbyz{} by assembling
  the algorithm definition and its communication-predicate.
\<close>

definition EIG_SHOMachine where
  "EIG_SHOMachine = \<lparr>
    CinitState =  (\<lambda> p st crd. EIG_initState p st),
    sendMsg =  EIG_sendMsg,
    CnextState = (\<lambda> r p st msgs crd st'. EIG_nextState r p st msgs st'),
    SHOcommPerRd = EIG_commPerRd,
    SHOcommGlobal = EIG_commGlobal 
   \<rparr>"

abbreviation "EIG_M \<equiv> (EIG_SHOMachine::(Proc, 'val pstate, 'val Msg) SHOMachine)"

end  (* theory EIGbyzDefs *)
