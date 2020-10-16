(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory ClockView
imports
  KBPsAlg
  Eval
  List_local
  ODList
  Trie2
  "Transitive-Closure.Transitive_Closure_List_Impl"
  "HOL-Library.Mapping"
begin
(*>*)

subsection\<open>The Clock View\<close>

text\<open>

\label{sec:kbps-theory-clock-view}

The \emph{clock view} records the current time and the observation for
the most recent state:

\<close>

definition (in Environment)
  clock_jview :: "('a, 's, nat \<times> 'obs) JointView"
where
  "clock_jview \<equiv> \<lambda>a t. (tLength t, envObs a (tLast t))"
(*<*)

context Environment
begin

lemma clock_jview_tInit:
  "clock_jview a (tInit s) = (0, envObs a s)"
  unfolding clock_jview_def by simp

lemma clock_jview_tStep:
  "clock_jview a (t \<leadsto> s) = (Suc (tLength t), envObs a s)"
  unfolding clock_jview_def by simp

lemma clock_jview_tStepI[intro]:
  "\<lbrakk> tLength t = Suc n; envObs a (tLast t) = obs \<rbrakk>
     \<Longrightarrow> clock_jview a t = (Suc n, obs)"
  unfolding clock_jview_def by (cases t) simp_all

lemma clock_jview_inv:
  "clock_jview a t = (n, obs) \<Longrightarrow> envObs a (tLast t) = obs"
  unfolding clock_jview_def by (cases t) simp_all

lemmas clock_jview_simps =
  clock_jview_tInit
  clock_jview_tStep
  clock_jview_inv

lemma clock_jview_eq_inv[iff]:
  "clock_jview a t' = clock_jview a t
    \<longleftrightarrow> tLength t' = tLength t \<and> envObs a (tLast t') = envObs a (tLast t)"
  by (fastforce simp: clock_jview_def)

end(*>*)

text\<open>

This is the least-information synchronous view, given the requirements
of \S\ref{sec:kbps-views}. We show that finite-state implementations
exist for all environments with respect to this view as per
\citet{Ron:1996}.

The corresponding incremental view simply increments the counter
records the new observation.

\<close>

definition (in Environment)
  clock_jviewInit :: "'a \<Rightarrow> 'obs \<Rightarrow> nat \<times> 'obs"
where
  "clock_jviewInit \<equiv> \<lambda>a obs. (0, obs)"

definition (in Environment)
  clock_jviewIncr :: "'a \<Rightarrow> 'obs \<Rightarrow> nat \<times> 'obs \<Rightarrow> nat \<times> 'obs"
where
  "clock_jviewIncr \<equiv> \<lambda>a obs' (l, obs). (l + 1, obs')"

text\<open>

It is straightforward to demonstrate the assumptions of the
incremental environment locale (\S\ref{sec:kbps-environments}) with
respect to an arbitrary environment.

\<close>

sublocale Environment
        < Clock: IncrEnvironment jkbp envInit envAction envTrans envVal
                        clock_jview envObs clock_jviewInit clock_jviewIncr
(*<*)
  apply (unfold_locales)
  apply (simp_all add: clock_jviewInit_def clock_jviewIncr_def clock_jview_def)
  done

(*>*)
text\<open>

As we later show, satisfaction of a formula at a trace \<open>t \<in>
Clock.jkbpC\<^bsub>n\<^esub>\<close> is determined by the set of final states of traces in
\<open>Clock.jkbpCn\<close>:

\<close>

context Environment
begin

abbreviation clock_commonAbs :: "'s Trace \<Rightarrow> 's set" where
  "clock_commonAbs t \<equiv> tLast ` Clock.jkbpCn (tLength t)"

text\<open>

Intuitively this set contains the states that the agents commonly
consider possible at time @{term "n"}, which is sufficient for
determining knowledge as the clock view ignores paths. Therefore we
can simulate trace @{term "t"} by pairing this abstraction of @{term
"t"} with its final state:

\<close>

type_synonym (in -) 's clock_simWorlds = "'s set \<times> 's"

definition clock_sim :: "'s Trace \<Rightarrow> 's clock_simWorlds" where
  "clock_sim \<equiv> \<lambda>t. (clock_commonAbs t, tLast t)"

text\<open>

In the Kripke structure for our simulation, we relate worlds for
@{term "a"} if the sets of commonly-held states coincide, and the
observation of the final states of the traces is the
same. Propositions are evaluated at the final state.

\<close>

definition clock_simRels :: "'a \<Rightarrow> 's clock_simWorlds Relation" where
  "clock_simRels \<equiv> \<lambda>a. { ((X, s), (X', s')) |X X' s s'.
                          X = X' \<and> {s, s'} \<subseteq> X \<and> envObs a s = envObs a s' }"

definition clock_simVal :: "'s clock_simWorlds \<Rightarrow> 'p \<Rightarrow> bool" where
  "clock_simVal \<equiv> envVal \<circ> snd"

abbreviation clock_simMC :: "('a, 'p, 's clock_simWorlds) KripkeStructure" where
  "clock_simMC \<equiv> mkKripke (clock_sim ` Clock.jkbpC) clock_simRels clock_simVal"
(*<*)

lemma clock_simVal_def2[iff]: "clock_simVal (clock_sim t) = envVal (tLast t)"
  unfolding clock_sim_def clock_simVal_def by simp

lemma clock_sim_range:
  "sim_range Clock.MC clock_simMC clock_sim"
  by (rule sim_rangeI) (simp_all add: clock_sim_def)

lemma clock_simVal:
  "sim_val Clock.MC clock_simMC clock_sim"
  by (rule sim_valI) (simp add: clock_simVal_def clock_sim_def)

lemma clock_sim_f:
  "sim_f Clock.MC clock_simMC clock_sim"
apply (rule sim_fI)
apply (simp add: clock_simRels_def clock_sim_def)
apply (intro conjI)
   apply (fastforce intro!: imageI)
  apply (fastforce intro!: imageI)
 apply (fastforce dest: Clock.mkM_simps(2))
apply (rule_tac x=v in image_eqI)
 apply simp_all
done

lemma clock_sim_r:
  "sim_r Clock.MC clock_simMC clock_sim"
  apply (rule sim_rI)
  apply (clarsimp simp: clock_simRels_def clock_sim_def cong del: image_cong_simp)
  apply (rule_tac x=xa in exI)
  unfolding Clock.mkM_def
  apply auto
  done

(*>*)
text\<open>

That this is in fact a simulation
(\S\ref{sec:kripke-theory-simulations}) is entirely straightforward.

\<close>

lemma clock_sim:
  "sim Clock.MC clock_simMC clock_sim"
(*<*)
  using clock_sim_range clock_simVal clock_sim_f clock_sim_r
  unfolding sim_def
  by blast
(*>*)

end (* context Environment *)

text\<open>

The \<open>SimIncrEnvironment\<close> of
\S\ref{sec:kbps-theory-automata-env-sims} only requires that we
provide it an @{term "Environment"} and a simulation.

\<close>

sublocale Environment
        < Clock: SimIncrEnvironment jkbp envInit envAction envTrans envVal
                  clock_jview envObs clock_jviewInit clock_jviewIncr
                  clock_sim clock_simRels clock_simVal
(*<*)
  by (unfold_locales, simp_all add: clock_sim)
(*>*)

text\<open>

We next consider algorithmic issues.

\<close>

(* **************************************** *)

subsubsection\<open>Representations\<close>

text\<open>

\label{sec:kbps-theory-clock-view-rep}

We now turn to the issue of how to represent equivalence classes of
states. As these are used as map keys, it is easiest to represent them
canonically. A simple approach is to use \emph{ordered distinct lists}
of type @{typ "'a odlist"} for the sets and \emph{tries} for the
maps. Therefore we ask that environment states @{typ "'s"} belong to
the class \<open>linorder\<close> of linearly-ordered types, and moreover
that the set \<open>agents\<close> be effectively presented. We introduce a
new locale capturing these requirements:

\<close>

locale FiniteLinorderEnvironment =
  Environment jkbp envInit envAction envTrans envVal envObs
    for jkbp :: "('a::{finite, linorder}, 'p, 'aAct) JKBP"
    and envInit :: "('s::{finite, linorder}) list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"
    and envObs :: "'a \<Rightarrow> 's \<Rightarrow> 'obs"
+ fixes agents :: "'a odlist"
  assumes agents: "ODList.toSet agents = UNIV"

context FiniteLinorderEnvironment
begin

text\<open>

\label{sec:kbps-theory-clock-view-algops}

For a fixed agent @{term "a"}, we can reduce the number of worlds in
@{term "clock_simMC"} by taking its quotient with respect to the
equivalence relation for @{term "a"}. In other words, we represent a
simulated equivalence class by a pair of the set of all states
reachable at a particular time, and the subset of these that @{term
"a"} considers possible. The worlds in our representational Kripke
structure are therefore a pair of ordered, distinct lists:

\<close>

type_synonym (in -) 's clock_simWorldsRep = "'s odlist \<times> 's odlist"

text\<open>

We can readily abstract a representation to a set of simulated
equivalence classes:

\<close>

definition (in -)
  clock_simAbs :: "'s::linorder clock_simWorldsRep \<Rightarrow> 's clock_simWorlds set"
where
  "clock_simAbs X \<equiv> { (ODList.toSet (fst X), s) |s. s \<in> ODList.toSet (snd X) }"

text\<open>

Assuming @{term "X"} represents a simulated equivalence class for
@{term "t \<in> jkbpC"}, @{term "clock_simAbs X"} decomposes into these
two functions:

\<close>

definition
  agent_abs :: "'a \<Rightarrow> 's Trace \<Rightarrow> 's set"
where
  "agent_abs a t \<equiv>
     { tLast t' |t'. t' \<in> Clock.jkbpC \<and> clock_jview a t' = clock_jview a t}"

definition
  common_abs :: "'s Trace \<Rightarrow> 's set"
where
  "common_abs t \<equiv> tLast ` Clock.jkbpCn (tLength t)"
(*<*)

lemma aec_refl[intro, simp]:
  "t \<in> Clock.jkbpC \<Longrightarrow> tLast t \<in> agent_abs a t"
  unfolding agent_abs_def by auto

lemma aec_cec_subset:
  assumes tC: "t \<in> Clock.jkbpC"
      and aec: "ODList.toSet aec = agent_abs a t"
      and cec: "ODList.toSet cec = common_abs t"
  shows "x \<in> ODList.toSet aec \<Longrightarrow> x \<in> ODList.toSet cec"
  using assms
  unfolding agent_abs_def common_abs_def
  by fastforce

lemma clock_simAbs_refl:
  assumes tC: "t \<in> Clock.jkbpC"
      and ec: "clock_simAbs ec = Clock.sim_equiv_class a t"
  shows "clock_sim t \<in> clock_simAbs ec"
  using assms by simp

lemma common_abs:
  assumes tC: "t \<in> Clock.jkbpC"
  assumes ec: "clock_simAbs ec = Clock.sim_equiv_class a t"
  shows "ODList.toSet (fst ec) = common_abs t"
  using tC clock_simAbs_refl[OF tC ec]
  unfolding clock_sim_def clock_simAbs_def common_abs_def
  by (auto simp: ODList.toSet_def[symmetric])

lemma agent_abs:
  assumes tC: "t \<in> Clock.jkbpC"
  assumes ec: "clock_simAbs ec = Clock.sim_equiv_class a t"
  shows "ODList.toSet (snd ec) = agent_abs a t"
  using assms
  unfolding clock_sim_def clock_simAbs_def agent_abs_def
  apply auto
  apply (subgoal_tac "(ODList.toSet (fst ec), x) \<in> {(ODList.toSet (fst ec), s) |s. s \<in> ODList.toSet (snd ec)}")
  apply auto (* FIXME filthy *)
  done

(*>*)
text\<open>

This representation is canonical on the domain of interest (though not
in general):

\<close>

lemma clock_simAbs_inj_on:
  "inj_on clock_simAbs { x . clock_simAbs x \<in> Clock.jkbpSEC }"
(*<*)
proof(rule inj_onI)
  fix x y
  assume x: "x \<in> { x . clock_simAbs x \<in> Clock.jkbpSEC }"
     and y: "y \<in> { x . clock_simAbs x \<in> Clock.jkbpSEC }"
     and xy: "clock_simAbs x = clock_simAbs y"
  from x obtain a t
    where tC: "t \<in> Clock.jkbpC"
      and ec: "clock_simAbs x = Clock.sim_equiv_class a t"
    by auto
  from common_abs[OF tC ec] common_abs[OF tC trans[OF xy[symmetric] ec], symmetric]
  have "fst x = fst y" by (blast intro: injD[OF toSet_inj])
  moreover
  from agent_abs[OF tC ec] agent_abs[OF tC trans[OF xy[symmetric] ec], symmetric]
  have "snd x = snd y" by (blast intro: injD[OF toSet_inj])
  ultimately show "x = y" by (simp add: prod_eqI)
qed
(*>*)
text\<open>

We could further compress this representation by labelling each
element of the set of states reachable at time $n$ with a bit to
indicate whether the agent considers that state possible.  Note,
however, that the representation would be non-canonical: if \<open>(s, True)\<close> is in the representation, indicating that the agent
considers \<open>s\<close> possible, then \<open>(s, False)\<close> may or may
not be. The associated abstraction function is not injective and hence
would obfuscate the following. Repairing this would entail introducing
a new type, which would again complicate this development.



The following lemmas make use of this Kripke structure, constructed
from the set of final states of a temporal slice @{term "X"}:

\<close>

definition
  clock_repRels :: "'a \<Rightarrow> ('s \<times> 's) set"
where
  "clock_repRels \<equiv> \<lambda>a. { (s, s'). envObs a s = envObs a s' }"

abbreviation
  clock_repMC :: "'s set \<Rightarrow> ('a, 'p, 's) KripkeStructure"
where
  "clock_repMC \<equiv> \<lambda>X. mkKripke X clock_repRels envVal"
(*<*)

lemma clock_repMC_kripke[intro, simp]: "kripke (clock_repMC X)"
  by (rule kripkeI) simp

lemma clock_repMC_S5n[intro, simp]: "S5n (clock_repMC X)"
  unfolding clock_repRels_def
  by (intro S5nI equivI refl_onI symI transI) auto

(*>*)
text\<open>

We can show that this Kripke structure retains sufficient information
from @{term "Clock.MCS"} by showing simulation. This is eased by
introducing an intermediary structure that focusses on a particular
trace:

\<close>

abbreviation
  clock_jkbpCSt :: "'b Trace \<Rightarrow> 's clock_simWorlds set"
where
  "clock_jkbpCSt t \<equiv> clock_sim ` Clock.jkbpCn (tLength t)"

abbreviation
  clock_simMCt :: "'b Trace \<Rightarrow> ('a, 'p, 's clock_simWorlds) KripkeStructure"
where
  "clock_simMCt t \<equiv> mkKripke (clock_jkbpCSt t) clock_simRels clock_simVal"

definition clock_repSim :: "'s clock_simWorlds \<Rightarrow> 's" where
  "clock_repSim \<equiv> snd"
(*<*)

lemma jkbpCSt_jkbpCS_subset:
  "clock_jkbpCSt t \<subseteq> clock_sim ` Clock.jkbpC"
  by auto

lemma jkbpCSt_refl[iff]:
  "t \<in> Clock.jkbpC \<Longrightarrow> clock_sim t \<in> clock_jkbpCSt t"
  by blast

lemma fst_clock_sim[iff]:
  "t \<in> Clock.jkbpC \<Longrightarrow> fst (clock_sim t) = tLast ` Clock.jkbpCn (tLength t)"
  by (simp add: clock_sim_def)

lemma clock_repSim_simps[simp]:
  "clock_repSim ` clock_sim ` T = tLast ` T"
  "clock_repSim (clock_sim t) = tLast t"
  unfolding clock_repSim_def clock_sim_def
  by (auto intro!: image_eqI)

(*>*)
text\<open>\<close>

lemma clock_repSim:
  assumes tC: "t \<in> Clock.jkbpC"
  shows "sim (clock_simMCt t)
             ((clock_repMC \<circ> fst) (clock_sim t))
             clock_repSim"
(*<*) (is "sim ?M ?M' ?f")
proof
  show "sim_range ?M ?M' ?f"
  proof
    show "worlds ?M' = ?f ` worlds ?M"
      unfolding clock_sim_def clock_repSim_def by force
  next
    fix a
    show "relations ?M' a \<subseteq> worlds ?M' \<times> worlds ?M'"
      by (simp add: clock_sim_def clock_repSim_def)
  qed
next
  show "sim_val ?M ?M' ?f"
    by (rule, simp add: clock_sim_def clock_simVal_def clock_repSim_def split: prod.split)
next
  show "sim_f ?M ?M' ?f"
    apply rule
    unfolding clock_repRels_def clock_repSim_def clock_simRels_def
    apply (auto iff: clock_sim_def)
    done
next
  show "sim_r ?M ?M' ?f"
    apply rule
    unfolding clock_repRels_def clock_repSim_def clock_simRels_def clock_sim_def
    apply clarsimp
    done
qed

(*>*)
text\<open>

The following sections show how we satisfy the remaining requirements
of the \<open>Algorithm\<close> locale of
Figure~\ref{fig:kbps-alg-alg-locale}. Where the proof is routine, we
simply present the lemma without proof or comment.

Due to a limitation in the code generator in the present version of
Isabelle (2011), we need to define the equations we wish to execute
outside of a locale; the syntax \<open>(in -)\<close> achieves this by
making definitons at the theory top-level. We then define (but elide)
locale-local abbreviations that supply the locale-bound variables to
these definitions.

\<close>

(* **************************************** *)

subsubsection\<open>Initial states\<close>

text\<open>

The initial states of the automaton for an agent is simply @{term
"envInit"} paired with the partition of @{term "envInit"} under the
agent's observation.

\<close>

definition (in -)
  clock_simInit :: "('s::linorder) list \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'obs)
                \<Rightarrow> 'a \<Rightarrow> 'obs \<Rightarrow> 's clock_simWorldsRep"
where
  "clock_simInit envInit envObs \<equiv> \<lambda>a iobs.
    let cec = ODList.fromList envInit
     in (cec, ODList.filter (\<lambda>s. envObs a s = iobs) cec)"
(*<*)

abbreviation
  clock_simInit :: "'a \<Rightarrow> 'obs \<Rightarrow> 's clock_simWorldsRep"
where
  "clock_simInit \<equiv> ClockView.clock_simInit envInit envObs"

(*>*)
text\<open>\<close>

lemma clock_simInit:
  assumes "iobs \<in> envObs a ` set envInit"
  shows "clock_simAbs (clock_simInit a iobs)
       = clock_sim ` { t' \<in> Clock.jkbpC.
                       clock_jview a t' = clock_jviewInit a iobs }"
(*<*)
  using assms
  unfolding clock_simInit_def clock_simAbs_def clock_sim_def [abs_def] Let_def
  apply clarsimp
  apply rule
   apply clarsimp
   apply (rule_tac x="tInit s" in image_eqI)
    apply (auto simp: Set.image_def Clock.jviewInit)[2]
  apply clarsimp
  apply (case_tac xa)
   apply clarsimp
   apply rule
    apply rule
     apply clarsimp
    apply clarsimp
    apply (rule_tac x="tInit xa" in image_eqI)
    apply (auto intro!: image_eqI simp: Clock.jviewInit)
  done
(*>*)

(* **************************************** *)

subsubsection\<open>Simulated observations\<close>

text\<open>

Agent @{term "a"} will make the same observation at any of the worlds
that it considers possible, so we choose the first one in the list:

\<close>

definition (in -)
  clock_simObs :: "('a \<Rightarrow> ('s :: linorder) \<Rightarrow> 'obs)
                \<Rightarrow> 'a \<Rightarrow> 's clock_simWorldsRep \<Rightarrow> 'obs"
where
  "clock_simObs envObs \<equiv> \<lambda>a. envObs a \<circ> ODList.hd \<circ> snd"
(*<*)

abbreviation
  clock_simObs :: "'a \<Rightarrow> 's clock_simWorldsRep \<Rightarrow> 'obs"
where
  "clock_simObs \<equiv> ClockView.clock_simObs envObs"

(*>*)
text\<open>\<close>

lemma clock_simObs:
  assumes tC: "t \<in> Clock.jkbpC"
      and ec: "clock_simAbs ec = Clock.sim_equiv_class a t"
  shows "clock_simObs a ec = envObs a (tLast t)"
(*<*)
proof -
  have A: "\<forall>s \<in> set (toList (snd ec)). envObs a s = envObs a (tLast t)"
    using agent_abs[OF tC ec]
    by (clarsimp simp: agent_abs_def toSet_def)
  have B: "tLast t \<in> set (toList (snd ec))"
    using clock_simAbs_refl[OF assms]
    unfolding clock_simAbs_def clock_sim_def
    by (simp add: toSet_def snd_def)
  show ?thesis
    unfolding clock_simObs_def by (simp add: list_choose_hd[OF A B] ODList.hd_def)
qed
(*>*)

(* **************************************** *)

subsubsection\<open>Evaluation\<close>

text\<open>

\label{sec:kbps-theory-clock-view-eval}

We define our \<open>eval\<close> function in terms of @{term "evalS"},
which implements boolean logic over @{typ "'s odlist"} in the usual
way -- see \S\ref{sec:kbps-spr-single-agent-eval} for the relevant
clauses. It requires three functions specific to the representation:
one each for propositions, knowledge and common knowledge.

Propositions define subsets of the worlds considered possible:

\<close>

abbreviation (in -)
  clock_evalProp :: "(('s::linorder) \<Rightarrow> 'p \<Rightarrow> bool)
                  \<Rightarrow> 's odlist \<Rightarrow> 'p \<Rightarrow> 's odlist"
where
  "clock_evalProp envVal \<equiv> \<lambda>X p. ODList.filter (\<lambda>s. envVal s p) X"

text\<open>

The knowledge relation computes the subset of the
commonly-held-possible worlds \<open>cec\<close> that agent @{term "a"}
considers possible at world @{term "s"}:

\<close>

definition (in -)
  clock_knowledge :: "('a \<Rightarrow> ('s :: linorder) \<Rightarrow> 'obs) \<Rightarrow> 's odlist
                  \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 's odlist"
where
  "clock_knowledge envObs cec \<equiv> \<lambda>a s.
     ODList.filter (\<lambda>s'. envObs a s = envObs a s') cec"

text\<open>


Similarly the common knowledge operation computes the transitive
closure of the union of the knowledge relations for the agents \<open>as\<close>:

\<close>

definition (in -)
  clock_commonKnowledge :: "('a \<Rightarrow> ('s :: linorder) \<Rightarrow> 'obs) \<Rightarrow> 's odlist
           \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's odlist"
where
  "clock_commonKnowledge envObs cec \<equiv> \<lambda>as s.
     let r = \<lambda>a. ODList.fromList [ (s', s'') . s' \<leftarrow> toList cec, s'' \<leftarrow> toList cec,
                                   envObs a s' = envObs a s'' ];
         R = toList (ODList.big_union r as)
      in ODList.fromList (memo_list_trancl R s)"

text\<open>

The function \<open>memo_list_trancl\<close> comes from the executable
transitive closure theory of \citep{AFP:TRANCL}.

The evaluation function evaluates a subjective knowledge formula on
the representation of an equivalence class:

\<close>

definition (in -)
  eval :: "(('s :: linorder) \<Rightarrow> 'p \<Rightarrow> bool)
        \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'obs)
        \<Rightarrow> 's clock_simWorldsRep \<Rightarrow> ('a, 'p) Kform \<Rightarrow> bool"
where
  "eval envVal envObs \<equiv> \<lambda>(cec, aec). evalS (clock_evalProp envVal)
                                      (clock_knowledge envObs cec)
                                      (clock_commonKnowledge envObs cec)
                                      aec"

text\<open>

This function corresponds with the standard semantics:

\<close>
(*<*)

lemma clock_coEC_relation_image:
  "s \<in> ODList.toSet Y
    \<Longrightarrow> ODList.toSet (clock_knowledge envObs Y a s) = relations (clock_repMC (ODList.toSet Y)) a `` {s}"
  unfolding clock_knowledge_def clock_repRels_def Image_def
  by auto

lemma clock_commonKnowledge_relation_image_aux:
  "(\<Union>x\<in>set as. \<Union>a\<in>ODList.toSet Y. \<Union>aa\<in>ODList.toSet Y \<inter> {s''. envObs x a = envObs x s''}. {(a, aa)})
 = ((\<Union>a\<in>set as. {(s, s'). envObs a s = envObs a s'}) \<inter> ODList.toSet Y \<times> ODList.toSet Y)"
  by auto

lemma clock_commonKnowledge_relation_image:
  "s \<in> ODList.toSet Y
    \<Longrightarrow> ODList.toSet (clock_commonKnowledge envObs Y as s) = (\<Union>a \<in> set as. relations (clock_repMC (ODList.toSet Y)) a)\<^sup>+ `` {s}"
  unfolding clock_commonKnowledge_def clock_repRels_def Let_def
  apply (simp add: memo_list_trancl toSet_def[symmetric] Image_def clock_commonKnowledge_relation_image_aux)
  done

lemma eval_rec_models:
  assumes XY: "ODList.toSet X \<subseteq> ODList.toSet Y"
      and s: "s \<in> ODList.toSet X"
  shows "s \<in> ODList.toSet (eval_rec (clock_evalProp envVal) (clock_knowledge envObs Y) (clock_commonKnowledge envObs Y) X \<phi>)
     \<longleftrightarrow> clock_repMC (ODList.toSet Y), s \<Turnstile> \<phi>"
using XY s
proof(induct \<phi> arbitrary: X s)
  case (Kknows a' \<phi> X s)
  from \<open>s \<in> ODList.toSet X\<close> clock_coEC_relation_image[OF subsetD[OF Kknows(2) Kknows(3)], where a=a']
  show ?case
    apply simp
    apply rule
     apply (drule arg_cong[where f="ODList.toSet"])
     apply (clarsimp simp: odlist_all_iff)
     apply (cut_tac s3="w'" and X3="clock_knowledge envObs Y a' s" in Kknows.hyps)
      using Kknows(2) Kknows(3)
      apply (auto simp add: S5n_rels_closed[OF clock_repMC_S5n])[3]

    apply (clarsimp simp: toSet_eq_iff odlist_all_iff)
    apply (subst Kknows.hyps)
      using Kknows(2) Kknows(3)
      apply (auto simp add: S5n_rels_closed[OF clock_repMC_S5n])
    done
next
  case (Kcknows as \<phi> X s)
  show ?case
  proof(cases "as = Nil")
    case True with \<open>s \<in> ODList.toSet X\<close> show ?thesis by clarsimp
  next
    case False
    with \<open>s \<in> ODList.toSet X\<close> clock_commonKnowledge_relation_image[OF subsetD[OF Kcknows(2) Kcknows(3)], where as=as]
    show ?thesis
      apply simp
      apply rule
       apply (drule arg_cong[where f="ODList.toSet"])
       apply (clarsimp simp: odlist_all_iff)
       apply (cut_tac s3="w'" and X3="clock_commonKnowledge envObs Y as s" in Kcknows.hyps)
        using Kcknows(2) Kcknows(3)
        apply (auto simp add: S5n_rels_closed[OF clock_repMC_S5n])[3]
        apply (subst (asm) trancl_unfold) back back back
        apply auto[1] (* FIXME disgusting *)

      apply (clarsimp simp: toSet_eq_iff odlist_all_iff)
      apply (subst Kcknows.hyps)
       using Kcknows(2) Kcknows(3)
       apply (auto simp add: S5n_rels_closed[OF clock_repMC_S5n])
        apply (subst (asm) trancl_unfold) back back back
        apply auto[1] (* FIXME disgusting *)

      done
  qed
qed simp_all

lemma trc_aux:
  assumes tC: "t \<in> Clock.jkbpC"
      and aec: "ODList.toSet aec = agent_abs a t"
      and cec: "ODList.toSet cec = common_abs t"
  shows "ODList.toSet (big_union (clock_commonKnowledge envObs cec as) (toList aec)) \<subseteq> ODList.toSet cec"
  apply (clarsimp simp: toSet_def[symmetric])
  apply (subst (asm) clock_commonKnowledge_relation_image)
   apply (erule aec_cec_subset[OF tC aec cec])
  apply (subst (asm) trancl_unfold)
  using assms
  apply (auto simp: agent_abs_def)
  done

lemma clock_repMC_aec:
  assumes tC: "t \<in> Clock.jkbpC"
      and aec: "ODList.toSet aec = agent_abs a t"
      and cec: "ODList.toSet cec = common_abs t"
      and x: "x \<in> ODList.toSet aec"
      and xy: "(x, y) \<in> relations (clock_repMC (ODList.toSet cec)) a"
  shows "y \<in> ODList.toSet aec"
  using assms
  unfolding clock_repRels_def agent_abs_def common_abs_def
  by auto

lemma clock_repMC_cec:
  assumes tC: "t \<in> Clock.jkbpC"
      and aec: "ODList.toSet aec = agent_abs a t"
      and cec: "ODList.toSet cec = common_abs t"
      and x: "x \<in> ODList.toSet aec"
      and y: "y \<in> ODList.toSet aec"
  shows "(x, y) \<in> relations (clock_repMC (ODList.toSet cec)) a"
  using assms
  unfolding clock_repRels_def agent_abs_def common_abs_def
  by auto

lemma evalS_models:
  assumes tC: "t \<in> Clock.jkbpC"
      and aec: "ODList.toSet aec = agent_abs a t"
      and cec: "ODList.toSet cec = common_abs t"
      and subj_phi: "subjective a \<phi>"
      and s: "s \<in> ODList.toSet aec"
  shows "evalS (clock_evalProp envVal) (clock_knowledge envObs cec) (clock_commonKnowledge envObs cec) aec \<phi>
     \<longleftrightarrow> clock_repMC (ODList.toSet cec), s \<Turnstile> \<phi>" (is "?lhs \<phi> = ?rhs \<phi>")
using subj_phi s aec cec
proof(induct \<phi> rule: subjective.induct[case_names Kprop Knot Kand Kknows Kcknows])
  case (Kknows a a' \<psi>) show ?case
    apply (clarsimp simp: toSet_eq_iff)
    apply rule
     apply clarsimp
     apply (subgoal_tac "w' \<in> ODList.toSet aec")
     apply (drule_tac c="w'" in subsetD)
       apply assumption
      apply (simp add: eval_rec_models[OF subsetI[OF aec_cec_subset[OF tC aec cec]]])
     apply (rule clock_repMC_aec[OF tC Kknows(3) Kknows(4), rotated, where x=s])
       using Kknows
       apply simp
      using Kknows
      apply simp

    apply clarsimp
    apply (simp add: eval_rec_models[OF subsetI[OF aec_cec_subset[OF tC aec cec]]])
    using tC Kknows
    apply (clarsimp simp: agent_abs_def)
    apply (erule (1) ballE)
    using Kknows
    apply (cut_tac x="tLast t'" and y="tLast t'a" in clock_repMC_cec[OF tC Kknows(3) Kknows(4)])
      unfolding clock_repRels_def
      apply auto
    done
next
  case (Kcknows a as \<psi>)
  have "?lhs (Kcknows as \<psi>)
      = (\<forall>y\<in>ODList.toSet aec.
           \<forall>x\<in>(\<Union>a\<in>set as. relations (clock_repMC (ODList.toSet cec)) a)\<^sup>+ `` {y}.
              x \<in> ODList.toSet (eval_rec (clock_evalProp envVal) (clock_knowledge envObs cec) (clock_commonKnowledge envObs cec)
                       (big_union (clock_commonKnowledge envObs cec as) (toList aec)) \<psi>))"
    (* FIXME dreaming of a cong rule here. *)
    using toSet_def[symmetric]
    apply (clarsimp simp: toSet_eq_iff toSet_def[symmetric] subset_eq)
    apply (rule ball_cong[OF refl])
    apply (rule ball_cong)
    apply (subst clock_commonKnowledge_relation_image[OF aec_cec_subset[OF tC Kcknows(3) Kcknows(4)]])
    apply simp_all
    done
  also have "... = (\<forall>s\<in>ODList.toSet aec. clock_repMC (ODList.toSet cec), s \<Turnstile> Kcknows as \<psi>)"
    apply (rule ball_cong[OF refl])
    apply simp
    apply (rule ball_cong[OF refl])
    apply (subst eval_rec_models[OF trc_aux[OF tC Kcknows(3) Kcknows(4), where as=as], symmetric])
     apply (simp add: toSet_def[symmetric])
     apply (rule_tac x=y in bexI)
      apply (subst clock_commonKnowledge_relation_image[OF aec_cec_subset[OF tC Kcknows(3) Kcknows(4)]])
      apply assumption
     apply simp
     apply (rule refl)
    done
  also have "... = clock_repMC (ODList.toSet cec), s \<Turnstile> Kknows a (Kcknows as \<psi>)"
    using clock_repMC_aec[OF tC Kcknows(3) Kcknows(4) Kcknows(2)]
          clock_repMC_cec[OF tC Kcknows(3) Kcknows(4) Kcknows(2)]
    by (auto cong: ball_cong)
  also have "... = clock_repMC (ODList.toSet cec), s \<Turnstile> Kcknows as \<psi>"
    apply (rule S5n_common_knowledge_fixed_point_simpler[symmetric])
    using Kcknows
    apply (auto intro: aec_cec_subset[OF tC Kcknows(3) Kcknows(4) Kcknows(2)])
    done
  finally show ?case .
qed simp_all

(*>*)
lemma eval_models:
  assumes tC: "t \<in> Clock.jkbpC"
      and aec: "ODList.toSet aec = agent_abs a t"
      and cec: "ODList.toSet cec = common_abs t"
      and subj_phi: "subjective a \<phi>"
      and s: "s \<in> ODList.toSet aec"
  shows "eval envVal envObs (cec, aec) \<phi>
     \<longleftrightarrow> clock_repMC (ODList.toSet cec), s \<Turnstile> \<phi>"
(*<*)
  unfolding eval_def
  using evalS_models[OF tC aec cec subj_phi s]
  apply (simp add: Let_def)
  done

(*>*)

(* **************************************** *)

subsubsection\<open>Simulated actions\<close>

text\<open>

From a common equivalence class and a subjective equivalence class for
agent @{term "a"}, we can compute the actions enabled for @{term "a"}:

\<close>

definition (in -)
  clock_simAction :: "('a, 'p, 'aAct) JKBP \<Rightarrow> (('s :: linorder) \<Rightarrow> 'p \<Rightarrow> bool)
                  \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'obs)
                  \<Rightarrow> 'a \<Rightarrow> 's clock_simWorldsRep \<Rightarrow> 'aAct list"
where
  "clock_simAction jkbp envVal envObs \<equiv> \<lambda>a (Y, X).
     [ action gc. gc \<leftarrow> jkbp a, eval envVal envObs (Y, X) (guard gc) ]"
(*<*)

abbreviation
  clock_simAction :: "'a \<Rightarrow> 's clock_simWorldsRep \<Rightarrow> 'aAct list"
where
  "clock_simAction \<equiv> ClockView.clock_simAction jkbp envVal envObs"

(*>*)
text\<open>

Using the above result about evaluation, we can relate \<open>clock_simAction\<close> to @{term "jAction"}. Firstly, \<open>clock_simAction\<close> behaves the same as @{term "jAction"} using the
@{term "clock_repMC"} structure:

\<close>

lemma clock_simAction_jAction:
  assumes tC: "t \<in> Clock.jkbpC"
      and aec: "ODList.toSet aec = agent_abs a t"
      and cec: "ODList.toSet cec = common_abs t"
  shows "set (clock_simAction a (cec, aec))
       = set (jAction (clock_repMC (ODList.toSet cec)) (tLast t) a)"
(*<*)
  unfolding clock_simAction_def jAction_def
  apply clarsimp
  apply rule
   apply clarsimp
   apply (rule_tac x=xa in bexI)
    apply simp
   apply clarsimp
   apply (subst eval_models[OF tC aec cec, symmetric])
     using tC aec cec subj
     apply simp_all
  apply clarsimp
  apply (rule_tac x=xa in bexI)
   apply (rule refl)
  apply clarsimp
  apply (subst eval_models[OF tC aec cec])
    using tC aec cec subj
    apply simp_all
  done

lemma clock_submodel_aux:
  assumes tC: "t \<in> Clock.jkbpC"
      and s: "s \<in> worlds (clock_simMCt t)"
  shows "gen_model Clock.MCS s = gen_model (clock_simMCt t) s"
proof(rule gen_model_subset[where T="clock_jkbpCSt t"])
  fix a
  let ?X = "clock_sim ` Clock.jkbpCn (tLength t)"
  show "relations Clock.MCS a \<inter> ?X \<times> ?X
      = relations (clock_simMCt t) a \<inter> ?X \<times> ?X"
    by (simp add: Int_ac Int_absorb1
                  relation_mono[OF jkbpCSt_jkbpCS_subset jkbpCSt_jkbpCS_subset])
next
  let ?X = "clock_sim ` Clock.jkbpCn (tLength t)"
  from s show "(\<Union>a. relations (clock_simMCt t) a)\<^sup>* `` {s} \<subseteq> ?X"
    apply (clarsimp simp del: mkKripke_simps)
    apply (erule kripke_rels_trc_worlds)
    apply auto
    done
next
  let ?Y = "Clock.jkbpCn (tLength t)"
  let ?X = "clock_sim ` ?Y"
  from s obtain t'
    where st': "s = clock_sim t'"
      and t'C: "t' \<in> Clock.jkbpC"
      and t'O: "tLength t = tLength t'"
    by fastforce
  { fix t''
    assume tt': "(t', t'') \<in> (\<Union>a. relations Clock.MC a)\<^sup>*"
    from t'C tt' have t''C: "t'' \<in> Clock.jkbpC"
      by - (erule kripke_rels_trc_worlds, simp_all)
    from t'O tt' have t''O: "tLength t = tLength t''"
      by (simp add: Clock.sync_tLength_eq_trc)
    from t''C t''O have "t'' \<in> ?Y" by fastforce }
  hence "(\<Union>a. relations Clock.MC a)\<^sup>* `` {t'} \<subseteq> ?Y"
    by clarsimp
  hence "clock_sim ` ((\<Union>a. relations Clock.MC a)\<^sup>* `` {t'}) \<subseteq> ?X"
    by (rule image_mono)
  with st' t'C
  show "(\<Union>a. relations Clock.MCS a)\<^sup>* `` {s} \<subseteq> ?X"
    using sim_trc_commute[OF Clock.mkM_kripke clock_sim, where t=t'] by simp
qed (insert s, auto)

(*>*)
text\<open>

We can connect the agent's choice of actions on the \<open>clock_repMC\<close> structure to those on the \<open>Clock.MC\<close>
structure using our earlier results about actions being preserved by
generated models and simulations.

\<close>

lemma clock_simAction':
  assumes tC: "t \<in> Clock.jkbpC"
  assumes aec: "ODList.toSet aec = agent_abs a t"
  assumes cec: "ODList.toSet cec = common_abs t"
  shows "set (clock_simAction a (cec, aec)) = set (jAction Clock.MC t a)"
(*<*) (is "?lhs = ?rhs")
proof -
  from tC aec cec
  have "?lhs = set (jAction (clock_repMC (ODList.toSet cec)) (tLast t) a)"
    by (rule clock_simAction_jAction)
  also from tC aec cec
  have "... = set (jAction (clock_simMCt t) (clock_sim t) a)"
    by (simp add: simulation_jAction_eq[OF _ clock_repSim] common_abs_def)
  also from tC
  have "... = set (jAction Clock.MCS (clock_sim t) a)"
    using gen_model_jAction_eq[OF clock_submodel_aux[OF tC, where s="clock_sim t"], where w'="clock_sim t"]
          gen_model_world_refl[where w="clock_sim t" and M="clock_simMCt t"]
    by simp
  also from tC have "... = set (jAction Clock.MC t a)"
    by (simp add: simulation_jAction_eq[OF _ clock_sim])
  finally show ?thesis .
qed

(*>*)
text\<open>

The @{term "Algorithm"} locale requires a specialisation of this
lemma:

\<close>

lemma clock_simAction:
  assumes tC: "t \<in> Clock.jkbpC"
  assumes ec: "clock_simAbs ec = Clock.sim_equiv_class a t"
  shows "set (clock_simAction a ec) = set (jAction Clock.MC t a)"
(*<*)
  using assms clock_simAction'[OF tC, where cec="fst ec" and aec="snd ec"]
  apply (simp add: common_abs agent_abs)
  done
(*>*)

(* **************************************** *)

subsubsection\<open>Simulated transitions\<close>

text\<open>

We need to determine the image of the set of commonly-held-possible
states under the transition function, and also for the agent's
subjective equivalence class. We do this with the \<open>clock_trans\<close> function:

\<close>

definition (in -)
  clock_trans :: "('a :: linorder) odlist \<Rightarrow> ('a, 'p, 'aAct) JKBP
              \<Rightarrow> (('s :: linorder) \<Rightarrow> 'eAct list)
              \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's)
              \<Rightarrow> ('s \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'obs)
              \<Rightarrow> 's odlist \<Rightarrow> 's odlist \<Rightarrow> 's odlist"
where
  "clock_trans agents jkbp envAction envTrans envVal envObs \<equiv> \<lambda>cec X.
     ODList.fromList (concat
       [ [ envTrans eact aact s .
                     eact \<leftarrow> envAction s,
                     aact \<leftarrow> listToFuns (\<lambda>a. clock_simAction jkbp envVal envObs a
                                        (cec, clock_knowledge envObs cec a s))
                                        (toList agents) ] .
                   s \<leftarrow> toList X ])"
(*<*)

abbreviation
  clock_trans :: "'s odlist \<Rightarrow> 's odlist \<Rightarrow> 's odlist"
where
  "clock_trans \<equiv> ClockView.clock_trans agents jkbp envAction envTrans envVal envObs"

lemma clock_trans_aux:
  assumes t'C: "t' \<in> Clock.jkbpC"
      and ec: "clock_simAbs ec = Clock.sim_equiv_class a' t'"
      and tC: "t \<in> Clock.jkbpCn (tLength t')"
      and eact: "eact \<in> set (envAction (tLast t))"
  shows "(aact \<in> set (listToFuns (\<lambda>a. clock_simAction a (fst ec, clock_knowledge envObs (fst ec) a (tLast t)))
                            (toList agents)))
     \<longleftrightarrow> (\<forall>a. aact a \<in> set (jAction (Clock.MCn (tLength t')) t a))"
  using assms
  apply -
  apply (frule Clock.jkbpCn_jkbpC_inc)
  apply (clarsimp simp: listToFuns_ext[OF agents[unfolded toSet_def]])
  apply (subst clock_simAction')
     apply (erule Clock.jkbpCn_jkbpC_inc)
    apply (subst clock_coEC_relation_image)
     apply (simp add: common_abs common_abs_def toSet_def[symmetric])
    apply (fastforce simp: common_abs agent_abs_def common_abs_def clock_repRels_def)
   apply (simp add: common_abs common_abs_def)
  apply (simp add: Clock.jkbpC_jkbpCn_jAction_eq)
  done

(*>*)
text\<open>

The function @{term "listToFuns"} exhibits the isomorphism between @{typ
"('a \<times> 'b list) list"} and @{typ "('a \<Rightarrow> 'b) list"} for finite types
@{typ "'a"}.

We can show that the transition function works for both the
commonly-held set of states and the agent subjective one. The proofs
are  straightforward.

\<close>

lemma clock_trans_common:
  assumes tC: "t \<in> Clock.jkbpC"
  assumes ec: "clock_simAbs ec = Clock.sim_equiv_class a t"
  shows "ODList.toSet (clock_trans (fst ec) (fst ec))
       = { s |t' s. t' \<leadsto> s \<in> Clock.jkbpC \<and> tLength t' = tLength t }"
(*<*) (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    unfolding clock_trans_def
    apply (clarsimp simp: toSet_def[symmetric] common_abs[OF assms] common_abs_def)
    apply (rule_tac x=xa in exI)
    apply clarsimp
    apply (rule Clock.jkbpCn_jkbpC_inc[where n="Suc (tLength t)"])
    apply (auto simp: Let_def iff: clock_trans_aux[OF tC ec])
    done
next
  show "?rhs \<subseteq> ?lhs"
    unfolding clock_trans_def
    apply (clarsimp simp: toSet_def[symmetric] common_abs[OF assms] common_abs_def)
    apply (drule Clock.jkbpC_tLength_inv[where n="Suc (tLength t)"])
    apply (auto simp: Let_def iff: clock_trans_aux[OF tC ec])
    done
qed

(*>*)
text\<open>\<close>

lemma clock_trans_agent:
  assumes tC: "t \<in> Clock.jkbpC"
  assumes ec: "clock_simAbs ec = Clock.sim_equiv_class a t"
  shows "ODList.toSet (clock_trans (fst ec) (snd ec))
       = { s |t' s. t' \<leadsto> s \<in> Clock.jkbpC \<and> clock_jview a t' = clock_jview a t }"
(*<*) (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    unfolding clock_trans_def
    apply (clarsimp simp: toSet_def[symmetric] common_abs[OF assms] agent_abs[OF assms] common_abs_def agent_abs_def)
    apply (rule_tac x=t' in exI)
    apply clarsimp
    apply (rule Clock.jkbpCn_jkbpC_inc[where n="Suc (tLength t)"])
    apply (auto simp: Let_def iff: clock_trans_aux[OF tC ec])
    done
next
  show "?rhs \<subseteq> ?lhs"
    unfolding clock_trans_def
    apply (clarsimp simp: toSet_def[symmetric] common_abs[OF assms] agent_abs[OF assms] common_abs_def agent_abs_def)
    apply (drule Clock.jkbpC_tLength_inv[where n="Suc (tLength t)"])
    apply (auto simp: Let_def iff: clock_trans_aux[OF tC ec])
    done
qed

(*>*)
text\<open>

Note that the clock semantics disregards paths, so we simply compute
the successors of the temporal slice and partition that. Similarly the
successors of the agent's subjective equivalence class tell us what
the set of possible observations are:

\<close>

definition (in -)
  clock_mkSuccs :: "('s :: linorder \<Rightarrow> 'obs) \<Rightarrow> 'obs \<Rightarrow> 's odlist
                \<Rightarrow> 's clock_simWorldsRep"
where
  "clock_mkSuccs envObs obs Y' \<equiv> (Y', ODList.filter (\<lambda>s. envObs s = obs) Y')"

text\<open>

Finally we can define our transition function on simulated states:

\<close>

definition (in -)
  clock_simTrans :: "('a :: linorder) odlist \<Rightarrow> ('a, 'p, 'aAct) JKBP
              \<Rightarrow> (('s :: linorder) \<Rightarrow> 'eAct list)
              \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's)
              \<Rightarrow> ('s \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'obs)
              \<Rightarrow> 'a \<Rightarrow> 's clock_simWorldsRep \<Rightarrow> 's clock_simWorldsRep list"
where
  "clock_simTrans agents jkbp envAction envTrans envVal envObs \<equiv> \<lambda>a (Y, X).
     let X' = clock_trans agents jkbp envAction envTrans envVal envObs Y X;
        Y' = clock_trans agents jkbp envAction envTrans envVal envObs Y Y
      in [ clock_mkSuccs (envObs a) obs Y' .
             obs \<leftarrow> map (envObs a) (toList X') ]"
(*<*)

abbreviation
  clock_simTrans :: "'a \<Rightarrow> 's clock_simWorldsRep \<Rightarrow> 's clock_simWorldsRep list"
where
  "clock_simTrans \<equiv> ClockView.clock_simTrans agents jkbp envAction envTrans envVal envObs"

(*>*)
text\<open>

Showing that this respects the property asked of it by the @{term
"Algorithm"} locale is straightforward:

\<close>

lemma clock_simTrans:
  assumes tC: "t \<in> Clock.jkbpC"
      and ec: "clock_simAbs ec = Clock.sim_equiv_class a t"
  shows "clock_simAbs ` set (clock_simTrans a ec)
      = { Clock.sim_equiv_class a (t' \<leadsto> s)
          |t' s. t' \<leadsto> s \<in> Clock.jkbpC \<and> clock_jview a t' = clock_jview a t }"
(*<*) (is "?lhs = ?rhs")
proof
  note image_cong_simp [cong del]
  show "?lhs \<subseteq> ?rhs"
    unfolding clock_simTrans_def clock_mkSuccs_def
    using clock_trans_common[OF tC ec] clock_trans_agent[OF tC ec]
    apply (clarsimp simp: toSet_def[symmetric] clock_simAbs_def Let_def)

    apply (rule_tac x=t' in exI)
    apply (rule_tac x=xa in exI)

    apply (clarsimp simp: clock_sim_def)
    apply safe

     apply clarsimp
     apply (rule_tac x="t'a \<leadsto> s" in image_eqI)
      apply (clarsimp simp: Let_def Set.image_def)
      apply safe
        apply (rule_tac x="t'b \<leadsto> x" in exI)
        apply (clarsimp simp: Let_def Set.image_def)
        apply (drule_tac t="t'b \<leadsto> x" in Clock.jkbpC_tLength_inv[OF _ refl])
        apply (auto simp: Let_def)[1]
       apply (rule_tac x="ta" in exI)
       apply simp
       apply (rule Clock.jkbpCn_jkbpC_inc[where n="Suc (tLength t)"])
       apply (auto simp: Let_def)[3]

    apply (rule_tac x="tLast ta" in exI)
    apply (clarsimp simp: Let_def Set.image_def)
    apply safe
      apply (rule_tac x="taa" in exI)
      apply simp
      apply (rule Clock.jkbpCn_jkbpC_inc[where n="Suc (tLength t)"])
       apply (auto simp: Let_def)[1]
     apply (drule_tac t="t'a \<leadsto> x" in Clock.jkbpC_tLength_inv[OF _ refl])
     apply (rule_tac x="t'a \<leadsto> x" in exI)
     apply (auto simp: Let_def)[1]
    apply (drule_tac t="ta" in Clock.jkbpC_tLength_inv)
     apply blast
    apply (clarsimp simp: Let_def)
    apply (rule_tac x="ta" in exI)
    apply simp
    apply (rule Clock.jkbpCn_jkbpC_inc[where n="Suc (tLength t)"])
    apply (auto simp: Let_def)
    done
next
  show "?rhs \<subseteq> ?lhs"
    unfolding clock_simTrans_def Let_def
    apply (cases ec)
    using clock_trans_common[OF tC ec] clock_trans_agent[OF tC ec]
    apply (clarsimp simp: toSet_def[symmetric] Set.image_def clock_simAbs_def
                simp del: split_paired_Ex)

    apply (rule_tac x="clock_mkSuccs (envObs a) (envObs a s) (clock_trans aa aa)" in exI)
    apply safe
      apply auto[1]
     apply (rule_tac x="tLast x" in exI)
     apply (clarsimp simp: clock_trans_common[OF tC ec] clock_mkSuccs_def)
     apply safe
       apply (clarsimp simp: clock_sim_def simp del: Clock.jkbpCn.simps)
       apply rule
        apply (clarsimp simp: Let_def)
        apply (rule_tac x="ta" in exI)
        apply (simp add: Let_def)
        apply (rule Clock.jkbpCn_jkbpC_inc[where n="Suc (tLength t)"])
        apply (clarsimp simp: Let_def)
        apply (rule_tac x=eact in exI)
        apply (rule_tac x=aact in exI)
        apply clarsimp
       apply (clarsimp simp: Let_def Set.image_def)
       apply (drule_tac t="t'a \<leadsto> xa" in Clock.jkbpC_tLength_inv[OF _ refl])
       apply (rule_tac x="t'a \<leadsto> xa" in exI)
       apply (auto simp: Let_def)[1]
      apply (drule_tac t="x" in Clock.jkbpC_tLength_inv[OF _ refl])
      apply (simp only: Let_def Clock.jkbpCn.simps)
      apply clarify
      apply (rule_tac x="ta" in exI)
      apply simp
      apply (rule Clock.jkbpCn_jkbpC_inc[where n="Suc (tLength t)"])
      apply (auto simp: Let_def)[1]
     apply (clarsimp simp: clock_trans_common[OF tC ec] clock_mkSuccs_def)
     apply (rule_tac x="t'a \<leadsto> sa" in exI)
     apply (clarsimp simp: clock_sim_def Let_def)
     (* FIXME similar to above *)
     apply rule
      apply (clarsimp simp: Set.image_def)
      apply (rule_tac x="t'b \<leadsto> x" in exI)
      apply (drule_tac t="t'b \<leadsto> x" in Clock.jkbpC_tLength_inv[OF _ refl])
      apply (auto simp: Let_def)[1]
    apply clarsimp
    apply (rule_tac x="ta" in exI)
    apply auto
    apply (rule Clock.jkbpCn_jkbpC_inc[where n="Suc (tLength t)"])
    apply (auto simp: Let_def)
    done
qed
(*>*)

end (* context FiniteLinorderEnvironment *)

(* **************************************** *)

subsubsection\<open>Maps\<close>

text\<open>

\label{sec:kbps-theory-clock-view-maps}

As mentioned above, the canonicity of our ordered, distinct list
representation of automaton states allows us to use them as keys in a
digital trie; a value of type @{typ "('key, 'val) trie"} maps keys of
type @{typ "'key list"} to values of type @{typ "'val"}.

In this specific case we track automaton transitions using a two-level
structure mapping sets of states to an association list mapping
observations to sets of states, and for actions automaton states map
directly to agent actions.

\<close>

type_synonym ('s, 'obs) clock_trans_trie
  = "('s, ('s, ('obs, 's clock_simWorldsRep) mapping) trie) trie"
type_synonym ('s, 'aAct) clock_acts_trie = "('s, ('s, 'aAct) trie) trie"
(*<*)

definition
  trans_MapOps_lookup :: "('s :: linorder, 'obs) clock_trans_trie
                        \<Rightarrow> 's clock_simWorldsRep \<times> 'obs
                        \<rightharpoonup> 's clock_simWorldsRep"
where
  "trans_MapOps_lookup \<equiv> \<lambda>m k.
     Option.bind (trie_odlist_lookup m (fst (fst k))) (\<lambda>m.
       (Option.bind (trie_odlist_lookup m (snd (fst k))) (\<lambda>m.
         Mapping.lookup m (snd k))))"

definition
  trans_MapOps_update :: "('s :: linorder) clock_simWorldsRep \<times> 'obs \<Rightarrow> 's clock_simWorldsRep
                        \<Rightarrow> ('s :: linorder, 'obs) clock_trans_trie
                        \<Rightarrow> ('s :: linorder, 'obs) clock_trans_trie"
where
  "trans_MapOps_update \<equiv> \<lambda>k v m.
     trie_odlist_update_with (fst (fst k)) m empty_trie (\<lambda>m.
       trie_odlist_update_with (snd (fst k)) m Mapping.empty (\<lambda>m.
          Mapping.update (snd k) v m))"

definition
  trans_MapOps :: "(('s :: linorder, 'obs) clock_trans_trie,
                    's clock_simWorldsRep \<times> 'obs, 's clock_simWorldsRep) MapOps"
where
  "trans_MapOps \<equiv>
     \<lparr> MapOps.empty = empty_trie,
       lookup = trans_MapOps_lookup,
       update = trans_MapOps_update \<rparr>"

lemma (in FiniteLinorderEnvironment) trans_MapOps:
  "MapOps (\<lambda>k. (clock_simAbs (fst k), snd k)) (Clock.jkbpSEC \<times> UNIV) trans_MapOps"
proof
  fix k show "MapOps.lookup trans_MapOps (MapOps.empty trans_MapOps) k = None"
    unfolding trans_MapOps_def trans_MapOps_lookup_def trie_odlist_lookup_def
    by (auto split: prod.split)
next
  fix e k k' M
  assume k: "(clock_simAbs (fst k), snd k) \<in> Clock.jkbpSEC \<times> (UNIV :: 'z set)"
     and k': "(clock_simAbs (fst k'), snd k') \<in> Clock.jkbpSEC \<times> (UNIV :: 'z set)"
  show "MapOps.lookup trans_MapOps (MapOps.update trans_MapOps k e M) k'
         = (if (clock_simAbs (fst k'), snd k') = (clock_simAbs (fst k), snd k)
             then Some e else MapOps.lookup trans_MapOps M k')"
  proof(cases "(clock_simAbs (fst k'), snd k') = (clock_simAbs (fst k), snd k)")
    case True hence "k = k'"
      using inj_onD[OF clock_simAbs_inj_on] k k' by (auto iff: prod_eqI)
    thus ?thesis
      unfolding trans_MapOps_def trans_MapOps_lookup_def trans_MapOps_update_def trie_odlist_lookup_def trie_odlist_update_with_def
        by (simp add: lookup_trie_update_with lookup_update split: option.split prod.split) 
  next
    case False thus ?thesis
      unfolding trans_MapOps_def trans_MapOps_lookup_def trans_MapOps_update_def trie_odlist_lookup_def trie_odlist_update_with_def
      by (cases "fst k = fst k'")
       (auto simp add: lookup_empty lookup_update_neq prod_eq_iff lookup_trie_update_with split: option.split prod.split)
  qed
qed

(* A map for the agent actions. *)

definition
  acts_MapOps_lookup :: "('s :: linorder, 'aAct) clock_acts_trie
                      \<Rightarrow> 's clock_simWorldsRep
                      \<rightharpoonup> 'aAct"
where
  "acts_MapOps_lookup \<equiv> \<lambda>m k.
     Option.bind (trie_odlist_lookup m (fst k)) (\<lambda>m.
       (trie_odlist_lookup m (snd k)))"

definition
  acts_MapOps_update :: "('s :: linorder) clock_simWorldsRep \<Rightarrow> 'aAct
                      \<Rightarrow> ('s :: linorder, 'aAct) clock_acts_trie
                      \<Rightarrow> ('s :: linorder, 'aAct) clock_acts_trie"
where
  "acts_MapOps_update \<equiv> \<lambda>k v m.
     trie_odlist_update_with (fst k) m empty_trie (\<lambda>m.
       trie_odlist_update (snd k) v m)"

definition
  acts_MapOps :: "(('s :: linorder, 'aAct) clock_acts_trie, 's clock_simWorldsRep, 'aAct) MapOps"
where
  "acts_MapOps \<equiv>
     \<lparr> MapOps.empty = empty_trie,
       lookup = acts_MapOps_lookup,
       update = acts_MapOps_update \<rparr>"

lemma (in FiniteLinorderEnvironment) acts_MapOps:
  "MapOps clock_simAbs Clock.jkbpSEC acts_MapOps"
proof
  fix k show "MapOps.lookup acts_MapOps (MapOps.empty acts_MapOps) k = None"
    unfolding acts_MapOps_def acts_MapOps_lookup_def trie_odlist_lookup_def
    by auto
next
  fix e k k' M
  assume k: "clock_simAbs k \<in> Clock.jkbpSEC"
     and k': "clock_simAbs k' \<in> Clock.jkbpSEC"
  show "MapOps.lookup acts_MapOps (MapOps.update acts_MapOps k e M) k'
         = (if clock_simAbs k' = clock_simAbs k
             then Some e else MapOps.lookup acts_MapOps M k')"
  proof(cases "clock_simAbs k' = clock_simAbs k")
    case True hence "k = k'"
      using inj_onD[OF clock_simAbs_inj_on] k k' by (auto iff: prod_eqI)
    thus ?thesis
      unfolding acts_MapOps_def acts_MapOps_lookup_def acts_MapOps_update_def
      by (auto simp: lookup_trie_update lookup_trie_update_with
                     trie_odlist_update_with_def trie_odlist_update_def trie_odlist_lookup_def)
  next
    case False thus ?thesis
      unfolding acts_MapOps_def acts_MapOps_lookup_def acts_MapOps_update_def
      by (auto simp: lookup_trie_update lookup_trie_update_with
                     trie_odlist_update_with_def trie_odlist_update_def trie_odlist_lookup_def
               dest: prod_eqI
              split: option.split)
  qed
qed

(*>*)
text\<open>

We define two records @{term "acts_MapOps"} and @{term "trans_MapOps"}
satisfying the @{term "MapOps"} predicate
(\S\ref{sec:kbps-theory-map-ops}). Discharging the obligations in the
@{term "Algorithm"} locale is routine, leaning on the work of
\citet{DBLP:conf/itp/LammichL10}.

\<close>

subsubsection\<open>Locale instantiation\<close>

text\<open>

Finally we assemble the algorithm and discharge the proof obligations.

\<close>

sublocale FiniteLinorderEnvironment
        < Clock: Algorithm
            jkbp envInit envAction envTrans envVal
            clock_jview envObs clock_jviewInit clock_jviewIncr
            clock_sim clock_simRels clock_simVal
            clock_simAbs clock_simObs clock_simInit clock_simTrans clock_simAction
            acts_MapOps trans_MapOps
(*<*)
  apply (unfold_locales)

  apply clarify
  apply (rule clock_simInit)
  apply simp

  apply clarify
  apply (erule (1) clock_simObs)

  apply clarify
  apply (erule (1) clock_simAction)

  apply clarify
  apply (erule (1) clock_simTrans)

  apply (rule acts_MapOps)
  apply (rule trans_MapOps)

  done

(*>*)
text\<open>

Explicitly, the algorithm for this case is:

\<close>

definition
  "mkClockAuto \<equiv> \<lambda>agents jkbp envInit envAction envTrans envVal envObs.
    mkAlgAuto acts_MapOps
              trans_MapOps
              (clock_simObs envObs)
              (clock_simInit envInit envObs)
              (clock_simTrans agents jkbp envAction envTrans envVal envObs)
              (clock_simAction jkbp envVal envObs)
              (\<lambda>a. map (clock_simInit envInit envObs a \<circ> envObs a) envInit)"

lemma (in FiniteLinorderEnvironment) mkClockAuto_implements:
  "Clock.implements
    (mkClockAuto agents jkbp envInit envAction envTrans envVal envObs)"
(*<*)
  using Clock.k_mkAlgAuto_implements
  unfolding mkClockAuto_def mkAlgAuto_def Clock.k_frontier_def
  by simp

(*

We actually run this unfolding of the algorithm. The lemma is keeping
us honest.

*)

definition
  "ClockAutoDFS \<equiv> \<lambda>agents jkbp envInit envAction envTrans envVal envObs. \<lambda>a.
    alg_dfs acts_MapOps
            trans_MapOps
            (clock_simObs envObs a)
            (clock_simTrans agents jkbp envAction envTrans envVal envObs a)
            (clock_simAction jkbp envVal envObs a)
            (map (clock_simInit envInit envObs a \<circ> envObs a) envInit)"

lemma (in FiniteLinorderEnvironment)
  "mkClockAuto agents jkbp envInit envAction envTrans envVal envObs
 = (\<lambda>a. alg_mk_auto acts_MapOps trans_MapOps (clock_simInit a) (ClockAutoDFS agents jkbp envInit envAction envTrans envVal envObs a))"
  unfolding mkClockAuto_def ClockAutoDFS_def mkAlgAuto_def alg_mk_auto_def by (simp add: Let_def)

(*>*)
text\<open>

We discuss the clock semantics further in \S\ref{sec:kbps-alg-clock}.

\<close>

(*<*)
end
(*>*)
