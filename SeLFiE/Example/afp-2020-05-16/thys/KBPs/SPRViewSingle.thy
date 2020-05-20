(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory SPRViewSingle
imports
  KBPsAlg
  SPRView
  List_local
  ODList
  Trie2
  "HOL-Library.Mapping"
begin
(*>*)

subsection\<open>Perfect Recall for a Single Agent\<close>

text\<open>

\label{sec:kbps-spr-single-agent}

We capture our expectations of a single-agent scenario in the
following locale:

\<close>

locale FiniteSingleAgentEnvironment =
  FiniteEnvironment jkbp envInit envAction envTrans envVal envObs
    for jkbp :: "('a, 'p, 'aAct) JKBP"
    and envInit :: "('s :: {finite, linorder}) list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"
    and envObs :: "'a \<Rightarrow> 's \<Rightarrow> 'obs"
+ fixes agent :: "'a"
  assumes envSingleAgent: "a = agent"

text\<open>

As per the clock semantics of \S\ref{sec:kbps-theory-clock-view}, we
assume that the set of states is finite and linearly ordered. We give
the sole agent the name \<open>agent\<close>.

Our simulation is quite similar to the one for the clock semantics of
\S\ref{sec:kbps-theory-clock-view}: it records the set of worlds that
the agent considers possible relative to a trace and the SPR view. The
key difference is that it is path-sensitive:

\<close>

context FiniteSingleAgentEnvironment
begin

definition spr_abs :: "'s Trace \<Rightarrow> 's set" where
  "spr_abs t \<equiv>
    tLast ` { t' \<in> SPR.jkbpC . spr_jview agent t' = spr_jview agent t }"

type_synonym (in -) 's spr_simWorlds = "'s set \<times> 's"

definition spr_sim :: "'s Trace \<Rightarrow> 's spr_simWorlds" where
  "spr_sim \<equiv> \<lambda>t. (spr_abs t, tLast t)"
(*<*)

lemma spr_absI[elim]:
  "\<lbrakk> t' \<in> SPR.jkbpC; spr_jview a t' = spr_jview a t; v = tLast t' \<rbrakk>
    \<Longrightarrow> v \<in> spr_abs t"
  unfolding spr_abs_def
  using envSingleAgent[where a=a] by blast

lemma spr_abs_tLastD[simp]:
  "v \<in> spr_abs t \<Longrightarrow> envObs a v = envObs a (tLast t)"
  unfolding spr_abs_def
  using envSingleAgent[where a=a] by auto

lemma spr_abs_conv:
  "v \<in> spr_abs t
    \<longleftrightarrow> (\<exists>t'. t' \<in> SPR.jkbpC \<and> spr_jview a t' = spr_jview a t \<and> v = tLast t')"
  unfolding spr_abs_def
  using envSingleAgent[where a=a] by blast

lemma spr_abs_eq[dest]:
  "spr_jview a t = spr_jview a t' \<Longrightarrow> spr_abs t = spr_abs t'"
  unfolding spr_abs_def
  using envSingleAgent[where a=a] by auto

lemma spr_abs_refl[intro, simp]:
  "t \<in> SPR.jkbpC \<Longrightarrow> tLast t \<in> spr_abs t"
  unfolding spr_abs_def
  using envSingleAgent[where a=a] by auto

lemma spr_sim_simps[simp]:
  "fst (spr_sim t) = spr_abs t"
  unfolding spr_sim_def by simp

(*>*)
text\<open>

The Kripke structure for this simulation relates worlds for @{term
"agent"} if the sets of states it considers possible coincide, and the
observation of the final states of the trace is the same. Propositions
are evaluated at the final state.

\<close>

definition spr_simRels :: "'a \<Rightarrow> 's spr_simWorlds Relation" where
  "spr_simRels \<equiv> \<lambda>a. { ((U, u), (V, v)) |U u V v.
                         U = V \<and> {u, v} \<subseteq> U \<and> envObs a u = envObs a v }"

definition spr_simVal :: "'s spr_simWorlds \<Rightarrow> 'p \<Rightarrow> bool" where
  "spr_simVal \<equiv> envVal \<circ> snd"

abbreviation spr_simMC :: "('a, 'p, 's spr_simWorlds) KripkeStructure" where
  "spr_simMC \<equiv> mkKripke (spr_sim ` SPR.jkbpC) spr_simRels spr_simVal"
(*<*)

lemma spr_simVal[iff]:
  "spr_simVal (spr_sim t) = envVal (tLast t)"
  unfolding spr_sim_def spr_simVal_def by simp

lemma spr_sim_r:
  "sim_r SPR.MC spr_simMC spr_sim"
proof
  fix a t v'
  assume t: "t \<in> worlds SPR.MC"
     and tv': "(spr_sim t, v') \<in> relations spr_simMC a"
  from tv' obtain s
    where vv': "v' = (spr_abs t, s)"
      and st: "s \<in> spr_abs t"
    unfolding spr_simRels_def spr_sim_def mkKripke_def SPR.mkM_def
    by auto
  from st obtain v
    where "v \<in> SPR.jkbpC"
      and "spr_jview a v = spr_jview a t"
      and "tLast v = s"
    by (auto(*<*)iff: spr_abs_conv(*>*))
  with t vv'
  have "(t, v) \<in> relations SPR.MC a"
   and "spr_sim v = v'"
    unfolding spr_simRels_def spr_sim_def mkKripke_def SPR.mkM_def
    by auto
  thus "\<exists>v. (t, v) \<in> relations SPR.MC a \<and> spr_sim v = v'" by blast
qed

(*>*)
text\<open>

Demonstrating that this is a simulation
(\S\ref{sec:kripke-theory-simulations}) is straightforward.

\<close>

lemma spr_sim: "sim SPR.MC spr_simMC spr_sim"
(*<*)
proof
  show "sim_f SPR.MC spr_simMC spr_sim"
    unfolding spr_simRels_def spr_sim_def mkKripke_def SPR.mkM_def
    by (rule) auto
next
  show "sim_r SPR.MC spr_simMC spr_sim"
    by (rule spr_sim_r)
qed auto

(*>*)
text\<open>\<close>
end (* context FiniteSingleAgentEnvironment *)

sublocale FiniteSingleAgentEnvironment
        < SPRsingle: SimIncrEnvironment jkbp envInit envAction envTrans envVal
                                       spr_jview envObs spr_jviewInit spr_jviewIncr
                                       spr_sim spr_simRels spr_simVal
(*<*)
  by standard (rule spr_sim)
(*>*)

(* **************************************** *)

subsubsection\<open>Representations\<close>

text\<open>

\label{sec:kbps-theory-spr-single-rep}

As in \S\ref{sec:kbps-theory-clock-view-algops}, we quotient @{typ "'s
spr_simWorlds"} by @{term "spr_simRels"}. Because there is only a
single agent, an element of this quotient corresponding to a cononical
trace @{term "t"} is isomorphic to the set of states that are possible
given the sequence of observations made by @{term "agent"} on @{term
"t"}. Therefore we have a very simple representation:

\<close>

context FiniteSingleAgentEnvironment
begin

type_synonym (in -) 's spr_simWorldsRep = "'s odlist"

text\<open>

It is very easy to map these representations back to simulated
equivalence classes:

\<close>

definition
  spr_simAbs :: "'s spr_simWorldsRep \<Rightarrow> 's spr_simWorlds set"
where
  "spr_simAbs \<equiv> \<lambda>ss. { (toSet ss, s) |s. s \<in> toSet ss }"

text\<open>

This time our representation is unconditionally canonical:

\<close>

lemma spr_simAbs_inj: "inj spr_simAbs"
(*<*)
  apply (rule injI)
  unfolding spr_simAbs_def
  apply (subgoal_tac "toSet x = toSet y")
  apply auto
  using toSet_inj
  apply (erule injD)
  done

lemma spr_sim_rep_abs[simp]:
  assumes ec: "spr_simAbs ec = SPRsingle.sim_equiv_class a t"
  shows "toSet ec = spr_abs t"
proof
  show "toSet ec \<subseteq> spr_abs t"
  proof
    fix x assume x: "x \<in> toSet ec"
    hence "(toSet ec, x) \<in> spr_simAbs ec"
      unfolding spr_simAbs_def by simp
    with ec have "(toSet ec, x) \<in> SPRsingle.sim_equiv_class a t"
      by simp
    with x envSingleAgent[where a=a] show "x \<in> spr_abs t"
      unfolding spr_sim_def spr_abs_def by auto
  qed
next
  show "spr_abs t \<subseteq> toSet ec"
  proof
    fix x assume x: "x \<in> spr_abs t"
    with ec envSingleAgent[where a=a] show "x \<in> toSet ec"
      unfolding spr_simAbs_def spr_sim_def spr_abs_def by auto
  qed
qed

lemma spr_sim_rep_abs_syn[simp]:
  assumes ec: "spr_simAbs ec = SPRsingle.sim_equiv_class agent t"
  shows "set (toList ec) = spr_abs t"
  using spr_sim_rep_abs[OF ec] unfolding toSet_def by simp

lemma spr_simAbs_list:
  "spr_simAbs ` fromList ` X = (\<lambda>ss. { (ss, s) |s. s \<in> ss }) ` set ` X"
  unfolding spr_simAbs_def Set.image_def by auto

(*>*)
text\<open>

We again make use of the following Kripke structure, where the worlds
are the final states of the subset of the temporal slice that @{term
"agent"} believes possible:

\<close>

definition spr_repRels :: "'a \<Rightarrow> ('s \<times> 's) set" where
  "spr_repRels \<equiv> \<lambda>a. { (s, s'). envObs a s' = envObs a s }"

abbreviation spr_repMC :: "'s set \<Rightarrow> ('a, 'p, 's) KripkeStructure" where
  "spr_repMC \<equiv> \<lambda>X. mkKripke X spr_repRels envVal"

text\<open>

Similarly we show that this Kripke structure is adequate by
introducing an intermediate structure and connecting them all with a
tower of simulations:

\<close>

abbreviation spr_jkbpCSt :: "'s Trace \<Rightarrow> 's spr_simWorlds set" where
  "spr_jkbpCSt t \<equiv> SPRsingle.sim_equiv_class agent t"

abbreviation
  spr_simMCt :: "'s Trace \<Rightarrow> ('a, 'p, 's spr_simWorlds) KripkeStructure"
where
  "spr_simMCt t \<equiv> mkKripke (spr_jkbpCSt t) spr_simRels spr_simVal"

definition spr_repSim :: "'s spr_simWorlds \<Rightarrow> 's" where
  "spr_repSim \<equiv> snd"
(*<*)

lemma spr_repMC_kripke[intro, simp]: "kripke (spr_repMC X)"
  by (rule kripkeI) simp

lemma spr_repMC_S5n[intro, simp]: "S5n (spr_repMC X)"
  unfolding spr_repRels_def
  by (intro S5nI equivI refl_onI symI transI) auto

lemma jkbpCSt_jkbpCS_subset:
  "SPRsingle.sim_equiv_class agent t \<subseteq> spr_sim ` SPR.jkbpC"
  by auto

lemma spr_simRep_sim_simps[simp]:
  "spr_repSim ` spr_sim ` T = tLast ` T"
  "spr_repSim (spr_sim t) = tLast t"
  unfolding spr_repSim_def spr_sim_def Set.image_def by auto

(*>*)
text\<open>\<close>

lemma spr_repSim:
  assumes tC: "t \<in> SPR.jkbpC"
  shows "sim (spr_simMCt t)
             ((spr_repMC \<circ> fst) (spr_sim t))
             spr_repSim"
(*<*) (is "sim ?M ?M' ?f")
proof
  show "sim_range ?M ?M' ?f"
  proof
    show "worlds ?M' = ?f ` worlds ?M"
      unfolding spr_sim_def spr_repSim_def spr_abs_def Set.image_def
      by auto
  next
    fix a
    show "relations ?M' a \<subseteq> worlds ?M' \<times> worlds ?M'"
      unfolding spr_sim_def spr_repSim_def by simp
  qed
next
  show "sim_val ?M ?M' ?f"
    unfolding spr_sim_def spr_simVal_def spr_repSim_def by auto
next
  from tC
  show "sim_f ?M ?M' ?f"
    unfolding spr_sim_def spr_simVal_def spr_repSim_def
    apply -
    apply rule
    apply (cut_tac a=a in envSingleAgent)
    apply (auto iff: spr_sim_def spr_repRels_def)
    apply (rule spr_tLast)
    apply auto
    done
next
  show "sim_r ?M ?M' ?f"
    unfolding spr_sim_def spr_simVal_def spr_repSim_def
    apply -
    apply rule
    apply (cut_tac a=a in envSingleAgent)
    unfolding spr_abs_def spr_sim_def spr_repRels_def spr_simRels_def Set.image_def
    apply auto
    done
qed

(*>*)
text\<open>

As before, the following sections discharge the requirements of the
\<open>Algorithm\<close> locale of Figure~\ref{fig:kbps-alg-alg-locale}.

\<close>

(* **************************************** *)

subsubsection\<open>Initial states\<close>

text\<open>

The initial states of the automaton for @{term "agent"} is simply the
partition of @{term "envInit"} under @{term "agent"}'s observation.

\<close>

definition (in -)
  spr_simInit :: "('s :: linorder) list \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'obs)
                     \<Rightarrow> 'a \<Rightarrow> 'obs \<Rightarrow> 's spr_simWorldsRep"
where
  "spr_simInit envInit envObs \<equiv> \<lambda>a iobs.
    ODList.fromList [ s. s \<leftarrow> envInit, envObs a s = iobs ]"
(*<*)

abbreviation
  spr_simInit :: "'a \<Rightarrow> 'obs \<Rightarrow> 's spr_simWorldsRep"
where
  "spr_simInit \<equiv> SPRViewSingle.spr_simInit envInit envObs"

(*>*)
text\<open>\<close>

lemma spr_simInit:
  assumes "iobs \<in> envObs a ` set envInit"
  shows "spr_simAbs (spr_simInit a iobs)
       = spr_sim ` { t' \<in> SPR.jkbpC. spr_jview a t' = spr_jviewInit a iobs }"
(*<*)
  using assms
  unfolding spr_simInit_def
  using envSingleAgent[where a=a]
  unfolding spr_simAbs_def spr_sim_def [abs_def] spr_abs_def
  apply (auto iff: spr_jview_def SPR.jviewInit)
   apply (rule_tac x="tInit s" in image_eqI)
    apply (auto iff: spr_jview_def)[1]
    apply (rule_tac x="tInit xa" in image_eqI)
    apply auto[1]
   apply simp
   apply simp
  apply (rule_tac x="tInit xb" in image_eqI)
  apply auto
  done
(*>*)

(* **************************************** *)

subsubsection\<open>Simulated observations\<close>

text\<open>

As the agent makes the same observation on the entire equivalence
class, we arbitrarily choose the first element of the representation:

\<close>

definition (in -)
  spr_simObs :: "('a \<Rightarrow> 's \<Rightarrow> 'obs)
               \<Rightarrow> 'a \<Rightarrow> ('s :: linorder) spr_simWorldsRep \<Rightarrow> 'obs"
where
  "spr_simObs envObs \<equiv> \<lambda>a. envObs a \<circ> ODList.hd"
(*<*)

abbreviation
  spr_simObs :: "'a \<Rightarrow> 's spr_simWorldsRep \<Rightarrow> 'obs"
where
  "spr_simObs \<equiv> SPRViewSingle.spr_simObs envObs"

(*>*)
text\<open>\<close>

lemma spr_simObs:
  assumes tC: "t \<in> SPR.jkbpC"
  assumes ec: "spr_simAbs ec = SPRsingle.sim_equiv_class a t"
  shows "spr_simObs a ec = envObs a (tLast t)"
(*<*)
proof -
  have A: "\<forall>s \<in> set (toList ec). envObs a s = envObs a (tLast t)"
    using spr_sim_rep_abs[OF ec] by (simp add: toSet_def)
  from tC ec have B: "tLast t \<in> set (toList ec)"
    using envSingleAgent[where a=a] by simp
  show ?thesis
    unfolding spr_simObs_def
    by (simp add: list_choose_hd[OF A B] ODList.hd_def)
qed
(*>*)

(* **************************************** *)

subsubsection\<open>Evaluation\<close>

text\<open>

\label{sec:kbps-spr-single-agent-eval}

As the single-agent case is much simpler than the multi-agent ones, we
define an evaluation function specialised to its representation.

Intuitively @{term "eval"} yields the subset of @{term "X"} where the
formula holds, where @{term "X"} is taken to be a representation of a
canonical equivalence class for @{term "agent"}.

\<close>

fun (in -)
  eval :: "(('s :: linorder) \<Rightarrow> 'p \<Rightarrow> bool)
        \<Rightarrow> 's odlist \<Rightarrow> ('a, 'p) Kform \<Rightarrow> 's odlist"
where
  "eval val X (Kprop p)      = ODList.filter (\<lambda>s. val s p) X"
| "eval val X (Knot \<phi>)       = ODList.difference X (eval val X \<phi>)"
| "eval val X (Kand \<phi> \<psi>)     = ODList.intersect (eval val X \<phi>) (eval val X \<psi>)"
| "eval val X (Kknows a \<phi>)   = (if eval val X \<phi> = X then X else ODList.empty)"
| "eval val X (Kcknows as \<phi>) =
                     (if as = [] \<or> eval val X \<phi> = X then X else ODList.empty)"

text\<open>

In general this is less efficient than the tableau approach of
\citet[Proposition~3.2.1]{FHMV:1995}, which labels all states with all
formulas. However it is often the case that the set of relevant worlds
is much smaller than the set of all system states.

Showing that this corresponds with the standard models relation is
routine.

\<close>
(*<*)

lemma eval_ec_subseteq:
  shows "toSet (eval envVal ec \<phi>) \<subseteq> toSet ec"
  by (induct \<phi>) auto

lemma eval_models_aux:
  assumes ec: "spr_simAbs ec = SPRsingle.sim_equiv_class agent t"
  assumes s: "s \<in> toSet ec"
  shows "s \<in> toSet (eval envVal ec \<phi>) \<longleftrightarrow> spr_repMC (toSet ec), s \<Turnstile> \<phi>"
using s
proof(induct \<phi> arbitrary: s)
  case (Kknows a \<phi> s) with ec envSingleAgent[where a=a] show ?case
    unfolding spr_repRels_def
    by (auto simp: inj_eq[OF toSet_inj, symmetric] dest: subsetD[OF eval_ec_subseteq])
next
  case (Kcknows as \<phi> s)
  from ec show ?case
  proof(cases as)
    case Nil with Kcknows show ?thesis by clarsimp
  next
    case (Cons x xs)
    hence "set as = {agent}"
      by (induct as) (auto simp: envSingleAgent)
    moreover
    have "(spr_repRels agent \<inter> toSet ec \<times> toSet ec)\<^sup>+ = (spr_repRels agent \<inter> toSet ec \<times> toSet ec)"
      by (rule trancl_id) (simp add: spr_repRels_def trans_def)
    moreover note Kcknows ec
    ultimately show ?thesis
      unfolding spr_repRels_def
      by (auto simp: inj_eq[OF toSet_inj, symmetric] dest: subsetD[OF eval_ec_subseteq])
  qed
qed simp_all

lemma eval_all_or_nothing:
  assumes subj_phi: "subjective agent \<phi>"
  shows "toSet (eval envVal ec \<phi>) = {} \<or> toSet (eval envVal ec \<phi>) = toSet ec"
  using subj_phi by (induct \<phi> rule: subjective.induct) auto
(*>*)

lemma eval_models:
  assumes ec: "spr_simAbs ec = SPRsingle.sim_equiv_class agent t"
  assumes subj: "subjective agent \<phi>"
  assumes s: "s \<in> toSet ec"
  shows "toSet (eval envVal ec \<phi>) \<noteq> {} \<longleftrightarrow> spr_repMC (toSet ec), s \<Turnstile> \<phi>"
(*<*)
  using eval_models_aux[OF ec s, symmetric] eval_all_or_nothing[OF subj] s
  by auto
(*>*)

(* **************************************** *)

subsubsection\<open>Simulated actions\<close>

text\<open>

The actions enabled on a canonical equivalence class are those for
which @{term "eval"} yields a non-empty set of states:

\<close>

definition (in -)
  spr_simAction :: "('a, 'p, 'aAct) KBP \<Rightarrow> (('s :: linorder) \<Rightarrow> 'p \<Rightarrow> bool)
                     \<Rightarrow> 'a \<Rightarrow> 's spr_simWorldsRep \<Rightarrow> 'aAct list"
where
  "spr_simAction kbp envVal \<equiv> \<lambda>a X.
    [ action gc. gc \<leftarrow> kbp, eval envVal X (guard gc) \<noteq> ODList.empty ]"
(*<*)

abbreviation
  spr_simAction :: "'a \<Rightarrow> 's spr_simWorldsRep \<Rightarrow> 'aAct list"
where
  "spr_simAction \<equiv> SPRViewSingle.spr_simAction (jkbp agent) envVal"

(*>*)
text\<open>

The key lemma relates the agent's behaviour on an equivalence class to
that on its representation:

\<close>

lemma spr_simAction_jAction:
  assumes tC: "t \<in> SPR.jkbpC"
  assumes ec: "spr_simAbs ec = SPRsingle.sim_equiv_class agent t"
  shows "set (spr_simAction agent ec)
       = set (jAction (spr_repMC (toSet ec)) (tLast t) agent)"
(*<*)
proof -
  have "\<And>P. (set (jkbp agent) \<inter> {gc. P gc})
      = { gc \<in> set (jkbp agent). P gc }"
    by blast
  then
  show ?thesis
    unfolding spr_simAction_def jAction_def
    apply clarsimp
    apply (rule SUP_cong)
     apply simp_all
     apply (rule Collect_cong)
     apply rule
      apply clarsimp
      apply (subst eval_models[OF ec, symmetric])
        apply (simp_all add: toSet_eq_iff)
       using subj tC ec
       apply (fastforce+)[2]
    apply clarsimp
    apply (subst (asm) eval_models[OF ec, symmetric])
    using subj tC ec
    apply fastforce+
    done (* FIXME improve *)
qed

lemma spr_submodel_aux:
  assumes tC: "t \<in> SPR.jkbpC"
      and s: "s \<in> worlds (spr_simMCt t)"
  shows "gen_model SPRsingle.MCS s = gen_model (spr_simMCt t) s"
proof(rule gen_model_subset[where T="SPRsingle.sim_equiv_class agent t"])
  fix a
  let ?X = "SPRsingle.sim_equiv_class agent t"
  show "relations SPRsingle.MCS a \<inter> ?X \<times> ?X
      = relations (spr_simMCt t) a \<inter> ?X \<times> ?X"
    by (simp add: Int_ac Int_absorb1
                  relation_mono[OF jkbpCSt_jkbpCS_subset jkbpCSt_jkbpCS_subset])
next
  let ?X = "SPRsingle.sim_equiv_class agent t"
  from s show "(\<Union>a. relations (spr_simMCt t) a)\<^sup>* `` {s} \<subseteq> ?X"
    apply (clarsimp simp del: mkKripke_simps)
    apply (erule kripke_rels_trc_worlds)
    apply auto
    done
next
  let ?Y = "{ t' \<in> SPR.jkbpC . spr_jview agent t' = spr_jview agent t }"
  let ?X = "spr_sim ` ?Y"
  from s obtain t'
    where st': "s = spr_sim t'"
      and t'C: "t' \<in> SPR.jkbpC"
      and t'O: "spr_jview agent t = spr_jview agent t'"
    by fastforce
  { fix t''
    assume tt': "(t', t'') \<in> (\<Union>a. relations SPR.MC a)\<^sup>*"
    from t'C tt' have t''C: "t'' \<in> SPR.jkbpC"
      by - (erule kripke_rels_trc_worlds, simp_all)
    from tt' t'O have t''O: "spr_jview agent t = spr_jview agent t''"
      apply induct
      unfolding SPR.mkM_def
      apply auto
      apply (cut_tac a=x in envSingleAgent)
      apply simp
      done
    from t''C t''O have "t'' \<in> ?Y" by simp }
  hence "(\<Union>a. relations SPR.MC a)\<^sup>* `` {t'} \<subseteq> ?Y"
    by clarsimp
  hence "spr_sim ` ((\<Union>a. relations SPR.MC a)\<^sup>* `` {t'}) \<subseteq> ?X"
    by (rule image_mono)
  with st' t'C
  show "(\<Union>a. relations SPRsingle.MCS a)\<^sup>* `` {s} \<subseteq> ?X"
    using sim_trc_commute[OF SPR.mkM_kripke spr_sim, where t=t'] by simp
qed (insert s, auto)

(*>*)
text\<open>

The \<open>Algorithm\<close> locale requires the following lemma, which is
a straightforward chaining of the above simulations.

\<close>

lemma spr_simAction:
  assumes tC: "t \<in> SPR.jkbpC"
      and ec: "spr_simAbs ec = SPRsingle.sim_equiv_class a t"
  shows "set (spr_simAction a ec) = set (jAction SPR.MC t a)"
(*<*)
proof -
  from ec
  have ec': "spr_simAbs ec = SPRsingle.sim_equiv_class agent t"
    by (simp only: envSingleAgent[where a=a])
  have "set (spr_simAction a ec) = set (spr_simAction agent ec)"
    by (simp only: envSingleAgent[where a=a])
  also from tC ec' have "... = set (jAction (spr_repMC (toSet ec)) (tLast t) agent)"
    by (rule spr_simAction_jAction)
  also from tC ec' have "... = set (jAction (spr_simMCt t) (spr_sim t) agent)"
    by (simp add: simulation_jAction_eq[OF _ spr_repSim])
  also from tC have "... = set (jAction SPRsingle.MCS (spr_sim t) agent)"
    using gen_model_jAction_eq[OF spr_submodel_aux[OF tC, where s="spr_sim t"], where w'="spr_sim t"]
          gen_model_world_refl[where w="spr_sim t" and M="spr_simMCt t"]
    by simp
  also from tC have "... = set (jAction SPR.MC t agent)"
    by (simp add: simulation_jAction_eq[OF _ spr_sim])
  finally show ?thesis by (simp only: envSingleAgent[where a=a])
qed
(*>*)

(* **************************************** *)

subsubsection\<open>Simulated transitions\<close>

text\<open>

It is straightforward to determine the possible successor states of a
given canonical equivalence class @{term "X"}:

\<close>

definition (in -)
  spr_trans :: "('a, 'p, 'aAct) KBP
              \<Rightarrow> ('s \<Rightarrow> 'eAct list)
              \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's)
              \<Rightarrow> ('s \<Rightarrow> 'p \<Rightarrow> bool)
              \<Rightarrow> 'a \<Rightarrow> ('s :: linorder) spr_simWorldsRep \<Rightarrow> 's list"
where
  "spr_trans kbp envAction envTrans val \<equiv> \<lambda>a X.
    [ envTrans eact (\<lambda>a'. aact) s .
       s \<leftarrow> toList X, eact \<leftarrow> envAction s, aact \<leftarrow> spr_simAction kbp val a X ]"
(*<*)

abbreviation
  spr_trans :: "'a \<Rightarrow> 's spr_simWorldsRep \<Rightarrow> 's list"
where
  "spr_trans \<equiv> SPRViewSingle.spr_trans (jkbp agent) envAction envTrans envVal"

(*>*)
text\<open>

Using this function we can determine the set of possible successor
equivalence classes from @{term "X"}:

\<close>

abbreviation (in -) envObs_rel :: "('s \<Rightarrow> 'obs) \<Rightarrow> 's \<times> 's \<Rightarrow> bool" where
  "envObs_rel envObs \<equiv> \<lambda>(s, s'). envObs s' = envObs s"

definition (in -)
  spr_simTrans :: "('a, 'p, 'aAct) KBP
                 \<Rightarrow> (('s::linorder) \<Rightarrow> 'eAct list)
                 \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's)
                 \<Rightarrow> ('s \<Rightarrow> 'p \<Rightarrow> bool)
                 \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'obs)
                 \<Rightarrow> 'a \<Rightarrow> 's spr_simWorldsRep \<Rightarrow> 's spr_simWorldsRep list"
where
  "spr_simTrans kbp envAction envTrans val envObs \<equiv> \<lambda>a X.
    map ODList.fromList (partition (envObs_rel (envObs a))
                                   (spr_trans kbp envAction envTrans val a X))"
(*<*)

abbreviation
  spr_simTrans :: "'a \<Rightarrow> 's spr_simWorldsRep \<Rightarrow> 's spr_simWorldsRep list"
where
  "spr_simTrans \<equiv> SPRViewSingle.spr_simTrans (jkbp agent) envAction envTrans envVal envObs"

lemma envObs_rel_equiv:
  "equiv UNIV (rel_ext (envObs_rel (envObs agent)))"
  by (intro equivI refl_onI symI transI) auto

lemma spr_trans:
  assumes tC: "t \<in> SPR.jkbpC"
  assumes ec: "spr_simAbs ec = SPRsingle.sim_equiv_class agent t"
  shows "set (spr_trans agent ec)
       = { s |t' s. t' \<leadsto> s \<in> SPR.jkbpC \<and> spr_jview agent t' = spr_jview agent t }" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix x assume x: "x \<in> ?lhs"
    with assms show "x \<in> ?rhs"
      unfolding spr_trans_def
      apply (clarsimp simp del: split_paired_Ex split_paired_All)
      apply (frule spr_sim_rep_abs)
      unfolding toSet_def
      apply clarsimp

      apply (simp only: spr_abs_conv[where a=agent])
      apply clarify

      apply (rule_tac x="t'" in exI)
      apply simp
      apply (rule_tac n="Suc (tLength t')" in SPR.jkbpCn_jkbpC_inc)
      apply (auto iff: Let_def simp del: split_paired_Ex split_paired_All)

      apply (rule_tac x=xa in exI)
      apply (rule_tac x="\<lambda>a'. aact" in exI)
      apply auto
      apply (subst envSingleAgent)
      apply (simp add: spr_simAction[where a=agent])
      apply (subst SPR.jkbpC_jkbpCn_jAction_eq[symmetric])
      apply auto
      apply (subst S5n_jAction_eq[where w'=t])
      apply simp_all
      unfolding SPR.mkM_def
      apply simp
      done
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix s assume s: "s \<in> ?rhs"
    then obtain t'
      where t'sC: "t' \<leadsto> s \<in> SPR.jkbpC"
        and tt': "spr_jview agent t' = spr_jview agent t"
      by blast
    from t'sC have t'Cn: "t' \<in> SPR.jkbpCn (tLength t')" by blast
    from t'sC obtain eact aact
      where eact: "eact \<in> set (envAction (tLast t'))"
        and aact: "\<forall>a. aact a \<in> set (jAction (SPR.mkM (SPR.jkbpCn (tLength t'))) t' a)"
        and s: "s = envTrans eact aact (tLast t')"
      using SPR.jkbpC_tLength_inv[where t="t' \<leadsto> s" and n="Suc (tLength t')"]
      by (auto iff: Let_def)
    from tC ec s eact aact tt' t'sC
    show "s \<in> ?lhs"
      unfolding spr_trans_def
      apply (clarsimp)
      apply (rule bexI[where x="tLast t'"])
      apply (rule bexI[where x=eact])
      apply simp_all
       prefer 2
       apply (blast intro: spr_absI)
      apply (simp add: spr_simAction[where a=agent])
      apply (rule image_eqI[where x="aact agent"])
       apply (subgoal_tac "(\<lambda>a'. aact agent) = aact")
        apply simp
       apply (rule ext)
       apply (cut_tac a=a' in envSingleAgent)
       apply simp
      apply (erule allE[where x=agent])
      apply (subst SPR.jkbpC_jkbpCn_jAction_eq)
      apply auto
      apply (subst S5n_jAction_eq[where w=t and w'=t'])
        apply simp
       apply (unfold SPR.mkM_def)[1]
       apply simp
       apply (blast dest: SPR.sync[rule_format])
      apply (auto dest: SPR.sync[rule_format])
      done
  qed
qed

(*>*)
text\<open>

The \<open>partition\<close> function splits a list into equivalence
classes under the given equivalence relation.

The property asked for by the \<open>Algorithm\<close> locale follows from
the properties of \<open>partition\<close> and \<open>spr_trans\<close>:

\<close>

lemma spr_simTrans:
  assumes tC: "t \<in> SPR.jkbpC"
  assumes ec: "spr_simAbs ec = SPRsingle.sim_equiv_class a t"
  shows "spr_simAbs ` set (spr_simTrans a ec)
      = { SPRsingle.sim_equiv_class a (t' \<leadsto> s)
          |t' s. t' \<leadsto> s \<in> SPR.jkbpC \<and> spr_jview a t' = spr_jview a t}"
(*<*) (is "?lhs a = ?rhs a")
proof -
  from ec have ec': "spr_simAbs ec = SPRsingle.sim_equiv_class agent t"
    by (simp only: envSingleAgent[where a=a])
  from ec' have "?lhs agent = ?rhs agent"
    unfolding spr_simTrans_def
    apply clarsimp
    apply (simp only: spr_simAbs_list partition[OF envObs_rel_equiv subset_UNIV] spr_trans[OF tC ec'])
    apply clarsimp
    apply rule

     (* left to right *)

     apply clarsimp
     apply (erule quotientE)
     apply clarsimp
     apply (rule_tac x=t' in exI)
     apply (rule_tac x=x in exI)
     apply clarsimp
     apply rule
      apply clarsimp
      apply (rule_tac x="t'a \<leadsto> s" in image_eqI)
       apply (unfold spr_sim_def [abs_def] spr_abs_def)[1]
       apply clarsimp
       apply (auto iff: spr_jview_def)[1]
        apply (rule_tac x="t'c \<leadsto> xa" in image_eqI)
         apply simp
        apply simp
       apply (simp add: spr_jview_def)
     apply clarsimp
     apply (frule spr_jview_tStep_eq_inv)
     apply clarsimp
     apply (rule_tac x=s' in exI)
     apply (unfold spr_sim_def [abs_def] spr_abs_def)[1]
     apply clarsimp
     apply (auto iff: spr_jview_def)[1]
      apply (rule_tac x="t'b \<leadsto> xa" in image_eqI)
       apply simp
       apply simp

     (* right to left *)

     apply clarsimp
     apply (rule_tac x="spr_abs (t' \<leadsto> s)" in image_eqI)
      apply rule
       apply clarsimp
       apply (frule spr_jview_tStep_eq_inv)
       apply clarsimp
       apply (unfold spr_sim_def [abs_def])[1]
       apply clarsimp
       apply rule
        apply (erule spr_abs_eq)
       apply (erule spr_absI[where a=agent]) back
        apply simp
       apply simp
      apply clarsimp
      apply (simp only: spr_abs_conv[where a=agent])
      apply clarsimp
      apply (frule spr_jview_tStep_eq_inv)
      apply clarsimp
      apply (rule_tac x="t'' \<leadsto> s'" in image_eqI)
       apply (unfold spr_sim_def [abs_def])[1]
       apply clarsimp
       apply blast
      apply blast
     apply (rule_tac x=s in quotientI2)
      apply auto[1]
     apply rule
      apply clarsimp
      apply rule
       apply blast
      apply (cut_tac v=x and t="t' \<leadsto> s" in spr_abs_conv[where a=agent])
      apply clarsimp
      apply (frule spr_jview_tStep_eq_inv)
      apply clarsimp
      apply (rule_tac x=t'' in exI)
      apply (simp add: Let_def spr_jview_def)
     apply clarsimp
     apply (erule spr_absI[where a=agent]) back back
     apply (auto iff: spr_jview_def)
     done
   thus "?lhs a = ?rhs a" by (simp only: envSingleAgent[where a=a])
qed

(*>*)
text\<open>\<close>

end (* context FiniteSingleAgentEnvironment *)

(* **************************************** *)

subsubsection\<open>Maps\<close>

text\<open>

\label{sec:kbps-theory-spr-single-maps}

As in \S\ref{sec:kbps-theory-clock-view-maps}, we use a pair of tries
and an association list to handle the automata representation. Recall
that the keys of these tries are lists of system states.

\<close>

type_synonym ('s, 'obs) spr_trans_trie = "('s, ('obs, 's odlist) mapping) trie"
type_synonym ('s, 'aAct) spr_acts_trie = "('s, ('s, 'aAct) trie) trie"
(*<*)

definition
  trans_MapOps_lookup :: "('s::linorder, 'obs) spr_trans_trie
                        \<Rightarrow> 's odlist \<times> 'obs \<rightharpoonup> 's odlist"
where
  "trans_MapOps_lookup \<equiv> \<lambda>m k.
     Option.bind (trie_odlist_lookup m (fst k)) (\<lambda>m'. Mapping.lookup m' (snd k))"

definition
  trans_MapOps_update :: "'s odlist \<times> 'obs \<Rightarrow> ('s :: linorder) odlist
                        \<Rightarrow> ('s, ('obs, 's odlist) mapping) trie
                        \<Rightarrow> ('s, ('obs, 's odlist) mapping) trie"
where
  "trans_MapOps_update \<equiv> \<lambda>k v m.
     trie_odlist_update_with (fst k) m Mapping.empty
      (\<lambda>m. Mapping.update (snd k) v m)"

definition
  trans_MapOps :: "(('s :: linorder, ('obs, 's odlist) mapping) trie, 's odlist \<times> 'obs, 's odlist) MapOps"
where
  "trans_MapOps \<equiv>
     \<lparr> MapOps.empty = empty_trie,
       lookup = trans_MapOps_lookup,
       update = trans_MapOps_update \<rparr>"

lemma (in FiniteSingleAgentEnvironment) trans_MapOps[intro, simp]:
  "MapOps (\<lambda>k. (spr_simAbs (fst k), snd k)) (SPRsingle.jkbpSEC \<times> UNIV) trans_MapOps"
proof
  fix k show "MapOps.lookup trans_MapOps (MapOps.empty trans_MapOps) k = None"
    unfolding trans_MapOps_def trans_MapOps_lookup_def trie_odlist_lookup_def
    by (auto split: prod.split)
next
  fix e k k' M
  assume k: "(spr_simAbs (fst k), snd k) \<in> SPRsingle.jkbpSEC \<times> (UNIV :: 'z set)"
     and k': "(spr_simAbs (fst k'), snd k') \<in> SPRsingle.jkbpSEC \<times> (UNIV :: 'z set)"
  show "MapOps.lookup trans_MapOps (MapOps.update trans_MapOps k e M) k'
         = (if (spr_simAbs (fst k'), snd k') = (spr_simAbs (fst k), snd k)
             then Some e else MapOps.lookup trans_MapOps M k')"
  proof(cases "(spr_simAbs (fst k'), snd k') = (spr_simAbs (fst k), snd k)")
    case True hence "k = k'"
      using injD[OF spr_simAbs_inj] k k' by (auto iff: prod_eqI)
    thus ?thesis
      unfolding trans_MapOps_def trans_MapOps_lookup_def trans_MapOps_update_def trie_odlist_lookup_def trie_odlist_update_with_def
      by (simp add: lookup_trie_update_with lookup_update split: option.split prod.split)
  next
    case False thus ?thesis
      unfolding trans_MapOps_def trans_MapOps_lookup_def trans_MapOps_update_def trie_odlist_lookup_def trie_odlist_update_with_def
      by (auto simp: lookup_empty lookup_update_neq lookup_trie_update_with split: option.split prod.split)
  qed
qed

(*>*)

subsubsection\<open>Locale instantiation\<close>

text\<open>

The above is sufficient to instantiate the @{term "Algorithm"} locale.

\<close>

sublocale FiniteSingleAgentEnvironment
        < SPRsingle: Algorithm
            jkbp envInit envAction envTrans envVal
            spr_jview envObs spr_jviewInit spr_jviewIncr
            spr_sim spr_simRels spr_simVal
            spr_simAbs spr_simObs spr_simInit spr_simTrans spr_simAction
            trie_odlist_MapOps trans_MapOps
(*<*)
  apply (unfold_locales)

  using spr_simInit
  apply auto[1]

  using spr_simObs
  apply auto[1]

  using spr_simAction
  apply blast

  using spr_simTrans
  apply blast

  apply (rule trie_odlist_MapOps[OF subset_inj_on[OF spr_simAbs_inj subset_UNIV]])
  apply (rule trans_MapOps)

  done

definition
  mkSPRSingleAuto :: "('a, 'p, 'aAct) KBP
                    \<Rightarrow> ('s :: linorder) list
                    \<Rightarrow> ('s \<Rightarrow> 'eAct list)
                    \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's)
                    \<Rightarrow> ('s \<Rightarrow> 'p \<Rightarrow> bool)
                    \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'obs)
                    \<Rightarrow> 'a \<Rightarrow> ('obs, 'aAct, 's odlist) Protocol"
where
  "mkSPRSingleAuto \<equiv> \<lambda>kbp envInit envAction envTrans envVal envObs.
    mkAlgAuto trie_odlist_MapOps
              trans_MapOps
              (spr_simObs envObs)
              (spr_simInit envInit envObs)
              (spr_simTrans kbp envAction envTrans envVal envObs)
              (spr_simAction kbp envVal)
              (\<lambda>a. map (spr_simInit envInit envObs a \<circ> envObs a) envInit)"

lemma (in FiniteSingleAgentEnvironment) mkSPRSingleAuto_implements:
  "SPR.implements (mkSPRSingleAuto (jkbp agent) envInit envAction envTrans envVal envObs)"
  using SPRsingle.k_mkAlgAuto_implements
  unfolding mkSPRSingleAuto_def mkAlgAuto_def alg_dfs_def SPRsingle.KBP.k_ins_def SPRsingle.KBP.k_empt_def SPRsingle.k_frontier_def SPRsingle.KBP.k_memb_def SPRsingle.KBP.transUpdate_def SPRsingle.KBP.actsUpdate_def
  apply simp
  done

(*

We actually run this unfolding of the algorithm. The lemma is keeping
us honest.

*)

type_synonym (in -)
  ('aAct, 'obs, 's) SPRSingleAutoDFS = "(('s, 'aAct list) trie, (('s, ('obs, 's odlist) mapping) trie)) AlgState"

definition
  SPRSingleAutoDFS :: "('a, 'p, 'aAct) KBP
                     \<Rightarrow> ('s :: linorder) list
                     \<Rightarrow> ('s \<Rightarrow> 'eAct list)
                     \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's)
                     \<Rightarrow> ('s \<Rightarrow> 'p \<Rightarrow> bool)
                     \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'obs)
                     \<Rightarrow> 'a \<Rightarrow> ('aAct, 'obs, 's) SPRSingleAutoDFS"
where
  "SPRSingleAutoDFS \<equiv> \<lambda>kbp envInit envAction envTrans envVal envObs. \<lambda>a.
    alg_dfs trie_odlist_MapOps
            trans_MapOps
            (spr_simObs envObs a)
            (spr_simTrans kbp envAction envTrans envVal envObs a)
            (spr_simAction kbp envVal a)
            (map (spr_simInit envInit envObs a \<circ> envObs a) envInit)"

lemma (in FiniteSingleAgentEnvironment)
  "mkSPRSingleAuto kbp envInit envAction envTrans envVal envObs
 = (\<lambda>a. alg_mk_auto trie_odlist_MapOps trans_MapOps (spr_simInit a) (SPRSingleAutoDFS kbp envInit envAction envTrans envVal envObs a))"
  unfolding mkSPRSingleAuto_def SPRSingleAutoDFS_def mkAlgAuto_def alg_mk_auto_def by (simp add: Let_def)

(*>*)
text\<open>

We use this theory to synthesise a solution to the robot of
\S\ref{sec:kbps-robot-intro} in \S\ref{sec:kbps-theory-robot}.

\<close>
(*<*)

end
(*>*)
